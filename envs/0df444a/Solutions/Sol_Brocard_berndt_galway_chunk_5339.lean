-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5339
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:32:43.61196+00:00
-- url     : https://prove2.me/submissions/1440132b-2398-4e6f-a205-6aa6a2d5ad90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 960071942 ≤ n < 960251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 960073192 1250 960071942 960071989
    0x1103070f11012c040207050309130618020a0e0103052203050a030e0102040e0c09120a0f0b2406090a080712020a050607050c0118030209090f100908070809010e 70
    0x8000418090030b02c3c03161140c0c0d04001c15000f020740c26084050400c02c2040d81c00580c0e03245070f0f060803880c44c0907441d025a804604e0801409101920380c100e0b0040f00c0c400200c5030440b40058070803005030301503c490100025034000d12a0842c3d07204c0d4200b15000300300720400c841d03c40c51106c0061899018240298007048000410300800396040c41060f143c1c03c100002181054140005500c101101501c030381c41d4600d0100740c003e01d40d6502007080348074502d8101100c60080e0207140bc80c1010040c402d09682d183d03032a500007103109407182c24200c5140070282c00d00352a41718a40c204610398118070341c02e6800403806880480e80c5c03041046824040c1c05a200c000e01c4082891042100c41031003034102901884e01400f0190002d0000540c884c2c00c4002402c100240f524201d144031010301a41e8070195110100700d082c050b00403408a255900d0700380400035109105004056441035a41c0071600401c010b00c100500c001040702d00c0003a06880a051400411050001c400103010000d06500b2810b0355802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 960074442 1250 960073192 960073223
    0xc08060901092007081306020a11090610081f060305191103010b1818041b060c0b0c04090c02300306041806150e0c1303031103070f 58
    0xa5003101d005100d440401d009070701c4103107807030384011180d05010014a800803880d0410000d807401640c842c4240c2c4502948416903d40000f5030311844550199580c07820240001035a08144480070310a001c0546411540050102d0481c1c1804005012240b212100c10038550030a5411b00564000c008542d004105130505608481941541d00380b0703142c9551404421040500c140b41c20b0b281100c912180c69502c07400d8508403041d5120022a003980d129080158440101e6007281159004500548002d107045541040807410064140903e1000c501e114803140005204ca0803690703484490300080c0c80c10306070b494403200180d5484802c040d0141e0442e40c8107035413000d030b07400c3c104a0400300103000c42106000180350709418030000d000540102d071221283c0304401e1035000d08064043d8403003010480d1a601e00400d100390072540c00380314104035010001c665510400c0c3c00f900d4408803218014801c42c1c5c40e503a0242c9200b02c4800f00140540000e005540100e602c0c03101110748540940070b0080101003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 960075692 1250 960074442 960074449
    0x50603090a140d1806211104090603030e0a0b09151201120515130609030e0306040819020106081002031308030901150506031b0d0621030305070212030a0c0504090c0806 74
    0x24100303241e03114111500c2e00304551a070214025003401c44103030b0001c0341e014807861140d02902c11f4100d04a102000020f002a8842155215000720383c060303511f400701c0c0080c0d00108540505940f01e120b12100017800f01180c5441d115840d804488011208980b41420745d04400f401003c0980c0003a020720a09014401482000d0004400007207020186207014642486000c480b6031040102401a82d83c03050300b0303800c043c005d07070205403051030080031141c0e14a024981581c8170740c00030700d10041c40007000412102182c0140a2a0190ba0f455000b030285449550070603002500021305800554804015040100d40400010343c060301081001045003442014418085d45150f1710041c0199801c001304032000d2092003005031044a56400b10780d88045540c0f50340b001e41460f030856503908550041171403401c013a07041400d640c0c030300c65101400680e90b40c480990b210700c000c0c944016105001c00000306000e406520101401000307042c42814552201d91a200b01c80078030a0060100b103452061118614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 960076942 1250 960075692 960075707
    0x418150c1106041502220f0f0e0c28030b090105090f0403030c030b03030a030f0609270c030f1209151d06041a1e04030c050603090a140d 60
    0x1141810003814101d074107419550180140003030540d107020020140c41d48503c0e011241c1544420041d450b000008503800f403481c011510074400d00041c5e404001680300c44102104007140c19a04000c041940c0e542518101ea9100c1c03661940310030310701c1c030513800a40b0401c5103125445407640c1e0002500c00b0450141f00e060382c410703000307540b107084480c003000202004c201c1e001c0c1d449507040ca40070658a82808003a0082e00360481c10f0f55050001213203444900380e146c0d002003400f4030075001c1030010f6030381c07160b6a00841d4903540d003005600c4501c3c40802103e331a071503103800180b0b205003040051180e03613813200d1045081c0320300110381d2202800a281601980040f000001d064031000038940d003110800083e200c0c52070312a841e00d040c0b00304c000c4510b0316a249004d64008101c94600085010b2080030354506070f6008a000607000c202c03412515500d40c1d00c610548080e06d0b44900c45050040c203040c00c201e0b00b40c000405413100c1d4401c1400c40c10024202e0b070582442105185c0080c40129a0f9800103170100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 960078192 1250 960076942 960076961
    0xa0b0108030910050d15061106160f050705070503060a060816050306070c260319020306010504090930030b0117040b04231e0c031b041815 61
    0x25881403048200c00d0f81c0710f080d5018120a0703030130702c00e90310101d10780d80300c2c041d02004805610300c0c00e0040e00096401e400406900e46440c5410913140e2517a624101c0d0188454901000d1001a0b00d0784401403c16024200401e9101c2c021130481c2d5103190b5500c00a403603c14211411109240c0301c0008200d0001c00f0024040200e10101d014000306082c81c01003a40c4a0700281080300300b0242c1c03006030081c00310003002c0048800d0060f010543e580505520ac10042d0f0007901e0341c002c10340210885d075440500703c0c801e40340a0706050751003511b42031501d800340c0080c03d00e07080141d079090020f103103840202c0024402088250610151000007295911000c0c0440356021540e038180030a5040a144101d00d00c108940e00035030003022903015445604150700741055440e2008102a2010b02c0340c120320380000791a4005406503800070000c090807010003921624805405501076010500700c100b000e4445038501202d900142001502d007881050900403403201600c242d030100013502c20034050081c01e004403140c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 960079442 1250 960078192 960078209
    0xa06050a050409122006010b210f070f050904020d09030801050604050d1209081510120210110c060a030608190b070c03140d0b18070225030506090a0b01 67
    0x981042c2c0b81e000d41e0740004c1d655101002003810901043c0b07042d000c036240d5082036030b1086510070340e151500020244d01806d801d02c45035111340c0c00380c1d09180d18207010902c41c81314001030002e01c3c0c8502c58142c4034040c43c6040d00303080c80414411400709443e50700c05407000082041c0d01003801c50765410301405811042e08110f004034030810080c403060b11070015104140358010400c0743c40020480040303c8840c015005400d250083da410740e14100e40f2545114003804248140c82d2602d5138602500500600c44800290060b0014a0f0240c966000d100001c4000c5001000d9403507042440c0000303081984904a842d000c41e075242000d0003080000c100403c00060b840703440c640200e0721511065805640200100100501881030f0010540b05180c1c958a01120a916503100c40b088030398030340a4100846068043c866130203254414580d4481928010160385c2c02801e4010003869207054214044400e40800c0007081900100180c420049244141d404030041c0c8055200d6160402c11f000060380415907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 960080692 1250 960079442 960079451
    0x703030507051303110f0a030807051207110609010201060b0307021b15070206130902120123010e1c0c0803091309030e062808090d0305040f1e0501050a06050a0504 72
    0x61400e2418503081c1c0341c0011030302148180240019200c1d00303041c1d46c0d20b6005a9698000400c000ca0600030300f9100e403280066817026081d05540d0941c5001c0c109000d00380001d40103000549040c00c5001740304016041c800454640e8440c00030340442e500c1611b01400681c000800600c41ca40b2196400c8586007040b604051107025003e101c007818068800c0c040d110b507000040800d060700c603088002c401030800442c00d40d2940340c0109120b4504109101d001000c600300b07a48040303031003090b210065202c44140c603203448808189041c880304501e50b01016080c0c52a1105030070201c1c00b101d040314000c110545c01541e4030300300300080c00f0740040d05512027100c13281010b2000c40041e41000d403606102c0d0701035a10741e4403820040fa4000305c01400100204100d048242e1034000b450744145524072a08440d000c40d204040380394402c40c01c84908031001740040849020f100300040340c026035540c1e48a5013201207011100d041c2c96a5085071426a01311403940d54404042195003814a180d00040404550401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 960081942 1250 960080692 960080707
    0x10605090103080f1225170f06040f02030a0501150503010803040308130902070606090c0c051f151e09062304060b0703020303101215020c03090d0305070303050705 72
    0x400304841030000600c0d000d4080b401c180035110120a980c03003210003032014481c0d81403440020081c1c0c0d0903401000c1082c138501d001c80c10710f1405603460b0202c4404100303800d906607950400155681e44c02034031459003e81c8429910066410303d0010358050041410001050752401c0c280209190b880901304040c40801d10040040103404402c1e00e089135048190b0a6031084070001c0f24042040035003054051602c04903c1500780b0895034048020740322460001c20000903100e00503201e55020307c41c010500d030302170140c2c3e001e44074801c5500004090b558070049808100e407071031009850302540105201294090058500b031807035500d00e2004166006e070400c2a141401034041a01d802044202c9444d51034030950f4806407181d038050001040b210b4003058880c001c0b850000d488c0c4c0d00603645080d5200501801180e9280e1440480d80c0c1a584040c0305c41a4400103095540030350407160240a8030b0106002d0240c0741d403100300407426014803035942d80c0d07070b0dc10081c41d02408440c409014a010071000b4800c00c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 960083192 1250 960081942 960081949
    0xd11031507050313110a030b07090506361206040314070807020d0c0e0c0a030e010605060a0f03020d0f0504050609011407140c030a0302040521070302010e1816030b03010605 76
    0x381c2d005240004041c03d044c400d0b0030455940070360b1448003508881402000000d02440014540c001c80d09603481568081ea00d8080101e113005000d0821050a01c1c2909804038140c0034601c0350601810601007604500d2280010b80540800c6075140c80580012041204250f400481d8400811003002e404d0300305009501d4150880c0a0b00c0c1c1c0082c09050409900f40602c000717440c10300c0c020a16146044007501d4007100890b050f802c1800040f010034107041913030402c54410700500041d40c20281040d42007800d21207044030846016141e003810305500b000301c0344c140758236070140e010075040c2e0380d43c08920350400e0310300f50385050303c02042d41d00146d00d080e0b0443c50040318215903075044107161900046001c80e6041100c1c09124aa0f25062107100004601e6407980c3c054010b03004544084860140301040001c05960030038200e50402d10715000190240019030280310040c072306481c06070064898031b50500c0e0544054206984400d0544010413901c001543c0c58021003007080c005400901c10380d442c25010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 960084442 1250 960083192 960083197
    0xc030604020a0e12010b120f0a03050306060d060b070c120f06050702030c01090f1e031209030302070210020606130c1202070302031215030d030506030309010e0a050d1103150705 78
    0x11441035800007900314141e03100d401c5881c0c080c10020603028040403001c450314020070318500d41600030040032501500d200d0010a4011030700501d03401900ca4030540d654101d95552000780301a87c8a14203010b01c1201c5401840303410058488014520ba850005040c9021030340e06a40c0501c3e04010b402140130006030f401c0714107032460f561010010429403104401a1b0440c000c909910041c0d42c60a0b0f5603d0030f229100221040c7c1318012020800700403c0a00c080d4002d042c0c9803006008220500070020480312550301c0100054020316005060141960004940180b07403004240103902400078410503103031492480444c066010710400048840303030760240003070307507030500d90025143c0c08240c040900d4000e004845044c45240c0385d5004a150220301c0e80e054241c03500c0424002c0c0b141000d1300a9180c040c2c410507000e02030040003981050b407442c0044541c4681c2c507e805070800d06842000030141c544002110b8682c1c82000322041c8010301000749032034100c50481d010051803141302403151281e0400d08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 960085692 1250 960084442 960084451
    0xc0603010503190201021905160503011b0e010c0818030715020c09040215031003031b020a030f05010e01150611030304020f09131509060e0a03050307050703023d050c03 74
    0x3c2503a0915440d00050b81003032190340f21030f041c1071107072401074081101c041421034880700b01c0481c0803c03082d00d031303014507080b141c1d0320142103012242c100e00414082e000d42c003404404e01052410241107221982da107407181d00203190344002c4c0d07a0783c0c2c0714102151409001a101400f1011491850301807800780c029964041c01c507080b03004d4103480010030150344070a031801d081c00c407805e140c45540b0705190760040d01140031807205a002034200b403291071021920325072903000190018103a5035900e003141c4540b803007041c10100c2150346660341c41180c072140d4028004c00c20020501460380344042c0c07800601901c2c00d08100c1520f5640d0b00100200401a034503c1602958440705503004030b030305c2d0341d85000f4140d2840510006007003024011041281850706d5001610fa0034031500c024403524210105090f900e00070900000c001c05c0b01072001407407072072040c0040e1034194003e1040395031444150814100c40b007540200b4011903c02603114182ca840c1070300c40d1045040401a04000901e450039501d106400081c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 960086942 1250 960085692 960085723
    0x100c0305032410050a092123070602010608070603050f131b03050703020414070806060315090c0301090606050408070b18040f09050f0307050a0210091d01080c0603010503 75
    0x50600008080e11071002d01c4004014080705450324a0140250036600003240a10014a5441020500fa0304105038210302141c0c80784419900a85960341c1c0030f0030fa85000c0044c01c40034000c030000483c01002c00502005014940001403807504003010582055000c2d0061828103041c0070900400300f10110340e00740c1c40901c0d01c0182c414580075181042c49010000f004c00d030324801024002c000d0003000308001f000c50b4802c840030006001100018400e00b603049400c00081919000019440d0074403600656001040c00400710161040a0001300d08000a0311150008000030006000a10092103004040c094604006085c9450711030140c0e40c404084c01020840c1c480443c0140118100e007403284c00d40000100107200e9110300e05c001d44002d101c00c1100b0b0713800c1d1090b001503524101010088903040e41d00300000d040c4280c4960203016881311919222001c0201000000616004d480c0c8500321194442c24441d205515010140d8542141c20712600d2007000100300400555400054240e28000e922 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 960088192 1250 960086942 960086971
    0x180a092304170d0204060807110c0d03090f090608010f0615050f070611070213060506071b09110309100b0609041a19051f090314010b1302030105100c030503 69
    0x2454456460206003014402081c1c021800e0018030f20b840e009002519100e070740d0411140d903610350898800358180781350071164100041030415400c0214150205034040e00702941499680c0320180f04002d801c0d440b0714202aa1140140082c041c2030090311100002e421040c4910f80c200707003586010950709480e500074030200041e2000380200d00307000d0f11403007034000000300600204200000b0040e030000204a22401800c2071201042d0312502c10300d0142c03040501080e040020365501d4146d0254000310803c841180407030005a01d0350319003c0c500884481c3c0381110b449007070940321700c0e20304801c0300808503400d82050130000d029200c1000380c90950004443c0420b004402c099a91581c81051021030b402560b0501c041c0400d16840c0c1031402240c000703540001d4a44940341c203803401d2080564000d00002d035070070803c00108980c0c02050107004083c000020305000c80034001101a814120380c00c1c1444c0c4c0200041100b4500000340340071112881c10800c1018003250b400034a01d20005000c5800003110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 960089442 1250 960088192 960088201
    0xf13030e0402030a0504050d030516140706020703020c09010e060303190509180702241308190305040b010b030403020a0b09073f030c061a06180a0923 66
    0x4699000305850050030455403410900380c0440078103c00c5070240d401e40b00700640100340320f00c05e10615105112250410340220301c1400c044407030842e80740c2c0807541004103112000100b1294402000000d00c00d070028048688400e0510841d044140d02c1110032249623030401459441c0402203e00d64181d000d0a43d00d00d040325801039070316014942099402031a02d42c040c01480003501005d9014400b0b540844000100c4160840d508407071548020240100b02c0d404501410119240c006006118103940b90800c001b07103c01083c91640321010200007500c0d4006e000c20b014802c07164502501050280502e5441e040e02c000e036a45100c60360040074206248009003845174180586000340003078081307440740014041c14000c1002d0080c030080044039084813a1994600548003028000381d071544403800704e404951110350003411085007602884010344c4035644169103040061003500c07401d440b405415991041400304c0001caa4010050103032070700c191400c07109002c2c5412040012244449103190360b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 960090692 1250 960089442 960089447
    0x50105152d07240e07060c1101020a080c0a060c08070c0f02130f0209030d0323100f060f0305070302090f0409020a120510150608041104060b0a02030a0212030f1303 72
    0x80e16009000b0000f0042d41c1040c190089220708070300412680180b00b14904400101e48489403440740780c0119089100000000f4000d010f80c0f40c0d5040c0500542da1079001507180c002442c1d02c900085015034104600100400100784030303294550002d0700e80500c80d4a004080030b07002115480020304030420700840f400441d81e8589400380444c034a4a028420501855040d0001c1e410840041b44070f4051109410304462182c402ca4039405685400034801c0821455a114140c402070301260f2010f2040d88042140c442d07a4484400400d060740d91150003030702d00c04000f0215940a0030702400c240c0100041059582c5400540341c0c00c4000300d0b400900f4198a2001400c240c5c1c207680300040703000202c92600144500821140343c00c0e008050140890342e101d120911000c0194017501000c1200b1744040780214640f040f107204400c0c4090000200c007912000080172940040c0c00010041e4030029508450b558140050103006400380001e034210f04003001850014040200418015132070b20500303106040c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 960091942 1250 960090692 960090697
    0x2060403020f03180d110411070213140714190f0f080c0409270b06030d050403020310050a0b0d0c15030603020607031b0c080d09080a0b27030409050105152d 69
    0x10004200f0401c5660050230071031a034000001c01c0e44940c031604070300b03812240640140511500285889400c40c6d0301e002c01940e03521481c840e140800c070810f002c03505031200101301280c0107079026142d0341e107203010405000f4216440309041ca001c1291000a000c2c0b4088000c00341c40a9418415003c40c060302c5042c41160040303c40507038821103405116807a8180022416030902800040d81607134020030308070300c05407020310440c403000b90180c0c00401c0340401840c81c1e0340017076000381e106031000c21a984100000307441c60907501416550600d00a10400c46442007071103070749200700c10307040078030105145400003846401441790103400d01000886040211500445a0610940c040e215040d13280e1500030b0103580750403601d031200100c0c0500d540410142400241100341981c07049840b41d01c0c2d69403102c9c044603042c0d1040030310b0f403041d02800d41e4506050144040c0020303012007000050150303d80410850040c030310f1008490700740300400c0f0100329070180c0312030001d020002a0417000c2c044402c170203a131201e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 960093192 1250 960091942 960091973
    0x61f05090301020d2c030406080a05060d08070303141321050c0d110c040203190e0321090c0907090b09012a0b0105010e030a03140d020a02060403020f03180d 69
    0x1440e02e500f40c450110384c28030744940e400700c0340b2911120a03104e0205d950390784294054900460840b0000a540c030b140c54201030703401000504880e0700d03514296201c2000d0f800400c012404a5120035001480d01c3c81c0d41c51103681714043c40c200500c00000c0c6e8940804c241c0100c2d03c0d1100710340c6580250401d01c0c0c010b400315400c1458803011500d07810303100d480c004e081c0d2510f00894500380c0076041103041649094020340303014400251000d58148000c1854800400b09a041c0c1c44560000b030090a41f841d40c01e8021b64065401e214045056203070042e011420501c0703072206903129164000520a006a200307200c1410781d80c03007404c042d651710003400041e500010040c54240c0340e0708061035500210499202000c601c1881940b0540781039885800640d1910101c0d0252038050740080d41d1800401d05c6105a410b400e440080090314004800039224180d1707002808810140c0c0c40b40b02400f0400d607040141140700c00e582c401641c00d002110401c1d04207034070f0100955100358181c0112005001050540c101d05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 960094442 1250 960093192 960093217
    0x9200936010617150708010f140a08070f18020301081f09050307061b02010606020c0f04090602030412020f0d02072607081c0e1f0c0516050405061f0509030102 70
    0x708003450642a0742c1d4542c00102c0c2d0304c04110358086440d06025200c1da5068844929a03965454180001410081062072180764000e958040c00140c42d0814025240584400b058610006040c01802844642030b148404281c03881000108048000460242440540c4c03000c0c1900800c0010341d0000034200016001d411400001940710411030290301011410800c00c12952250800c050706a080310098400d0700050f801c014a0090640742450148c0515070008000003901019522404100d0b00212000c454411640400101e0301d80c04220303101200e400100100100e0000c0800203464080740d100748001d2401c4564000c0302001415541001c4515040c1180d4407155240707802c50340c40004601e902c1c00c40d00840e03000283c00c3d102d020850721300704004e002426025082c885441c0c42020050b030820400040384400c10008400f031100d10f103c04020560444180d040c5000c001c01c50340050b000c00d114003c8610710320300f00b4805040d22280002c1d07500301962600b5010020902a100f10103d4261 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 960095692 1250 960094442 960094469
    0x90b0f1b1312210815030a0b010902030702031209070611070f030f0602040816090605100525020a15081305102426030f031603092009360106 62
    0x207800c3d50000d5082d11a913802c440d225001c40c0c0c042c0c281b50315210f00440140541e411000180541c1502e82c00940d0485800c2c81100e20740b0583c004085c41c2c0c42001c0d14024004d800c5000c1c20010311b9807051035007040c0c283c600b014044c064a40104801000c405101c000c0c0400c040400100501119505a0740200041002d541c070007449800c0c0c6415048913800745401076840c129000c40c032400c00c2c204114441982e03464051920410441d1000491060600200c000010b04104c4005840e40440d4900500316210b6040d4000c0f608a005810814000c0041401c1c658001500012801c0010b5400007116030351800607074503070000410007020340d40446c0d20305249a10b003000141c801150661030341003a803191320000b4284034140c41945a2003099681401c81d1000e0004c101034402034070000b06805200d040010700324419a4447c611407003031142c2c030b48421035030000505060600000e010361002c0c100301036030f9120100034a0042c02421138105d0716030529040e511110b80d80b000f5807058000d0b00707901c00f0040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 960096942 1250 960095692 960095753
    0x909090812091b1306080d1206050d1203052a040302090c030f010303140909040c05040b030f100b01200a0311032b090b0f1b1312 57
    0x803103621004119061004003000107400d02c0020900c404016449111943e6080952081002c65044010f10b031419a0780c94000040c1414108025087c041060b2035158090740b004980400b140c0c031030360096025115444c0800002440c00c50f440400070014140000d071500d032000d0f6004901d000880c2c1701c0310140c0515968205803040c2c00948112032003100c0e980f011b1703a180300c440300881c04191a000c0140d2906001030001a00804a0840c0340250400090800041000045030072105a034152280882c08070306001d01c2c24203000d500c0a2250640c001c00b4098010710149588040e490000c13071445944114184540c0e200780800c51000c040000820050020880c036aa12440b007150102c0100e42142c0701c0011229000c41503507915440060702e004d260600710b6500108818038071060b000701e0303592100c10001440c0f504800b4028606440c0c12201403402c600401c044000082000800c2c017400e201120107003110008030415101c1040310404c3d064a40d140110603c135602d0504e1403200a45826030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 960098192 1250 960096942 960096953
    0x6030905071a120a24051305130b040c2c07030c051308060726040b070309020405090a0210090f050d11031906060e0906130c0f14040f05010e16090909 66
    0x48883c844d02c11021890010100341c0f5403100c0c1c01510643d86c0254180c1207440d541f000719440135511840b0707179500612a92280c2da07041d049500442e8100c504583e10502440301000313a150122443c00340702c9481c80d65a00034007004880701c0e00140100304042d201d164544849200d5800d40700459800c0e241d0030000d980300e000341c5403a40f00454040c030004420380300c95035000041e08070b0316120022000044511f03803074581390054904401410b807401e06480e9481e420061710f5500c074071441074181c400600f842e81d41500c1040343c0601000b0740390040200000e0280318003900e0700c04a10840e01d084070300000030740385413410003041d01740002600d44c1070043c1c4030040302480078011500e107820b02c109000c10103580c075510f43c207401c81400c0c0c500c0100380c3e001800154440c0b50f082c080341c540307034000c070300c1001119603c810708074048071250800490f85800803070265a9003054018900d0381c209151082c009903040424110600d6401407088030140c00c245030045000d400340391004007418903110140442c0700c241c2080c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 960099442 1250 960098192 960098201
    0x7030e161503050705071115040801140114010f2003030405030d050105030d081f18020711030303131209030506160e01090b0f0906090414040c06030905071a120a 71
    0x5444120322240040d007035031480380c880c56216003070382e032181802c0207110344403060812010310406800c03080d0a4140d4100408010190008107010800410303c0d5007042c040401074107040e0302005c04d20504103450140c0e40e03002066861000c06a05d0300b0404a21500c21600702d05a0110380d100050100205000900001000400325850070000601046e6a180d05066031103000c0c1c0183e030006a298400704060900103840700401030610b40600c41c440343c51343c81d001c07030307464441e003005c4483c6138001240400c10818501542d61064100c024508500e04003a40c6584a01030650040c0ba00f8450502814090301847c40383c009150014121003246c980003c0072100750080c4901c0c000864812500b2011a41c8100038000645000ca28642d0410490070b0400310300360011002e441c0c1c44681070040d100645c4a5104001c4050041c01c41a8914201410081c105041c10342140e02014141084070703010403000501c5000311100420f80c0c5d5004c0a00810b8261203001e111020000c130300d091001c1c0010351116412 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 960100692 1250 960099442 960099449
    0xc060c05031b0702060a0f02160803031b18040209150d140c070c050405100803030a05010e0c030f010b070201030b030a1a15031b0301090f0308150906011707030e16 72
    0x1d100d030242000c0b4240c0c0d142800b811400940c0003004200101d00b151048441010500301801103868505001c003624003500c949820140309030f400030080005500d1300d0740040081584203070700145486510743e40300c0c5012656100d258040c0e0740002d0b240001307403645015000c90890300148662a4800e03211100c01404208114030514000000032515100780740007201d1040c2d9000d021070030340500d84001d003c040c09000700791504003a042c0d0b0b000115108244000c5100e020320040c00159581050800005490050301c03405181009100304501204620300d6681918003480103280c64200d05d10040b0007030705554000c9501400380003485400c0109805501d00500b222688051703603595400c0003800c89006489145038103038402d210543c0d00720f0b42003400c01e18414001e400443d0f451440e0310740301600301703100508500054170107040100405020101c40750108044500b0102810541c2c0001c119541000c0c00c85015500c032800f2031011402a4040341d00c4201010581d500c3d046019202842800c1520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 960101942 1250 960100692 960100711
    0x181206010302030c060f03040605101824030302030304081303060f0905010f02250c091b17060a2c07050d060e100e04080c07030c080c0102010c1209030c060c0503 71
    0x11080d42e11715200054440300c50b03146401505580d01c03601da200250002406507460041600c3c4003184400100301030f8a560b03400e0460114000880106c0152031b01707031020404683d01c2a480044c000603030701004403600641c10003440360315a169038455900810241d0320040c0901d28040e02d075031485c1c185421140103103004000801c071451904c06101c00340d125000d599104000d16080712000200b0038000c810307055000f04d1110006035201e114410482e00c0e01a8100c142075020300420030242e50007103000c0e060044500d152a0703a802c064012441c2d017140c1e8000e07501c01d031401851451200780100444961940503029440042c00c00520140c020f50140c01c0070700100c2c3c01c104000c5840c456501146000e01e01842050140f185400300003001100701a2044641c8002007105004030302c8200961000355001d00b10411034140381000080c40c00070086021410b590401c5c41d500f031400e1700704c8141c0c84a4580035001188011407441d04417118910380d44000c1c41d991034510510000caa024024500c60000303074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 960103192 1250 960101942 960101953
    0x503150603030307120905030301030b01030210140a080408120c04140d120305060d060e16150c0602090d06020403080927070e1c03031a0d02060d0218120601030203 72
    0x8a40084800211503180d0540e20800100b01824400c4000c4121189007034000600202036079241410350748281d109946424107100107006502e4a107154480b8918141400c4040460b04003c0034454090b01041c50107120020340080c0234810b13683d00304d882c280d6510764a81b00c18078042d07403010348540050050442c0307010100a103046a041c004c00c0d9101c802c2e0451100095000f81c92403c5024000c014640d0760803050f0803110360005003040c010b00c8481c240103c00381180c14000d01d0513402803607841d80440081d40480d200d01c008180c11103101c40503290019005a40d0304001404180d02602034840100210310004000003807040b0180030f489940400c64010344000715840040d011201410300b182c0c0b8808003140840d5480c0c0c020800c45101800181010b1610150f43c224000142d01551080d40429101c41d00032000d45400351202201610444280343c0b03e503020340229815005480c41c00000d99400240d00880301031070384202040303490040202c01d145000360b07402c9880d020700703110480c0a807198 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 960104442 1250 960103192 960103213
    0x80610091b0207051e090c03070305060d0b13080f041e06020f030301060e040b0a17070609180f020c0109150e06010b03060d0309090509030903070f260102130f0503 72
    0x7405105041070080340d000b420000d00780f60800c0011261404d400404554001642001d51158410203216500300d40c6100d48030b1a25803c003405488004101d68030609a02445000240c56403202c03581000c20441c4c1f07150401c01c13500d408140352281c0c8041c14028600420300040d00b03415180443e400d000201004c203030f0555100e8080e41e81d00f183c01c80b500b225030800d100600c601c030312070300c6c03620040078005001103010031040740400c50303404542e0405405a40c0d0130f40702000c02ca00030446034005181910f442400c4a140000c01c00310901000d000c042c0550b1990080411102c40c0d8042e1410000840000c011900311458400d800c1d10040340f600c00c40908245122140d601e01043c018102d03861009120b240d6a21801041070500c000001202403180b400000315403083d191046520502c1104011035843d03501c0400c040c070303140ea281c2c8050702c0714075130800900610000100b01c00d1495101c0c41c014840c010780c043d00c0b60180c045c0a2000d2030b081701d0703840001a2007441d07014a4003290420ba00b920b919850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 960105692 1250 960104442 960104471
    0x31306151d04050706140405061206011805010503010603020d090b0c09010801060f0f050f1306080a06050616080721021006060c0c06050309121209151003110a08061009 74
    0x102e401400541002d141041043d01030040d410b40e1003038943e80645800d4440001078000c0d08201006aa481d180034100032455070006007042801c2e00c0030880301a468074207400207003580b005004400c00c00d60045440c20148030700e50000503016901911060751450450141d42c890b07000b984e10540083c1d4008000036800d4028080080f0382c80c0160f856085080c0040000c1d079290b84001c0a0050845c0100295050b20100f4460800503003d1903948208a0402503c1c280a4070100d0b0411882440300304a0b04000032004108200c4040d40f00344002e85035942e50400600030f00406072000e107400d5907015460081640454607400d001c0406004000c502d444260441b2403203d0204002c5c5511118207060200c40d00610203194092805800c135180719002094010b014dc000c5800400b24610740000d100541760244031004a9034101c00500d9950b1900102001884983d488040c10301f00d440c0e0f6007692070380c4070400b0020140c05401c0441d181d0b03007052200650035524611414501c5031900107a031000c00e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 960106942 1250 960105692 960105749
    0x9020a140406020d05030c0705030a0e040c0314041103010207020604090b03060a09021c05031303061d062403010906051801060e10030312020403120206040605070c0f060203130615 79
    0x1050b5a006010f2002822400e960325440641a00030022007846500c001075010402022000c05960f03501102c0f100c00300a002c251a0b42800c02c505140c105801281c00a002c0e030803095103e900207002100080c40c40020030300921800c1e41c0607411040000b00400e254049400106c0c2c0c014055084a010703560f44060a4102c2d009808004d5100c00c59a40c4102c5400310002030b405c40314010015240b4100c42e102102140007030580c02203d04640319030607250419826440044540f5852028100c14601284050900c040300c92f0500c0c0701c1074483e4002546038a01b5130190010315404242007109081c10342c0c81410307407224140556895030038035034082420680104d10714080d600244800d40d10900315501038440608282c0004c02295003032100201050070b800210b00401c203940c010b000b442c18a0b062020030386500034000c40c02d001ca0140710b03a000640d2000501642c60300948010707100e84880016800d010306400e800b400c101d091600904000c1c010644079021210a0a05a0b0207146e09074a9140d840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 960108192 1250 960106942 960106949
    0x191508041a0c0304020609010908071401031d0303011203030e03181e1005070501201c05040f0f0302030d15140d020306060f0d0b09070f09020705061b0d020409020a1404 74
    0x1202d050010500509140028203100481414000300464a0f2100c079841e0000fa5400303906860360300b0001008558242c8210140f0500075005042d910b1b820703d80d803554922040c441d01010601c11a210744c00e0512a80c403d520801c083c0d81034035501c1c40080d2140040089080d44507104d059080d0400d0000c0c0c290205441982e2406170806005604100c015a290f0f0091681680c0d0b554a80d003050704141482060303c072454102c9403815807140755081241d0302c03100310340414042e040d1030001030001080040c80f8200403da0302c50021030400c002450104d00750302507540c0c894412810041039298091a91546109607041c4654124013121b50b401000f4400480c1030005e9019001200410100e0038001070401c5070304000b50401268038001d95440401c440101d4590728541c10141d03082c40288c04a144000040c0f055000650900e070a82e02c2c1ca0f6201e81c00a051516480b51284c850141d005041c03099030100c1d42c8d0608110748072592214100060741c010701010000036800e04800303461000c281d050302c0c00d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 960109442 1250 960108192 960108211
    0x1410020c010c1202182b0f1a04080d091a0907081b0901050f030f0d0305010e0f01180e07091a13020708040b0a050f040603140a06080309191508041a 65
    0x42605003010300039104004291b0b901c0c0e8840000d003181001d000800900ca140e0701c01d4551900d54100f41c203002e200b954041c10a61206400c0009120100f08008151903610703009100000e0784c4a801c0c41c1007055200d000160400a00c240340c208210302402107003034001c0322901425540c21000400440c4080c1641201e242e50011103500184443d08010344c82a14551020703040700d00c640c0c00040c4d00c43c600b0b00780340d1210001a868000600c202103e1681d05034000b04c03110300d852815410142204c07050800c0285d038142965883d55102d40083e010003000300145020a010800340105080032036048134212a0280544200d0403807410a03003070f40c400c550086030006c1da55400d05080207488806540400795140c200842841152a0384c01030000900080413039480c00612200d5003000c0000c1c580300288400790580c80c1c85010000d25802000700c440110045500d2458107000034a688840c080d1900201407007019007642500080d000a01c0e18001c0f4064001e055002c090040401d07030302c98003210030044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 960110692 1250 960109442 960109477
    0x408030901050114060a0c0602070816051c081503011401061106060d030f1101090803010f080d1d040b010210020c06010e160e1005160507061404121410020c010c1202 73
    0x86c580c4246c01076207000c0d11604025140c41031984842000b90400140e428100b60703034a05100c00c02c40d0803c4404042c101d00014100f500c180721002414840000b000c5e225000300b0301c24504841d943c00e501100e5546900c00e007010595850303501c01428054101c3c01e1550324170485021a21a00d8508201c08810368955109040c00003824800c440d07210b0742565412296403160042e8001a110801450103400381410303d0030703580d180c1030780c403450130315010408818070584400e100782c0583d84a04c5140040000c1d0b0380450311a20020041b86006000000c5865451010909000c80341c030109250f4101d402041c501c218980783c0d81e6483c8111843e02002d100407a062039000070148c14814121203000c1c0304e0f42032450800d94200200842284080303000c84441d00941010700a003a000b10020b1070034104104403600b0b0034103080a00c485542007980c041e11001c5440c42c2e01104040070003411151103082103055456480c003566840c0a8a0800003a0003c41c24018100055001c94800d030b03035150181c0d41b401c07a03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 960111942 1250 960110692 960110707
    0x10f0e030a020d24090204050a33080f1c052110050303070c1a041404090519060606200309210304320a1701020909040803090105011406 60
    0x360411110f022110021070400e81d040c44ea1403100c8001040c41d100d0804100342c2c040788100000c40718001c1c5088000c0c0d14110901c0c80d5042000507110000450b0002c04d20710000718604942c0391509035101e451030f4819601d005215240110b00c10748000308403036400e20710142703860003918075025455a0000c1c01c0c10040c0600c1c80d518111042c1a0000d6054082480707041c1c4030f5001c24150351011030161200800910200156914050b685c6904403a03000441d081a08000c1d0308001d0b20040741d901c2d845540c8502c5100240301041c00701c8588000c01041c6101860702030300d42070b4080e0405101c1c1202140070068030307040310075030b0030340c03803801254038001941c0b03001d40080400c15109090811000e03803181451680d600701e0002c20040c405001c04000a441c021201c5610002a00001c01c5520002d000076000c1802030b1508903440007620459052031041465034540a4024015900d030035038840e000106210901207613a0045015a030600c0080c001a03807103140401d52040144081500100100070300d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 960113192 1250 960111942 960111949
    0x5091503011a22030318080d020a0209041e050615010c0b07030509070e072003120103080f2208060906040302120f040e010807050a140109062a06020306010f0e030a02 73
    0x40c0038511010f403420030307100c900c60200703103d001c810b03003088000c01d1842c180c00114151180c0070f100180609802884030040e01c0b4030007511445005130003409010306401043c10001d8011310074a0180310382d0b24020601416040085c1c0d42d203000d44644000705c0000800f2601035105a103d038094540241c00c208054031f54a100300d00410008083d4000e0780030329040410f00e8610a40c98500a00441c2d88a5080d40b21803050350941e80501140001580d108000511004601c4a48070341165002640217072181c40304820b01c4018803602201d001e288641d030b85c0b02c4081150651020041d28900011240c6503a50742220540e038072029100a0096844034030342c1e24144c40c10034020440c05008040342e07400c0640c1c40d00b05c641a074400303030465401a0407440d01405035040032103440e401018810900082980e0501c0040c040300440d000b100704000349100f201441401c0c030180e0380e190f5000203540e8200280c841c24004008e4200751008d90000b00d04078003209209108d0107001583e000002c001c1d080820491342003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 960114442 1250 960113192 960113197
    0x303090102040e07170412051207050901030e03031e07051b01060e06040b0a29040311030d050315010c0201030207050312010303090803040b04090b01030612050709060b04081b040f020a05091503011a 87
    0x322401c200c410482044149032740b0103004c3c010481c54a03820344405000001505590416043d26000c0d84180200125041007446d19281c0707100f14040070440ea2242101113a55104030b00040707040d0b00c00000c0d80600700700150b002504540e00141515003e8071880100815200447e0b409540003103d41070038803542c0340e8044030420054148040c0d076021441c404d11003203035401643c816513600f0b264074a6846581824880c20258014503c4d20703a140d441d00700010554101030311100760400500f000c2d0002164000d82c11900c0c1c81d50030800f02d82e1146081688020111000d0000b140002e1b4127550001e850302e0300005071400d0315030400030b0b0f60500303082c10000320050450b0311040781059255280084ca2000642003495601d02500280c100d060800341c41d40151039251b8841e108001c8104820840700c10701040810000a00c0400543c62000c0c034030018007e80020080302e03e40d00e01c00118111865000310082c000d000e0251540d110388802e10341c00d40402e02091041100303140132800d12210740c01340d6400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 960115692 1250 960114442 960114473
    0x20d0e0406050a031b2c04031407051b0a12080d0603060e0d031107021c05010f021602040b03010504051528050403080f01140111010e0303090102040e071704 69
    0x10000d2190b69440016803803d0719944140c50140e100407881c88000c0c0341c401154043d0040010710302002614090005402c4600e000c01001a2441004641010700c2920640e415400c83c01e009911441e05060082c1c641024003070109140e04c986082072100d08084040c60125802803480d900c0a48a545506034a58441c000e2035000507038803440480090800c6c4038428004c41090020102d160303440201808890000d81140e000800030701685c40160388804d8600012071108640400d5010145006405042c20055405445001080c0b813001a03820400d803200140c0212424885080000c0c01d0601301d40040d0380c05040c5030094900341c1e032403c11800e070841d00142c91030981e210420707a4481c0e41180f19a2100c0d0b0080c0d0a4460080c4010b040d441400a0781244644a44014a51400d85103000d0078030800c90090511055807000881c1c29420340c0301c030031401a110252aa203191000c50f06000358014000d0007403d41001001c030350a54410049110101071010211803151280e4591142040701b400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 960116942 1250 960115692 960115699
    0xe0a0501061d010f150c240e0d09180b03070801090302010603230d1110110a0f020d051e04035d02190b0406060b0a020d0e 54
    0x44410002042407003903000074030903201c1aa015640d030100110010340c06a0082800041101d024050400e11403602d0403e1901e90a0105492110386020310000108000d240c00c801c2002c1840b00f141da025801c4500d034000c0e041c00362a002202c0c1d003425990b80902c0c0c00b481c0c03040d68205040400100196200c42003401c0c1c02401ca41d00f49948003589800d4500171041100141d44500c820820015030703403041913042c40d18010001b04030700d41301501566103109141d10020440209031803411001c061100540b14030045906000e5031032500c22800c0c50798040a002400510300c6180214030b0362020898058144155030f5044c580004400c02424004500068018421040100000003001c4100c6c01031500303001442100040c007001300c14a1014019040b0110180f1131034030b41d21120f9408500200b0410300e000c043d12641400c0c1760124901182c0c203006142c08043ca120060030b1000c42c03a201c40c89079100300005c0c80f0541d1110580300041c02600c00400240c1d00501860030001d011300c0e0720140401016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 960118192 1250 960116942 960116953
    0x207031e08031905070302040303020a0303150b1602130e1509073302120f0c0a0503071b050f06030c030a1b03021c1a120118121710090e 60
    0x54440901c2030703100340c0f00940d6008846002490302d00090048681c4641c40341000c508140c40d42d00d01944420307000d00700404040c1c0d101e4981084e2a00070560a010f0700162071816200c914112001028007805102603110f83c10400b084e85600e0628003038070b20060302c000d0242495600103403c1c503011400280c58200c00b0701134128085030034480307001c401015550250b04581035000342480030b0040a80083c000c8210741020031041003581141c0100d401c41a44200480e94460000140e241400c8803824000c01c1400300091510510401c9440b6a0b02d00c8417a5028a00542d5a0010892001010b0502a0700000248006043c17a42c4c260701442d0b101e005084041a1503142c0d64032481e07684001c0101d1b5011940c041402c2445546810305040703001ca006c4800c1000c00891060340301071140c68403407148200d120401c07066a0110a40181c2c412010405041600550074603007154141c00a204a400040442403c080a40000b4130325034080d64000c81450700103810b045454001d446d8101c0c6008843c890b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 960119442 1250 960118192 960118253
    0xc0b0c100c0c11010908070513110c160f060e010807022407120b060322050a030e13140601050a090317040603140103030e0f0109030b0f0402010816020703 68
    0x540030350300150210b41d0302c40880c2e007a0b0346041d0085400c212100d40c1044841c1c00700748280780000032110103440040f42d2402c00d002c1c0e040000005401542a00c443c210b4001c0303914001c020340011480489402d800190600f0340e29503e102c0090945071080c100000c010000d592141c0d4003680b14150407000324410343d540c0d90511a608001e0503485a03d0a0500100908200c042588181d004002401c00c0c5424000c440b40302c80003d00c14000905208a442c0d984004200d000e0a80701c10310384290317440340039107607400e00c3d9083c040c24903800c3d61441e901410005032011004d030028807958000080e49048403100e42c40b65401128540c02c860741080078041418008000700b1003802c0200703410610a43c1c80c41d501c90078490000c05036228031440800d070150000042c000250000301901c0c00507425034000352044136500040f03403422541c0d44040e08200b009402c1c407010702c0001c100c0030310a60003a00c4810150b01c40d240192015510f5461000050300405000d200151080c9038001451a41a2450808008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 960120692 1250 960119442 960119473
    0x3021e091e06030d09141f02010203150402250804171e0a0f06090305090a06020309240f0702030309120604211413091803021005040c0b0c 61
    0x580c1c1c031402040180c01410703a003070008031656500c00310640143c41c2c84007244030050903840c1c0d14095001402c0c1802c1c500c042a40320000e00300f20700f00c0100020802078400c12006070003948182c4450102c8a4600405036260400f4021524040e1082040281250810b102c01805101881003194001c0003084001450784800d071f54031780d420000d5406000324400502151400259400b407840154102001c61404984880400042550406000708861415103012942071207580121684020910404903201d43e002001e4415040c0070740d2910000c0d440c2c01d480302c0c6201c01815104544490800905140d296203c028000c52031000d02103e09010b0660000b0301541e4180c503210059511040400c0700f0f1040e00c4503c1034948280340003201c0800500c001c0205401e2203200c000203400c2c800540605a4519480c81d00010031001e00700f0081007103c6200c0601c40c4440b980260018880d00c0a494541e0096100c0c00d401103070b00000d000c11003464541d1181650b00300001401e814001e202d00d8441015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 960121942 1250 960120692 960120709
    0xf0810030503181e0d021002030c01050709080d09081b060903011a130513060207020f0316140118062f0a02040c03020a08180307061b03060501020a0c03021e 69
    0x8010b4145035100c00c40c81018400700700210850300f004160780e0a85400140c0317404004014454069070514414401140e0680c594443c2c904000d800350310f0300e0700b042203455001070b040050782c0355002626818603040d0300444180d161406061141c0d044004219991031032516410010306020380b0007410410081d0010b402c6540c1042400b080f0114441d11003024079118560980703490219204200d64100050048003803005084020000f44d40000c4d0720701595a011f80007000b006000b0100d80100800883c2c0584041780786c4178694803040c090745213510941c003400c0a07071002031205400c042d80034a44a412141400960b480f80070281044428411409094403e80c2c11260094000e100302121841440100c4040801820416106200c0301c0c3c2e5150740048495008810414125010000006540d0840c031031450001e0110b40780400644940e0460421640787c000b00d0740741048250355907801642c80c1d115030600240301c1e040d01d12041c4010328140c915189070b07522000d40012012072000100d60103d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 960123192 1250 960121942 960121957
    0xb0903070806011e0807150c1110120605010e090604050a020415090f0f0b27101710080a080a030b040f05042f090c120f0103050c0108070f0810030503 66
    0x12200613100c040303a002c0e440c00203c001c1c005000101059898804a0249010342401580400400304059805d0106102400d03104102c02090780d07440441c07510f000b40c0b030000a6118001d94600b040c100180a41c042c00c40c0d010307031001c09403103203030107580b4401000000c05005150908950f8280008a120080c20100300000181074031015009414401da64807154026800341c1050142900248811840102507403060010807102441c0150300c441040344a0b0270080045400c13403c020000c07008103034010030b88402c420301a0101c000f19100d030034403104801c0c1c1502441c00141d1003002c0080c0042c4810004141c2c174009460002a041e041d140010203440c2d210700388400e10f64450060100303019603284a0100015079a540106000c0d14240454031142c406052900ca102c61000080c602d00302d0a04490704440e00002c1c0382e4040c90100350f0750542c12000e0000343c07a035100d803040651070b80d4001c8101502504494451103c085403285041b10303d00e60040c0320301030710110000c00000013041003000e007400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 960124442 1250 960123192 960123209
    0x1f030b0712060b0f0a02421308070f0f060f0e16060f0201090f06060e090102070804050f0f09040303020a0e0f0a0b031b0d1a04020903070b090307080601 67
    0x11030030805402810284000c2064100510344401040804100000c8804410034100b00e10344601d903900041e410035850138907030b980c108076401e1a013a01d04030f01000f40029414440e10765088540201142c01600b07000c48201c043c100d01082520041440c50380a01307035142c8a105603410002581c1e03941500c00400450890f041c03501c6030880c6003050514001d229480415100a000e046ca2210004116011901c1a0340074402c682003162440c500c01c5d00050603c0740c00000000c0110054a8060300a20301441241d669188003c04207080d000c041c0207c0e043d8541203040f00b81040d06003000c01c01c108000c2a4661390001985408400303e84601100d188a00c0c001d40300142c9800d1303400c0014010302021058148900c41909191150307644035401e02c402d4810364090345450703641c1c0c1ea10381c14055110b044992680b00000c01c181d1401000b43e08504c480004110b9080c18030b01ea00014003043e4010108074a600d40c001240501ca00c840c2d01e0042c04240000604030b865442d51100000d040450031780040740d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 960125692 1250 960124442 960124463
    0x30c0a030c0c080a0f02100311070f0614010b0f160b0906011a04030b01090f1808130f24050f0c010e150702060c030903070b0106080f0115021002031f03 67
    0x40c000d9840b10580140159000f0b00418140c40d030390301030a05a1494003c3c8101441000112228844da00c060300100030354481d0703956640d04e403e0003441e0f01707038850003228a00d040c40519901010103400080c100e5031304241d40d41c200101850640301076081031001380000c1424510030400702e521030300a240503002d81c2c00a003607254100a9480580b04041541c1d403025881080104005400340000c1c50450310108800136140c0390400034500038180e55603601c1403052280a80c6004e110711080108407407c04142c982ca29159141005c0c409030000d48520000c0b4000d00b029101000c4c102c80c60441c0d1002c3c149001c0d441c2108055002d02d59401590a042c3c00d80c0d91000440041c0c913080120b0319a0a00a03040c08442c0d1070310320002540c2d50300003844503004840200224004c28401c006035400d0641c0f20401120307668481c10001d1207150120743c1e44544c0b4004400008a00c18828040806c09070290b0240001d2150108564065400540039140108000007008901500002ea02000d184115103500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 960126942 1250 960125692 960125717
    0x14030c03031504021e0304151a060d140106170601092102030106050418060501140607021c1a09011b05191101020f090306071b02270702010f1508030417030c0a03 71
    0x1c0001c07030354000902022728156109176480540009c1c841c41100442d80c0a43d200004150007016110006840d0703d003090303150003c104039401401d00191010702c403080c2d030b04980c1c0e80401100e10341c520f44200b90000c1d01000c618810800741d101600c0b02c56001030008a2450f0380d40780807404840c60301007102400c0c21004c9894003082a1401100d00600e4140c1e01060203940e0a0000b8405201e540402403140b00e0091401c10303400041d252241c17410f0f40088107458915070002424036000400c48442e985541f80c0406800461380300702c0f141050309896a201800d06000c001c0c84403003180d4a4050030309000b8110805003a034802400100a81c1d180095190f0b07c2c2d40d59201450f180003000740c181018019640251003981c0051140001700b190115840a090006604203d480c2044110140001e020000400035034580541240c2c0c50b00511600402074480e01c4401402030100742d004001d420780041008004040c5d4940c401440c01201105517031626003500b0016140c8450b55804030040391340950f801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 960128192 1250 960126942 960126953
    0x7020f070501030207020901090c09120b0105040e030a09060e040209040f09020906010c0b13030507150e07050604060503010e1f150e09150405100f03050a14030c03031504021e0304 79
    0xe0020701c03083c2425800d007810f60780021429901401142002580c60151021513445000d04034001d00701045034840031406810b020400c003509000b143d01450902c8040307414900000103c40b00c4420a641e82d40000303007029811079050f1013000845501540074420317503078603a8580c03240031151404010000360081092040c85016a00200300030b051000c5140f410010800c0c2c42002a446040b540f242000041e903840d0941e840d00070094003a282203d4081c07515280e4142d0761050860300b02d401c00700c0d45010f0b51002004502d204d103000b503a00180080c40100990b10071440600c1c0c001002d41012242d8501d0080f41c03100d4401d0540c00b43c2811107095290b00c14a40e04042c6440c2800e0701596510002e1038250410404600d020058070701860740c40000444000c0e980c800017001d00718907800741d4482359590a0050303841040000550b80c90030380c034801440c04840001229800300c541006142181d440e1444110412165044203400940801c003c0c5026003484225480f1072241061301a200c1c140350506 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 960129442 1250 960128192 960128203
    0x1908060a06080d0207090e210d060b090d0b06031002030907090f181509020a1d0a0207050c1210020f0c0d0c080d09140a0f050609060105010503070c03020c030607020f 73
    0x2c0074180d00600b905520301513000c200c00d4292000b401d8042007480d00c03000111b1400c03c1c41950034000181d0040e01c084c10000c68030041c20003400040081c001c141c2c071600c01010502c540780a060340019104103e000041c500055641c1c0f00400900791120314409840b104143d0740201e49010035500214030034010007189103d26034940c04444000c10081000614400384180582d001074086445409d0300c045540c495080518200d6000d004810841e50325210303c0342078030040c0642000702c00c00500041c0c203142c0030b2003610704440c0c00200500d0b498044509000c01d80c8000301c807031245406031100c4611290380c1800140080f08143c071880c0e07901c440c03c0034407a08110300301c843d000801217503180401c00325080b8003e03242d1203e0782da440022600c0071413601d0010040e101c0006a40d5000c1d183c0d5a005200070896208a5540201c040c0c40090f81ca1107260341c0c80720030074020720380810418004540c03003d00c104c3c603010b0094071a00466100700000000280303001411a0000016480164182c203402800e102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 960130692 1250 960129442 960129449
    0x507050a0819090e1b1306050c07143703030c150e070612021b0303040b010f0f0306020307030b0916030e0f071205070b0301060513120816021908060a06 67
    0x1c2c01d100329030905401c081180b901600d030f580d170510391611560a84084030110340c0000c40496284c40390554a03000681503401910800e64030b4062240c0004c1c192003080003005a0f0f4200404440c018220a480c20a01c056004928a000829141119444442020f4202c0510302030340303d42d00d0b588000d1401c0e26030b81e101300500c8404541498030840302e01c01b0001c0c1c058140d800508100302103400e81c50756580240140308640740380403807401045220b60000b20045010354000d0074000110703a03d8001074004103d141c03240007002c45850004001288242c1c3c00f45402c416145404107460480500085590b00c00307850b800360b10108800000b403859058444c5d003500e810107038050058255807138001e54403074070103101e540020841c200c0300d502000070034042d8030050003031440309076260358541c80020550b80080d51549840702c1c0c00d00c4040b070448040b9980c40441d1340e01c00482d910b4a420300d00c51404007013000004907005a100307034000e100c401c10490840050524800100304d141340005218042c0d9078030351b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 960131942 1250 960130692 960130697
    0x807260901021905030f0d060e0901021905030415110a0e0301270501060806090a1407140402070510050901290f0108070210060b0909100b040909030507050a0819 71
    0x10a00d1141d801203882c80c3e0400e422190344401e82c0450402c182144201c0244001c0102c1c0041d9040441c1c91651244003aa0885c81c0520520b61b9801e482500300d100d04135001c0508010308060202c0c5c46e204900540c1d2081c8580344020482075100f0b4400d09846400d10342c01210f03680411004402a0f0020b401d040c1d40f1021070080c0071585050a9003420010845850300708099119000410312400b508694000c049400803035902d407804e107404540311002c03070900b15803c850b111042140100009041029078001010071141010908200002540104011102401012004c61060300d0070700c11700d40b242c100180085480c0040311181181c0c0c520f161582c2041c0180c0e62403051840e151080c5500301c900080c201340800340c0701c4a0059280070782610800c18a40d0500ca004213008082c030024206001007540c40010a880e00c0c1c0011104080318040d10517424400d00080100600d513030045103500703010b1304213545031000d50344506040c00c210010503962000e00064004041c210001581008503051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 960133192 1250 960131942 960131947
    0x501050a061809080712080106020f03030106023a09050f04140601050a05040905011805070305060102060c0f0702040203130b0105031504030e0a1502010c0e033007080726 75
    0x584250032910702d8080c0c440802d5640c1c035402c0c100b144010032a400385400203904040320315081070040000009001e1000103004041c1d00d0540040008240c9061380e0864000e4070498001400000741c003c0f1402c0c64420340c10829614003007400b4588484120700c0b5243e51404011401d18092152000d02c030311301140164500300420b000c41d0405214940c004000740390440e56a400b0000848050203182c0042000500d0a400020f601da010941810f1100800c44d091042e0340e01d001064040b607070202c41c00c038050307040207000940e003151043c000c02800d199240d9003800c00545030045812600100c624000c80d8113049411000d010310303402460300500c011001083c98111490362070054000241c00102171200400001c0c04aa603011035110141c140b0030419000f40c1580c400c0240640a481521008100012203c143c01e090205001048002d54000e1044900c20b1380b00c1b0303200600c01500d500c1c000040c2800b60704006400c40d4010034100380038400c2e80c104003500b0740c401280f500c1c00c42d00003500581c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 960134442 1250 960133192 960133199
    0x601050307060207060e190f080a05100504030e09041b0b040519060c060209150c011e181716030504080114070e04050601020a060c05130b09090c18060a08040501050a06 74
    0x11000300b18906c01d0650740f00c50714200210700a403aa074140d030001d4050240e0607001042000c800208082040d018004603460340381081042c2040300d41c10b07a00500001c88100d4050900d007068986290440e100d5171090050140e042c01c2000c084d02c658010307116400000030b0401c0145030905030081c440c14400059203140d0315003100903081d0401000b000700215004548148075643c0c03440e1003400c00c27506003801c1c1d90340c1003240e1714603000b00030319140040c500000740d0411074400103510403a088801c00b011611145849a281c40384d540054901e540c13050b90081000c01049182c0c0305640051900c203494480d1a14203188006003510507004515281407600740c104424507a1105004071541c1c000e403000111a140e05004030b0030a00454805442d86041101882c00780e58404010a8449008100710300081c0d100c00006081e44a944191980b1203104004101d494211600030310b40ea6080340010f002007075135100441e1440d0400300f00700340801c20311800c200a1007802c1c007038075912201f00b07402000040d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 960135692 1250 960134442 960134447
    0x5250504020c0c0d030504091107021206280e0a03170f090a03050d02090415140103050603030703030b010215040f030e19060516080c0303071418011404090e060105030706020706 78
    0x1140c80403e80728407007501c055000c1c14005c804840c003820750002d041c4100b0001e205880102d910012049000e8941000701140c01d4a0104429004090001c0ea145040307102d5400d503100c05003000c4119510fa0b070380b030032501c44a410400c4060407a0b80319454011448420003603808021200902981c5c440a0b01820424803802c041682400c5690605085441e250a4080c03200203004000006070410305e0085100c403502c1d98100780b41c2c212900b6031030b000b5481c0e00c41c0d001181621420354038180c05900601406c000280a5040384000030010301c1180c4100d41f08030b042441e1440d090f54280c1c3c860f01001091018580e00c502c1410040b8415264200442d0381c0c0350306402d180380d046c4500020880041010610392940c551030248050b00080340c29101d5820564440d1640d0065501001141481d048030740c00c102d4802c25245038243d0110031b0808005031a006540500070010301002c8a2001c11010480946510070503e004a441c0001c100f44d60410381810720b00062908010305640c0291000c100351036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 960136942 1250 960135692 960135703
    0x6030c0614120f1305010f05150402090109120807050303010902090f09090d030c0e03010e030405040e120706020d1d0a0308060312040306110c07061713020604050108060d05250504020c 81
    0x21110040c0d440d5480f050402c02006500134001c0041d420320322503101c40359064220f50f0042588613141c500075168081040b0403485480010b0b0301240d4210003c01100b4902e0402ca40c0441c042d0940d00d20b0310403da40c0341c90a43d0b1007600300c40c64082e808250946d4034280555200e07038081c0b0595080c0b02c1c86c180705200b19030f6004104145410191210341d609480c0d071040150303204d0010050b009112920304180201d4a94000c0d0094900036460718040c4940b4820005d0000514100548a01c0c600300043d01c030940a50b010740d1942c260140c0314103614141c80381003005502403090400c0500130042c00391400500e489000342506100b40c0c013003941c20a45100c1c88044400b00c9521810000300e4000b818920a000c0c0542900a0254050454001450754000081d20540ca0015503594541d80e070304e00c4240840f05125001035040542404240401d5000c6c6541c2504620700411210700c0341031964580c1d181011644460f81c134103003503640700c904a081d540350203409802c04075800d40c208600d0020309507488 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 960138192 1250 960136942 960136951
    0x30c0b070312180218010f03080c031201140405060d2004110d0c0807050705070506031e0a0605010f0206152b1b140310051906030c061412 61
    0x840003452108050245940b46402d41140506000444001e02e034045520700c0d03110182d0080e510100b00c050356030032050b04103040c0c40501c5082407805085446c2ca407601d41206001140f5480100040b04d004490340c140d035030082014050b22401c40141406000aa402c050000c40c01540c880b000500010305035007454114503101c11000003084501c0001070003900e61f000411360000320003e07400413225031541022280f9801c68495844a0705e1b0b216003150184201c800c042c1282e084000140050700d040f800464010100000780364410340b070030b00e0209421006503001d0304e4541da50304e000c11040d6000301100c0e01c07400d680d00141507a4a00190030a445010100d18680308105441d40c61441d059840003280c0126440032a41480301da5030b10b000c000b000a0780c0b0700302d0404152034000080101200740500414003014000d000007400c501d00c4400505030240c01a144401801d10710440140d481c42034500441c080c3ca40f102c0d0a5103080030180c96440c8200d01c0070307001c49040014403035892200e01160b800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 960139442 1250 960138192 960138209
    0xc0109050108091e03070b0f040c0521010e0c01031a01051204020301110706060e010e331003050609070302070203070e0604020f04061709281109040302030417030301030c 75
    0x5980c420f44103600703165051540ca200c0d0032201c0714204031030400001030500a4410441007001d901d801000170030080049a00030443d00e02d00d482400141410a142d038602008180301d00d08400d2000c0c030702800c0d548046264412640041c0c000092503905010310014a1074404a19041c961200b000901903c1014040d03e2843c00e0000802d0454500350f2069800d003510181113920b90700d0b03500c0c142019200340d10640301c5d04c2c0d0001c0d002180700c1c20070840720741c0122801c0e220407511240d8072560250449003401d07c0c0b007415800800b08a843d85a42600c3da02031042940c00150394907151042000c44800a458103003014030501c80100143c40000380c00e0140c4903e5101c442040d502ca0000901170b200e401d201400407040400d0000d000c3d03800500d801c0b00030140d4817a590603903a030f0100560740c1d4441044400549103a4000c40f50281821194841c0c15602519140e504c006442000c199000401c0d10f08030b006a0002404102220000049503240712120025600e903502d55104e4000c2407034180a500c42 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 960140692 1250 960139442 960139457
    0x80a021203040312081608071d030718020a090e06060f0d180b1909020906010c1a1503060a0b060a03050601050d15140604051e180a0f0e0c01090501 65
    0x49418040080c0c600441d40134108141640a0034401408002d040e1604080d0651aa05c4200d20714002c0481c103100f00d0003983c800d02c0e201c00c0d40c458403103a400580303092a05030080c5034002c952a5a02c3d02c0f540c0208900400c05030395a41c1d0485c00038060001580821402c2c001ca07414003d05e652618203d80c100711000e400c00c0c0d110301584c44000000c01c2d011058070510110069200c0400610201080c031980a24003034001846111004d401520411040294003408000011f0701c00e41c000c00050401601440c50400d1000006a160b0340c0b050080c1d40b100424007031040c1c0c0c0529860708100207a0302011001060103042c1c000c00c00b04159015080d1020203254941c1c0021b08140d04c6142640c03c9060740348428130024101d0030007003440c04c13458040c0c2581c5400c140c0706003006040601c11141104d0020f4a011401c0454000008080422814566000e040c44280d010200c880c54502402203c0380f440c00607001000d42407032001c486464014000642000410300c009a81044440b02110403c1c2010803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 960141942 1250 960140692 960140719
    0x2060c030c060415051f09150b07060203090c030f0307230a030e0f01090e0c0717070308150a03110103050a020d090b180a0510020d0b0d030512070801080a02 69
    0x500350700500100c54014030a800400080c00100051910381200710b1604024035159040b005030000c078050014940035007101820417140c546a0301828240700d06d48080710b02d850b2a80c00f04038084c0d02c240b0b0b0070ba8481e9000b0040c4045d5070028401c0180a000890040a9000c804100d81c0d0300c034024070501811501e41c0c920b100b1f1400c607001031149250204082130f2010100c0c507103000340003544402c0d00b2500624000e2164402035024030500026680320342c40c191115501c800100000703030702585045071840041043c00c00b000c2c02c802e01418015103c4c0c0c54441d80c41c64203038055170300a40001142d61081a07080c1c42000407449140040021074030070b2a0200703090f65034201d120007170300c01c00781d204c09424513050009c0140910040080d0107540040d03c101901c042c2d403c400355031002c00c0f1002910a4000d00240c0d401c10040d0350040400c4140200c000c241400c03010001400f5840c01c0c0401d8022600001e014142c100c0036402d03484c2e11140d0350404c110503504100709070380e031703110020340090248440715040e6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 960143192 1250 960141942 960141967
    0xf02060c0c010902090a0c0216050a2322050721050702120c010c030b181f03050709060806070309120c0215030c0901111b0d060216200307120206 64
    0x995160b4020f4440070705030a1924409008047e0041c110740140a940c603515108005280000d0454400401d000b91041c2404403d03140c2c0b01203448107101c5520342c07007505000e03500d030520312010208039691049030000c40201c04c5401e07900002e000c1000c010703a50710300d000300d0340c41c9461131481142841b80008561b071b14000c080e8585104c55500b0355078118081000c4500b41c105401c4440300c40180c0d40c091050100190520000c560b484116420402110002a0203645c184441ca0340105a40151928499480c2c5448ac140116138004c0c0d14900e40700c1c1405d03c031011003041180d030402c1c1c05203000c100e071750019115051510084000c5504104c180d451020075560342c0341c0d000704503556440200395039040c900000d08842e4000c940507404940f414540310707a1054003260f000c4100c8612016880e0752004401040506142d032107046a91030307800e1048044480b0020408440c030382c45403104d0355071141480144501d00070741c050710500c02c0e03100c003809202154108010071425941036030b0041e07c034201d21102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 960144442 1250 960143192 960143201
    0x40f1e020909010b150403020d260a05030601030c230a030e0106080105040506010f030503040b340c050d080d0e071a030a0c08160c03030204080109080306100f02060c0c01 75
    0xe544840600c082c05201c60b810f5001d550f41e42021030b50580409585081c102c1e9902403480080c2d4803052a00802002c2140d0281d0400600c4002259a07100c07008003660088940012001200050002c010840c032035030507121740c250000081c24484520303201001901103808c3d00000d600c042c0c00010445002481c0660044295640300c00001e000958071004414000d210131a4291410702c2040000110b100c441c2d0840300c10380350480e010318541410700314008110390146d0081c549204445c1e00f20a0801c401450280d0348980ca00160801c0c054141010000c41d40c0e40d80180707100d20410488000007032100002c6800c8400202c40101d1500702c14a601420701903070b1344c00030b103041c059100c0902102d64110020b500c1244c00c420108480846078070111600b420031a04d4074a000940000e40503911b0003820518451442883d0241c030701500d803c104c0b03080d9104440101ca4415020041c05001d142031002c1071164910352511400410b04080b0082d9551006400883c2c14000001c0c030040c601700a400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 960145692 1250 960144442 960144503
    0x30b060a0e0f0a080a05060f0907090c020c0d05031c06062c1f020114310c0611190203150a0204050a03030f03050a0c1e03140a02130905040f 62
    0x951100c113130766500881d45034842c0a00807180f5015010000c0e6502d41d181003014015012000202003080c100403200b401002040d0054003940705003e80d080d80c41d03031000b2045a0480c4210041d5446d1061500e010b14684101a1050051410030034180304007070340300011060000100c4500e5503511084800481d04180185883c1e8000c06415040a8120b0007090344e05088903090b0300802140303116180c52110b03414103841e402c0308501c54448c990716a01c00d8855510302e2142c40180f441900d94107980389000c1840c1940994085200c44180f5100168280319038204144800c05140903840c5942c00252503141182601444607000310124500e81d4041e4180c4014010181070603c4554413070078007804440410741d907040040d0400d0001b4250780d800380070349141000360780c5988070508001582c0010340410004024205640c0c0c0860740031000a043c2482c0c047c4011a8006076101e0319448008007a0b105900190030050900060000041661030b100920300d8101d0151940c001d040340006d42030194410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 960146942 1250 960145692 960145699
    0xb06031c0e04020f0c0109120507021f170f070f0203030c090907090e0c07022d06160606032a210623180d0e06030703110d050403030c030b060a0e0f 65
    0x40391310030b89030f0547c001c2c00c140d4000c00e40807503080242c1c2c008440a1050f40b2009400c600080344c5903905c0c2002c40d600c0040040a0704208002c07803030703000001c00b401c013040b507800c1c18400181f014001e041c1d42140035200290f182303201561940c9810282c110162003525429030290240c13100154000d0b10071a00700c0041c0c0b0b038550fa44c10660600c68805801504000c6040e8828160314040300003403145044000130034502000c941d2030402c0320740d0410486800824100d4804900806054009601e81c807843c809036125505032102081c00c09012113140342011041ea024000020003030043e2822007440c000c8103144051107030042c811034a0010b0103802c0480004c50401c4111510002c40c41c0b034168541e200c0d80801078950700b4185030001c010350741d060601c1e4001c0030582070310100a01c7d00f0480021a4018128140804e18010310040c055580e0300c032074104849240d4907001d100c00c0592500805118038621301e03003070169103240300014100e8821001c0c45003d01c00b030101c44158680718040c800310500e4008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 960148192 1250 960146942 960146947
    0x15030405060f0a0b0924030307060504170705060c07050106330f092310050a0e0405070e040519050127061a070501020915070b06031c0e04020f 63
    0x203252150707881109481c0d50b4080390046000900e01e000f14441d0110b20764005010114540356403070079581c0000305100c080c1028044002c5070380fa90710100000c0c6003d03880740c0d9001400c4d05c0c150510f0240c01079402c5c1c0549540d070301000214081180020f00717542208246003029a500382e940b914038010031039a48180b548140503c015444848146151060410b1020b07200754000c50b9001c0072941075008142203404903207201c01c14070103030a021004030200c51002c103030900c400800f10b0005556015411000002840000b01c0100c42d03a4018800006c185d005c1e01e0901040c00c0ca142d02070103004030540f4540c091035413000046e0440952003045492480c8084c000c10035540c550040d00a500004008142d80020043e00c404140d0301c0784c0700e00e40807104154000e003007407249071041d03640c107510011040e1260f640030302c000080d59551203000b4882c2c213050101c2a65a103650702e8004943c0900410b50b604c40d800032103000c04048070700c0750040c0c0101035a24004c0c1c1e04251030341c0000c0090203515900c5002c114003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 960149442 1250 960148192 960148201
    0x170309040c0e12070f06050d0b04020f030714040303080402091f0e010801060e0f01030f05100c050d06240e01170c040e1b0711060403020402030f01050a050d031d1503 73
    0x110080761401540d01840c4100f404400300d603941218841d510044100c4541006100e10600242100d91000ca0340490ba9040ca040002c0503078001040740041d1398000400c4c407410540144c0b0384559000e1090400f42400c0ca0340e00c014007014002003001c0c1c0920720036030001d101c50392169004a204400d044c070400700c1e1a00d6800806002100340aa443c540d883c1c4075011540e8041c000c00c0c2845544410080c1100c0d86c00c50b92412030310850180c0880326817081c506048001c030381502440740e01a0b410368a654135100c103181c0d2003041d144141c0c0a245001a40b500880680c3d241c100041101c107114100031404910b42c400485041c049989403c071500030040c180815000d03000b004101b200c00c0b40c02d10501c16101d0000f03040d0801e1a190521913a04006c005903000600ea44460308075417800185107e08061303603600406d0036a4400c0b1000307070490351181c005000030b2030300c0b440b208041e000540d003c2d40c914600d640c029103aa480a1890440004440f60038225a900e10030078aa000c59441415520780c2403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 960150692 1250 960149442 960149447
    0x151e03070908150c2809030506150d110a030819030614030d1d12030d0b0108010806010e0c0904020a03140705032e03021c03140310170c030f1501051504170309040c 72
    0x1180c2c00229524027070341c2c01058800c403480024803030b42e120041c4414003c0d40556256070500382807038040c0d5002034012000001041e0f440014028120801c0410211361100190050031500da40e04440301203100302c1c0300c0c0b400c42d03240010006949981d50420000e00202c00000000042000f64115440313a4050f03480d552440010002d030808540c0c1000c18070a450341000151803001090003400c00d190701c0140100014003d0300601500600850561817600303010801007003ea90007402c08902194075a06100c2c0c0b0641c03004005940b0a141d86081400c9d0b090142804502c040e410400d1040d8078280014411034085024924009640c020441d440040c41001c2040300303103001c80700076004101c189070001016449902161f104e11018003813000114104181c15402031040150395069208412410b40d068404100003498222404020404006500511003500b0016080b5a02800140350003110788541d0340301b80e40980708590708140807035403402021859400358010250b4403e040c0b00390b24103840e8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 960151942 1250 960150692 960150707
    0x3130206040f06031a0d0b0a0e1b01020f0d14280c02030d0f08040b070c1416060518010819050109020a0f05030403090302151e03070908150c28 63
    0x840f151000c1c003045d412581c01e080c451018010b902d42180c500710078500003071425080d1680c498002000003800c543e0303e640f13061411545d04540c00320207450402007030b010740e010407486442580c090020128510340d22001003200d02c0c03036415041c0007a0045410a40b5262600500389014000d0758a0311044510b410002c10702015160280e000e4010403003001e8500b446003640071202e0070309440340442a25140d91390140c012000700040b081180a02102c0d00062903c9106101c0320304103c01400340c014460402031000390f003030740050148036041088024014480041d003000d2042400c0c405040e940e92034000107035045401d0854101840c0200104401c11141e0113880340090a5548020007103483e003041e51236110a560160228510a07010001840d04a03d009090035401c40d80d20f003042c290485071011045403441c1d4241d1080080704000206a03c14a500000c1030542c0061400312140301c46840b602601a1444603c0b02d8001483c507010b118180300f012002c4048118440c3c00c5000d10300c001c0100c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 960153192 1250 960151942 960151949
    0x14070e0a0624020c150c060f0907080a030c23120a09060815090a0b040207420e03072102012a270e042604050603130206040f 55
    0x5440d001005903070900804803460340d4140d0018504000130404002e268040d031501c0b281940d00401559444100c10b01c00c0c0c40c003130682c050f410982c60920380300e6141080099000100e80b54840c0c2081008281c3c017291814a45801000c148110713170000a262070b1091590307400c140d99100e0360200f61b01941c0d401d0010311450240b941c074100801e0325210210740095059a40303e0846190180b03c01191420040454103c2c0203860b0001c0e440300c403c0d01140030782e00b0110040d6400603116482840124000100444414402890300688090b400160300b40800074410840ea06a44024140001004200b00c2c4d0780c01740c00017050030154401c4410242e0740d9002e1084030006500b80101f002c08a10401c3e5608000c1c40d1841485500015014048812034a01030040c80c500d00710112145241442c800da85000d01044807071500307203140c030341030040300024009010505c0714245440d4100110f2090700b40c031300b5290100d8060355683c07030301e03044243c494480c044003030b5006500080009040c07c02d040c421084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 960154442 1250 960153192 960153209
    0x5040c1707031209061e171905180d0c0507050307030605011503050c0d0b04060f080d17070912020609120304080106060e100302090d05010c0c23070314070e0a06 71
    0x95030b4443e403085814101510a07040480d19401068084c0c0011048030211900107292560251003061003442c5401c005807602d1041148040004001c003010f0301403994424400007015903440071281200340d60b9170a003041c01d02003143c0e00c21081d0400c1424084500108402002c50f80a1510f070704000004040c02c1c4110051071500d854072880182c02030094510481001040340d051018003016040685004080700740d0041c1e4411001c01c1c8000f03000c42c0e000c0a050040000d0000b010000c2c0060540f4042c032694000c0e0241000c10000f0240c0c0c8000d80c442501e030048000c2801000350300c080f650301d00490036401d41c0036508404594010780004094012948450000d00c10280e46078810f4440103942600503030080802004400c145010b03400900943d0400340540007490340b6030300e0309400c490340688540001915415030300d0a204000c00300c00200b80e400b01102c000303190650029a40d4004500c401418485a81183c02080300c0c1400b6800040034070074041507840c9000980b0b400200202d0151060 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 960155692 1250 960154442 960154463
    0x90111010b0a0b03150406090e01150e010312030204090234020303030c0c0a0c091a120c0d0204110a08010f15020d110a02060c01091103010b0a0905040c170703 70
    0x410800500581041c1c41002d044440e0301d0781050800322813540300404d440c005066801da42d4405454034030031a001000d10160024001d84035041490a5400b003500a41410b214034030140100d6152031455411642d202c0d00c00141c503010320b4021b5011b1300480d804181c08a10100c1c42120f0f0401c16003912100115030b840341c00365110810341c00c00d0f00c007100d4900a9019807050001038185d81440c0024034614241c1801c44001d6800c0c1d0b07950300016007030b94100464641e1224070014040c000b0301c0c0700000c0d0300c01c21107000d580807216446081d078034030481805034418046500d941003951250750128030143d4004806a54a40c002d0b02e01501010003882120095a1200300001c1c1851108004a000e0400d640c040c004aa042c084103da00f100d1810303849101c2d01039180c104006035206070042c030f035070441c880002c11440c042d424031910341081c81e20042c3c040e906228a00007180d03107580c1c00300142c4040050000e00e648807810403110070310413508101d030302594480000e40f80550006200c01101d10a80c503814 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 960156942 1250 960155692 960155717
    0x1f18111201050714070c15170c19230d020405011707091511060708150a03151a030a060506090901090b0105060a03022a070e010f0308130306110901 65
    0x41c2260b90031610f440c00104440c10400038810040c2c01450868042e814549009450301100c814400d0303c1c0b5205400f26512059030740c0301091950820368402084c03007a1904056038082c42d428440c140c8a40c40e82002501c20741100321425441a07942d568481e0340072182c17514641440c2c072000758094080c841c04100300f00a40100b00c018501000c1c8a104030343c1d11403e800f8642202c0903180110048148103001140380c00e40740811003085107910402e50b5036100b1a990900b070300341403260301c400d441c40c60045801000234004101c1ca903141c2201c0140785003000501104140d491046c600c2d500064a5040c09901c918105002c140c2e04a07c0c0204000c035101d40a54890742c44040c201d51003184000c1081c1a40320040210345400405003140302e04a080152070b00401d60100c40c400090101c0181201d00c0d0300e228030650072000c101c0100036104c04c245d0341500d0350400c00045504103003803100520b00d160029544071030382c481100310780c01164040405c2c0a0b40d60202c0000810f50054141d140c00118052540f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 960158192 1250 960156942 960156979
    0x90a1a04060f0608010e1623060403050f030318210a02010f020705151003050607050d0e0a06091b0b1606060b030a050a0f060509150f030d090302040f0e1f1811 70
    0x50103c62440c4000030f490b008d40301e02a00141d04400c1503540c045800e000001c0854828410030120003400c001171503880c5003200305152110f88405031b1648540c012900422400d5002c1e03032043c605000c40040d242ca0b894001c0c0e00320702400c03103501d100200d240003280c11410850009511440000000c001d41c0c213541d039280620f041d502252001034010307070120011070566801040101009401e20801080c5003425000c075034a401d412a4045600d659600400c0c1c0c14860001c00c1c2201d1a00320b003000d10005482d04107600c02c10b0140505800e44142039220340000c101495105e0001400e400210030748070300d040c4004030000e080071500d4030303821b40c03e1406007a50350706d05101d12026075800612102c1c540d11104040d001411900d035880da084500300d0710780311040e0780030000c01010704030a81d50101c0c2c0030700303500c14081902e40c90345520b05100c1c24074149001840c004500b030f001c04815004009100c45a01c42c020016205c04040b02440742c0001c41c500d003e1000360702c00c40c01e0394007040d1904000294448400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 960159442 1250 960158192 960158233
    0x6050105010302131e05090c03041502130e0907030606081b010504060f1b06060b210103031e18090204031e080414040204030501050c0909090a1a04060f0608010e 71
    0x1a146080720104240a5445e0204680c20040da0701041024615200d802007440d101c401d44070b4203c0b500c0084200030030003005034079105510f07041400c15400c101180a810784019514019142c25915182c00140000010003023030700159003004060125550303c145203500c0d49010030014004000054110411354015400c0b01c08031009a50f40503000480d00d0b204441200c409000b03480c0542c1d841c0c2c25400800c01e280107c501802104040a95a03c01201024241492039207440403509a400041020a403c000d40a140d0f140501d00462064600002210048038031004200c8003810014080307668220f03035018100f0751b0b219400c1001440328009032020300440810700102003420402042c04469080099800b0b04603000d0005800d0584941c0d0306400c0d80c001715403c9550741d001048048043c50840000c6401c1170040d006000d144285850314804800c0c00c1041101002c8040701280402200d58041240d462600c2420442c0c95111444540a001881003004544c0f08a610b03510324002102032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 960160692 1250 960159442 960159457
    0xf300a03031d0c150306030c10030c27030b04050a080301080c0a090504240b0a0306140c03070219080c0105180607170a09030c020a0e06090c0405100c140708030706050105010302 78
    0x490549881404c84c401041d600061051b9014012404842e045455050810410707400c251402b00310150b401000401107201115aa0b4015116070803183c25213001d04180c3e41900d400c040f00e10702a0b50303141002c4d441d080c441c402c01030254200000000d803440c4049240300d19104102c45806c00a0754540f00082170300e00c207440c0909820750000c03a840c03801552416060804210000100d051011280011100071466105079a01c2c0d0311a1a0485010042600242d0180703091008078118105048020740d52000400307010307042585064180103110307150003a605000034035002408280f4083c40c0220043c50141822586c0d88075074070203e2143d038000d80540024040499100c2c583c0d9403200641400713420900410380c1401002095580035807115410784025201c90f90b08400c450500c0300034003e94a0000301a117848071001c0c40140000d035501000504889120304d0590403c14681c2010011000316001803c4203108280c8001040503000c40613018003030213030104004980e6500c00540582c86800e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 960161942 1250 960160692 960160699
    0x3100e1f090b032a040207030e040b0402040303020a060b010516200105091c0f0605010b040f080d0813052a01080f010e06060d060f12060b0f300a03031d0c 68
    0x401c280300e600c0f4818110381a1610081d4201308083e10201080482c0e10010b0140c0005100d030100c0503240c00e15000d01034241c0c0c1d0968045140a01d1502c00035103903002180c0082800b5151030081450303a208205682001400503108200004e00e807401c26014160203260030084c03500007030804c5d9550302820550710b0910001d00710106450f040307003841000c05841c1c00c00f1240c01d000e050b00305020500c0c510400d8041c060010607141d0321414151007409801131035009140c154084041c0302c005a074010341094001c80b502c0040e0200074404d05e006414510b9111000c0c100012840503070300e80c41ca141d482142e41450a8840c0301690310341200b100024507090103401d40400380080807a5541c10300c04001d10840208010001c0c2c41c0792600002c0c440c5c02d90962058244004204d15001801641d02c03a460400303034210ba440700c0114076440072804425809072506561008051024000c495031001c40c40720405460540d0000d410901d0302400801e0142624211034015104455508030000343c6903400c0c11009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 960163192 1250 960161942 960161953
    0x20613080301060309060e0d270f0501030507050706050c031509010f031416082a0a030809060c0313080c090c0f03060414040c090b010f0e0603100e1f090b03 69
    0x401075010b8020110200c94a59907081c00b2540803000f8807483e500e941231581d50000e00a10318840c81000c01e48980007150001c0114010800c249541c80d9040c02c0fa00d003802c000c02c00d542da18006a0b01400354210181c10541040d003005070000d041c03802144590b0004407001920320604051141301c1209000304a122880c0000a0020400024030510b00254075000c64003a03035030f0b00c000b011101c1c070070703a001c4600c550000e0a98449a4040300c240140a103009100000c40c41007c0006087c160880c44090003151001810ac0946e031251812580a840e450b01100d039a8a01c4195545100600348141c01c007030b0040c0303071180307801c1d2400365443e50041068003002410318400c1c0521101c180d001408052340159140c440e50504024214924070482c01242d1000348580791000a60540d4020620030b410003d4902210141c3c540216072007055035004d48605844e036940c00d016501d03038441c0350004c00100700d0380c40801403440e00f20407605d0300b010399031000c480070b043e43c803005002519688200c0c2c0380e064000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 960164442 1250 960163192 960163199
    0x60c0c19020a080d0228120c03030204170a020307081603060f180515010e060d1401020c070b0c010e1209060c2d0105090a03080c0d0f0615020613080301 67
    0x4000311000c0c0c140002c14100c0d2103540c0f000c0385840e04600e51008400358011251540071a01c4200c60056080c0c100041c504900b040c5607100c00c90780008003420414461600b5174107003454841e0741501d0140000c1865203a606125400c0305654008510041b4424400c040c1c0c0032071140e0340410b01d4100a1102c0d81c010549606640c0c500d0040c00920314901e0b45540d41e041d030900d1247e404001d128080d405500608600e240003003940c6c11001050704198210503092013400003a45404140700109500000310860700588440e0351030192080c400c20421501ca0b40b140400d44120f214000c043c080d114100030030021782d41c409020b0300c400d40300d0032140301447c0a203d044a41c0c01e0590084c0f02000560096904002c0d015050050000d410115150352148864020400e65000d21666401c8a203c10085c0f004203800e0341c000b03010768401084000c5140021a495080c0c40c029002160343c08000c08052214544400041440003d16204500113210300f401040403803c8008191000b5900244041e1a503800e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 960165692 1250 960164442 960164473
    0xf0c270f051c050304030b01090515010e0d030e03151008010c05040311040b04050c0415081b160b04050607030605040b0f04180c14120313140609190602060c0c 70
    0x81e4040e012940e02c03a800400c0300044040c0000d102641c440d00020199505000143c4215440200190341550b840c1c80d40344410780c2c02000030880c6100440390740c41340c101d5520301111a4110081a282c00d4410301038443d00f620100356155225083d403040d02c20507142d5540744242039504010001011031410403051000c980172103803106145a010b0300104481307440b4004542110f40840c3c064100150210302413182120320462104400c032240b07484080c905180070040f80710071950782181c5d59100000707844280e0050001c2c60001a68100c1034100040c0f4041c02c0c0a03458034000c413840800039141400c0400d8501d040c3c4584901d80c07101501214000c845941404000c101000079414081e80c880200000a50418041d00152202c0c80f054209840b45006000e500d0304c8511181d00a0b8009000564040c07080103000300c00c0b0746440c0380006000f0085004660b25224159105800c402048100c110f08403098803d00111441503003190f05075521140a40344a000c0c141881000e074101031a120900e10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 960166942 1250 960165692 960165709
    0x708040213110309062a04121b080c030d031a04090819090302090708040b0f190c08062e080603013314060a120f0c270f05 54
    0x120880307800554101512501c0c035058204031090501035100c0c4c020462030320340786102c5400e4170342c146202034094850010500d06501650007103800c081e020b100c0380414052409404481d03000108400d0980540301d45940f500c13001c000c200030303009100740000031940510a10030154902803089061410201d41010440544140d00081e10340c0320303041c0107807840c00740580e903c843e200d01251103100599166105100305445e00400c03080c240b01c140c408110200354030816a1f03502082041030507480e0342e0754112154500c0036140d515500c05140118540c004e540100129000e40300440d2985103030011510181e960000075001c41c0c051281c06003050303c0303960203000d185812600090000c05c10719507001d000c074141c0580601050000480526916035000e44030342c0709000e821041503903010222100c02042c41c0c0d124003101c06080064900922140b543e1581c4501030340c00c4440000d0080c41007501c0c0042070300408040d01300340c5600802c40780d8601c0c0241d015000440b4807240b580120103103020104040c45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 960168192 1250 960166942 960166969
    0x1b0317070f0222110a021209030a170409090308040605090604020f0409050c090c070b0705041a0a020c090f0a110304201f051306050702031f0e01020403050a0b0f07080402 75
    0x1a52043c0140c48402c0c0326000b01d0941c0c0c0c11034002d071525000041002440c0045000003031885590401000c0e54507240400c00d4800c040d088907069149584d030b1000400c1a2207260303c4414070614041d60380040650104c2c005010f43c2c010602805941c540303206060321450107990080d40444425401c410138105078000300f541da4042c02c1512103000040000c035071b021504844400c01d0010000d001010403000e03180305904001039282c0035080509081c981d050032107042c00204002e00d00410001c8100348204800640050094084000d43c180054800300b0100d00b540d070a14814100028100110b4840c82600d200f40d030803540311601121144004591401500803490b0050004d01003800e58103040527854a10000580d03d15640701e10034406000382074480d03000a4200141008544007694000030300d18050703c3d455038510698002210703600010444240d5052040d40003003400400e0110210b22803d44a001d001c0400c550381d6015900c200f00c80d8112411408078020b0408500503007803482810700714 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 960169442 1250 960168192 960168229
    0xc0d0b06040906060b131e26010c030e010f021e070614070e0a050a0518151305010f0608010e0c1804180515011503050c071b0317070f02 60
    0x100b0606484210984245402404904070009500c58440b250918114003c02024082d010709110110106100c41c009108110300020900c100d0006010540048407001400200030044000c0c0c404015000d00300d000240701543d440c011182010078518003ca5442c015070000a801d8100800c2204034947c20951087d80e0b011780e181500900086045482c50064003e0b0700d1310032a6089150404c4a4070210350005401800800700401103521100c100001450301d1501c840d96940d192074141010982d4001c4665105131008000c0320108007541c80701c1d05940881d09a01c0042e80c80d05070980c1d48140c203109400030360300b220740050340022400f406826110816800c842d181ca0003c5c00040607641c0d046114a82103170000664010410104400c1440c60003800384c007900d641c9055400c0c100750000106660515403140c0015018441d51421a442181c0c0090b801030300700d140120407004801c00b404201d0b55442c40c2540c0cac150b040103031429214002c1d4050060700808000c0da0034040000d5074118040d0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 960170692 1250 960169442 960169451
    0xd111003181403121008010507090e0a020a1404090e010b100f0c0305070615260c100c050109050601080607021c030b1f120b1206010302100c0506070c03110c0d0b0604 73
    0x2080c0d00102160091601d4150305d22880d04101911703007112009000c0c40d05202031820100044ca18069100d50304c00c0e4900c0005844201c0c0b41015070b450b10001000851a002c00100451000d0250b8490445206154000c0003e240c41c101402148813500316458003050a03145001c040e90700c1904c803a03040380d00c1703441c00b05e0400200da940d12007030390f0061211840b200030380ea5003401301d0010000c10035000150410303c1a8803190780d00311503807210075202c051801210480d140c424038030300610031400a164004001c011107c0d1504020740c1382c410a008015450088101260226100299000c04644001049114004442400d80041c0f41c007089194200e0324800202c44482c1c0e1003030940d0380c40300070341d26002e04481800caa01c0044643c0102014411002209140500b880024203d419241c0c1130720780b140070f000ba070300d03064811884c420801030039031050800300303c142a03000004400707840c400c2c1c5407220b1400d401d5580d1515402d01c0c40e612034001c0da58402c108003241c100d402c002d0f00860b01620014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 960171942 1250 960170692 960170707
    0xc15090305130602010509340305010b040c0f0903080c0f0303190c18150908010906052a030a050a1b0e0f040c17060f03160e060301050709180b0d111003181403 70
    0x50804c0230a81c02515035940d02c449106d020300f0a80610880008945405c0703982089501e000713007010849010141a0290200300c1c8041e06104000d058190f81d0420f0481e030701d1b807501b156800740144200c940741c1502810500341900310390041740d00c00c10300300030518280b0207e810440303900b9248280703100000400499840005641d01c0a124044116010340070200d000c1c5800080d04e0b038901c2180341e0140502c1c0c1e00c0007485200e100e200058035044040380c400491507440304100c1802400c05010100701c0559070801500465070050050321217003030180c1d07609011210640402085844034025800410040c0301c1a514078290405460303808400184441c2560402c000407d1810201d8000206810409038040c02240203041c2501c2d44210100c000313201302d01d04800c0c0240b0034a00c07403084c0c1d2100f4030501802e42c0114007a40108409034006040c8501c8501c280c1002c103614041d0040060103400b4484510401078442d002e240340c00d0a8480c0c100c15a228580c0e65612000b80c3c401c0072405a010a01484 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 960173192 1250 960171942 960172033
    0x429012109110f01020c01081b1b0c06070c05041806110d050108010b0d1b0b03040f020907020a031407080c0114180a030806010c15090305130602010509 67
    0x22201a5614000078000e0344030b250030200c25030074108441c0310320382c4145410416a4000380340c440700b110a00c2c01030401c0d00e407803068090780100ca074085440b45001041040502d194141b504400c2030510341141e0700e0805000c21b21020788038155000e4490310090205129506090300003240c4540481008510640e00f81c40304001c558403680e2001e070f00341d4005407181c42a2040d0107042c0c0076092820003000078820040c0014450f0030007603001803013104940034401130105921745500050001614140d50b070b02d4a40740142071890b507003900701d20841041012501981c400102c0c0010076909d0788407400760301c001e00c032205da1075040404100c2c2c1c092801c120f100590b403001c1c042e04c400301f08010095407007410441c1c0940301d504e007020b4031050164003a4070b403040820b91000d00345820100a0a1010b030240c86820411040300001c1d007615441d500340300500b030030154054000c000e8040c11981c0368003800c0d250441282079800070b039003941d010b03405401001c00100c08581e00b82d4034189100c00100d4200d04030f0440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 960174442 1250 960173192 960173237
    0x91a030f0403210c0e03121206012003030105010f08040f0b19140f060d030f05090d021c0209090f030702060f1905041505030906180c060f0408010605042901 69
    0x2000a5542c40341c5000c502c032a0007550001d1444003c0300a041c08044c40041d1000500459002d080f5848e03020010a0751a409028100c10030040802c0641d005d08508420307a07503d03482072240c1c0f800207a0321500c20003241d105240c25402194009000008141030340c440c40185107020305282c41100441400402413500751244044400700d00d0310b15007941c50084008811104010042c5000e240e000070840d0009901446000c49c0441c142402c648503903010700860f604104064000703402c4200358941e040d81d4640d00080142d138510840e1903502d00d40e1b4000190381c0b1210703289500f00e00303a4070034401c01c0c00501d010300c090201e06001e10002c43c10700005444c00b004030340e4032a9090b004600001008c0c0200382e0450b000455408041c14400c4c91410701e00c140942d5543c0041249070401104c22085102c4242400040c0c26641e000b80220b46406a02030254100e40c418440c0004540c80d00d02c0c0096242068000e000b5105600305540100040d40e0094810b8482e1060b015810860f0200c084180c840b0000e01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 960175692 1250 960174442 960174497
    0x1503021c0c03151e0503010209090f07020a240f02040609060e0f0a060804030e040213050904021807020c010306050a05031f09060c1d2b03140304050a0201091a030f0403 74
    0x91025070813150a028aa404d000d800260080c4d0040003c0b034901c0d15070a00180d001110300c107001c44181c8c0d401382d0803400c15048800061460200c00b200e407201111010502044036113540080242c004c02040000492241b4403600b0046035403100100003160092803040a2040b0140408205025a03c000b9041d4480340e0841070119810700c01740f200341a030201c10440790702400d5908604e010444030750a64074190314891144221000b10020b0215156404203242c0040824072034141c40c2413010029466080701c410720b41c0000e150050004240c13514030120401c03504050047c00180741c40030440102c0e0411201c5403207001e610381007030200040c4075205603130006020342d5400c0d10004d00d03001040385a410904801c0d1162440400c14031604200401c1c4070a0008407080d0151108400d14003610080701c912941501c40d40e001c0100f1044c4a0301103102d1100034400d81e11360311030360307152006049608813844403401904002d1000071950400303103c905410601a044c1465118030030315000028509086 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 960176942 1250 960175692 960175709
    0xb18031605061b16231501063203070504080304030305030a0f021218190804060206010b13050d1104180506160c080306040e06010303091503021c0c0315 67
    0xc10026548001d01c0c03410f03515804119180e00e49040360038500191502e440e005000c04004043d01481c01c84000c03003181c4c4007810303034056035800300c20907503600300031042407040601042452441c1007003041c2c500d8122600708102c8003c0c1c4c3e440c0c403411003101c2c45500000d1154050180800c000b0a402c1d808102500041d4840c2d61044d590346040c40e4140c0c00d0740c2ca41031464540a00611100408d028040c2000b640215103001c90000009070010842c0792141c41040c04440c64850450b078028082e1507801401510b40d140c003120b8059a1f40c503d00002c0f44030304e030315000c83c1e2182003000784858a011580c00c05100c0c0143c00004007050f03c10000b4080b141c848101007612258160000108142801215031182d000340f03d035101210381000207080c0010b400700007044d0400000c005041940d49602451322b04204034102c48582d03840f0314000d04401c00c1e41c0a01c03002010000e00030300700c041c400e0080b13030340e20f40041e190b609441a007803030303c1c01c003400a1880c680103068540002031a48000e10348440d000b0820903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 960178192 1250 960176942 960176953
    0x506041413020705030304020d0611040f03060506062b0f0606020c01030b2d0301180b070318240617010f0e071202060c0c09041401180b18031605 64
    0x90040100c1d0510001a03a410540140b2140c00880c0010050303907403081c0c040d1070007051500a442e0550060210604049c6030160206002c070341b50150340440c00c00e41e03108050400035510f8010800180b800351403d80c0384d1a54000100708820403d2500001c01c0000d8101d0100c0d000e1418113544050390305540001d4016402844070502940c1e250040000c07014080e42c0d4440110041072090200e032030f01607101d881100c0451000200c0fa00c00b5405105142c004e1410002114441d1030481d0070032100f51400c200190034080043c0c05115107110610211350320401c03088641d0011a141144183c2d202291810b0030317a03495000601948030800c0707034412001e00b0000283d40d114801d90700f003146d41c5204045030383c2e071110760b090013122010071000c0201da070103d03509a112039820200c175203401821031101c0d41001e0094148401c201420086a0b485c2080500074403000c849050394450510503260054510383c034030303c00f14402460070548020410301c1042901d1400c40c6075810954040505401110140d228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 960179442 1250 960178192 960178229
    0x4031e0807210f03050708161209050303061302030c030f33100203091c15060e01090b0d02010e1002070b0c06070e240f1209010b04051b0d050c04050604 67
    0x4140f00c04446185820200a03508140d580208904401051104403014401c1211440c40c0503c120340b003003000818007031002d1a40c92400e44e450303800607210300e80103100d07900201d00056454000d503403280514650050071644c40c4045843c1c2c2c0003000d03200350b0035038107071000302201d0000d00d142640c100a00807414200d200511400c1c0058941016008070440d00305008040341961441b407514004420314405070312820050510805110010b2040c240062a0020004550108c081e10034105c41031503208201d0740b0060010302c800b07003094000003130000f10075007401c0324213182c04900c981172803806104850000f92280c40700c800365844a4070170000784c0d00000400c25481d43c02819248070990070380e03d44205600088001d891501c0e1503000401c140310205142d1805006807003903498210100d44580c0c00307810310440707544c02003c854a10038000d900341030000304805007404881045010b04a070031841d25980041d91340003004003408404002400b000005001d60f81c800207040541000c802e2000100d20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 960180692 1250 960179442 960179447
    0x503121009091115040501020a02090a060b12010906050f03031e0417010504140a12141312020a0b0307140d0e0105040302030c160e0403050c1f02090406090204031e080721 75
    0x7084d8860344a5001c0c208024000ca9038049001c0d005030342c4c1511380543c9911000b49050242842d82c00202d501c0d20046101e0905035424114541290002d04041100d19140c40c1840100c540c080b80da290154420020001190101d000701c425400301071304041d04058840c980c02c2c07016100417080400316074440742880203100103000403140c81c00803080101071691107a030714500300320705068000003171000042021601d424500102e50310080b1200c12558800d07260040d40154030f039610b806134003441c2d4606000c100d00740d0780401c5030b0241c44641c40d114070314909940c414407194401c080c0000c52644950500112040034000c050080c0e2190f0042e5445284103c40f092402d402c1c00c441400d11000c02c2410444190486015030300680c1620344542d4940c2c1104100c3c1c903200b9042256550718104a401c1f444c1e244c115805440b103240220303800c0c0105540d071070a990a0380900d0201a1200340e1004c1c0c450303215000c90389a140354620640105060104980710b08041c0b40005511100c20600030443c031803c83d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 960181942 1250 960180692 960180709
    0xb03040609170921070314010902030726121b0a05010606171b0901030b030f1e0706020606030c0d02210102040306050f0f070f0908070b0409050c040305031210090911 73
    0x958140e0316480000b01d1281c1c1c117507a0110761101409aa0340018014051030082d081006a190040d04490711960707a000b0a42c82444030f1140303030109868540101301030324008540b03507031144990303c81a802c1103869601e440c039100f42405407903010300c2a0341740080022002e0280900424035900c61240c060755a45006641071700c014003070390300341c03885c0c1c0700c0001911050000d8804040080ca07000810f0910113010920344451070340407900764031945800d02419110b8103020225010514166140c1d150f4803a0240e80d55501911810b901d900321690403452802c2040071025900c0c001004010708891711061082c122a081e01c03051901e0750006400e0091110398082e182c0c11408502c003800361403030410500e5400300000307800b5000b041030316401041102c0c8a15168009440c51005032100140da91102c60040d42c0a8890382540c1810800055440102e480c02e4030100c07500b00d00598075202602e04400300d51040184080c529096503074001c5004840340c1b142102c3e007441403800d100344070704100c100030788038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 960183192 1250 960181942 960181969
    0xf0201140a0506270109090618110102070515091315032d021807020f1009060e0304030b0103030302090d0614070215090c09131a0f0915010b030406091709 68
    0x2291300000c524001144584c185045542100000620382040d00c0c00c10040c00d5010811031441040c41d000308144200501010408a0300760226556190781e9410311a107d05a1022003820b000709100751091803c11030203106a4840d004000100d96140c8150140340c012a500250788a02c00c0f8109080c4d207814806190b60100c00401c003641d1038032540c1e40005c00d6000c0641680e1080841540498400b074000c2181c003081c68400415a00c05800303070b00b0701d44020400110181c541c40c0c02c1240b801400c45021040741c081c1c0343c1107130f0061b900b682541c070181e01130360040702d07410f0300a0028605e140206030349224078401400c070350510310598104140000d142080e24205541b0014501c400c0c0084041c0c0050f800143d624140e50200039075444140c0321580032403030b42c0050105181001e07034900010309080707000e2003002c0ba08146486904c802c1c0116980d862240c031401c0c076181c5410014001900c0001c050340c1d116104030004505910750f0f40d2040a0f08410503102e040b0040089051802807910b0711095940317 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 960184442 1250 960183192 960183229
    0x6061203030f150621060621021204020607170f040e0601021606120f060807060207060e03030405090916091a19140a12150e06040b070f0201140a0506 66
    0x600f8501c400403d100c603a40d10a08080c0303c0540c05200c8220144601d003142d81c4002c1d041040015a1404007420200c0d4440101440c10300c54490640940c2c00c0d44282c40c405480a0083d1089640341d50a00c9070360741c0b0003202540d0f582c1e100c1a10b2810710074800000c200e40c4c2810f05010b03171142d24002e41d5280b030f020081c1c0024155007011110800004000d40420200e5026240c09001000980c1c0f6010041840c00c00c50ba01d024286040030a04030000035058080702c00913402c0f2683e20303640c0d4000319840c8000703650b06a8560130820082000c1d250021580c0d03000081041601c0d81c201c50b6010000390101d1503804040c0c031640b90340034807000340450100b40e22520001e503410400303c0c1d81c52401e003404071303a5800f540101c400500d0741e500c4d59850b08640d08003d0400241d000c580c0b001e640c1000c0c0c981d840948100d141c1e250406041e14000c04011503445d02583c0c0c81001c1081341d84419401f40c1d403c0348001084000c640d41c0d080c0c40360700c00c048510028003c2d03c462400092909140040c003154a00c1b084d00da208 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 960185692 1250 960184442 960184451
    0x12060a0b0705100b03240705121003050d020303071211160c140111151308120f06010e030c0405060310090b25080c09010c0c06030c081f0306090f06061203030f 70
    0x1b422403254040a44200e00c00507041030569038603a00755070300c0c0105a1032422040740b03141000b0401072001002400e490190302111006591040100da903840f0499803e000101c0003c0c11a4084080703801c1030201c48801843d542c1403500e226401d550000460b0020b40700000c2c04d85040240d80300c0c00507815410302c1d0a01c1d215554101c806845c41c0e80710314403c0e5416404054400081054003201d481c0480d03981d00003401591480c0c0e9040740c01c80d400d810f41d80e94421021a00204440d58001c2050084064028000c0c2249441c2901040b0003040e00400f403035091301030700529040705400c80c4546038142d84110305003903d900317080520607240f00d03500c905000f4030245020340ac00c0b4181c00020155202200b10546651501602d004881641424a004202100700840496180c0d0940c000da00e0110303259440550641d185410b51007480340980020703113500e0020600f1b1000c01c680e90040e034002402034000c8401a01c3d0b580d01c09003283d07401ea02c8503581c2d401651181c000c0685c11b01804440481e500b00921 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 960186942 1250 960185692 960185713
    0xa0b070809040509072105190b07030605090712020307090e0a0e0709091a100308040e010e0601140a1d09010324021312051f0e010e0102070812060a0b0705100b03 71
    0x2881c4488014040340040111600c10030007d00704a2401e6506420b504d013641e175050382c50f1080707071004140c41d0307500131a040c031a000c610360804840d180e11071060b81d50f64400c090308120116001358405000c2c0d404100b2010004035821400322038040c0070b6441e141001400c455141c102c6420051182c000b681841d040c0203007440800c10b1080c01d151581c1344510003800301c2d104d03066100351070740c0c080d80300912424020078001045525a5400c07412100c0007e411101c07541c41c04011650099072100d07a411103030051000e4005140f18507010741c401c0c440f0860665a05268000260032001c00360f20803030310000c40480103100545020080e030b81e519080740c010b5041c0308008004800000c0640034030510000a50040f2050000400400c41c408400d03140e142101244409841c001e04040c8030181c0340c2c1c0d8201420350f01580b805208882070307990081c00303041c01c21a00741c0300702c201a400034040c07a5204107014004140d5244203001413030858801d10050803081c8084102300181c4a041039520f10980014081a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 960188192 1250 960186942 960186959
    0xa1b020906040b2101020304020a06110a06051305100603050d08011401050f28020c03151807080f0105040b0a050c0702010c0309120308041a010b07060b0a0b07080904050907 76
    0x65400076402c0714086502081203000c02d040101e0390713202d2002151000f040d00389620040d80254010340c000e54840a086807140c03810b6070302c180039502c18082e41c0d02064a4401154207580b10a401444032007045c1100307100b54039001d0ad0b15502c035010000c40c0b645c0b140f0070010440e00708131010103841c01c1c1c10b0001096141c034081b80c3c00e0008110005040c07100004412080707110503000c031201051000c07003e4400c40c1d48031050581c590018105000035105240081103585000590300c0401c0000280c00b07440795403195040146002d09000480d004e108130705000c61220414005103801d10442400000c161406040440c1909070143c01c50080030314107070600545180319403c84141d41e0f02070806c102e040b0301038a400ca8005266621090080000002d2881050392055000340a0790241c01e2a80254060148420403410284144801e90400f044103000040181d00b0503086c5040c02403482a04d29618900001c0301e81c0024422510f00d20006401d0007240342500c103040c2c1221096004011490070402d03003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 960189442 1250 960188192 960188209
    0x80d080c0a1809110d0f020f04030f050c0916180f06050a17152d12011517010c0207050307050f030106090c05190807080703091a07050a1b02 62
    0x2104100070010350755403030b540255001c030402401d981400300f184100ca860f40c80c2140d0031485084154500300011000786144074001e03140d20034212a072291a2078a03680d60214800340d203050803034150045074071043c101c2d91181046445003115030079000991000d540c0040000306100b101c0400200e000303c007403003e096020415401e851450500a9549605000c260b40d0384500c0c0b4408411070442004200350003154030407480481c5000d58020300707400c07054003080380c644564112181060010701301d200c4082ca440c80761000581c9541000207240902041d90002c629415000312000c222038040f10b4426031b809100b10140c0d041d0a201810406090100082d00c40c0c180303215407807054880040f603034403540d000c2d8000e80041103018000c00400d0f001e001d003c0e125070003101841594401400310703381c1050055280900c100c62540e00d460140e6100d07402500201072128050700c03034080c1007808481c1071445000080c018012515020348444644000270907854194a001010444c961031510050716012076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 960190692 1250 960189442 960189457
    0x530031303050f13031103011401031a18010609140703050405250e090105040303062c1503150405010c030c0212160b100905060a030201020d03200d0204080d080c 71
    0x40c250768508202001d42c449018811507132445225100000003006150075214000030fa0660090020050781c81d40c0c0f01c0c40c00c00911015065100d05031600080c44442c0401036403151150b0b0401c0340b40e42c0012155821038441d43c006200243e6180c011682c010703c00c44a80e1341c0000e2600d0300f80004c1c43d050383c600c4d46464000c078901d60300302448151440c44d030750600d110b44054410180400991314045440c6800380000340c40a0380428605480804d400360040e800e29458403a075984140c284442c4151240c000c440100f00858901c4c4844200e089568244100145412042c0601003c2c0c209414444d01b1a5000828601030502d041400e104075900420f2011038107180342072054545600700b60103c00f4031035181c2e0040601820104100c0403a00910400c026503407014810031065580000380004c0640d10301019007d07070700c1143c100c601d0502c030760030a40d200d0008150300e880a200e000d014602a03003102280500701c5401080030b00070140100000c010090007840c4c01030250401d010b13610b809118800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 960191942 1250 960190692 960190697
    0xb03040615170a030c020f10020618030a05040e04111806211b03030c060705190503100b0903070312030b09091914011b0905010f020c09060d0f0530031303 68
    0x2417480d00b035540700c4041000300d2001825116400d404404000e40360302d030482e00c00b021152043d02c85030007070100105030b94816116803250780c605820980384003140c000041013210111240202c1035001c1c0c076800c410b04010343c0e000310b18a0709802c0000c10804004a400340031a022650321404800c244070001d010003691083e036a0081c030b90705c40000447c4c1180f1410f4545000303845008213124042d6449001031030386900e80d41894503440b05000044640c0d102c140c41c1216802c141513420700c941d285034001019208030080445100740d5a070343d00d02421604d6616100080baa0343c0b0208002800c140160390fa0054038039016011880040d0704956400840303503406460841c5800000c00c02200075446440b20440c040b41076101910022801070a10f9580e02505000075a500401156640006050328006000030052035855a8101c01d0100032a80070005440038072040c05140d011030382c14000110b404d18400ba010350000300101c03ca0940400d540b22240c1c090600f007040141850140001080855042c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 960193192 1250 960191942 960191957
    0x12031406060d0c2f1c050406110a0605280501030506130203030c0a15060b0306030703080f040f030c0305010606080c0a0f260a0b040902010c08130b03040615170a03 72
    0x2880c049400c030b52844480742d001c0e00442e0555071110700b0461000000d44c040b2049800512103031201e000000d900c110b0620120780c0034030083c000d89000746049006404108c04607591006262620f9060300d0702591164402a09000d00454801100e611188000074a29044c442540340d030395010f0307507000c000b0400740b203a8148034002421982d043c030494448420410840f1851000c0b0f040c485005100740c2c078200881d0b80340000005a03080500140c2e44110f00050103084c0d00303403841d01c94107518ad0083c9000c0001030020007000c501c3d04640c80910020b9801003220009031030851601d01c2c2121004c0c4c01080501c02500200400c1c52800c604840013801c0c1341ca091410811050400d0b100040070741580000e0404145102d01d4034807048488a1041d541c0840a1150082041c1071000702c03000c1c2180607000402581c441008201c8400c020841e5108000741c000115580e102c070450b441d04140d600301c5216032a01951004010f1100014000c2c103010115404440a00101a075848a11910040500074074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 960194442 1250 960193192 960193211
    0x3190b010504020a030b0a0b0306190608070c21091503050f150a0e0a0f0b0a0803040b0f0d020a200304051c050715050d14040f1e020301020712031406060d 68
    0x283c6c0003078400c441c0c080c0450b05050386800c0122456001260214003403184030704040d008100f50030102c0d00300d4200e0780360500543c071000001c452100c0141c0003503c1d100202159201002d104540300120300704a559880101420018442c0d0900c0f0118840300801d400d000034850007864010449030080c50014011428000344d1010601c40c8145a0000300349900d42810002c0340f0500d6085912240c0380c1d5003040007079000010812a448100340201d11580d8018001803120022040091540c2e4490aa5103414001e80741c01c04010b0f43c3c800d082d440700048403d03011b07266007003000b41c100c0c0070407003401c000c0c2d41441c0c1081c010031010012034421890310340740010b801c170034000b0510211003e8008420044030300e035a0700001030020b5006515428003e464214540c40c07a014024000707010f558000c0503000d072411107842d040442e00d8508840f6440103000c015200042c1c2e024802841030500c141200141000c1d04c440280c1150200c0c40312a0b49900b00000f04070b8269240d8080700c144030383c0740f04006800c110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 960195692 1250 960194442 960194447
    0x8060f09070b130b0409050708060a080c010309050c100513090212073213051827161701050402010917010f020d02040f0503120d050c070807030e03190b010504020a 72
    0x1070f2548900d0884800203004a0045a039411251052200741c8946206441d044103000c40d001c518441e00409030444601c0e02d00642c46908200c100e02d020f4000c440101c90140000740c090241c01034114042600040c0d01c00d0101e0540190200401c07200904508100380b6400840203204010107034820041c68810191141040181c0d00d800700944a01e540f0035075142c0d4807d80a59406480b2009668000c5030b40042c0503d45050a42007503d900d03441d858140d2640c6405810039102c8803042451046183d0303840389448010041c5001c04510f100446014a141215017100c00c00c1c0e030b445440032030f41400c0400002d42d0304000403d00b00c909051510220000718800c0b2070041409084840c952800091031144e486a150058402c1d02c08910a64060300c0d80c8804141d030b540440c2c0008603503a8800d01c0506010321179a407280d9440b000d4211218034140c03841e601c5400c030741c0c0851000c4020440c035480442d4242003c1103070301300588040003042c0688a140d02c5030b551400d0305101d650310a640008400c0855031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 960196942 1250 960195692 960195727
    0x131d0f0c07030903050312190902010e04021b1f06300c051504030b0708240f040e010f05060f1e06040b1b060a1116110a060908060f09070b 61
    0x5070170400340d90b180e0030310b258074021100c401d840040c81084403c200748801c00b0b07588611010640c0c16151207852010400070300020350400c8a500021030018800400e91290034029200108800f42c0c07400c04149082410204895007034011114130760151017055103020b07541000024070001c13528000d030a60090b00e45540745443c150805900441d0200a90075207424a40203082a0b0b07120750a4a5110380d19050b0445041008a48800710101090b020750400e1038030090240d160034016204840c682c0000e03010909645100b40c0d03481d60707a99204c40b045008129407142c290042c0c801c41e040d0f030b94140000300081001c1401103900d02005100b42c0e42e001725665101c02c880080411000881c0c48a0624080d003038510640c96040c1804d00621002a80c2c0c5040c030f11400022400c112491420300c1052041c1e0510307001000800c580c035a5585140b495150303a481c0c40700000b054155100d1310071506140500303003403440103488040480e61140900a100101040c20015134070810140740d01c4812000c00f40e0880d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 960198192 1250 960196942 960196949
    0x10c021201060f0803070b01092708070f0305091306080309040c0215010e0717010602030f07060f05010803180303030f010306090314040e07032409020a09050402131d0f0c070309 78
    0x103d250f100c00900050080040c160440c011020001c090b82e0721480d4409842c00741c3d040d0009400c2130700d5120401580b03a695910300c54040c14201e0304100381640c50380040c0307502c0f08084c0c001c210b0120f018001032618018021070300c088400148600d6190001c030701c3e40c0e400303042d030391034455a11185004100c9200704400e042d0710380d414070180c4095a4030081c008000c4410368a9200164404092541c0280381ea1003990496540d03034001d51402180306807440781c9410650b8200c4402d500c0f003240c0404a035060003414040c00c22507000d556207074800c04ea440141c200d00d81d203a80c040d03001403007041403940c9100c80d41c2d811250848401301c3e020185140c1240d43c2c020f0900f980e100e201c008a404502c0100031003000d44036905030389080105d100c108240c040b000400c800c1c2e2120030074a208040c49020035a80150941010030705001d807900e83c40300001010b980240ca61010310f050604010054801c2d1a0f20300015000805e001401e282010240c1c03e00e0402d00a1048801180009800007014419000d00c0d005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 960199442 1250 960198192 960198209
    0xc0f08010b0d2703030501050d03050f0a0509041b0f1b06110c0d09050f061c0f0e0106080c0406061803032604050c030f060c0406030504060902150324010c02120106 72
    0x1240c40300d43d8040c8003511400300c00d030002413802001145604158080c10314003505512980d0030070807520410340c40d560021010b03c0410105120400c000e0300e139805a0400c016003503205a500c040c8400c0010151300c45006403108002c0480001c00034034082100e034001c06ca400500100e020502c07011644418401e05030640c00921a0362803208003164482c0049007075580c121101485100d0700010842113004aa0340004419800a8001b41510240d402103207006240326011031400102c2c8156401c45100743d010603410340091021180500d064861302c4042c2546080285488442e07682c91850301c1140d0000805001d035001844400610000031140d4a04000c1403c81182ca0245002d0383c0f65045480380d41c0c000c3c403a903c200c0b8904540800c82500c41e00d8024201d9052034541201200500310140080c3e0340b4550303031220070700580c55054001000c0c210003440b2940d207040c0601d048000d40080b00c0c20b030f6a00403200c48603003904d81e0310805100400f601100c070450b0030030103801800d0060269034448020b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 960200692 1250 960199442 960199481
    0x11415060c0c03070b19050a0807030207142d070f1509030845010c0201120203070201050603060a11070201050d0e011b110303010e0714041806090c0f08010b0d 70
    0x240c5040c694006d0903030000c640342d450415404850150b50501540d402070010848403400264410700c20790241c05890301508240b00400c0c0050300b95820040c011010203502c000700c01d0f2800195002c00307403045041e0301c0c020080c01d001d440e150810051624501500c4c40351002c1240da0004144641f503007201842d044414150340705c45040101e0101c003401c401c984c5055424151350003000306801229144e0b100d000f00740e46000c80d90b0074011039000700d031400c0490501080c02c45002540000388095846202c040d0000a480d003080400c0520700900108003401a40c1070101105000e05081d0a40725410790a0a0281e00e80c00f0340d54155001d440c03d05800c080da503207030004070803281c0d01b142da854503ca5000e8484107080001c01e034820703481e4407090140d41c40310310a8001149a00d0300c035808428405900320150f6041946582c004400c0388003040742c841d80070303444400a102001551042000340042c6040480c440c0c81350081c041c11481c4144126405690042128400e032102d54020b0803c0d0f90001000301c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 960201942 1250 960200692 960200699
    0xc09042303041401051315030609021204111c080d0e1005240a291803070b0a0f0c050f01020c06040614010807090f14010b030405011415060c0c0307 65
    0x1a542d03041440b800c01c031a03a01c040c80710890750003403089075a981209034030380102c141030115202e4101c0d1808a103c007015540c48001405500d58405411400c1d03c012541445007024103104c00720042025041d44221002403407a18040131074900d0058a60780a104035488030281e0400e00300818281e041459240240360f4100004d60355684143d00ca58098100500c40c540c4c030f1125074030700da000c1005058000d410718000b802103114503140080c61403103103200b01124424a6040d24070642262128001041c1108481103a40ca0107010200c0582030742c2d00401c1c00c1010070034000b420b0015001c240070505c180c040100083c008140706030013040910301c0096640d00e495010709551004101d90035a000ca1800d020208895041c2202c3d60403510300000402e031440c1005240341c003c0c8401600b040240e6980d52000c08440200c1c075001d4000c012400d10b2a40b01e00d8141001400e448400800030403070700d0080d08202400c440d0101c0001d4410090320020740b1140c0c088034180c07030216410300c89030b4907118901002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 960203192 1250 960201942 960202013
    0x18050607050d08070305060a0611070308160309050105130603050402130507050d050606070c050114120c030106080f06150d0213080604050709050118091109040b060f0a080c0904 78
    0xc40b1120b1465035030068950310350384218125803040e40e01c503078003500242c000c0000c6803084038a103035000b0b480c03015500081d03503980c0c5214040c0e0100191804c5110300c4170307400c001d1641009020b4002c20b02130801c1303850005050125950009240139000c1419542d40c040f0782951141c444102989c140038804000074103280341d0103442c070f17001074a85240b41810940000c0d19801d200c42522001507002412500c06820040151801903208440d1000c603442840440e419801c0000302a01801c4181021603895041840c01480340000400c14070f14140c1d4a024405103031160100950201038102d002616100021160b40c007a100703020120500c04401000070030540c07c00b0940074025407007907048540f460b0f91400044190780f4244035440204000e11210380410302c880c1c00c011029845001c42c846210001400999010400d03501030f20f4981d041c01c00c021045c00d120840e01200070089030003449036880c207030026a40781200c0d40410f0048080c6000b180801400c070b060399002000d1480004c45030000e85008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 960204442 1250 960203192 960203203
    0x220b1806030111040f150c060207080901030501090b030c0f0402090a0807150807020d030207020112051e011d0a0f200d0510080c01110c03012a020d0f1805060705 71
    0x1064480e518000510b203030f0007007001c102c4080341c0d801d5000400d040d1500c690007201e105031110711800c0c020744c02e001d000007800920081c5016031003004510b07120285040014101c4038140c105001d00c5182c880781c0702c5a998006034144090b001201e500c01801460800700f0043e00440d15070903003001c0c05030b00c085003140d0301041c101c0c00d81302d0540c242c09030f0720441503045603604407d03a900c80c050f0300720900b20346219100390011302a01e401810200300500e8000320140880f0740480e80b5403110741c224a941415542d80c80005401440c0120030909240b0b00000350021144001e8024003545d583c030140f5000c40109034204d040c40c3d40c01301100441140c41080140000d9200c14a4600d506143c4400a905042c0c1010b9070401d490700440249803006501c40155000000b40c551500079104164414402e17035000d0041103120184110781e040d000001c1c50118601110800084c003e5421442c010801c55034070461800d4401c01da85009003040d40005100505404603800483d004540014607000380540041c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 960205692 1250 960204442 960204451
    0x10305060702010504020105030417040321020c12030a0302090d051608160e04080d14071101110702030a080f0c0304060e010f09081c02191b0801020702220b18 70
    0x15a425961040710880c00c0b00c404541c024086032052000c2004200c6040f88032210844126406161544940341c080d0040341d940714140c0d0021026a20491103175041c01070140000c020703285141c501151f1400c4540b40e01502c03204508043d030200c0c5000b40703503480000c0480d085410006a82030010790408082e242c2c05140207054251041c2c5112201e00d210445507902100c444030f241e203203e5102c90761341078070550010203a07044c1140c0309c202a82c1c9003072001110500030740c681c3e1282c6040310011055242501d1410b0740aa103150810300100c4090303100401c10300e0001340d0056a01e50b03200c0b000300c3e41c03046a01a050003608240310100340800c0c03a940101300e40c54014001d03200d04c40b80c80d0b0002800c490300c4031203010b2220f15400c94505011407800d0000e50030805130180c01503440340150f1040300e0000c0f44171450103648410080c2d180803421041b0300b4058002e07005160003540b8010864000c00c0841200b01800003d00c4440d1601045107091980000c52030440140315503820710b05070340100541c00e41030300d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 960206942 1250 960205692 960205703
    0x40305010c08100e01032a140f0105131e0308031006030605060304050d0f0302041d0a061d073e0c040606080606070f050f07080105101d091609050103 66
    0x1000710b100d030095154400c2c00c81d0b41e00801c540c8203070308550712412081c40d06010210400707032021101f040800c02c0050103000c0c011680411001c9130440c000c10044080210006040c00020410021a541d0044a801c10350b6001c829603c18810a10300d6241001000d0b0b101030f0040101206100b040c604845c9224201d85d86940c06005903525213040000c2844141c500130282d40c840046249114020015405048c016050050400b540d850503140d0012403950b80040301400001080040e032114854070024116540396180d0721070880420020000c1c0142c010010712440c15003030841d0030213028490707000d0000460050f4804800811204021407032500360716507800b400180c01c6260600740f0902d0b0841d690760341d03412010740320b850a001d002da022580a0312149540110f102c0410b0080001941401100b17001b450b18034600801c441c21114003a01c901da065848040c100b00c1c0c0d4074041c41007a030341d14800b0b40390f0280b5100c40134103d1611900701810b405080d00540c000440010f903911413412030b801213 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 960208192 1250 960206942 960206957
    0xe06120901060b040b07020f06040b0a02011d030724060306110901020d0819110f12041202010b060a1d0307091d0a021f03020d090803040218060a1e0902040305010c 72
    0xc00c1d043ca618029805103d10f503e000703028580142c5403100c0788800781032001d0701c010b152944403184189540d10000007140542c0d181c104500c0c484081031200001c00303210070040c40c1030102d5070b681c111180f007014a11a030300e001082460b136a602200c2c2c0c406402554007500412104a0341c80a4130100d0b0001c02142d405070081c0c000b40000f2a0040680d6403050300d01c14800c0305e441d9406503400e0014005800302f8400f1200a010b00314240d000c005c004d0000d2042480c4c21810b0b0714051a003c0801b0600c3c0c4007000841e41851401915038840c41d007031b100140301c0e0b0f0130000740300d040e51145545c421a440d81c0455042c8144c41000502036080e9014012515006801e0b1141041d5900141d9443c00d1f801002500825410b8500e100c85840c04170b282a28089444c001d440d1042d011320352400c0c1c3d040c51000799400c0d80d0010a000452822000740000150001c1321201185030510009241c0b21803481030552401c4070340200d01c160071081030078401501400e8003c54685440e0300305140200441c42c2002c002c105403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 960209442 1250 960208192 960208199
    0xd06080d020a030f11031605010603021e01020304050f0d0b0709061d060904020c030c0114010e06010201140f1008030706050f060d0c0504020703030f090b06011b0b040b070e0612090106 81
    0x2c40c020004980540720700541c5030300c030764003201d5012100341c22030740a001c28054040001c040b400c401c0b41840c01000082070440c15401082280c0500b4044112066082d10030702c54207903000320684003240c0302150a845800c58860100341e5021100c10002e000c0c1c40c44104000c0602d0304480d2450588005584443d540303065284003910314072141602c194090b0741441010110f203040e800600c0c024140d18180d80c00c3c031160790302c00e03825203110111818a4000900050140008003031000f90f010400344001e2019000e014500000d60340c00bd0311102080b00b4010010f58548002c0b1a0b11009181d0300003240d030f0303503030903418140001c040c103664603c100c8031282c1c08164589070190005581c503802c050180385e4280740400304002944296801c0341810744640c0030310884d030a10721504594a01940d2650158a0004001800c0b0f401c0b0160002502801042d05400301c7e0f90401c1c8a644641d0080014001e5120b85205841381e008600039540c3c40040014803625002004a10b123000d40c0812009010341600c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 960210692 1250 960209442 960209447
    0x80a021509070f030b090f0d020a11181b0c030d0e060a09020105030c07031407030c0605060105040f050904170a12050c04050d1211010e0106050f06030f04030f0201020f0d06080d 78
    0x200c42c803e001c12100c18010a1011503040002d00b17411040450890710b044000141c15400c00f4517400c10003015801140b503031000e000a0241c441c06414044441c100001030180062162003400b401030501c2500b4000e40d40d03c400035174411104100c1e0100f048035120f4904d1400c1d40040c054104142801c2d010710780220302d9050a07401449041075050f118a4210303640d10050041da1b8120840a85c1003203204004050a041c0c80c0e0000c1070018000e51340c082c7e008106040c0344040d1b0b170300907101a04001c41084204521003203034030204284c80c0c003205c810090341c642c0d081410380a40c0010705038040c000009200144180c11030315441c58207070001014001a59490a261030354040c6201e902d0b042031b0929004400241e0b841c030814485203150078411011050b114409084900c1d440d000310b0f150395210001d000790b02d890610041509811950903245103400701e441c003038028000d0001001c0c000d6003104503040c40d000303406890501202440d12034545007c180700034058251441980030500448200095991 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 960211942 1250 960210692 960210703
    0x40504110705061906030209190515030304090c03020403080d0b031207030f030f1503051e01060b0703030b0102120309030703090501050a09141504090c080919021c080a021509 77
    0x68001c4040c00d01695031356469940b410b00905484103090f90351a0201c01680c500354a18010b03000c081102c00070030300c800c1007101129405030144402178400c40082000d85e03000021030341584e00142c0080703041e40706810705070048c3c041c90304000c20b0403130f010070030321440c400381c1e070011550180480481322149508400507045126000c0042c000410081c5202c030000e01036084021084044140040d1000b86620718424007403044d00100c03034a401040c0c2a0b0b6260090341420082e410182d00204801442c000c01c201d180e1103440700c000d06254856680b114540c0c020300020304500d00b10304489a89260560f000b58482d4060311040b03012620a004c00b090f0f5500c600f05546c8800a152941c1221070308124140000406100c0616400030b600100c0001e24035044001c0e000514015601281c030840d82d080292064200500c104070f5035004a41c1e841c030703551158405603038094040c5c0f014014418050002c00d01004030381000380182c0c2000400e82d4020b070740058801414812984422080d484401c24180c59a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 960213192 1250 960211942 960211957
    0x170a0c090e160b0f07170c0604020102011b0203041205030c190b0f0708040209100b0c0309030106080f120309210310050a0b0a1103071b1a040303050417120f04050411 73
    0x140d82071240390609294030300240304550140e020914075200c07a40c074031b01190388040341c0c0a505800c100244021941c09003d101011003119a20105808204400075902e00841c4207440c0058a202c0750001844020301c221124a0244025910000d1101a0a4407200040c2108945a2595100059040c9091a8a68001d05456131071074600e8a4039002c1080700e0030013802002c2503150001e0001900c0c64180010040620070310f01650300e51840138101421141c5962100c801c0e030b0891030248425160104410000380c000c211100c0d00d076190340c01564945111011003444aa03400c0625901c5141c2c4c0c50b0186100d03080c01c4681c22442c0d92104280b00781000c00c0d10039401c5901c02480640360b500c6c0a0b440c034810040c150710449040c210340751500750b064008668001c0b107803203003818284907541c041e13090005081680d41085180c58030f5035600030040d210b68070404155030980b02c124884500d003840f2591500030442d0101d62586521001444290300c544503086c401d601d00200c1e4040721b1040310598014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 960214442 1250 960213192 960213209
    0x8060f0a0b1503070e0a0e04021513150507050d090f060e011704060e100207021e060c07090b130612030305060117070507031710170a0c090e16 63
    0x1500d0303489408018110300803055a00c078a601103080c00b002140ca000d10f02c503da0b9070307460800464101d8180040e606864005c1b11201102004100141c1c0319145149110b242e441c0c80c0316a24409090500c50b0741000d03803c186040c1e240400c4c00b03c05190b101d005820f00d94012011b80741707140000d03c010703100c0a116110750241c40418010070400c01780240486000010b06052074089800b810180404100b012103049601a58400056102c100b0400c8200d04900f04c13200110b24005158000a200300040030031a0810b03041001c5490580d1920800d881040000c1c10440340c24030b84484c60b1401801091880902a4170924032003004043d4900411049a850110134001d03803d403a14120068031005102da03060001c0f0a0a1005e088100c0c00e8146c8103030941d5481c5902c3e80d92500d401001c0c00c0e03089441544a602c0c090038040904e0842101ca4121503283e90f03a80b6030032041c50300003801c01d12441005011682d92106c00500c0b18001c1e00110321280404040e1451401c40a441c1c038950341d1940181c1d0103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 960215692 1250 960214442 960214471
    0x1020a02060a02010609020d023c0a09030204050708180a0c030605101a03010f0509041505041e030c0b1303170402210c150a020a03031d15040c0806 65
    0x5401c1100050070312844620010503405d4403804640241c0e40256680d2901c5a0b00180551020050914500354510a89148002d92492007500c0380030b1301c20029101c90f03180e000200c51304914058061000116400b50080c44039142c040b0011b410904101e503044d0b07540c40b518541102ea44800b0400d02511a13210066540c61400c6032120001030000400c040c0042038512004541441001400020281b00c2500705550b98104510001810750540c0054010400c0b00c0a020025403151f039444107a17414948001896030b21814029172039041d078040b41c0c103080f1882030604145640544020029402024405010703114030390122502a400c4602400040010051100500740001503980240c0018110091400310415065994051920500c10383d844202080600e0600e0b0b0850081d04a000b18a60705101e4a500301075204c10b0311540060405030340e440644d01041050b404c0050503a01e202c11034410f607040542100b4848421342e01074580c4005243c0000318940e00180c940e204005881403542e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 960216942 1250 960215692 960215713
    0x609090623060312030604241a030408160c030c090f110a0f110c150306010809010b01020303392a0a230d081603090b0426030c07200102 60
    0x46541001c1c0c203407a031141c0c40f00c0030310786a1200c100210311000c500c40d008800049c50400010184514a1840c0042c2e8800b07100b0040400c2e80729082d00c2003108046402240c0308194905012100b443d42c01c020298642e5000c0480c44c03100d10b511048205c040020100100c00d200344800702a8080c00c120400025400c4022041c1c8a100b030710035a0100c00180c0c1140c010740c12000c001034108024a500803034060000c82040b2403580d100d400306800c05a104001c0118100e00c4000035120b00c00117202c1051444c0c2c54989081c800d01c2074110200342418486c808160201041440a8691084070014041e241c407503c03400c29900250302d200080380c1004002c0040305095078404a004404083d440844440d0440340d9034152401c1c044200c0e0541103035189240d61030070607906000842801c2d4050704161908814100069551942c1500960030100503c04400c5803807111800b1b80c1c1c0d0301c202c6040c011010041c401050505805441018803034981e81e00b081107078801024000603e60031070781c010307800010480c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 960218192 1250 960216942 960216973
    0x90f010e0609101416060b09070827150604060e011d15121f02042106090f0c0608180a030e01020304091a03010f060f0308090406090906230603 63
    0x820b1409441d003098011032140c02000304c155005000c1450260180f40721110800030184586440071004840c0009a8141054001c214140052004002046120f01704408810000510381440042d07811a01c1c80100403145c00103420b42030310181d000c0d84c100710380401e052600c035804a050320a2442d450030b200380003108a150800014040e014106a07107048030343d43c1d8071101c0300800913108030310041c600810b14117083ca4110420341c100f0b1848030b105100501101040010030980c9544081c0c48039507c800a0800c2002041e000c0001050314030b400144104000441c01d10000321219621403544603070300c150744200c4013040902d0742d94441e00024060030000703004103003841100c901841240e04154441d07001400b200c00725110322415102d103090120705840c0902a000e020001340805020031440d0aa07002d41600460100409003440800c1ca080755849580c051402030a10040500900700581041d03402045000001d50110740c4081554800340c00d002580e6000f11f002600400b055041c0000a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 960219442 1250 960218192 960218209
    0x20403150630150b1e0109030b06030f010510060807020102070b0103030c11030d05180a061b030314010e0a0e0a03020d120212072604051009050c15090f010e0609 71
    0x40441c04002d030351582c0d01146201054074111401030000103081d102e07120401000ea94410300429004099041c0810180da000300408126580310350700c0c0f10b154490000280c100000351075000c01c9503280508101020b1007030803078001194500c2d101c60066860f0040304034240d00c03400703030090071044001c401000001d2060903a40d65150007407105200260410002904020b61001500c00003200030420100158210004403210704044586a010a2900d100a000c041f9180c100954030710380b1142c82c009060180e0010300c400780d8075680120340b541e140c5000c5003c01000307440c083c5450745400000001100001207000300c043d050f03001000f0081c0f110404403181e1000000300010940c0030b03c2450a10102c01441600888161310b458440766807642007005100e80f02c440020040c60000c09102c0461404102d6500442841e030020907017550500305035290444600006070400c005220401003101440048c00c00300d0011100c943c00826540011220041b0041c82c05034003540c00c00100e03546180c02d0f40e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 960220692 1250 960219442 960219509
    0x1e0311060615280305070f0e0f0607020d080a09031a190b120f21040f090b010936271b0306470316090204031506 50
    0x200d61106a442c2915101840c500c500c3c5801309803070380207110245402040d2084000600c0c070300307017401e810348000182c62507110340c00d4540204c0002480c1c030107648072500712400c01c5070402074441d5503114080c0000e15a404603c01035400e2060800003484241000802074058050340c02d00201d03910312001e0181c002c2020b00000e83d03000000541500c0400020b014120140b074000700602030800149203e0403010015030040c0d401e21804000501032541c0c0404814190340031100001020060000140c5d00752040760009001e010202040796405172801040c2c0310b18041024402829600381d12041094642c5a0440c0076141d44030503c41690216514061451500658084840305008603c1c485000c02070340056039495110110200751503103040b040450021860a582c160403d0b4480700340c1d407a805d82d41000d003a00301074200c00a0300c1e5420041c10138003081080c0f010b1115560b032450400254031a2004640300c0c401e2a120302810f11292250508a0b080303414003021009900480c0741c01c0182020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 960221942 1250 960220692 960220717
    0x21903081b040911040906050609030a151104120515070c020919140114010e060901030b1914120c100810081902013009020d1e0311060615 61
    0x440001c40a4450013003411503501e006101d9513030741c148810b01064951541003980508000c10041c81c0585000465010362a0050151010948101c00171805440020078550208030049804100442c0300e1300007800440c0700e4011107005c00000c5140e4004258200c0d012070202d2400c0480001509004581560100e9107045085485403411a15002c540840400005036000300e0014000d20000c175900c54242c170000d0070a1100a1411800980c4502c1404440c50406442c0c0507190019110030f41c040300000a282c151220703441d101d0080702ea000e0100e50707040384200c01c1c6020200398114007140715001d1400141042c84490405c450542d1482005040709045803405080003840c9542070041603c10151201601c2d85100a07000040c00c2d6400e44065140503240d041150402001c66080b1500803524403c001c00d4441d458000a060230403140c4025000480c0c030f51200c46056518920140307030b10f21070740b20055503442c814500baa4076242101c54a1b000450f4008580500d08440e001d04000003240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 960223192 1250 960221942 960221947
    0x30b150f0901021006090b030607030e1207050a021201022502061b1509030a090b031005010f090819021009030b0a05040f12020601090b0d020f041503020a15021903081b 74
    0x4010600440b505944020340590f9070f0050b01c40603203001d1008d80c1d00022b0920f0203001c55180303100042d85030b4008108041045100045500401c0740501622100940050449100d90f1007092800d000c0d52142048041c4ca5024007031050308001c90081125217660054000c0d41450b0b01d840d006030140b03840c82c80180744c030b101f41d4000e48051071540b00c169214080070b501031a165510080003a0102c8043d80120055440520400080c01c21403a0200c040314000d2030008058120300c0340030b0b60460541d800c07603201c0b401020f90400301b2030011070094800300d2080c1c46400381104403036070441d81c5120a00000b400d103401342002c6500c1c0302b00b42d080f0f503030010b0140260503c8200542d4400f0070544a410301c1d00c4c09a0800c0c030040104010500c26210f000d4008d03508141030484030350020b800441c4c60208103100e40e0f5203164008015812032280800346d40e02424150b00c141c0c40e6400c00e040003500b2002d03580140f182c507074800131541c1c40315003480384682e060b00c0c1c140c3c081e15455980078202e811406039040c1c00006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 960224442 1250 960223192 960223213
    0x30c020d03090e070e1509181b0409020403051203010305120d0b09010801050a0b090606070308150a0b0d0f0212010b03060f03011e20040e0a180303050601030b150f090102 75
    0x403443c000c0c0107100c691030f02039090410303605000f9041c0351314003c0b8112400500c00c08143e0b0302c0c1c9400101502000281c284000da9a0b50369010100e040701d03011035000c2c030000c00c001c80c081019500800c1524022411101c1c050b43c40355280c0c111340300c00d001c010115004500d058282a0f0090003805032208040700100740c04240e4400b00d02e03484000da020b00341513912401884604030036403180c1c4210b00420390b85000c141c603100c80490494030524400404002001d40055010b4980303440b003110419009040160b940d86d1548020030682044a140006c2441c1c4401211622030318800c9a5403407422046100c4240e1802c00421101d4100034942c41d0003c084402e044100d607070070320480c02d0a440b24080058440840e00c0070340b080f140c01046000014440c141078481c450841c03400d80301202c8080c20000003d40e036000d642e0004d0898035291300c00510000c0103aa0806400d81c00440c81240c003030f6070402c41003c164040284002192825021500c410042184500d0329030004044a890600446048104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 960225692 1250 960224442 960224459
    0x807151101050f1906061b060b03120406140306150a020114010b03160207121101090b0703050706050f1005093408010b0331080a0207090b010309030c020d0309 70
    0x3003103c590080c4440d032401c004000c112a1141c001d82c004005080101c20305000340a0021182403010052403a00142c000041103000d4108004008028081e1800304003641001a15038125000300340114a028240d00e01101e540d00940e846000010104002c0c1c290400c03400c1507035400002c602d001c554980e072074207140b145042c0d80c040c0244100c840b4140d603490403604402d0b0040704511181e00f150400d003010417204401124030181c160f0800341580b240a104001030720541c01e2680061000c41002c5003003010b04d50810041d00100d030068a0500c0103903035501c0140320032203049841302104070750b0250920640c101081c406a011b082910b0700858a481d00100c0d09806180344145084110402c16150545a0103921030340141420344841e800c44c10b03d60442d00d0b00c100c140b62908552000b04020721182150400c41c1004d0a41204800350794142c49031009444036624001d0301a19802c040190440394400d200c4c3d20b91a680554a6900d4211983c2c2040040c400d20702003a0308003c40c541c2c010800a2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 960226942 1250 960225692 960225701
    0x80112170325050c0318030a05060106020c1f021905030c160923011203020109082101060206010506120901090210120507080c16061103101403070807151101 69
    0xc00c01e68910452140410004040e02c0c0c42200b0404100052148a40810380003042c1c43c0c204d00c1129040301c000c0a001e01080c80d00c120384802802d244241e1000203002ca03004254044611010f4400100021100040c10a0030540c0b140c1c180040e0310003400c000c100c02c0d1515640ca070003482103007968600b4a01c0b003415854840f0710107030f43e007058407e40710030020280a446450740511162082174507a40c00f451800c02e8030481442902030702c051070074125040502c00e5000d86079035036202103010341741e00300e25094000088520380c4102c8a20312103800800c509000144450485500421031441c1021280000d41a00e001901490b9159281c0b0f090400580e40d0b003229502d1000b4075030b9a880034805420320441034410280107141440071f41001d112442d111a0111401d2506a1a900001ca0468a0942c0085c8001054001004404002e00000d09181000070b0202e0b48210808203140010f0403c142e269481486440060b503c501020080900d5441c070914008210307003002d0144490b00016103007942e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 960228192 1250 960226942 960226951
    0x7030e0703053c07120804080a0605040b090f0309011808060703020c06130512070203100608010509251e0314011413030e01030b0a0807080606030d0f0801121703 71
    0x128000011229489208883c2040c0321000c400c54003103d4040c48031040d10f52649005011642a45401c07060a210a100072980144603d42c101c504258150401100500e401d60f0126104040b40c1c000c580d080e800050103400074447c0704051490040290015034140c05411011908a02d00c2c0500003440442480807904c1081240c4001da0b0b500d51401a45003030002c01824801039019070001c06010031800164150340064150030182d440c2c1c207900002e80740a01c003c80d038240d841d05000020480030b0040d044076004170028000c0f0f403908a0741101100780d86800f1648840c80e600010f000b00104680c244051348076488108041d00121740307a841c0d0aa90683c1038071100c0c61a91070b0820800e6a2180c400b841e503104843c4c0f4134003040b120702030340c0c000e2445100341900e034101510703001980d42c41d83e1403101074801002017004964886565100040e251402140c1c682c1c0b107030207200c081940c0c05000302c4030903105114035074540c044c0c0da00701215411040701c140405e843e84400b1104011401205600441c001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 960229442 1250 960228192 960228223
    0x181b0708031006090303020705010c15051005030709060e0f0a110c01060e010b03090a150615020601140f09040605070201090f030806030d0203180409020d0503030c0d06090b060307030e070305 84
    0x160325025589940340c102a600510402104c190200040707a0702141100c1a5902468011a04000741c10420701c250b4400c0f540f0a07120b46002c051044003c0c1c1503183c40100e59058095401c02581d03168410b085a04910400040c070420030f0008440040c2c2c0a46103074800a000c0c40002c7e600741440400006402481d42442c2c40d070340d19a024031801690962003801400b00c21101c40c80c6103400020b882c0c80f80d100e010001c142c2c0c00001a050100041500000041c00560840440144608000079941c0400f0b206802400b000d1032007100c041c4c200340c48080c0d00150081c1c600c02058445a4886c1e0040400030103450071956150407100005401e03d002c0c0b14141d000703035281041800d00404041c00e0513079003801c0e030056604c10400c6940c0d4640d0354003072003c1c01c041280c0024140c142400494843c041080c0c0051040c0000420130880c92070f8500901004c5e000c0724420401c8980350700c1d035082102d14880c811a03000034240000341c6a68480d402c0b07041142402c005a400003a03880d59203602e40103a4001d045031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 960230692 1250 960229442 960229447
    0x50f0d05011517011b03022805040f0803090f1002031e0406020f0a031e02030d090302150a02040305030403020d0f06050907090e06060a031b1508071d181b0708 70
    0x7400d040b44020300101c880008103d06100090810700340841c5c90700c6002031580104100d5050750402c8621103c9580d9280090301b50942e414004210b60b015004401900c000380c0310110b187c60303001040d21a0540e001c2c0407050250380c5c0d40c1c10401060a6100341c5811444100483c481071000310001d01e0a40031880c0c001519181019006801c000030074150400c69030101e4503c0021a41c091040382040c1403000c0716101c0d08003007510807401d520568603140d10301410210040c0c20140e000500c3c8460f00ba14803840e540940b240c0010509a01c15031001800f1544180700a102610b01204c1d402103880c801c0003504d40c07002a0785c1e0781d64280c54003255400c8180e00b00310b01c200000c00c032500500e2001507243c4040c150034a02600041c450400f5404003802103010140400b84ad000e0a105803000341000307844440072203030030b10002082501d0417200400014038912800b90104070280094952010042c1451400c094103006003441090051031802c041c880c060090142036802c10061200f40d0017600c081da03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 960231942 1250 960230692 960230699
    0x1c0903030911010516150b06070515010e070f0305070c050a06060f060c020604180212462408010204030b060a0303050715090c151413050f0d050115 65
    0x690450b124030400b41800b00802c07010821001e005c0c51188a1940282000d0411641c865020020505a1815034104800048203400c0c040002420046030724a6050b4001c541c0c0c85001a07440c0c08010b4603042c012505c142100c02c801401394004940c42216031810b103105071295121540340420b1541d044d5103290351003205114030a006104031000e003e0394100019110030541c007181c210700c242c0c8120203942c20100d10703200c620120798049440c005e4040e07440301c0440c00c1c4400f03642400d100d0500030950752030344036032200c10129049040c007804080406200102c0d0f0002c005c00c0020348130200e10b140107407a604142150711050082484043c080c00000141ca80c0c0c110b150001c802e00c00508514412a0803030030410002e5401411036041c190722401043c00ba0301c0e1524554042e041d903100041115042400215500386003c1c45204103c5a65540d0504451a40c9000009100345107250340d8000603000d0130b020b0741c10402c110743d9002c04007600c11081045a42c4070f050854820145104407003e10bc0c0d401c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 960233192 1250 960231942 960231953
    0xa0c0905090c1e040216060e1605040b100c0c090606020309011107030f080d090515060f0907080127020a0f020d0203040b0a0e030c091602012304020103021c09030309 73
    0x607004500159401403e8400c1d5126800721110b40c1c403a2280f140b40c0004400040243da185003480240c3c0c04041030003035541044105444040703079403034289420100d0000181078039142c0110081c0341c101500c40543c20f07500349000c5400f000050800c0d100070344e000100055060742c512401c401401a03901954444143e60001420443d190b00a2120b6611044003803001c260044c1007020000d52121b09156210800001d41000c3c1c2018074001d400780c001c080c01400c040a0b0006c4d003520450742252000d040004ca1000c01c0140740094445a0000700a1001400341100f203441440f82c40001c1003a0894001d015140380090780d010b00380c1d0000150b9812200351300103404202986a8000f41e0014505007400d01c42c82d219039025500f110702c2000803810800744280c030103000c0720000c0300780904241664501340120041781d01050755004019882c08000f0016880344000303000540d81840400409619103400460294020f445100d514000188a100f10420f462140442c854866240801c840d80300e0b0403c07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 960234442 1250 960233192 960233203
    0x2131b08100608060102100c0518121b031203010909021212180411030405060609060a0f170304081e010c0e010c061119230c0604030c02030a0c090509 66
    0x140800d0109600c10300801081c84000d40c0152600380ca480707507036950360600403842c0c101010308500b02685000c20880758944e010005003440d50401e1041d810403083d00040c805d15202c041071816540d040341240b8200001243c50039043d0800040c1150440d947d103124165407640280d200620880d070b142681011410007490074402c0310000030103010052032a2400341c40a1003814085840040220b005055075501c80d4407003100f00e905151810f42380d1130140f805c02e59800c001d8803814031846640b0001440761600a00d4041911031031800c41d01c0c00c5203040240500e051080c1468400c90000313000c0450318010820100080d00d01009242e4030030b02d18840101d007111800480c910030868058000342c1c1e03c0c0d0b00005014803ca9100d50001030258030743c141441e02d409111610b004002c01a81c006524540c0810303c0484400303426440801881018003d103018820240c40c020301c2d8000c40002008a40140ca03c0a0128000341c1507891420065403580d4246990760419000140d0b00c03400c2c421010400c106 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 960235692 1250 960234442 960234491
    0x303010e0c07150903050f0c010b0102070b21060a030203060f160302130e070c150903020c04020405030c010503100b0a030906051e1b09040908220b040b0a0c0213 71
    0x1030510704641c9890340c034100203003007100301d1029403a134010008240c401c03401c0716040d1166011144d202c1e030300b40c0030040c043e001441d242c500500c81e2400100704060a802106d82084500d665980040e0440403e0059240d0003010158450b4540c64004090780381880700c40d21403a400707403007404c05240c201c044100a80340c4001d55000c15105002e0b401441c0258601c0382c003900c8501e81c0200c81c0b9511101c0448202002800c000c05a9045110510202d0704a0708280c025500c260250703120610648180412402a4425664107500c05041c030a00340d4050001982c10090802c900b41e4015190355502486d544842e003002d0000f07580c0c2000d103040c81842d12804e50041c090010f44008418002210b81406c103000d00b21038219040f51040d4052102e02c2402c803682070390f001e0300501c8001c08504206140340c1080d800788003004509040541e40e138000800400581e20448851030815044c00c8a4200c40d030840d048000501c2288880000569110b40320b0b04502d10b4051404500d1b80c1c00f0007503160f0441c00340c81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 960236942 1250 960235692 960235711
    0xf1e030209180f0628170d1d221401090605041a060c0312010f06020f0708190809041e1112060415170f1e2104090e0303010e 55
    0x10b00a41c3d000310100290448030440d201c0c501c1340f2045076129011000c5a020000f011812113000455400c070020340401c1c90000350548680009006080d40e00c1c1c038160145c00a80810450502c07028584506c0d404240c01098440d11001c43c8607407030110441c0c5401b8078144000300d8800041111a40c180118406007101791814440c0d45840801c1c0168070f817202019611400000c1074030384800d64100242c5400d01c00599801005584d170744030360001c03010035004100040c00f40300c0c0d01325400300d0f000501000300e403035100007010001400d0075104203888400d00b00321009081002a003400360f8480c0110b04680401c107943c2c00c1e0844149022004030350b001723046001043c0c000d10001145600c11401d056202d02d00390703804078161007000350000240500b504407804041304003280400a0000183c901a4146020f048454458009400c1045010103500340416540001c40c0d00c0383e4810968502080c54240a00840c141502c40c0f134824203541041c41c03106516400400100900004c0d00410380e007100320807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 960238192 1250 960236942 960236989
    0x303090313121e061503060603050f0f070e04050a0c0902180108070c0201080901110417161401180b160506010f0609050d0c03050111031509010b0a0f1e030209 70
    0x580d100441140361071034a80361141d1141450b428411550090703085d10b10b100e9000340740300e5100e01d0800700400345030005880c0c0b072103450188011020009100164101008000c00020780b8028420170000001001103903a405030f442c8040000700303d025000d020f403680c40800b60329110803c0285401d0724520b0b14440c108003c0b0b90a01c04c00f0340d0850010a40070b0303020300c3c004c03110381d9810280381c0c09411100d10f1894000f00001c1e0006156500501e50f0a0201103a025030b5000142c40103003441c070003003d00403d000703d0b0504c0c8821003258024000134450807078030087c0d00c0c0015a11602904980c010880c0140d001c5041c002400410500303000e09405030409901203441c007418010014000d2a960094500400201d4812000e21a4248030341d00295071000c000e1051181d28001418541c100b9181144049095030034407841b4909105034605807010b050a603420640384d01700482d6104c1c960100c50040c01001c1e6419108129a01402c102409881e1009651000b07540b05000100c3c26451081d4104a01c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 960239442 1250 960238192 960238229
    0x14010606080a0b04090b04050307031805090f0a1b090612020c0706110a0b2d0f0f07030b031203041704120b1b0c0703060b1c12110303090313 62
    0x110107074076081080c030074000594003900b4001c24010306032507401030201074901c0e082200300030002000300301c039502c00e6070b0349400307142d000581c2051383d00c841c019194071003001c9000400304801800350070303030040c104140864098603514501900ea00484121701c000780f01860203111490300150002e014000d0380d1740842c80d004604406548174040d90084c401004200d20306114207503820400c050a80b50490720940f80c5003094551680503000020a1408a0380440c2d10744007121447c0c003640e1301c551680443c203230306c56507179041c0708440c201c004240d0b80906545003001e80c003540302045040d40003d00b04000959900307290404500b140c0010a14200c5000c0800081c03099807003d040030005941d1248041546c0c3c1ca6030035801640d040c0350b8222080c2c103403001c10541044080001c81c0801c481c0911000c015550003e004e02004000600c02c4441100c2c403c030340380d8000350240b00c5000c0280c9583c64250400400c15440310304607803041d103120f00240d0010403030008800340c401e0100f00401c40c112030b51200904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 960240692 1250 960239442 960239447
    0x20315030d0903110d0503040b0a0809011401050d0f170d020d05011406190912080703170601050f1803010504051b0102061308030711010f0609050a05010e0402100521010314010606 79
    0x40c00302c810780c010600e50317042e07000f003100c00c01c150340c05070000301034483d2912403915008004d810100c42e1040d04e982031968412a0007520040b8a060380c00240802c0c1c081c1e0385680720207da524108004a581020440c0802e04e0524038801901101003488009030b0341d003001826500c140c0300c2c1030b00011140820580c0d01c0300d06540b010304440d00003042d2020306565403003002d42600e0b1000558440c421a00c0130407104810032600e20010500700f8030980351640d0700c2c4038003e41144149011544c280c0403030300c108070038415542e001d03026241a41d540c001900da08000440481d00303580c0c0544040340e441c1d021b90070104031030030300b8450102078441c2840205258600403e0000103c19001e101a00c00c41000012655062141201c940442c200200034445524100700c80001010284660201c481c50100420f174071105a00400307040366405903015045480c0c5400304111045c00034440f0040c0b0004024202141601d45803080390a208084500300780d40c55810000d40403403e038500f0000c01e9252540c1440b2854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 960241942 1250 960240692 960240713
    0x1170708070f0e03120c01050907050604091508031305100807080a090f02031608010b030c060901051312060506040b010203130915170c0a050109080309010c0312020315030d0903 78
    0x10322500d02039416102c103000c1568414005540680c2500030103080c1703081c00c0c0007180100740c200888802003145a9803203e0305a01e81d00580905940140100001c020800440d0082d40ea5500507208415400d5a00c1a00501e103901615a8070004101c3c0c2000704207902e0291040400d002c0c09040000c0185050707040100005401840c8150840e03540749a04184002140c00440b4541d0180448554803003141c801c1c08054650312400c14a9800c0031031440700d609021811075410780b0080c102a0900b81d09200541d06034021142c50640302060607000150400000c000c0c1e90281c2c040c030b50004a41c04c00805010540d5031001ca424155402004450700512041d1b410350f046905000c0001422000c4800840d55804070740d00c40d414460a201001003c1070011800150001003240d02600007a070340c0c1c0064610023251701c01d2100581041c0040c03031007540144001580e940c803e2074079808030000c81e20070a08980096858807500e045072441007200b401c1c1000604aa9592030504280c4030b45141d42d651a1403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 960243192 1250 960241942 960241951
    0xe1c030e0d080c130302040c030510060c050c120111210105060f0304020409060e100b121203010b0c0109080706140c031003060f090221101b0302181c0201170708 71
    0x10703c00044404100d43c0405420b00616401001031050908040004028007400d40c1c003035a80f52141d5200140c803d004071000c0c1c520070743c408060b04040c88400104512050f0031906007001d5526603617052020310740140181492610ba0b030b080c05640004008030011003205812143c0108420000741000c2c1c0300000c281c0c1d0344964102e80c041010141407600310050107000d40600c02a216001800001c40d1142e04514030000342030744ca01410a115071080303030307640c10b181103010b00880c0108014011501d14900500e0064000400420310505696407415141d105460a64103107554136021a03100c8006140780c0e8000442140311415820540060049040c0700c1c840205116940c1c0e030000c0c803c10f1903130800c03494107400400101004c410744060040d41c0c0501540c1c0c152901a1006d0341e00304613803610036400c818910008504e6148000c050030760003544002031401e0118403040b81403466a607000440740988030036003480420404244000f403c3e8542c4c080c501c0c00c0d440464010402d041390305c1034221750301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 960244442 1250 960243192 960243211
    0x1106070305072f0601090605180408030c0a0c15050a1404020f0d03090f151b030801031e02150912030403080a272310170a0e1c030e0d08 60
    0x100e2495800814030300c01d0f20480b10414000e03c03000243c4c08102d1340c424000c4a10550381002c0c0018440301083d1811400c441c0148100002d1011414010b941030241070841c107682401010b120840e22402c10001803044002c00b0561503a08004040500f80036001c40c2c216400d207225900e06065001030740114400000500541d01c100548007418030600e02c2c44001c02146204503103681e166500d80c2c9100c1c046144400c0811312502000e03200054820b614250315405a589008030790943e0f035000c032000d03815110b042c1540d0601800101607a1009a00c1c52450550f6200640e00e591801c288103049843c0740e40089141c00c2031000f0008a82d00c08111195028546401203950402414a60180e10b8807900d0200000f07201e60086501c6c0408144056080c8403000d06821022880080000440080500e140010001d403000d040c1c1d142a120030f039421000581010131f59032181d030100751510700d46110803044100c984801894061b094490103880c40d10702805012000b46400d4003404070240580300c0d010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 960245692 1250 960244442 960244487
    0x3032118060702071517040c0e0601050a08220203160801050108070509010b030705040f030c03060f110a0309140a0f0b0a0c0206010b0705070e011811040503101119110607030507 78
    0xba864440c0c1d1001104645100c0c01b942642494140005001d005e4002d1660140041001c00e01c42d602600075154182c1e22a502d80ca51541c07403980d010303942c1401041084418250310000030040e541400042c0320740c40091001184545000010303420f540c01039104010310b8010700401c0c403480c1c68005406064a403071403217031035403a11602811229031046500c080d0710034114210200400850020707142c1102d008440602c82241c0030b0b071000003220726100e10200d0641d0304000803c42203002c2d2b0007002643d8004c030f00a8038042a580c044500f0326241c240d084a00c100c00300c00d00b00410040c6022280c2000300d43e2010802000c0b00807000e5a115410701030f84004000104492041003010840200500b0784e883d00c0803000d50391903018450440c80e10380700301007642c14001c120f04010502010b942c1101c01c014020106441410086001404001c020100000c41005802c0f800705034520080c0108029a4407601c000c02180c64160501d00c1c0030704000c0806041c4400c0c40134a503030052044181c108030032840e08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 960246942 1250 960245692 960245729
    0x2d0902040b0304171608070c24120b0109090903020a060e030d060e0621030f07081803120910110708070320010807080a0912030f0f27020303211806070207 68
    0x1c02324582d4440e0b0341c451050315aa55084c034040138070404400c401c0d181c41210841c218408010354201d8040c0c98001a030b80d01042000714059000030741c526001c6c1c010769a51542c980c441e2002e6683c58166070100d40e00c0029405181201d030b03c1590010060b80d8210320003424240001106081100d41c5102081034000c50f0125910085c0300312036412200c0104641e44a0342d0740b403c0c100030341024400500c2c01c5140070100d20a0f081c0454440c40e0031101e0b015070b501d041040c40800c891891545801d200f04900300c01c02100c410802c006020181141b00001c025441c84c61403c0c1e00541c10b904000c1e901000f20707890000180e40c011030140d8005006003030441c20351780c804a80b03200a00b4100b102a01c1d03d8881740c07036038160b01e4143c0d005000000301000180301601c00c0458804c1650019070f00c002402188200085600c0343d10405030203410300c01022340e0324207603401c0721486510307400d2266140f00c61651010301654421890003120425044405050342d0b1800c03030070107519040d040c0315841500303888107880c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 960248192 1250 960246942 960246953
    0x1802070b041b0914060a080607080c0d0209041118060f0304150b041401050114040b0418060f330813080405040c05222d0902040b030417160807 63
    0x90016000083e420400300d4404004074020810070364089015031040d440220b0340180204405224010341c0d102c40c00682c885040d540c400343e10400850380c0050b400c0c0107058155503075001d03c3d60500f2120074401d44603c00c6034074085c940358a41280a228200801405040c3c114050650350701581214086560400075819107020f4442d902080d42c3c41480c00402c21003588a403140c00f8161030007030340c03561400150805000c44510032801a02105076041c00b003001401c0e10b040b400008045840390108005640d2036681005000300d400c8108074188640348921421104903401c0c0d11a0b03415440c4541c2c1c1c21741c142c000380030460050030400202c1d103101d0000c01031013643c604030380051201502c02c200e45041d085000f0f00036042820754840c000803035107042403064483c80190060315240e00b6008441d610845408896401d40044c0713038135034640324100050003091440030348014143d400c94141d40c0e01e080c2c84d060f04070b000710f011348415010b020b000788081c80100321030311601da55000010507070320314940c00c2c0b2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 960249442 1250 960248192 960248243
    0xa260c070311091603020310180c0305010e150d110d0c140307060804020904030c0215090f060703090e0907030503120106020c0103050c0324120114130506061e040c091802070b04 78
    0x30301c423003000341c0f168279140101076444240710104179641040f040c8d0b21041c3e20a100c00d0f0594110904420003156440e45240c91407184040c0c3d4880c4415000c01900d40c80440d00c400c0010000366041c042c0054104031440e40c0041020040320124084c20082e814494013410040c0d0141000e03010301c0b2648001010140100d017169102e5400074424042c101c4221b100c0d014550041905034000c001c10001e60420341441c100b5904406da140c1c54811900c1d0400c07000c86010304004142c028503100e0114000003092081c401401c003131101c00d40000c0d480d81072410282c0340600b03841089040600e000d0400040749020826242c02018424941c400990b28201c0b040e92070408040c11603020724150301312421401e056102e0740700d09041c2c54021511395600000e19a4003025a400640960803110000c3c01030b20b8029040084440c10007600700d455a41040440c08440d80360084101081e11064240019000d1025486a42030f0442082d450702c607090340d801f40340a0014000034003000841841006a0303440c42130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 960250692 1250 960249442 960249449
    0xe1803130b041a03010302030c1c080408160815060f031006091a0d050a110d060e0a020307080712080a03020408062d01080a260c070311091603020310 66
    0x110308881501c60000103442d40c002e104070750380d052501c8a01e00f4800c40240640c0d04032900200a004e0081564050020743c20060100403078550840100d071001908801c06000900b112200a107183c10031110113030040821900700c540e02d58090b14085d17070b400ca5807060a070342c00002940c109692001c003030042490410007480d21070209040c584040f034218101d91040f00b900c0d090019643d901c050800c24080a289010740160094000c071546601082c0101c00c4428042d00c003400041c564040c941b6a002218143c85280b09290804001036081d49010400c1c440a81001d00141c0004c81ca00149010407240c4820000c151031f4011841c56100c0b4060380c1a0380040544806981141c9049000c0c1e101403a5030f41c000d400b4001c03c45624441c00c006040c62203060344c14040060050300c400340c8417041c080b00304100110090034880c503145090018040940b44d84907000c40184441421803602d901c050b01312981030750084c680c2d02c00300605070304502141440b0a0681c2401a03907500d8690307200c1c0c9484101e40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 960251798 1106 960250692 960250717
    0xa0c020a1a032706011a040f030308180f1f061a0c16210f0203010615020105090109080a0f03110415020d0c02090604020f04051c031403010e1803 64
    0xb46d6986020f0044203166050070b03660b2030980c0382e011040d0001c900141171403080c000c400403190b40f072104401040340586003054041440c2560341800f0540c031502c174211029020b00031449a80090050151586c0c81d80300449c0c005c103264915441100300b10200d100b1054403111107191419898107070723008043c0011400c0255092421261000b01050341e80c2c00340c4154010040c1d03401d105160060147d001c031902c1c590070707514003c6d0848400402d0321806904040d4440c0025003544229403071404103042050782c4201840b002c400801080d01489201d0308005000f03d0000340060480e072280d540b030707030858a400701e0801d01182c00801400000350480907000200b08036207170035000342207c14100c550355410300b6901c00015441ca060802c8801c8607110307076000c060030b00d03a002001d48010506050650300d1545000e416000400000b80045801c10703410080030100d080c00d204490303294282a = true := by decide +kernel

theorem cover : BRFrame.Cov 960071942 960251798 := by
  have h0 := BRFrame.cov_init 960071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 960071942 ≤ n) (h2 : n < 960251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
