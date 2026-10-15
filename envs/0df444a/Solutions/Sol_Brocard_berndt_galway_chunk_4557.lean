-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4557
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:32.224764+00:00
-- url     : https://prove2.me/submissions/c96c47fc-df85-40fa-88b7-ab8e974c591e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 819424460 ≤ n < 819604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 819425710 1250 819424460 819424523
    0x30e04020d0f150e0f0c04031502070f1401060902041d1803041e09021c050601050d090501060314011b0f2303240d0813080f150a09020f0d 61
    0x1c441c0c01c402c000b1a03000c0c1e50300c541e0110134013540031442d150918a41905020f2408090558504027104140f21402c65049a0350683c000568600d0030a42e441d081a0380540c1c04001032165081c0180064015414000e94080d1409a9400002601d54101d8ac0d410790100800e00803959102864001301075409000a0010703113401c0d064900a051a1651040450004d81c03200c5040c52040000281001d42146204d0714200888c0000ca95a02d4400040303400f802950f0440d1091440c0004c0002005030560004003268800c6105c1015101c5489034a8200c414030b1f615003070800800e102c00f4000034031030712011321020154102550340c10004030321060802107044c42140319100000601a02010f44117000508081c10401203044100382c0f00803d215a0b920758004200d40341c08180410000c51210091003d4440780d001c4400f400c40c04204117503210001070b200c0100701c440c0c10215800300054068400556005011000c130452068280400403810300015182c0e1844502010004081c00c4103004141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 819426960 1250 819425710 819425741
    0x30406230a0b030d0f2613150c050712030204030812070e1009090b0a080f03041d06241207080106111b040c020703050a030903030e0d030e04020d0f 65
    0x1d140001d4050100c54590040c14481e50111142d0300701e0961050780805103000c0ca10703100f10540f054011041ca0f002403282e0100900d0001810020302c085849640c1c0007050185550310440e81b2000c0c000404c0300c1e6240c5144d80060700c100041408500640c2d0752901149592600614103544c9440c0c1d10004d40000710408940d800150520016030f9010108041c0745e035084448860310440c81e20040c140d0b454034460404002e40b6640d04107403a0b81d9400c41d26001b810014291182c10030724680060b02d030b9001c1c2c05824284156400009442d6030002140b511804014001c60041a44044407141c1142003103003199115000300f061824081390610940c1c0a0101602c40750165418188051312060307080c010243c041c1c0c8450724143c82030140800c1d0716020700043d10001001c9160002c200d091100541014003144906510041096480581d01c01101c3c020369414148038203242c100700000300c51480c0030300003500407000640d89260950081215034102900042d028006c0d01900c002d0b035400103845800b9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 819428210 1250 819426960 819427031
    0x5070827090a1404140a0c0b0a08010b34061b020106050105270d02030a0503040e07091d180a0605150103090b04080915040905040213050c070305030406 67
    0x403070416801c81500082e8062041c40700640302c0204507102c010040c4068004542882180440f4800b0720038201807a0700f110803010304035152800031031142d03c001d0385140002c1c90b0200008074000158250f03000007616006603820720103014011a0780700e144168a001c4000c4400744240000e05a102c0d072002c1c0810b0110720404030b248410080c3c21603240764070180c1840010091900d01c0110f0300143c4079840711403128030b40c0034802c810110302c40c043c088000075003600c030b40d0748198103201c000005802101c0b08c403855007000d5030360380c10200c4a01d0580d1088144649040c6c0030311081381140b07808141c0c00381040c4080c1c1241d0248411480c5804d003912000d8640b240c8d039100307000606214a9000704102800e080511001e035041d660396452410080c0090401500070030b02c5659a501c070b1401100300a0b16207041500d440c3c0f1030301020000c1c2001e40e0124803406d0030400e03d40d0907411500809101ea418201001c1c2000c50170348060f1441d80c0010021160340e643e500040c03402171245030101040901c049c100026 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 819429460 1250 819428210 819428287
    0x17161a0a06060e0d0f05060c03040501050c0a080708060f03010c031e020f030720060f19090305030a0218090708040c080601081c0507061d2b050708 65
    0x250006004210954185a42440441c1e00710080100d8028203a401034588038103420b100f14140da040d24014524000c41c4244038140f10081c001d90300990103031008011940b0b895581184030703c1403412140110381e500c40001d80c1d0602950030242d2080020349010200e41c0a400081c0c2103c05401220b40447c0d90f80c1004064284880c540e4200c4a07092002140b0b41007502d1010042404003c010404100c01007100d50121402c40750031001104005044440300d0410032a000d030b007114125441c00f82c581c070440655410030114001c0074055a01900c07034510b1903e9944020001c0c4d4403e0190060303600d508000400d403038884803c05881105680e8808000341024500aa040030030b990000c1c08541c00040148441003011805d000d203003400020207401d000400d4070980c0c1c180202900130b0316840c600700480031001c022103482003007144544261103000c005e48002010220181c48007440c0060756405154051340100010841140940c03011410901c8020741221040c039410021003510000114265 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 819430710 1250 819429460 819429503
    0xb0a170f01060302130b0312070c06030e0d0c03030507020a080f04240e0409020a030f030201050403021621320c01050307020303060d061b02031c09020d1716 69
    0xe11446000024041d00e4a190005404a4007440050020b1a50380450050b1aa020044d4510300c140305500982c441c2c1c15030410400c109840c0c031a102c0407074107040c240c07000504081040c1440f01043e4079294560b04094504074000e010041000041d0710901c83c216010035aa2070180082c6246d00c05055500ea05081d070b030086904a4a1081501e9406044800c0302540c00110055000030241d0b80041e201300c4900009005821383d40c0f025046031002001001455810340101c3c1c030443c081d4003240d9003403900d03584103030740c0208034403c0200280d8004041403d00b41c036507942e040c0d00d5000e10601884401020602c2040540f0341c503451805d50545880b0205018003070151007900142400d106013980341c8820085d442c7e20bc0104a14460080200c2150030810030360720011110b00100c4a80d01d803051448000380d03480d805440c08002844134200d8201d80034409005540140c0d0707001d0180e210701240c2d81d480301940040d03101d00b040a40c900f405100141e03501e1000f540b45e0940621485000180107000b500c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 819431960 1250 819430710 819430723
    0x40b0a1a280807061d040b0411070b0c04180b040b030607090e0603011b1101061701091502070512070303020408011506030f0c02030a0f0302040b030114100206040b060f03010b0a17 79
    0x2c03805904510f4080004a0700081d40c10003550f83c4103283c03402107511030001002051140a03080d40280b400074000d00c0982e0010140c441544100b0521042d03482c3c400340c801d03607030044e8420007020782104140d5030420002e03608052241c440c00750001c11180d140000090420001700c0700f803030001c1e800fa403042061624518082c5e81141c41034000308000c1801000020319030301000a01410711460065002c415002544054010130480e1916100380002050742400f030044c02c001075411100a0361000b02012182c401c07101c165620a000340400d4142c0034401c0083e0b00050010b0342890760a00c03000503508428064008201c4425004009007410010083c048400545540c7c090900c0c107a0040c20301500041141c0640040342003050425070b2030b0008802038801d5070802c040003100440000717190101c0b100c9000e601981110319442640090404903900c1808840140c0181421004508030b07040c0034524125a0b00b024001290b407804220200c1c420921661021022100c50f03443c20346210405c0c07059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 819433210 1250 819431960 819431969
    0xf050d1a1305060c090a0324090b180106050d02040b01050d0501030f15050702060103030e270604110708090f04060503031602010201060f03020312030703020c0703050c031203040b0a1a28 82
    0xd55050805c41c0d80410204503050100500700c0c0ca80000461803a0170303000e03004c690346944a0040c0403420307480c0340051211030241c0e06010000c03206070b25850002e606008003000e40340050a0722000d40069020000503211b501450307418000c00704a0180649803030300805010b1401019943e42070001c0e0314000c299076000d003003024035051900080c00100b0348e0101e2810704590709468610f80350301110000900b04119017002041182800054501c9100d40c11b2286100f400b040340e0400c14000740e445042d001d8416240000d00c10305040110b041c0a2505000c08044940090000540551a0008a0302c1c5500c07006000c1e250500540140045680c2400f03210042d05001e10b144129919680c0403d41c0c40d102c1141c00d10304800701000285100303100e81e044d281886a00070440c0c052589d2810519112541d60081e14028011030075034466440d4030004481c01142d00030b14030b1000342d4030f034459003000340350500020814800100c1604001d648121144882d0341406c105c0e4041e074a4880c1120b01103001c181e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 819434460 1250 819433210 819433231
    0x100320090a0924181a0903190f02010b06030a0906060b040612231303030f02040b2a011e0b09010303140703020f1c030509070f050d1a130506 62
    0x2214002450004084002c82c0d010484400502c0c05800d50070f01074842d255450783c1c000302d0882c448091003044407084000e15406104013509880b00e1004039143c1c8500f00840b01c8001090b89a4801284280d66441000c030040c4000038651400348000b51195000307a4000c1211901c5422100902449100d03072001400c9c42425607141500c0d203180540441c400d00c1092902039070354004007022824000007111400801014210240b5001200e4440140ca07600705400003440d181e0024180310350f902c2140d054541007103515003000c81e1741c035042004420400c40301c942d01000650341422120709014120401c03512011041c5aa084c0441e190100c5405020848c400e02e00d51b40100082030700a420740d01c203840024686940d480450600381c0c98200010302c02101c5100c0d020f01d0724aa0708180210b52503034130a581e41440301d5114252820307607405c01c5014003c9095482001008113103803009030b10b01e040348910740d600307440c102070716507a20f05103800c039210800044050000c81c100071091040f030b54024181c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 819435710 1250 819434460 819434471
    0x30c0d021309061107050d142104290a0c020c130b06040b0a051803015f0f010e01030f081b0c03280b100320090a 50
    0xc0024555040441011000c5950303021010140112900411540c4c441c211845030b0310b000c036140143e40c1c0d800c8074076484002901d049004490b4545001142c00610389902c244c0d940346e00c0c0043c45814078401420480e03c060154061421010b95440f45e0a0f840c0d2490f08440762138a010711041d029158280e80c49011500411510b003290750380c40400091400044030001581d080b40c0c0c003c20f41500c600c0c0c08c010452000032032441311960340b0100500040c1000079101d40240c0c2d501061500303980c83e02401d900f05030409a084c0ca06000001c41c051441e072000c4070428018808030b03540d1400c0c0040700c4890380325030a6100d0b0070b00c1403003c02d01080307412410440504403c0d40c581241180d010348180002400005100454000e100b0b4840956481e00c46800c2c0e00e159018544109940c1c407195160b985010380620240c00090400c1b80d040d454225003070070301045900750503a80d581100742008100360810400d05d00040301003010000940103440b840b00340c0c40c1c0440d8200d01000f03040d0304010102c98805080c103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 819436960 1250 819435710 819435713
    0x30b270105041106120a0908090a0902070204060b090105030f06130c051201060801050a03060c02011e0203090c0a08030a050c0114010605120c03040c1e031514090604050705091302100509030c0d 85
    0x1084a281d01020074038000400784c4440c500810540709811040d0790020822b040411481a10f43c0140b1801c1e20845040105503540c88401c0c50b40d001d400d0149000c22400d000152030054202180e950041d0001d1481103400105030700c180071a45a5010100040c80c04075403036518050a5143c1b50140405d0f0820348c0f540c0d0714020005040e0340250000030442d6031191114032140b4000d420400805403010701e880d49201d19440004000c0d00211011503003842503000028490900d24501c4003601c0c3c08002551420038200da09445070741c0180e109003802d40d82e07441141110748070508554082c1015607585940c2e01d80300c0c80340c0b45000300050a50980c40ca030800038040010301400d4104200d072110985418001c5130313240c2d010704441e0540c0c0701804802403601c0785055040d003030340040214070390200b02c852151a4084601ea845404880c000c04650010105002501d40781304099880800025460b281da51990f02040710081001050400300f4004210880d142c9014802c928501e00c00740d51101107400c60703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 819438210 1250 819436960 819436987
    0x204030b0f100b21010909032c04020912030a051c1104030b0703020d060602030d1113290d060e090a0f1205090d0b060103050105010c0b01030b270105041106 69
    0x148158004800002290710030007411192a00740300ba6804078131300c1a9030751840b8070760282116080c2100011111002c003002c40c0b0140360780c1c8805101c80328840d0000d0342000c05100095000d00311041d8002401342041003024420001030000b82407566400d6258111a40b43c44199084510100034a034100030026810000510555040700d41001c04208561540c000c1a8001e20403035409408407800d00c1d41c00319810750004004c05c650300b411001000001180c070301c60074581c026100300d10b428000c204010894039241071300010140b035001080b0110480740000c004c10300c3e8820305050645984590b0104425044121060790018192020307000c00f00b455512004100610140280450680a0804500c501ca4000d503410410003800b4400f05590350308081f681c040301283d91031700280c1000000b16655100f40624001d00e640104540c80fa6400c641d503030204258000c0401058010440d040c2d0060490110140c171501d60080001640d0706260800d280c8410404c803503140681c40403c1410104145d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 819439460 1250 819438210 819438241
    0x8030705030f0f0403051504020a08030c0c040903090e10030203011802010c0f1e060906060609030507060e0324040b060f0a0306050903160507081006140d02011404090204030b0f 78
    0xc842c410b295618104140441d060003660005001441504641c03407038144c1194401d40254000c480b0a030100d50340301c3c20035543c0e10501c038100446401003000040142055000b405506110381800760140b502c4262084441c030040303900c52020481c040c0104254182031240184901c0440340c0701c90a40c0340c40d0000b80141e19180b10003010000b103842c004007400814900d000c148100280030803d250007604019018200140040d40d4041ca0030200007015809010000200da61143c003428045192036800e58005c1c1e00d08244681600400007040803010848814200ca091040403640c1c5604007800d1022916800074081c41c040c10281070202e415030b803041150011641d125001003440d43d1200704580c154001e5104604d280a00420580300308200803c0300d0007034400d04022200c440d0819015407064865602c51401648600740507510b10307060040c0e807001054010704040c0e1921010106c043d040780c7c8503511040300d16602040a00c10000003501030380e0410401440207001e4149120390740702820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 819440710 1250 819439460 819439477
    0xf030c090f1e0306090a0b0105011211030a0615020703110402250605041b0506041502011514030c0618091807030c0501090801051005090613060308090405010803070503 74
    0x1401140c441001e5490a1030750780701d0100602244095180744100d9a00140781c10201d51083c0550400240c120b60006a101e8440303400046200ba1070b40b902e801503500c0f12400803100c5076035480c3c4c000d801008450200031030145a8109002441720f240024492041c02810004000c41d00030034801c10124035003501019040c001140c0050741c078102151703c014003106115014030500410803150701800b01586c0003034803031f074020300810300850198107120300080b44600031540e101070148030a0005214009202e0300c0403c0600000a00000142140a5135200d0f07601035081a06000802c1c5201c1c14240f054944600d004e0700d41c54105240c040d0002c0303072070040c0d44241c0d0240c03569500003000c110a1485101001451606880581351079080041e4903003524002e01d408141101000252501e051107424824a44002c0c4070303021508210030000140c00141a40d6804000c1c0d80300d05040c2c05040c46240c0045100303c04441da03a142c41001d0009a0700168043c0c0d0b1540c1003441804081640442100c2650 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 819441960 1250 819440710 819440731
    0xd0c0216030201050c0709050a0204050a050a060203030f060d08071b0b0702060d0c05041d06010806010807020d0e120106141c0b0a09080d05010801021b2109030f0d02070f0503030f03 80
    0x1a0b0407145c01030f02d000e04503400111403e050400b801101d8289500810640740191100e50b03029445500741701e0358000398803c0400592082000904100e0895800350b0444001000740222041540321400c168015140580e0000d1500d070320020350040000c0014000c100c01c060241c14000d00d500000c1c61805401d03403200b0038a03154141010100c1c4640111809003110203e52040c5d07410745035a400c102e070421150a804200100c001c14081c0d07002d26887c0d48100916401007403105c1c07403004215200e1000d0182d864104161400c9008842c1c3c0038056400502010030034090080326800c1004081030a42040c000c000c03240743c060401049010346a598400a101d5001c9000407035840c3c0210030348104c10310700c07440d00c1c078110010504032419002001003c8056a102c00e01c548105442c6849100c13030030300b094103560160001010000d00c40c000c0c1c03090000003030550b22500407c140f500c0c10001081030000040e0098001440001d450b1004d600150105800030350a05502084102140c40044c1049041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 819443210 1250 819441960 819441967
    0x30f01060801050a180e060c0c0c030105010e063a06060e040512030c0c010903050705010c0305090c130b0616120c030206070c0212070602061005030303040c0312230d0c021603020105 80
    0x2e0111ba040091110b032020122100c6107010b0001351660741190700b04240a010300000100c4508c1d050054605841c01007110700c0294440408111083c20a1070381c032138600c20010103210401148189030b410348641800c0c50380f00000d0500e031400c121b411b190410551202c51400b808003180002a011010000c0346001c99075984404e40b850b400f41c011012146a02c0d800d005c03254080550100243c14041e01c0b6000a00100602900980549d0004c607210601940034070b513502082d1406002d0b80d81050400d420000701c105000b4085215640706990300c80d61020859103650400003120fa6019808503540f0303001c001c00803e650000d4903008040d24000412244401200c01c2d980d41800201e801a41d500840e410700380e5507140652602012200c0000e1240c0080300012282000310403648640e9202242058860841e40c0314501c084081780044100003080040001002e06010300385030b10034044030241d440742c1c20344002009581c44d10448100f150003142400b007210101c0e004070802c0c0d9a09085c01a117 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 819444460 1250 819443210 819443249
    0xb01090e0111091212040803070b09010e0d03020a0905040f02190206040c0e0c1b16050d0302070b0d1b390201080712021305040b0d080319060308030903030f01060801050a 75
    0x3e8900d0082185c01e2070480010000b4000c80004000c2c01e00600c9030209044540c1d030320340380508841e8944809403ca4012a0004090b030b482030b4010140003095040041c4e900e1385940100d02180c50310a805801c86600040c502030800c501c3d0f080c044005454402850940307441c2c0d13074005c600c3c54103105803100c1a983c480440c00c0300300b68505503002140e5112442c0300c61100044650f54440da281c8406942d1209054080303503d0504e0b06010320181e0b01500102700e050b01e041000449540b101c406901c200c2e9894000d1a4a0003d842251400714002c1d5142d071340a001080403001007094012540d00032842d402c0101c00d030f41200740700161080341c090078003c2e201d50703868006844103d50002c006140902c0052459915550301c02c80c0819208140d80420402c90241d007400000002c04e8009041d4032400d1000409800905201c01d040d402501804114507550750b40b520300031f80007581c1c014183d400200030010142c3d600c0300340b14014102c41c0b406102a51620002c10b08201c1c060080c014860844c100405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 819445710 1250 819444460 819444463
    0x32e030605040803101406041a19090f05010503190e01090203060106031e02071a07020f01050103030f1d0f04110c0d020c01090e1506160209040b01090e01110912 71
    0x500854000c0d406010030b103842d01e4a041c190f4400c03601040290113006020810f403075014007541b0101000780001d0320f800d081181e11001980030b0b41403800300c124100305102c500e01c80151941d46010450315400b007410704000c803080e04072180d50070042c1000000d000300312811111360000400101c3c45140000e140300001d0400d0f01402d00c0e0030b8040d40601c07540b000021490360662103c5440d080521940804404907804c200582c40380c00c2002d8118105005122070301c000680c10142c100040d40101c0f01c514040d00485030940e0000d920640c08108070b081c1d0700c440e468024a000030010845541d040c2440c14a500003441d01d400707885914082c0781d65031920310050b181601100c25905060003203842c0d807841c18000941c0c03880d00044450000d0154500043c0c1c68201054290060380a0400c5d540306030303004000d000107034010303030541c1121030741c03031403e003805030b00c0700b4240300d006a000d000c00401560609078900b007030b60901802103142da03142c500e0700329541d0348107810303101184400c41d084400c41c0710300c0c1c2605 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 819446960 1250 819445710 819445801
    0x103090201200d0906020a0b060f0a0909061401140d080a0c06050f0402040b01021c08070c08130f061d0409020a05060301140109090b131e0c030e0c0603 67
    0xc0c4030b4000c800d00b40c008056000500501e0a0030070b03a42c4810442d00c41078200d880e60100310300100704056084c0494040d20300200c0d20140c8400151220f00d6042d500d014420984019040c29201a03a039040f04140c403503034040c2810701400c201071003040c58040c007401086440c0000b80300900551004914607812038400e0440355000f1f50062014003503070034005004032111100703079402c0380706c0ea1402c0c00f01d0411354008103a000c0d010815205148800461420503251000020160700c20440e44100c200000344c018005403180b030000c00702511050b42040c2c2003440003441500642c1c00e02400a0403040441800680c07001282002d403408111100d861021a520034400c0e040309a1010307003c00081100d03114000002403001090740e80c2551503640d61090303012580002c42c515000203002d040314601000680080b06071000f40c2604c0c00c0403010040031801141d40001701d6400280d1130780201203c404003080b003080e6000040f20071030718509101c1c00c1410540b0140c0d451381030605114085195204558204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 819448210 1250 819446960 819446987
    0x15120f0b0d05032d03040809041b0215010b0c0316110307060507061b080106030e10060f0e160905210a08031e0f070509041b02030310060806030a020103090201 70
    0x481c100640c50840d803a03403c40703001e07140290402002d8421021407210801d052079030500d80c0d1361035034565840c2c0204950160791010303002900d400242000413190441842c000030a60b01401204000540d4013000a2040c0d0003401d907100d09101541502070302004a803407441140c4010541400d0515084540501e80f240e9142d00d0300460303030005082034002c0002c080700342c40790700c04000440700300021060001d84403010f140016406c1d1b00510526000358442210880c180e0221a02c00200300b54400c00e9419940201100c01c01c501000c0004a85000615411101202c09105000c04090740100003030300901c41c180c41013900c5051405c00091040b1206c40c078031002400d07500b41103601e08010160303a2080e00c410303405a0006c14858070b40441d500d0094091056056008441d840c1e170281200d80703810501145a2040d07880b51110b40d03003810b207026002140e55031b03000b440e100d160401c980e80040c4806e50001c424050300c41d00b0403585503404a8a100880c0c2c0c2400c0004043c1144d000407151510902c58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 819449460 1250 819448210 819448219
    0x40312090b15010e060a0503010f060903050d03050712050a020a0f0c0228180902011d090c0c030912060601090602120406050307030b0310061a07020d291602060115120f0b 75
    0x9106e040c150f07001c80210f0590b912031a40f032404540d9500c00326008a2588409805074010814140241e4400d8010035000802841c0c2180301280503a404012140142c8078142010f44c005602e40c1a00e40006030b541860f412800e1082c0300c4d09641e00440c0074080498801d001c007080c2d04c01c01c50b5400c81c0403c80322015050080050401030840328020004251011050303000c41c15503030554110000109050951307130310142800300c11ba01c840146081a40215031110365a000620402905440703000344203001c00038610091407542400d50006d0031410441e0899021904100c804c1c2c0d084114003012102120b0310b5103051952540c034030341700703c0003041581c407841c1c0d060141000002e82c800c007580141c8140c07410030104004c034a403514a4130344244101c0303000940000c4085490703004904880d004103c103040760407951b0f0b85144404801c01f6125400c43d5000d03181001007940b0f40d086581044418090300b0400d6009803646848100a0303c09007a030840c0c800441e4540e1950304071440260000444c2120142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 819450710 1250 819449460 819449467
    0xe0118090f0501050f01360b060d200304080319060e0915070e010212090d0218160f0e04020a032705011406011e022103040312090b15010e06 62
    0x1520b1400703000c05681040100c14a6400840ca80d14507030b14040101515201e85241d0b01c034000044810043c5090074980003039524030140c085501c0b003100411107444040000910164000c4120100c00c060002025215800740308003c00208000110707600500640c0303a800b40407a0400e00600a0711060304070009403204c14040c4400c00b140002c4481c0d030004048405019603a40140840c0c500603804840d40c0160703c60000e8940f4414a08003c201121002d01545003621064010940f0420703400b0008400b14011030401c060084104440d9000c20440d1600b600d412100e20001010a400401a03038841c0c2c1d40002c031240e005000341e02c404810341d11044031418180d1070442406801002034005d07200340d400c10601c10040800404501d103c1c4a0584840f602d08820230760a88581d4480710120007540310f85045c07450b02d41c4016030806c0e00c1928041440303940b0301c3c0a10700203000c0b410b040052890f1500740762403000010510250542c4c070160186100380c5081c160740040364451845444150801e1000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 819451960 1250 819450710 819450713
    0xc04030816061808070210180605070203120301060923010c0204050a02190f030e190609050f160501121503020f03010f15030606050a080607181701061e0e0118090f 72
    0x1d0000e4005640207d501c8854800e010078191402032844011410040740074000348410b41c002c03000b6081240c006421183c41c08158444030708298800e820500c0817410121007000303a0310843e120010600a20803030180b00c41000f400191103006a880001d2041c1c1d168000203400c07070482c7e419208590a1854500d4001c01406c101803d00584a05c41100003410050441c1a50b440010f160030540070807900707480c0c5042d041e101c180041c0744038041112513000b14100301034040010440702c004c001c1d01040315416135103001c00141441c60004040b05140d800c100c0843d011004038a46803003102d030161003810038102107400280c010401c9040c4049011f250034008100b003086010444141c2e03100d100200000c945600420404820383d01c00d070304441d8030071400070301d18600c540344211015241c03882a400180c4c03607a4070044001c00240d9801c5960f99106d00400001c803111040c0c00e654441d820003000b1a034140000d0100751001402400b0603c04540264640c1842d0ba03030050313140b42d070005101d924101d00c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 819453210 1250 819451960 819451973
    0x903031207030b040207080301030f051509070f0906050102060a090203030d0c09090506030111190306030803070c05070603060f030b1e0f0a0606031b21060b09090c040308160618 78
    0x580740180040d18103008101a400d081c800c075041c2d180c008021504507841c550b14000350346440c01c811a16401034650b80034001c42d504403680c2c01015001c0240c641300b82403003c86001000940d015041aa050584c20030103642c000c02c1058000080b52030119001c090f40c00402e00e144101d903001d244c1d25107040040301741290301a03011000c0e590682801e026a03202e6400f09426104407041c042031910f010440300140c034010206104580e1040d0401140040d80d2b80c942d440349420031074005011598001310102004400d2054001401d614141041100d04189510043c0c25240c0401828000e004011440c11b01d90752000d4800e10380c8400d16648030349400180c002c4503800940345d0f03910282c1845000b003406400390161400e00e0001d2030f00d01c4108005120120342074801c0300700302445807504007070b5100c6a10890007090042c11080711805d5032030b14008180415040014580030803c03c0c14030040c000a180441110404207448550140d240c1284c201900140407000c0702e915039000c0e00b100d400404c40d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 819454460 1250 819453210 819453247
    0x60a15110f07080c0d0521120f0c042903010f0612050f040f021f030e120301180c05160c0f0b130b1e0c060609060d05061902090303 58
    0xd0500585040016035001d80ea82c400040c0204500740e0040b0480840a042c10380030011602d02400c2101c0702168002c500000c1240906041041c034800050000c1c504908000c6041d0841007144002100d0300d805500340c0401d000d140035a19244202000e64410b0603540382e8000c051641e11020a0343d2540e4442406038003130720b039100391004252100101001c0c00c4040c03251500c40d40f2074000050b001d545607030741c2c84d10311020501c1c200d074402d84c249615135064a222102c048074031940e48001540c0700201c1d48251401c00040341c0110441c00c204014440344e0062003041144002e4101c02007050f0801c000c00b9a01e60059641c000005500e02c444071040c005145400340c1101c00316000d41d2299910b0300e040801e02d1142c201d8000a4140d500c10812580d000c040c02800c0601d507103002100981408403415466a0111494181035441603040c00b8481c54008000c1d0741001c02200c49048040240da0390945820008200702c0b64441c4900445100001ca40c049820807c00101903d984054981003c95042d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 819455710 1250 819454460 819454487
    0xf04031b080105090f0a150e03180a0b04061b060905030c07140a050d0f0309180f0f0c0f030e1519050907060e06070f060908190309030c0803060a15 65
    0x18240404110541c4d00410b200032030340d0180c0058602c44c201e45d11a5610584603200101e9190f5880c044403100300c506002800032103d0b03805000c0009080d000030016005516000b41e0030b0880100b1007000843e0304200c0c0009504250498070706283d416080c54070040c1890b61014080380800240041060b00208002c000d43e0001001c034580c041031351042c011851614000c20760444d00b5420040042070580840c0842d141c8640352250000c0d84501d400d001000140050025203900c81c0c0f50700050b40f8050051103500d4241c481c00700078103a05844010076a00314510a0340038195181d04104500c8400c0c0800b580e0b412000c040c080711401e0911080c151800310a040107062858400821511180410840e0032121265140e516200c0701c4010010943c1c0244011610340b065594500d00051440c01043c06040c0207201890306d4200096a0000003084242030104141c0b03030102c4440042e801c02c200b040226040300906031242d0f915801726160150541020240da807017200f1004d074942d48840301c1c40c0c620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 819456960 1250 819455710 819455713
    0x304080304060e010504080a0c060e160603060e07091505040e0708071e0f0e030c0301090c05090c070b150f0901151205010f12030c0f0308070e0d05120f04031b08 71
    0x5444542c910341c205d07982075900600e01c03e0104811114284990112140940200400130f00170000b90070162510040401e8200d0312010080d080240703581500c20f190041c10000002074491802c00001008400e803400784455041903040d80a603d50700c6002941c0203000da001c0484001d061240015141c0c180844580001078100c2d021a0040d01e00c091203501d09100c0c40c1c5404001002039242034910f405422100e035058032070300c0e031504107640e400d0048100c0d035030090f500c82082a00305003d0000c142001801ca40d00d84c0e804000c1000001c030040c07441940b00c0219094040511688d01c00121074141c3c4170603440d48201c4600000c1003082c001c203480c003e80c0c4060348401410507240c1154005407842481030701c003841100c00b02040340108800115600324400c4c640740d4004100d60740c4040303420000703000980014082c5010421519009600c0d07141414040f50b52820303207030f03440d41e44580d90394040d410342840030382c08225200c24140e550243d0700a194056150395000c88001c44015001c3c0c0e01c0d2080400c1c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 819458210 1250 819456960 819456971
    0x30b04110d02010c02060901031107080a181a090f04020304060605091b0301030f020d1b05210c0f010e030106061e050307021b1f0e0f03010510060c08040308030408030406 75
    0x29140c41d208146000d64183c40354051400a9000c012003500700c01d420606054841c2103d41c01511200000c1414a204080941d1110300d40400200354466005440281604070304050060481702603a143e034002d42030752030070390354a800350100380580c005010081e001800841400100300c0c1c550010000d60b5416210f0005940e200901200408160704444d001709500300010300c08161301945403103001e40060503900c0c003082544d5074144a000b80c00d65050100444034002d00161034800702c11a02c02c0010059444031085a01210762104440c903030740d51051140c1164030400380d010300c240060301d0000400030050315a903204090b0903450364000005403c0710382e1001041060140c025640580c866500400c1810700f0f034011014507003d038446403640502203101c8041c1900780401030f2030340d20366203555011002c0e4070003081c40040c0f502460690b203ea414201084045d20740900e400c0125006d9141c003240e41107035402e00e002076200c1d6400c040e1100c10008200301c03d0001050042d401144101402c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 819459460 1250 819458210 819458243
    0xd0f33110f040308030903190f0305010b0721120c0f020c180f04080d0606091d070503070509010e06040303090f0b0403150e1005070801150201060f0506160804030b04 73
    0x10034824030149101da800700b0311050010031104006558030544035002c0741c4c40c044c071885d682035a1070f0903482c4100000310020006400c42e0342c103004043c0101070002c0918241081d641e5003800c0b09260811059140721069244154140b0500c11040211103446003004440350000c0001d00081036201c3d103202500ca0205052144e04010454000c42038800300c600341f040d281c5524200f00c1c1c29003d84140e483c0700c01400054565500e03403240300c0007044c56403100c001c0c1c2880c0c0740d0201d5840e0b500441610143c0b00744c81c00c00408580050031280d01140d245400b0780c0d038292040050b1590503d43c18540e40160001c90048101a080070b0010705503008030007140c0905544200520b81ea12440c040140502d07640318401c40c521455405c03030280344c00240240d036a030a004000403001c642007159104000755030a4010010441201e601011404080c40240212811b000a255181d0380d0391044074060007000810400e0404420700414015902126a41e41d8075039900300494a4041078409480c2540030300c14104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 819460710 1250 819459460 819459491
    0x30b0303031005040c090b0c030306090f1e06011101020d200c1209040204031a04060522020904050102121303141611030c10030e0d0e0d0f33 62
    0x20302ca0b4142c0c200c100002d5040400b800060301d0040d40760300511100803004100c0c82809409802c0f500c01080003141c881c5881410002e8541000c0c0480b4000d0b901d41c0140045d000628840030801c0c0c481002a83e16500c1d180012a04911000808501c952002c1110403403248141c01c8030400781500702048400c0300324a205c1c00107502c0340648604156011604480c0b683c0c0d00e43c4081d12000100603c01401c06640340c4440c13182c0d003640880010102c0a0f0003c00040201a2240d1a04402c00b1314170040109800c94a044900300c818401900c02e000d01c0c00040c0c03c101c42501140c4030388d50a500d4001c3c090501500d400c811541030b01088020405201c10a4485e00c1150256001c00e203d0031040888210740d91100c401003912402c0291b0103001d5030ba240c0303049403909048601d1825080c1c1c2c00040b90035251f11a10b0411103052045c0041008505a886649e03645281031000d10780c01c142c9100b0039140e0b62a124a607080801003250b9800f0040e02d04440080112541e0380601c4c0c242070051011204184400c4c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 819461960 1250 819460710 819460717
    0x204153201180303031a10020307030207060302042612040e010f0816050409031202131d130201050c010212040c1d0903030705070309090f0b0a0e0c07060b0f120d030b0303 75
    0x101c084503100c0041001c207109400400b0080a5250041d0381b115070342003c140b20403614400e03140942d0000499008055040000400030041490f01318142400c0543c404250041c0c1c080c0810200034032400c0b54070004081c083c040c00080180b140a955075a100400100e148003481400b00d07030307030054000140d90b003800300d8140002a010084551081d040c80100300c0140340040040d0308000d50110414101d030340900c02041455594034058841601d02250801e600040c0781c40034a081d6001d40074441c1d070219050b45540c40da542400c2c050f49500c4480c84090090051804003003042c40380710107100611054202d5607050300c15802c400d030001090401d8011000200f0740380645250310410000b020240300d00301400200d4031900d031080c4010382d60b14000701602c0c9402c0140300b0603566614040c0b040c3c5003c0c8440c03030061090301119412494155220400c500403030354082c08035601d918040001e55600f00f90350349002d20042c0b505070000c602070701c000c3c1d4409060844c1e902103890945421114900003055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 819463210 1250 819461960 819461987
    0x51204050d020d2111070b0a0f0606110a080f1606060e060928021309020414120a020411070501090f020325120305191205070c0f0204153201 62
    0x140b19a204490b5044c00080c40d01d1195000f49031800c0c010340d400600c10805803070081542d402e001c504000047d1219040710f0540d40014144482c4e01d411821100011030212040ca030808402038403580041e9928000d44140f075010912170101d84248010040f0304d50114003610002c00317030715034140d82e03801c144503a0340c0e0140d0713144a880039501000d5580b00d0381d1030340d0340d0035100341c03a0000b6042c00e0640c0c0500c040d050841d00007148440d00440d09010000e80140610711020085441d00070350742c1807040a0361102c8200802a014645071a0581107584d100800c4400b203e500074020000c0c0800e5040c040303a20403aa10080784039005c2c6061400e40f0f13801c2c1d034180d0080301c911034502c0100c1500d010132a1131108484141142804001d00c0303504003007a40d82c40d40082c1e00e000c640340d14520744001070031681110301c01405c103002d00c04100c500e2000300340a4110b034600c9a0741070318006841c01d071460b020800510340e60b014541c441e03010300c08041040b0000900da0012014402c4400340c1030a800010b40300818076210307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 819464460 1250 819463210 819463247
    0x50114090a1d01020d090227220b01030302063403050612330c03010b0c1606050c0c040b030a0308042901061101050115050703051204050d020d 63
    0x803400031840c40d0302c07510084a210040440210724600c5042c01da070001610944134665550044043d410260111a40401c40001c10607440740710801d40042044040c5c8400400300c64100c0c811258202040c01c0081c05d42c01401c89902076070b41c0d1500a544140c12145005850a1042e020040440081c854505103000030550380c072803044c0340022001050700414080e80b01707150344440c00030b0090a10000c07030750f01c11420000420a0b1511028078088024580c2c90b504080031408100803040d510080c0c80c15501c00341c002c1644c03010580f058610b400160a01540301a2401c60300045030390b044401041c0070340f0754800390f40a03003140c0800c10044409662400d90580c1080d504100017a1190325a503910502c00c503207020490760707401c0c1c143c8458446c1c0d00e40c00c00042800d20041c401e16030099803549402c11000028007003503052000d550742d041044000c00f030900101044603001c060240040d10f151081c00d0082e0a481c2c0303041d0920940c0d407800401c4100250003010a00281e05115011282e200c030401c14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 819465710 1250 819464460 819464479
    0x110f041505060708190c0308130c030b04051e030d06080f0601060e13050f0601090509040201021c0905091905010b070309141f090e011409160306080a0f06050114 71
    0x14802d20741d000c40012140c00008000b01c0100a0140c09900d81e6910103aa411803c00e1051a004c4c141d600e010f0000e0042410829144000034101c000311025258010380c1c4541030b4886103415450b05031303022241118070442e04518214000000302a020810341180d06110035591003413401d807039140c0c10744104103540010b401801241d0007800c0d40d00c0c550030050481c0022841002d000002c070f410944800b0010342104c400c0c84182d680c4481d110000e08001c44d0f60701c105d4100759001079614441d8140c0c081d1503101c404030886055008545250041034060030080c01403070911480161807030606803190400d440c3c0400400c255000740180c0d2000c550607210000046d0424003c400000b642d42e543e503a103c040c2c91040d88441401c0040e10701030401c0350303d940f0740707583c1400740d030f101038040580105518401c003001d04204c55a5192455030803502142c00381501e070404900c228094051504045414440c202e8104200b10408486040e03d501a4a0030401b0b41d88a0100d080348820b50480d07641e1200060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 819466960 1250 819465710 819465719
    0x3020c1203030f0402030c0a1206050f09061501020f0a231204090b030c0d031101050f1e0a150b04030c0509060d031209020405011205010b09060907200109110f0415 72
    0x40007000d80050000b0201d603d0540c440001403001c0400349c11101807080c00500703200400ca040e0141e1038000e1544007400002c1d1400481c096522003008180200041030700030140c1d1240d000b804a6145c00300c180c07080d1403046080f81000c84002c0010b4035038405540c03660340e00e09102c140225043c1e0901d150704003d180781c6454448402c01420009440c0b42d458000d2a01c0344026544844040c2c042604c01c1e11012030941407448001c0c00c4400041a1903044001541002012020807070484c1644014401c0d50034185c42c0c40c0d440c440104421042502c0c140100700002c1500343e0980c000d003044910070a0b0034003a0a80351000d00078040c030306540c282e402081484201000a01401c407580550521880010302d0101e20f07000201558000e03400725480ac42648182d005106c07007030041c6400303d1341c00d580b80715807420300101042c202203008081c40c1c1081502d1002185a1a0300310006560a86120090001c2d0340399040ca1989490009030a600c00c4018202103842c40c01d00d405828540501c0340341c851405841d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 819468210 1250 819466960 819466981
    0x901020616030e010606031a031501050618040f0207050f0d02030a030203090f0109140706020c13090327060905030607140c0703051e070b0f0405040b011707030903020c120303 77
    0xc80d095030240b41c0c0303070300c610807900704244250300040c881543d000c07c40c600c1174148091000005045c03580260410b15042e10500c210070320450464200741e84041e5111a081c2c8190014480c1105031a80682060701031110780c0995000380089600550640303c0401a80924540d03825200b014800035030021b010100f80140039078051544039503140292191042204007150858081d40021990807041700c0e801001c80c002003001e1805030001b4001406404444c10010713040e2511106c908042d2a21592000c0402d1700c601c0e03200d00c078245a03040881d81a42c80b000007a03140903d82c0616800100e81a40004052800181103406903034241c950014030402241d280c6080d42c89003100014a10841100000003407081220040100d80b0360022043c046040300000d00700039035940007000700a01070140e40c000c0b0142e4406c503402c039581220300103180f1007480010790301002444c00b2401d4891520b001c1111080e055004414140d1080e426206c00414002c2000140d805a10100d02598030034000a0041c190 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 819469460 1250 819468210 819468241
    0x30609130c050655120b010e0306070503010e060402041d0624030103060e03040f06031e05040809030c032a0d02062206050a0c03080403140318100209010206 69
    0x381c140c0c1c107004102d03d030080444c0340f50040e40c840c840b0f050414503141440c1160141319919101c0c040c07290003001020000240a800c0440c1103205555888070400790a03070107101446c140a2014003aa4000e00c1c0c0144081d025410900c00e030f88440b035001000540502d0144210750039030b41141100d07600d1a0110001121410004003283e8000000494400304403080c03c1181803403203a50109250741358150710b1304034290b5041210001f02e40c0e000380010b01c0403032402c0000038242c0382c0d035103000200f464000e40c0d0012651040540303000458501800d2206000d00034000f0301c6c117010b0540c21904440102c030103040c3d6614210007810007034150a61843c141001040a0202001008200701c413800f500f600043c2c1c1ea984146140c0c0b00380b04a0341c2000d149401500264802481942030007070801d00c00c2035007c0c10703c96070b200005081021550000f41050b00512060610401452609840703181c03c0744000300100d10760f90b104e05544074081300001280803d008882e922101a406060346840e9a1640c1c83d6240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 819470710 1250 819469460 819469477
    0x22051015030213033c0c0503060c0702190b0412030f0f05190e090a0e15070512131704060306172d0307050604030e10020c0907020a050a08030609130c0506 68
    0x4510181d402641c903c1e0441003000710b200c031700349000600d032602c5491031002d5070001c3d00076003007030081204880d00c03c402d8071407031a0142c1c1c0c0714001c440d80000d049540407480e00b1401071490b0110f00880c3c10783d000e94820f01143e100b9140c6909501d1040d200f030360000300c409407100020300c04101000c40440146c0c0071004404aa040501d2003003020307400101c20000469180359060303560100102c44e11010080b244448002e401d00c4082418112001001c91050b07483c4061002c0641020590340b0350341d030611590345038000d074810400140d980704083c859403045c411000040e040079004242203a2210f03c0c6015012114010034800308009840510700c200c0e1441010000b200700c406a81c4110148020010988100301402136803078145030203014501820b1109000f4210030003000b2130f190300001d4000c00c000040318400700995131403404918100c03205100400c41e0003082d01c4034003000041005940119401c940ca141155904c5400c451203400d00c042c0a4005015010301304030f9828400010175551 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 819471960 1250 819470710 819470753
    0xa022704060b0a0807090212070c0519140303041202070906051e0f06040e1b0a020c0909030f0c06010f0b1219020d0203010e040605242205101503021303 67
    0x75507a507003884c1820520390001911030b800091070003548c0074400040d81d000c1114240710604880e9521010307032310351200c44001c0803d0100424417090201c101c0c03c074104603e900c0300b2203503030f49000d181a50010050321218000340c4510720010851040d94000c00c42540c4000e89600c9651038a00c884184002170303104241d030800203007a41c42c0c032f1640b140d4005001130038200f01c050301c0605017500d40c8009401c41800d138082a00742400500c1d8115030101e1109110039003103600582c00e84a02d00c100381144202c280003841900001184050a000420210b04a840161a070641d441ea114100c80007446032005650340c0c4842c8600080d030f01e001c0d416540d902030499110041c00e0000008502d02240e00c00e070030440d91030200c02c080000f00800c9005007980401d105208020b5401031000c1000c0c90781d01152600d10405891101d40e40f0030100080301007007001101e105100381e0506800001c2c680c3c01600507040d4480041c80e000310b059009008846072000140400603145281d40c0799020300341030504182049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 819473210 1250 819471960 819471979
    0x9060c0906112e020a110c030a0c090b0f03190308090d020706051b070338010b0d0906020a080609090304033305010b250c0e0c07140a022704060b 64
    0xd11200c1e02c0505406401912014012901b102ca11407601300d03c284102d100364400d0780000e0000d64600180002c82d8501399021a16007200e20008283c0c42000914075050b20500500781c0c44c0843c0c01d40002d96550003512103600f0380d01d990069035144c0320042c62a00141c0d101034000c0140c540f241c001000c0e4050070000d200c014048038a20207080042c40d0380f0980d0001c2c80d004807144051602281c041000825101000701c9000c640c00d6040c203c9814410300701003142c0803e030840041e586402c0f1030241548650308656840c40b0003800343c13151b181603540d5030150441e03500244184500000715410b03690811090f407001141c00d01c0c281510498a00d4401e043d1038003c880f507215581d903015181c042c0c07140d55011500c4684c003043d00610a01414500c1c541c040910701107001060201c0c1c5003906441000d50106010380c0c03403030085100d074412900300601449612524241045005ca0201c01c505d02c00c130752420501c504400e185101c0400c40700300c441302d041490042070004445501c0b0740e49154019018281 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 819474460 1250 819473210 819473293
    0xa050a0c055104180f15030605060a05090412020c01021b04150302041a0f01230a17040302070305011d1507021002040b040807050114070f0c050409060c090611 70
    0x80fa0010b0313003d80071561076803031003219042c0c5501445210740f64a201c2000300103402c2d500081007036042d10024007401da44e0b1011401e140c49040d1240d010b42405080d8041a040034500400300c0300038800c0c1480140500310195589620110b02c5450010b801c1c1040300f844a81c8501b000010500300d100e012896040034000001601c0c0c2c0d00440d200c440e040055114800058002e1109a401c1064500c1c1041000116650f086507144552280d54000e007280645481c2602401c3e1004030501c440141522480c00400c803c255001901c503040d40c0c0302d000203110b0003003c82e5541040e20007e07004202c00740c001032400ca10f1045441c6041c0d5129616104a9103501000b82032101207030710030341180368501400242403010360410045d02009000a20340030b4180c0e1b00f1110016203a009a900003014806000c21303800c184004039045402401c80184100044001c1d860040000d120a0074508089201010001280381c018180315031079111803006429a40c40b010142001ca6000e512100260500b200b486403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 819475710 1250 819474460 819474619
    0x260d0e03040e0403020a050d051611040f0912030c18120615061706060301080619090206030f0402190b090126010e07090b0313140a050a0c05 62
    0x180514060317009401000701c1418070360704114001210405000c01001003010300c84458107401d2a490700b007450040d4060b204800a0058904000c200e08d55504158040c8148440c1050150040035180c408010380802e84009940e040300c8900c250a180701c100304100981100c40c2e2800003807502c034040000d910422100c51400c250040d8100c0b0000811950240c1c003036000e005d1665400800489075a411517143c1000203550704030007002c940300c24404103a8804021010707001801c58581c000c1c94a51240740c02d039031180d03011008603416441420f940c20f4558210f100801110103660320541c2161822070308030019106215841c41c011a0301800c0829010300703444118620b8040c16032400310031072130700382403c00130521910783d08003581c00001042444a604445581010b005603ca0310585c18034034400001810500d03240c80251403801400c2d401030030016210b1b207010a031842103c0b1102c502c91260f031440481820b6040f881d040c01c41d035018106900000d0f40c0c00041c00c02100c020301c091600c1f01050305 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 819476960 1250 819475710 819475739
    0x1b06021603032715110a11010f050f0d14010506120103080f0d090803070810060e0d030c0b1305011b090e1003120c050c041806150807060c260d0e0304 66
    0x10400b40309511080804c0d81e42c020180c403442d0200310300914621501d9256013a01c202030f9080907060183c020090060240100309903200080d200d11b40a4645801c0b0103104040c020b0684242d40c040703c0a0004551031401c401aa00e14520614103401c040e820365440c604107602010910807640010311030252011081e003c0d9402d260f100f10500c548a003446203010b04048409011400e485503800824800d140c0d0015040c0f018030011030350401d06802070708060b6182d01d1365000260031004c1250411039800d41c0e02211198880c8601d0003040103241409641307181c0c04454030707541c0c0003500d9200c0800210103000d2805422144541c4200720460b40e036031b1402840385550741680d0204500050f0141440028070084480d68000d40e030600c1000200c480e50f8041c4408902e008010715a601c0c91100d01e1050511910702500810342164085909c60704007030880d07004440d0880e02020358003807983d910390480c80304a8140101244840c18003806141400241601c01d046400034071090000050054951010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 819478210 1250 819476960 819476969
    0x50604020903250608061e011205090109030e1009140f12060712140103080a030f11040e0a0c090b0d09080d1b03050405120c0c0307031b060216030327 66
    0x50f54001c03468508001d4030080d1990042090110510400c80b1a45030798000003178844030b211031a079032040084c0050700c10b55001d03491221070038a41400c001c00c69a05502c044c030707042d0181d16a40000040b400402140c07a6103510710400064045a040207801d11200407800582402030052804040d03000100d48804101c60101c0b016500c09410b001354150010203d00d0302c1a8802401d202c80d80901e04503108808040c40b0060001d4000518513410b1807282d4004414142800e006201c0e20042101c00000b54000d4044c04207103403004408640e030300100740304e07003241410ac589031045000c0c42c04000717007850b40090302e03034602c408d45070070072500020407940060004c3c0303200b0b4900240c5840c000c0000220304441d00f01c084c040c10300d070400b480086100011b060400742c06100c101035036003244040700c908001d8210300140d00742c40740120102c20080c15100301c1192055442e07408a01641c0c0341800c070380d43c0c100104003e9501104800620100c2d1103808404d4aa110780240b40420402040100c404072803203502 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 819479460 1250 819478210 819478243
    0x181b0f151c0b1f0824191d09150601093f02010e0f0409020913050f0d08060621070315090204240c0b0708010e07080c0d050604020903 59
    0x141d11601d15105814031450710b8040f10354076401d07242d8000504156006802c0f603284d0b55807079071610801c09042c8599940c02002600b0111036112020002d682c00055020b1721305511404c1c0030018960007102e003130b50310508111004150004040035044592140070386010f0402004801c04034000450307401c0940a800f0010001d002041300c00d5043c02c0340c00d0760310240f808500b1103040da440585e901c120369a0008400301c0d0071074109410306000030010200c00200941060f008410072280f81002a81810602d00a4040e20249442000398039111911828503101003803409000c03032100c0c01c0500140405a021444803220000300b21a4080c003080d04840080000c0d480e14900f44440d01c103640203000a0286100a40c10981400c5005d0030b526144054540204980f03201a58201d205111782558560480c1e515480c509100100600c50242401140c2585d2441c00c0803680c1d55100e410043d202e0034864203090f06108110750820054800039090b03560164080c0300c203161503682448041002c081000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 819480710 1250 819479460 819479471
    0x18020f040e0105030c040e102708071a1b0a02010902041103071202040524070204060308190203030c03040204020a020f07060201061809080729181b0f151c 68
    0x3d080500d40001c00401501880c1408102c40c0703035000c0020007413a219240200030450303485c592031015084100c1c646c1c503c0010640c4042c4014080c80000602d04103002ea000b0722169104030b64610710b001d00964410b40e80010381080000b540d44480c018042e1000c0b14030000c2600505600002e0660350303409049115a1b8000090080003a0810a45102c0e05e910030415401c2524040009601400c54040001144080195082c0e440700a8003181c402d140c0c000d20030044180c49051015040d0069030300c508208400c03203205030b112400042620310078420044c02c40e246540315401d01000e9007140c0210700a62051694048201c03006100d8800944095800001d0071440c1014401800070905940c6000c0d80c60006c06c0d401180d0100c0490349415046507a142e00c0d8004080c407071950800e03e0130902100c1a098003030102c1d0b46102011070300d04e03128040c101c40d002c43c003240f104203104a081e811681c2c42525a1211201070402c2c5088182110b804c0c004681000d00340034451074800f4082c0104a0100d07030342c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 819481960 1250 819480710 819480719
    0x15031506050a0e0f010e0d030c060e0303011d04050304051201020c120c010c080903030103020907021e03040501110309090a0f020702030604060209010306060906080c092214061918020f040e01 84
    0x58420150b03090300711343c01800c0350036140018112040203090302c0c2c011058040c40c04249401151813110310380d442841040003181203440261250801e02035880d841c00c10300041880d501c0c0c88003c0700e005ea90407030091890103140c002041584803d00d600c294071035400307012195040e2802c0c071406900c01c030001c140341d645840e804000b508413080e9000d6282400070050a01240e903600100356030660703a05440803030481d20380b100300341d141c51042640b001320864405044a04802d010015004407802030700d41e1309084001940c0ca90b280d0141071040d5400a04031000200a110a81c015400b10b00c1d044000503e00b100940201b410b044007250192061900000c03030f441c45503030610540d001440b1078a09010410300340000240102800ba102e04112440403610382d060340d0303a01181d4080210711220316040151101e8948005c4c28440d842c1c0c1d420100030b00f0000e0001c1c2000c0715140c482e00010303501600d0b450b0501c03c99440d6040132188200701c11b0ba00340034600d8044c041c000208040e0084001003000c3d51b160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 819483210 1250 819481960 819481967
    0x4060501060908120301051315080c0306010e01080d0c06180303090c0f030b070c020103231015020c011101090c1d090a0b010521010606091406070c15031506050a 71
    0x80e620200095101c04d0011100d060030a05407815141c1c00c4810014a000d00706400018003114111070244428206c0001841540012451903184041c1c1c26518581e9031030081d04900b0b002413251081d16008404104500761240c040d0000c118881c0c180000c44100081410814400f103605c2200440c0e6039100d09018080842c41c080f00605905a00010241c29503035002d43d5801d01030050028006807019803811a800303074200c11181800d0029502c01d0304070403541482c18110941e0382945c1c00040c0c0d01c02207505900f1000c840d0706d0711415001001004940401150458048103074440070b55a199070800028003444584801012070303500080591030010304c8003464010180c000002c0c0d07031000e44403100140c00008a00e0440320126180c0c1071440003096100c0070740d050700402ca0381a500e0117601090345500041d203c4165070001184c0c800f4041c9910034451140310741c00d406440c4c42c0c05c0e40001c0021403030115402184d448c03d403502046401402d02d241046803001c2d01b013580400c03000300708056401e51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 819484460 1250 819483210 819483227
    0xa0201090902090102030403030503091002070807031211041505040824070c020f09180a03050a17100902090607060603111c0c05151b071412030d230406050106 70
    0xd4607204614100d0600c001035613034880c41c4002811b12030301000003a8060000c0c0701920740c00a190f0020355507801f842c9003519065000d18000c40108805140c1c0c100445403602c00e200c1c207456106400c52a0504010b40000d413080e0b24030807281000b100704400b080c4c01405001a803e094800d044c5c0551aa00c0c6074003410b80d01c1d034010110400c010580c0d52400c00b59480707180118549070706a49040c0e42d81c6508900070001040c645038114140320b1004013508050b44000100700807011552060150030103071603c549110000e0300c0b4036400300b00189050114104541c01042141c1d0010250f80c03400701140d4480050320701660040d00d0140740c0183e8103a2900300441c0d40404801c0840004000070b8940c1c0e81c028103c0700d1801390a00910100340183d00c400c40301001c17142080c0c60743c0c0340741d100c40702c1031640c0a60312500d60103141c04034100000d5840361414000c0c4e1050728440c03600050741c10301c02c840d00350702c00400d442000c070b210340384140900300c003a010080300c9030340168040c01e00030a0560424101410102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 819485710 1250 819484460 819484469
    0x3080304151e0518011d1c09051009090203131209080a1407270b0d02010f180f1701141603051b0a030b0406232205090708010c0813030f140c0a020109 66
    0x43d04811441c1030341d0b400003040c07049d20390841d100d0220180045084403460001e8124921a03231000081c80100402d2101d0f601a56200d690310540c002c0d02030b6011036440340144500301c826484009024001380c1010707c16040f10061000721400c0d10303600c1e1051088801074002d00300e0a00d03c1c1010942452125000f40180000251039421001b0703400e81c0000c1000c038140d640d02c001c00003645100e070404d20040880100a0030303600d10714407043d45c5910a0400084020070f19005070342c60003e0404521f54003801e424410303e03000307441282031085000c05402908000704205400303982010301c480c3c0d030207110016280400995800040c060043c0050004403251034108002840c3c61383e283c03101183d0320006007500d682c1f040d41c0d580100305c0d0511010200140b14188640e215013000104180c0d541d0000b0120215481c0d00c2c02803101c070b00c03508070541e00008245c841c18446c1c0308284010010900600c01c04c1c40328040c40c50404005000000a407a40307400c03906e04c0000f6600001d5089040d5a4860746402c05030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 819486960 1250 819485710 819485743
    0x1811030c01050a11120a050405031018020909030415090518061509130e010e16050906040e1e06090d05030c0a08090708010603080304151e0518011d 65
    0x522900c4006455801007502c2081000041007402090b82c90a101c0460079006141d9555250030f9400341c0904a5005401024000e10800d02201038071203903800754540710910541d0300340c4000707480d400f4003140d6403000303140c140355100c10000080c003801352044400c2c0709145940d0306071000d070030309082007500c0954000811005500b0344c18040f00766120050f44203000490007075143d45940703000204414405031420042c10300c0c035141c2015510b080c190000c000f2152072030f0030740d905484600b161842403013003030092036000107680700020703004d00b025848050f490350f00000316110100810101c003050b50703da002480f007a80002090201405d020055008000c1c02c40c10081e0561420181d00c0c0c00360b026001c0610b040100e600041b900070901070040002a00c0e155000f070010540340e09010201d40d2066074200ca04103240d10b05030003014410710468200005141807102c0c0e44414030300310b070060b02015202c09250145401e0203520301a0034032811884200302400942e94240e501400e074100050b00c40010140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 819488210 1250 819486960 819486973
    0x606070309030b1f08010c12150305060901090308061c0818040227040b1c0c150504061803120f1407111201060608010303050f040f08061512030a0309080904181103 72
    0x145a0448902810800e90071230000360000382c1505518401c0650740007400c140282030a0080b00201900022041c0d4004d407240384290721103000b03004480349051401c850400c1850200c1c2c0000e84444010050345407006640e01d941020640010120f90004400365011a8241a10403029a600c102c0b41c0840c641210700300f00c10380c001e0700429201d2255080c060811005d8a01e4101004002950b920181800b1400041c00c24a00c003405400c0c1c2c1d002e0302840c0b000c40c4221012031411100c0052400590360302a0ba40c00d011301012406940c14800d401c0b100f0203201030300b071080040040b84005060418002c03a80051144900c00038480b001e0701113a5542e44030707410301d5004c5c4192a08150b809044992500e4116610800341204115500854006400540840400295206001848038040e0403001040d240300300c610010803070050340003154001c054005010302c0c2c5640340a648068000c030301611b50786152214010010b4100c0300c01e0f11400300c03107541e8007a54109200754a9070369001c0c051300f07a004020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 819489460 1250 819488210 819488231
    0xc0d090609050d0f081207090b0424031b090303030501140918030903010603060b011806230c061303090b0c071a1204030929030606070309030b1f0801 66
    0x1049614020540103c407603800c02000c01075084a02010796800441107510344102602c03841c1e840c1c00a440d0180007458009000c902040c0d408215800c0307508114540440c0300d0391038000807034500d1801800003455035514541200c03c0600561141da800039549840c00b860462501400b102c8040e04186142454910300c03224688400301c105822191003403000303201c40c00d840c0d045407640c0324800701c440d0154240704000003040516000341c48204001d803a190003180ca00f441700c0640e40454803d04000481300b40c00c21030107034181c0882941c0590104041450010b1b08070440380b400e1810396403501c04688040c60380c030034940e01040c0a006000d820300c00703504c0e000d1518810307035956480380074550306110982c0300e507040e03031600d0800c0740c6d2100d100f80300803815460709080191080102e40304038201d00a9007030203d56840c00d0140000507252013000070031b0030343c0c50365810f0200542100d0012024450000c1020010411240c4414481ca8111146040e07001121603004e01901465206440583c10041c02c0300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 819490710 1250 819489460 819489467
    0xe0709020c0a020909070f14090c1314030a0f1101030c0c0c0501050f04030501151502070812030a1d01050a0f020a05030403231c0c0903021804030909110c0d0906 71
    0x4460741d0110b40d0400141c17220b82015040140c1684580c148840012001445503480000c14088503400c0316094070b65503840c8201602c5103d0b0f0001c4048403c3e40090074008021807000000010401608403803c406079079494188035407211006542d420080380e8640f14135070341800348506041c03091805004003400d0340e03a00071504000b4001d0506100700401c540f0703c4505120251402190081d000b8841000f113408040191401c41c015105e07200e0700c4043e6003403d1030001503c14101d5060000400d041103814440ca4440e41000c1c20300c18400d40c0312a03000c8003002190070082c81e0185104000105824aa9050800c0314007c001508050b801444501c21903504038098941c09901820614860404141b081c40624200c080d1841c000783d01084091400904c030301c0103180d41c1d50703e83c0c1c200b100c00200003060701c59401510009520003405840701250543d00c22035250818840d04100040300d484130640416100c07103040c0e07a000f5400c0400c0d8144900010040320004140c0390500211107424050000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 819491960 1250 819490710 819490723
    0xa05221202030d0c030209010e0f0a0902030603010905030403050d080108240a0e0303130209010f030206161e08210f070e03100f050609090601230d12030e0709020c 72
    0x190048400e9114494054000d104891408034021020041001c80c944d0150003074011005007400100444c0d211041402c28107641406140000c021485d618070f055003500195000404036501765488010072030002e4010030142000e5071081c005000c5641c04080c000b41070010590200020754043c1c050408124521a02c645031000500b41614942c0d5800c813005014000c00c049880c0c0791311001003000424110f401072550740c0740c401c451246c0d1a980e200c0c144551031006000c00b0354008400c05c80b42c03a84004503031721458a94030400e042c1103007c02c07101048240c507002c05415500c0d0341002032850b800700c00d544469180082500400c0b03006090000d030f180e00c01e10380105024144030b90000c1e4a03441d50307400c10010b4007804051a003030080300c121100d0903010702030541d10b07079000c2c00c00c3c403010035a001000b0503103a041c1d51041c040341c9101c0129802e1158150300c0071071065040010b06500101142140c141801c100d595510080b4404580380142482c10040b648582e40840c414020504000c0b40030404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 819493210 1250 819491960 819491963
    0xe091b0904030e09070e0f040b09012702070501020a120507080c0a05250c12080a081e0901051f0602030f0f0903070906031101050a210b13050a0522 65
    0x806156503186002d8902c10040d80c10f10343e000e00030400308050a50302210042d000e2009580e4045c4004815040c442640d07103102d421540450540b00600825204070000824841950004c0380a00c1180c1b40010880e409200d0565050350009402c00d0744503008009500d0066829004010b03510b000d41005004000140811003800d900007018481c0c540716000b90340c03507a00c4954403030b85ca00b640c0400d920400100940e00b240c440b20b42c0c03100010818480c0310110310765508480032618001e880b100484200340001c140144030140c400f400281030002a070030622410741e1800004075401c2ca10324080c40080044811a20020740d403601748440c0da4040240c03091900d062034619154070000100c0d5020f8001c42c10010307014882c44200184080e816002642243e0003030f4136115440c4082d50045416124a100c0c2001040465002450005101e0f42c0481260060180004c05610b00f400081c44540b940c05161480c94032002070214001c8180306054002c00b01900300200540000d00400310946400c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 819494460 1250 819493210 819493219
    0x10b090907050d0f050103021002150109022a01050403110319030207051e100e0705011409032a180601020a02010503100b070804092004050d050109020402040803040e091b 75
    0x1c21011030094003600e0440211200500451403040040001024248002c0c0e10404c0610041d4400c41d0001c6184200311095192060241e070070308081c50082e42c0f0030000480700414003412504020880b600d01d00b4a001484000b0a0a0070315080050a0740140340c0381c50b17400c2e081003100141e000c1c0400800c4c50141d81c94280540c461182e41081418401e5841c2d4221120554000368810300c0004501c64541000c1901c0400280700940c83c42c81e902c1e43e06025003800700751003c01c0c00c0079550110b03000c4c1c0f03a0f07000020100c0d50801c400c12694140100c92000321825500003130f5105950b843c00301e4200c6c800382a214162511842c2c0000003d503181e041d14800707030500c000040410040c2138800e03070314005801c10a1403147da6011500d00140e1652091044411552500c414840305800050040b03082c0c0800b0f441d00d40c10103003404200440d5088401003181c2542d80e5481340c40058903180044d000070104440a551500c1ca880303500c0c154031034024018103240e0042050b0503194089001c0c003401000c0d0544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 819495710 1250 819494460 819494479
    0x60a0f18060902070606060f03140106121d0c01120e0706080423150906040203060a1d0601090c0806031f05041a0411010311070308011502030708040611010b0603010b09 74
    0x124098001c111035001588590300000b164070038822142c000d081107076182d40c0d41ea824904071030303021011601c070304645207003005d00c0c02d0041000c0c5200300b00041591107040720000d50001c000d02240c04117816641c4880031741d0081030b035003007030b941e0440080ca0840740b44090504c4100b09501409488015a0040c0030520020078042400d02c819144005403207030380b045410600310141c4000a94542c03820b80100d540b044030000040d0403001c0400c14a00480c2e0143c0140000c0d1602e01c086400b402040f42240720400d0b08038000c801e2032504100241c020104c4490001e94081d00780c2c001000041c00514035400390340921040c400e14180900c1c00b090818480900007541d03120341c50048000d090ba8503a100d003203d1508240301c1070101001c00050340c0603090300c0411203d948101b2a40c182c0c01140c00c050b01081ca41e82c010030100c03400070640c90342c100c03061040d03a14040c055900d200c2c040e0480c2d00034200050f51034803510045e450900c6a0368000504613403290840d0301d44815400b040c42810504c0303001e041c459 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 819496960 1250 819495710 819495749
    0x11150f1e010b0c030f0a080f010f0608060d2d05010c1403010b1602130b180105031905010e160e09210a0c020901141e060412080708030a02040e060a0f 66
    0x10300980e004602d203010201c6d940c04030004000e10081d0300b91003100300184c41600008041c88007400c0402180c01e162142ca1080e0b6407a010801c00c617410301c1d000e403102d107414002c403c0e0304172403c20520f5504031110101810100c6c6810240e00311403070700303000c003047c8005440c0c4540c0011440c2c4c1901e04681d0661100303075556550380107400b807000743e90100070340003041d0402c624211022030f04903131031443d400e448603031200e0203000880c540c089080c4202c54041e005050207504156481c038003484464026030000c1480a01c000519140000c82c0c0c03d10055012951030502103200718601a0703401a1054008081e21003200540c0440189443c45400e4500000110002d8803130203500381100c410f4004024600a41c0e642102203060f600072a207403489452081034110044018660250061401410b06410300c2c0c10102444c5840180100544580c0020b1000324000340c2e10b1401544100e20000000d038540d44ac04408044d803010180c02a0302c00c403629482440300c01d0074150b201d011a010b00d0704280214605 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 819498210 1250 819496960 819496963
    0x309010e01050f15030a0809040b0d050d0e0a06020615040915110a0324030b0c25020916120507050d0f0e0c09100302090711150f1e010b0c 61
    0x940d45400903650070502042400a21072015521552182100b21480c9041004050b1142d40d2280d0080c451a0140301100050901740c0c48140c0843c00a406000171a03540e0301c1d918504200c0084403000108558944403250415034140300050403640024000c13418442030008203d4401c4000500596882c1828010701c818010202c9445010745810841c924000701150303450f520000e149030100741031898281e05030004242c6001100d1700300c0601d920140c103540c0c0c0c640500c0030241501c10840c3c0144100640300d4000311414840c4001107a04620304441c030310500c13218030701c018802d81d6101420300360402d0003074001015510a2030403010008207951551070554040c0200c00745698641e01c1c2c29802c1c00810000d4ac0040c84010403801121302c01c034001002c00c602e1031000c84080381c03860700c1c421080006050a515040e00700c1160f0070019150011003844c5890182c0885c3d03400c2c040a80380301800901d40444841d01d03040340001444118a00c3c9900c20500c00610611401c440d01c0c00001e0280041c110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 819499460 1250 819498210 819498221
    0x10501030b0d02100c030f300608100509010b0103020304020f190b040603020c0f0105011508090a08030906071e02070e06030a02150c0f0d0906050d110d0c0e030604020d08030901 78
    0x34000c140e0300d948490136100400c08040030310220041441456920000c60050044141c0003407a0422aa420f0412148080da0b00158403c50350b16030b41c90f0316000c24205e400f0301005120745519580044c2d98686421940d0945651140c206e06162041081c040542c640010540308100300344c51410440703031560320406c1c00545075444031100d1100841c000c10295456001070140a00c070008856500950350121800c8070406c0c03040d00922526401c00504040c00f80003c0e590000d15a000d554003010341ea00d40f80242e034011201c6200700e410074400c001c0c240e50000e0f52074110074004100d0480e21140900060b60316005405010180200240000c109503003c00c030441c10994003a02c407641c1e25100d40d02c3c504840e0881c4000704001d0291004200300c105001030303000c8060344980d41e403811013032500405980d5a4040c1941d00c02c03042d105c20489802001000050040c092384940c006603400541800622940c180760903548660030020a000160360795207480314603250003010b031320350300d45038801d04900400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 819500710 1250 819499460 819499463
    0x30c1b0d0c050705090c07021005120406020405041401060905060c0a051e0714060d020d0905011b030c050906040b03071106010e07112d0a0804260f06010501030b0d 72
    0x41a1081200e20540c030580d4071034110301c90000c03641120344600401030214011903002c00003040601911025250600a6150001407800c06d185070041e03900001000f07000860f0140c58207500003d0400c81810244910056190f003000741030015414881d00500504080c42011300c1102c0c0030075032100d400d0302800340c9064180d1013003c84003604201c0c09011204034a040103210b19000c0c11000103010707040c110200d090b000780180494503100c41b0b046010001d420070311b00301aa5a035100da8020000d0030034841c0c680806819841580a00030f04a801410b403549011410200603082c030102132281c0b208401d0310217890250060544a68966104558a440e0511034a030710344201e50000a0444c18800d103580125907650390b400c0400200081e249da545061744110070364030501100319960020140c5001444180b01040d02c018061540310441144c1054000c03407001021802c06184440295406458500340c680c040c0c0102510750b061030b600c5a02c1449494181900c500e010800b039503c41c82c0380c480a9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 819501960 1250 819500710 819500713
    0x60e04060b0d23090d0302070609020306070201060f0f0506070807050115030f021804031d0316030803090f0a05100f02070c150807030204080d0e030304090216050c0a050105030c1b 79
    0x102203100c0d100020781404004403400d452001c0150034100fa040030800c0c496030721030000348408203d20100b10300a6104040c10341c4e00e0766a400c482c0c0016903061042900941151307002041050800c01503402c0c020301d07031707202c4250301c04040010010780d1503030b5080d5415240c110441030786802141c14860b000d03104000e4103600000e904580031080080f21444403200d14003d54660848400c40003d130741203408140c401401084605002548548910070048568507004d4207903103050215842c1d5200d00e03481ca13002180d1407400881003210034802080b52105030901c90300145204915915056246c4c8a85000350003102c0c0c0318240340f2910109501100c0000e6849004501220780d210344d142c0d14140700700003c0e000a03050901050405109000780c0e01521a07a00140110300030320401950b80d21011002d040d014081032000240c0b5a80c07505c0600112001180900d60222152400c0c60030301200d0200503204070038100d8240205e9a008003529072040ea00000a03588031035085400408181e41c44094200d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 819503210 1250 819501960 819501967
    0x80c01051e0723060f010504020a030b060c100b09010312110102040317030601120e030316031d0a0506091609050606090a030302010b010e030f0d080c2101030b0c090109060e04060b 79
    0x2040701601c01901d4000742d25000220200f4820101516404251040c440c42d40c2c0410040c010751426034003e008251803400c0000361604400080360594200300044013403a008028040403c25840c041d900c1c030101c04071076100c0d166042d40e45040b88428120543c83c1000580740c40198908402d5040f100a960004905455262440e0180246a204862490000d20880c00c815010f4038035002c0c505142080310007941c250394550703281ca1000c1c0c03089106a010141c907103012441502401e07400c0070783c408030340d8043c2c00c580b0824204249170180103030126071203a200001e100c9007040c4c00440482518451700c0081525101c81d80003461038003450159030751104814200100305601503200c61003001e020f0721151030500031502007584a041a4034041c5064000740d1240300b03a10f00c91815643d001c10b01c0d81600d800c2110720b4102010b410711014030a8048070b4076800601c18441c0e10006e40d9440903543c0310701807401c04908002044426180708184c107000717020703130360a803103643d2508004043c0c801403400c181c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 819504460 1250 819503210 819503213
    0x5060a080f06160c150b06070f0b01090524090c0d0516110714100c050303010b09090a0b180a0e12070606080705091305010216050a030e0a080c01051e07 67
    0x868140c01d075004100941c5003c02c40046a00800d2403000d196088032900f0f0000c41c10744110790141c800010710540c491010004640041d030300c403541e00e12090013508030740c180c0c4d0b06001c100c0c400c503040a001c10920303034000b80200300b1b00182c011182090102c2500d507441d0070745808640c03204500030f81d071072a0b0f503542c107007401c10040c40c01c408500c1d90840c0040e600d60b50700780c2205403025103500d000c0c001c0000c100752a6160070200c1c00c08801414102c4084e190041b0420132503141c003030658200b81c0021002a0000410440b00d20b000e42c802071b00b05000f20030802c00c6007055400509241400d03d08119140c0c44100054451501c59000001c805480c1c01980c1c1e1420001c01c41e80c182d5840760600312000341c500140422001e20000e101425148003400910003602d0704020200c403000001d40803a41036400b044090a01d0322040c050281c0244160000c0160005924010301302e60340301c0da6154081e402000040016030f07400511a0180c0c3c0c003c1c02c103540d50f6100e0404294011110100c0fa00510800044000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 819505710 1250 819504460 819504463
    0xf0807060207030f0503160806120a03050a0e0a0e06040b0301090516050109242003040603060611210c0a1202030702011707090302280e01090c11030a0305060a080f 72
    0x80c1d071511076a03452a00c9002c181e0190307417500040e26070090b603240c11814410b8041c06840aa5046603000f4010b01d800925082400c0c0390800d8250114005800401c4580c441d542094080010b04000c5a0303604140341080c4c1c2c044152900180300f6485551581820041614294029811180c0040944498410b00600e8484e064003510800b8001142c0c0007001809003903511901c001d08040c40e2418010314003070f0500300c3d5505031500824001c0d640c0c1760045182008108010300090800351004610345244c51800341822101802925954210a03c0c42070410001208020044510640985c4a004500946103040029240148841000308441034013070340001c0170b0010113100366500e03070103080140541d003140d550664000c0045411a401400103180001d100c0703286103600c0550b80da8607841280f01210880e1681c1c040d0f18501d0b4540014403820758180039041c840c0c5814200070b081407002642e181e07904d108030040081019a510003048255451200140003026501c00701d40601c401e110465 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 819506960 1250 819505710 819505717
    0x31f080309120a1e0201090f030b15120a021c05030f120702031602130f0c090302011101021c050604020906030a020a021513030c0c0f030c0306360f08070602 69
    0x20b01c6950941c01d00c200e032640c000352082c0510352001c0d0f419840d01c1c86504552015004543c201d040c403203288808104030b007010720214000c43c001c10b0744501d103082c40841c1c6052a10018102030040b8004408241d005400160610040d60305888040001920007111005145640e0b001005c5010000d8a00551094070b40640340096030040a0102c94844040c00e070303501e2050308201d43d14680c01d492404058585981e82c00c0c4940781d00c28001c141d21140303040f4003003200e80d0704c1104c10128031071603000d10035940c0c015401d450f201c5401c4000c40c0b0f0041410854401e485031000400e8071107072564000341807034a82d82c0640f10700b4070014065640301c4c03c0c8040d15030060340210411a0051107203408821140680e0483d050142450000c5440c0b800348940302100d0340408101c042c1e0350f401035004000741040704d48003250021802801e8010507941146040d02c1a50200c00751101d01000c03080440030038011241c01e00039440005000391100300b560f890a00c03007500e0300c0d4601074902440403443c50181b0413290006c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 819508210 1250 819506960 819506977
    0x306020c0115030c0b030c13060f08011e18060302030d1d09100e0603070807080f070905010e0105013209090624070309120302070305070602031c02031f0803 69
    0xa01c0080c0548880719000d09041c40044c08034080b03254200044018400150b810020380044145440303c48540589009400e500a40004070a003a0030b0664a80c81400f440c003400e0700b070084006c110101410200480b41034004c0e50500310300009008110001d641c415001150b005e4251a6915803a04024000e021100c030407070007225a51016023a68070300728004c42d100e503c028100100090801c0000d85040000620b95074040c80750301c40108600504020070070080220070700038144000c1d0440058100101c9a0203105c0765802e00b0014041fa85c0341d81d9880e41924400e103400d40c0b81d00c40881400d203c01c42000310f0006041001201e906441100000500003071340d007078070b001d010b54844005105a02ca801b40d50490840744104441401c2c0b44d2041c0181507030340c002d05c1d004000c0381c0c1ba81d0041901c088204000c0713000da80b008104004008040c415140249203a0000e1030a140140000100084e405080004015400400a0014126400700c0d0313a030a0380d03200c00ea49859450380c3d4825640d500803141d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 819509460 1250 819508210 819508213
    0x705070303110f0f06010b03131a0a0c09030f0f030203040e01091b05030f1b0f041815030312020a111606090801090809060306060405121005070504031a0c130306020c 73
    0x40780800c20002c0c6130345400815400810f011381c83c01d48624031a07000a00302840e207045800b00070010503038019810101300452a1036900f18102643d461007101d119584803c240143c840c010008110a0b10036880039a80200302984111060302e4103c0c214466600101040c4490350300200e8941e0155010072030782c20300038205507020450081c06884500041310980c074004442c1c2c0008410100302590f16200b41010020f090800c80420b007118410341054001c001070103503030351030501c1c000c040b4010a41000c0341140070582c60340c20354900034240f05807948414110f81c0c000800001d501c0c070443da09035400f003210080e030700404500545402c00710720920411002902c000008a01c200043c86043c141e0341d40008403901c2c055207501030000c20b0308000c10b1540d00c1901403000003059201c0490f08032040140f28003400c05411030824181c210781d0042c05034404c00c0b00c107100520010310043c03160074100359424a120207955481d106140c0c58820a0350381404034a40710380001c10008150041d1800a05000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 819510710 1250 819509460 819509473
    0xa1509020904050d1407121805100c0b060a03170307051b0604231b27090f0307080d090f080c1011090a0512010f0203150f10081605070507030311 64
    0x5012005c0c138002c030040a000e00903644c2941e0718503801405142181c2c0002d0200c0035409540b040000d080c00c80c01c80904000ca241b440f50802040003096040754003002c101d960b08512401c5440740c1e2090041c15110741050f110000105140f04c0c095429108003003401402c0e03000740080103d03802c0e201c0e076040d9011241815419602d031845803020341c510300344802a0005040700c2460280c3d10342c81c4c13001e51030b40582100001c90040c56240c20ac03100120406030b001568241070074040441442d0030b05e50f604040040e0070500c2203400051490301203904140e0150400326105c04e6509100441e010090001401c11100080070b0140700c030301007051030890000c03000030002428202d601351700502c00c9078499988003084ca4014003541c54000542e02c4210061b2000003141c9040d140503004a9000703888081c28010041c40c00c240c240b8200c210010104403e036039140d0245254007000d4070850001e481004200301140e040b102e22403054003a00d01c503e4000046504482e5a824003401990005920744881d0140e00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 819511960 1250 819510710 819510737
    0x240e010c02070e1308121005240702131401080f0705030a02060d05040302031c0609060b090a0302060a23030109050708010806040b0703110c060f180a1509020904050d 73
    0x42415412901d500704001e0743c0c0e680c2e200000341001401e40044030f12420900c4030049404103402a54400c03070030381c46c85091035414442048160a0f03820030f0311902403908400d81c038010ba520300aa620b260740c10341e14150100054601c0c540500000c0d14501420134a1800000341d800b000104410039115000649550b1602c170001e05d511052603000194104400700140100c4800a50143e64818080d2051b44d05103440c0302813600c2e031f010742d4486004819803102c00611025800c1e01c14400181181203103545844080b001085404c1c03410721002c0e02c02e600200d0540039a6016103003498242004801d0761540040f18008541c0d03a8000380903030301c42e05251000003a08140100d0005043c1c5040e0b100900c900d90f41c4d85c0c3c036002103620003072100003003684422818540904410180070700f451400041c240c0c2f8500b83e041104c0c24540141940354420001c00d1809260380040349045203250481c0402e0b40440c5414001c1d40a07100706400250080080c4041000340480407502e40050b40d41e55445a100c1e50740c0c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 819513210 1250 819511960 819511963
    0x31106130312120b120a11041b0c0b0c0c06150105040b1204050c0307030201051602030705060301030602030717060d060b0d170703020f16170c12010b040e01090302030f07240e010c02 80
    0xc641c0a00c026808981b0040c085040c9207501c04510500602c0800d4070150a00c0d58401c04d000c0d9003000b000b060074010200200221100f10301e9210142d61f8000c1c0c100025550025036401c4003406081e50081303000210703945640f09400b01c40207019070644141da2032408040c01c0010110441d401d40341ca0140010145c40341c6004241c08080302d40503558681400300c00c0c0c0a41c40303050000c1c1c1d0204e82c07601c120f0a001419441e117a003d14001c5d03005d4040182c591a0400d0702419400401d48140074801070802000015500c0c40c04800c40700783c0098001800c4a03180004c220b800c0c041090203084000035501044141c0040c10003030810130b100350300307035504104045496070303403035007640000b4101c100d031007038180484910001807001c17140d0028100d507a06c00c040000b00755020740b07501520100da51584260f25803810b00d409581289a200002003010b0201c0c1c0e14002e407607020344022100f0220000921780b0600c45080117010001c81090300e071003840c002c403003a080c0c014110f00742030101c15401c002d08100031600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 819514460 1250 819513210 819513229
    0xc0605070c1514160f24110f0d06050405180706210903050d0f020901110c0a03080901020a0510090c0e040f320c0307050307031106130312120b 63
    0x140394a41c201101202c920842a82e00002e0b00b00400d2069000404d0110700040303051002d00d03018120740041c0700004a08200404401c0d00050f680f58181001070302c4540300d56049030381c0004401106501c840c2050306080180216910860b80242082d0610001d4040c00b940c04111084003c11110b803555102402c0d07400009217003032220b0b024502070750001a41181d4000e04003161080c60083d1a203032a507410b40041340e2501200020b180c0c3c0c045020006540c001e5440b030400000c00e0020041030800c00c000034220242400001c100403008207003525164002c02003120196406000d0f030b519025101410030050480d0030080d22801c0e0414000502d40d010442c80d103025070b8000d1003e00382c2500f1925140070403150421981d188030002c0812102d10141d0f0b000c8120787d402018080c0020351150b801b05403800b1b00c25041070b4840e0b04100010400a0401c0d5603e0310960010303a40941c0320700810458849403041a0701c081c040c0c0c0210000130901c0e0341c1c0500e2420311040c01c42010082c40d6021000c0c0f210040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 819515710 1250 819514460 819514499
    0x30c061008070927060e0c030a020915031c020312072d091d0103020306071b06050603030909150306071d060f0f0708120703150b030402030a0c0605070c 67
    0xc020b2001446541e0950704983c00c2e078445254900d1a5011091120002d4406075105603800303655055050b01120f02402a030009074000c03001040d080e9101d0b00060105c040180215014041089148900d84c4091100e90100b540c0c644501e00420341404000c0c0d100d0b407150b059241303800807110000f0300b041d02400d00101072083e0801c45914a200c0c800c07845a00d483c3c44881c1c802444a46600010310108200dc0958001040d0100c03013429451407040c180f8010001e440001442003510714a00c0503038100c0540d50480d90080790108140d103440d13010a041d403240d01d51154105082e002000580b136802c5500450b01d9100b601254050ba84014080b605000c840c4041c1e042d012003a403480c0d01c00d1a20102400801120400031071a109072904004115401f441d0100d80c4408003061080700421580e10a0341c0c00340240c20b090180c1980075030003458580640c0100000801c0c0800850b081d918204a00321013030354801071291100d5107452010344140c11104c02250314a400640100d10b618038005041d07580b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 819516960 1250 819515710 819515713
    0x507061404080d050403140a11070506030106081611151602060601120b011202180a0f0b1b01020c0f070f32130f020319140106120e0708030c061008 65
    0x94440d440c00f201410024100707078104000940c00030500c010080061070121103680307410401c0100c8101e0541001d103107500c900d118650501c01040180d41106030344c1d40c41030b608140790800290982007940e001c040d51211248074070681146210300250810514081c9449118590f51050350420499407410120350060010b54429900f480c1002c243d080094140414141000720041c401c040e00704a80041a1100c864a14611a41c1d01424030f98010400760888910302e0444506100c2c80302d20500c10b60214140042203a005c10b01c5545082d81613403e80d12032041a03604141d4160707029992484540602c0908041e05c04c000600000b0180c0304c82401104040b44091103046038028081d0740108181c45c5401c2210712501c246d1040182c0310340c000c1103035803950060301d0742480e10328400030104600f446000c4a2900341c0070740c461044000282c1c1140c0070b900e001004c1c80c42c0c000554014000c0901c0c1806d4912131500d01043c94a40030005e8258516540216040f0781d5410b00d64911968151190000342d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 819518210 1250 819516960 819516967
    0x821120a0b13052e03080d02031512120a0516050705011409010827160602060a0209030c1003020c010e0a0b0a14041704031a07090806061318080307050706140408 71
    0x2000c440354110490184c01401042c02c96a4a44440c043c680c00040f80c12046680002004654512400e642c8400c1406a8103034100e9420104019524081542298103855020440c3c80d074440c0300380700300d40c0200240d160208006607203180c840d9840c09603005450116038810074841c60407205906681960300141d6130680c0580703485101e10451004440900d11110032618842080c140c200a5240c66200e4000c2c00f042c0546401002070501c0702c06000305241034010070081e60703d07907000220094a19412554101070740d0036003006400a10980160440550810801030b0b4080703004203001e000540110740705460b607076070362900304d0032240c40a0140215000e01004100400d0844c1084ca0050310050300706403410340c0701c0e01d8070b00800c07902100a407441e842000400585660290901000b0300d028130007001030b030810b8400a071206000e10b011040e910f81d00c2c00040d160505144001a10a80103001141d590514400c001d040d03078400e40099507928104000303d0040030103610103920444e00b11581302d00b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 819519460 1250 819518210 819518251
    0x60e03160204270b100e0118020a20010209091003120c06090209010e010512070305100e1207080901090f0305030909042f03010f060821120a0b1305 65
    0x2010085280c0350010f410510844600044480440d525401210508a140b41080542d0045541a042a0301c0142c250004201d078101030240c520380707a05048009611031110300411502040c0300d030040340a03a500c40d403161450600660041495007415102015181e9998050300700032549884000d105148407045a105580301300e05d021a160311694002c620043c181d0001842040d080e0040d101031000e16004101c20328200b5654080b4140c0d00001e8941140385803611a107170b2036a0101242041e17241c94944122180a000e941a40c41c5800c14050312405242400c8586801c80701e02e9074042080703220b000c0760943c1c52281d0041203030b40c01401180740c4000e43c820700003500c2015004403000e07481d111815a6103c900c020318a5841720344c003403130900c5000060405096545083d15074180070f150080c2489009804100b402c4aa03a0345108107280383c50600303602205106840d8186408017080060102000f002c1d00610140d00701254020a041510300d44070342120802c0d01c000d6460b503e40c252005c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 819520710 1250 819519460 819519469
    0xe1203010b090103110d0906020a09061b0201080c0403061a0301061d0c070215180f0402121f030b07031e0c230903010c020a0c0f05010807110102090a060c060e031602 73
    0x1441c42c107401541500301411845154281c7e001c03d9811100d894022942d0b42100d41d00c0b01d01840107040b1b900d00200000828200344540070440c460184c10000b08072b000500c0f0440c014219002141c0c4000108200b19045001c0e030110742080c0f402c0e61081d4200000040c058003601a42d9244505020744020192940c5c5e103141c0c066031014000700e800141d1204100c06046d01031002e0310038001d01405808407403c0d4802004010704001d14640d105510600a090280826008440e031000407013800742141781042d903003910b5440c910b500040c900c200e00c03010403070360b20b44c1600300b0302506016458640d45421140c402d10203403841a100d0a0000305440c04902c90420041c194600e6040ea00305500e1a04280c000801d00b96911080c03400c015a10004440c000c0001c144450303402170030245480400f030341c10074000034a140c40203442c030400c101c41000313015008a420760484000d040002c150300406956030320080c00002c031100040d00c103145400c56856001d07001101b202e03c09440526841728405680d400c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 819521960 1250 819520710 819520721
    0x5041d060f0a0801020d0c050c070e090c030a03021c050a12020307030e01050c090f120303011707090c1215150f0201110409050f0c07050604060c1107090e1203010b090103 75
    0x89a0254241141c54640e031a407110000261000400269460b0b032568594410745600b41c0031034040000401080000c48004201e81c1c003900e00446154480d42c40782d041440c9040311b181080c941c10300480c440081056000525085000b0900c0e40c8000403c0c1b4a44090301c00d030041d4159100422415003030314805051543c01180c2c03242e030509000038120350b1307000380c5400c440c81140c1010700c000c000600f04403c2d141c242a028401d0308200c603c0c4000d050b07007215203902d900040c0f04030000a0198400c400c800c0c502071154170060041d1403002c01803010701070402080804c948840f030003441d20f4440031290b101d1000d00700c0810756658170809010400030200461703090301e0610300d82c01103560340e40c06100681d10040c000e000500c0b110f0342c0403510b410440c070b990f50300080113030038403400f03c000308110f07000588041106a80035800180014600b50146c2c010f0710005c11152401c0d00c076002e00907001c5180c5a055004805003541d42e01182d9907a0f581444c0078040d07100a008400411005022621980d8401c2d00034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 819523210 1250 819521960 819521971
    0x90604030f08070221120f09101104030f2a1d04030806090907030c17010c0906020c0f061c1a01030b060d110c0d09050306100e04150e0f03041505041d 66
    0x2221b02c2c03d0010880c0c4443d0400603101189000c140380e06000382400d0420501213810380060f410041060030200789082403140d440700a2981d00c18140c1c9405120340c0c2c98158040c11a4218806070041000140140b500c409000300c068400050307202c007a143d00480c070380c070344210f41c50384410507991100f0701008241180108240480d20800780c1c0400081c8408a540300145401030ba0821041080d012842c00e40d1182a142c9003000503000c000c100c00e650000300c82038401400ea80c0305600201510101d40c940c402c989030010a9008130361041280e258070381c0407080e6030b000c0e8200c0980c002105001103042c0c540d5248815480344050010f0103904019034001d210074100002c0c0300d0315000034401001c1c1400c1c000d07554580481c1040c00204424201031041a610000c0c1007104854203051100e2815507074400740000e01059041c2d059012154000d6106451181c030b41e03011120310890400c0750079580c0e8000d010b9001d00a15003984903440b07900623070a40d4181c1300c01185218112181d0103000c80943c200611 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 819524460 1250 819523210 819523273
    0x20c061302061b01060312050703020304090c030609110702040f06050a0506090a08060903070b0708010506040603380f0907050901081b04030c060e0306090705121203090604030f080702 81
    0x1000003043c6100f00494240480d040020070118510305101070040f00d0300d200e01d005e010080100f9030009602100703c409a07000c44000080000200e1801c400070403090b049001d00520701707000d60140707810319005232918a208490901101d1680c211100c01d50b00944aa0354001e041381406100304c1ca0034001038000400064a040c030041d42ea055420700c0e2590664045c40541c00c0010200c00b801000c0e204140c3c0000581020001940b4080c0403c402e807049128080070507607113147c021300d001201080d1142511866541c1059440400d1190a44d803c5070390503203115243d124075141260a014142520603a9030703850f0b250030400e2907030066a0b0007000420001d00c492000f900700c280006110040d1014500490801c4281c500b0080d018002c0c08481001c180b29030b02c06400c00c03013600070000e02402920310640c0d2940100001f00011850000d5440303065420800100030000a4000004d203144618003035030300c103880071000c0742e01a214000e0a4a0320310040e080566041c0c48214804007290f100d8041c0b04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 819525710 1250 819524460 819524467
    0x6050a060f12090c1d040b01121a09030307120504050a1b030f030807030608160302040c030e03041707050105041805100801020720061611040636020c06130206 70
    0x64038000c4400d40081104c00f60181d1344103009551258140c101d5850881407144810f040c40e46400003c01014420300d0481d8050120000c20810f60302500d0346c4c0075001d00046c803030354140080465100c0e0411504c00c00019010b1400c4d0002040b907010f4140500c3d003210160590599603100c01110fa444005a1502642084000400110325000c920f013414040d56542ca85410b00044c01000d807601079004211a0344140c12031551026000182000c0360342c1110f00151002c2845001d9015100c001e0250519000105001554503070400507855001d40d11001e4400704d07915040152014000c41c010200c071100c559001d55134504081e4446c1d5001044036020721304003550b5164060a990007000226801c8005203c2c0346410011032200005600c001c42e4580d003003141c00ca22190403840c00300d801401075030040300b004e10541c80d241d0060001d0f15040003000000c0080f6402d090804e4800c0d045030200c49688030542c3c92054040c0300f9250740c1c02c02d10300a4101030725074038803080090075040d00c140e90111040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 819526960 1250 819525710 819525737
    0x40f0e0406020f030c090a0e01030201020613020f041d1002120c160c1409091908031f170c01030204060f05090f120703050717062a03040c080f0106050a060f 69
    0x30000d90310403800100006d68801d040c20a00c5a000c4883d400054044e1010005100507030300850125400030094003c10307125019030000903c444000d2a0054120345480d182200c3c0711408250594800e0483c000c407030b02060100c004104034810204001402560034002c01c0445130701c40300424943d4801c108068a04440d07403a580c01d848407540c07000c1801e0000c02c1882046003000c4c42525031043d60318020b040701102d02c20644907804c00038040144510000400100c03a002c0346011200203183d01ca07102c803041501da1051030940380001c40b260010344203e103000b4440b503200e4000c0781d05481c030303c3e82da80305007105d081c0341941c080e0048030700554450280c40c019806601c805048a0203507030341000420600d4554104642080e005801a009207900d0004c1c0400325040000e01c107800074110b0381d1850b5080340da071001514208540000f0417203080300105200c14072003c1800501a20100c0c2c0541d0f5040d080c0001b510b08940143c810740740c000d00c032207030100507a40c01a0f508800095490500d0b04040781c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 819528210 1250 819526960 819526987
    0x6070503040803040905040201271205010f051303020709090c051318051c05030c03040f020315040c0302090106110d110c030a0c0920040312051c0c110102040f0e040602 74
    0x10f90001c102c170b582c1e910200025980c0c088400602d03182042c045440f038440400101da2519900d008043c8104500c16154041010035804031800304541081041107003010f0301031150320f420032101540140b046030000701c0c1c0030700c0b0344c450310109a40c005400d413003207071428080c00950040d805410180561303408a021b980ca2200b0880720403148114003600b08460440c55012a40e942070850b001000014810000f500405108aa070000d410044480108000d440000c1c90400001209c07000d145010007031000300002c03101c094064174800c840071841c503a00d40741c2c116442030400d201050180d00998252468034011070b015002e68503070b481a00e070700910b02c2000c24500800268111344103d46000100440c0416102c1c0400518a48241010414101c0e21b42411400303140000340100029400c20705410380642d08a88100301c044900344059910114035030f0080c00c0b032100440c00710f541d44d001d82603078400c10320864007603890100c00400500d041407040890a1002041155241d90801c200043d4480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 819529460 1250 819528210 819528217
    0x603061b09090f02071208180705031b060408150a0c0e1309020325090e0c060406050a0c020d1a010503010b01052205150c07060201020f03010509100b03010605221406070503040803 79
    0x2558458110a04281e01001906141072000b07401d1070308a40700600c2b0942d0302090081414100e0a00d2503d42940c4500191044c800c0d9840385000f840386034000031484150440e120f201c2c03154031504200700070800c001540e204292034030301f0354840c84aa103104440702031940503440b481d001800315a1141c1e21241708121030300b00b2450a81d80f80082075400c00a40c11035020700504404964064180f600c00b4002262541c01a03026000503c0008510075103414440c3c0c440035002d5400614103200030040381070229160004a18402c0b0a40340d5100102c2c80d8101405900781c00c010682d0f03070618010505901000030b031342c5506400d03a0124a4074000420b40e035140d0710310341075000d20005250380b00d42d001080c6281c6840366015500b5a40148014240003452000781c0e411200e0aa45d90003035a03030761002c1800190382c2500700c110516008030012070100e60042c040d06030300c25600b0721291094684a04101c1c0a2243d21545210810950144d801d074181a0003804142e441002101c0c1429105c200b01c50847c2c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 819530710 1250 819529460 819529493
    0x16090914190618020714010606050a0807021002040b04030b060109050f15090301020c0606010810030b0103030f030e0a0312060f081209060712030b01120c3509010603061b09090f0207 80
    0x5030042106000d0001c410034106e1070081450003040a03030300e042c00142a078026200c0010500c1000700010310500c0c024032030303c00b11000155046641c0c0d61603c14456070340e04180010768044880303000107811035024031141006d40b040200645140b0b183c1c1400c024a20511031049901c159003482102029242400541711a041d44800b0f000a854000001842e00200400b0f00c3d9000d6400c4504102207452004400d041d00e80610340400102d030950800d40182c100309000d00d8030b9200f400c4240050680c032002207118541440e00603c5080d903a1107466188004601400c071060300703d401c003141c105548070010546040003070285400c200041d102c618074288013003c08070101303444501e40d452541e4000900f88e0310b80c1c1c800b201040401d103e01b1000b000041501075420501c0c0d07540c041070f0007110700c505441d4507802180d403941c03d003403405804031400707003000c1d00c42160454102aa00700d01d40c103180c1315840c8502c046a84000000d40fa000301e070800b410205003034007401507003004001e010961031b541c1c0c4102035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 819531960 1250 819530710 819530759
    0x2030a14010c0c0b070e21060f0702030f09060c0c09011e06080c07060e0f0a0614150d0803070302070f060c0e0a0503120705030f03160909141906 64
    0x5000a200d81425503400c1e01800080100310103807600082c502600d9aa0862100d2410151910090000c1410050b0068115040c5100020b81e01e580420000c0c0d150700c28001481402c1441e00e81800a0343d4901950305408800342c0e080c041c424050a21002030040d2246140454203040e24810100d403200c80b003070304150500581c200708440001c80c9146076100074055468480014a40692004494090444000d0409490b01d0300031a919600304850705982c12502d00307844054030b980c50004008e020b80200c5562204450300007400e00c00544c414076002c2580540a441a40e60607500e8039038a500003084641410f03400c1c0103000225903050580556944103102c005078030381c0c2d80c020140468911241c80c07071003290600800e1080d81c030007060418805040301c0701c0323940340e002c0313441c0440c00d40c01200c0118860460200c1040314410f24800304902200300c075218282920740f42d8500d04150b5481d00b405002082d60300c0c0100e45032100200c2c410318611280c0c5800260b03203481e580004140414031201d600c0c0b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 819533210 1250 819531960 819531983
    0x9170c10020f01060506070309090e120a1710081c1b0f05010f09020f040c031b080601140a050a1b02042409020c0604060207020d060905030310060e010806040c0c02030a 74
    0x11008244130313070310252101b2607005040a8043e0340040405059000c0c2d1000c00d80c440400700115032b820000280f1841500d00303850745039404038074001d00400c02e440f020f1095882c060045000e0211002d08a0301791800500a015034020407990910716118081120003006030f408a12080070551517481311030b480c428807140c8001041070070001d0944034000c40440c00c0900d02100000180d4410144042555094501040e50010990160014028140441c00c5003013403c41c40305800d80d0004101d4070030704d02600d80c200004102e101c03292003400f41d0314241020480c04c02c4a014054011005840072141110095405c00c0c469400300d01540c4510401e6220300e508d402801d101b2000030380c98040540004142182070200e00144c041d6104c0014001070030113980054140150344643e00031031105900100c1c04c0c400c0f11107500d000c1d607495100325645024202d0000300810b00f80d01c210031880a5400c145d40d900900d85a250401000f0419030510a0511100710100340040e00c003401038171b0305c6900900c2207503038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 819534460 1250 819533210 819533233
    0x801050114032e0b0402040f03030f021b01360603062309040f0c0b030627190621051c050a0507020d240e0105010609170c1002 56
    0x800c8441d091003684030360806050b541e440d8000000304105202600c00d9a1400315203000c0c0d00380181900e090541e0000d000040105030f00b9000d82d200c07400c4a10030741da408c0030200704140480e2681c1c2114604108001507905050b459841501c4c06281d5401045941142c00c0caa102c041c150446858110811010003c0341040225010711501c0000d041501c0000c0022400516008450340380741a010301c5140003501040a12100120301103056900c0300349280c81c1a10b4801c001a0354000700e64103486810052008001403d0140e140003540640c1d40c02c1c02c07042c2c0c5961045880400842c40e1688103140d54640c002038030101c0d0260007550b0765001080d145032104600b045420304030f42e030643c030314030151498103031030010f80c42030481d5881c10152404a0702c50041c2c0c400180b054170201006403030b02881e183c4045c503a20005640e005500c0956004201120f20158513900b03880c024420342c00411400f81041084242e49481c44807200d20709801d0b600d5030018000001e2809403805000401680407895001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 819535710 1250 819534460 819534479
    0xa0c020706211e0204030503040311010512040609020102010b04060f050901050402030412050d140a2702030c130b09100602060f0f06010509060702040f59060108010501 74
    0x406070030146042d00c003107802c4400820600b881d030400c04003000d5850403c0720f64002c0c0000c10b4071a103582d02c1c80540d80c0d40d65034148550b407500a40002d4031428040104000658014022181e000c00c0a5480842d1a59aa16110002c040464040c0d043d03540741c0d07420103400da07210f1080c0f1000c0d003414941c0c06a100e082c1000e10501000503000240554410824440450380f101d84200c0d00c4a0a89000e968030040384869801401401441e804c00781c4010090260034030003604503440c100d41c40c031a5108000ba2029101402036814000a90107030400c01c49a0014100070032071242d410010000450720f0031030030020403e036903411200b16503c0c03c807400b0180072065042c400260000d1304100e5038071aa0034082e04c0c0ca203000602612040c140080001d240a42e80c4440302a40c00c02030700103100300701d0300c03200303034000b9002d8080e070320742800041c10074929000042441e220340039654005846412980c070400d0003903d0b80d804400c000c552a1240d519080d03022000410245019141703140021070903515019018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 819536960 1250 819535710 819535723
    0x603081c0b0d1106070b040c1a1612090e09060103140f0721060509010504020a0f030804090e0a051b010f0906081f09091b060c02060d0b010e090a0c02 66
    0x112080c2401c5414a0a40d103880030b080704240c01072040b002c00d6003403900092251007211002040c210f50301c42080180440c000b8800d0440d01203080358081420903046156076803048507075000c50b00d0411400780c07010408402030f900ca16800c034101100096113414055100303100032151140d003a03000b840107108000e8840d21040d144002c0070014040a08503482c8070b07444104074001c080c982540350050001d0641c05060050015402c120108564104050301d00e010b40300841307043c3c0c01031040718000141814821205400c503030b0041002410203080100c403c0181c03482001100e000c0c429640020041401403081c0300500101c50085003100102d203001424004800c0d41c4c030b40900203900400c001e0b079078008400740c0d4400c003100c0401c4071036805184408030083d200d80004800d80c0c50102c0c03600c00c004102031069140c425900081c48143c0d40e81c0d000319010700000a0082d080a410b000d0307541501001d4000701d400c0711050624144140803003000c01c031040700071600010318a45802903851040d4050003403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 819538210 1250 819536960 819537007
    0x70f060f060503070306050402061201121103060c0a50040f0501050a110d11070e070e01320702040e01090215220605040e090706090b0a12060308 64
    0x14001c861a100000f40c41c0c000d20b1001401c0b0949a00004045548050840e0070382ca10741d000c4100196100c01d15903502a080090850308030240308616145441c0004100707124607809800a841c25034504411504900000c00d94000c0040514250746509000300d80000e042c0285004c4200102d003d900c80040310b11030000d0f9a001d1081008140150703011b00d10f0761015141e081c2050799540d031001d075007118050400c80e8601058020440c0b000302040e84503c8441600d407080c0c08231481542c07281ca040d0400c1300700745c03101da01080a03814801f010f5401180511840030551002041c842e6030b4002d00010900c008103408029030700000c1650452825101c0c6045410800008018083c41030340480c45031318414040801c2c0071004940c5d030403040d4406101d103a1100145107403c030202d6a9850280030f580003401151101000480094a466400500e610841d00d06540c0c0541803850300d00d030700c0890b511001d0104100034140f420040300018a004103401548222022560b90a50052038051440100b06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 819539460 1250 819538210 819538241
    0x1e2d03060a141b1218060705030109110306181e1302210c01030e01060503070e04021807020a29090703050609010612110a0e07030605040c110a110a0506070f06 70
    0x10f41a601c80381d02410360b00440c00518080e0003a440f100403401c00701241d0140c5200c18070500701004441036010000c0d40c1210118a81800b0003045000b42c02018001103a1a0b90088101d40c0c0c0f041146008071612a0068076803003109542c40400b488071060201c04440103021480c20b400460b08509007080c0c14079484a2540f0b9004d400010180c51640b1030070b0003410a810580c5441803200312540a520400007000000c007100d88056552590302001c01c0215002d034400d00380e45c4911562801c1910a00d80b254180c0d501030a1044040c0da550240340107800060550501c1c190b2000ea43c0c101050f0206004603100c1009150032880e5107441803914000400300500d6905007030341004070791000d001802002d0b9001004084c0580c50202148140b07581d9880100768508020900c0546038041d070244068820940d020301000c44c40003010b44030a00c40d460041c001d940b1504182c0085600000502100c2a009010b0282282d8540005a42e0781007004191042c0901c820b10004111342441401030a00302003d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 819540710 1250 819539460 819539491
    0x307080604151a040b010908070303170606120103351b0c01020307060b040f09140c0d08090409050705150c06340212070b061e2d03060a14 61
    0x1100f502e804082210340343c040c584444c65011103030302072040e107006802c3c080e0803198a50b0f40c90030000c00e02c5035290f40c5004200644400b042d074a003010411200700742c240805074512a40380daa06d110625000d464440541d1280001079010203200e1a1115030402a50403d41d0b2185080c00380c500500c1d001c10b01c203d480340e03c6130300303501d440c1e0360040141c07080c0c141c21010005241c0107000100d00a46140500390080e81e140c02d5180c402c1100800c0d8100100c0c05c007004440c040003104043c418002d805c00f0001d031214005208a2030a854680c010003410b9101c2c03029070341c1982da20310201c0e10015600d403180048483c04615885010b0f410018154840001c1116011380308045020141042d42500d1604c6202c94040d03c4025003402001400403511040c0e0901d5a10600c505001880c0041942d1b118460308101801e02201460000641610203000700b04448100308480c911449420340c1c0c08000c0c030300740b21980c0f0311b18940d81401501d106540321400810031110050201e050408001c00385180f40ca110b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 819541960 1250 819540710 819540731
    0xf0c110d06020a1716121407051903020a02060408250b220209060d030207120809130c09090f0b0d0804170f0d1b120c05010b180c030411030708060415 66
    0x170201c050a410141c1400b04c090143c041c400f002405010b036000021041c884203111010790f2000c0101002c400740e420402a005801d94214240c0c401c80d090000140d2103030001c203011880e105c0042c86051000c010344408180644005008054000c006484906000041080181d56074034a804001d2640c041c44e100b80e8810780c00100200c1010b010329001d003443e100040f08040c000c10451001d800c04140d1502c00301001c2c6481e4007241e0000c0fa02c103001d04c20100b0f6030541c0e20001d004504007030146496440c2c42508002d840801007944111911400c0d0b00c0340300c900c03c15110490690400d901801900784c0d40c80c1400c808105800c01380760a03030364650180d04ca41d5444400070801e41950005490041000c1100c01184199561408009800c454038550b4003001d65400c50701844030300f84150000e000100c607200800003841c0e54007403141c4641e810070f00000c1446000e040190790280c4640c040b01e10101019012a241c00001e4100301c1d059800b841c240701c10310403040300c04159101240004d115480c0d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 819543210 1250 819541960 819541981
    0xa02070c0e090a0507120614011211040f020f130608011511150106050c0105220f020301060306020304080d1b050403060b0a050916120207030f0c110d06020a17 70
    0x1d128190001a160000c55a1058140312801c0907640090031500a07945640f980b00c038800c4064021a0748500c0c2c040e44a4016000d681498100d03198620501228142600c1c0d0640c0c094201a0a43d800f0390f841242c1503400086102501c1b180101380c843c50b869040440e98404040324980011092001400040001d200307101c0605078101c4040c81c1c1003186c03901c5542c0c4a80f4010000f800a000142c0703c1c0001325aa99002010303011800380c490003800f003074880303100075000c00383c4081d1380b20304c400003817806100030420001e00d201017030348050000202c10b0790300d46501040360020340d4201c54481c400110040507000600600d000d02605040440e4050902040500140309600c00245401d450f0100100c055a41004d864001c0c2000f5000e00c880e40f4049000e460861104128800850460b03801c54011181500c06e446440e5410748600082e840204010303580d4a101c120308541810040c110013003103880e04c15010aa0610030380015888400001c409030102042c820905a02d409074000c01aa0455 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 819544460 1250 819543210 819543233
    0x30f3608030c0711030a0807031b05070528081e0c06032d04030e121207081c020c060403080703050906060112151d1e0a2c0d080a0207 59
    0x21003862540d80f01c1c54600320304105540707404d082e8507000d0304411206112140c0010090244255103444403a1746652190f0328010b00794602a00550040c00140228103100c0321004841c0c854030411450b420801070034100040c05c54003d40d20b41d4000c0c8248440707481002608140304c0f10b001015010069071000481c0c01e0303000007040c0386400c080c180301c034070390304e80b000115204041d85900310000c10340340034280502010071480896005103076102110780c9e010b0011803824070415044150383c1c81d0154984030000380745c00045000c459640421a04641030a00d0300c018150060040013030140c520709802c01a00010780100365400341030401040200c4501d0100d241c60384103200b404e20f1107148551659400080c1054104039201c00101440440c0142001d04007060a221440b41c82819603a50b01d1a0300103000c00707219090445004001103400030031a60081c41030700b29240440d1074891108184040d05114070700e01c11505e80c119162074802d040d0300c480685ea01903030744501540360050035507443c480c81c1c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 819545710 1250 819544460 819544471
    0x5182802010c02042913060b03040803090f0d0f030b0a06120c020c190e0105100c030f020a0b0103030809010509030a02032d0a080f0f0f1303030f360803 67
    0x96841e00d240d00315951580b12007000c5c50084032892070801c5480d0403201180382c2d0415a403164100c0010450a01c0407801260152080c07407010505680707440d69100d2064101800c1108a07028240d820303440f000040041804160880e0f4034485519030080c0040d08031040041c18034051242c00800b400400d0308404490950f64a850b40000c41c6119520101d04150010820365030110600c1c9407842030204211105040c0c80b5094004015640d0f80c804208403144d9440040c00452400030480c40440c1c02005030300c1801042d801602c01800c2183c0d41c4400c0d07410700340c00c01c80208080809104404a09200d615072040906009500d842c0400502170750f0380c06440c2c0500c5100b42c0710303003d56019044100100d00004170002e86142ca8041c500030180c09200210350b920038040c02c0000181610043c43e5182b030180e06075543c0140140c03240c0b238040c0615007800c1d80603000c2c035403164000c54408c1e10741d2254881404010101800d54503030807111030764001480c080e000342510b250b2004808100200d08807500305 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 819546960 1250 819545710 819545717
    0xa0501140f132a08010f210c05040c0f020d08101505271915030c0e03061602160b0a030203090a0f0b01210506040201050a11010518280201 61
    0x49944a038068058000e0a051030a1a009142d5110f8080302c0d03107501800050440c1c5414055a0701c80d200032803816114403621854480c808611854a41c00901001030640150301c0103161a448070301140a0300c520041c134200013809a404480354035414442007070b108105103850450780c1480000300030090f600d4010748032840040000b0f4400f490042089981e1001030703d040e0702418811400d814400515541e1081c0a04060f0303010b05524088000c6810a80345162000d407401c1c10f00f00800ca0003403880400c00070600c000551407121940e0308100d41c80c401c01684e06400d10380c1d42c031200e00a0404004070380c101d007420003442c3e003804519149001e0343c040140c149030050700c1c0c3d502c00380130503e00010480060600e031502e42200d814000b11020040c1a40c0c2c2c3c0e01015040e10380044c141d45081054544007816903000000810010f40c8948000c1c0040c182d14540b07100404000918642160740030343d0703854000031007901c03140c9188500744140f5420b4500c002a4407145402500280030a451211009042 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 819548210 1250 819546960 819546979
    0x40303080f09030306031f150e041103070b191b050a0c080a0f120c020a0f05100c202107090f0603051c050d0c0302031806090c040509030c150a0501140f 67
    0x304030154080e0300c030300c00070045032824156200e9580400e25418ac40c1514442802c22400354103003400200d00c02101e040d0b00d1034515001300c101c8440400c94104080c402042a01d6088480c1006081000c090040c003a001529500c0d155192100e030031119503018660300d800480da1280844c4e04913401d8640d558020f10004a40f0003120400c440c2d200130344030700039408880000013061203200119140280d400c19903140816594441c0c0948514182c0c1c50300510810300560611205000c0c0141c050034074001a2100030400d014070000300d20481071102d0010541d01c9560100683d00003030203003900c20303031403103108004060a60325095103c0017001d1820004800d0b591103190b40501c0343d800c0b103401e2050354600300910152004010007941c0103072800c6c0300b0300800030511072900202140b52400388401038010816107a02c9014880944030041000030076000522481c90500ca0030b109041e00c0c1d0340e481d9024420791400340d10440840b09c1c10f0304442010031100b105c95000d500c40c05d8540c0c0384084211a01c450303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 819549460 1250 819548210 819548263
    0x150501051905211501030c050306040b012112051c150b07080c030a030c18060519050405060307020106030b0a0902030d050d020904091202010f150326040303080f0903030603 76
    0x503480340558140034911900c40501c8100784d084040b20f050324404c407080210360360b55101300350f0b494009175030250490480d01c004000396100e2080b45071035044a004003a4501c0180e440b484255410b0009000100302c00007542c8001012840001510502c40340080140e503048041400d00c0b28001c6c01408040c00300083c40d41c0602143c3d00a072020408400c040341d81c0d83c00550002809013043d00076002c0031500c1001660310f00302c1070301c640300156001383e582c41c1d0626018000940030740141c280f06405100c4200070100c0caa03100c06000718420345040c0c0020440d80d19610385441080801401e454031540342901c0200180d4000c5069030140d000b619110384c48030080c10b0284002d00c146807119502c1071410b1000c1d801c022561507a0001864a40c008202170181c410440d0f091301ca420080b01c85e286241c1100b8030000b542e440051410116503030282c01568440f92141181e50300580064010404a2040201241d040c1c00b440c0e91101004001e141941000e2021959030010340321031400e000f900125121 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 819550710 1250 819549460 819549499
    0xe10020c071212080712090c0f120f20030307080c070602030c0304060e040e031c1802010c0f08040315050429070804080d06030b0405100506031504051207150501051905 74
    0x101c206c1100d050401c01d90400e407a225a501c0c40d0741c8180c5104c46a1220000f5038100401d8072900a80e400c50803115003180c032561045811120683d400a0141d40703941e24052545003080a020f81314401d481c0c8076590700b03420810603d0180350341d00c00710440d4020010510003103c08800d0300d00311180d60605840000044000601030035038410303a1481440049121094008820b40001490340e1000c001c01c101b81c0503000c01c510041500c41d0203404604401006130008240d0110144254004d5418074102602d940d110a81060003109000d15251590b06110600010400c02c46601042041000c01c0807500d05021100b500014083c4041c0101d12001605101d060f4085070010210a00200801512490b200108080964003030307549203d2120f80460250081c81103a014000080041c00c0112035022160100c8000900031102d601035101040340540843c00031700704d054412002a0782034100c103401101211030582c412803150030ba2544104c90b1041d00708012054400036108040f54803103044800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 819551960 1250 819550710 819550727
    0x114031f0b010e1c02092a0918100812040e060603150604080a1b0e1b071b03120e06160c0f090204050907030e03090105030a0e10020c0712120807 64
    0x65410070860280c01d070307028883c1c5002c500e40b584211000c00c0380e629005d01387c0c040c01341e80c00443c414110200c1034896420010f0405054031280c001c00c01d84141c0d0031010008007000d03003503e6640602c11a4541845030030000c0c8446101d00d280000428241880c02071000c041400c007401e03180c0150700010100d60041001c01c0c10180300100500724641ea41d69031400d4556490aa650981e88000d0030b00301802c01018045c21401211407a802c4040300380c858040c210428884480d26040031102000102e001941c3c0e611050040300c05030800c41d002a1031801c001d8420314016820008020400c104404a9a00e40c0b00303039003d998003100c460040004070324203020740c0c94041e000001660041440040d0000b00340c0c005000780c4505544070790b13154807041c50581c19a20420400022a0014000c00325103503c2040a1a44000c5041c40881d034030150752a80350a1942c031040d0000c001d13400158117a4041020000c22001384401d83c4100c142c1d00040e202c40c2480720b03210904000300640c4e5404a1081446038008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 819553210 1250 819551960 819551987
    0x9140f220611130b030601090602010b101404030b160806100206040b1008010f09030908070e04030c020a051e10020c010507170c030d060503101a0f270114031f0b01 72
    0x10301003003540780c503c040005e4104442443c002441c001d00400e915206001d2103a1040003e496100350345407042082c3c903c03209003c84001d00382018040000420b90703500c0150300411458815244c00509048010302c1001c008040302c0c0103a0044404015850380090b401e640103400981d80d0619440721120030040405550101529600340007415915210a50107004454403d84500c035180e82c0d90440581c85245500c20104540100b0000a000ca801131080344001c038030050040c1c40d10741c4c54200050403460100ca4012a2501c12a00c00d0914103100d00030b64680031541c0010407920140c080000e10911820b8001454045c50444c09060b140c10402030f5001c031000c410999494110508010300103050500c2401d10074800c25004a040e40c0451003000450442c2003078900c60b0002032428000c00c080c0c12035010344c000c0c0c0b0f001c032481c5228120766106594100440b46038011545451400c0c0150144694030601c03e400010010f5482d01d104d00c01a60716041740300380410488508401a102d00f007150b10f4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 819554460 1250 819553210 819553237
    0xd0e12030d0b090105040c170a150801051504060f050f0609030f061e070509060a1806051b03040837030c060c0809030d1509140f220611 60
    0x1610200a040d0b03030000c0807401000d440c8040180c0c0d0f92010041a40d81450040000c2840c4d540700018007005c0380e4440e035001802c1c490202d200d05ca01c20002d80c1c202d00340d5000b200385075174540078400c1c10a11400e07a25600e2800f150700b1b00425081c61358100360441c075445400d2040418070101101c5803034400c161452044010f0544400361030821500380c55480c201e1798108075810303036100c1800c40b822007035502e40107e0895640b41c0c1401000d07818401c00303600a1142c0d03403d014590740e58078043c5d8003c8016201034400f07550b030643c441c103448426102030070b0303071580d41001508180814054100c0001e8101030301d18880002c2e103420240500161441c01c80202d001e64a003609500100c141900481d262040c2841694200117090340c2c020308550f0904142c03061034030707a081000800102c0c040364020404150614083c02409940e0300c1e0350350b048a0031030709810881c0c0c6d4920704100341c00c40b1483c000c036400000d8441c524044409030003900401d0000c404001c182941c2c0e0564216913203060f5007961070013083c0e40c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 819555710 1250 819554460 819554467
    0xb06010518030105070503070f0203040807030b090f0f0309010315050d0f02060d020301320d08030702031303050a020301230a051305060a0501091a01051c091709010e01030603050d0e1203 82
    0x280c00a00c00e1f8411034440000c207401c48200c5900e280300104a40c00c8070b40e9440a002103504641c0c9250000d480039005441901c41c10401c03192885040c0070780f0b0251001d02d801960303038203075480000d030a5458403149101c858140f0101041aa118805510f040756400f13080c81e0b1284040d88006040342c000c055400c80b00c5840071001041c454803181000701c400140c0c0345000300d8156007600c11400c0c03410000740c99030890b01c0008020001110704000d0744d005412401624104030060344a80b480281680c810f03140c03544025651000d504083c441c00d5034512900da815803d00c03001140c480c4060401070410800203a0b603000142540c41d41c005d618a0240d407050945032541024602e00029040a00170400384625042c5c01020f405040d00e003003004000706840c2d0a040000300811010040c0504c400004d06549600008001030640240f0409030b01111011988075800000010308414031070030309071b060600c0d0410a01c007251001540c3d41d080d034068682020100e04942c08221001c200f5601d8045c10b20012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 819556960 1250 819555710 819555721
    0xa050103020a081614040b120c07050d0f051b03030105090c0313030c0302011b03291012061d040b2211030705040218010332070c020306070807030e0a0b06010518030105 74
    0xc07006081100b4808c016240c07e441e8500a03070b0300e51054040081050b84205903004d0b005006088400d00c42c0d41c94140903003490314561071000800700c964184405a00008018862403401d45006a0800013807844981103190601656203541c0300e1210180522031107c85c8141010b01c00d4203d40781c4c503400340d8511007184a035914068050005144034101030710402d00e0005042114040c12452082d00030b10780b01011120f044261103022030b0007030a1000548940010900b4002090741c210341444407000040031b0b10346410700d0042084042c091108184c04030065580d0a0104c0301c00c07807079440d000704c81015040e00c0c071030000c2e2030070040c0e40c00150403a0010840480c00b401c1800c00003071948017a2420311422061071940d0020700d01d61a00c4090143e130900c07400c1940d0614400042e0303c6145401c00c003110f00311540000746041801c03210000003584460420501302d5041c02007814024001008000c5802542d5030310131081001843c0e01d04004011466240c40c0071035030000c102002c4003034000c21081c1041e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 819558210 1250 819556960 819556979
    0x1a010f18021c06060f17070513080a0308041b060210020a020c04050405070f050a1206050907090f02030a0c0507121215080c1008010b03010509040204020918060a050103020a08161404 80
    0x7944280750100f43d107170916920481c015641851080424080c2e00e2942d61060320a49240d0007804181c1c2500c0883d090210f0244010061070040e07030b0203502c0e442c0052825203003003041a8401031b004041d4091001b41000380790740020318401b04000c1981c01580320206640200d24042200241070351080c100401e0009000c0003140c01030079108440b178841011511402485244140d501c40c050309032040009020100c0c040d82e205a4000303c15000b50740d40c40c2c1c1d541c0754800545000d4003940346d186600000703000b002009031141203603400c40390801c141040f540b91030344000d54605001c806c0c00c0c0403c0851001c00a48a90b000e002e002c3d100d0320042c40318940720401c007656000b0500c3c80300c0c00360441c0002102468081c0e240c040c101c0e44400c4915181d42e003040280080008050310403070f0003640900503030f11165500b400e1800105000581114030340381c00740812001100310350085040c1481003109000c001d6000088580c0324a2448000b4042c100c0780300c0403102607020304442900e12402050200307a041c1c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 819559460 1250 819558210 819558221
    0x10608040f023d051e070206040308130509061008040c0f0305010207060606091211030313080604150c0e040504051608030d05090321040309050406060c1a010f18021c 73
    0x1200b51803c44103249a841c84002180c550501022603c00d00854a14400f1074240c01d10708143d1044140c00c0844070350104103545c026804c1203a20080211325424010034081c80074000f05021a2034010b94240708010490522424a010042095003c0007400780204040c48000520024060050303003541c0e0304005000350480b0030101d8036103040c20800500c00d807082d0034a6040c0c0b048423109100e500000d58820000000d001c1d401c42c1c06010901510040c0782c29100900c0060051102800e040d24051900801600d2140c011002c91031610b1170786080035a018910150340c2e03c0c00d0720000b0302a155810328918041503840c89111100008c080454007402c007001030a40381d01404014411a00c0b8003210355281d004500c0c2e4034241a4291401c101c041d80800300c03098001e8024103082c25400c5c2c8900201d800d46440380c120102003203251004004120409640502107290301d2400c00d0b041d410401d034008160304901c620b030104114100340c40b6480c01c02d43e0448581e4981c0300c0c1340804d01e02100070044003070078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 819560710 1250 819559460 819559519
    0x62d010306050a08030a110c061303060c020d0e0d020604081006150c0203030322050715091a0901140c010507020615011d01030c030b06040b070c1508010608040f02 72
    0x9042020004050605182c00c409030b0ba11007005e582803030722412040f00d4002400c030031a112485804600c03645521410001c001a00f10031018840307641c1503003002010303101c1c4001840c04541c4603641280103103502a0204040c840b0444210070295440c1c0002200344c0070b00d82004c82540244000328500c00719507800342040366410580fa902c140c00002050b0780841180c00043d405800070800030341302a0b0701c103032007240e000700c1f041c0c3c003a0058425465051610002d9003102c0e00038041902e0a064142e0819210b40090824034081d1601d501c420580035880c3c003496103c14188126030b001309213070104020940350350040600003080b040c0b608500081d81c84c50141c2d45080c0c0d0700b05460701e1456951180000c0202e00c401e01d040300c001c4012900c011801400100711400416580342c101403030a0365800010002000c020001e151252000e0030541140801c561100150415400e100b180b10303078001c00300904640103424a460141c1d29414121000310300d07610300a6221807418061519070314580701504107030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 819561960 1250 819560710 819560717
    0xc0a051027050312061f02010510050a060507020f0102210a0f0305040f02093606060103090222090602040801020d14090c21060115020c0102030a0c0803062d01 70
    0x41c110105140010054080500b090700200025000c0d44640348a41d600400c000d02110004c40010b40c401038690212280c400050351210240041ca1940d0032801000c1d06088401030100303460010041e0080c410340f08003e00a60242c3d0041295078001d01080d005000740c188810b050070403500d0000da00313500105a070300100b5000107035400341c6440303446403610885e03100203c2000d00102c1d4080000d04080100060401000c581002d28034006e40d29030520b002d001c80551050011800340310a00386a80103201078100b61900c0b003a68003591f2284840010b0304900c0e604e1403554490a409100540035403a00600643d0000800064110055008050096550790100b15501504002c440304220a41c0c40d0109580840b88580003486c0103204049180c400000b801c80c0024000e04043c10040240e00c42d040b488080f0301041c0c04990144480c1c6110701091016602d00040c0b620060460050483c01030b0a420011000138200c1d15021265400e485144903500e2015030307150f5111246180140b28140007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 819563210 1250 819561960 819562001
    0x5040516080304090e060613151707031e0c06080a06050303120a0f050402032e0507090f0605070c060c05011e0506040e06011518030f0b010501030e0609060103080c0a0510 75
    0x105d13803010869500a00b002007144440e80680e0f00c3c0940641005002d0f1100c0c3d6011050014450140420081c800d04184c0d0240a05030b2441c01c02c80148121a100d20868148200c80000090f202c081904265541410440340319112801707000003c0c60b5542100e03815220010f10003007a4100c0c01e0304103126032510303001807214501c2e061000c0250b91050b01c00a40551007042621101840c148540001c04010030002c4000184200c141003910801d481001c04aa50140140401840024020041d110b5410010b2604034107965054140305a44151010460020030701010040300b9004020f2980c0005d010114214180244000415090702c03040d10461400080d0980843c0101e4014101c034107018510910060a8400765103624501303c400007071420440d0003100040000c4404203840303015003020406503042900140481f001486400001c0d4855004c0001019000480034192640055901c0d00e482c05409040e190803841070001b862805468091140c40603168440620100003a801248 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 819564460 1250 819563210 819563231
    0x1903021b040b0d02130908070606080d050a02100515040912080105101d04020408060f0a0f02070b04030f11010f021c09050d1419050901030b0102060c04090504051608030409 76
    0xc80300e07544001c1d0741200f250405440075103404031040c011404640000b10381d165044e070341e1040c1070348107060840745170350343c0e041c288503d0904004c00389011000d4140f240c170304400924080e68940818000754501910307000000c10041d140d00c00465400b8001d8802e101110072803a20a40c0200d003120060b002401880000540d490140c2e03a021000758161120040700c00c00c01b491000403000e111006401580800c00040c8400c1e00700200d600c01c2d8400030804c0c0c100c0c00d03c281e44000f620b5403a03111130f21540c01400300b000843d99806180d5001035041c1803901d5400a103e03416074000b4064030340d4803115443d02101109481c8160002d11080786004031f4000a070000250785d00803039004000142c4a51b22204280c40c0700b83c010005222141c8030b100c00070b400d00c20002401c00700285090501400541c01046800440d42c00d4094015418401d0025001e20324003041c44007500d000e580b268400260b21000854184101070040c900c900b0110341142c5445901e40700019a02e9109200340d40300b80b40703000301900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 819565710 1250 819564460 819564469
    0x4021008071409120a14060a05010b040513091b03050f01060e190603061b080a0522080903060403111209060304080c10060326030903030412021903021b 67
    0x184551026202d074520303403042c407000d8666074005161294003c1540e035120340740a0070400618820303901c503001d41e5400700d5001706054288140540880381d5070381071a00511041e003403e400c2d83c066031001d0b210001c11061840c03240d4050807507800090716000345c0389038095050402254200a0b42d0040e012149003441482d00c4600320348552045610945111001c500441044214030804403c416000301d1043c0c3c49403511001c8540c000b0141c00740c8a10300c208801c64541010605030b1045501c1003c102501c0e020480c11482d460103ca038652564102d441c4408000d2000241c42c010300c000707812244c0510b801c0c90050140700c40c030020b00000c0e1092065245842c0200b500f11002440050507640c00c40d242c90755100a00c3c0c0040d1606001401400c00402c40c408007442400000c5003e00c1e0140100100041d081d80304180d040c6100d424224108104071140400200b1650401d92000003203082c01180b03c0120706204003040d10b4142c10100e403003501d00b4140d0026160859490700c07240700e00046440301c01c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 819566960 1250 819565710 819565727
    0x1081e090606041802030d0806011101020f040905011d04080d14010f0603290906060403061a040b04060302010e0906030f0d0206040b0609070c021002030906130905130b0f06010e0612040210 83
    0x81d0301d94445c0c40c400458902c0b07198030300d4212750181015000b07685490382c0182a82c202d81c0c6000d100803c0401c4c02c0000403440d000b03d03401448041c0c01c0502e0503200800c104c8071800c00a0028011a10000d00b260410400b50310a1001c00c181c03258801040d61524880c0031b0300308181c0300f40800031f406c05011107025600f0741c04000d038417031104035408401d14011090058203240280050f42c003210501000000c1a16809240355001024038a0130381e42c18000204411207860342410381c02285003520520050742c000d0540c0e154220200c4501840390385105c0000e19080210058070380c1c5005140b800804160000380c018040c0f40300e1862000036580d04401e1003034411007120314200260800c09001c0240c10000901044402c1c1441a00d1034400d040d80800c07026401082060450500b5040802107100f69102d010740001d840c100c4034840d4007a540b590441107201402615000d18414040307040350307001c1c030b6000c040300201402403a11441c0090201c20500781c100d4cc1a400340000c408a2a46588111140b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 819568210 1250 819566960 819566963
    0x801061d041221050601022521051f2003240a0b070c080f0c0105160507122108130201030e190c14010e01081e0906060418 54
    0x189540d900e80c2c80744048040c612000c8001d0103000b9090f06400700703079060201c0f00c0c01800b00c004541414058002450480074440c83e54200c103a00601028041c1c9840c55001251941884080c0c0f500550140d41c050326031001c4010207520640c0c83d03401103858010501c020300550785600304880803280501851500510131030403503080040000420003081c050f0000d607103180090311228143c0140e80804c826103100d4001448a40000c03490400304112200ba0b00050248180900420810070f0003241d9a034032600340f8181440000b1887c080710302c40d000c000d0840e1940003011160707450f035a18030580d50268400000e4658100980d24101090014414059295655629103149681e000b030383c8252040048800c030304140d00c078400851102c00030041c07141c07003ca12002108046402e882c1c04c9110841550010001950040901c0d850b40c0e04046458003c030400c1c00c0c4003800d07a88480c0d100c0b240c0c000349040003a0700c000c01c0e8217114400200040a41c0304bc0c1050f201005000442404103030640f08040c0c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 819569460 1250 819568210 819568259
    0xf060e010f060c06050703022106151206212a030a0c09020309120f03160906450303091d0c0a03060e09010524010c030e0a0504020c0106080106 63
    0x90200024000b944001d9001e0b085141c0142407010184c0704d040c11000400040c2032649ca42d6042c0401032501014803403070a168240d003a03240c03c0d000c0d00a0305070000028211031127550b100c07501c1c2150908917108120007552880503202482d4140020494005088140505200d401203d02c4010304000800340d240c00d40080080403410300d440420070281d1710013001040c01e1302032010042803950072000901394001340c0b5800c4d01d45030f1500103440010400140d0035a02003004a001c104556500702c0200036000940c5465052401141c00c41c02c02e210f010f048a2800d0340e01e1075405020303000400044401501d01c66510001001d40e076201180942c03010000010b0081850b0022645125041c40203000c4141d540c00c021034800e680e03102c850a200c1086031030072866511241000120b00f41020102103021070076002100c100001390000304a800b841030014280f00c6115400342c0140d1740d10203040000c100c005d0040d5601d041d1110114060704051150700f003d582402d4022826000d9501c132400c200ca040700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 819570710 1250 819569460 819569477
    0x7030c09060e1b0405060d05060909060103170309190302030910090b0a120b0d261c0b010212030c1209060705071b0e0a0912110706210f060e010f06 65
    0x18154a18040300304500450043c10080082d640c1c4484018140c40145040001907a1826009101c142c1750300910b211080e4000d40010320000d40854042ca814517001d6844603240da86103600c4a16110134281114420100e201c0e0820805a00000511444809950004403401d000d41c0640d02209280207070b20310b449061000a1039503201c2e96188403900414400410364032102004075150325a08101640c1c071109445000750003d07140d0b40410504c0304059129803510b1405415030701c920821440311071440c2e454245400003a0720812100ba10300944400459403800c00034128440c07170f40321159250840b00c1c0c51002032200d15002c5800d91150550f80c840710301e4454540c3d80c0807a110980984905a07081051010401202846009101d2251800005110001810311002d14281c44421a04000e046086140004000710381c0c1412501d4a0038403580c484000d1007065002070710300c0c4818100300e00e0010749114414590300f0540c211140c5d50a05000d0f41d80320003103003100401601643c1c0120b400c54 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 819571960 1250 819570710 819570721
    0x40b0f1c051006060f020d140313021206090607020705031501031b090e010209040b03030307120509030702090c0301030318030b0f07140d051009200c01110c07030c09060e 75
    0xd030881888144140151a080146034000c0411070b40c0c0343c0c00c02c40003e160740503903640450f0101300007030b001c03c2c803428040300b890901841c007000d0f440020070340d0f034004079800c01540c110745071120442048a0424161285490325842c0c090780e440003207801a00510400a00003150704000c0303403610080c002101c07001c0e0640e095490341c0c03500002041c032010034010000c20014611045100c2e2090f02c3c0710348400582d44582840800c01640c0b13002203130520a400403c103000c0710316001080170104407a601d0000c40c1e5a5148041d250450050480194015070450200a20140c4100056040e01d21a4481c3c0e90030903455540f514000740e043c0030041820701c420010800020301000c0035a4462003900c1c156541c95040c0c01c00d207106810012001a1551311002440409040c140c140d4001d800301440c10801001706541400d01c0961003460106004000a17208142190070341110183c0d039451904d4540c0d450004802e01d83c2c504962000307582c1002c100300d000c076000319030340140e80856280d07034150300094070351 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 819573210 1250 819571960 819571999
    0x90f0603090a12090617070e010f0221030915010b0a1b0f0b040b090111070807110a24050708030f070c060e010605010207080c09010303050f0c01050c0405040b0f 71
    0x307020850944140e100c00320001e020400c0910250fa1140d6541c94468500080901100d80718110b0b800909010410403208a40c0a03000c1c54010409182010b892021160f042c0d0420140720036039941103c1038040011131a6003d4001e42c0078100220407912440c0b01542141400709017800740100c0c001d03040200c003042e20711401c0c016034041d01030b25039480c101c001079903a0440348860050441d414a910401c0006020f403040c4c110f41c0c0100c0d80002848284a43d84600000c0d2150349401443d00e0f0700481c5200c10300c107041010780355008001d00f22811481e1a001c04101c1a156610082c0d0310200765407030340c6020352040d0192018141d00400c0c80d4195124890301d1b220750341005103880d04001c12600f0070310100d4290301501421018983c000200c80703091000090600400b6003280520ba031103ca020040c2d03403035500c0d80c581100c4d054075195480d1120920103020602c61a00000c44a41c00c000c1404001c2600800800c120380048404000e020586012b000030090f001c2c029680c070003030b41508860900786 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 819574460 1250 819573210 819573217
    0x60d06020d020301060816020109050c0423090f0f03090d062304080a030b031504110303190906030c11070509150303070b040201080708090c060a1205040b0403090b090f06 75
    0x21424000d414140152403a0040360000d038081000688444240040c4841c42c0462a0100c0380d40d00c02440302c00020349580b69520306100354140901d541c5e190440300c404c0e6820303207409800360300728410755030b400d01c6504607544904003e401400d50050014151400000100311607100b00d02414400c649882520b882d00100100c2c6c0d040903000300c0c3e1000030105029403026541c0b00e20b1180d07640c26101e0b103c0901c01800c45120103800b501039803042008181e00705080220a41c002d07030000b52240c1c10440e141c0403d00b03601071003060b491001c418911840269400081035029529142e504103c2c10f03507203540440b4580000b441340c03400707500909400d110b1410b040300c1d0643d02120748038900611211820100c6d2856000742d000303079900e113007a40c00d1004640c0d1202c010ba03044900c0340707020141414542d82607902c540c00c10820621404000810070001030140d445950181d900500800903898075040c012007651041790110000741d000c201c0404c503200c8030000e90340f2205000d80100010150b05040c0620b5a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 819575710 1250 819574460 819574463
    0xc02010c021305040f1b140405090c0307090c021b0d020f0f0607050c090a0b0901090c0c081c0c03110405190302060a0c0302010b010c031403070c1509110a0b03060d 72
    0x7020325041c0d11110006000343d07070140e8400c00321020045080d0502045400301c1c000401c102e202001020803072100c0407200304c06003400480d0001a20f442c2c0001441c038084406d511503805004001c8000340c51005c681c03000500816940960b2075888038001d00c0360040c1e044038038056220604001c820301508200f0f12280155401a09080b459500c0000148190b04034a004440660100300c03892103900302034014641140024009001d203041341c0e0001180c40005009030348480396259072840b0103d1159107a143d409400c410250750701c804526000d0b014802201c68071320101c0c14041020b444034802e1207211001c80d9907881f41c03400d00381050304008010107a04e1494041e240c2c45030002c0050b945540003071403112000c2c1c44245000c221443c020382500c40c0c006019051000ca040d100c80800d403c201084a9144402680381e980d80c4c0d418010f450880e40c0c0c0301c01802a840780020308030220469880703000058040d600b5030342542003002c1000342c2d400050103100302d45103060022444a0510561415545 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 819576960 1250 819575710 819575719
    0xa030c030c060b06030a0905150403090b032208090916091a0c01180c1208030c071a0103050717060c04060c0c171615092c160206160c02010c02 63
    0x105031000107186400c207540c0e91441b1541c40c1c181c1001c100040010b86000b0a0301b40c0707078016601e41528050004240381c8229500d641e40080060b07810800b03065a201486403010301e100f002c10076820800603d41010320414021400b050114161151000d03050203036115643d100d0681c14102504544000658000300c507440c24140010460a07030300707004034101000310705000e002c540c00c6400c102d02440e101780c2c0101c24000c003448803c8080b85101c021244c2c06608441c605030354808070701e40000943c041c500c0c49508011600c001004018001c9103160031991045100c02d483d03100840302c0754440c001502c100500c10b000b08410001c0d41e0241d001040118001c0302c101e100b660751070100d421007000c2d0180c9007141e5000582c0e21810707000c40880c1c40b00508403150700301d0000c20003440b024011440074000c01424440c100802141000d130440e4800c007904c1404042c4040b410b040c20416038240440310084098000e1400060261008550b2403e401e040741e07a0385035401545030015100101403260682c0c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 819578210 1250 819576960 819576971
    0x2d0105090f0303271023070204050f311209030f060608071403060a0f0f090302030d050a0b031e010603080a02100b01031517010b0d1a01080a030c030c06 67
    0x81d42c0e00b0302c00b8064030711000c0c0036615622030098102035615006140d240c49010180c12060205902400f01031505180000404501c0c88503044e0307084074024110025407160070802003081c1e41d0714200025002c2d00b902000d040c030180290701d02c0f5134541084940400c080c0340c50200103011804c42c5a070025031315403505045100c1a04c079140d50840981e51001070303440c582c0368401085142030801450700200300810b08140c101c18064000385e2030304009020003a1007515440220031403602640003015541100c01c0c00c0001c401d003454040e480360064441001c54070314090000e008090580581c07614064002c000c0e00c80c43c00041c41c60001c42e2002c0c1c2c00303400d4540d43d450007c0002000c170b8008010115031790f00200100d08600444100784c8200c90016810181000800102c83e181c2200e04000e039007248070a91102d180201c180380c018085170840c130394820030b0b5100384810721070101e4032042103072044c50300c1d00b44980c0c9034266035645a514850060008248000754008a0f2158010280c0075204040c0804c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 819579460 1250 819578210 819578239
    0xb060604030b130b01060905090708090f01060810050c03040206090d1109010e0603100e1b01180902030f011d0a05040206070c080313060201110a0f020f010207030e2d010509 76
    0x40c5041150f5500e10054003602c3d200502c125007210500416192400c089103505000214a0304c8402030008002e10800c00c0114151a60034011b0002c0c40300800d0080110958642a00340c0e00c89028060303031002850320b40466410710881c011a840b40c2d4000e807125203440b15000500205c0e181409003074a504d44084035107071071680e80810240c020100d90078000b40506105041504001c54000380b10030291602e403042507401c43c0419101040c90880044d4a0306400007001a1040c80c0d07102c2040c540d11610800c0407402c03220700c1e030295002c0c1603c485c0d0500181e807120043d0f1760343c0d80300a010901640c08180012003403810743d00034a0b8001d101800c2d076424050aa5070b50484220351b80c00228103a04007040c19407040c070703010a8101c000c1c20540300921180a4584003200b0b18480c0f00900410000000c03080c0945034000c00a180d07080080c0380085540d01c2c0c15050081900d4114024a0701c106400c2500d20848507400c5041d05500c03885443d0107038420302c08001515598403980660340c20442041c1d0521 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 819580710 1250 819579460 819579473
    0x40c03030c240b010305060904030c170918101e09090809060a0207050306090c0123040b181c030e0d021f022413081c0603120e01020c0d0b06060403 65
    0x209041112800b0512043d503800140541b0301c0141420300510f80f20040002081d0310820b0100b0a0b40c100c21500318480e030400c1c2c50249440750501254221901880702c002c030041c0d001406109240c411041e04060b40c803941c40902c4100800c09500503d40051030070701c1154219401000c0c079902c2050a180340041c0341c0e011942e150800e02115002da0407a541c20403441c18140f15055025022401904105410200182040c1941d42e00000c01c104012210703202c0d49610700c2143c002d481c082980c552103003140f040340c00c403c8144c0314850740103195060030360030784001042c90081101c0c0d058603180310340b015046c10b000680f91401026a40075041040b032403006107810f910343d04048801c1d8007038508150202002c1c3c4603815a418480d0700030041c00300700300d0012441c2402c00f40b040d034042e0b00580d4482c491003e0005216030f65000c5500e032442e18400004025450039000d5a940c4180c888110f0041ca550041e602c4d814088079103500426401c040100059250303000300d5020400801d200d0070b02e601ca48644 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 819581960 1250 819580710 819580763
    0x1b09020c0a021f02030f0d0207120206150609181e090d1205071202091f0203040e16020d1209050d080708090c090a09050f0109080903060c03070212030a1404060f0b010206040c03030c 80
    0xc001623001107051048e00442c04000c84200c507020303150b040c9050031640101d210f010d8000d100603190661980407074140088131481c0710400c075603510b500090f030424640c110b031280c0d100d800f03c00101d03031540405041203030140955441900141c4880345400d84280a0030042d512100308c0541c880f250340500750820f5804c08008683d91403e07401992924100b0b5448074140101420011501403024601600b090340015041810781c11450440d03c2c641c03011003c000078005001d402801030082d0195803d010382c0c041003045c81074502d41e42d0601e49440384080140c4400d181070001350442c48010016400c51036a4008030140c0384a03c04480268005100705400c40f24549030446000100003041c00b034a01e010060f035608000e01d00a21440e40c00c2409002e0350360b201510005075840c80100000704211050b1780808061305134504c50400624052400e03a000300b4801c078040404520340282c2110755440060034510640e4082820039403035042d80c6055608101d0340c5400c0314544040555195418003035900e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 819583210 1250 819581960 819581993
    0x604031e020d03020601060e0103200f0f0c010209011b050c01052b0902040b010f020c010c1e0501050a2003240a08030d051b071b09020c0a021f02030f0d0207 69
    0xc5d208550600741e00074010b980390407d0314101402c02e60940c0102c00e0383c1040d10300c000c18404215550303a40d80407203134403180a04c90914143c01c0002c1403124181c1410b400910440100342d80e48282104003050110076010040c0000c0c119902040200849500850081403104e0385403104041c9642e03002c00f8151004101903240c0307071103611400d0240441c01c00d80541c0711101001d08090034026041580250344015540b20b482c1040300c0400c4080a0021081521001d1103444044889899007400c140e4060441603130206c440c40d03d04103110b0000c810410b91151140411848185107448032901c006101003011050110381d140b8580c014284d03036442c200200101460400b86488070404101e10701210300080100218480c04810703076124403005012100d02c207510415546c8060000c0070030701e030101803a800c200c044074030020301d0385064840000c80500042c0700b20381851040e086d01121241e85555048980c0c05680240144029002d882d0058030303c410107064014240052a03c1b60071100350388000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 819584460 1250 819583210 819583213
    0x30c11030a111903080a020a0527090901020c0c0d050f070806010e010b0901080105011d03120c060903070f2607080304030e011d060708040e18060f060604031e020d0302 74
    0x2d004088050078000d91440240003080c0c44600700c03840d14040c0092100405c4009002d500180445c1140d011f07000351115030f081c014141303040040d6030610250040d44080440d104144400c0080c403e102e050007100c010840700d2000c0e0220720402d4091003041000f0b0362048a09010300301068003404001c0015400520b0004010310342945003c80309821b07070006800918125000b000340c450b540e40c1002d0000d0441d1000e280040e4248640401c0e813140102002103075905008203001c07461400042d4001e4031081c3d456405840d41d0b510b03940d040382d40d01d12400070020b00259000c80480042040507004102e10105283c2244409030150a070481c20382c01820b08584410011052009043d072008015003080403e00741a000c415600c88201d02040a002000d48103038000200003041000071015a0010400100a8685c506111141003040c09203044030048510070940001c030780b5048d04100502840300548043c1c079040c2103132506c0c81c0111244108110183c01d01002900580340c0c01190420540640d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 819585710 1250 819584460 819584477
    0xd0c0c0204020334020705130905060c040503280803100909080a1e2309030304080f0c0d1515030203030703080403030614130527010b03060109050c0a030c11030a 71
    0x114000840e03184010f0544d9100c0c50038410420326030001501030070354000315010045112910741040182600c00c0009106014130400d00c0240c1007a80041c1080d00c4d421425039150100312a01c60100180a40b04031140956541c0075401040031100150b07008149031b050181c3c2da03a100d0b031b08801a41c1034070740e04890040c1e0024410a031280e00c5100882c0b4100b80e01c030f801c4054845240014a04541440504014030348410611580c0c180788044800140010b0141ea031510b0b55869101c2e11480c880e0314031100c41c041d000c100c0c21140340040c0750581850b4403102c1034a55024034541c01c80104145441c01c0607a00d482c44010025070380410107000c07080e100b65240d00043c074203441d00a05880003640080c60300f9005040c810400d5848040034030b0084e140000006c0c5584c2d900d1602459880323090700f5083c400d5510309407000d0596041d000b102c88034906a048851781e0341d80e0820340e02103500469464802e6207040c015117100b41e21942149040d4011880c000841c1c105112035141142c2c800c0a128003c61100c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 819586960 1250 819585710 819585751
    0x21090703030e04020909040204053d090e1e01091a271f06050607030504080706080408121009051501020f03090a05090702070e071716050d0c0c02040203 67
    0x5007000b400c2c1403040e142582044404400300352140c202a2000f4804d64843c170005004856410a4440220346800d103142a0b2030702e0002c80c040c10806400c00442c0e200005130101d42c0b100a4080c0442c041115801000f01c00d0320300507801c40c1000300c0b418407440c654940c1c1015000c99000407080c161100c510030900140e052401c0c1003101c490310110100080c02400007511407080000c980c0903d12401c000300080034110800c86180105103d40290740d10a101203100b8051650190252007a5802d40040300c1003903441d00c0b020360307c55600300c400400c05403003041116540c40d0032083c00d5400004001e2260f80d11901c03085104103450040395019001e10680b208401e5543c0e0403c0706003480c0840c5009103162141040100e040e0301d215004590054500c07a0114100300d100300302020041800c095400c80f103007490480103240b0401c900b00c2441400301c0d0400304203c180301c1c0c110447c4403030b00d58403190320304800d44900364080c00b0035000c00424020442002c00c0962110300040d1300c9034182c0101c003039104961 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 819588210 1250 819586960 819586967
    0xf111006051201111b07030b0f190b03030d091e12031107020d123e030a0c0b0a0b03030403050d141903090f02030a0501050609060d03080c2109070303 66
    0x2950ba00021681095aa0095003d410086600d070448030002400d0190784000711a280c40c0e6654070061402c02c4c03d1080007440c00340c80040e01c0c011380031201c01c01c2c00170441c5698141550340303a07102c29a05810411214501c24410351200c801da42c45000f507410341c0b181c90140e008045034032100580705068407684e24109590f062160084440494200c0c90030200280c000c199520410710004040140d9801c07c5074283d40103d08820b01802d460311810642c4c0c0b41c000b003082c500514103d516400300800e02c2c4030202c5110101c259016410981d0f1a0742400c1116103074505c80d010098060f40b0450b94500d01e07040e03540c07018802003010b50b01800003006650003a01e00103002c000e903280600042401440641c039080712070200f030031402c0014a8089010710301402e081038011180d1000070340c1032103180390307d208101c0b040d002603206004c112101611a550002400031040404100a0004031200300040743c1d6228600600120700c00b8604144840c517440d40415816003066070483e201e940001010010180d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 819589460 1250 819588210 819588229
    0x141f020d12140405151e13020d051b0a0501031a210f03030f010e19020d06230a090b06041a0417030d0f02180d0303110a0e030c1804030f11100605 64
    0xf074101b0f840720401000c0e441d900c0c800000f4051000d89080c2d40301031819503850445c140d070f40340c4c0c005d07090324510490451101041082c0c1100507001d84100d40340080c066001c2d101d00340c1c49140c00c401142c0c94040220400c044081090f0000ea000c5885e01c1603034058030820080444041a668001c540d05d080141c000540000d050740000341c880c1d920005c001c407840003090460504802c40d940907840d10400300c000d40180c0082c2d0007100c0c03003d50914000c5540c81030035441e0b4a8503e8251000820b00361110740c2d0070103030f812408095821860800081155100030301d0910591007103c41418141070b00d03189400c03020042490004d1041d0300114601011901b5486040107401d04050110f00d4007600401a4541413640c40703c0341c0c485c0c0e1003900004d041c10f001c2d40140741d06540c030040c625038035506d840020f4914421040032038000d201348403560f01c16080c1100a0f8801211005407002540e64a2b9011107081c0403900082d01000312092110802c40030803c84911030070780400c80820200e0a000a0200006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 819590710 1250 819589460 819589471
    0x1809020c0a02090610050a0c050c13020706050703150b070c090e010203041b0f0b0a05130f1e0b120c120103030903111e150c07141f020d1214040515 65
    0x803d41014120580d40042c11264010000c1c00c061008c054030342809824800308401d1580c10102404108002c0c5e00c01d035004128017807050304200026101c11a04a045901c154901c039520051400144000440d290103014500e12a0805040c1c0301c0e180c03c50f840030303541d941d680c2c0c20300f981d0048280310802c11040d2a000202d003440060075415480e10301544500c0b0103d104041c58a400001c0036200c10b84142c2c103d4840c1071504840d491902e554454035040910244140d28503400e4010031002204880d241d000201c0c0e000c407100314100800c03889281d400400241505030758032010080c440c1c10890301024a4000d42c081d0700d505c2000d51541c00c040030b4200e18540100e21403450250402d000d4101c005081003c0d904c280c644200711041081c45503c80d00c0354400303034801031140500001d41200c1040d03000c441c548040c0c0d10380e80100b074800d0713001064089414003000981c200320003000903148241c04540702880020030110382c3e9804039001000c0f4100660702030311a0303003050b12212082118480c10a4021 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 819591960 1250 819590710 819590719
    0x501120506070804020d050d0c030212040b0f030c120411011727031e040513090201020d03090219030302030702010e120c130212090303010609140f011809020c0a020906 74
    0x501180e40e42945920700102070308240100c510101c2d01350344a10a402d140c0316440401c6501c920204600078210f000503080860062080c00802c4140b0240c1d0f006403001c559855074540d040c041480c1440400790001810030700062424020350010700400c680c1c40e40034500440a00041c41000000100281e40c503150300c42088100b07105202c03002b1411a4141d495041c40d80d40203060220150a6508600c104041d14850400c201089024040c180d0000d00890340100c03840311884071401e1320902928600100640581c101103940031085002c0d401c41d844151004012442a002001d2040e1311840c00c3d4006500603400451000219600701c50b241003002c1c5d0031200da0508100c12141c44c1d60f1841d09016641c01000504001d103000405074041d10403900131101e500d44a40342c80c000e40b40e640e030024802c10b000120319440c000750449000c080319541c80700c09000001310402440c01540d840035a6952284900060580002c4804281c40500340c5003000c14040d00c3c082184c0d004018002a0151000c1d01c035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 819593210 1250 819591960 819591989
    0x102070f0b0402010923121615090305030d0603150608071a070206160218010821090406080102090a0503030f0301031b0e0106120e0312060121110309010501 69
    0x108515202034604180d1045548003180e50b5480126401001c5502008800003034101c1d5000f0b80c001c000c0b240c0c3d079040056030341c08100045001c465565410400c0e04c4400b0190144c418000d01600c4c682c014015044c909000d00b1003507590740c5840c42e5900c441321f01d81490f40d84010601c01c1029601005100488048041c0010380c11300c2d4402d9101d900c2c80c4101c08454020f204103021000142003981c040b10b4000340895151401216000c903000c9540c40100d10640120b96005500d281e0707804601d0580d043c075402071a045800541803c040401d03000840482a010b1241c400640c0e580d00881c00074202d2803001503100c441140600c0124211303600128480d800c05d000715444100000d0503281104e0b040b06176034010344840c00c2000c0703690b003490f000080c1c1c40070208008980700c0d40201849601060a00007080b0800c550702d00c10752070f40280c3e01400c07030106484d40403c90344d41c031482060b030b4010300201c40c1791110b160f907410040450b8000307d0004041070b004420800c41a80a1040c1070062403189101c102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 819594460 1250 819593210 819593213
    0x2150306013e0a0c1e090e0a0c08030a0e0f0619020f0c030109030c0602090d0804150813050606281e05010311040603020331151b030932060702010207 66
    0x40082c0d650040d001965480102e100c0c170080041c07116001020940740c200700c00f000b091410380d2514100701d015203610180c00b10000b00c0d030400008503036000c4080d0b601d40c0c1082003d8410032003103036020342c0328a038401800e0101070703004a200200c1c000d280c04203800410010801d55440780c100408a440d01b0301c2649031103809808a60420141140264001d0300107942d2250100041e0002507070f80f10191080001003408214590401a040681c1c001074451003100d035500c407640d001402043c84010100e40000300401c10509099044030100c002d640341c88130009442d403010443c1b0103102e9124141d158075403c2071311445070080e0014005080286824000f00480410a02162007288141c0c010164004000750300208406200c0c0102d04c2006c1610001010070b5400840421141c02c3c156440b40c0c0c041c2c180c8a0801c014425007002101c000301203400c0c00d4130118250014440c0d0801a102c4551600d039000c41c0c0040405841c40e80f54500441008003400031144c0d81c076121004004c44103583c4100403500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 819595710 1250 819594460 819594473
    0x9090f0509060601091d061c050610050f0d020103050414030a320a0804030201020c1b09090d0f14120c070c090605060d020d200d1802150306013e0a 65
    0x32424101030b005140d1076000c0440e26400c4005d0000b00308d2140d203841780c000c001c004105d00780a084e1820303100407085e4582e42040304961150103a603a101c640f100354440154002e810050740036004000300f03811011890300380c1d42107600c000800ea000480444602c148100c290b41d81c41905580c5100681200d180001071030124811065900184070307a10000030200347c400d4041f10615203002050f140c1d1910342c1868240b0110307040c400341d4414111280020900100000c803510003201940e2000407059107408140d5401c502c0d4041c40e13078004020024001207840d0107442c5801541e948422503a201d800b42000701c40941c558005044850900c0c03001c00c034a903200700c20b5444143c141040160740354414070741c04006181c801800300300840c0c400000442c140c80d00e0060000714614a4060001c0305074120404074000041e90001c0d404480340016015075031482015640c0500306050100502c03040040c030002c200d0075140e0b0014881e0300103a40c00512407201801085d1110f100c8000e060b01102550b801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 819596960 1250 819595710 819595739
    0xc051204030c0503040909060507031817131212030e0f0606060d0204080f0604020324012c010806160c0302060403080c1c090b06010c031e09090f050906060109 70
    0x501044040e650b89010f2000c1841101c3c011300d90035000700030365801ca24245000d00030403070f54517000c40d141214021407414501c035158035148e40070403903119002452280c402e0030f03000151081c4031409401b030080b80032041d441c04145018011100e150a001e038400c5c0c0207043e01e83c042c4a0b00351b5504038500d000100c4000143c219003014085810310340761120b20f04804024021603200303190920a07145a243c03110408610140154020303420b5940d08200300c8841c0c120b0940d80710318040840f581d40700405c02c4500c001503200724902a0240c150020f0128941c001500c5001c3e041101a9000b242c24040e481c52441c0345003030941080d04003044810040d072006500c86000400140071b0003040e00009080750784a500703c0d00a00b240d01c1680c00240c0250202c080140303101e8008440303520026010581d40c0d801002440031a9038555038400d200ca450850082110f03d205410b2014000e12030400300d400d00c0c8034020149010102d1000054510702420081e140041c050480c60620810040500c00c003003051044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 819598210 1250 819596960 819596963
    0x5010f2412020406030e21090405090703061103100f03030804080304050a06052e14061c1a030115060f03230103031716021005151509040c051204 64
    0x140494030341030301010740e103503115050394103030003880050003140e4241c041c0d0001c1c8416000f803084a50401d403143c400342c460005000f51030210074040c03040c2e03000fa2500d0b81180b60702c1060003003134802c001d54968a14090b00c0540d50000500c0700040104010148044440c40041c19400c3c0916103091071600d002e0401040034101406444c800000030f024040100030550085501c22020400d41c940001e2404101580950345600820070310410001c4591103500ca000341e804a20010703407072020103410008030703038003000b01034800002c0c2100000e000c013442d1140300b003000307a48007a545102101e0380c101421076242c40002a40803080310000e21140b03900159086a00c106414001212406181e00d01d101d10702458440300c01c040c4507400032080541c05079140c0c00d4144410796241403603c600c9220b0829103d44c02c0d555006a004c2484140703884c84c02d03003049420940d0810907100c8058500c0100305080d020415010301008000750071009818103201f00c00d00144140f0700a82481401030a0707400c071000c081c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 819599460 1250 819598210 819598259
    0x302131409120f0d09150204060e0d0b0121050114070906050c060103081b0604150605010207120f03030204051002010e1b060d09031e1815021c031d010506030105010f 73
    0xc91480f25122940070351a896006510242c14400184542c0040e6200b8003645d00003d41d0005004cad52824910f04000b038103035101100381e0580e030900d54044a6904542e500308031844c06005c4100c007140d020710641610054080d452107041c0340548003d00305860540c403202c2000001c203c66154038030b0100703080e0b0549600401c0c0c01c1e650f10340a45861003000e1a8030300c0003003a0060100384010420320740d84e140e45c4401006000d02c0714503603490069803508030307500ca11035205031000002ca0010341201841040503101f81001820641c882c40810329075101102c40c040580c0d51105e43e1a8140010042c2e41c13840d000240e00c10941e00400c101090440c002c4002c0c0ca41801d44598680040601030f43c82d1500720f001e00901c01621030310001c4002c1407940b640d00b107900015202c03030010449403030500080b0880002078000348281d0b00700011840b140b051a101140c20541d890b540c00414165056011a02e07103540c900100d001d040c054101421a241a4020140c07015005802c000d040e612608520084081d0304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 819600710 1250 819599460 819599467
    0xe16030507020709060b03040b0c03040503030703020a03060906030b0a050a05090d051c110d0e01090b0c031f0f0812181201060f03240b1e0a0302131409120f 69
    0x41c0e090b8500706040d04840c0702d06007014008203001c0c081c0d41c06507101e9405020200541d803103581224034284030544010740160810800200c60b60b000740c005028103001c0b4a000200c255803030b81c0850440350700341c10495a6501040a210880a0b0703030207440d401c519104410003880c20000300241c0d64a060651481c184000411201c003031610091054000890700070741480007403400c1001e0300c1d160740000c3e0318030061071411a003441c800c1014401e40c05000c0d4002c0328401b894982240c5034400d504001c0c01d41a001050480c0300d2035524034000c64400030110060031510041c00d0100c010305107926002410303403403641441140c150450501034140c5201b025145110b242208400303507800740c419900311542ea00c0340c0c803030000f00b00800c11000344201290ba2001c880701e41c0b00354001000b56030241a00645c4505284032020000c2e00c0c2907103109155100500d10104a0740c0c03680455003c92004480540440d55550034814104d00c2401c42540011000080c100d040161000806140540030318841102e5010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 819601960 1250 819600710 819600721
    0x90b070e1e0a0b0307020a1b0303020a0209090c03070e090f061003030f140f19032a0c06090f0302010c110312100518011505070c170313030b040506010e160305 70
    0x10750842c001c2c00c0c5004110303940e841e100a019544913002902290100c0307004514040c8410010451001d0320707071583c0a089941455000c2081c007000c040c142414a024032102e211403a9010824240200045103c18a4914015640703504024103241e2481c100d070444020008008206001071042d030354541011a404012603104803401c5101c19103104c00e1200010700111241c218001401c41041018035103040826401d50840990305940782403010024000b03240c3d07810b20301d0000031005000d41d51400d901010601e881c2d92084d0795050000755086505c0084500034158280241050103a030703070400821800040c80520350301d10948000300f02c9600220302044501c1c1400080e0001000b000b81515034540d18007021ba807400d4000c1c444d0424050383c110805115900030f0082d61010350700000400001460321000c0c642684002680c0003a9000400a50070702141d4010180080c1d0b015040c0510246407900e411481c0c504180c00c1136921171800d20030040445c0030442d404080801910b40440c2c1368417070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 819603210 1250 819601960 819601969
    0xd09080405191809080d051e010b090907090803070f0501020903030d0e01060b120f2a030a0606020c1518124611061c110f071704090c03090b070e1e 65
    0x49030100120044070000024044ae5208040d184508013156641015210850207a82c104441d1140b68515041844080c0100310700004600601d805200017524201c0c03002c00080c2103520400d420340700d10f039603501c002c09081000d2143c40c0240540015842c0741402c0074010511600005164158600103480011003680f0390040780d05603145001407207144809204031110f5a60000c03a1140e40040c9445030025026200207030782084000091300344100d008032841c10490580c0400709540404540314003100c0035844280c40b40600204c200c01905800148005000610440e1410034052460810094409207440c034261410b1151805401468181c03c0c5450840d114803600b4250b448080031a8a6203400c0c216043c10125258140b0300304071021031180303e0303001d500038410b04c111342c642c050051000003290303c01ca502200c1903c1a4007820f145c0e5402c110f50988040b980c41000194031151400708010004112070f4005405040a2102035840c401045c035024101d0080f1080d815400c484441d40c1d10ba = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 819604316 1106 819603210 819603241
    0x10e0f0105270604060306080714060412030e090408090423150a03150218010e0906060a031401030c0501020c0102060106050d09080405191809080d05 66
    0x1980340800070350912400d549120952018000d040c80c0e42c0c8402500040c200c0b46d50104449040030002400c107012075010103801c230840b100e180030a556440a036001c0d40d0301078007210042103442c04c04a13010b0504c850080d4000c000074003888148240340006118204003070700c0520001d15003580c0c0300c0c0324008801d64050021703000c00200e110080d018585024408000384180b1000d0344a03211303416100e0300403003041d0110340c2c0050410b01c0100601d50501c0b880009084c030b4260081c0020100301c4540000345018801c9000203200c0c81514081d90020071300c00660304250400b582c40386410345c046070181c0a0b090140c0300300b541c0000590310000c7d20700d0503a009603444509003000c10350204040c001000e0115110101808040303041c1d198080e09101040c22084154180b52428008082c403101054403a2a42410a903c04000c582e06038105c03044407514140005a079551215010a05032 = true := by decide +kernel

theorem cover : BRFrame.Cov 819424460 819604316 := by
  have h0 := BRFrame.cov_init 819424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 819424460 ≤ n) (h2 : n < 819604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
