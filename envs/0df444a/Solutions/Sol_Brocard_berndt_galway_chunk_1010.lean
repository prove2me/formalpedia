-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:49:11.968267+00:00
-- url     : https://prove2.me/submissions/258f7b1b-4b2d-499d-973e-3c504db5600c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 181474820 ≤ n < 181654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 181476070 1250 181474820 181474831
    0x603050a060b0415022407091703031b091207090c14030a110403080a0c02041107031e02010905031201030501060f0605120a0230070926030c0703030309051005 70
    0x201c10081081130120030b02d4000254042c601c10307200001e40364010210380906854800c2280da0b540c03024018440e8020b05810001e1131401942009111442d03000b94582c00018002d55100800b041c80c2c0c2070340c015032000c50703d135014001d11003641030f1403441c00340d507846000e4020005181c0c5000680c880b07450107121390320215042d000302a4a155200000a0302a10410101d01c45055003404084000f608000141101c121190b41d0001c1d0b070b0303445004010513501d891200601c803d000b0418480480d0348445180350701c0314108014103030341621120480c018140c1100160280c0000305503034160130500480d144c103d90183c4024810b0a49a440c80c2c50808802e1007841c01241c0100901004420f40b480707030a90059841c0d60050403c9010a60550300d0080e0041e2199180300c0700c02c0502c0c0c0d550407041b006400c00c0c0c040c54081c0c8100d0074814850080000f030603000755a00c44050028250750410000c80c0c00d0080760702e00b43c139205556850040d0181c48100c404540d00c2c05078002d80801c103000c602c00c1d64841d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 181477320 1250 181476070 181476089
    0x60c1419030b0a080114010b040503190311031b0709111c0605060a020123010501090501030e03040f08070612270203070302061c0509010203011511010b18010603050a06 74
    0x44094594900098a4000c0c500074503403600848881ea580d0314035448028030140c40045034021301040d0860b14520140c00800303010a00303010504c82e9490008104106480010701e0310700b0b9448508050342c8070401844070381000d11001403528403801041c2c80b1044a40030101c02c80c0c103210b84544981c4150345041c0c5566501103000c2c4903084210340e01e00c051666084541000240d00d51311500810072941c001100b81003d07070744441c48000002158440e8070f052070088081103038203504100000300481ca151281c43c1c105a180c1074480341e154014800c5600612005100b030707250560725400c2c6900c40c0707014072543c008614902d85400700ca541900480300122208800700813458108510340001c2c1a18520a0b070b0144510030f000300040c2c948100400c107003184c018840d0fa00c851241c0d020403d031080100a44800c4e4018001081034010300c04005000c20300c40e050140852088c80009401003030000e03051540301040903a00c440c4d0700710002092303041e0380c1181e83c1804035554a02041c01603440a11030f08289 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 181478570 1250 181477320 181477327
    0xb070203070e07082703070803150d020a0b070611040303020a1a040b07050a050c0d0e120a0503090d051c0e040c020f0703081b070906051207030c090c0912050109060c14 74
    0xb803101009803280452807a15031600c0c0310a070042c45d916640058030100d5207030500000f4000444c42c0c0580180407140100c41074810803c596020072020303529841000740c074032000702d8100e0401015401510380f2080c50410305440f5552414025980c0c1c00031301080e6801c42020b2000400395004207a40c0c0e04c103540003803950348180c13103646040b98154801d044250402034144107803143da41d07051000e0b9040404942d02c407070610034043c0c100401c7c404030600c040d80d560301135610300700028408400c1e207980c0c0308100c40182c060101402c02e40d007080d4900c40072084109010440c1c030111504a503921140c5002610300700400d080003039050b07a942204150190a9502c03641042001900460007070094a040c040c40d40d807038061040d0b110749440e01940184403025150b03c000d0085003006800c119600301c1117401042158510344a18106042074061000f95a840300d00f81c601c042d009080510040405201d02d044408050601d54020483c01740221101ca0902088a10541c811a60181001850710f100d625 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 181479820 1250 181478570 181478581
    0x307051b0904111e040e0708060c180f040207020303030a020706050a0b061903060801150504050915071805090109051e0606090402090406032328060203100e010b070203070e0708 78
    0x25100b030140343c64141d451200d41000003a07225400b6052040500d81c0080c0f140a048c01c1c41c803802c10000400040e4000c034207103c0700701508a0441d16840103031041c1e030a560308103070400c04107000c2d200b2640e020350184400028000c0c040b99950051610900581d020041600c0340070090f02500c07038142c0703d10750201d01440302c82d91000840b602d6007103e42c200c1c00c0016166039a5280c542c02e48104141000102c880820200154100b40c014580c0c4a001c02c0003404051032390300c450382a4007102410110400a01191158500310b4840203003019110023481902c56694502076000507040490704045507089408a081007088212041d6000303040c010107880c140505242408000d402856982d0b0744907440d090000b010801140c220300c1c9040084402102060301240035524041801240079030409160760040d0740b040f00e041d16940c0300d40c1e0121000d603407078441840d11100241c0513080686e81e4a030b0000009071071410013000340752661094082d1240b03a0f54404440d0000b038011110100404c409000251 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 181481070 1250 181479820 181479829
    0xa0e0d030e040b0d06110702040b09070f203304020102030f070606090507050901090f0305070e041b08031b03030f1314010203040c060305090d0f0806060c0307051b090411 75
    0x10f580b03040c094641c0752400d503640c484105840f10001d51041d00f040001e0300c107040d801e150042180e840d505940c10714503814109802488032304c800c809501000b8045903001c00c0b02c002820110b140c82d03075400c200c40c22452401c1000e1b1407909240c0c034001c0c110940302808074804032080402c038030a58050b0051414404040000e038007903805641e00329841c680c0c0d51804aa00120ba10489001d0383d90340d50384c582c5480003034001520003070746500000c00005150b281000090b4000680d40300b5540c4581c2e5650180e2103600d131104981c50200304100182072006004105490000050a1107c03600c80c0c503184a40103035005a9223906c03050312041c459400d20400107558042d06020145920300c91504d00c0101d851401035a0f08980041d10100c8d91040300780700800160f40d050040e150413000c0340f006401d41c0642e0100181882038008040c100b0301c044c500011b225541c9030019212440c900200b0b4a40e00c4401c0d1400310349601d08100300c2c0f42e00e040c02000070101030030490509882140d22070811010890700c0001c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 181482320 1250 181481070 181481081
    0x105091b0d0e07030506070305010f030f02060d14070c0506010f0e0406151a030108240708060109050315190203070903110a0b070b0402100f020a0204110c0106030302030a0e0d030e04 80
    0x440721a02c456074070482e010200041002107020300050007003820580e90041c01d40d40180d0010709108101ca00c140040b0b800354401ea49400d5040b075200c0e07540c0f0443d41c4100041d003c0c0068912780d00c6000c00c2008121900035540b404198810f80c140d030120b0781c940d034501180440301c1c060342d00400d14813000100000c01581c000c000d006a14000c1c00721460307a8031b9910505c0019100c115050f2100400100f010060030800c07480c0e100b5142c00d01c8a1258010700c000c51100200030100010400400d004c00e03850f074019011340c0040d003006410b41d003120804800d42c480800c0d054501c102c01254640311469054a184240d9000e10056a10030680324516241c01c2d0708000e4005201e60b11184504000a0700e07460080148545803090880340b00d40c4c5400d004100b00303c0d040410520a001100c80142c5100354041a0413524690444001400d00703c075021601c440e004001c07552203603610f07011010080c160000042c1c41d040f800c40d0b40d0205a800c1c85005e00000c501145d00c0140818808001e09150f1318054201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 181483570 1250 181482320 181482337
    0x50601030234060501080a032c01120e03160302070503072402010e1c020f1b1c06020c03220501022d0703030f09060302090d02150d140105090105091b 66
    0x48004220b040e150b080484d0001c1c2e20079a0076501610b0301e50105904807610381170465038020082400c4022400c40b520034070302c1c11056410450030f01101640c621076903005441102d514000c0301e44800d20700c140e074040e000c02808150050b02c5100740014003450000f500340b00344c842d4804500c50010302210000e41c800f5894004906554840c1c0318170700180000c2000051203000500c2c00c01a83c04105400b0f0700303012644c130301024242c0143c007400d00c0110081d1034480c0708681c152070420400c1c070b5146c01101c5400340c40c00010015800041d000c0c001c004004050071401800a0401d0b000610702c04920000e20498402c40c1c3c05600403c41034164002030705c43d05500c072100940c5a01000d2211038032941000700503041200443c0c0310074903645046a1201c025809482c0c40e08085140807091000500f00031300b11030b0002d1046030b4654520b1042c95280301030303401e107441007002030201003200d044490402009016441c0550015000001c00e45800d407462030040440d11000c524a010060000c9510745c0720300354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 181484820 1250 181483570 181483657
    0xb070b06011b030804030807080907030305090114040f051009081504020d050d0216080706020c06070614010311030105130807060c0905060417010b0406050109090f0f050c0901030506010302 83
    0x5407051103960b54202e000c54540700c3ea48500d024500f030710300509502c002901c0d0000f00580d190030404c090b80005400320540c2e41506049844145090040b142850001c0034141200004100000d081d00f1000b8540195001112640800032031000b080f40e00041b1480399804070340c08003e8485040b088103901c0741e00140040c0000d41552480d440c0d591504641841c84d000690145040010424520300345d10054480da8020700740852520200a40c2d8a22a03041d45120f0036000405208114a9900a080f20040c00114006542c0c0d01c0c107040e0021014400100d000b0750a010000e00405103203641042044c0d803208a1508000d540d40b0350790700900070500307280300f80030300c0030b50102d01562200081c000400805270135810310000b1500385401d66000740150f42c001c07800c100080c0000d0307810401e4003080e03801c200320000b4084c0340700c0c920101403c200700ca04101180f800052124691480000300354a80080e01d00b800241c4800c401101244141030703c8911105a404d03d0307005800030050700d610140c1c045c09 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 181486070 1250 181484820 181484837
    0xb0901030b09030d11030603010f231519090605101e0c020301020c01020408070b0702011e05041e03060c0c08161401151a0a0909090f06091506080102040b070b0601 72
    0xb02244101c40345041c3c80c0e0002c5c08007108002591a09008014640d11aa1700c1070044038000c41445041d580782c001803440c10300300d00c000100025803242090743c00c000c0050401041c4a4a8400d0134045001401542d010b2030420f90041040e09100d204d912201002c0c2e9512102040e0700ca8a4000542111020300100710010250f4405079500340090b20700420500700059031a031400840d985011440e0b884050321010a12412015070b801c0045c110311900488202040c9038211281103aa40c480ca070040100e80610b058204245451441003405880c03051340104a0820407250a641610300e18900418009081101000440c0c002e280c0c03c0c090343c8280400a21f0f4034040c65500e003540d0240855000b104007407101008200103130141c41100030074001d140b619080da040d10041c001074240c006c1840c1e080c1c071014a2410404a85082c200c0190045001c00446420b49401c0000014000d1070b00300341801c00304040707014401031089500301d8502031241440c01c0304030340d03819000300f05c0280f10906001801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 181487320 1250 181486070 181486087
    0x3030409020f120f22020f010305060d17190206041211070315021e070b04031d0409060c0e0a0b0301050d021f0207091103070804170f0408010f0f0b0901030b0903 71
    0x411031240607a2198008150515100c286020184200c0c0e160502c800240200e117030246c0c0350114110a100ba00b8680441c869480c0c03c04910300b1031005000030105500786200314081f40101025040c02100251040d0b15061a17003000c83c0d0700e541c01e65011f07103110104201a030031180120381c0c201c0f0307210010b01900d000640d66140c4d0349032008800d41807001c142e0005082e07500104c00400c1404141c10381170f011400c0c039920341c65806010b00004d0009040c05040c2440c0100b0891143d6420034440c4005e101b4403040d49140740a2014103d44865000801c01030708299125141c04a61181600d1025050f00d0a581c605000c0200304c28490700280d0708161940c034011000e800c0741200c4a1204283d4000344201d600d0100e40c0011504c0c00c2080e82d4400c0800c0c810b0004c00c40e800b030302054001c3d801100101074035010301303060700c014412001054074180c000240043d103640e0640000c1e8441b004a10f0402c0440c4840c8603080030b80d900c0b040c045a00c00b25550050002070303d503007500d54201c00601d003100d0800c91036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 181488570 1250 181487320 181487347
    0x9070b040303120b0301021201090e010219110606100c0602030a0207020a0303080f1e0c0c0c04060609061209030504060f021207081b150a11120c0309100b03030409020f 74
    0x1e41041c1d000038003490702c144450000d4010780c0703880807003500214030303022a44041d001498410700600c440c01e40c0758071203c00380039002d406a894603e1494240003c1d4120308201070080e1a8400409103217000b4100001c085140043c11103145103c184c0310004100b41645c0c0e4600250b1009014440f855800c0c03041c600961141a120000b80d44a0340380d120507400e0080105590140007400150712901d4581d012101c1240e0040540c0c002c80b030500c0386501c5000d00007035103090400109044d5003280c601f41c400190b00781d11980301c90848403a0b03101d41d03654000e01c4606001703440c071190002d404241c0411082024038401c01840140d2461441603542160000d0440e4596901071002611022808241411904a00f40e0444070300e4607608010021141441908900c40d03070000c101c00036080e07982e80140074150702e007012160340b0004840070003800d2814191420903904141c3c2c083d07629216486080c42030050350310919140c410020021410a40f07040e1800001c0c0d80025640d14060000b0310060081200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 181489820 1250 181488570 181488577
    0xc0201020a0b181912080a090b040803010906060c020a05090c0f0406031a0607020306010b0d021209030d0e070e04110604150c120f090512280b0a05011d09070b 70
    0x14150a4504a88450100d071038000103c0e6410543d20191030300c100010a40742403000b01240070301b802c110b41d0350340c0000c11009000150015001004150800c0100b007500c100842c11385143e000c0402580352100d07011142c4211604000750130070200c400600c07561801c5882c944d800900401c1861a1100c1c814030705c1d24070303000b943c031040120381c442e14009a43c41000c10503002194003a2a80c508114694002a607079441c184501c03034105100191140c0090055012528902030340f00b101c2d03502c0d00b088050340d40c0e00e921400720451103604c1c000009407040000700d8500125040c864091038651165102e000080400d0001282d03c0007040000103011800054000f098a660383c8031041001010f04081c4044503104c100d8104005401c01314150054005c414542a100c064400c024011111941d50307240c0560781040c0203004042c681e01e400501789410b03100c50241c0c41a0300080150b00c400c9000019144207015040c0c503200d0078160040070040e08504c1561100e61001240e170002c2e90b07080700215660 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 181491070 1250 181489820 181489831
    0x6030a020405121612021f09050a0608011505040503060a020c0a020409050a030e0406081f110f1e1603361a040e06060a030e010f0b130501150c0201020a0b 68
    0x10005034200c4105503404424038000c21a440e680045c000042d80052601c05e4400f90000c4458400303034141c2d05651044101c20042c2c00060501c4a00782d03222038004c2c2c0900310901c6280240c4170b5408100c20b00502c610281c500b2508040c0042050307450300700010740a908418001100c510440180c3c90142c0d1715401080714460058000d00300d004480d003001066600e080000340c4c017407824400e007003005150001e224240f10642c00a150007600d200402d1a026001c007112a403104080800d001161440250082500300d00996451810300080403048000d070080c4081041c4039181103a4440c0440e0041000c0c0b40500034021380114003c800703081440c0304400071000d149001d03052440c02c0c41540c1c081e42d841e01002012601050509144c0b2130303074858042c00101054090800400c850006501940107281003008820003884400c1c1e96040c4600204207440d0000c1c0315000c8011181d11030200751103440d060300c03800442c40d0340b01d003440b0700140d0350500713410f50403030461248081140c082603460780c5060251 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 181492320 1250 181491070 181491073
    0xc17090a03120e0f03210906071a0a1107030503061305040803270a2604080c040614010c03081905150315221106030901090b07020d080606030a02040512 67
    0x142c008001c05100700d11400d680a2820104104419940000d05a890784030041e480e07a00c80801c101800c1450007480c01c416003044011030000c04208a425a00c0c00a5002c041a08070554075041c1c0e01044d5104004008900c8004100700030210b0720907c02076501400180000114250402219084640451742600d210a01205010784040544020502c5818207418100a84002403001c0e850f01000300d401001445030f0080144030340744078044243c1c1c41c0801100580c070f4607640d012007622130b20210f07540361046107020008200c0100d084a1201d91290681d55400090010341e01541e80c840013074480703940e014541c0041e01d203a5109000e039510650811030441b54804c1880c05040c0380c00001001304616101c900d0810020315000c0c070210740382c01d8010b441d48049142c6418011607100c034180c07400d90000000002c0150030307001500004070b501c1c07048094603400e80d20850106d07120f06001c5401e2000801e1100071400d1490414055500180090401454980c1d10b900049202540c00e0324030b80c56 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 181493570 1250 181492320 181492343
    0x31a0a0204030f03111b0310020904090b07020616030c0e01030c120f14060d08070602130f060c020a08061302042703081b09011e0306030c0618080d0c17090a03 70
    0x105000c2d000006c41c440c1e005d14043c2c0e08a40c0042e032212121081d82c402c20394081440801035031541c102da203403039130800010011030400500083d101d0342c0c02c0316404181031001c0c11071768581b882845842d8091426030b4070340801c81c03950b500450107842c0c5c5a2940041244d19800860403c62602c14003522104c070600000f03440d6107694005020300030041c161407003040c0305000c0d10080386801c4100d4800c541d001c00700599641c0400342240456129401400e0950703080b40012904981246c00b0300d02160088410800c825600c0c0440750391980c00300c8440240c81545a00040103080540152035448507111280450069191401002d41d00e249402c1e000203c259052085070302007504221178105064074440d107000d100c6400604410082c040d1100c820a21303804c0d000380c003482640700c000a0759006c50f08600300d0350f0f14603008109003128100c105042c41c6079030000410320400105010200c139961218250030196844820110a0824914000110810502d69503aa03003101c3c0c00061480364034445170703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 181494820 1250 181493570 181493597
    0x606190e040e0c1207060804170d020315010225060f050f0a02031903180209040501090b0a0c121802100207080706031a0301181202030f0d0203010602060c04031a0a0204030f03 77
    0x90360526a41100a00c0e0050311040c03006ca50f00c25907081c1d000f0b80116804001004180c8010001d00c01c080c143c1c10128070101c107101180049000903c0d501310700340d0860b68444412080080c0700718960350340c2d13506140710503c2008014010700c07040328894000d0420608110305211200041e074000403000d0700681000070703d018441c1100c9014802240303540b408105404142580c1c0b0b03828444010086e1003000103800290411a094020020300c0f9801410351006040c0070051001034441500e10344042000741210600300d4409115071015850000300e88041c10001d5001c0c0400b00703804c114940c5c11801480c5020862200422040c002807680390343c00940360340d81d415090100701048941c60320a905290042805490303244817154001c0d00520b10310029003035444240d242d0f01c608000c003d48030b030011407001c410946c258051812900c2c60b0302940d80300e55a03c001440e1610460000925a131161441d20503050750a03a50706074040300c0c0800040c07502c0e4032034403400003a4101c48011800070325070954051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 181496070 1250 181494820 181494829
    0x11a010216033c150e0d0905060c010b0a03150f0b03030307030b011803060e0609070302090a0504050c09090f100b060912100912030608060606190e040e0c 68
    0x30352940740c800030312050a09650380c070b405502e10941103040007002040c060054400c0e0b400ca40649a2040c140424540795a00e0240780e225604030010b8400d40c0340c10f001844509021640f003517000c01035a82c001d4280c0c00c1c5400c0050360b8000c0a01c501d001e41d6034062a0301c2030344854110780090360040011a1280010044040c20381d20003017100101641040b204442a4500109990b00400c85007404140b001401d8012105041c180c00a8440100d4094000060000359442404c0c8000b5942c25900640d541803441035440815100007904110300340c0009031950403e52109800a2040b01601c20f0202c4d254005132400c10f00b55400000e90700680e40c030361400d40f020020340e1016101c940382032000e1b600c0c0b1400201d0f00c0c042c0703c0a40c2e0190040c0340e00900b05038400c0c010303241b01c08841d000c10040b1a1507410000c5003124203079030741d0700400d28050003c01e4501c00001d125105290040070540b0b4007100c19030413900c0c0842c840d2090140304c003100d0740c202180e403a8051415106100e43c0207103040c2d0058410031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 181497320 1250 181496070 181496083
    0x30605040515090109020901030f050a05011506170f07180503030a110f1c05070309080d05130f0b07241103060a050108010e220507030b010f0b1306081503011a0102 72
    0x180020317890b04003140010b80301c880c41281101d030444a050003103160f074104242044100f14004140c0d528103141c0e204108820000582604c60b03035174400800000420362440a03110a0300d40c0010b01c4900e41c000f441452159080748040801048c2801220340c0d18008249107401143c41c6001082550703200306c056100804c003c2140814210007460101e10140f55400c40141d01999041080400221032041c140118001d50080c000e80040f6000441441c4d001407003a040820101401803501800050700b035003001060003030b1407400301d02d01c0c98050584c1e10b050708920103a820201e0b241c440481c0501c1007000d0310845082064060f40e00b503072481e1800401c480d501190300040c0c1400003100042c0241d101016100c0d5101d407419a00802d00c0748207244d00301d0103040f9180010720500c500c420110400c114080c07024120f0345402000800d0075200c422505490084184003114280020750421002c0d106080007504000c50071f092002c2d200c440004242926a4069090007942000c41851b840b941d041091 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 181498570 1250 181497320 181497331
    0x50303270d02070504051f0303111e0604061d070524030709030c0504020708090409050a0c240e060a03050a020d0f0914030721170a050f07030b010c06050c04030605040515 75
    0x180c07e110034241e00f80c0031280c80f440c0405402c02c0040401e80e40b000c0300801841150b9401c140c11182c4806405000558404003110115455420321301c030303085a01c80280203510212404c00c09010258185000e100a06106405e46010010301144003003864101d000114041c01c01d43d030740c1d2020341c5d00314240f0b1110035089600c52401284100010400b0840c06411b950038128100c401107540001828510b1a0030424080a00442c40c04c1000090900000707081c0400c0d0010701d10310320071802c0c41e400140c0d9000301040c01c180d0048000c100c60b908651007580030b103038400045200141050896141d890454ac90000c40c6c260507aa03404003038062120381510030f004207203000025031415000760746411019070000900800180542130401703041c0c2c005c640505100b1030300740c1d0004244c6000c0c8c405001511094840c1f651501e015408100a14824080c950f0144010b0b1a42c00c079140050b50340800400008045081d0304006100100008115000349405140200000c1182800c56000c0401c1d03010b000e0701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 181499820 1250 181498570 181498591
    0xa080414060106050405040b1f0215010509130303150e010801060303020f030a090b0310030f0804060813030503010b09011803030807080109051512011517070e04050303270d0207050405 81
    0x4100f055480021030302602e40c242c501040c00d11020011501088804034580200c1404401130340d1803031b03030008540441c5160b014101e0281d903618400d2041ca07030300580d90680e40ea04040500d0002c0ba010303410083c031500e22040070510840e074410800205140c2a0030001c941c7e5110181007003415810400c031004000381002a61501c20141070103401001c4900ca0300765180004400035a42c5c150f14080da50003180c0180504100b4070840c0341c81d84c20350f80b140c000c160220b460440450807500da1000c030311005642c103458907403842e4240301c200461034021044c1c2c02d0411410211500200ca0030fa00c0d80c2d0300a5110751500802c40c24051006080888144c109a410b2440d1004103d40940395a00d11542d454043e1500b00100c681d0001031809404911205270f9050440080050302803102d065021007000c0140903030714884d48400440e1109032007510b003e800b60780140081004101d40d1103e546142c81d08201e043c1500001c0d00000d800c220303480d464040560040c4000300306d9400d1070f00400340e000c0990390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 181501070 1250 181499820 181499833
    0xf01151d01051309020112020304060b1318020913020607061a0603090a0609171306030b010e0303030f060f150a02060604021c09081606050103050f0c0d03080702120a080414 76
    0x10104046110b00404420700715190404c1d02e0659018000c407016145181c501559246800d0522001401420224070f002d041202e080d0111460340d40310303c00b1044030300044c107000c210454007041040341d4050703d43c0310500300300143c150050303543c4001842041c0c8aa00041900d03000103101001c443c030203840c5d29005541c20010045403c002040120585501c13043c002402502c0381000702821200820300d09610000280140b1141f480362222411101503030f4091082140d014011126152a841040d82661042c000b24105082d10400780d5071044000d0400290a00200300003000c00440100d2800c0ca03100001d0b85002880e810300031103500100c01c1d40c040d0b00c5c24001015410404018048011409035204100f404200380c2d6000c031181105102070b2031038100050b06100300101800e1004658500c251b40740c080401402040701881e400b0010302615062161b80c805841c0a8002400c400c11400b8916255107220106405054807015640d80c44c655843d203442c104207608209410146281d0000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 181502320 1250 181501070 181501079
    0x50601030e030d020d021e19050918190c120b010906050f2206120b04090b2802040e09060901091205090d08030f071b020102030a110f01151d01 63
    0x800c6610b102c02d440c100685d60400e161003400280240500351000c0c0540103050380d41500c0c0c003000350000000800b40003914080c0400240ca4610403034007800d81103000e50f01c8082c4124548081940d005010315001d510440300b5220b44000c07105601741c1c0d00c5c08036910885491055100344200000e0034000e08204003110708100c800f130030a0044044000c038001000400c4001c504c1c022080040d03400800764000d17441503c864000d0103090fa205030003481e8510b0b054100a43e4581070049000c40358024800440d152141c0e031000801004130070a502855250707585d4110b1500881c401040188010100f140081c100314101c9414603002910880d8280e04025074580415100355400404e000d090038019520b41c11a808034030030001841e00504080c002204000000b12030810fa03510070b0405503520031030380b40700e004000c0340c1c48040d500280c0140d10030b00507284454083c100f55110392a011b400c8031014010b10403828290b9810001850551010840400405074440e201001d560024144800c075981071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 181503570 1250 181502320 181502323
    0x1908040b130e0f09190609020315071103030c0d020c1e03090a06030e07090c020f07090203070201050705040311010302030a091e03080604060e0c030a0e030a030606020d110a031112120406050601030e 87
    0x400e4001c80e52a081706014401c00c5640e6010103007103503014003a660584150601c10024840407100300000c101caa54094001000c08411a8403a103030f840c4980c1e041440060b090b10003500190301000d81ca106000e0700c6034040c031003202041c12500b5500000c5a42d10240340078008544a140d0056082c0347c1480f00d240e141c180d011444070155203415500065060758100c013280f5200640b420b600c214001d035000418400c903660015485003825400900c02074403641000c5034144031b64400a046143c09202401c900d6210f41c0045d03400086040011a620200b0b840d0003e803c221a03410242c0ea054541d2407504042d04280101d41c00041218104901480e014003080c81e050024001c40e1021000400602e00c8003403507005240745c81d0108200c90300d07240c3c00007010700140010f0140001610849008848040c40f80200000b4130400c50041d20a0420030b42d020748090009111050181c01213401c0c0f5500c1d03401c20405002d160303001320b100203914101828403104440000c1c260a04150408440d800080b10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 181504820 1250 181503570 181503583
    0x213090204230a05120604060c05090109140a0b0c25050307050402030a020706020406090e010915170a15090314030903070b07110105040c0302040f06081908040b130e0f09 75
    0x4540b8100006010340340b0004604440ca41c001580c0b062000d012070326075801c0043e0302c6204611a450401194541d410280c07a2800b0700854540010b031504403c0c0054848103110f00d140384405400c54030a81d460303c0070f50300150040004081d00b80c1c8020710340600851580410714402650108001c0d0f5182400042600c0c1c0919028840c0215000408030754280101c1d411070b403011317820a0341107455a0312800d0043c1026080d102d01016031040381c0004c05c0d00d00c80d034403440301940c513500c034158880b9140010380842030a0780c403da0380250060101e6800890310388480140c89050010000a10914a14024001c250142c07800c4940d40350900800014081c000f00320f8203413903008180042c03140c2c0d90306400c468020070b00090040701d50814061004024840c41e0301010f4034421a410700034000000070700c1080b43c14030311401c10158072140d035089054080c4469810781c0d50041e030003030780341544a031808941903001d01d200c0d59415007106401c00049107005507898101e507851070107034010b08042c000c1584d00c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 181506070 1250 181504820 181504859
    0x921030732030f0a0e090a060807210609150c05041505040b0a200109030503060411210a1416030e0a03020601210506090604110f010503040b0c0c030d0213090204 71
    0x40c00140440100d015003040b003c0801c0046c507003500fa29180d02c0d008050312851052154510448e038012502c0340200f2400e80042c0c959030780002d94151142c413200007038000700809036000040e01c191a142141d82c0d0280405000607034980a94031454400b2b2848401c410305500b00030444107010a0200204107c00c544064500303107004c91480d01200b14800000e000e05207010380540c40c0042c01c03030401d60880302661080c8000c6600f0016103030842d243d44114410304100009482e900f05080403200368821885800c031002900c001010100346200031030000301a601d4409802500d602210501d51601504000b500c034074014007500310080d0b5020f5074a102c18020030b0558000c2060303008201d0840d0500c100c0d625082002c680043c1003200009450380c0c1c0a031801d4400c895480a08403881c140010904100340c810303900c851465079581c40b541085100501030200d401030420a04540180400180c5a00740c0d00f01401030b82e5036282480e01c079400c0c000f54400100c4900510080095941c0740d401c1910f01c1c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 181507320 1250 181506070 181506097
    0x30090d0207090f1d0105070201061403060f07021006140f060a080c0a030906020412020f1f03020c1603080a1107180b180703150801020708092103073203 67
    0x70b0f1590001d65002d440700d61044541050703200114084814150070003401340c051600204a100d4031380700c819289015402c2e00b207030141d04c410046446c8142818030180d00c08810700c15158480c4ea10701d075140549409a0200002d40c0301418101c041e0b1400b0034071101296000c549080c03609454282c081c0040310014a4020080800721389502c107103020740c01c0880420340c055401c5646036180d8805900500d03130a50309134081c4008540c41000c6050100519a001c60b40310444601c03000801d07402c8000e5400042000c00038001d0541c00b4856031101012000603500c100c07003c0c0d4a0703c03032107207009042d0b03030303005890301c40d04c1c3e02520041042d5a603078a90101596a9080c012940100401c0800c003600c95081458150700540030030015403591541c0540c0c070100c1004a004c070001d9031503400500f40c1c0a00e120261056804011181c01132500d410742040f210220b600e99000e08082c00d0f070150441e00b07c04003d80e600b01840f482565598159208480c1c40c048180c04480b0302c501a500107a42d03405004070100d2030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 181508570 1250 181507320 181507331
    0x10f140c0a05073f241b0e0f01090302041401150302090d02151207050a11031201270c03090204050a14010b0a050c07080703020a080303070c08030402010530090d020709 74
    0x2d084031600420307010790304411003565180c0702080140c408041c017a085040d69140c000f05003c01d00580710365000031829540d0312003a1344104801c00c01240d22a599190600c480000b0000058585028800b018005044410300c550303d08240f171030041011003040010548100075141b065900ea024116105405440308544003101c44515139640c4250a40303070030405a030a08016059902000070a10b0f50280e66030001130490040c941548c83c010141c62400308441d07540103000303001941c08105194035002050415070600a81044102c501c401d607400006525000d591095081c1405115080308049a003040702000010401c020403006006001c515040020740000543c4a00140c4410b00d2341b15040d20040e40e1f407812441d66a0032648400c9004001c1d01d280060481008815248900560f840d80361491074075907180c0020380e200810032414048d050095590b4034480480c4411030958180c2c000701c10840380448000c022800030007610803540720b12052100749901040c044125070b43c0140c0842c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 181509820 1250 181508570 181508669
    0x8060a050a18050705010f170f040602040509010e0402180402010e0f0325051305010f03080a03060e07080a0b0303090d0803040212030f03070e0105030c09010f140c0a0507 75
    0x180c540510289035542002c0014014460045891000c8901c00d03240c20002c010461829101001042c0003441c00300c2900000a00d040d4038096455882441000c00610f440d40300e1002410304502030300080b44540c100002c2004504140701c2078900d888030340700010706528142e40004e0050025144a0340909d4074181c60040d1b545003041400d85c0141404807802d001007140301c1112803101c8030710034248070710034044404d860f10850740300b03c41c1030b19026601e80c0c007a030341162503200c881d600003000c007000c1503600d081c0003411150b110230040c050700a0383e0b600d800c1400c0c115981416901506006031094104004c252500c0c0d40c0c5003034400041c1d900400d02926583c17140005002032038600314900040c00006406552030769140e0046218015940f5003000c03000e0010b0044450703000403154030074252020000044903600481080e49400842d1800410045042c0d031411850740003401601380c2680101e030440104502403101d00301070400c0b04443c0e0607030061900c0c2e0402ea2105000124600221040c0313000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 181511070 1250 181509820 181509841
    0x604060c02120d050c0105060a03020a0b0a020322031406060906130b0d080702360a020d0608030a0906030207081204030512071713050a060b030a1401060509070908060a05 75
    0x80b007160340e8016160f0001c00010081d101e580555144006546041c0002e000c038034101c800c0009503500a01505409400e04000d41c2c640d034030599441d010341c8024403078003190400e517651004028008043e05520f00b0f01e980340650700c14040c8100c03c04035030404000c00845450b00c0880e10391000084480c03500707034901c0219050040c00609019030300310070540014014004450010f110b5039101343d44041391811000f0507007030b161070f40c5001c071101205404110040448406111500301551000051821020268000868071a0b500000c003d40000c128450000c0c1c0101c881e100410300d0307040540c50103c1c0340c0c2d5924564404c1284c440c4008900c0e50100d42454417030000d4031704001c207023180c0011a003000075000e40559103512600040003c6800007860000a05440c90115a8084000c040c000015640c50f009408800400341e01441800301010109600084122076440d040b800001c5c074074100b2080c0045408010b00c10410b2289101c020002a44000f034620f0344042c1507000041c07030340c5070680d121 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 181512320 1250 181511070 181511089
    0xc130905060c030a181a0f0103050a021005090301181502040503060109020a050f0310080105011a16110315090606090412050f1611040515010903032003120a0c0e0604060c02 76
    0x2604566003090410080140c500f207040b001050401804103991f07118251004170f60000d000050490b00a00012401800c1017800310005a82c60704205041c80c8202d400300b400c48030380780d041c020448401c424a10511404001d00720503203108010552034a0705140c003082c1d5500062096140310359002408000d85480388040d29000c1c03210f181c21540e20300742540f82c5c40003c4114014510f040d443c03c0000686070314100041d002c02d45540b00400d040c43d400c9c00301c07040b80084c44c45c0143c071b00628828920340c00355001d00880c50b41207046c0d110081030b8107003950700c80d24001c1c008068600455100d800d00c80455400107e21740720800714a405d503540c0707050003401d01c1c490040150001781003c9401071101001301419500301c007070400b03441c100143d82e01e080080c4148032210a1050204080303840a2001c0303807142217900214900f0003800c007540c91f180c1094900d5a07120418052804c11000b05200710135445010b0b1600d0200e4510b403002d040018400015480d101e14441c0c4000d20070035043c80411912080c441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 181513570 1250 181512320 181512341
    0xa110604031202030301090c0e0d031b0b070c031b050a1b05040612110109030b150114030f181606111f0b030705010306290f0c0c130905060c030a 64
    0x22400b01d0700520801075035030f400a000d84524141402c083c455080d2181802401e80c0307030014007010789094252801d032100c40f9000b8a0061103407120403c030022070700d9960007a00901c9540c5c2d40d00703000c030710b03604004102c9056040d192040e100340010000100d030000800030905500202030350340c4a4191101200c1486e500c0d072100350443d08148000807150b4804907070311443c0e40240d401c607400c00901401101c0e01c60f4580801044802841c02040369045100b14802e0691818102104c0303414000f9804240b0780c004441c0380c002e101c1214100203070754542d01e03c20a460848000107002c1440801a03642024006000d2081081b001d0902c2c24011710040183d40141c81010400300c02c02441011090042c0c18841652800381c4982c1d080001c83d0351203485200100d80c849000958903421480130381023a281c20040c0e155524500b80181c40c00c0003030300302c000c281c15121070004041c4400f02409219050035602030600034103241645a002041010545581c02000d03540c0c442e96130b94800d81208014904500f1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 181514820 1250 181513570 181513583
    0x905070c0b04050a0b07110607050d0623040606050403030c030e040b10020109120509010215091203090708120f030612071802030603011b2c12010203070e03010203090a11060403 78
    0x24001445004134166150500800c840300c00c5d80e840e80d101f540c9000b40380d210b4070b80e5940f0200c00248101d2140000d4003014911150200301c00744e40d141e0080d40c500e610485442e2020b49900143c09a1030a40300d00c2004080c10304009040914684015040800e10003000e010300c000441d2501c1c155803075a1061071100c50050415a40b811110b10090080034140011101c0c00100e00c0e20705030b001d014100751030075074205034000c0540f04602000c502c0140b401034228501841440703007007481c1c1d82075000614403c2c40d221009100c100c1c0b800d59124034100d9410214401c0d00303000c100c04208142c041044039030000007507a00b020303140740c419001450044c0c0c41c0c0c40307041c9400e0109441c4a00b075199400071030007030708210003d000c0c0c0e03d10109400036030b09100c1c0c101408540e062a41e04400d100540d010451607621803840c084658015001c254110452500500a42d60010401000e1a080404002117480a600840c2113240242260b641d882c1440800f41520000b80034501c0640d0302c0100700ca01440d4001c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 181516070 1250 181514820 181514843
    0x15030c0108011e0504060e06100305010b0d0e030f04031a0609040209040f11040f0903110309090712060503100f050a050108030306010309020f03010f14070309150203150a06120b03070f0905070c 85
    0x8411105c801303002e444091081104070f0041c050312b4400d010b800d060391110720130503182c58200c0e581c2c500104100160f145540c0000c3c0042000e0381c6813100038000540c021410788440d0240c0d803d0411120754010110762154000e5011f02000d0f03140c14608503031040d8000002d000d400d04906080b00c801a03071000403507103c1d0400d000c0c0b25613010b40d0b42150034007a1003500c4603c00e00d800001c03110f80728001c490105410440c410300044070b49102c0c5a1741326001c1c551748400070300d031621403011034100001a642180c078540c559070014642d138550712030b0341e601c408942010042e80d41041000d58807440080c00032810580c0700c600c0b080c2956600c01e842121040024002c108599520700c00001410442c81c200501c60381550024410600030f018140600d540031504040b8060800b24010081d04042c1c0607400e000e5a8400880e902d4031140c800101424181d00c0d049901c0e00b07a06906070503a19294140790203500714560401c6100008103415003601d40000e800304032544c1e00341c400c5941c2c240d83e5030080c122a1030035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 181517320 1250 181516070 181516079
    0x7020901032604051005210906160c050705040b1c0609020a06020f03030402100c06050403080609160929040b0408010507032d060f0e15030c0108011e050406 69
    0x65401440c11070303814419520002da161400d01940034a11807180c110500000d0403a0b4148a84024040e641188090310840400b98600300160b2030100c45801c00ca512150904c1240c505a000b00c031003940e024603061610030141d50716076481391054801c250040341c0f50002d01c042c03540c9041e0007481a143d56548403400120a083c90070240264020076801100c030080e0200d00d051000ca400c40713110020800070740c695100d80d424424410031680720030080183c4050040c00042e102c0c019180168040d03903400620b414010100011544080e203000c2d03200e6200e010407200c050b04846920220340c1ca44985510303500b102c3d2110340c1d1000c003142c024210410009404603094044030090410703507142100800581d55503640c10303000c84141d0a000854503014a003507107400388030f001c0c5907541e610f0750600c01300c3c0c040d43d11140020300701c0882d006040044104800c00c410140f0005440301004011030040c4503407651480080e0a08106001d2880751034000041607000d00010080710000b0b00380580100581940e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 181518570 1250 181517320 181517333
    0x50d1101060503100906060609051c110904051b010203031b0f090d030801090c05090a0b03180303091b1f080406020f04030f02040e0706050901110c0a03050703020a080609070504020903030702090103 87
    0x171070204454482c58031602094552142c9040021340d000a072082c10360074032030102021b82c40444603007181e40b508180c2c54099a51102c0c50523034002c51250b0007e00000d11155000e0680e480a14055030455200740204000d50301310031048104000952401941e40c94807500229051080320382c199084003200e65800c00b00750380444454125008850100308501c40e50404480318460300800a40c0565814818458030203078800840e00084506156415620036040070b03811b40e002103072015199000000980b4a140e0f0390310040c3e40e181d50032595919400704206020420700d030b00700a450700700021040000c081216603411070703c4065581d05000d80f510b5803031030080c0040b09829001c90140b82402d0305400070060000300742e03060794259180c40741010f003032400441d0284102d0b80004010302c50781082008a444464034235000e18080c0009e4000f550450040c002c0c0c030001a48010b03141d51041b0100901c00b4004281c10040e14400c840160342d401700340c4000307803a50080f0000694421403000000080141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 181519820 1250 181518570 181518581
    0x1b01110f03070c120206040b0d0f060e0603150f0a051305010504080415020109030e0f01050d020309070e07020a0b0c070204061d04030905010521130b0703020c07090504050d110106050310 82
    0x440e2440004560310344aa00600c5650900c0c006d40015040c4418080882144041c0c041110b2440d00010403c50103000001a1001d03940111803203c000c000b44440d07802e003481301c0601800e0828422003213041910710f08002200080ac10b00800755100c001c50201c1e2800c2c0c404030040b0303400c28003c0c42035080600303000c5495031203031082d1a85d1041e8007811010031390060017000100ca8060b01d8a40d422040b074010300031864100c1002c141049010080700e813040c2c0c0799101540c0280a1600109041800d2800c01000300c0c03005808282990b000103c8540052850307603910368420f4451900703a8480c06030b84042005451240c03c018400b02c1c0300c45010244020165402d0302c5103001c1da0740d844403766070304019141c031b2103180404404138654210140059680441d4160803910b01e43d0380b01c03100419a1204402c8400230341e203800c006500000c80e2149178100300285d4015000038401003149080c1945d405985a03a950640c8003440802068004114420740c0b010008090280c20345a0340041010b00304001e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 181521070 1250 181519820 181519823
    0x10201110d1a0a0b0a2f07031101080603030f0d090b04030c0b28150803030f010e0a0606050301030609060f06081015050d03050d1e0509100507021b01110f0307 70
    0x41c50389510080d03914002c3c048604031141c1501952800d1410202140d010908143c078191401c0d401e42c10001600d4501040700d481c2c072403079010384000380c00d40c942030450060807811241003000d400140304456501200310f07245a507075940503e50303c442c0d6205160282200080207052107048030200400e040d0004c40307000d01584104103003029070751200540701c03000310660300a000100c01c140b0440c21151056024181d2100d045142c009010f56620740103140d0340c41203071081800c89485004021145100e942250001e0080c1c4052012500f441001421408140b1000d8001c503251319404050043e039078018001c1d40c9401009004086d03d03250415601c0c803000c4e0000f81c001d071034040d80040300000300303841d4425254020500e14006042e900c0c2200c154011110315810150740781d010014802c0244403002035030030124000700b281c1c40c10010702c1c1e041001da002004010303420b0100f0428000c2d80407030840640d0f40c103d032240b2076125000d40101d41c284407100c281c055501c60080c550140c81c2c2c00201404009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 181522320 1250 181521070 181521101
    0xb0d0602070605180606040c020307080703051e09030303040b0604091506060f0804110d03140307080709061b03051e0d020c0d0f0207230d060f0f02040e0103020906010201110d 77
    0x81d02c0b03503068141070a041e8110088280c200c170000c19141e26050b040240b20041d5481183d0400d0000c0c6c40b6500180e004200442c0410f100140543d110144188403070401100c5900103030070000c040000c40d441e48002000146010034070700001e0713a56520303540228036403504183c3c0c1c0c071801c2c01c01003402c10041c00c00f80101c0c0045181050310380e80385481129647c0c841d541c00340d00100500595418003d5440c001c01080303090280c50108054840d03d80d001541c170980c4071307a4070703242075040c81c1c0c1001e8019410b5400030340400501c08403c040100d00003909552807a4989001ca0781c40231a1101030408070041c0415003258480040e80403d039400c26009080280f54400540f445100c80c2c078000c2d1440300301941000096040b0352070401041614801459900b001d1041ca0203a0240010010320300b003204403c104c0b903540d81d840d140039000045114248050f449014114030b0315042c0518048054030500c030007442100d510380000c840741d1003034014000d00c1d1381450480362201d0241c86c0c3c8002400203001c103841034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 181523570 1250 181522320 181522331
    0x212010e1812180603041a0a0509060f06060d090501061802120115030b0a03050a050d0f051602040605030102030123030607120905070509010b0c01060909081b010b0d06020706 77
    0x1034100041c09410814104801405020140c0502903190340000075000d070640b182804048850711108015441035200b620300c40058030411025113020780000d00602da020340303417908021404200081c0b06400090003110020113540e29400150144240300d2520501402c01c1004420823405400c19002ea581c0301ea4a028020344045070f64040380180c03000b200c0d00c03000c140c0040118036103400741e0300a1070b004d0745008640140703400c1c042a50b9031200d81c0110381075445501c0c4c100510105000c440a84e00b00751a20020030190040020880d0040e003501c0c6141c40c410719289400c5540d82c4d44528010100500299141d41c0d40f101c0000b030741800301980b01c50384c4401c0c80710040309140105100d840b803011901c4142c0c03507102c1c44c0c42ca5030003440c43c900101c1b06403050b250301145a40c0d50b408000e008020030641b090b40c1c0c40c0b00788a11407c0d40d420b6400848201c2c1440303c0080003603c40000d607100b980040c05d55a90300345140100d14050500090210f40190008007640113103c4507400500406002c3e8500740701 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 181524820 1250 181523570 181523581
    0xe01021b01020a0804031d0d11101707050f071a1b030606030417090d0b09010f0e0a0b0702070f0f030308060f0a150c17040806060904080a0e060d0212010e 68
    0x382d10803c482d0100003a80c0b040050002801140200c0c8041800040c141c903421100c8086203030110100d4007903892810212a0064624100746d50025510291400b108a0100c01d2803240c4160307805441c58041c088041500c0ca9840c0000042e02d070310300d40207410422060034100015880c0b4100313803401c5034070b19840d400300c00c5d0001d20a801c403030041e180641940d10315551074071485170503401c400004085403810002c2c481e0951300ca54000c40380ea070141c46210060306000c090142140c14000040c54198101030501d1450702c00860110410303904091103050030703070780c01c0d0b0120304044140e00820a140c1102c1804546c404480c1020400e507807203502c0390143c0351100c0341080302c0340303407440c80c4c86900048c000303414060010651a0b035070141010b400c05500c04e90300c1d03503240a80754420040c400d290340e0340482c0c03c10210a0420a00760061400e417515446400c0685402c5000c1c4581a81e030024070410380c101d07801a4441004a541c0010824000c40d02c456003040e0a8000c55030a00c50070101c440c0c1200410f8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 181526070 1250 181524820 181524823
    0x11509060303080f0c0909060f090708150a03050a08070206040509040c05030d0801080319090503150901060603110a030b030703020d030f0201050c04060509011211030903120c070b01030609050f010e01021b 90
    0x9000c5e9110466290921351420100884d0000040100d0741082c0c50380205440ca07264109107500480054071480200e181000003104d01074080710540344114004039007000421004250307100a10780144010340d5070751881c00440e005108a40c8100e8005442d03000f00000e0008100c404402c0d52011001d441c6092071000044403109028002d96440e50010490300701031443c0c04010755101003050800d807107031075030b18170021b401d00c0d441d0076191001001c08420889650403e118907006011a8181006040c1058848245600443e00c07141d042c142d49049a980f00d1b0b400700000030013180e008040700f540300c0c80792a00912800b0161030703810240d800c020219011086810a8806650003070307490504060041d001110110590031000354030996444c07450303089001d45001103100c0e0012070004e5039140c1400b03001002041005250211419092010f0300000302e2440c0040d044942040c0045034800c001e04085082c890f50301c42086041d80303404803011301c080042d0040d144503400c104569058403002ea2121303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 181527320 1250 181526070 181526101
    0x70305060708071b061d072408011728030f020705010806041a040903091a031b0d0212071206050604080307061e0e0a06060b16060e01150906030308 65
    0x100081141c0300e00c0c0d1400d402480c81000c4a0600404011a15000802c031b10806e00c0c1080464032150b401c803690600c4445014061141c000c080c6115030071500c400c0c82c1e4000c14085041c0100040071010050b150103030401006003104100b5440000c17143c80004e00058085242d04c12401c802148a5801c1c003000c4500200d9580b00715207040e100c8140175580c1c441004020401544198036043d010149600700b03450b01d20548158030300c26200d10300d0031402c2c907000d00c8085807969020940303c0ad082041000802645c41000030f01641607040d17a44556414164201901626000ba03824103050010451405d43c40302c629040315980c0d50081000c2a20344050005502c01ea000710704903035004020500c000741541d4040101408904094210101c0d569a8a020303510480507940a640c0301482000a004c810700c078070002480d1242034503281541c07550107035800903904078000d004159550704041910400b90040c0c00d144c1d081c500120f05aa4991648200030310907400150001544500010281454801e03213 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 181528570 1250 181527320 181527331
    0x50f0a05160206070e01050d0e0a06150b37090e010b1806030402030708120408011a030d210e150606090618031002030a1422170c030c070305060708 65
    0x380041341d0320b1500503100d03802201c0c000c50401c101040035031a0303e8181d07c201110181d00402400070080d15050500594031124070080000c403800d8010400075a6200489641c80f156845503284007890482981000510440070810204401418110164410100416180503020f0500303c1e0b6212045c155181c002c44017000d245241054008c00b4625010000c8c5070f010380300800b01c500342920f500c0750038100141480030355a0268081002d0040580030f0107803004d020403404400d0360a081d20000656181d041c40b40c890180071500703410080259400e10010070800340b0311420702c030481640403829540d43c0402501e0245540d03d0021800721302e0710401311800c8841c0180003038100b0641080114045061942e100e80c1481201c3c2920121135150000d13510501070000001450f80020459105a00004280580280b50342601038400d050a040c04182c203608104144a804071200a81e0928407460a04014078800880c0350340018500103603000550b84a441514016100c3c8042034400c1081981c0f03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 181529820 1250 181528570 181528573
    0x501080c040905070f150306061b120201110f09040e0a171b0604060605010e09090d030c0203160b0702071215020711090708060a170705040e0f01050f0a051602 70
    0x203200003a141940050318001d00038016200f90310307525614500401c00903401840504507590801030b1664140c840c1000605080c1842c1c00b800c3c1440d5042c07804582c40d202c1c018510405201c82c14000e510075440b002a061400c40d02c40d039920840300240089400c407a14051041e811b005d07844c041000040f80b941c00140d4820b0300c481403044425039080e10b81d0844c3d2900c00d10000f100ca1703003441035541042a00c1c083d600441d0009100c604010005004840c6203800600401c039000c248540d403400007804050000c05481d00265a10614108900310301c10304142d4111002c4044804040c441c0030303944940a21201c5c0c08a44800b941c4c4d0001c20a2011210f802030000204000709440c15403540e0010980242320720720f003101022029001901c178440580e518000621514100085400c0503840800034103031000d9818240868405c000303a9855440c01054000c644070140108542c07400c002c507a110050b054020300061400401e8618180b204940d00c00a01d41070902003030040395080401c668540083d0b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 181531070 1250 181529820 181529833
    0x210201060b1e07050a030804020a0509070e01030b0a1d090613030903030e0d0624140d020d02060712081501030e0631030e090f011224020301080309040f050108 70
    0x4408441501100281030342c0c041003141c2d800040c81841340c035480502c82d031280e18250030640140003070b02c0385603040a0b00030f2490205004006400c6004030b034001b82c00740303004600258050080b03002915079a00c90890401c0c0320301000d19841c1000c0e14244299030140449019549411514111444481b00500130038007545080c000300e44940243c00782e065014108000d15443ca83da000121040c0c144622203440100c0b0040d20368001000356040109141d815001015508000140d103052000030001d1048806005910854880d9020b41d00510b4000030054249410380c00c000d07007c3e0004440c00611031500ca074081845600170b00c641d40c21890381e00000c10f042d5032062503404807091107203000760002d518041d500c2403000c00040c903810000d00c0303907035040404400f6900380114220083c1820850581030b600520110440e107004680942d0130000080401c50030700340750304100aa01e500000118000800031821050000040140703a1007520300b0000d40c103400a2040442d032080c007400321742c1c0d0401c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 181532320 1250 181531070 181531087
    0x201050f0c031c0b09060109061409040b1c03020f0706050f1b070f0e0109051b0a0e04050703050720060112020609040606030b09010b0f03041419210201060b 69
    0x3000507207146000351040341e25041c08a0b801594801c0707800340180c0d42c01d032248040c0245003050501141c00c46820300745611350a040c0300c806070515000c07803170101c291800030803581403641c0c5a4004025000000d041c0f91941d5200310003600b03007100000f5003540544114404141d40754000603403201110340a82c1d0700c0c3d05020805601e6516580b051210031500082100c07074150310102808080e00500d400480c800c0f110b0f140503c3d548100c0340580c44072040e5454042045031451019400340e0320b40c1040a0036560380c02d0604c800703882920310811402c3d0094901001c0114039501580000d000c0d1a01383c55055401e8441641560070880512008d911070f007040c801042000300c01c000d41c400c1140b0040a407424490003601041c221280395000344002a102e11408000d420f121a805000d001108606481e01d6130740e45030b08000d80700240c00280075400400f0103141c601410720941c11940303c0d80b8100500c3c02c40b80d0a000b0b56414000c0c0103482803110700214010450300500c00c1c0c0080701c2e4a28030752800c0c071085 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 181533570 1250 181532320 181532347
    0x303080c07140f06010f090504050c040b031237020c040b0d170301060e0a140105090402040b0a090503010e030c060c0703032310120201021b03011116060b0409020105 73
    0x50350049840044030b08040ca00c02c802803042c4852604090000c0455601d481610821462264003241015181106000c04140301207566001d5071026100031569143c1c9801080c5000d1401314101c952007404900d41303004540c00107001e060381c0300f90ba0895a090010ba5481600350b03100110940140c0c1c81143c44050b5070a281d00054800a0024102090426503840d070078005881000c0403200034400100500c5440e420422140b88188181c030700124007401e0001094002c01d68400bc581440800302c2d9420484e51a41c0456002d00030034800720f6240c1d8880710300030b041c0d0b5146001d420f02c03039402d0100322070000380000190351820394008000c0001e526111085402030740055803d030205512007120601c0000d0070400c115086140c40c4004400b4a82461800000307070b0350f604400407a88140880c000581c2e8000781c0007282c01150b1030b00b9146160f0042c000390042c403c085142e841000b001c10b000014980c0140941c00440c02070000b4040800344404000480720582c000a001c01d40070b01002e04c0c080300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 181534820 1250 181533570 181533577
    0x10e090c0d15030c17030301031b050409060227100e03010b0d21020106030809010807170c0a18030f0f030e09010e090d080c03190f05010b091005040303080c 69
    0x805514145804031119110050320340019004100c580002d40400030003450070701c3c00c4024660000010100c281a03104203850340303c103101c040c19040d0340e40c400306450361a01d45080024030000304100a50180b030325251010f90408541000e030203014003040c40461240803c116242a00200004448404a00b041da22101c0020120750190350391801d00000340c480e14131300020103000d01c00034101112180440c41c0082c4a032260300c4210f904000d410000517050030155080e41009080403505603a413580c5c1161140c5140a003010325440e07c5051241c10603003a401400341c1e080d1569941850441010310610941d0300d0700c40200200014a040808219040000c42d040e512a1030b200591072440c600040c1045e03403e800c00c07180c48901d00c0a2161108040001c00c41c19070840c10821414a42000400a9400010310440750302000303013201c0125450941c0144100007c8100410141d610b40b070003111540c001c90304a1b070190850301c00310010b06005209072001c80340e060781d4400c1c481c0c0da0035002c1e104c281c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 181536070 1250 181534820 181534831
    0x126070501030f090602040b040512030702010207170c0301050103120201150f05040903110304080d0e0418170403080d06080708150a02090d05010504050c01030c030b0306390910030b010e09 83
    0x9a48158000020f1011b000900080000c940415201ca041004024121418014104690303000300451030040c1d030040b5180d001c8039010702040b0030194000c0c0d122400c1c440c00215940e03041d480c24001208102107500014440003140e402041881d0080c500b0708130603840307400b42002c1d11070000402c0069280c42e400082c0311034820715002403162402107805146421582040c811a04003248a03455264812010220510101d406112540207811301d030340740e1408944094407140844a40c0b8540d00b11000440700115800100282d50b4510f10540000070301ea9401044800c3c013031101c0004480500080c8608101080002c02c541034503021018402584208241070300000d01c05035100200e41c00303102d0f8038401c9001d076029103518140b680004049511028000c2c00389071078229071404680340042d0b210352004181c5240d005d020034207001c020000070382c2d400c0d84404108401e41180781c0c0343c0d179102500003050240d0f030844032040b624000760190b80010780e410f0700207075802204a000d8604880c0c3c00d078001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 181537320 1250 181536070 181536101
    0x5031c030908070b01030201030b1f200307051c050c120c0a081c0605100903031d09040c09060902090f0f1306060c020a0e0702060f0702070b12012607050103 69
    0x30000c42da80e031519034110480035149100c160b1300400c02c0d960103000c0ca0340d0b0540200c440017144e802803c3e856003080c2080015808100300c1901e41e1008030010a07150700e071945101d044940b5800c1c60701e4900d5503030181d10601000c2000d059034154100f401641590a04181c613006071200700c00b0500300340d08680008029034214842d549400700440d007a08005c100e90041883d2281c000b140220122040c0c42c0168001390040784600404110f00394880c1903407058951516090a561400c402154007801440308140e510411050174002003104241c081012038144036420310a2540d9200401c0482c0100c103103854204d40010f00710a00c628058031100f100b94401809080200701d450146012940c403504040041406c010b01c40c000d616103d040d61004040d03143e01c8400c1c03803414900080d216000581040350000b007070004074000500a02200d800f41c480d100550362180c40300340540514450a01c240e2100c2d00310301c609d40d42030600d05c0384502c20a0071840010044c0c01e161200441c01489442c1c0303040c2c0390 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 181538570 1250 181537320 181537331
    0xc120d020601230a0303030b1002070e0601030f0207060c2106060903030c0303020c150109110403051e030d0e01020d0c0206070c020907090e131a040f020f041803031b0905031c03 78
    0x1076566403013101c0614003036600010085101001d0041c44014803491605540c04148204007112110591030b43c400f0082ca804902400c0035214200079004023400184802c5c1450407184403a40e2044901c004117800c060f801400740d00b890040021a0014060000014942d54040c40820b025491002071148a45001481d045490f20a1401c041c54200d045038100c507900010400e40c4010700580786c94400b80d00c1c02c2031a051460fa50507540b03a000c2076005954081411404e428007406206a038100043c0754011b102003004141c3c183d0003540300e801c85e903200918000e80c1103040c901c0022010b208400130303140da81e801010354080050300354009041508000a20b68042500c0c2e040d4644903006010b100c440b200404850702c0c0c4049203030030180e500301c41d4a1003d0b0400c40451484a2109503030ba030140c90401c54100502d0104010340207075080a01545001c0f20450101641a400140e81380c090950907043c402d84450300301c54104042c400d86a26030b00420300110780c3d00b000c2101e6142c04050b030800107031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 181539820 1250 181538570 181538639
    0x406141c0c0908030c0616030e0d0e1f1704020f0d08030a110901080115030906110909060f1503062403040506060604120813170c120d020601 62
    0x21060300004a0880c8030307100c040300105190044161006088600040d50400810b800e04d1a683d903802010321403040150b1041242c0b080c080c1c1d1051010001440c1a900c80362040710000d0404040300001e1405180307070032072075041401a0031440c03100c90000d6071400418210b000e000c50b01014058026640030200c80c0103081140c1d01c031071112024a10942c5055200d2600014090440b12801e0f2005d005c42d408110000c841d07031b4442d048906517101405000000400c20004400030110350400902482c5418840b00120f024100542a00c80c070840e40c0d00d0181d5601404d00010304944c0c0b501c180c109000e0144400580307c8900030350780c41480500181008031081c21881640546c0c8401582e98140000c2030209012083c040a503010720305072490784c5801c0c5000794460031000000c0c1c000d003400901080501c034400711440c4840c010594210708084010900c000c40c1e841d01410004140301b0362074a030b009102000301044802d12180c080d005005141e00c1c00000e10290044c0d2800b00a400035011001d80c2e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 181541070 1250 181539820 181539847
    0x51003060f06030e24010e041505010e150a060e0d11031207030f0309122601170f01050c030a0506120319030c08040b0a1104030512180114040614 64
    0x1402460306580114444c40210026030402c000b0a03206061320203521003403840180302121550440b101040d0100c03840d512414542130030b444001c410a2038a00b09000011284030b98007009004a440e00c082c45441c122200c1000304600c03562044e02c01045d4580b00b00c034a40d140416441c0c424600076122100354146480009040829a1758141d00050004ca00711061560080e01c0725102c0e000c44c141004043c00e151100300e00030404000903010850400102c0c0c072000c81280e514034035000d460421076900c1d61a80000440e034448141803004034800c00120200b031480500903c1c1c040c80807414118074580300c0015990140000401c0e403070b003084450611070a6048100b00410200502580c1c1c102a82850000103090b41c9a482c404030401440c00c00340004607000d00c1101d0740105c0030203400250084a4041d141107805140d0029125014a003800b5011104080c020040820280c00c7c005101500000544010030800001c0410b4002400240f0403035016814840015044904180c1404002c0b8080c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 181542320 1250 181541070 181541099
    0x20333280e0f0a06230c0304080310030b040507080f0106050d080d0213060507050c040e0613060b0604030602030f0601090605040b1305060315041a030c0108060f060316020c06090a05100306 83
    0xc403820380c2e40c0d820107118821003042508582c140c8a0314111746042410444a141c003003d0300140c10620000041707100280307043c40041c02568007400600243c030349824551b448241d030303100303486590003a00404034200d4010b214410030354074014500030304121542c13122544c54120242600015a00700008060158040080402040309a0300d09948100e03902c0c03d01d0811641c210040d00550400c1400c004022010809541c4070500042114201d600750800d90081c201a04456821000c0064044140442600114030134009800140443d444080044402081c103101c0c42c1c0002d4018031003480707031007407090041c44103418169412400c151200005859540241c0d560280c0d490000e02c514542e05240c0502030a013417103c8110080b00300c0b2180071a46400d0386c07603009410441441d0000c0c0a582d9208800d00c2801d40c040c00594032894140640e01ca05100707081c4040251190710b10a681c1840c1c203c044841009020f0500071400c0c2c41c01d000c8c4001004000b541c08245511b45002045000715003950 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 181543570 1250 181542320 181542323
    0x3111006080703120f0f0503060409080d0e010501080c03060402090c1c02040509100f120201050c06090c0108090a0201090303031107060c0806010e0402070816020333280e0f0a 77
    0x2910b40b42d4078514150701d05183c2d103020b40f0b040c008102201802250000ca0604441242d4240160313039507100f20014008140035503005140010100300b40d030340b0000d01e5200c11011800c6200070001c5980f9110341c00e642d5024940e2450381980094000360060510100e055000b106886074036051104401d4403071085a8500281455607134003042c1000140743c1184c900d9085480c0c030b440140406d003849001000c581d07541c02040c4200f41d0b805040c004591140781180c208000d40c0080e10602d0070441103e6488015421090340000e2049011410003000840c8a00c5004d5058442d0a21b0507c0c41e130301035002c1c0c0148a29002c03820f03401d00c03e01c804a40341d400383d100348030070030758450007030f40340400025080b62050070000e40540d2041c8021130008500b1022600c61513003860a03001c0590700c03440040c2ca4a442ea11701250091511100c0b0400b13204071040600d581248a80c5010706a594000c2c910301030801c40c140f8100c0c029824040c03034185c00241c0c1c0700e0401c024010303054800170051454854a0011140c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 181544820 1250 181543570 181543573
    0x5010e0c01030606030b0306060f1305150f010801060f08040303091b06030524060706060b04080607030609020313110a0f0b0309010e0307080711010903021e01020c03030306030a0311100608 83
    0xa00c690103680c50301c5901e002d0200c60508020b240c1d40c0321302181c2d8400700204554040c03000c026002c0c0003940d07949680d00d050104588107000500d08145403082c0b4400b18000700b809030024104c00308031503005d0325099051700c40b1076039698446480c0050848a40c24060002d50601d55210010008144921402040f1201c1c3c000c0340c018103803908100500711a40180915045c0c880d5201c218000c5c2101ca9030b07030340108001c6840d03a4a0b4503140c14004001c001c698000c21413102c0000b0300188946000c90550712a9841c1d80b4104259650392281c142a0320044450629101d40d0760551000600c66007591210a94043d01004216480c0c041c511031a00e100e801c43d03034003448040200002c1d01024080ea400c080c0c1e000e005182000925074418031203014042000b40700c0c1220b101600541c0e4402c040702c2d4000e6400820003000300c11034500701d048400c200408640180154421452141400000c8900540d0041d008246220302d6850894620211824600443c01245070043c10003c2c0350281c000035140903070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 181546070 1250 181544820 181544833
    0x5040f0b28140601020105010b090402070c050a0f0303170705090402030405010f0c050403020a051f1b0804030809100804230c03010f0b1801030314030601110105040302071706040507050f0d05010e 86
    0x1002440358000041403c0e046a050074018041041000c1c00d42e9080344003541e002d270300e81074a0710302140c401035690882500444100c2c000641e05601c8410401140e0103502c03900c864840500090301100e4041320f001010481c208021081400c05a0056511501882c000070f821926804044240c44d01d4416803c001280440c0610551420501c3d100007001c040b0703040050310846a0a10300c0224801612009020001100231001e000300041c281d11650310440c02a03a59459280151407900b0090320503000711004411182c00318081d9805034010b41d08001d141050030f0a1007031803c100b6511a108551078003a0490a1050362001d0080a01c0303140720103808200840c1c22410703c811520720f0420901008001e0004001081d0481c1040302d4054040004540e01e0781c40f000141c880300441c82c45040729601e000200300c249035000c10b0800c1642e4905000100d00c000c44c924441da20101550007a0840e0881c200030000e0f881d1031940f68411010161600303e60620300d80301c0320700f101d0001244016640110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 181547320 1250 181546070 181546091
    0x1017060126010525110a11370501030e070e0601020a020a0e04030e0118031b0b07032a02010909021e0708040501080f0403080601081b0f090f0405040f0b28 68
    0x841e14100341001a180c50050061450400c955502e100140034100d810741801c40c41403501d4201d0180700c00350400020710044823191800c51110982d540006859450605001c03810358400d02070002d502034500d00510f0901d051151508040e40042e010b03030306500c6010b0400c0b00580f1801c450400520034070383c441c4080d20741414080d05070ba0100c407026040041ea06200381134040400e2001c000d0303035080904510300c000388445080c405d1400341c0200307080d00404030703d0900705a40801100c2d4642c03401e004901c2c0198400708010b0480c80c88070300087c04544204024490301c411a805090095603481d80c000c00f180004242d041140c2c820042030f6030b10400000e041c0020750b005520140c01c9410910844c0040c0380c1342d03e00401c01c10010f070159041101450104034016482c41d00052000718000700301da902d00b12040103c20580c411942139004803c9405c0d100ca4916061013458400c64001c080200c4031103090b540e041a42900030b002c0211000042e0003516400401410204444181040000c048020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 181548570 1250 181547320 181547371
    0x12040503010516090e0a14040503030601030c02030c10050c0904110a0f0507110603090c0a120506060a15081308071a060405090d1101020903120310170601260105 71
    0x2444403c208803080070088146500058220868044500200c4651166081138000d403038224078000005988209000a00c00007000950148000740c034104404030900c24141c0c1c907801020103410481e0400c004510081c1c0250304856804415440340743d161412080c000b40440c0c2c040010784071040804180410165008010101608000c0c101141841041c2d5290284e0140008101740030b010048046600c0810811104400b410000c0c14a086c160f100c0c07642c071001107000001500c0610980303000c40d00608000800740203444413120106074101c0c0c1200c041c1e4281c03402822a03040c60100c0c0d0004000314665001a00310944a4118588580a4140c03a0140840c1c040d04041c4900e180801f0300200c030400241c0c081c088001410f04141004d452001c3c10b0080c010140e9103909802040e040c41c40b0841c82000070751184004913260004d4a4640a1600e00d8403800c0c082c450040d48008014040c0340041041c20b210343d480000e1001d0030300c0119040c5400d591080d00c0b1001065104a84001038001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 181549820 1250 181548570 181548581
    0x24090414090a150603080f090415090e010c0305040503220e040503033403180b010f0510020d2106030501021204030e0f0607020d08070515060f010e0924031204050301 73
    0x203401d200b8070013142541c0341d4052a2043e107441c00ca0340030780062645e0180d2500d8220aa500d8007401000500c1995242094041d01c650b07030f8481c049503e4865000f00141c0244255401560000b00640c01c0000008041c00060071140185d045c004505a000800110218840d4495489480616101e082913120112405400ca11102c0030110042650b0702011204d02c80040741981031030b01107904040300e20341451003030001ca8080c0105070201c002042800b4111000307030846600ba1480038040e88940000c03a190070740f10100b940040c0c1103c1641105c20418500390301484100c1d0070000d40e0640d60350702c2ca03003240c1c0720003070800440c81c0d4013081100741034001c44140c4050800755541c5040652041c00150302d48510701c2c1c000d200b0301c14000040140300001040d540d0180e030207812142440ca000004544400003221f0032482241c15032030100310365120303c42480006001030020500c9885440302c501c039800700b0114042a030290124500d80030354080001c2d03c218071218010558a5041c8802d02d400c0d41c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 181551070 1250 181549820 181549853
    0x613021209031317150c0c012d1130131401050106050a050c0304080d17060418020409030309050d0f170115230d140624090414090a 58
    0x10681d18403201e04c2c95003c2208900116083d16440c15655240d4400307802d409822540d150561901c58a03c174015004800b990221003140102051122400c0304103007601c3d030001c1403610300603080c4010014449003444a03044c800d110441090300c01c0b19030b601032075881403c41c0d4a001100c904025482400100c080ca41803248460b4006d00c81c0358100707180506144202c039502d004104002030500c1c00040d0a2060710050204402995004031107030000070043c440d800300b0780940700101000304036a450684506846a00d80503041c00d0b01403156000c200003443c10510540506403a0303a07075480000c00c140f01e05000c0c400b46845688010b0380040700103115400540e46440003900a5005005e00c408811130111550380d0703441c01c0444414650030913014130308090402540c0d00004540001d80d12501d40040080745400c3c00c03c1006540d52400704440e0703110503000b052421485170003d82e0070324200001041c074050081e0010075000c10f0f05040004405080b1082d07001900840300240400110b0a100200903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 181552320 1250 181551070 181551089
    0x304090513020f0d39030804060f020705010c02090a090213020c010c0203090d081e0d06061101022a032104030e030d080a02070c050d050a031b030806130212090313 72
    0x801a43d40c41780203000880300b8008024103411050b00750b1030380f2120b140c903240d0003260b4000a03180da6850040500d030028012400814440708051601900c0050103004a84050307458001e06e031030a0b020700010300d80140c440d1904036221041c14016071607184a50301030862200300103a480130410407890840f0100a294400c54108202045055a80010070304d69242c12140c2a5074030310702c0002c0400840384480803419035600100384940d61a0751039201c00c08464950321927924004000c4400e134201d00c94010030030001c103100300c8005411210204110304400928080300c1c41c0c120006221080320001e1542c0080d9030701e042c0100020541c0c841c685000c151000d500610380349801d45005440c10000624810220340c1c045449000c5c8410a2088402414058005090030510f0709085850300f590300c0d000d4010600502c141003440412245030540d164142c3c4d19401d1544a100800500741c0041ea11b8240d080e4080c089820140b90880595009980940040d80d90300704144017040c55605035806810358 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 181553570 1250 181552320 181552339
    0x70b04030506061302071a010302090109110a120b1e0f030303040b040b090a020a08030c011d0c1201060e0c0301080f0d080612011407020304060206060427050304090513020f 76
    0x301c0016402d50400e4089a803d6028125486a00b000780101480034240d030594020030403d915000d03081700c5c180d0f40203403500700060b0317225038004007510006908940090400c0015035440303880760010015240360058042022b4401c5000100d026100c3d0420816420680c2540841458900000580244290091800d518082d200c0d241c2128000344043e11a0301d010307000400300c54080c0910000d881e8020020055140c481443d00c3d50f035005115a0707034544d813905c40c1e4444500c0c0d514182202503641800100300c140b030188280401c010924030f41188a648910f4041050044030f20050305c1504801020743e182c1d07150083e000c0c41c0c01034502e032618158100c80c502c549156408007409510410075180c190184440c2c100d541e00610789401e20040a8505806000c22164088000c004542180d401c0f15901e445d01010402140c8124080500714900f40c844a2000000010070a007102c0c000c00a50782032513601c3e44510240c5900b2502c9040480004003468118588032650f58007004058841481 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 181554820 1250 181553570 181553573
    0x10902090105010c082208060604060821120a020705120301050f040b031009060f0b190603090302070f060915020c0d02090c0903150103120f02030a080a02090d03020f070b0403 77
    0x1403818020706040290354000303102800800700403501203214503261400c04580c18032080540c14030500450004c1d00034200410074030300d407071b001704415100c000c0050010421500d0441d02d5190b003920b0303003500310716091004c0b54902c0e494012452007000e440b00056a100f04038641142040783c4c40ba084a00d0440a00060226440b000501e14640070165070000b86030b240a8006840d144c03801820101160605002070f0401c18140c07c00c02c402c192004090140e01d40710420041901780d1001e00962080c0b0728002001445e00c0380d000f04007814024010348160b40d448981030500344009402c0b88004c03802d0200b00708842501e044d0700150303640140c406041100b00742c0d0300203207640c41000f0010748030381d01c09800300f104124043c0c11a200c042001342154610040c0f1014580b80c46024802074801074141c0c020005071f240038841d440301020a990103146450406201503d9101d005407461802580c2441010081d80360008045146400f03030700100510402c01c042d80b0324002d201c0d0003080c95540103020420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 181556070 1250 181554820 181554829
    0x2101a010f0c03080609060112050a150b0c03030a020906040f030c0807090b061602130c03051803030c03041b030c0305060a06080c03030f0c0a0602030c030f06010509010503070c020315091e010902 86
    0x150000c1d803c45191b005030b125400103d0700b603210b000c00b600d1024545811701602c0d40c5c565005020841e0110704244a46940c5c2041401900849005004a4004000140010409600070800c80c00000d04043c02c01d82c8951b03d0300301d40340c80384e041180d01c10f44040b014400302d41c080191070014088600c0500c90483c031000842c20500410550702c2100501424010840d42d0f0f405a02e684001c172030700200800c2c41000d80080140100343c8200c001c00400d0803c6c560b0140300881280c0c82040e10541407480c507250f0355101c2d51003e035107801290700046210404800914030203902001140624000c0000e802d108010740211070040d40900c00700e03404091007801903200401030f01c0b4a0814040c807591a6006815011304150403008014039041c400406c02c24040c00b40d8010714042c150f49405104955a101c0043d80d1920030043c40d103001c90380600002e0403c0384550324402c845880502503c50f030700c01420f07a10303004140c03c0e14240c4583e00f110b0940d0328103021108070020201c103500000d00c00e0340d11540108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 181557320 1250 181556070 181556087
    0xc06150a0303080a061e140a08060106120e2d06060a0513020f0f040f0e01060c020418050d050a021644030406091215050702101a010f0c03 61
    0x40a210b95840051036001603075202ea0000e204106800401b59998002d0302040c5156003d81107110302c444030a040d0724101a20f4000960b00807c0091a26909005040d501c081c0c42d118081074080d1103016881105000b4403c0c2084040c0a010501c2c0540300301e199051206070313041403c0c180e544408100542c9640300300348c02d03045800c00e45020010a0307000c105200603205080c2d0010390751400041c0421451211002030003110b032129455a10036485503807180c0c0d010428030031840041e21030361107440549815030000390b14121130031248000c404999602810040b071f04800a0110300e002c2090318040360144840c144045113111281e880600b005030600103808440c10160006155807030100740e60060180304040c40e488902d2a08034058040e40e40ba58030380c068081e2500103a94001d000035130301c03410780f100c036071240d4841540c441c081c0e0500c0c00d401c02000018104000c604c20a03900c0c0e003d12200380b080440717101d1004014400754034030360700240a0b20500700f80c030300802101040000101c0d9208290 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 181558570 1250 181557320 181557323
    0x306010c0305030a061a0703090b0a0e040b0d050d18050d0201082a12040614010b0a030504020f0a0f03050105071106070e0d120e0102010501080313050108100305010603080c06150a03 80
    0x70540f00d4495000c500000d00c426003000000504501c1c480d0140c18102000c1c18280d4400d550752442e05481d03405010030b9005d0b444a001c0401c0040074185424a825000740405a4018005020059aa88620785815142d0301160046810000081c114a4495055a02801c02502c03842e100b10420343c0001c0061000424101c0180455201d0b884030841c1b000e194040d00c4505008140c95545101201c1111907041e501115060706e0050415001c5001000d40c0d8101c4005440c21418003134a46015006400010b20403607100310441c9407102d180d598418903a014010345c0b90840402411440d002d0308448000d0009400e202c0908403580740c1d104d00040c400c0e03001c00c640ca406084501044082015489400802404030201d0500b07801b955900c1086042e00410981c020b000603680c0c2c010b815120300c0b0752205050b148030001030a10855006200094002c03a21845508106550b6103406c0d08441158004a882a500160420582004000d010b81014020030911054103e1400099142e0380d503210 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 181559820 1250 181558570 181558577
    0x3060a060509060f09060c0109050f19030504060f020c090915060d0f24050a0c1b0209160e180603101515030b09010806091203040b06011b06060803120603030306010c03 74
    0x9000000e074860000b47c640f510501c81c001d0002807036628100761070709181c20100e40d2034441c0450621844c820487c81c901210b40603100daa150600b89001100c1e40c1e1896100c07807056220382c108021030f81e10341c2d6032694402c80b21000078010281441ea0070840100d4041e086502c07440e401070794580498141540340710102c1e4049500340a0b00a01e003507544402c80c0492900d90082c0c03608040000394085900300481b03221b8650f4943e0360010806031150300003031406074040d41100c0c06000103440da101e290004043e0048a003889026414541c0c0081e880641042c200121b9280703d8050001c1410100a11034608600010500c10805a00d10440c50741e81c10380300d10703003500b00c0714140e90007404d009510035050500054a1951503603100c0344001d075954010b56580745284205440c0b1780c045641201540c2c01294082c0418400d0707101d060044840c504180c2412000144031000d03140001c0329031003680c0040a842001c0c2d41c855015070142045100c0080610b4005d8004000300310f1140ea0222450440b941d00d400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 181561070 1250 181559820 181559827
    0xf20100c090308130f0e1e091504060608010e07121115030a050f15061b030c0a050705010f0c150c0e03010905010212090a02010f081b030c03060a060509060f 69
    0x80c007180d0328145030b400905908400038001002141c040c102c0700951300c0e440041000c0030754a10405210701c0c811242000c80101941c0d004520602c101850b40d0444159821125030b0800c1d46080c8010720002d9408941243c0d5807c4200316241c4203004a100c46078042020340a01d07480c12850721000e042e0304138010701600684002e46019600c00d60280c4044440041070b0b51289025254603004020660310707682c80a5010000402498402d01d01401c480000b038069418840d02028016080122608041c9107000c1804000e20214040100d818050300400c001c082551a0500150402c91510501010441c80d0b02c0d9450101da140703542001580e1440d01c00203090f6030105011518801c1d00c03092140d01d54204100d400901005401400c049400d01c00c0000441d00c80e5029a0340d00c4002180082c0030031066407000ba40d00d401f54246951202c0c1c1e9400c00705c0906801c01d01c40107994821244000da01e4004400e000340b5091486000d8003619103820058030b058410f4000404a028000301a5080000007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 181562320 1250 181561070 181561091
    0x20f22050703020f040612140106140309030c1f0b0a1a09010903060e010e06062709150f010617090303010510030b030d17150d08030601020a0c060f2010 67
    0x1d0f81100c6103442042459070301c46480e10700007040d849a203808050300d04d00700050000c658a01c40c03800c41c100c1e201a2503408825650340c5192010741c0006101aa29010074825401192000e1050514141d614213240d40807218180e04142120220101140900f044070401e110600b1400040c5400454410a50751142e601000490b08221399405c024080d82c00d10f54106800302c015009288080312000c1901c01ca641d03200140141081c2103101e0014042c41e403080111030100c07a074480c6821404035425501d03408030f42c02c40e8403440002030721644d80c8110008010400c09600078040540f494511580200c40c0c01d00c1c00c00c42d9079901041c005d203440391044620900816000e0781c810092244040c0980d00c2e00c08440c8405010601007607544140e21042c0000100b803408240003402c1c0d16030000740f034141018540d4641d8240c0d9040202114154030600e4210b40210f101444000004c000036900c482c524040d4002c0146514400b03000e042520745025101d00103841d000c54144014102c803000040c40c0e6810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 181563570 1250 181562320 181562327
    0x10303020a030c210207170a021e0a17030405120615010e010c051e0730030c0f060c030c05120f07032c120307020c040902040f020a0c020f220507 64
    0x1c4c44180c0a01e4429144210119031300810010700300d40002c0c4c64100181c12030b240441d29515000c030001c0d4001070321031030203041d040c90341c07070070001001c01406506109465003200d03107450b224140000c4c065440460100218600f06500300c510400c140040d04850070f1007440c0c1992000e02c800b4450521030310181c0e40c901d59104810280c0b20300d40081c00c81e6203000915040050001c0341d00b600700041c0c05080404503c7c51301c00319000c0d40090800888070000700c14419400c040c018002000c03403c10030001c00c5103020504a00d030980d0164016032001442040801018084943c0c0b0781c8080e0a202040c0a150400c09010a080d94000c01d0801001541d5940150440c000c00042c190420803039040c1c1d085055449074804400111900c041c00c0b211a5840d0ba200c543c0640012102100180c0c400e90080000741080d82200070704a00c003074804156980001c684100741d80181e49820009194580340b0300a51400e0000804011010381e0f50015100d80c61704a03078488407000514a048580303450119961740d21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 181564820 1250 181563570 181563593
    0x527010e030a030c020406080c1f02010f0c050a0201050f09030a030f0e01091a130c121b090b18010e01051203190507020907030e060115021c030501030b0f010303020a030c 75
    0x60003020b640320485207240103480129050000da000380d11348038000c20742503c0042d85900100000b040803010100501401801207441112401155296401c0744a49a96402001d100700400c0d1140f0b5100e881b007800090864034028426212a81c01e04140f04d801c00d008001c590f00030030689008641011021003201c05808003da09500b59881c0589920a000200820ba0100c0800c03e030505625100c2004000380420344030b6001d0666040c1000401070304001d03800050016224004804c040d444000c40085110041d07402100d072a40c036445140f8a46c0382210700003502000512240125504007480200e42d20014083c4a0040310500d000c0c42c440c005c104159460700035034280d1084009800d0100814941020340304a020b0388100002c40e0341e9600900039082107900c0ca8001700f00f00c3c1e180008441d1310028000100080d070244500c5010f104c000170805c01042031070740d1400f0030554034629140a0315440100b21200d00b002c0c210042c400030f5400700e250085140c15207401d02200a0b00d00f8554201003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 181566070 1250 181564820 181564847
    0x80403020a0801020702011d030706030e1501060f020d021506010813081303060506030f060606160501020f0c120415080c0d090b0f10050303030c030405010b0306040c15052701 77
    0x450380c2030020794000150000c20100d803007a032350b840041d0320480e1510420804440702581c16007010200780205c41c071903800051340030010400c40701c8268884140e02c550b40000c0c0c08c100c000841030b005440119404011102d001411403000f05204040504481008540501242d0402900e44d0100c2ca81d0030500310240c4510b40c02210003941c420704078603280126807141c40219511810900010050b28004c103801d80c06103000d1001e0801961400100112544007400452280d002c1004080205a00744050001e0340080d10450f541d0f05003504900d131070301c500e100d001915070740b040109000c04001e65003d40ca0900c0a0704041d403007a145c2c0440e20825004940e00d24004516051068090140c03c28426004000b18040010644c540901c58058189907000c0c66805610410100b4480b809000c01158014010800022500c82d0301c0d00103420003c041d602502da00517050b07030510402d4003010340703000e51002d00d0420b40c3c900b01210b000040002c1d01c000c4002c0d568030030501c0608299016410400002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 181567320 1250 181566070 181566079
    0xb0a050a0902030405010507110a02010c051f1416120b130c08041109060d0807020a0305061305120301060806040b0a080d03020d050f0603031b150103060c03050a060302150708040302 80
    0x81d01c55a80400940003102c0a030340307943c00c0c0000320f044640500f5200200140c81000b8201d1118150015503803c0f441c4041240c8900c1103070003444024441c45404400c01500302c0300842c0e141c1946901c90601c02d005443c400202d002c4618103c8410340101e9060303021003213020041030911130800090b0118040400c41140c040c14440b45040b00350b400441184030354400c0005150800c0031409001010100700c54140c0c000b1644107210001c80c5080d1b010340070752480144041d11042d2260f6995003011420741c0c404c14100001c40664007041030034048408020202001ca40c11b66140030b4008000036000303090980a10f83ea03800090303207034450300d020202034080901154003e0b024040c00500950000c3d070960121031a0001141c1480f03019154140a130344010019070806203200240920f540300072640b06101c4c8509105611100d91250686000750f00908001075010b008010140580e031000b800d210700c8070325005c1c040c40180e8a2518000c204102c12401d551951031034035100440744160780000c0d600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 181568570 1250 181567320 181567339
    0x30705100e061902012031080c1c0308010e07030921030e06010807030209061c0609030306050306040c03080a020c06031501020c031603061a040f050603120a05030a0b0a05 75
    0xa40f120102c0550007001141d000700154214501c000d04290136002c4c0210303883d5410420144544414442d689103c82000803105c84071008240817181e0840f42d41c441c17100c2e900000082d0345280fa20008102c821a541500d00343c900c80166802080180d0501803460041d55003008180040d20980c00048465400780d000400440c1000c0c2010000c103255914070000707403c1c0301c40035642c081c000c9007d504a4844000030b18074507041d5401c1001d0100001c044070f0b001950504150310b08090703a8606520140034050014070b0610070f003001000d8405076081a80a5405401030000140c0074580503021250407aa00c00e4a442c1c085000720b060500000c007003179101c1d00100138040c100c212280c2c00e0507000d10176000c44094000300700c03d16840c1c9106119012145000900401c0030451f036801100d04411208540411044601d0005080b102c1258038013000e940d0380c5081040909040103020075040e1010f1085081214012005040e4030004040c000b0464686da0300c0341964803404050000741a0013405101d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 181569820 1250 181568570 181568587
    0x250302011b0204140906131e0f080301030c03020a15051204151e0f06120602090a0506120621100216080c0a030806010806010c0f0c09150302040605030c030705100e06 73
    0x4c5030300e003c0d42c00030035900030b510100705406c5402c5102d0f500f0310b902c02005907121525502e0381c0c02481481d0303401da4a00e800056100d000400314001103010318400c81101c402c003400c40c01808241e00c01ca820000360b0a0548101ca003049401c44151040c0006028204819541d14a022038210204200100c12715003014400c4800100c0c43d625a0340041d800c0d0300821000343c14010f041c0645620f8861001b42c03410801080e00842c449400920300c0d5040600a182d51940e1200800ca007540400418448465408103200c200e01d01818200341040e110b50f02041401007061000303488000180600005e00e0b80000c107013050881d440041b49504c0e82100394140c8805104014948808401d0750480001c2c0420300042c50079800380752200c0c000e00781a505c00103440d000d03689000c040d01d28200151510f0000100c001007600d100c0c0a039907107409807074800c210902e05e9031042c003040c1d070702d59007019100c3d400004851855460000c0c0500880b00200c0e020f0b0303119000a00140c9049181151060300460000765a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 181571070 1250 181569820 181569851
    0xd0b04170f071103030703090b21010e06040c0807050306060d112b060803091201140403090503070501020a0b06100c051204031703060102060a05090102041205010e250302011b0204 79
    0x2c03240a840f080320320788000030800d038991213192002000706003160400d1001503203031f07006890420003400742c150140d1001c8040c605802d00986c00700c0c40442c90300e01002040c1c1001e000d01d068111007400c10b4007240c24203843c0035016000c0204a0f5024030008140403d02149039008100500480b18a1503070300c0f042455140c84c0c084030200c1920314041e005a141c01100244e1140e14110303034800d4051800d18010800300901c800301c103205003410750348a00d48842502010710b40705000d14401e07215542030314605021b01d0b0030700183d07a00c543c0c1590007074480c18000c034000c400c00c681d02003c00c5a40204982101e0020342e90304a00140180651049800d800c5600102000400c00e0301e02526101a4403880080414241d22044079020300680140010804004098100c6034109000c1c900250520740c851414203011240742e803040d25a0303912003060900c101020300c8a0300741010000040a00000480c2004081c04098031009040000060711f80d903c00c08400c80071008583d00070428000a0070484059 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 181572320 1250 181571070 181571077
    0x122e052a1605061e0c0f0a030b10020d090f060801030f05010e070303080f18100c090b0706021b0102030732030a0c02010501060e0a050f060c03030c0301061d0d0b04170f 74
    0x1607245034104484d2942c0649600b15540b09800c4481c0c803510300090fa01000465411001500d82455202e1144415a540341451400c102d02c3c1039000300708000074920010201d080300d50080d40c0c42c242818007400300541c0081c07050306507a00800b03d07c1d1683d2161070b000b07005110b5660b440c401030003804c00110800d68860710050164090110013645500c9100c03c14514103000d04402c100395100070a00c9400300c103180c000c14410105030500350511955400c4560442d4031801089501d25800900340c5c64501181c0061840501c3e050300860079440c18002c0680500c44041c640c0929440c481e00d04100210b21141c04605034018100d031a4690138801100d50207400c5520592004d5401c020004c102c041c030641300e02807031100040040d5402c42c0303418103120001c0c45001010350800410803008542c500c0410046004820040d841a56507241120003030440d15003409000007044c0d101e5070142e240da143d60b01e000c030040e08004102c9007603ea40c541030380e0a00c3d002550045014000c1482c103074020018010707 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 181573570 1250 181572320 181572331
    0x80405030d0212091203010605040e06040b04060605090901090e070519080109030c0302010b030c09060415030203030a050a08011a0304080f0705070806060a0608010b0414122e052a160506 82
    0x486400a50700c400403000341c04240902c00024809000800c0f0b03003030b5290026034000c036000e040058030ec603c000102e0282d580c650820404100c00207569400390424101c41801020706a00401824010394112911403030a8807030349102c1d190303071030702c6076400c040e92a0040b00400d4030000800456000e407030302500303080c61100f0560165107000001c040c2424041040740110320300030920b0712241d07500005c0200408034000c0541e074a0b1a60750004c00140c070108010140b55207151101e40e25120f521600816407030050700000410701c1d0088000503016402002c6d82e401550140c0c0d80b540341c25501500300854082c945010b040d0b0710a04000250368900840c10700e0140d001901d1181e850307a2200e1050351400c17803e11501f001110100300c01c01c5000c80e080c80c16000503400400201218600b00d07121481d020000040003034003a07104501e1000321040901d04002e22078004410b20051031303c4002d50710f05001304a0644030707007001d005a0032908001402116600d441c504400c00e0032030402d0514555400e800c585 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 181574820 1250 181573570 181573573
    0x1006210c090509030c06011404112b090f0c03020f060c15040f150c020f030a0c06090501090f050c0406061d090c1b0606090702070b030c072105070b0a051501080405030d021209 77
    0x4aa00c09418404070742c88040d1002f014074184003004600d808001c2031000c3c0302d01441d07946003100f00044184901121301800b03103940030382240c1540104940032a1070701c0d240d0300c1100c1c02c10001c0019280410041294004c019080d2103580e070714140710361340c0048044020050016a000c10210300740d640d200009040c0c4503800c489084a10024035640c2e441031581040118000c50380400025045402134400d65110705c0002ca4806480c0e80e0b0f0410203190188225015005140c00d00114101449048002c0260f85004460403401c480500b844000b103a8040d0300a0350444001101c03000000c085038014582c902c00c0c1240c61845c4810261241400d44503284600f00d240e0209000f079200044d00f10582d160314600515588440415168962201404540d02c0300d0400281c2e41e01002003482120280040d00c03229911710052601441103880140030840b054500740c01e00600c0800c102c10b0071108802800d1038505512141041032560060001e0b261034180000781012441d088851080e0140c0309490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 181576070 1250 181574820 181574831
    0xd0f0e06070305090a020405092b02060604050f01030b06010207051908160f150e0d03170a0510061202090307061107060302030103051c111006210c090509030c06011404 74
    0x4500300e05070788081d94400c00c00d921954000d005464640c0c080c40c1c01540c41d27401c85410704d0000c003a081c0701013411807403000403510324550f410510350180142036104070110740400140c42d0111000080e00c1040c0005099204000005005a4002c00c8400090712005090729003500f040891b50310001031134003564a560240c09a950303900740418071183c040c0c6a46e10750841c58541007000c1070b0307002210f04078030000300090780701c400e2802c0d00c4054003008d845000c1c3e07440f5041005400c03c24200d6410152580034a03510b0201000b4140040c18901d030700340d0b581c9207080807000c0c41c107482d07000c081d0040b0240c407945402a0900040c1240e0030070300d94410012107005503510709036611001e5081b40800d10001e001600b000749071280440c000c02c0b0310f07000940316003060301d25900007083c4180b0380034040d108138800076500c100922a8260f001400f030070503c07070035080540981c5103581e0185c10401c584910301c0c00c03949507404241c00202c05d0050303a00b00d00311201191310940c1c0d43c0240c440c006508800700d9000d685010b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 181577320 1250 181576070 181576081
    0x3080405130e0c011b0c030c06030c0f020c1306090f02070b07050a05091009080604060b01030f111c060b0c070519050904110a080f03040f0602010e210d0f0e06 70
    0x18020803420304140d0016003c002d420000640d214886100c030703490090348a03500c00c0c000076145101140558000c2442a404a040260190481d41c41801c000e00b4465004c0848801d15030001c0c414106107800e84070407803180c0b28007010b0b0000e40050b810210466040140d042014100c0380d014202d480c1c000c0340a039200341c445e41c80c00c0d01c2900c24401d02d1400100d04021550080c1013005d00c6004c1c1d1115403924444880c0c1d50400b00381003100503a0222465a211390074100c2039a410f010344d00c0d040b84018401c200c10081002c00e48514070030700b4810060407a40c5040400380341065401038004100c1180000d82c0c4500c1d10814546608850049900c20103100d01e00f20300c80310307621090a0994501520015460701c0d0394903180507110808500ea68400711040340494541c40034403501c82c00800e000015611a030400c0701520036207100740c20510031a85031600441100800242c22030221245800207103101c50100e001d24803c0c40f450030005c1c0910b0828102c0e070084411a44016441030b0040d09a842507203a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 181578570 1250 181577320 181577359
    0x12c0d1b030f05250e0405030d0f0b010908070605070b0a0908041d0c070f0209091c03061d1006050f040306020f0d051602030a0f020304120515010e090601030311150103080405 77
    0x100701248203200385103109020400c581c080300c0c0e411a001f078046a092265480300e07102901c0b41e00f075080041d80e40710400005a0350f000382054001c0c04601000d05107141c18228001c0142c0500d04c0058804581d200209002e1542c507880030f0302082c0c2107021250b540c1d88803260f51410420030202d0600c999908400180030b5010f0105a90b00c150707001c1c2100203031031900e400f003004030040a4a44500303401070448050f80da0175a0171f000040d8900e10703140813a10b1407620461038002c81d503150401e9003040c100320410051384403500350700099a5060074121b4075003020301c9101c5d0607806180c10050101d4400200c056034022a80068210301c00e6905c001d2145a540000c1c50311100c8482d4100000f6070700512114103c2c6001c0d0581c030581c0c80a92041b6801d00e913558441c0741c2c00355091481a80c4982201d000400141d0b40c580710180901155400c8660b5410014601a5282814400981002a01100404030791030922103a10101031480300a02c29507102d0608141d55441031240e940303c0d601d012035803502e8000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 181579820 1250 181578570 181578613
    0x109031a040b09030f0706022101180e0f030d0c1101050702031305010203130308090103020c0105011212021c0e0612151e06030a09020a0e1302012c0d1b030f05 70
    0x203005c00e03020308005140d554903029401c1003122811a403001203c000d09180e500000e140240034840c9004205c400b0100c081d41252145e0f00c2111117904140c3c0112643c400c00000c4a10388a01060001900b14088000310745050024400c060346500f00014040380ca580000036143c8821b20a90358000140c1c1d50b401a6601c1c0f0a1045007820155503103001c0001c81e8820000e481140018140945807041084c84035084405c00d0b00a0504142400011001c0c00040c8400c4198850306000500c0c1044180340b07903510b100150314800c41008180e0845840503100c2c001610110045940e884805003030100d00e0101203080040c0345802040905400c0000c880c0108901c5118600601551b145886200d0128003400f004502aa0400d003004400140c040d8038030704841c8180c003c080d41c0071702940c80c2d1000404801d8055604c1c0d019400e013801d80300202d10082c010f080c01e0300d41241d159903002040d01d0220744a2100b035034103c10714203840343d000040c0010500d0452450381311340e0030380b4150700c407025062a1902 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 181581070 1250 181579820 181579837
    0x15020a151b0c120f0318051b06040f090504030302070206030732041e0806040b07030f060605120402011e0207320d060204270c08061c020109031a040b0903 68
    0x400011015842e04c0c09000c083c000d5045900c0c020618812200b03207200007000c2640200c3d03da40c051074218a00412054441c03140500c2101e0031490146060780c10510807120b0700504115954410104003098003d0b030440c0c00b403d41c040e08440d2207181c401c1d400b4106500802c100360300341d8274050b0005580c0c4003070384e20a01040e0290381c40b40c1c10107040480e02150010042031149080d50300c0d10340415401400c1010610541c0b00b881c8003802440e001da40203003075030100e183e007000035414541c09000c1c1a8100b000d68090158038a00b03032196642c0d500040710010118201091000064118034216650214414069807201019000c0c4000740e40782d81441403400088041c01e0b20f09044151115180c00c17240094558003c044c09800c1c90785401807001d00e0f8942c241907045907800364400701c50104d042c0c00350a0040a1074144002549462030120350129a21005d12101040e803581d4142168064001c000207160040c01d03281e01c06040580c1d031340900000352015034504800100141c0c0f0351400008035440d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 181582320 1250 181581070 181581083
    0x1e041104061b080414060c0102030c032707091a0a03060f0b03160b0703020a050d0347030307140a1407030503040303081b0a02010b120c01050415020a151b0c 69
    0x1510385404805c1307054000c0310b1183d10440400034480050300034005180603c0d40c2c1c034400c590741c3c144040d1981200200c1c280388402c002c00007034045e0750480045a001d007200d096200210345000c1400c2d0220b8041c2d0300c050001d0340600100300100501000f0340c8100200c01620604003c840850020103a0342c0c0080104042ca0354492002440800091409400c0311442030044984002d000e82d00d242c1004640340704400001d9840c1c20340c0400324507003400078400c000ca40780c8000c0d074401119489201e011071300031140341484c0e004c4240b0015031010030072500d909400800300c00104407030350a42926411003007411350b0780d040d44004a882c034a43c041903490490341e1290003145050b1840d0b80a9400d100010b180a0b440341128480003880c500c008010442661140d00005001040300e041006044001c00301c80455408000e1104580c1d0300502141d007514408131a02c4403440900c0000c80c5004140c00d8010903926a082d280c2c250316030300b50400c024103140d0641c0000030200c64402210105485080074155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 181583570 1250 181582320 181582327
    0x150702030a020d170316080703050c09100e040c0305010e250f05040e15040509030408030f0f04030c260102030c071202012408150606091e041104061b08 67
    0x1850450050005144940d15110132404801c4160400d0f8104a41d03e107081001035480030b584030360000d00769502580701d0030104001d040038413021080340128100e0340e004d03203114441c140c1c0040c044e40c100000160003c0c03043c002020048e50007006014284540004808240085800c929502c10540e1122030701ca2800000da5440450482e080c004004010b403e1020401022400b1b90000e40c0462203010483c044030640030039441840101d0b20010200800303504240300030301548002208403070340107d1103a80c55460b08112028131181c1c2c404c56000405000c0f0103a40010010151052030311079480201c1c1036690000c408500c682170f841308840d81400410208503240000748940e20450f4071010510002400740602c003003040d0f07030842c4110b1003102c0200d5408100f0052400b00290342101e0865012400d150a102c2e010450fa801001c19545c400d0521500410410188000700b981c0d10380020414401c00c0b154144011341d95000780a2070001801d0700305010130803940c103000507004c6a4071019581c90f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 181584820 1250 181583570 181583573
    0x6080603030c030712140301060801080d0e010e0d030909050702010510060804020603071b0b07080612070509060d171809161202090406030602191b26041203090302150702030a 77
    0x2002c0c0c0c00c5c2145041480f000301040113240c448840130318013920301a1503022081d410300c1c0b030443c41c112481040c9010483c80071081c10060f41e0011420400d074200b40c80400d41c20300c1d64581075a1500258100000403443c1002708504954150000b40c040d03030210381a5200c06449203400c035001e8074101d0b40690000420004a204144240d822040b030042d50b001d013450312551a9600780c0c0303d05047d104c0900081c134038014010703107203828260445c0d01010403000302050340c505000328041c41c0c0000c043ca071007200300410350b1080c00350f030442c180c80044080002658660000d1003c41c5030000039003003030703002d5045400000d2952880c1c01e80001d00c04040e88900180c5500382c01408040c1d441480c400340c2068807207900000140141c0081e00b02070240b03d0b6500d0020021800c01003428888030118041e8602c003000c10004102944100c201c250030400a10a40d4010484500258071a076441004d81906490a030000d0540c0800c2034802e4034800c0f1070001d9a00172804a0450b507006109c0041d5054122050140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 181586070 1250 181584820 181584833
    0x1b03070f080403140d0f05090109020d1506081203070f0f0c02040e1906050a0f091a070e060418060504330f030f060e060f0a0e151006080603030c0307 66
    0x80e80079200b8500130110142e4425044a9504045035a100d21a04c900301002500441c0c042e170b030392021102000300521032041d00040d95030500c00320050442c0512002e110b8403501705401c0340c00942452022114000f0007a40024002d61003194000b00003201010341020b918031071003404507a40c4040e6201e59101c001703502040018210000720b83ca252040d60b0480c0b18001d110402100d1050042900103480c1c64151501019500d416001d4401640340c25105c0f000106074140303c40403d4081c0001d0b10721951040c41c261031b01200f800410b07500c910b01280009180c3c0c400040040200d0783c400c0107000840e41e40301800b0540c0c5144070300300035101020104501d0a40540c500059030740c4e03110340b0a032095544003035034840352109801c183c45444100300401c00340111801013641b2210010002d245924000b400f5840c0e55001411500704030b0b45502c4c000403071110400904145800720203c258043c2044440000c2c0d0500c0e0b881010701042540001400901d0301009071200340720307000040e5288c07956580d01c20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 181587320 1250 181586070 181586087
    0xc05030709050105220803090103060b07050d05030406060906090203040210090f05011413081e0303040803040f11151b03091003020f04080a060204060e0609031c0c0506040b1b03070f 80
    0x31701c02480c46000c1c0d0174200380d10040f030380140b221314080c40d03880300203400040c00d8444940050140c5c1e1810009180010400542c145071a0b035140341c00c81d100d440b2803a0150150a05a020286030750401002082540d140d030300560140744225109400c240081c1005d03142c203401031150660140f1150030400a40d4026a1010a407404200c281c9140c10014000820804920b401169071a40440520244d902d080040020084003140085066203810b41c3c6488a81c80000c100071320000d81658000f04024903041110382d20703640100900ca14810000c0c6c0c01045422061403d8011890f070400035804006c00f0089490319a006424814100d0646c0e000360302a42c400d5171803241002080000158080c424444611881d20400000d80e40c1c510303002d00207000d10810180c0c1780c8038103010480d810b010303503000900000054507414841c515400c80f6201b900c3c00306d480308018149001d190100020403003012142c1d8840d10540516003030b004110800d0b4907280c082160154041340421440d000070a001e10f002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 181588570 1250 181587320 181587337
    0x4020309010f0e151e01060e122514010503060d020d15050f060603061f03060b12091213030308090a020a081b100e15120c070302010c05030709050105 66
    0x101e407000807554840c0454190220f00c5800f6000600705404519020580a42004002e0440c2c0c40e410074540c45d142c3c001c00c062081400380500c20200d01d856480e021b02610582d00c40d1420b40c1e100c1500d40c4000c411208031400420070586c041400843c0784500d0b900000c510030410303500c841c2542d644105000d909031000300141da200800c0780d5003200141c540400c5004070300fa442c0c004522400d203a0012038106070301500f00d0b84035900501c2003000c1510303100925841c80326041505a515254981d0039801404507800641d28040c1c0011020348030a40b1021740c80c003c0c01d010086544480250401c0c6066010b03080d1003950502035030004002081c481e42015030800241e600390f4003081550b07800951258661b82c0840d1850704414911141c003040c12002815015081d0341100741c8210200d00100f6900700885550720a0906004840c0c01200c20002e0305c065a8100303494080d18200054010100d4000d880110015820b02a00001c042d02ca201540d000d4aa540c0f280600c440c14180155801e03003018a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 181589820 1250 181588570 181588573
    0xe1c030e0609030303180727090c09020a170f04030c08130503010507090806100501022d0102041403161a0711030a0c060e1503070f12060305030a17060f04020309 71
    0x401d44150f405000941c06030007203480f5150350303603003003540346080c030601c1e9001e0300d540390f456640710380d4408208a00e40141000e041c80080e49207298a41860490041c0e0011001c1602c0405c4e8081880e40050240701180100505018030340d42b071101c59100720a0407203005002404843d1720030005010040503004818822440c0504c040d268008a401c4400880b080000124100b01c1004007200501c1b0701c2da04810300c041d200d11818103100010790381c0d150140c0e031a41c070003a6003140d103002c0c01c50400701625a00070302002990b485130b842181c500c0d1040700b801000e104e402020b9a441001200711006e2049035200904211207481241041c401500715040075920302012118103003060b60300f0310900780200d1041740c805c0701c85820701030010000012400558041c2d081c00340c120417441301c588192940148940741507200041c0718001103d05402d8075140388501070034408080200180440038100f0603a03255281941300b0704000403c2c800800646080d9004020400020043d003447d03001942e0010b0740380d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 181591070 1250 181589820 181589827
    0xf03041a210c0d0b01110d12060323011104120312140a05040b070201090c261f270f0618030c021804050d050703031e0b010e1c030e06 59
    0x3041d0a41c1000712080400e01c507000030031503080020f038860b0141c5003000f86802202514050800c40d5250344441d9030380c050110301104a920090390742c100902866001041d40595415002100003040e074540b000c4140d0b500300b4410101c075856017020344088a04d1300c80d1010300c04040b03842c00e44014411381c500c40300c3c1e99121030b181c0300e040003008075180c0941c0f1101c0c400991490641041044036402400000841e4104080da80c0441c800c14111000d5a284801c15031a10448a07003501d501000402d104c00c990080c40c03140d00701c0f02c52401c7d002c03040d04071075401802402001b15800e01910310f00030b12002686d802c00300364804102c041d039582400b288180c50010308071a0258501200d514603410480003e1030b80c1e1780b501d0850030f01401d002850100c0807018485801c0c05e5854a454200940c0780d0000c0102c00b003280014588030743c10200110030b140384450024481201c0101c080c1c40403003415800308124000841c03190502000b41e040700010b03036444000c040000d650444140500000c035580c045001d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 181592320 1250 181591070 181591117
    0x5070b07090f180509011802120a120206070f020a020a17070906090c02100b060304170f032412030307030f1416140a08040f021305040809030f03041a 66
    0x61100001d00f035151500035804801002c02819540700504c02c24599040c10079a15518551020000002d68100d4010007001a00c0c0c05c05442d0041c00a409408603102020a000301a0040355150254074255030b50748500150100030780e5079111618009401119001c01000407049a0903040307044800501940c01540e81c4108520a032251074001c1e6072129601c6550410f8540c0412080078074407500031060001752400c0c000100217000041001d000d24801d0300061603a0007200007150161040304030010744908111243e003940e45040d1548148000000314000043d00d4600c00040e500d400c120011465a9145082100a860035200c0c2400068541401d080d400008441d035a1064083c200001706082c0e6402c2e004010b0781e908030825400c1e2604200300704141d9480026075500c55000300e4219105022440801c094038849e05c00010010324000c1070004001480006101d8140704074103c0300c0300c54000b000143c60340b00d00d00c078142d50f0001c0c41b0000900720043d4005401003c01481078607440300b0701d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 181593570 1250 181592320 181592339
    0x20d020301090c06050a20070e0c1c1d2a060405040603062f180f09070801090b060c190203010e100b180c0702090405010608010c0809010f0c05070b0709 67
    0x140c0c4c008601140c4085090b0b04101d90044001003c0070301d000c01d03445020f1070391440702e460f900c00b03025400d208a0300e100080e55036a440c07002c45407040750070300c80b00500450700f29002e4010100800c0044e043d480241c04d83d001c110b00061452039030100742c642c0a80581071080d80d80c3c5550b40401585800c18001e1100040981d5588a244000c500941c4041010200c0d54150450000142e07926080180c65111002d0700d1610103098420016800602c20120a404400544048490164141d0006a030410400215480f031280341c12030744186000e2124095080c1044200e00446200481d03e41c003a500c00810280be60b410300317840704d001034000600038812070501810580e031007000c200d9480e120a00422036080407035042d408000300d48001e50240c01c003400804182e200c1d00001a02c220f45403800304080c46000c4d4041c200400c0c92400801943d0f1381158081c01c0c2141c200c901c444035500e4120041c3c10076100e40914544c051107a92101c0c07070a0b0540c1e40300c84844801402400c00c0044030074003c1564583d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 181594820 1250 181593570 181593593
    0x10f092102120d0e090603030f030c090609121f05150d08090306090d090501020106030308181006080a03030506090702060105063a0e16140411030a020301051002010612020d02030109 80
    0x4e5948141c09098207052181d11070000c0c1c000c078080c2c2e004100d000c02030780480701500c0c3c210901601659a9240300400951207004001141d50301c40030300c103440001c500c0001810049143e86040d4400301d90f00c6d042c60142210011140d40080ca440811390000707a24200b003101c84954802d802060030007a162001c20f00d09482150b091500780d20034602e549000c0d0300400c1302001060300344000d008040c11941c00900e940b0002e0411104a100400c81032200d000c01d1103024140c02c0015001c02c140c03595551000d5880296035403d8000c03a2506000c0703446e07402d2000c203841c403807100781c0c00410320b0740d2171714040c00850b9004512044407140d100c0c00b2400c02c540f8040c081009009401100c0c002192441404011207075150040700d403d50003c519542000d9004201b6401c454034000052122244c0001003070142c031842c900c0140c051400010015904215030285044c0c40c41660542e2180303408500a070308070b598500460611101480d002d0005103003610511020500c040c00214102d600e03540e41881807078 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 181596070 1250 181594820 181594843
    0x1502040b04050306010e0403020c100509030604110f010201020405091b070f12030506060703020705100201020c0304090e0d0c08030105060f040506070b2a0708030406060503030301030809010f09210212 88
    0x580014100b1861404200c418007400d05041341480a08050b03030007941c0d40e0102042140912100082401c00034000d0741510b6607030740041c099410529107071400c4044c1e9148550b00750b20481d001d04401c0e205510520a0b201942e1029041481540301c000e41d05102300000507140c08000310400107480003d00d01c40c07401030036910031440e0010440d2511005400c0d200010b010701e000d400c051100d000031075400901e0501b1100c068648220484d14014200d0286c030408004031582c0c440000c001810120542c00b0560783e0945405681c01008207100440d226040700304c01821003070342800140b28034075024008186240c1d560314040d252954690116100ba04081000c2e90240b01c007000700030041d6104104000c642015071005040541d40341c100040600071684054021100800040c0c108100d503800f0001800008040341c0c7caa681d6841c2c01000c03030b4000343c001400901010403540c2d055010340030041c00d07107200000301440c2160485001d943c221400350142c0c3c1c4a510b003801b03d0502e1100707002801a06 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 181597320 1250 181596070 181596089
    0x311060c0d120f0b03151f08150717010608090a0f15050612070e04060b04050f18010c0507080702010207050913021507050a080c12040e0114040522150204 68
    0xa015a0b0000044403101102c0500c01c41c1024560b80715643c01007040a1040c030318140350b52503910307010f28549481165202c1d0300e00d052501880801e00102c000348141c103503008400241e4259031180381c2140d2551061114111442082005000b50303401451900c0e03200d1070600c1101c0c14900240c803240e400b00c992010596010391848400d4503049030502500c1e52060040e030706401d02c02c40e03600c0066600c6906104119081181002140800c110f40e004848136510052040c00b690400b40c00c1d480a055007943d111080001c0e8045131490802d06024029002d032498859500f000d400d500e0340c0d01c095000020403411030256840c0801c065070380100b4107000c1c04070040303a1070035003400f031043c00701400f4010000101075909108000c0001d50006a001e0380130b030b003c2c21280d2100100384542e46018003008460b0b0981d10080340100d424982c3d58161412903240621605030940fa00e001c0c003049500654074240c802a404a41043c00001d8109401c1e21600c01c0c04c0781c0990940441c40303072080b0381241d040318104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 181598570 1250 181597320 181597337
    0x1e040507030e0f0d14180307080f3702010c0614060406060201060b0904110412051006050d020f010518090a0c08010f0b09040c0e060c010509070b0708040311060c0d 72
    0x1c02c0d041010303002c0c1c0e4002400078544500d40300c1014058600119144078604000a184c001003000300c040b400b83d0305030150440320125140c010709600c51030f8128039000d903032140c0102001d81c04801c030b0ba50a10204d403c03440e40c2100b580000005000120750a090707040c0301c0d04080b5400090028802c0780c01001c2e03418100c000d00e0030b041c1d040000343e80c42e642c040340441e810034105204142c010b004940c140c4900715000500b0342d42004822040340115808003100307684442004082c0305020a8120695281000c208940d640755401c000c05505856030194001d20011851180d40d40180010032440500701d910401950007880042c8200000300c0c1c080841075100c2c66190700030741c0c01084189c0502079990020120700c0c244010360721103004403c00c41e03200e242c440c800301d03801d81d0284800003020800504201d584408020b8858083c0030183c4030003036644078000e0006692850342c0c0c141c8042650280c4018913242c61764981c02d403200c1d1074109559025400300412180b111041024030790100094466140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 181599820 1250 181598570 181598591
    0x714030307080921031f05030d230403030c020d02062b0c03050708070e0418080702030601060207050d060b0a0b040f03050601080d0f0f031401080f2503021e04050703 73
    0xa040d08403608801009082d0400480c4c15031000c1501d1344100100501c070480032101d8208402d0341160360010350107009080c80f1081682c4d2010501140340c90f02c1100c019402410350b0302d00050310440c03001900041c003684c40c480041c41e00c1030130110107900040c10141007001000800642000404400c0340b154a40709403036259001900a80c0d40c1c1e45094241000030340751001c03000c1c00c80003004020000700404404040b01903680c640c480c20450405950480b064181d903d40b0400640c08035106034403d03c03030f00d030000940a100003070314010f98101808007924800d541d6504800b13001e44d54452036101c00c05d0030001c03800c866000040c100525004002d440c00c0d51440c2002404c0c030030182c11143e02038100d6180e040426403c60342041c0100a140b070007a00148051038110018200348481548d146003da00001b038201000902400c0e101000040d240c41e40d00d0b04440d003000360546003e402e2845a00c52040025180c132244034011400a81d0810b02a41c1074100040c040b91401c0300c1c4003001c255129408032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 181601070 1250 181599820 181599823
    0x602010614060403050601030b0403020a170c210a1209050a050309270103030f020f06090c01030c05090d0f080f0708030403030501150207030b0712090510111c0207140303070809 78
    0x7400705645151400341181c03900d40c0c58100500014150308000c0020408240c400c100e024180d034ac021411203151081c240070b0b82000d0f0301a4151a02920403042c490b000c10710141d84046200c0b0003800064030b0161000c80990701c0c800f90901c0c0000d40d43d038544600703003c101c1c14045a400c0b11b00c100003955565220004004548140d40441a80c40c06462050f00c1900c100f9900e0a054a401d8100a41d002c04c15a000728030b09012032405079404c0c010394044c400424030014001400580c01d03241402001440c10f0111424040d0006103a40102d000750306071b01244580c0c40c1c0c0780d2000d0040300214601036001e004a51140c0c0600d001700d80f44000082080285945442103038054402003011480001d03010340f000796625054040605580810808251998081c514180e03100c410b105080c0141800c03418007a8455040c4031110711103e0074221280c02141180084582d816622040400c4024040742c3d01c2c4020741200c0c40403219122035040d4a2103108040000c1c42c4034250340d175a1002245410031180f0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 181602320 1250 181601070 181601099
    0x31b040501120b0105090411120715140f070302010902031905010f02040e06100e030d0801090c031e090606030f12170c120c040b04300f060b0d0c06020106 68
    0x502e03030b0498881041000450407944a811900100e44101c859112424200903801d402c0c0b10700c44e4072100c0340340c00d07180c0d18101086032011030b030307560400c2c0b0946042003a05860407028440240a000c40810103800320300d03900005819014000d2000080303404490740800d01e80198202c4004249000c0c078a50010404240075400345540120310948c00c151410030208030441002e82094440c21100344503c021500c9070414500415004007218031300141c15102404141c028000d20044c0380c10301c2074802f01d01d4001d028414400e50740307400071820452140c274000000e241100003102c180d43c0720380001000c1a89690b0201ca07113030184002c103c4138005540080c00101c0710101c40319203100220204062200600140c0f0310243c11590b28600e06d0341ca01c0030301403040c8500c0c0c01022003800c3c00b0501080c07061020340c10081d190100701100c1c006641600b03c144405c00303401c0004151401d14400000000c0c890340148044581c0500b5425903040c41d6070b1000b072101690380191005030364801041000e8250903420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 181603570 1250 181602320 181602329
    0x9010605030706080105011d0a060c051b01050f030c0c01020f04060305160e150c0a0f02090739061a0a05040605150f0c06090a1103010516030b0609031b040501 70
    0x103282070b07480c205014202c82d01c144521410300c0402031018841d65441d03c51702690b14070042845000035101c0c04082c04281c049402969a440340d00d065904801000d252002d00c024140c41d400d09040850a0001c2681d000800c401e0060f40140091000842d00740042c0412920448039a9112030030044001c0c12107400600710204114600a19424560040200d40c00850151070315003a103c100c1405e210140320b000141c02e000c0c0320303010805080c000004003441d01c0d20720031110240d81d51a1204115002041072080107104017061200c1050301c141100e2941d07a040e02c0e0740140c1007540c025240c07001211031510f48200c07564074100c0180c0c010700d4500d280d4409400200e5040200c0c50030f120200c0c07000c01a103a510f400d50240010a2a6038900d48000e075031245d035041045455900c2e00c031060b40d40f01c0c08002c204480442181c9924130322850180540383c419149034041c10190801c1c0030007180640f03003462046030002800c10040c04251000e00c24000411001c102c98451024410203010849178164032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 181604820 1250 181603570 181603573
    0x5030d0e0c010c14010209031203010812031e0417030403080405211909030b130c05040221220302070e010503010207030206070e010306120308090c01030b100c080f120901060503 78
    0x400e441c581e0300301100000d4940c02c22800b00030900d5000c88180244034a17814143c1c10300c10007141e03110040a2030000d60503210340b072080c0c0d0101d8100c0119030b88507001c25103c90740d10503a0401d035083c0d04500150b5141d07005014043c3c5100c5c100c0e54400d90300060b8002d6500340d0014880c141080140720080010509110156881006000b012b000040181c0075104096000000c2501e07201004d503c176524060155070400c603d9034030360810040c3c01c0810940001c0403164210503100004080c0b0346442561901401e44400301400403c0403041d004442c801051400c0c0386140100c15404240149540210b40323100c0c3e0018141e86040030702c140142e0605038170041c4030b40c0c010814100001e034041a1150441000c1c00d00001d0110382c2d00050f4050110354000581e00311011000304145a400740c94503004401c80350503075045840020044040c0c07540c136203c4940002210f41e40c2c840700c074464030705d04000a010f0316409040c1001c03e6038080d11503014041414103c80320b80144a034151083c820031009040490 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 181606070 1250 181604820 181604833
    0xd0b0a0c11060106201e1507050f0304060b01020f01020c0d0305090601060c03050a030906021801180b03190207050105070915020615060307050d0606080106030e0a02030a0605100801050405030d0e 86
    0x4e0010280342c20381c2c2445100042c4e041c00306603c94000c01038007620540c84100c11008007210089180d40380901078580075008050004a28040d01484c116404c031851040b0351884c0d0b64540d241d42d0080c00c80d00700d843c0d045108141044000113803c1c80901403040340c0718080d0900306a01d030402000e90b5805491201d0a0700502c004200395034110100680c0c0030341c14213045443d07150b21031060340144a4441c02038121400020343d101a64548201e030800b144090301d130390071103031211500e9211044040c02000810082000840c8032031b8003548102c01c1071040c10303402514110782552014207540054401c070001c56140007041c002d0703072001d804003259401071b48010b10440c60048040c248e1800340880c1a4040d11001000c11031240c4664112000810000c0302404000c6e607540c0f0003844018240306640c0060b25280300074402040100702506a070340c0007401071501040c503032603a00003004080c1c2080890b00c801d40002441400030b020707462046000301302031501c0e415400011815a0709603110086590804d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 181607320 1250 181606070 181606079
    0x80d0813020103090c0b0f0d180203070303141e03010e0112030801050405060d0f2a030c14121b0f100f080901060902040801020d060803091e0d0b0a0c110601 69
    0x304140c100c032902460080b0780500e0300d0410f0440d0054542120b134050400148440d400346054008082004400004101c0720304040c8940301850703c00d160007585600300f100e082011a2040120112108505880c5032801007810780104545160307150175030500c030000c40100a0a14465000c034014158a003407503144464568000300410310500400303125580e284007181140e180c4482c08006680e001c0c0042446e00e0840c01c0c030300c40c43c6100c00001c0c0e10280c0703042202e480d12001401000103ca41c4920100c0c0d000b41800a003400c0a001d4210301900001c0032101c0100b46101040b4010240e446202e284500810180c00e102c9811542c2c50a40c1c000c4070f014010741500d40c0c1c4035204c1801a20146401050341d01e4142e031440c0502000d40c0600c01d45030001c0b0f0041008101903004101e0740d40842d038200a02c2d5070710a200c684900920075219404035480303040b240c03407109c0740c00d20840100000700b004208120729901d1801c1c04401780c0f202003e6603a1240800320036900040141c06544284000b00401d6161 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 181608570 1250 181607320 181607341
    0x30405061c1a060706090609080304050102070c050f060414280617060d1101020c040e15100e01060c0807050316060b0a080d0c050f07120515060109030204020a050c1006080d08 77
    0x803130070001c103c00d40c0c0d0103070501130100c168030119926030300008095403404e0500f083c5003c0e4002c401c0594040800020001e514501003a4840c21444060300390781c10075251011034081c0c21030818181d03410820307405003a1a2240c11107015440d80e141c684261041e182007213070003802d580b620400d4002c204003e4083c0481903550b000c1a1031044e5000c0509402c01520600407070411074050109034005013040004081c18401180c036004040164203141007a568008102c0911907803842242c5449004030f0040c0300041c031546d540c2340c50360301600d842403070158039079100c40c555441000d44800448401d40090300700300050160240a0300d04584c295025814440b03c00c0c1c41d0032034680c0890a02101a040c40f007045814804e070389109802200380c0d03000541c0c1d607801c090071007446d40c0e048819000300c194050803007580c0c1c889940140010303511000194259800d20000307602140a034030a0240c24448104492020002e030150100c240402040043c90118201d10b4200c0040e60b01084c00649020081e8103000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 181609820 1250 181608570 181608577
    0x18060e0a03080d090b0f0601170f040b07090b03040804051c05060609100e010b0408010c08240112020c010b10020d0509040515100203031509010b0a11030405061c1a06 73
    0x41082d625956420140150030051600d2a40104110042410001c07240c04031095148104400c1e00c81542003640c09807051100441200c0504045144002040206600d9241036601001c0c5081410600d41c0f1104002c138150000c40e0700300d41c0341500042c00c0c4881d00f42001189004c0310740da422400001c0300b070341d0744a4032540010304190081c064080001d20040381504100b0041c03160510700f244550310b071669040594884c1c001e910040d0b09001000d0502031064402e03921541401010300700070180019142035120914101604100c58080c8202a0300440e02c01481e02c81c412030000510540080c06100043e00310b03042e031205540002c550680c5094102044403104681202e001400d03030384803c080c075900008440789a41010032500d0328400e141d000001035006002d401c4110714265440b104116003480300340100c6034113020034050880036600840312004054a072170240c90a00d612200410303001d81018640c40d00341e11400718803150420b2640715a9001d010030f00401601c007000903010452910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 181611070 1250 181609820 181609823
    0x5180702031206010201020f04170c060c0709020702030129030c010207150507050f0a03020d0e04020a0c030e030717070303110111072904060504110405040b061903080a18060e0a03 79
    0x2075020b0000d14540e200b941240c0c139510707980a078283c846032100d00c1203001e90f0b001541d031007180c414000031100d07601c4c00d10b044d2010f00000300b0040042d0b0b800c061405001c0d4102c5841260599201d0070455040d0101400001c0c0c3d40c20300030307441440c40700c000c81050b1404c20707203070070103415504038010030700400c40d5819014415a6041c00c2150381c0700302c540b404a2405a8035051502a4014841000708040d400301f03458101203003139a292041050a40200012881840075003800328100241e0380c070009000f801103848502004041d20040c969607034000c0c01240b05d40d564400c440e00030361000d20405420000d01d42076920b080c2c00801c00d030a4080a200307154803407010041c0005519045910840d0b000c8903c41c45814010140c103101801d252030030b0302c007409083d2400c69094100d18000c3c681400d05101e1a0300c00c682001c840d4030710b80c4a0805000b542c1e03a21086194041d100c8110210120718180028100e4041e540e503060712644001e6000b1410744295048401004200410301e100ca90b40d682e000404d8a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 181612320 1250 181611070 181611097
    0x1806020a1b0201080601030c09230916121e1122030c06110a06020a0503070e092a1b0c04180b190b100c0c05010e0607080904020403020603040501060518070203 70
    0x3230300201134034004800d1303001c0313200c10740b042810000f080c1001c0c2120041c8003040d02d480540b912000b9081751f08200388043c03100015200400c00315628080c1e08001c1d850801101c04a1402d0441c5e00d0391000d4440c800c1894101d09000100c40f080b840300781c04904c29000f0300d4400d40d054281181d9405a0420142c400d4404204000c0ac0114412030140300c1603500ea903100904558540041070003500680040b104000895000890110a810031101c802e1080300002100c00702c06800c0003c08000e00101d1042004240f8207018000c0c070f210881c2d65040c0010000340040402c6004041040203540519a400004c004070700e4284000805400f9099000b03c48070310008c040324213129900004090581c100c1c1d030b03c44ca004d400f0400341900030340c95040580c001c00251703c810b5220801074440220041005400060030812070020806100140c0000e40d0024001f62801c0d41e40c2e00040e046803c04d580a4989940d6003008209515003e26843f070040002c0d14a801546012000651680200c1f600319150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 181613570 1250 181612320 181612331
    0x14040204050c12040308090c01030c17070908010c0c140f1c030219080402030d090b04060c050a0b04141b0f090a060e0a15080609030f0d1806020a1b020108060103 71
    0x9804482d025910300e40c0c01c410340e2200d2840d0a041c001e2050400b520000320b107028041c42441154842c0c05005404071880d214100e0110903a03d17080b99900d0020f00c0d44003000b03032294012030100b0003070250f4a07074807500366980e4003030700031500380b541074140d6403190b42c0c0c0c5640c84403907180b0042402142c18808800c030501001680002c0040980192050024000c3d1515401481e6070203e0b800214141c0640d00070f03004c8a9210182d540165064001070141c885808000d120401102d84101c514002140c40780d0243c8401c18202c0d40e070381d140440700b510202e50709607034541d1441140d081084480c000110410105556030001c2c0c0100b00c00b1031809141c1070080c00640300148102c0303400e801640c010b15904000c80010f240902c04003000f4001c0b080d0b1182214184540060240030000780e60740607032510f80246103000b011468003100c0354804d800342141c1680382d51000e03050104200003041424013550015030f8424618200901401d049044140d00915041004000d40d03404540590701c61000e00340000e8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 181614820 1250 181613570 181613581
    0x200a030209030d030914010504020901140a03060501091d01090818120a03030c030605030f07090c1206030c030201030b04020304031205131704050f010908060703050705071e0b0601031404020405 85
    0x1038400c800150b50148507038030b070303010340140d1550043c0340c0c90740240c07010b24120b0341102030982a514146c07006503010141d42c0061142038111200707122114001094900a181e40761303141c02c282d032401d80c000000c036643c0c0c011031200d01103500c51503d01c1c400068001c0196122983c0d5012050041c4107082d80300712601200c40700261074411144440b0800316080b19480901d515008014259003141c110000c0e00b800d000081c2d601700007c074202e4a120907000340400e80d00f40404c0700000d100c59422a0b04002444816180c448610720940010754010700707012050a05600024040da4152642d0718082c520400410010a9002406280f040603110700410385485040304070018100d45c020152808140720300d841041c0d51510000d00460b142070380c0c004038404502005454000c241e10860806400000000f01468820750019610030303c107050040c1024042e4440d5856139026500c4118405524021079081c004220407007540300c13400f4070701801840400c0700405500d0030068402409181c44002190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 181616070 1250 181614820 181614827
    0x819030207050a230c03060f0c0712050c063411100504140d0210020a142a0606010203090d02040204170a06050a050c0406230d1e200a 59
    0x442042d00503084860b00349190a11140d021400b81106070a82030403201c4401801c00810400c810a070001c0c0508400c1d0f0790041d6400080c030b00103101c140b0074682080032000080c95054a046001116902c00c2c1d26010b08608007032034014042c1060201300b0078422840405800313110a580300000d06485081c021304210300a40e030b58008134a03168404d0045410080214240e41e2003684a5402800c034110701558454045443c0c00c0340c03c68000c0181c0102110342c071607050b41d0b0020001c0c1c05061034400c2d041c0e01c0d0031001d8603050f00410802440624030007032030302c1441803070400c400c0390000340c5010380040e08108001075644e00c1048000f6000d0700024040406540e51681601d00800c44068003600118140011984964003083e048a00c28038103c04207801501368481c0a10038600441154a40750074002c0a64a1001c0c2a41d048441030301101000ca02c042040c02810306541e000001003440304001d40510342c030017042c10b01c1d1003005261000502c0071280c0c440035104a60103032034070640c2e0f030114140101c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 181617320 1250 181616070 181616077
    0x120203160f0c0b13111525020d200316091104080604080a0912020906060d0f09030806040b0105120103080310091b080112050d050c0109050a120e01050708190302 71
    0x3074581d103c00780410502d2031a1100c00a81c0700d2150803508145813a02c000c002c1899200300407401c0300c4105001e030040c600680361883d00c0300c01002c0703065540002d1f80c0e070000d556041007480484080b11100d040401114900c0903041111030118050220782c2d0700e548001c1c1d1905035500c20301040603102da0140400e0102c020480d40034103c10f00c01c0d074690b807405051107181980844200400500c0814000030f84126418010303418a81c018518400c98440c0b03030400c90705410043e409002190340310b880c058070010030710510b0310b1148241c80c0d054180c903140c4104001c403102c5060700d9051040410110a03042460300e501e42c1581c0d400901d480e05d94881c000c44028140f5290000102e5a1030000b44080d440c2ca032082c011440300c1d0556802855030b0b00c0e400707101e42200d00032400a120b5070007060034002c84c40c02b500141010320720034070000844092039101e00341707007041900c001d1b02c104198682c5668070650240c000500101c00382041850320b0010358412159208071b00580d040b07901c40480d0262510702c250100d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 181618570 1250 181617320 181617323
    0xc08091f05060d05120405030d0801060c030507211d010509010816110703030c0b010609080a0212011e020c0106060509090a0e0a0803090f01050a0b0d020103090204020d140403120203160f0c 83
    0x450317100c0604215203041651060140c588680300e00541703080c140b803160061a041c1e400c0340e60744a03100003944d81c0c2135400303400048089030b40c55402030943d0310031540f48030f0890020845a454120030b05040d284a505030f094800020b040090403c541182c5980014185401c4078844141c0b00013a4000b0342c045a009a000034107203d2800bd00000006160340060313a2010303a4001d4400039180e0341d0b01c10050fa2141454440d220301da030400908580580b81844041a5240302080003050103021544801407001201da0001e4040c4d03400300e420784811200348241c80c0605000d01380f00c4d241c90101400500f07a14402410104503d80700d0101502140003844060451544034420700e49074204101d006885009c044001040d0350300c0c0000142c2c1880a50054400f900c00161454040b180c561f00110080d01102c6000e0782c210380c08010048500c0c0c1240b00780500030440c2c010754043c904091500502d81c00c2915603900c0703c50f0050050100da5160300302c00700100340460a01c40100840d0440c1941e01d1501d04a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 181619820 1250 181618570 181618573
    0x2a1e03081303080403120315030b010b1b03030718090c051903020405150a111c0e010302040503030f0301050114040e010506090d050616090b18120f100c08091f05060d05 74
    0x500104010b2140140398503c095a1000e20219042300c900c0001405244006843d840030040100300303441e80000200241c5500240c510501c0c0c844520030f034610f0b030007070303d0040002d0301c1c180c0a140d13050100e001c020007911160b00c0a20410300340340f00c001e146014014420040d05902e5841c0744429000307a0448009080191a08000800c440f282402d40d402012414010919a607681502c5100100d103020000300c4050003c002d5800114045840c4040910001e05241c1d08200201d401c0e0340420141c510244e040c1a8ad5550358140000105100f801c6003044080315021b000a0110802250586054510039150741703460b651403200141d909081c4c020003401c00c0c002e80c000d1082c242c0f003021850350107002c00c1e205c04a1250303560b541e862051040446ca0300344626050454407940c035040318001d0907600b140d0100d030003120122800c1d9041003545d070228074100f03079201e01c0f84982c1900180110b5004803500702808441568142c1c1c202e049040018288850b0b5903803000500954508401c2a0015006030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 181621070 1250 181619820 181619827
    0x403080f0d0923010c08041b08191a0106050d0506040f02070c141210050709031704140103180609061d0c03010b0904021c0f2a1e0308130308 62
    0x1450200304605501c40483c0043c4210464030f031601c14090b00ca84100030760380c0d04e0709998442d2600740c021710302942a16a007500c901030000f82407008220494400782400150140c0e228580342c403022500820b0900300d80c604034400100b00d120303003101c156444070540c55000301d655502c0c940054000c0103c501c8054850f407011440390184402c110801c0243c9440820700c2920701c007140304001d0021a96111004d859024a084081070016600060340100c5582054030340c1c0c0b80c4903034648100d101d1010318560748100208040007600044000c000d60b10070207080c01c01507102013542101c4600030f15400600300c0c0b038840b10b1031001c0010562248003045820f100c4141440d031441d014546400c055025a4401d40c200082c03540350f0315250208500840c0d0081008100b141442840c072070a1103240800d80317104510741907807400308a190740c1e01550706240c82203429000811074901050b66100b03800400c48448460024070300d20686160003015207801151880e200c0c0d90301d02c0320000d00301968000600b140f0b00803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 181622320 1250 181621070 181621073
    0x60703090b0f040c052709030f04030f05030c0102031f061803031b051b03010515060712051c0902120d020c040f0f0c02010203060111150c160b090c03010e0705060403080f0d09 77
    0x41006110041b403196004405843d00f40c0c400c0e07524010b90313180c0b04001504000400024080081c80340c1d513036200724182d90615103102c841c00d08980040740c081d191610302d0050300500d0405d06121001034000ca04004801d030f2690000b40d81001c020740030003001c0c44040f00d01c40c0d00d000014039040720040d50000482e816819070004110600c000300d0a0789010798207200104203000300300c00001c441c80c0b17806800c8500b031a40c00c1e00ca0980703114107010000280481009080442400303c0d41100e100d005507140072a55440f80d00c1444005180c020407544117421040400c62110340c0402d20128001e011680811800c0758804c2c00c4c00100301e46050080b0b420710f000e601c1c001f0142c041d000355100702c0007620348484035404250300503160300c040b035450711b4040c020000140c1900c5481c4040d211140240b01c850f0700c0e080302070b943c1c60f0384400281c428090aa003e043c1c40c1c201d43c982405066003020744407000d000d0b1989050042740540c012404024407060b000318007580d0881d007120039121100e0540509000c10303242d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 181623570 1250 181622320 181622359
    0xc050607121109030c190e0408070b0a050403020a060c0509030708010b0a06050a08062101090c091a1e01111510050d030c11130c02010e060703090b0f040c05 69
    0xa4150070160500742415003590140200607106544800340240020368003d60401010715031040944020048402c2c021960806420150f44640d03c1080e07201da513070585050800c1000001000441c00c203003400100400250b0100e00006116030000e001704444040f0103056420340101c16070281c152180d803c001440510541102ca0600b00a0700c0320391980c0d81300c01d421911445004000404900c0ca28081180e5051402c5000c00745081d9160034101803031080c07441400d45501d040262403164440e201442200c403a44101403104440303541c6020700c01da040003c2a41e8503401656401160744400040d19145d024a05c0280038804c0305040d0b0350340c00e850061004101c541030b01d480c030040200f60300c0480c403030502d2504444200d4040d144c0480504082e6901802200c00d0010560013204d200b01c082c0002205008500d01e00c0042d0b000491480012840d2070310b03200f0020b00c040d003054100301c10740020411042900360042842d070700c8506595030b0303070401d207003402c156500c025005001c50b800b410250702c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 181624820 1250 181623570 181623587
    0xb1206010905090327010504090c050307121a060c0a02040c02070819170c0106031709040509030f030402060c071e2310030b030c0904030c020a0609060507030e010c050607 75
    0x240756420000c50b118030440030b0303690144004080c0c010452010340307400300900403280008124140341c05441c02c0e4554604c1410740f42101840c00210b24080103000c4ea40c0d4119003003514010b1b810000304004020040c20310865549a605e4a014981c0017561540d100c10900c00b2841c115000f0b0024020840f0480d8003d544580300d1090110502440c50110541c014644400074219004040e8400009601e035480c0d900d5400b40744040382d80c0d0340c1c5d503034008005140e804480104e400d00040854440c00b0040600003500c000400201032901f00b085000b43c880c91402c01d4940041c5c0542c0c003141c41d10182081286000c1054010500c13040242c201c030540c08086008000a444402c1025000030102c8411211040c03424621390341c0c440d00302258984401d10070f501c203032011000102140d002c088050041042c03000195010b0300000d1104c0c0c070071070550170103030280c038024403403454114010b62030040b00170414028808020204103403d0010a42603100c0e128031402c043d0003d054070914100000c001c0d14885 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 181626070 1250 181624820 181624829
    0x10e010e07030c09060f051902030c01060501030209030303010e060d08030a1a01021516090314010603050d050c030715060902120f01050409170f04081009061802130f0b120601 77
    0x200008002070005200340109000c41400d40c5608051074206101584d252040000450400c04107000ea4038000651480304200a049030b0050f569401c00020032030b094031150341025040c180100700c9079840c2d0320004200e17411601308841c4a051a00d8210009820303106c0001d000e01700080c048248001ca8000d9840140070080c000e016900000e0000b00598071890b00d418220142080c440000301800c2400000e42c8000246152a80c0d10340c0d2241c0e107828000819042444590795a0705041c030800c8410041d000042c0003a0030f01c0750800b91142c02c519030301d100b484030051890000081d10783c0c001003660441009080c0c501010740d19400f1072042000b07426422a1000000710354603000140500705449035020560704590101000c4006020f02c80543c0d00c40e2a65064404c410040001c000c0401c0c031507450349130748040c408100070b2003508000059902c190600e6102e00140031403540141e8030140b40608501c64004041948450756441d14001d10200b8091508910b64550102909002042041c10785 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 181627320 1250 181626070 181626089
    0x21213090507080c09010e19030515100e01061112040b03150f280302030604081e0a09061803080a0c1502070f080d0603020d0614060d030207060e0f09010e01 69
    0x40d03940342c030100c503155400d0f070b41404900340030016030400d54400c1d09400f40009001d0700c04c40030b800d03050903800300600c0313554010b0790a03412020251080b14443e180081c2c000d00d001c04480e8855040480b04103801d1018424042404520050245085010f118500020710080581b40c0c660f40e40e4840741d07003a6482140c100d0380042e240c502500d00c9141407180b2403500880603103c0342a14504000318a03400a0703881018050b404403450000050b1740402450384034620a1450a46070341351101c291306410094120003d0104050000c200100e600804210440e2524901012004801d031741b07e5120f40350580014190a1f40040c00d83d010680256041b41c2143c402c9501441102c3e06001d02c03012030055142c0100048003000c140000302c2c0b40780b00504400b64054100040482c0e40798001000040c003c82c04541c1da60315034030980104140652450350140041c1d03007890394140d0f0341c2c0e002500c814041c042c45090001c5d1509049407600d41802c654117481000d845a412540c40748030307840c2c00340700c24801c11561 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 181628570 1250 181627320 181627331
    0x907021c03020c0f15010603020a030e0d020c0315040f02090619061d010c0804030602030924060f01110a02150f03010b040306180c031101112a190b0a02121309 70
    0x504c18001740118080034139826012031030342000c00880203036110602600415444500018041e002442a80d005406c9900203281501440041c5800c09045407015000700c41c400d0100404102244001703065950f04503154490741e60b40c2000500d074400030300d9a40a0400300103401003061500030900d0819045403815800c04014144011209003034002801020040207000404c0011416006190403c0900017518984516442c03150100d644900c194182010302800784032050814140c0c021880c5801e10b8000e1010754410152661a00710340c6009016010088224918203280025603101411034444e03aa644e59442040da142600640019034242d49401c003a000c00814101d11501d04580c00050711820034515110702181000c2040e00b181880024540303080d40320710922200d6084800e56004003540301c0d40c070940380c41403245106190b0041201d01d5048000e035240c0000d16007161020101c095881c0000f00c0100c1c100141a4500070071311b000480e1030f41c00c4041210465041c0d070040c4404100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 181629820 1250 181628570 181628593
    0x90105060403081b030c060906040c050a03030203030f0a180c050901240c020312370c0b06120a030207081203060109090209010e060301120614090c0907021c03020c 72
    0x1a030300c12840700030031540f02040343c01c40d01d0310b4008480071101040d0f019641803101103c41c0c6403c01d4011144404a60406020841002042d1101c0700203130105070b840c80102819964003030741c1e038400030300340c0110b01c0c00100019160790340e0350b00500303050005185c880ea514019842c080405408038050345128414480010501d5010940092060500c261383c0c810001c40300314040c1d404020502c016030b054005c1034039080f81010510014a201d1088a0000c1c9400c4074403109510203215004070404c5004455520b107650301d40c031030030142009400040980302e80e00d80200188048011040c200300500a1040101c180b507008a10070080700c400406035100645503044112003071100f00c4005006c00c030401d0080c084043c0a80c058000850f0604219040c4440c0c60006050754109034040c02c104000854030300c00b0409180616210031942640009207030500d8181c4544a840741c248680c09000c80f000013a80c0c1d54401c01049145480c0001d15115010390042c004000e540b01d803140c420035108030313400800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 181631070 1250 181629820 181629829
    0x3361d07081306020d020f04180603020303031801152706050108010308030a0b0a170f0601120602160609030306150f02100c0e0402040803070215040b070303020d02070b090c090105 79
    0x24400e0415a54a81c019035444081078400d00c1c02a00c240c90a81c0d0910084013203403814801400203190101082e6102d84c50040140340f5036112600c0300308102d0805004100513140001030701d800006600040140ca0030b08060360703005183c101030b0309100c0c13081188001066170440b20440004070349840c480d81641c01d0410040c05440551241c540014070b10001000418001b1020f16005540614040303031201c141030000c0d01c105c1564020a00c030640c1100d0701c2421000c01c100751840a603288000c3d008540c94807000b03070300051207007202410f22500002d180c004903118a84801010ba400401041000c2103404c0050040c14640507441ea9440080d0703503410550b0180100c003400c0102c69008100081c0d800001c14090030b443c102030741c00d105440c45030208036501c50000d0005416414000c5445107154010010041d1b0042d4209500c81810407042c400000c500044900c01c40e0581805030b582c1810742c4201d0024407542034090714030322211061000c0003c010844400c403120031510900d1590300c800810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 181632320 1250 181631070 181631129
    0x30b01050d1104020a030f05180105100f030609021207030c0e06040203010302090402040b15040303030207050105060d03020d03020f0d1d060a021330080406080a09030504030336 78
    0x1500000003205910b5040c9850340083c031405209240210b01c103d090b010321010340b001911702c3e1384042d1107001031100618003481460b83c0b2003880b43d400358a10b450030446c031048000c1070001819454803034032400250348450707502c030743c48068040c02c07142d11651380d04145020050310b0003103402c214180030209060b0b181030b009881c162600145054001e0700c6941c2004003c00310780d40d80580043c0c8103055400035281d00f07000b800c000d50194a0250790f5030000c0c605942183c8000300490700c152600312100010a500261042c00002e55060059952905100c02607881c05280c07611741145040c00601d10002c0301d2000011541c00c001809c503012a150140c0c0d08082e4007543d80840b17503080c5002d40400080c48070300e0144418219038940b100395905c000744070182c4018012425103c0c024006010010380b6808001c05074820744000081041000d295401800e41c8135510000d403c0081d0203812040e900c440d641c0e0119100540d1000c0128400c46844401c0035018502c589d41540c1e641c10362543d07200da00d00c081d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 181633570 1250 181632320 181632323
    0x513110a0c050d0f1710050915180903072303030c040806060d080d0f091401090210090503060c03090309030d020f2112040f0b01240519031a0316030b01050d 69
    0x80e07030340c1029807002901c0720b05801800a46c82d412100301c0040d90f0703143c400c00e1501401034445a12072042001c03080c052003500040040b4140300e5107108100304c5090103c140c40c1d506e640044400e501e858211144502280c410000c0350050100106108400407240300a108503001c00c410303903005070740d24005c2105c070f94041e44002e01000c05c01c01a18015540d582c0c41a4081c1120040004622082e41c8410100100c112154007203a0340d07440f01003041d072421101d48204c2d100035180c50f811150410003c25116203000e4120300180c0c0011000c1141840706205407000c07000301404940c52070222903c0256680c00314030702c41c62035000315909a250628010301c44c0000e0184046020f2030504902d070f000d569140010320980702205441010f000003020160105e0007080344961000c104000e00e15421b0200b00034185071030503c00d080102004000d00e850366808070404038100012880300920000b20250840521180d02d402040c010341c0e80d82c00488481420b490052444628984c0c0f58000e2000301c2081000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 181634820 1250 181633570 181633577
    0x5040c050c07170a06090807050705090c0a080703110d0501030c06090620030708040b0a030f0b0315090f070801050f0105030304120602070305070c0909060b010302040f0513110a0c050d0f 82
    0x1030140c0c154040f10500040282001c856141c1010345868040f55403128080760f1a920015009061000030046400030701400c0300c49141a0402981c512006e2080d41030607410300017000001844039000313a1100320351052080c52a9582c54030070303a10000a003000d000403208981da000012481c10b204000140030b8070003e8444190a202448901464900d00204038001d4070081207008005007940c0041d000600c0224085910b8031180c0c0c0010f0280c0c0e88845003842c40d41e24005d19001c503590002000792072480c50b000d406a4507110300a25909020050f0064101c5100300c00380040d08050550140344035072402074110301f09988802c2003540760300c6035104010f0b540702200c40d11340100d00280d004000c0c6921909003d0710f4a8001d40e924040810f0640c0071032442c5940750320520501c540d50140f0040d60000b46011440e19061240245804180e8050a40a1910690303075145400603a03005e6a05c5d0315541c419240c03190381d120001004c40702c0095048415000e054214200a03010f02d8010010312503d45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 181636070 1250 181634820 181634833
    0xa0b03071e0f0c0803190c11010f0203040c0b09120d0f020609030a08070818160806060d020a090c020f0307111c11010309020d060f02030a1a1e13051005040c050c 71
    0x45443d86150006031102e90b5049900b03100e040c03074884602c9171488507e40d0742c4a5000110b068003c0303500f142e4000e0005016580100100070000f80703e4441e50b0150f81e40038680301e8403260310401042c0d814048840200c00303132180d02000b8812a8200c9049040312401c1c0c0d00b12070311039031104016a01c84c00f520302c200011072540404540031a0060b1105540400508086109001c10540c00c500d009030452506005215100d014043c5010520146a000d5030940703a001c0200310550200b140d104141c03080440055540b0f60624403d4802e1104000110301e02080300e480d035810342001c502c901450385650340b1501c54848400d4806000f041901c94503504041d032031400c01d1187c401580507240c101d5049a000715030566030000035420b449807130300007040b0140040e200c2c82e144071804112222102003050100b440c1201841d5681c801e81d42211600000d040ca040400280003c1740b51250011010140c542c201000c02420b060031613200c0044803422142030000c1950342d01c058500e88a4200c0c0c8070020380001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 181637320 1250 181636070 181636073
    0xc05100c08120403181d07020606010e040e0111040815060d0809150d1407020601050105070507050f2706030111121303090801180203010b0604080312060a0b03071e0f0c 74
    0x260041e54403038000c2c141403100501c05151000c0344c541640150a05480000c610714007824106c444030b030f002c5850300040401c2e00b00710b00064805840c2040181c4926104c03625480d410300e084d00546d015030010180240c9998640d00d1458035902210b030360324032507a1190b001400a01e08413080f0181281c01609040ca000e80130020701c51800c0700b8000c01c0032100010800403c02c0520742c45030020218070038280648609100e41c0c02410442c0603032005042041c24131840d0007180d0041403001c2124000c65059540340c5000c400310b078044482062402240c0c1c0d86000c15000d019011382283c1c45400101c000b000206d10b101080d28941c01072030b503040700c50703074494000440440d42c450680c1e040e1406030400000d059a9464202d00f941d480c808400f05103c0b64000000031820700340108208040109e81680c1400c1c10005244c0c2d690040d0b814807a000c980580c040780003a2600001d1102806030711036240d603a0710f0020703005461900b1320315184071203070005150448803038820b40321409a05a5540c800e403000050707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 181638570 1250 181637320 181637347
    0x4080903030423030d2105060a080a0305070c05010c080d053c0c120f0c0903060a140906041e1401051513050127090f0c05100c08 57
    0x40800a40500c8208008070768008102c0c951056002e03c40d46049010107464285810203421030385000a01007818075080340d40f60105000d1144000540b4002016514500001c009100c91b901101460140c1c1c8145424594004010080140501c15034010141e4031401101e03000742c44400500400c400b845003800b000c40640159400c16002030101c203021005540d000d41c82950041d1500d0b0041041d07800c400c0c1e00804101544d0710500490405080001000303e2880a0348020100850b400014001410b60303242c03101903a03480d901c064100c50540c03a01c01c43e1340f001440004100c0c1180c03804400000c001c000d002031418421607014003c203800c41e043c1e4544600c2116800e04c04c69a95041c2025061701c10000d1003550310805a20341038410040c4464180545865480942e029090030000180f00130300c40540b1040e0085410f00c0500004d502510100c4014070031441b006003a103200a2518040c0926250108141c0d4421a07620140044050090707078050301c25100100082018004110100750 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 181639820 1250 181638570 181638577
    0xe090313030b07031e0501050109080102120103260a031d01090201120c03060503010207060f0c17060105030c0705030c0a0215070201080f0a11040e0f010603271e03030209040c080c030408 82
    0xf4509010904401c102c1c0c1250500182131700300d001880d55035004200d41e41c3d12016020041c0b246c00700842c5850480000346201c1c010501004d0716925000c01029100d44c81d016080c1c07280400b21301c3c600d0310341c0400d2100502504042014600d1140d04045000c4406418440c820140d5816190140310a401d0b9150b28003400e88158141c05140e502c00000070780b41c4033800103005580c4202000100c100c41c102d114011038035201c501004020241e0101d00d02e10b0f503015281d5030041801d0074102d44030b86e05c4000040c00c5108980c00245240800f24032040f0201d00043c1ea005443c0c400c5031800031849a2003e4402d09000310309010340000c1810002c9414581c4a00c8020b800c420701481c0881d030034000f40c20244550b400f5522090828040e03e01f004140480c80c0551030141c1140d203420320070a00114403040980c4080c0701d044600101c52b0050b1401c10032505c50386e0300700c10081008224107512500b1f016000b508200d08560040d804c0070101100d0b14412801d5501c502044500c2e9230444c0c0781d60b22240c04941 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 181641070 1250 181639820 181639831
    0xc0b0705090303070501050613050c0a2a12110f030913020c0102040b0409150b04050f01020a2405010b0a05160606081204080c03010e0309120a0f06060e090313030b 72
    0x20040308010b03880a00080c0b40090088002242605220741404102650504c10070840c914140501000040142c102c0780402c0302c42c43c000d014001c4019100c0500140c072180c0c1460000101d410604004091164060440c0d483d218401401c01011003140c0b18100062151419041000140618500a02c0111102150150050800d110110756500720f03401900085034403100803904214410060245800a40001d4078401f04a8a4000958258050350007001d114200418224029034420850380035440e800054805d0904140c0c2884484245540072190429080200218801103540200c0e107180702d20350b58003440e00b440e50400c0d0220701c1d0f45000480b0040e4a4080000d0512010010f0021044e42c21050310b03600ca10306a6220b00d00801030b50030034000d07410f0094203843d2400200035034620f10410356080301005510f403102d50a000b0b00413001051325400c07805010500145034026400d40f4045a009001600d500484903500c0c06010f0325030740003100c0300c0000e10006480c080c03041d8105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 181642320 1250 181641070 181641077
    0x318030403020306090102120c0a171e04030e2107170708060f060f010c051b04021c02030a1413080f040b03070e0103061a191403040308060a0b0405010c0b07 69
    0x1e44950001c0e0400f0400e83c3e200c039440e034012404520710709046446541001e040320049103448a0340c2d001031304c17400c2c2003410700201a102d440083c004142d4202082041081040311011500c0e0a14000e846060984032650091002d40c2183c0701b00300c040d030307041e50f080c0d00701c48024126507240002c0740c4080920042d00010074022404001840a0300300a6a80248035840c181440c514000d024031208512481180741000003a40000020079000300d60b0020755031403644c006500090340c0780807502a00c103090385050032040758914002e5004242d409075000d000220b0092124a2500e0001b6040400581d01c4a10341041020f00c0000a0010030007000013140031928141415030740d59458a90740c100721481da0114040f10300c050150b69151040402400081d400b10038a030901d44d9000710f603801851030780da040e0b618140d45098482e0260201c220780c43e000166070380d40d03490986001426440c043d14076501a0784c20300004292022240300b500c00392001a501d00302410341c1a240e0b0540043d024003580d050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 181643570 1250 181642320 181642327
    0x60f0d0c0c020a0602070302150f03070e0301060f09050414010506010203030c09040b0a060f0305180304090902040f090c0e06100f0f17010605070c0803040b090d0510090f0203060f040305031803 85
    0x6840740400f1100034900740d005042c0940c51401441244410300c0720010381d104080110180d50307481c60781a01c1e041030f4285040864041c07804082801005d41d81c100312002c1c020040c0c0060282541d070041c40c4072b00e10032105044d9031150402c2980c02d0320400d0311000e0141c2c02c1440022580703070f100405050710200040001c0f4071206541c010440b081c4135504908000f490700091100348940501900317820949802c1e84a6914540381d51381038890003a4000d80c0851a100d842e1032084d559141c00040d03040002a5041140c0355207482c0c9280803c82d20f11907110366080560002d01c0519110000810740d51442d04e80c4444030300d075024220303504d800081c050001c0c171484d00c0c081a0820306800140380a011a612103665a55581c142080318200c641d00c844026030040006011000108064510801c0203544076858141140342180c103106026007601c42c03961400c01d0303d106100b12600e04010041c0242c0c20b40b52207407202651311001c00e804840c0500802d40400100f50000f1140b8002100041e100301903904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 181644820 1250 181643570 181643573
    0x305040e1905250e0913020112021603020f0601050102060c03130f050607020712080d05040804080102130e01090b0a0b0a3c0206070f0e0402190804060506060f0d0c0c 73
    0x202d0302c05503000e21240005034a600d5880300c00380c10106107240b20f030a00b0b28641000344005264001c004001221301e48106d0011811a40203104542c00021141c40540d01e8002c0703048480c80d80c81444105400601c501d1030000c0807030802040c5103068500690160206580f410b5160320360b503102400215201220030b80e0440810001e401c0c0e0403200d0720800103450241411a8000c0c50282ea5801a44617004000315032000210b5450841d4400010900042855512030038850702c7c6000d96031100e0401e50000032201c43d00e515000c1c05a0a07141c1c487d03400c1d1100d03600c45014404450000402541201c0010f0040c4129280c04018019404140c0b9044181004410403c03501044d009070010b0243c01c11000380c40d84c140c01408030700844030302e880203108510385403000601000e080388820062013000c40045016444907011a0617141c4290343c210005105a20010304801d030031141603560b2071070b0a0100310306103402411034480340504422981401c01c2140c284004040b060905c4040c804007040c102d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 181646070 1250 181644820 181644871
    0xb09040914100b01080109060602060a0c110706020601030510290a0b040611060921030718060c03090623090303042c06010503240a0305010509010c1b0305040e 70
    0xb01265060b010903107104400000d4880311040c0c1000f4812814210140f10230361b80028940d912008032200440d841d000c00c403060b05d0b955500301e5090030a010b40d4002190f001d030001820f504891084080b100030103851056403044400701440300b5501c070307032410030030b00400c0c41c1d44200c00034510020245080309030f542030b0b1340b80c41e54007513400b4802180c11024141c0d840501400701943c07040c0c507030010704500524000302e804403845143c9c0f8000c2540b0003001180e00c2c00c1c40741c04034440301043c5510f029440d944503807000c2c1642044101c12000185c1c03104c400b2a21034468401e55102040402c050702980c404a0082201078024802064140c4010720001480c2c18071107408400e0300c0340c40e0904c0540800b8400c203040d0782d64001844941030041c10005c6c1b0180c071f00c0032158041c203840344081c031054682d0b1000024118000a6201818030740c28201030004895044d4090100f41301280c480f000314220300c00d004a20a2140e5001030040398060101700410145501416841310300c030820075410681c03d5a002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 181647320 1250 181646070 181646083
    0x609151f09050301180825020303030103031707020705030d050d020f0d0c02100908090607080918060f0913060e10060b250c03140c03010203090120040b09040914 71
    0x52001401d121001c00442c24280b04071140001104003d603220700d4030340c541240c0c6120351900d1404074443c840420030042d10100203440c0c659401030589541c0d594034100101072600308c0b00c90b20100f0900e0004a00e6460001495100301c590203400380c0030b040003450701511244c210501d4040721b02e070204a02000000030707070000c1124800380440001c541c004075400070328080361014000c50503031612200c90f02084040d420303140d2a00c011038440c0d607500032a18220045004604240c0d0700f08a0030910b9800c040008001c5c60300c18401075840040320410141000b1580d0340c107903410386403d52610500008a2403581207400c00300030000c110341c1c03001100c80c5050116103a683c824140400049250060b8400540608104201c0401000406030b15038071007180d5a40d403403200511524040c40724070008602407181c1720008800400854803403410300d0070140a08100382504400c2c0722049895042e06c505582560203030360f541624070b41041c600c5d80a00004161407072007070350210100403151a42c0d40007048035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 181648570 1250 181647320 181647379
    0x140a050a0c240c080a03110a0e0306100b070b04020d0503030c04080705060c101e1103060310020c0a0b040c0302040f0b01030b0a05060a2111040e0603010203060915 72
    0x8003220501e80b81007a21110b40000241400d4001c1070308803030007903074007a0b000041030b44c000c03900c10740e10b034550030003070b0024001c20b6440c100c1008040f9440c0103054002800545e102d07029419900c9603600c07841092030845182c020350034150f0003485400042811210a103030711500c05040070116007169140c840c61504120b802d52200080002c05100d0302409000080045c83c0c10b60f0200d0910740045002a141c1d204091628001d560301c0c014400755411b1035021501c01e1a840008214a400041a002050340111440c6000c1e10512500b014442980d10031920f4210301300c000342460b40702e1756490003698070002d0400d84e221031401c071010002d60b07111705c80e1b00d602400040d0002031100b0808005003d6410443c2d1003840303044501d900f007001e034a490003100c00c00c01480c5445072071102500001404c426030317000601311841c07501d1603005215007000020b10503161842e03401c40c040c3d6070307081c2058240e1004444c159007003003454000c10380c25403d4050b800a001ca00074603075500e180880c461160403078019600d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 181649820 1250 181648570 181648583
    0xf05120304051609090c0501030e0c130b011e230405090a0f0509060129040b0d02070b130c0b0903011b091d01030b01060c020d0803040503040911070302060103140a050a 74
    0xc1000d095104540e01c0013400e105a00384822003164840001040701482018145612103041d2606990207020f01058020002c05c8200c424440400f200d0042440182c4540459404554901c20f00c403401070011000c410ba503a02d03681080d0080031012a00c0c501003495a11104c1813101040561b01d00341e40381d12400d102c440c0003540f56489410803003529000b40c01d861705a0030250051002c882540c224803c404140296291402c0002e6560f036011310542c0c0c4202d244190104e801100038025800600c1560700415200b00e00e6114007120032103a041003000103125a41e288002c10052450030090b080700310004000184010b521240030304410115019800000d03503409041c0401030149102110702d00d01501d41c2d48107981190b0761751001031010b02510080c410710300880b0046545524032000720b15400703d915900c030b0804c2d107090303030362500207010313240c00c5a060191020120a0200580d20155027560040c1426403a44e1901004901c12065240310f0b8010344000d400070600030488404168070030302 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 181651070 1250 181649820 181649833
    0x30c0613210327120305150303031608010519140a09180302010e010c09140307030507030c150c1e06150308190302090a0303080604021b010203040204060f050d0f0512030405 76
    0x4001c0c1c8884014819505040140c80f00420007048074030743c0e0500410040d050001c0d1544900029522004c101840580e240c400003007005a07500c80300495402e000f200340c848045a98803002081204080c4c0c40c00285440281c4070704204902030103007280042e40003e0280c0404039242c10b40760041e501780d400c01080c60702000c2261801c0640c2489084100701c5004001c0040007040c180c001d094211a102e001b0700030580c1450708000b950144900b034020b6a114041790b0ba1a5902d10300708000e8840c0780308680c1000da4060380003400c1030158510707084650340400c255409107626418180d200b81818800d0340d565680c4c0c040d28403100e0000c041400918001c0254584900030340926600000580100310209401030000c2c0120361100c6002e1010749605043c00541c03603440c00b02040090060b505881540c81601c01c442c6804641940290f0081d0300903074060003401e8488240340c4140c05540b00752a0051070429201000c581c914565504080c8a0317810f40b113450300b0301d80c007419a039001038409640c0c90b00f141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 181652320 1250 181651070 181651091
    0x203070b06060406050904110d05160f050438310503151801020d0b1f05190c06050403050909091209010e01050c060c0a11030c06132103 60
    0x21214241e111204903801440c00d8207040b4002d0107030140c1c010306402a0f80740d84a03000040070442c150342c52481480e2007000980340c650b20101030ba038000c810704004101800a2043c1c298403500c103ea05440b0040999540c0040e9071071294054118494044902520b01d5088244250b265006044d200e00b0f90400d8441180707410144050412800c1002920b03404e4404c0c100840d440105001800001d2444085400da032003c40499070682c040c2c0c04544554030004000c51221001d500c5601c90000c26503440b84044000540c801e0100d80403c65600880c4040c000d0003c0c0c0a0480d0b008401080c90340b40000044000d65229403e840040e60100c010032804207444a87d42461130546034044181c0000340541882c0c01504009071141c16402e60402400915000c04c99029a0803203100b0800e02045416030720300050354030140e40091644100044200d100fa40c3c0780000001603400c0f080d03850b4090025900c40000d90303a010180c0040c11200c045264110904103203004003500740d40789194401240301c4425 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 181653570 1250 181652320 181652333
    0x70e1008070905120d03051902030f150d0b01050f0d05010204030606080f0706090e0601090312110c0a05031f11040b040305121204030e030102040b0d15080118060507090b0307020307 80
    0xa640005008072001d102c0080085400149a030310316409090000342e80c0c9a600044071581c200e030108c1500c140c000030500150004c003614140c490003641c801d01612031100300421100c0800d100c80a41801c80d500c006100c14a888000620300c008018900c0440340c080b0340c0c4903400e82e00a0b51040c1e8030565a43ca0410541e003041c02418402c1072202c000e0304500303040c1031000e0700c03003440c600035032409841c0d500016500d0f9002d6800c030300155410981c43c41c41c04040300320081030655000440070007405100884006410300e4541d00003950320040c09459044100b2041b11481015401c03414185910348040c0039414103050000c201030300c04d981e400c40c2c0ea00e065081061400005166850001504015841641c1c6000c5501c90304030354949065403202131000c0c0040d0280c043c0d5040b054403c0c41c0050502103d0032144d00c06500d0400030815103032010360b20850715080780c0310071410410b02501046030b1000605140d02c4958044e9140c20030076805615031100c0d41c084d800868440300583c1c8009010800d0244 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 181654676 1106 181653570 181653587
    0x1060e042304110402030114150d050702070e060612070e03150702010603061103010b12040501020c06101d07140d020403020d0308040b09120f03070e100807 69
    0x840c158100e55030003058a00b2910070541c80040f2005080c036000b03890485400444000f0004005000c0c8085882c40c900c500c43c8100c010040c03061203503118402c040c043c825560007016664107041003500e01d8140034100c0d9126210900403860003101c0d055505a00c40d03241e241c0300e91812506404a4944400b0510142e180c0f02e8107401c02680c0783d81580030743c0441c3e0140e00248840b5100403040d00440c4030038003940340c13940c0080040c000350b0780050030360b941c02c207100c4e500042c9400d480c01070380c85c24404250307884400c20440300d904020001c150203007841c22403d04011b004003410322010180c640590312060040004000c01c5103c9608240d078160783c0150b801406150008043c0c4c9002130038241d0884089400802c0d100c04968580c0300014a60b0590000d04819840c00624440645060300020121400c02a082142e842207844039111081c0d00034880e01d8160b914108041c001d0100714 = true := by decide +kernel

theorem cover : BRFrame.Cov 181474820 181654676 := by
  have h0 := BRFrame.cov_init 181474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 181474820 ≤ n) (h2 : n < 181654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
