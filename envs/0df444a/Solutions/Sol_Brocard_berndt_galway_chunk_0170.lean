-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:14:27.091606+00:00
-- url     : https://prove2.me/submissions/9e8c2645-bb9a-4a8d-a2d7-cb1f98c84c21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 30395689 ≤ n < 30575545 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 30396939 1250 30395689 30395731
    0x8070c030609290403030c0203042103030b0306071d04090204050a090201020c0604060c0809010306051002011a06091e060d0213050f03030304170702061902010f060e01080a020108 79
    0x4088140d402911001e07a030307200000520082c04100708003581c0100280026400e240700c08005202c000d00b02804165a881c00da00364507000b002154040d0060b032043c000b00036501103030303143d0207450600b0440000c0d08000304240d42c0e0400040950040a4030749030302100d100b0340c8107075010707001e4816146944a9100c003400c2c4c1c05a2100d100f018050521884003141c04143c03400007910305000180c8403030281904110811030745501010300071034181d026070340703540e43c607440c0c03004034080c14140c1c2100e50310107056248000c4054056001e042c00d2000c1100c4040da4a80e054100710803409084600c0e9048100c504280a50400a0081441c40980180034904006001c101001241c0000c9642d80350707543c003004180010b191a903c0704c1c445c1c206c00c400442c5107141541e03410a4880c04251005610380380803078803000715a105815101120b450b540310003104d180c8580300034041c2082c0c03041c1407003461a0950214841200c2511103040e074500070000c007640c0c21181d004440c3c101c3c0007010f286545410f0000e1b002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 30398189 1250 30396939 30396953
    0x1d040b0a0b030a060602070501020a0b0a060b0313060605010201020a0504050d0302210705070e13030c140a0804050906010207060905010e0d020301050117060a0507090e07050c01050a02030714040b0708070807 91
    0xc09040d8550000d6202c0c6800e500110450708076400020541d1721041003001503a0f40010310402d1260712a5124003992101940e1001829054005004030000032003000701c0e58182e0409890f40b54044d10080c0405036480006a080b407040c0d00d94480083c20401050005007810000107084500c20704c1102d01c40c917030000e00300903140340300a0000145070000078028184941003142401a0188e8081c0110b10700380b580c050000520096002410b12842c440d00f541030007540e41401c0815060385055500300580c6140140c0140d00a010301480785600202203801540300223a0342c401d03180c03140c40729105c00382400c0c01520441500c22441d5400540c0c8000000161800c0c02018024a03000a211001c40c1000600c9824400002c200042c26450441003054070383c1d21030012404c40b5160104070301e15031140302045640e8801c20204204641c2424207101002c4d04503402144600070a0352610a003101011085040f072045114040440c88103100341404035050400600805100f04507241c030308505540c1d604 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 30399439 1250 30398189 30398209
    0x60901050607151b030c090f050d03090e04030507021c051e010603020604030506160c0b0601081e040f020a05030a030815030703050a0312050c070b04030e010908070e090f0d1d040b 79
    0xc00c0603070f04c0207121420607090302400c244103005051501c090750804004100b600070074864075120b119010165030916014855020180c1020f00b414011481d02e07050142180c1e1114a00700d0103808402e0141c9500e142c0b051982c1708490f4020007510000025004011600ca8600401c071840d5503560800401680e498000744021f502c0780000e044030b464005c2840130400360081c0d5803802e201540c40d4407000201072042040c0d00103070908101410740ca4801101e06801145001d10403180300e23900a00052007040c20580c8642403003250b1141c0d6990b01d55040c5502c48201d14802400f00f5501c502103480174518086103450381d00050122030491781c0e40d803180340c81c1040009040c1d0100c1c22200c2803480010041c010316910180841a00c0d10b0803001d03503111032520600400180070031143c00036101050303200d0840032009100700c2d01100d15041d00c40340e800c06400b906856030300d898480e003003005007130007004600e940f601d04c915210040c00c0c0180225507100e1801058000303510a035510790140a607030b00ea403000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 30400689 1250 30399439 30399461
    0x10305060c09030c0d03112401060806060d0f0204030b0108010b03010e0321090f03040e0a05060f01050910090302091006030e0f0d050c0f0106090207060b01080105030c0607060209040608030a1706090105060715 92
    0x110104082e9418107023000345060304008100300c8182c040055540b210803c44601c2030481000203603001100319040001d000700d400c01498130040100010300d036081500981080c1000f20003c01041075900701d0607990f44150403040b14200c1c00010540c1c0d0503803028030081d43c0000781c602034a81c8803a80a03841402c644c840d03044070f00b003004094148901d01200e40306040c0d01003401d0314212070728100000017038440c0c00f950b06410f02c02d206510b000108113204402c01b000940e4050080c21082c01d101d545880301e02101d010b4140003074036225001d0656000003c9442c0025201006002e4003903861004680b140e010541c85038992203020206044164244604001410700f204016210f0081c0e10b4110242d5030b502c00200c0c10400d00b080107204079900440d842c0440c540c00c0b0381c81c42c0d13200703801d15041d0f01034001c2e0482e103a071061400c00b000445540c044010034882000e5a0b40600108900003240f82c400c0782550312a400c41d8504005100c00e00f8141700030706219000c4d00036403c03070102c402024000d8070305025030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 30401939 1250 30400689 30400723
    0x309031b051002071a090d051c0902040c020d0f030b0a05090403050f0301030309050f040905060718092903070b0306010f0c020d05070302090919020d0f0503040e010305060c09030c0d0311 82
    0x4020343c007445e49042203401054510180008292903540207205018510041081081d01d0034107507814856940320b42d01855000e0001d002c0d403d00701c0b5000e91108100f84099002c00e40c0c03040b1040281e031107407003040e62109000700a1070343c035401c06003070254181006104509000701001008a80741802001c1c500940c401d5480c0740300541018107100150f01c3d000e210710300650500e26800e001079000f02c1c04a601182c98903110010040403000e0161648203603000340365080c07a0074042c2031040e80801e059410304082c100341400c5001d111040c19519a032070b00c503080c880181800416120b40c8101608446d012092030b20804202007030b0000b8200d442c2e841c40840701d540c4004010811030503c00019544219584050600c001110703441030759504c1c040d4402072080c2c81e040c80d5142040040d405019505801c00101c03a00d50340c0356001000c0d00351003070000355028850100003032500482a0129916040702401903d013560452061100c640c2d200c01045051044441c020016200200030203000f1103c0c1090b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 30403189 1250 30401939 30401963
    0x1407050307080c0f120304030503040611090d21090e0a05061f0c110906030a0f1a0f0108010f06030206040b1c020f21040f03180503010203040f02040c0309031b05100207 74
    0x103141d601d000c2c4d00c41c504450b0038009208200c04a274002d400d599000b9006900460160003110800c0c0c45445040b1049070b00035008807109090010302140034502c1081b201146001d070b000c03014160340104052150501c1c11240c0400151901d034140c10194001c2d0010780002150448150f15102c034030840202480040d01e01000d5105009070400754503d00c11080d1141400c80c2410400301782c50b54903800b8082c0910780c2c03612911007000104501e9400310744a1100e0f0700c200f030602c002207002c411000e115020040d828442d010640040034882c40e13003103c0e40144a1840c0074501501820660001303560005021000d880c501000705180c0014000e03072440041540d9100c110175a0701c8210042c8a1040c440315016004110018010500805150360107080001e0941303902c820301088103a591704256019400030041c002000a00c1b000b085c117441c1300311410300c850f082c181801c070b04a44890001800047c003c0503110400c07000250784c81301887c050401c3d9144034991404032003c3ea40400421661640000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 30404439 1250 30403189 30403213
    0x403020612040b1b04060f020c0612061201060b1c14040c05040f0209090109150305160905010e1003080c0705030102030c03010312020f0a0303020901090503100614010f1407050307080c 81
    0x42c8560040c600d29081408080761300219145004a014010030300100134112121030303008002d03401003032800514059503500c40c02500c1030003103015100c080c0102d03045042d0004200040c0644d0040d40c0e081d030382190412104040241040311101d5110034a01c1c1d07070300b051a41c009031a018003071095000b500c1000b01e441c508018002111344004881d01ca4610500100ca096510508500c1c115400001c0100d6514040300685256001c10760005201c0e12a45103410314528040d286034007140c401d1601000580c1c1e90303c8800c1c5041d5401c843e4002006d0b96071000b8000980094090090b01800b80100c6424a03118000300e801c82c0d1003980d51542c99800800100f0801c0380b43c01642c0003609180c80682500e07516500501d50303d0a0411004041c940c02141c02d2100d64411a64440140002030894407640c0e003405101c00240b0f4180180301000060401c0120294041c00030002030038030700d6880034142e00602d54985419000081c048655001c10044000404c50310005403210480800140504807184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 30405689 1250 30404439 30404453
    0x6050f070e09010504020702060f0403061e09020102060f04061b0c02040b06040e15040b04020a030f060501080105060f0309010209060406050a08070c1502090307090e0a02120601030203060714040302061204 90
    0x1414901000034448500c41c60392a005000350440f04d003520050f880d2006440052014003a40c62609c0304000003003400030500415400840c0c400c1a540d80440112801d540e840050ba01c000c41c011f40580d00100100b409a248014850362040c06404005a6019074414815601716410721402c0021044003006066240c0b9202d41c007820041222618039040c501802c411442c50014400502c03681c0c03108c0e40d404140c4503070700807807101180240115a250100781000c0d0042c01e00c3d047c0d4910a40c82d00d070300454554000c0708024144d42d8010405810441c00001c0c4545983c0020403001c2295000e000001d1140c80c0c2501500181416494441c0c4030400c0390310003407100780c4c010001c0c010003681d21b24100c046100c405a0410000c0c80340307409680c07802c00a000c20b1a0451590108404501e8140c03c0001c00c3d5010440c0126030f40300f150701c07821080b0100841a5a03000038040a907158002e200425519809800c030700c400f000c600202c05091030b5032034001410315004040e084280f43c2e04c50302040100070a07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 30406939 1250 30405689 30405691
    0x30a030b09010b030405120a0201110403030504090509070509010b070f060e060402120316020d02010e0d080306040f050f06040221040804060f0201020a0c03050309011d03070b34050405090406050f 86
    0x680743c5054110725050301c6003552140703a85001c031084040010f401902500c00e401c080403c0342800c1c0000d80e21b81d528900242603900c980320f081490b0b480c0402003070280501045403002c844004080c03c1c1140d08141c0c40d001c2c41da0001d0400c8914010b141c1640740020024064048804134a40107003020380741070300520440c0010341c00d1000030782d0000c0008001810920081e1030740d00341c05450241c0300c0000c51005843c0c80d040024200c0e44201c4160a400420100c540114404e00e0700384c07000d0020247c500c00c028162442910747c003441c4030302c100009202e420076902501e075009880c18014000848050011a4284165019074441c1400102808401e03040301100c4150800c1d40300071481e01a201c14001c101d001000c400500300b140000c041003008c10250410500851588001549007501e19021a600c0e403044008480c3d28400400007000e000c100601803825030304038544403035107043d071140080780d0b006401d8620050180031f010201d840d884c0c07055020b100e1807003000005114105a840c0c3e464141c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 30408189 1250 30406939 30406949
    0x50903180d050703031b060f1a040b0303040e060301020403170d05010e01030f02010807030617030c0c09060d120903080c010504020109050f060406140d020f0a090906050d0209090f030a030b0901 85
    0x12586860000160001070f120304890305460801004403924641022403c0090805450141801101c2d9070f4030807190711800c0f41c1056441d81a0941c05804240015111081c0007075a03d500280000c225000c040d04845a02c550000d000500c0c0584a96405201280108091003881000f04540700841040c0c81418050b000d00c2100c10000e43c5076035a045011020200000d040014940114005a00982149024094107071800c0c05071800000d075580e40b0b400c100800c3d1100e10070140882c2c0325040070354409003c2c200c0604005683c1d0525103610018410441d5200100244001c0000c0030030740300400f800a4001c510000b04460404d80001003d01941e40c105510407035040300190300940c2e6000843e4100d41050078402e0442e0cc503004001001e0003540c4840d16040d0000807c0139041000b800140011506904d50340c00d441c0d140d807050030031910140202c076000742562000c02c025142058201c1d60141d000804c441003505045031441c11900010841408a511601610b0b110b2418550380d40c0501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 30409439 1250 30408189 30408199
    0xf0801051006050904060312020a020a0e06010c020d21120c03111c0e0f0102030906070503150904020402070606080c030106050f09070c030207120503041503021e0d060302030105090318 81
    0x208203580d040d540341c48680305110900c40300180c00c2c810360304d503600000000c50704055944000064058040e44a9031101c03002c9110b08080b62003c1032070300000008601032901030791f03400380c8404158244201d4100c40324050b68a010049010200440e5044641d002707408290b82d9610050070104111040e1010300c08003205050410f101d042d502e8002a00340c2d40c43c0c0003003030500441c00c804a0340c0f0300028444900b00d503040b400b50422290030042c3c1500114043d0703030240200c4106580c2d0369070883e000e0000380ca40f44000c40801030550114601101d01d07035000f070300081005140c4002641e44100300c600690210035103401421204110303140a10900006203802e40c0e8403c0500c291100060003800014079142c1800004e800580905200700207000140c0007454140f5040c84580c1003041e0b5a820600c40c0c10300485142810301c0b0300c50720074003c1d40e45101604031003122101a4206031603494014006601c4001d45c0c400c030000241c1d4003400380754000c111140145035100d140054100744c054040340c1550141e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 30410689 1250 30409439 30409441
    0xc080606010f08190204150912031407110301050a090201020f011e020d020f070807020a060f020a060507021f02030103020f0105040e0a0207150c08070905031204060e060706150f080105 81
    0x241e40c000340302241841240c40d000e00c0300d60728800300d505040740c01c40c1008140384c0f0218002c83c1ca0880d040900512800780d403142c81c00941d6840c04250b40700000c100c024001107203090b0700501c02e210103014090047c400c113080c15801c084000801c2c05c4440858007602160b4031760030710b08250b5806004014001040c80002c2c080390801c0c0031081000c852000d2100c3d26154006180c240c014120750554030b110541a8500d5603408050404081907008254141e101703440c12280081c12900800340824806401d40103031840030166103401c40204001007601c000c0d809884250a89a0912203910041c010840b10040c4c9a50650060000240a42110f28107001041005000001c105440e066200101c100090b83d103242615003c50300980910406c9600b50619007020000c9401039000d074810001030307440c12600c543d02c00800d65682e15145005a006204201c20700c002441107100b0014400094030761854012030f44d0320f030703030490301c5080d5581d44030084a04140400f84144035288018032999000307001d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 30411939 1250 30410689 30410701
    0x6032103050907150507150203041b060806090a020705070b040b0a02070e0105030a0f060f051e0f0f180319020d020f010c0203030f0703090f1101170405190206130603090c0806 77
    0x80d92a060700070805009000c40c480c410068221505a11b07c07081080a648a013490b1400390140000c1da80203440307013210090081001440740b048140b0640004041841c3d944a03100c0b920000d500c004000e503658014042c002c11014810b00040c0010200705030066030b5042c16940003400e020181c0c02c98500e40d54024010030030399800003004801c1680207094a414071752a4035000e8004d2103007c1c1c00e040c500b41408100125007440b06119410543e01d2910350000c1c3c0e49415103003e040c5012202c0c04150b2003480e020501c1d03e004008080714000001c4120707403030000d007901e415147c00300c0610388000507840041d0800901d076051001c0204220003030005d1028a48a1002039240d000041c040e0782924074560000315024400e801c100320068000022001c40708080c20040b010b14483c020460114040703c04805150101d501858030554012019207002c0c04003c2d40811285620801039900000a100c80071840c1d6817040604001c2000e80c40000301c0085074600102c0c5256242d01c8144a0303003000c801c00c25 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 30413189 1250 30411939 30411959
    0x1309020a05041112010609050a080604021503100b0711030c090f040b07030b060a080105030d09050f0d1106030108010b01020d0804030806091803040303050418020918090106032103050907 82
    0x250340003140e0110750240040b0110f0038a0041d0b042255045500c6800001c1d030a0f00240b0040135110191545a0f0450301c4034a50b50350395a00340c8000750001c60076440940d980f54208007540c0c210350031807126040103560f4410005160469101910900c081150354005032a04100c0c1d1300c88000265101003a0b03180000c4d58002c0c1907001403019010904520000340308900c60780c00310600c00c1c001000349071100d40c3e40000610402d42402044d0003485600089a07005006072507036400c8860040001b048000d100040c003030304140304242260051443d0b4000e080c90303981c81000d5030181500000004100a108000924114401102c041070201203018040401d0340b06002e0b40c5d00c0a4141da5820311070b20343d10340503d411007442a402c54107010100c1c1c0442055070080003442158410040303102d075040d0004003141244203001c021640721404a1000300001124140d40e6031000440d800000c1c0159aa2609800c80c40400d40f0300410347c016a5108407030581620480c2d80003000140180710040c10260761403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 30414439 1250 30413189 30413209
    0x406090e0a111503070503090708011803032007050a030305010605070b041202151005030c0406050a05100c0203070605031e0103030906050f0c10051602030a02060402040f18050309130902 82
    0x1074000006080004074a07221145070702040540f02101c1079403417800c1c80008025800a8491030028000ea500000c0d031031030140510310065541e1030b4406040406030364140c00500c120300250310450651001440e8071101100500703003460241d00500b191441a2400030120380050704240b041c004144074a40101c1e401403445580503034071a10300108c10f4024070040c0d01d400140110000580600410810005402218402141c03026401c07030b08030380c0800301040140c03641c40c050a03030441190101042945003031200d0000201041c00d15090a01c0d03607030003190419045402c8030011410010500c501c4401d00b0380103800708a01950300180c15410f59030000d000894910501041000104010040b1794644003201e1400d201d400466180240c4900381d80c02515049403130036040000c08401c813900354008001ca80e20070b003d660141a26a0751a402c0000900b190702070803000715914201c81785100c1e4028015140b850060b802151100d00740810030141c000c24000791001c15041100c0040140c803011404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 30415689 1250 30414439 30414443
    0x4080d0903050c01090309090b060c0a03083409050105070c0323010509070e0c03010b090d031b03030f05010f030b0411061315021005130f030915030b0406090e0a 71
    0x45640080c034102151036001d1000d000c4103075481d1035081000c150700916008100e8007000310500010389444c04100090151402d11041500511001000a482501c019a001000b514040340e4240d00380e95014420641d2001c211056a0b04d0441400071500001840018003003481d00ca0703d0310f04265280702040e0500c1c4030040c01d80c0c0e00c210220100424a40f09a070581d40c0150082241e0f16090f007003a40c3d88c08030ba12a0b07050f200c4410011400c0052545c0460b810303111a10810343c0b034440002d0520810019143c0c099040000d0740002d201403a40c6c220b13160020074029900440c001003103074860400c5480690000300143c088243c1000041c00054405c3c1e80940c10031802e800c1c0b00524008200b903440340800c003421903160b408020802403d000351401d0102100d60031a00c0c5c80b0088000d030f100700c49099400d100c2d04080b004040000030b1820043c020300d035100b85070040600c1c1c1c0d28000c402240220502107804a9290800103105080604c2280c0c01422040e005011003580c04000da40c4651b480040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 30416939 1250 30415689 30415691
    0xb0d1703070e060429090d0f0606080f030a0e0102030409050106030516031b0c020d0b090a1505070c0803070306090c11010e010501050109210f120206060108010810021803030304060213080604080d 86
    0x70002c5c00380307030b500d0903a090103030050508020640203182c0060f00701550501128040d00c0d0079401b04010782d0000e040d20302e03600010003e51620341e0f000c1040e00c80c8600c40040504620007000003151046a40c0502c50003420f0036100414503062503000702c13201520414039803040500e000d410348020119045500034050389401d15990303021450011a800f090301c8040504401c41c0300c41440310b440c000103409810302d400760a404c401e03d005140b03220207441c02602c9101c0000e441c00900004941030000558009a0387c1c140000c865a0300d44044054540600d01003012410400e00e540c1000028000e00d4240b141080003040300e0360400c5d00181c82d84511f80180304580302c015121a0001262080f40d55007550402d0f611584084680350402040c0d5040d092a40140034407004581954014003450b4107840c50f82d0b02070b00780c040303604c04948000d40000350007e250187e070481031000c1e9101070009502441c040d1001581d04d8146040d10844031074507038030881d00350f8810001c0001181c000000d6031072080002c98 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 30418189 1250 30416939 30416999
    0x20606090a020915040609030302070b0306060301050402030c070203100b212d0105010803070c0b07030906050307020c0d0503031b04210606150306260a060b0d1703070e0604 76
    0x4a1240744d0b0744081c808144000040c0425400d411003170315000c4030700c207a0880c4c0d0365039202d03080c0f21640e020585070250020420702c010302807880c05030007840e800700c05240c1031810300c1a180c0000b4a4054180c1000109559031440c0303540c1400c003d10900c0e04442980a018002d4680c2c81e1116a188019100384400e41d481823201420b4104020701040b82e1000340000f840b40c2e50b103501002d622640304400403200e8040036100000d10006120594403c0e80d0151580c010042ca0f010064602d80c1c030060407981107014902c801020340e81e801c0d139003400071400b81000750303241d1a10580d000c2c0d4103126110f014008440a0008001450030711601890000201c108200b0091036460241c010308034580002d5400c0b820341d03444c000e940d50305500110072103091080004002800c4c4101c4074440007407152811880d000b0350603e03030200c0c2c40c50300320302043c1c03001915a00d2220b0007610b0300000f003850b42d805000c0b40140041030118040e4080c1c503901c101c5038101c0f40d8601c0c00c0c1c5400056410310101082010300104484 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 30419439 1250 30418189 30418207
    0x2100f05121314010507020c0409120c08041211040b03031204080705120c010506190f09020903160b0307030507020c0a03120e0907092c19061e030201030c020606090a02 74
    0x341a404243d6008895100d440048029107020307100803561980144152200c2c42c3c03c0c1d207031034050780241ca5000512110b00c0c0c14001412182c180500800f6110110b04003c001040301d8455210080740c0d015500000004003114100f00586100c0d048081c4650b200344007501e42103001d482c1107600198004021a61907145140840c103104640c12070000c0241d020400200301d03038064000f2031190408840350f1801000542011844010b9030141c20f200007498078090080c100c40d98006c114513600142110a00c0d41910441141c00c030091f00700341182d1700d011051140b03040c0c0600605030000700900240c44089520004110350100500c00070301100b50aa003604601030045000000d102400b400001681c1351500c0b0140203113070b030341c40380c440a44590f802041202c11381001d000c0580010019845141c0c035002d515000f4103064900525402d59154030003c0c00480c5000706444026004407195200c502d10300003d421104440e03198000d5402007010020b0740e5481c2044103a0001348144e0060306c8600c14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 30420689 1250 30419439 30419461
    0x6010e1302030714100305070509040f0902060c010606180602030a1412010609150315030201140409090b0a050f090c100e190905070903030905090a0b130902100f0512 73
    0xe40203909800f030032a01081e118a007190f5191001c0f01500d056900100381e040860845004445140003d0b0040c0800044d5203007035003110b082c801c0544004100b405980e0000b0740c80d1f030f20490180315030760f640303c10400240f034101c3c2d0300a241e1002024040e651516088001c0d440f48140c030705a4003044a1401c5040c2720281440aa40003400000d110000940e151440a0300310754542c0244541e500424544c1034005100f80284440c0d8420b68055410380340c656401515080c0300b800f0507100604040c00046001a176520400c04064002c2081005078140f2208000407601c001d13210003091000c0d9801c100c0108400203a00309408016249018804800c0f20105d44140502c00540d074400c1083c0c0551141740e18440c4440d0a855030403204110f01d4940102c140d81005842c1720003008540300036020821860070b5259954400c03503009000c40c40408940c00991401d036005209002a99542c00c0300c020b505004c0c07141d400041c42400e0000a458802e24050414003c5d6291041d0050074800003844010320 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 30421939 1250 30420689 30420721
    0x209010908060a0f0b101b0507080f0105040c06050a081305030405030706030203040210020613030c05150a0c14031003020d0206210a050603070303080412090b0a0e0406050d0506010e 80
    0x1089081c0c0b207560524120000140154007442c9000d0390070b00c0a0785001b4640303811244d00c48905900c8480000103210a041080100c0b40001e48207401002c00c0010300c0c0005020040c44805094000a40c5e80703840d2130080003408080c1c10103001c000702488815006900140c2e20341e0401d0920000105040c52454464550b11640e002150980911703000004e078250190044c40c001d6200300c1d42c0074000da5840300c04036078580c0b040f1092141d21050403160000b20b03004030000340219003d0010b4442c00c0320075000075107132804141ca410498546e60008001441d500141c41045114049000d9241d420b18120720b0240210502011b0f21401944549000b15030700c400488025500c1128203c46100c140c541c0c107901240e0413030b0410008c905040c001049403070003240200949600d521030180d561116212000002405000b4006000c2100004210084401e01030300c4001540c0d0b460345607034500760701400b0503076210758002400781b040c800090f000504045002e41c15654148080d4031140d403400c0200e90705c0c4507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 30423189 1250 30421939 30421949
    0x9010509131107060b0603040305090603070c06090b0105010f110d141201062001060509070f0c0b0c04180203010305030406050c100608010c03050105010203070309090b060c01021201051009120602090109 89
    0x442c22880004030452100503100c2940960000c0021941610910210384008c5070000e000400c208800c007540d2600c08055034200809180c03807030090059603516811034124140503148011407500400c49582d000c0001a01411103107440c0602851000712241e0b58207030141080180300da0090184c4070202c880c4243d6001c07103500751440ca2603581d82c820203000c2d64046001c500142d801050012110581401901c0c11180c01410700b091564032050200c40e04d000740f221050410100240ca280800e10110804d4007030368900a540743c1d01d614083e40d012490000340c1080140e240103000410104002000380d03401c46519003840d507925107641d000c181c1080a0fa0b150900c4580c9403060200e4490302c154025a81244039450412003640c0b42c100590b503c2c000c0040041c000307407403d4414003e0030b420350801c18088001038501401e00e003170414041c3c00d98104124060051b19000300401851510f0f0b00e800144601c2ca041441d4514144103240d0710388607004d000070b001950000360a08583c0d02c211031100c020a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 30424439 1250 30423189 30423191
    0xb04020f062104020a17060103020613171b01020a030e13021204050c0f15030610020106080f0a120801050904201c0c050405060d1e0803040c1e0b0901050913 69
    0x481c02c505801040140d030260f004014190b0007080000d2203a5035540c0384000d035070040400d41c1c80c1da400c101103940041c000d080c20742c54100001900d0880c0b105a180c000909102800c1d01c610780b0610301d8602809030509030b0456115251441c04290400b1581c0035001050300c4006d0707010000b407400340c042c0c0320300c1c000b14480143c1142000107101000c18001080ca80c102d98100a020103882041700600190b51440c80d00801000403400071702e06820080510043d60001148155030344040900b081402500c403e419009018860100500b070340b81c10032804180d0078288034070b50400e00891000d2100600040001220b81e00e000016152160701c14101c00c0024100300550004032a50050f1011244044603098800728011480b444d0030300906104034005000003440c40300586405910001d180901c000821000d0011f0002c202c50b0b1000318807441c06003c003c9900d0749000260b0034401030281d0302c4012510744020a0021035a000200d4580c071000b40781503915950381d28005a403100412140e22405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30425689 1250 30424439 30424477
    0x106051c020607020315180309130c0e1c0b0105040c020d11120307171303020c1309060203010e01230105270a0312020c0a03050d1b0c06050d05060d0b04020f06 70
    0xc14010030005100d40a1000d15a251f210000f4076195240111000603510660b1144092507200c81a400b00c1d180341d945107040246000801c000c56003c1004140e9203900c55060000c07103041c0420303142003c1c014041a68100b055621001c03000b0f40b20320790464045c1c10820f10400c500030390f480402040c1c0702d020581d510300d560303400c10000103429280c60f41d25800002d140c0740c0000300344d511081400030788280c068000d0300191044804100c0791522056048e100340766500e4a9a0102d00680b02850181503005c82c4d01c56194105a0242540201032100902c6100d02048130286660710806823004e04940b8042c5006040079034121844070000e0f110000d4110314200400014444480c0b03881101d105181c003513840d4506000140803107144c641c0001b822551099000f42036143c40781420340c0010490f094440e107a01c05c103070b58849401840b940108000756010402c0c5044140f18452660030240840d1a048201645d0303580c007001c440300500107403146400032102c01007501d400d002c86e5041c4603201840c00c19 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 30426939 1250 30425689 30425713
    0x405040206040f080d110105071403090f0703080901020111030103080f09060708030a0c090f0806010b0a140406021513020904030f03150f03140307051e070b040e0a0e0106051c0206070203 82
    0x6105031700c49140c0001396104000e074000d81010720070310740540d10700d507500e15041d4411034540146a001400386040c5100f0802c1080d8010010b2110b4409036200702c0049039201e03004000282035642900c09003081d603900300300420001d0090802c6600700d85203001d07001d07201d0031554000f8070603014100019220072000803c11110720700304c1d8007140740140103450364041a40c0b900004005c10b04e0f140600901d0341c3c1f2003001808040b641c0009130010750018a00203c40e000d000003610801c1e04964071020141e070201d016110311031041000164003082c51201d01d40b842c542070300000e0b039203400600050706000501e010000854403130b0b004007000600651000081c0d42d512072000304031000354442170341d10f94084d1400005514021003140c1019410100400c8980444886450071042e0402400498030991500048659540740039100404125940142501e00700183c60b094a9513400d246207264074188051105a6404030fa004101c3cad60500c000c41e08641c2071010800c0d500c500030700a5411701c039400c10081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 30428189 1250 30426939 30426943
    0x60e0d020409110a090209060702010503060a1205061b070309090203040c0302190e09060c0a080c0d051014100504151403151305060108040f03030906060602030c07050d0b01050405040206040f08 85
    0x4815425a03e01c6012651741022a040380940701030700fa8008000c10210015601c59805907030801c40052074065960703a208a105241044000110b50790b410003020418044008480024461000304a035454904555401820003045008080541c0e0780407001c6400d00c028092540081d56002d881a030f03804100c0f0922142234915481420401c001240c001001c1c1c20340450064024910030400710305184003410192502031000305014001002404100750584d254098140940301044113540b40c1410700d107001c006902c1b024405806041151203045180da40310341110115411100381c8020020580b10440708552030b41003041c41440c01100748100c1591012000c00c018004807444100520700003009e40985004036051030118003030100050114030388464403000c141c8039260018140086966660131105a40c005200591000c1510f04031254204400400b8102c2100c4402c4035614a955241e40240140280d50055448034086411900d800003550701402141d079035101c41d5611400c60382d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 30429439 1250 30428189 30428213
    0xf0609060f080309090103020405130803040c03021e090a0507020316050d090f0b04060f0c020607060c08011a0415210504030305011401020d18050a0611070b0c07060e0d020409 77
    0x7000c00300c5080c00014180c0002046400d44003001c1c0603d81281e01c0c54007000002c080060207001c11801c15503610380046c0c01c9a0080d4400c9101d151070805290540c018010848039900340c0e44860540361054150b66541d000180354441034a0102098640d00c0f030000324114024a4040485100c099100c48108900481c13003010124035641e841c00d46503928a00c0c811004010700c1121411681040240921840381580f1a0002d516040a03040741015501292441d4041c9100742c40b4550785011511044d0382c4419010b00401404c110600c6542603944100060312407441000b24030700d070541803001d05500a0700082d5404040c070503203450b00701201c01100c001e85000c40b004c8000034a03041c0003080500c5402120400c000c03041c1c0c000c102d060b2000c0c0044e038098040c0195072000b55003d240004040d43c890344480003400740795660100345d09143c0c507070900d042610f42158200c0308090002104d03a0f2030000c6c00784121041072402c0742e0f075502440c0c04074202080c1c00501a401c141016403141c00c0c4542d10240b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 30430689 1250 30429439 30429449
    0x50307061706041e05040c0314030d0f0b0a1e05041e180b010b03100510020a0201020111072d17040311010908101d01060806070906030504020d030f02010f060906 71
    0x1691040c0da801c401c21013110954035a00004120816212042c000194442130f8041c0c0300b1b6191412051703e0743c07500112800341ca8040c103500d80c400a04c0b0001c6164074050560828807402c3c0902132100050000f0b000f05846000703024a45041d909141c0d00c40401109803801400d01902c204a03418607110b81f030036042d81000303452a9950900890740103201840007d065010b800490560859081152204030351b880a01040035003003807103002261a07514180358100e90034054009003c601c0003440060709580c441d51104848035000c0c06500045555552804a80502400200038040c0155200702e01c0e0b200d2420040d01020200c2c243d000c90311421001071059a001b100d0012031080880011940301d4240e00615000c1d0300b0140c2400000c03200c5811035241c075080c1010309081141400740580c216001a4050301c403e60040090224140c0c000508401505071458240241d2606801050354000307141c000a080004842105c54028401c0d0b1101014070004002840215517030300b032544c068242d80c065 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 30431939 1250 30430689 30430727
    0xb010807020c03071502160801020a020c180403030504170a020a02010e12070501030c1704080307030b1005120604060306051e010605040513181704081b130504050705030706 76
    0x412061400003849981080d03004000303100130750a0544041c040c5101c003002005500ca081c6400044140510051021b0050070340016122154400001e13701403240007424003035a903204410004100d0004040d51054050501145075103482c54031813940c48440c41c40080c0c0308004501e00a81a070b0108159040314001d07614081e21081080c100044200442ca40701c505a009a60410055000e5002420000114200302d500803400c0e43c480100c24400700c03803c40b20044e001003008107044e01441078003910801031720080b41c00d1850000c068400e12a52800c0740b030b4689503800003105a5540c0d04414040c40d80700205200a0808140340001003080902d05040c0c1c041410001c03580910400944040340c40c010003004c080210f07880140e00903d0b00c400317034400c02c02c0c00100070004516920040d110400302030960b181d4481c60b282c90300d410b000029044001c82210220910a00c1e81c41c5400c030996494101000901c036101ea00d0f040307161904644c0103d4050249040c00500720b60444104080703540c0041e6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 30433189 1250 30431939 30431941
    0x306050106050307020318060c03040b031f0b03010e040c05150d050702010e070302152505070602010b130b040b0a08010b040506042c0114040c05040e07030809120106090f0b0108 78
    0x700303036a140000c071007200042e8010700513802420560340a2413400e04025019520300b0b01c803100920300315440360300240c1c0c5408001041c440c40224402d5051074030450222075001c49820101d001c1c4040c40103200d880313042c41d0048045024000c07088075100c01080c4c02010b450425420403039500c1c0c1c6802c142d1743c1d410007518240000b501c01d070042c0a0411141c64042c05001114110b42c2042607452244102c0d510800c000e222840c0c610040254561103c0003211454094003618540b040c944060354210108590500356146055160b8081c84100313802044000715800410390302140017060b48141d000c0e0301134140cbc0400240d03080c066122407041d82c02580c0502150343d17000300340400e0750910302405044d2203d29500e052060000b5114501004040c13001003400c8216203000c0c6200f00701558161a0075114401c00c02061400d0304c41c5826102d005400740c04c6403451a02e03500100e0003140c00541c00b45c3e14a9040038070028080d44000041c0c580a08200208482d40d1218070040410310742013400720303d50030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 30434439 1250 30433189 30433199
    0x17190905010e041505040e030c03040603060302030601090903140313060507030606170103050a021210050108030310090c120213030204050f04060b0a0e070309030e030a030c05120715090206130305030403060501 92
    0x1301500b421941300c6048000070781e242400340402411084a41c80050005201d071424284091005100412040c0e8011400604500426080100681c014051207181c00742c0500066080746000103222500b800c200d0b101d589208000c102004540c0c1c008007202c0c908800c004805070141c0c0f0403c01d45026a403544055400815201e403014030a000c0505250303c600300000c010b250442035480c0d03001010050b646007079000c03080320042e20001c0c1c010004035040881080203101c0c00c100f944004001145080c0309200002c88081c20040302c2d1400c14040e29000900c952442d101e90516500643e4050000c011510300511044000001590200c80e00c90400c50400b01c0780c644008000c0a444600001c400c203500e44200a81c014161400c2c110144110000950440d5405200410700c00c1e0294950001a018901c3c14905114a60010f01d4507c8414800b44010401c0c01000c484034004950380065005058000607240317000c0c1d5a00d5061302e00e9600004410050080701030012030348100001d000c566203070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 30435689 1250 30434439 30434441
    0xf0b070201051302060f1806040b0301230907110f0f0307020301060504060b0a0309020319050a02040f0c090e15030a05070e060102070317072a1e0605030417190905010e04 75
    0x10f10040c0d0b1000c0d0074465490f0301d0070082c004245020020a0080d100c1c0b03107160105240d9049075000c541c0e032500c003100412018040d20500c0440a4102c4c441480e80c00c60382c40000d03220704010300680200007800c200b4070480076040026100c42e22044080700c2240d1900640d50780d80b40d2010230f01724000d500b4034400092034200b81c0214015219117880305420302d1031451046004100c00002170f03905108034103613500c461010381d003010f01c1240a1800781c4048070050040c4020f44017070300c1300740050524148003440015803010005003521480c900000b825160602c001d506881c8680368541e02d8040c88000740304006002850700c04031045001c550b01740340e84a80059842d00c00340c0c4406080350182079501405260f40718024260341d4072920f941032001043c0c4415240c81e070076610410542241c203e4003400b070b01c4d22241425513114079031110040c8040c18440001c08074040600020303e03c21760175880b0000e40c041881510110000c0d000d00c00e019220051000341000344500c115408a20f00001000803400d00b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 30436939 1250 30435689 30435721
    0x1511030406050906030714030a0f0e07050303040b0a0c1703190b010e0d080d14150901030809060a0207030807060614030606013207050c01020c0306090601150c0f0b07020105 76
    0x2103602d8580c20241a64103001844d80000c03c01c00801401c011101d207952000000b56000d00b001110008140c800140628121280c1e040144010b0b070100e407007005555800811203059416002005c0d484080e08801682c0f46a2840001003529110195540130851241e0140d8032030034040d4483c01862145c1d0080030221100b42110038000b034030950070f0a8143c24510944202680f05038400d928005102c42ea840c116801400d680c08003000e607409200d110300118140c0b4403c1e123411125811076503d50b64850007644a00740350240202c4020a08050041c000d0101c40d0095410503920350b0f8642003407524100a00b490f025415500c1c143e07520706100d03804d000075024415081a101c85941e00d40346645090f16111a2020104d80b602007101c00f500000e4170000b4001361072040001f030042281d83d500190902d62040c0701c050190380007204111080707400103501030440b0805019264044207010301102d4815620b40050164122a00c07030b0000c109603240410b20078501036001f00101d480d4242042d0407010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 30438189 1250 30436939 30436949
    0x906070f03020c120c100908010509010b21030909040206040b0c030c0601060c0b0f04050304090e30070b04020d080f03061021050c0c0d0903030f030605060a110a050715110304 77
    0x1200c0500c41c0d0150801b0580103128000c00d00b49a1f100c01d40e6940e1050a403070b0b0803242c07080f49075152221542181400000b40c0740214801c0d462200e407521603980c1998901414072110b120714503d2000ca415522210202c030080c1c0200c004c420354464200418035520f920510b030304080380c810039000055152080f02c1c01100280e020a80282c95261000c8055200b40b01902c2595036010030413002600c41070f94403c05c034081e048000508414031400354180a41c0002e9070302c007410710340100003541c1211440400c03101340702e610070f9401d610368445001048019060f02c400501d03000001900c003e0700070010000d140b00364000c41e0219950b5050240c103c801008640d180c2e0039003c05620100f140d0722458101561000d2010480ca0822400c51007080c60310034100c0390440420500001442455407006010070000c0507403e007031140c42d05d0500403403c6803150700c0d0140204610b440c28115030710b20612042130082c0c0c0000850b907402e6101c908075403031000540822004121205c1003010716070300100540f421a8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 30439439 1250 30438189 30438193
    0xf061112030610030e0105100603060b0405060901051308010204031109060d1502160c06172217090d0b070906031104090509150a06140301020c0615060906070f03020c12 74
    0xc2c5030368080c00307404111445500c05254480036155a900c0c000d00c039286c0304000b50f030781a2007101c1c50440f0140845085801001c0b010784200820712881d2036007070071140440c00a107801c0b50b4481e04c0301031440d601200354025040341d50000800006101d0042903000028004484810040c1c584000300201086807010041001c51001c0d0a0211070700d10b54007600c000402005e0350b042103211035954803c80c00b0030b034200c038000c10301d0390454503c2c80b0b03007896480e80d004120200b49031506ea46800024181480c2000c02003100319880c03100f8242e808144165609800081d08480c00e400c1c0514014003042022076600c4001000b4003800650203110b0f00074049010210f00381e4600d468108040e080160000610205107446032080b103094141440962a125040540e400605141018100d032070400c92104d070540309a0040c0303c000e00e58400031a20396000300107043d0400f00540c0140100c6c80d64000c840b00d0359407003803001c1010000c2c01f0502102d02003031441390782511354200d406802c1100d010354000d4184829 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 30440689 1250 30439439 30439441
    0x40e0c090a15050406300f021504120f060516050906090d0209190b01050301050315060406080f0703050d0503010b0a030207031202041e050105040815060f0306010f06111203 76
    0x100c0c1c0d45900c07102c06192001c0d24540210784800200e400d032a9580c2c002040b041381c0903021445140c0c1d070a5801421104006801071310300e050f445000c0d0207030516402a04c44c5103821040c1d07039010310700c0c4200c1d0018802d4000c4c3d200c00c60b0343c0d41081200410001b40903a00b290400000510005060341115100000c0b52541c0b4200b2040c10203101840e00680030b06500f00171801220801b60b030359a010b06100d1034490340e05070225144441150281c800d860500c0341403183c24001070055640210b541300a1002c5841100c066940d240f0004021b444144d012800a014000c00e1041003400803412000341ca0041040b50010b40070b00c1c0c4119050b101c24891060120030610822900501c0303a0003c044aa0003854031426481e80429082d049074031039480981e134105112140d010382195900d003c1c0040c00e0900f091410306186c11000394440424041404407450001d0002d00039507682a14807a0745100581110660340c0c54004036002020701e03003c0c100104200b0880c104004800280b200034440385032000a0031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 30441939 1250 30440689 30440701
    0x50c180d06060e0601121e150905040b090c040c050a050a091502030a0e030c0a030311120f0301180c0807111f06240f0806040902040c08070e0a031a07050714010209040e0c09 76
    0x28090400d803070340b81c0d83c0d42100c0007909c400c4e18090f03035005a002e070100e0a02421b182048910300140b05186c18002d6040070794007002d0a41140940707440d01e550303041c078079504c032850501141c021f82250001c0c0b2881c0308154030030084581c00005818007065a4035910031640180c801c00d59034251208066a105034101c3c000e0002034410900000883d4841003241c86415030740c260300e080398000c0d01d042c44492002100400040301d448296015420485034200301107002084000d0408100400310014003d210300d4440c1500070420004e10f141111000840007280b00302700b0344c00906824441c07049042580c00c01c4003200a011030284103025000d860342103400c840583c1c02e072042c2c1d00060203103038400da8032a001c03001b5071628002e0409005580e135540105141100c2c014040d403500d142c03440e02650468100384002540310700010003882801a4488880c0e50303081c42100c10740709800f0010b10100074040080058401500541002d54003180e0502007044100c4003640e84a0383c20003083d90011031900420b03c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 30443189 1250 30441939 30441941
    0x60b042c16050607060c11030403050a02130216080901020a08070606060206010e091b01050412060b1504030203060408030903130914010509280f020c03041404050c180d06060e0601121e 81
    0x1124181500b4111f108003203a803800c60842d040303503000340c8041c0c005002050452030140303107180e40391100d0201181491584281124a00c3c0640d10003402c5030381c0000c200c55181e0080140107141c690040c5101c4d40c0703888500d05100945118400d0130007601c20b25002141d04c07154084041d110313000b000021701c001d41808420501c4103801c950700380d06101c01000041440c045e1040741810443c007402021030100240e406208803820464140803140c24148400c0c030041c1d5020600d0764100e50000100d41d03e984038060303400d09600c55052400162101e0050004015086401c0f0504135020310041c05480c0e0b82e41c1c01401512001154104032140c101c4ca00c0240740003855070780d60340120804100060010381c44014004aa20040c0410384691000c541000042d01c0380c25542600f1000303a50900c0366040082d0030403000d001e03001035031606c0c0c440d4541c41840341d11000c01020410b43c01c01c01c08d0010036a00e40c0406202d40c0f054071392500043e40900038490101060262030301c144030000f0000c04034003042038100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 30444439 1250 30443189 30443201
    0x603111801140c06091006080d0507050309040204080a05010606020307020f0108180102031e06030a030918150e071704020f1c0819020d03050c07060b042c1605060706 73
    0x103414801c4900c01c0c10b46044507440509001c0c501c070f20003407050f4100982c03070f0340c5081a40b9003014116410018180901000410545a00f0110341070098440880349030940c2540503001115130824400300d0001601c02c0700095500c1c5050143d8000c01c02c441c1c94a50032030301c0f44614a406900100150701103c00f40d403107070307000d1a03200705040c1c14000c4540c14442d500b800d80c1d2099504507120b03000c5036910080c001d50840170507000320003200240503c406540e0701405440c050310036841c40c0c148440da41416401c0903041054161034003c07003448180d4461016002740c840c19501c0c00006540e42076001298603058050601890b0020116010b25201e4000c02c642c1c606d4240f5400b103850124000e5200140300080a04001006500005e00e103000c0848002d01d442000340350842010706081c180159918001c049450860300b01c140400c1244045000c07601820150280140207916655036012100714280d9040c1e030408104103582e0002059807452090350318038081e503640040b04110090000d12954009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 30445689 1250 30444439 30444487
    0x901020f010507022104050904030305060a03060f020a082d06040906050103060b030c030a0b01090c03020c032d0408030904020d0603050a0305030108070f080c010c060b04020d090507060311 83
    0x16140030300652100c500355101070300d1501c05a40f1004e481c010f0502000c0c041c100389443c0d8000c69080902d40b0300002c12484010b080a420306a44001041598850300b4040d0b000e10340090040c403c0040c040702100c000d6004d011204c00007008c030800710308118000b01d894045218051211010b01000e0160010341400c042c1c003441e40a940d42c04508006401400f9450003140202030018030703070a140090605101854441500c40d07048114000005004101c3e2141901d201c600e00142035a02404203a00a00c501404031000b4800810000d60b240082c0231030284880c1000d11000d00e425003600c0400303050003079026009417074006102002241c10250f0181168030f02020002c1001580c07a21142c2c02d1850002060380012000001400098001c0003650000c08900c03501d80461450300c3c0000752161030540f00345040219040c0c100c0140000358100c00b0901000410441d0384002c5640300c44000c040c4044121141d010300f10b40040c510303000b482a082c84a010405032460400e101189941038034800c408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 30446939 1250 30445689 30445693
    0x3010b120613060f08060c120703051b1801020c061606090804090204030807030311030402010e01051e0a0302040302030705030c0306010e130b04030806030f01050c040b0703140c1c03060b030c090102 87
    0x144440070b03101405000000d00e070f0011101d034403d00b000d403a5420900300905224101d1001c000c0714081d002c45102059202107a8500081e464481b208440c1c2102940044603d64100120341c0452403402c0302d4000316109026001c58909828030014080107004a059030348489002c0d01c41603020070a142c1000c400644071360081d52620380c455010f00126007040e0030980e0000f402245403400c16030035105815582040350030041c21403800b580028100c145800c129410042d01045600d400e81c0348140061000c094500c40c5a240d0401010040003034116100170b07440b031303c82c01000107010300f0049210b410f1800d0240281110341c1c00c000b128407440b400580348098102d004c0c3d10400101c0c102400c02c500592180d030300c941e07050400808042c41c1140c2060701c40c500fa403521007802441c0900c90101d4045079002804503440700d41ea402c05407010058250007500304c450001d00c0041081e00031031205c01071407074140341d4210079901841c02c5084540074007030700800300401c03c04942c2000305034010744010101441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 30448189 1250 30446939 30446959
    0x70e030a050307050a0b07030905100c050c0105071d01030207260f04030c0e060f0d020f0301020c061510020601060e011209120c0c060e030a110324091203010b1206 72
    0x1841e070b861548500d400f500c1d00c1d080079010004000c03180c01829000344061806110b02c51064807640c2c0c031030b03600c0480c1d49115076030341c00d203501100d0203001074915000d40840200312901d84040d01a100c00360248141000e0400304114400070f40c000e01c240c4000f44e8220551462412040403c69051500c1a800080c914000d100c107001d101c9091005102a41c40345c0d00c200200c6107084510102002d002e84801c0c420b05040302c00320295240c4c1410460350540440300703c0c061203a1140442d00920941130038016a0003007904100f0412071228411481007400d8440650b4002d407a40d080b46c4814080c0a580000ba02019100d0100d6126103626000d844400c44005101810b50b956035002c41c007007640060100b4040341d8540305118010550301c1c001c000070300b4180030a04481001a403144007819004103542c5410422580300e0710200300c442c0d07641c0101c2001c51307410011810040ca034a0000c0300c281d0040e01c40e4566560303000003142c0649048403160320348242001e01d0750118005544009011a40100c4152 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 30449439 1250 30448189 30448193
    0x1803050d150b0c030405030c010f1d1201060308190201020403021804050312010905060a0807060f0809010e0307030c0b130b010b03330a090501030305030619030204050c0a08130b070e030a 82
    0x70300400c9040c010100031543c60340303000f00381808d141884080074148000d150380c1000c141e400050045c3d00380560a904002c05403110b00242e402a8441035001680d8605400401088112030052106456078540c0100a008100c0103c0c242e10031400000e41040824014400349902da1801507001403080007620f040c0007405030800c4501100f6403140301c0c0507031107005220f940e007000d8000c18054075803040900710003402c1c043d014110300c030114081420031016100061507500c0a6011002c2c000c05481a80c1d40c41481d410000c00c500ba010805031040080340340441c1128a08207a0102400d51040c907002c41c6a1030708542c07a82d0341c2c200600c4d400200051101c0d00d00032451103081003807001d4550481c03281c00391a03d000c0c020101165040b8490701c07868100103101098014040d6a030085046070301805001c80a07408400035801640020740160500040c894840031900207040034000a0f5280352075642c500076102c601c02c1d4804d4010b015003001c000882ea01500c0f40d000c80e80ba0030405001c480e10b5088903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 30450689 1250 30449439 30449459
    0x50a06020d09030806121207050a020901031208010b090d0609060b030703030801090606030b060306190806040f0204180f0b07170f0f0702070602070b0313241803050d15 74
    0x1c018039001c425620b01c40441050b40110303485810801c04d0b01d4031410b602d522014160364a144400d021b50111004c101d01c0c0400c40b0400070741c7c0440743d014214550329690f0345003084c41c2001031141800803401180001c1000c1c02d804040c0c500e2840010158a100b6515854400041000340c4017036591a460b5228035440751010441d0000840c07183c6c0d601c100c00c0d854510030900b12005600154101410208902c3c5c00e903442c04262500110300311030151540103c4880045103003100d13401040140500320400c418040c0b400c00c4d003000c503070095500340010560940711140c2d846c03411b10020150300c007110310300c0007040803a095580c2c080050300b403041c40344100c03201c40280303d0000c46c1c070108103804490030003500900402d441c5400c9552400203016060502c0d07400307501e0725a6401102c07440c81e004000209001c01000004103941e0304a0890014640c40840bc14a00d4141c0c204e185a4641454200445488444407402c519601507540b14203080500c44d10402420020300700e004403038030219003c034000f408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 30451939 1250 30450689 30450697
    0xa09062114010501020105090703050c09130c06030e0d08060d0f0c0504060b0c0c030d020624060c0a061a011b050a060e0d03050606070804141201020c0d1b020f0d050a0602 75
    0x80700c04102070710b6141000081c29141c00400650107a08203072010000510005000480050204ca07070700c1031035491a50549495180b00409402843c8024000454035010f5114030702c0b20002409407080c55040300403d49100380305a0b141034112196200d02c1000c2038151081c06a0184128004c05820b81c1e644005800e90349541c20900c16680002600201c2c0a01005403c080d020f0070341c0545056110070002a444007801000c0b82c0001c0d04030030781c40150005000003d0101034000f4016911610f01220a40c0d841c50364a1046602c2c1740381129a442401c5500000644000160f5400001c007040840c0342c0450600b40804139202e10500a0f140c0000303500340151181201c41100801081d0000f02d4010261500603000d5809440c0802070360001c644140c04640558600e00c00f8a10740d0391180d008500d00c941d203e0040106548082105540c01c040840d41c081800d07420703529640021966910340d50180d51a620082d884540c20fa003003021400d2901d04201d415028209440c2c00c41c03050f45400042c0ea00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 30453189 1250 30451939 30451961
    0x60e0f03070f0e060d080405120a0611090907021605060a02030c070b03061e1305150a0602060a152301090308070501020403030906022d030702060408100506060a090621 74
    0x22030504240404031640940a40c0804100c400e0001c1030000c6d00c5460286c403a03030084c84d0240003100d1180e0707661765003013010300e1005034040780400c0350012510724000305800001d000c510031784180002c62021407001901d09001c42100c41d4480707002d40392004109441e8020440e00c8194041400f640b64401802e03c01c40d0014051002c8003940e13850402d080000c07000030300d240305140c651a4a00a4402d490b4030652940007003048074001100d440310000c00d402c0000e9020b2190f44850015000710341c1940c0440c215000385040d09080c0100c80c0f0720280b42c510800103006841000f00c1c0035030011042000102da00410010604100b1005922501c0702d5110380e101080c1034480780e40004c3e04204055101c003611004102c1840a02a50340c050700160240a82151007c180c0b020308100e4250001b0b01130044035010b0760b000300142d0355039541d1b214050725480c103420700c480b10502e408009000c80c1041021280200290780d02c5c80729060801c0f40c203840d107845000c0c580b4050018034031000d00c50b100e40d104002d1050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 30454439 1250 30453189 30453209
    0x7090b1e13140d0807030c060b1c0b070e03120d020408030304030f08010b1c09110d0c0e06030a02010206010e090304032a0902040b0a050309010e06040309080c03070e01060e0f0307 79
    0x9400e2150240711100101080c0d802001e0f00c402c120049650042581d030844c0d850b180041c41c42d040e90a150300a00301050701c0d01c2d4040f03145602c80341d005000820010006200c0d0700c400000d651040310540700034000c0d548607a010f401082e1541d003081210001031550b003a42c098010304141d01d4491003851a001100c044022603158148001050b80100e103172030042c0b44545040340b038480000250001201e10080303112105071145c5852040008543c800143d480026040c51101603a50400382915401842a1700070100001c01050240c10045003401480d074040c0c00800c1140d1a22007401c4540100603c014110f000034072012001036601c2410940340c2d6481d004501d08082d184009800d422541c1d882040103904c104001c000e250813080540d0b90094041c10070b0754a995420f13180a0161140401c540c00b50301402c0100020141c01c01c100200742d445407400c8402d9504a40700349940d600490250352005002c400040103480e1242c1d440102a49002e00540c40114800c07000c02d1a25155401240386a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 30455689 1250 30454439 30454477
    0x3030c0501060f05011b02031c030b04060b0408061602010e100509011514060a0c0605010e0103031b081215030a03020c010e0f090411060c0a11100201020307090b1e 72
    0x44034003400b4000c0a05864158200f180d0f01e03000003c3c4c81001c901c50006040c0c00010030680c299a41400501c14000c0a5810070314002d000308802402042131440300ca00c6a898208041355444400c010307181550950801031400c1c0d216a01641c1101c0307101c00b45c000c1103640700d128508004106109220340161140c0c4040798904201c0d2600c0e0030b64820308040180c108090a08201402030181c3c500c1304c0880a4403607a6540f03103907010803540c081034a80007404e89030070030f0000100d0790707138030800309040704c0c029030700c400003010450406150141120b40140c485101400451941704070140e502e40c10400c0c0c626000c659041140129003020319030f07002a400340e0031070b039152003041d600801c195a03c1201103501c602c6c214101c600080c203190000d0703c064205014485040f8030b544400045070005803e00048425480d024688940200350700c0d095103009400d5501605121401402601c0c0114855100d032080309040c07260071850b50300a94203030903031211025615101210000028401040380c50580041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 30456939 1250 30455689 30455693
    0xd090807030f021501050621040c0602060105030a082502040c020c03010501050109030506040605130c080307020414090604031101021306170912040b0a02070e130b09010c05090409081303030c 84
    0x2080302000110425908000030003500340503101c4130f55056920031900c2c42d40350341b0715110008408003009a000c41d00d40d101c2c010300050040c800410402c44499500300c0d82145c0c3ca5000b8940c03141c401b284000d1500c0c10034401c020440c0340300c810041a0301d54220000c1072090700b580000c0c05884001c554540581c000394600515400c00380035442c0500020700b480c02e021482e41c0d41c0c403541c814000340007409056031440072130149860610300d03607010768000d800c2040b03540d10783c05525140d501600e0205d100c0c526186500c01d10300d007401d02d098815115031020b4220381c2c3c2d072a201501d030045100345a4000d17550030007003401500c410306a1031016011a98891403004d080c1d1403480030a65010b07000c00b41c2548011400d80b1a03205c1c400442c0c040d0380d0003201c41516060001e41c10703803500d10141c10024400c034046003000141c44900d07000b21000350282a5011840e120b103a42d1508072041072420100085c400c01203081c09080a80100c030815200740c0b4141d14000701d03003d5500d4500000e4004500090740040c101c41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 30458189 1250 30456939 30456947
    0xf050106030203090a0303020d06080f0607030509070302010c060903020a080309010b0109092703090806010303030e0616080106032003040303062402060f060303070501060603020d0f05010308040501140d09080703 93
    0x800350199040462450402d600155030300c40010900404040d000600001b54100c075410070002001140101d8629030700904040380c56031b404451041c000b034030301000030b95480b40c001032590480e0b03010303100e4512080d659101c980280455110690541c0300d000c00c0407000030340010055100e00200c00000030030800d41ea000412929465210b1a4405e04040b2406006000d00c2d481c5100c044035004240c480c4e030801e1506681b0b076030440c2d119880c0341c01690000018141c16400c50700c4001100410b843c12644d8594640307503640c0c610825500062510300c0148200c500a50110741c91100140742c0c002030780303141c8039080350940c012501100040d0b15080104035a2900c0b03059000f11840462900e00b4004680c5402540c03510000c20b5100c010b80b05c0350105a29480a20440364a0707034010b002448102c0d15103074043c001c0d610500e96609014600004802000d145100e05030680740d100030081d00c0c140c540801180c00d018070500f00e6440c0d10042140131b4520f07010f44240d0000d03510581300192180040d080140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 30459439 1250 30458189 30458191
    0xa1503060c0215010b040504091a04051507080f0403140708180301180503090d1401021801080c072004020405060a12060b09010512070905030a05070302031c0503040818060403060f05 80
    0x2d0410f411800500901d28102c0948080d502c043d21300041304105424907030030180700050444031070a0343c0b00600042c08004140140304104070398508441e500d900740708072081d1104481c030706050201a0003040c0040d2041c145000349100c405c0e4084e06040e050340f1030f407019a0000160500c1026210004049800d007801000c2c2c90301078002901440307801549520b501c80c4a8a80405c7c4100588445c074410803443ca04640e40ca612444000c549030702c40204203483c448100308149011516040000e5203680e1090708030342a060303000310b0400b0100480f143c205c4641000c1a145a0300503028040403030315865a0010741700054643d621a0036103521001880f080b40c1c3e4603045000e910070104180d00703499070071200301c0b15221495510b905003a99601011101c9490a41041e68540204416803050001c001540302c1964002c03401d0715100c4101580c1c40040c0c583d20a010340100d0000c0c00040c01265410001c0c010b41c990340b0010b0300c05281c01c0360000b0040e9116800444900e07a0310740c0c03080007142c0c0b948a0a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 30460689 1250 30459439 30459463
    0x61205010b131802040902030c09090f13020d0809060f0d0506040c0903030c0303090501020a02030c0105060909070317040e0a1a03060601020303061507020405010605030f1e040b0a1503060c02 84
    0x22030b192007030b00d51580070314500a024005051280805281c0000070540c11200101240c510842d1282419801c0400c65440b144141c0d01c1681600007054a0421509146008900c07014203800701078043e03401c0c0100703405091400c0d00c2c0c01c03905008c0c0e0b2103252590380c014010002e425200d43e40c0c03200c403a6007181c101d54006c0e003128062071030620f0410865410a10800c1902d401d400c184000b4400e41c68210098460f01c440180749500100b2102c919503000000b409105c04084000d0200d6620740e0f05021380320b6801c64240d03a9941c0400d8041000c074003640340d200c1c0900005162980b416484002c0340c045c0c050240e951004160340c03030740005c4e039800c0c20391900702403c3d0045020300003509003900002e40c5da010152030f00788180400803210640c08640360855240e26406402406190380d01c5901070804d4000b1074088040344401c3c1c00180b00c50840f14444880d040f4145200f1809850340d4480f02c0d515140103009a6015a40360500e40441313031890300205c0158803540b00840c8407485410000d0030160034081c0c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 30461939 1250 30460689 30460709
    0x50406050a030e030706060906050112021c0c02100c0f1710051002010b0d0c0515040f0b0d0204050d050a0615060c14030f04030c03060c05070f0b0a060f06120501 71
    0x414409158440c049400c240d16528000c01c007650a01c1000f42144980700004160626001340043c1c405c1360364000c8400c4032002d80b9025680c5440c410580305078400e100200b06240c07030800d40a61412140c0d408100070a0703451048440054109100320112074280038020f010400046580400582c071100104e00e94044500302d0b1741a00f40606100f00b41486130090134400d41c1401e0700c0007841e40c802d600441d00c4187c02072142c6206195414200644801401500e021b94034540b2200b18030b4050308111002c507040c0d01c140404242c40c016203500b103600100c0c42c035904203408000005850b0380701c81c440c0f0b9602c5c0c0503102610481250385032031400c4034601003e461009a90001c10022507070401158100940c0001c1d80d0344040c44140310060961107070140703403150480041004418030a0a6852001f0b6030300c00e6004000d0303494020000c0c1c0e07040c05216002485078201151900005080c00b0700940c210018190100d086034071103080d41d800301c0a5400c680005060100e04070b011103070764021140140b401c1c0c0c0d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 30463189 1250 30461939 30461947
    0x1050612060f01110307030e03071208030a0f06030204060617060f1023030106090807060207030804060507050a050303010909060b122a0303070f0201020d1d0d03030204050303030f1605 81
    0x28900002000041c0980d00c1025000030702c1c2c0e01c0c2d0b40034861000ca01d0001c0c1c01070701c0d070b182c01071b140117042115070b050154028070640f60082004103c000c3c0520b03e06400c5400281580d40b1000356001400041203d07504040e145d160001c010788070b81c0034450190080d40c5603454a000000c142d0b1912150007400648038100b520480507240d2503198136010780c0c0c00185040021902c444101282c03411000405649801d0004000984294050041c07029a1900801d07240b0072992071000b00d07901c2c0414040505045020003040020a004000500e9250f1240094604110745502c880341990801d074480e0800fa07444007503030390402100c0d1003241c1e455001100d801440058a9002540d140c0301c450a16000e20480f41040d02c9400c1024854901e88000608503070b644c81e43c0340f070881c800c3c003c10f500403405482121010302c08903016520341640081c00741040c0d005007103040204032407080c40c0c50040d8185a0f0801001c1140c0d02c0038001075214003064480d213641d905011041d19084d0403a0100b000070001c0a01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 30464439 1250 30463189 30463207
    0xf0c0a0c0e06030c1f030b010512040b0603060709030c0b09030c030708160f030f0201030c02030c0d090501110c0907050d021e0712021b0405061206070804140309061b070509100e010506 81
    0x1d4501211905d40345400501c1c0014480140c842d4890103480020819a840420003085807109455105180a500b40c0b01c2c162100101914940050300004009400461042c01103101000c09010440d82c02001c80e1050340d50f1034007003410b2495031740180345560010042c1108400514100790014aa08038004544d5031840c3c03110101e003194800c0090405032940f134144000d13442041510385521580041c8c603c011411076015041054a101e440c0c00308021510896141d40041141200743c0c0000e464062a0769450608803259485002d0525041e542400104e0b1001c1100294103070101440c100280d413015141041e0084156202d50301045500c100e04900f204105031810340f49840c0165030204403510740400061404202c852903031140c1c85070404008560b6400452240128000c411504124421401c416280c0c89500150794110908025495583d80020260701c502054102503551194440b400141c00c9070f4107076454400201004c0040c8400c2e02c841c0800340c014641101c060349004511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 30465689 1250 30464439 30464479
    0xa020105030c031305070b071208011d060102030c01020c032d0d020f04030602160c06020c0d02130f0903021b0409020d0204051302030d02010c080c0405060f0c0a0c0e06030c 76
    0xc0c2001c1d44a103000c0007007400c92481d001c11407040d60f4417800703888485860f06034454041e003020009498001c0c111003040c64050180404038107071200d1074210604000007006204401d28007825450440c441045540d90b640b07001c1c4090400018000040c6540c2d89903030f54050b501c1d050040c0c40c000031002c81c030011110300c01000c0480e030b403c150b1000050303250720102c0640c0c2524006d550020340b0080c00005d8150a411142040d940c2c110b2084c641c0200d030640300c2c8004c0342d5480825070031682100f82540208090300d400c1c0409000c20342c80138004559562050080070a030340c1840340403030159104032800010680c0e134510400b103910040d10108000159600003800c1c3c00c21002000e4015541c0e040403031408003183c40034800a540103000c840e9007442840e0300900808100c50b040d0b0000c0c2c500804104d9100e001d60841e1700311a00181580e0604102e54698041c0e53b0054403804500d12418011400003207c165880000704120a804141032600e102414103101040c80f160384030f41c0d4034800e4842c011b090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 30466939 1250 30465689 30465691
    0x6070f1e0203090d0602040302040207150e01140c0c030c120c0601090c05030103121e050c0705060405031209270a060b030702070e0601090902031f06181413090b0a0606020a02010503 80
    0x8540f013604540e11800c04c1002440f130781e0800380d0410300000b07001e400c4c0200954000303004c0046160070004103400d02500e07800c880e100d51000d0021000180861110410440079040c482d180a003600c0c0360001c4004214074108440518401019001c11615080d45041c80f84600400045000380404150007100170f0491005000051114141c0c1243e100d009110b4107489840b036101e540d40140c007041204015020741c1041c10440d0307451080c1c00700810282440c401340c0c2d0896001034024002e00c0e0300030900c2031154100b6846280c102d491407550250300044003440108000c5001846001030504501d07500c00e840d00f5401031410a0780130024403150581c00200c92088640004111010740c550320700407103110103143d10003030541c2c2c000b000380000a540840d0341c540516941c1c07018040c0d2944c403070003926012a04212400401c0034260b041100781086008001491f0008240f94804500c60803080f080314901030050720082d0014003002070740c188070321824015089a00080c544003c80e580000c040d844 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 30468189 1250 30466939 30466957
    0x5090304080a080d06150201060f060e150c0a050a030806030c0d051e0709020f0c0c0108061c05010b09040807030e03031303110406030204091203050a05010e040305071406070f1e0203 80
    0x40024030003a49110950201001c1c040740b00c22a030030108001b00085c042c2503039000e000c01c281140400015000d018484205007004007074265441c080004440b0b480b260410316403420035003d500710100c00604248582030300580309803a0f0b0411414020300349403400706000540ca0081020500c0c540c085a00000c888007200c2050081d642100c00c036a0000c1d091611380d41c070402da50345c00401e01d120380000c40c9014000079200305084455403c0c00d8030045400324025940150800888403c031000050b2055020030217902400010840c01d034030340041486080d00b03c805a80400022400d03c0406602c07009826104900724021030a10800d01d103480400c41451000605441140c003402c10141c459070480f40055800600401c000c0e10306d0304244103411030309602e5000091070000040c4010b0f000740302c3c250603038140c002203030307800d613110307075066440342d00c00802039500250404903408010070420289115480c15600c0100d1ba9848900152141045040380414014440110081c00390b00009640e4680 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 30469439 1250 30468189 30468203
    0x90a0b0903030c030a18060626060705040b130510090302030c040501060516030e06070501090309060f050a0c050102120108010e0d0201180f0812090705010905040b03060703020a140c010f05090304080a 88
    0x141c034084054445c2c21b060001000c5500740fa000284040c400c0051028004c40340304200e4500b4000590540c50b0170381241e5040208005001c14010500b604002d003407044810a80703032508a480d10009a20300300d551280c04c001038040d000030301c21410284034a1202c040c00b40c8080c0200e504001c1c0141c102d020b1219001220070362280300c87c0034544103281f075101e1084041e04046e034965039402c1070f41c060580c49000303801003140c6240c0001c5441c4584002c02810304a81d6401c0c0c02c10310841c0b0101c402a10390102901c141d9001d21450900140700d0800d40d00a048010001892050007000c1908100e407000548080d6403510100002424054050b454015440700b80064040340a01d044195400348c01c200b860800d0307a0b0420044840d500041e4001510001d0700d0340800560748030104826501f003070f05034035003682102c0003084446005c2d8010307110400290a01d40d020024400340e0444581090a6042c00ba03911404800f00b6015503200300c0e03801035101d4015615160911044035510400ba800041c414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 30470689 1250 30469439 30469451
    0x5130209060307090501090504110a03050d0c0c051c050105010b120109020c0708030d0203010e01050936010207060603061401030203030301030803060d02091e0c191206030209090a0b0903030c030a 86
    0x25540510030f24000d03001c2a0010000380d41c55001c590002c0c0030495048580c1c6c5c10403050020685050300040003181d1744140100044501303200300300d07440a5000e8044941e84034101012505984101c1440a00541c80901901d15045401d10720f0940383c1c1030780b100c001c0040410191000484400c2082c0c152a0011400f603500c00c01404901d00d82000d60707008000340d00010a1440c11072203142c00450485041d01440d900a980311030400c0200b01042da0b000d83c54180e00d07805200d645844000d10b02080d2a65440790340c603040c50385a03080c00e9911130b001c01c44000d90340749400d01c1004118820b003103664101201001842d030447d07002c260340c1e110602014184c00c1d03000c0002216503442c00b000d80c0740c5a501400c550329508022096104d2400245c40314400e80036482c0000c0c81c0082490160356101c0441807804a1001c0400c0c17080d03401e0901580f0b83c0c2002ca0b142c03036000c4050303103400b014903028900c44401810921020300704444802c05c05060403a49800400c00d00034188040d1003a60341010f000800080e00e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 30471939 1250 30470689 30470701
    0x18080c03040305010c09170303011805071701080d080108030304051e0a020a0b0a020d030b01050d0b13050903090102160e16110105040c081506180709030c0e06040b01020105130209 79
    0x9580076941c002001c0d0760070b120441c060070354000c00440c05c1700c02c008414014098446070b4140c4a010900903031003810110002c804c3d90541030303042941c0000039030422a92074580c61165030b45550098000c02030035400010035828542d881101c00317004020300b0700a50304504050b600c050f1617040045040703c080da040790f400b070808a010f01062026580c0100820781e82903854140d000d00d5007014000102502800305c0380004140070380580340c030180c0142e42c0d503440e08440c2c1d2007401c003c1c04400851a0840b464054003000c024080c440c0750b000e40f10719801076845e076411100081c68504a425461041d808401c0c0400a48034441e00311a0050820403285590b03049a1000b202c80069000c2c1809140d0309220a220038801000e40903c00c0e24070010544103140c141d442d20f60345400c010782e0300b40d800c4081d014400411544044026411135024a414503c0035503d48031504a44460f4124020504001b820702c90702e0b242511414010400a0001307014a00d030401c1003038020350422101030b000d0744c403050010794 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 30473189 1250 30471939 30471943
    0x9030f0c070b0703020a031101020702090f1905040c0f15050406050a050903150702010f09020616020609090f070e0108070f0e030c06040f090b0901080703030e0402070f030206091018080c 82
    0x400b91075030880e40340e100d00080c14000e60f2611080301c25404a00031454400c64040103008130b40c111a000b0300440040d484007804281380c20802401e047c0b45a0f841d600000d60602035000722030049004503c150121030800c400100948801d41c0001d81546c0140031000c019a04042903504803135040c00d0213601e0390240d4400351090b1207103160080c0d150250071907100c14940700014580c050089030340204501102d1201d40300c100c2d14000e1020f540182d0a020044a50b1000d001450290f44040c041e10704164031030004c545041c40a0700c0440050056404104d8882c0d03100b0801c0110000c00d1820042504014101515018103c4202c0e0100f001c0c2d103442a1032a1010014112182c0004c4c060a544959411030340c015810b282c00345280e42030030442d4507106490f091411a040c0d542a801030403445185139410360f0348807035520b11190466020310486011912480b1030303100c2c0500070740107800a4a00152014140ba0190607039030355561138550410a6816560f85004046901140d503960f81c01c4040f00c0d4078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 30474439 1250 30473189 30473203
    0x402030c03012a090314030304050708030c030d0213260c0f09070804020f06040f050405010f06091e080304090203010302030616080106050d090506010603021909050d030e0f030f03090a06020609030f0c 88
    0x1412030b407012000241c1c441400001235104500a0042c0c400c5941c4030300d011504c0380b0504203080305950092207111b0164180354020007121420600103c02c0315a566501100121016008198800b0b403116118200c2d406000c100025074007241c11003600041603001580d02d81c00944080c08000905e000101151a00691003003a210010649130302d4035520b25100f43c05008030301920740039a060900008030040382488420036109952210540541032002d02000141c91880c016040202a0400a60320b4002e000400161000645c05a5070758114010315280c24406004004078180f00d09442030b06551000c400340c1520818a005c0d80d941c283e0320019030141c101041c002c2d040d0b0040800000c1c4054040d801082c450000065840c011400c001095035035089031300c0344d680c1100c62480311000103440745000041d91a0003c1000c482116400301103403510307100c1c40700d1808681c0b00080400b245e00d015a004801032900348018622032800000d6039440c2e0141e54035851103080c001c28401e8009000340100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 30475689 1250 30474439 30474443
    0x101703090d150b090c1e040b04060315030f05010614010e0901030b07020a140105070207050108040510150308070308060a140612070e120303011d220503190302030402030c03012a0903 80
    0x42441c0c5e00341912280e0080d884140b00e88103c1803402100361300c45040205032001c48607618400b504003490141c1c00d50142c90803001114007200d036140003100040d415640d1040f041c0c0544000641c1d1b50804211000c0a00ca003400d544c1132014401c024500c0e0b40d504101c6506482e0702008565054688070f0b020b902d0300d0358445009081d5204900d0340c2026a01c1507001d1442541d00d64215082c056440006560b421006d990141c81600540443c0c0100350450b000110586220310007129940d96a440c0c21082d034001c2d5000b02c000900318000d103c181d103051004d2401505291000070890b032140780c0012080d20504024660074030b541d10005030101d02648840c071201e040642002d0b5020f001d403900d070342c030fa074000d000381c105180c24034400095074095090414850129640e1207400c5c8264400e41c0100081900d008552501c01005903500c80d038014003803040711007016100941c403402c051040508080b03075140f49034044da142600c220f4000c4648103840402071106920141d01e00451a0100c8103030110f5000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 30476939 1250 30475689 30475699
    0xb07031409040f05160e03032d030106020303150105040803070609060204030606180e1c0507051006060e040f02030906191811130501050310020c01020c06101703090d150b 75
    0x2c3e0010010b0740760441c84c461184030200b501c5501c44c6201c1510b0301e603d0741800e1901607009000c0200c0009a411390071407101c1c7c01840d441800d445840c00420985d0098001800581011061080c5c00700c0803030085030b00301e40909090741041d0505100035541d006081c0b02a10301c94840d07000400b800100c0e411540559040311061141c0b070f4513414201d01760300040094490a03803500c0f500682e044000305410030703a01c0300007104160b01c90606204440c2a000168262118000d1111001c00206184103040c014112503d9800c50901018104800c9800641d85a84c1c3d0500400030004070590104255030b00c0050480b2021404280300503c130020448101195450b0310407281d500140702e0f551100042003c0201c0f000700b10b01d5000320780801a10028814160143c2c800c280c000c07841e0602c0e030094070000300c0c100001410003030000d989901e040c0c019580c010303500c0c140f15418041000001101c6280f541000011440c0c0720191700070900c0c0c54413080c0c01400360319030444100321407180742c0c210034150100141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 30478189 1250 30476939 30476951
    0x1d0307060206010e0c030f0402060a05130609060f03020f0d0e100501080309040506180f0c09041107050616090302010e040207080304060e0706020a0201120e010b0901030305070b010f0b0703140904 86
    0x10003030b5032810300b80102042e403072002002401e0007500c042180d05c140f40c00a1800c5540c0c60310f60a10105800400d070500c1480010700c6401814000716100f400107121a43e900f94549190001c05400d40005000500c10140100b000c0450965030b130040f00c19195025400045184500a0303490403c24030981ca82071403400c0100014054000202600421004403400c028649a48007003100e110310726000556420050700004804c10b02405100703a1149d1006101e61401c40341d0780020f401c540074070090303c0768aa03010910328240141000b1b42c43e0301c4100c01c1c8000100d4100c04401802a40b210300c0024100072101c03409c9103103a1600d805076a03003c1c2c0d10840742d580b241880e00c0d00340d02802e8404d0503902c603880355210001d0401e10018134172079025010713165982452038104828001e07002c0c0b4a502c1c091f542d00c0d12510340080d11908000381c02503000303079a03407034a40700585404201c103031042e031064098070074912003400010302d00c9c01118010355050030492842c0314180d6400340640158110980d10a1a1070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 30479439 1250 30478189 30478199
    0xa0504050d0f12111006060215060109050303121f0302030a0b1b03090309011202090105040905041e200f010906030e070906090e06010b0703090320150405090f010302010f1d0307 78
    0x10544200104ea00c00640e5112111054030504a850701d00c6400b0040c2e00019000d044029601001600204189094001d082c0c8443c0440e00d15400724003100d000341e05030000c00000c180c81200320030100d0406014040d2442ca10340000e80d070340e240604080c04901180000c14403070100c041180e549088031011040d00d82c540a004992641c201303046031408158030700003030748102c070b01072080302c1c844c11058641a060a0070700c0021801840e0040089401034105486e605c80700544a1100040f81d02c641018801c1c11407920740d10709200300e0340700d82c0b0b400f8501c00251030380039030781264440068a0b81c52500041c944403012513940351038030660009004e10310b40400414203011541260b05482001070840790542d80c1c503000c03048244601800a030000786901001d100068141d4402e86141803003508280d4005440030000f1000b000c601c8901c0000280064108280e0a04a8946510a550060444a0b90302d0f580001e0031410790b805200080103c000512660700227080040600da8502908841485482d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 30480689 1250 30479439 30479447
    0x100806180a0b071e03060b0f0901020f03041509120b040206090f04050403020c04060605270d0501050a0510090506010210020a1107150201050c0307050a050306040f0e0a060b03030a0504050d0f12 85
    0xc14101805810707564041800e041c06400707000115282080d20610b450070329094100a03801580d6260f04601034cc07018941d02440030409400504503400181d102d00440072006010701e50946e010703d8000c41540000b001068840c0c10313983d40241c06481190f43c401c0010009060002d0284d0101e80c420319080a100616500150000c0c50041c1510100170490311072400342c2c0e16010b02c0d110501201000c6d9005402c1124400b0b10050159019107000d9003440705540d0f903801d54071704407008144940d80d02d00700101155800d481100030b001c02071040200d805c01e880001d40b50010f240302d20340b909400003080100e140c41020b05500103000901901c2040351103801341f07001341a8141d0480300540c20400420600c10a100480340100e100352240e0746000340c4a4801d40d01504014880c55000350759202a85800c2e50b2401184900e00707849000d07001036075291405408882e81103a58601130b44c014050044044c1d0001c04803000e0303a0b4100d51102581c90180f1b082c460060100d0f10040c46450781d200140781007a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 30481939 1250 30480689 30480707
    0x50c0d09090c110703020d060905030c0109020411040b0d0b030c0a030803090d0201050705071b090507030b180106050f07080906070f031103090901030b0601270608100806180a0b07 79
    0x45880c01c1c42080401c0780700703c605080301e4194400e2500450760030001440c1400107454138906c20400415901401d484590441d0010302640486035100c038000b00452509214014100300d059610030700786420b000d030f4003450f0301825880000803076980e0054551664104004462200f00130030f0406450384910b4102e07511741050315043c406200304005104d0803030060152510546090b40c0d85030410342192204500070390195100c407003224102101090541050280f18401c009540b4007040b001e202505018980c904045440c1c41e100c140e600521099038000308548110000e543c1507a213860700f90a007480d86208848900354000800540141000b60310070015a01500980b0b856152a081000e403649a109203150964001c0c00e0100600024584041d11130304154185031032104401003100d200c1280e100040c041100080d060000c00074280d02c04903481c0e1006010041c2d4009602d2f1141860344d504c00074001901510200c01c140007400400c1003031010081d00051280d44604107007401a0100c18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 30483189 1250 30481939 30481949
    0x9050903040e0f0402100f03020706060b0a0f2a050f1014010e0105030c010815030d11070807080d0309050307151406040c020615010e0301020d0209031c05040306020703050c0d09 78
    0x5800c8006101c8554500f2032a00c243d8014020000b40080f04900301c41d01c802031883c010500d5402d101d0700b0003180040c071078040a420070320340f40303690b51001900c090700400605d0521010450843d02c0401d4407184020110010001c0e11051400c845131450410304058100036404c04501c030302c1601ca0f86499a80c0c001840d070b4507070f0080681441e43c8038944410108801d01a031a00750f030004d2040201c0394414801c80340e0156421100f2000d0104010000c0d040c11102d1ba1800001011441c180c0000380e001e02c00d003001041c00200615070549004d219603140c29a0016040505658501c000e0502600f1300849003101d511181d2a0070405000303990b10020030351880000300c42202d000010700c0c2421300d4820580294003e4004041c1d0b60f45114440c9208a004044107040140761840311031551001d0000c1c228007000490096143ca0202c002d1500d0080d4607100c0074944a4034a551410700b98000b0121001c0d650070900140e42e0742d000d410191175500c207525002e41e551140040b00301850307a1040c130500c1a11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 30484439 1250 30483189 30483209
    0xf060601200a031b060c0206161b0b0c040509100f09061d0601020c030d020f010b01080402090415020f0a030c020d1404120f0605100609080106140409020a0905090304 73
    0x900000345003091071550580e10701d16584107600a20200740200c642d1048024501d80291210002d941c42d08140c17101c240c000c401607070100060140390400102d000501e0b80c841c4c940200605c90701007031454990b0a01d0400350481500c540070a090006450440d00507107809803c4c5440c5080440c68500d90307101c14829034031054010007020075245154052981140c014070004024026040200c01841a000e04000d0661166081c02c0e80741d03031000c0c041000622080d8019144184074140a83d096500c5c1000050401040400301f10042e80e80c4524590841e800c4254462003045948054000b44a4400c007a04002c03008517441a40550680141414544613400c0d0380c0204814003003980c1c010050080c0700369910b0280701c24040c0b80117032484242c00501a8010241c900c5094480001f154019240403a03094040700d81448200e40000c0180001c10a0304020030805140c5800580981c03011a0814840e07912420084150b66400c1030400141400c071500700f040b81071084200e07550354428400c0816503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 30485689 1250 30484439 30484457
    0x70b10060f050f090f030705040513140703021f0201110403080a1814060c0c0a08030a080c0c1504020105070c09020301090e0102091014070b0a0b01030b0f03070302090a020c0f060601 80
    0x2644500c00f40d030f40016405081c1400c14900c6410402c0c2010303040700858152140400010700c030b50b12801542e0260204105101840c889400d1204121080c44422003a5900003001000181c0b103c0419400310156000c000c03400076a04101213015001c405210902203002041c08400e00078a2030003481d00c8146034840c1c04003d118424040b01e1139040b842103c406940c1407000d0403060400c0d80003412021030800650b4404d03804400029002c44850704002e032150300201d070401d00160415072403500304070907890180c188000340c0707403c650f1411020800e0328000700c550040380469000710240e8080942c400b80c41d202c0350b91074003281c0c03000390002d118014149060145140f419101803080b00d6645402030f245440f000c106070000d64504001c0d00398001c145108214400116034101f000c1c0d4014003400c00003040080450b80010282c3d180f00c1d01e06446030154456015007039500142520450f9416a16070352181e4a801e0290028000c2c0082c140043c01801d0355603d10400100d100c0344110000d8032401c02c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 30486939 1250 30485689 30485717
    0x1903060905040b060402130503100c080708010f05060906071509060b06040501120b01020307050d030207150e03030406110d090303140f0912071707030c0b09060705040b090402070b1006 81
    0x580d00c050b81d010340300c0818040400d04904080d00100150880a0050680c590791140400d16101001242412543d51000070385145d540c498900c0340c00291603d010022541001c2078140d20544500c41c2d42c1c42001c00260220058490000350345c4c02d1600800301042545200134102c0203005084e5049441c80d1402b0404c01d0140b90900542d8180c500c1a595003808454013401203004041600145055110512030840052410840a040d5440070342c1c01580341c803404c3c6880703843d01e1803801e20b4170318240c1401c014400f0034a000059a501c660001004220640b91039060702061040d8030090450134146003a21040c150990450140c541801d003911840e45c1c8d030280030030344a0000340c45802c0c0603000a5001d50640d143c00001e0003465008107000c1d003980412007104090756001c01401c03408a92004024801d00611090b02680400b038400904068a031a513802000c51045010b06416201e0100c0c244070780361541d0781540c280c6030b84400c5003481d40c10000d1160f800c00b0200d206010000300000c0d90141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 30488189 1250 30486939 30486941
    0xf03070815060307080601060c0b060406060f03050714040f08060a020c0a0308100e010608010806070c0302061609030f03030b030d02010b090105100c0615090c05030405030405091b19030609 83
    0x2046424140140225980305914000c18240c050111541885000004600c3c414140300650081c0884d440b003005068041c0340c000d450107030040c1310500c2949010f0040010310b821401004011205180000707096031000c4065800340110340000b0000d40e000f00700840d500000340c0b103600c103a52100c0c088030825500c49425000780c1c4101c100180709504900c4416002a0091070380c0343e0000004600720400301c6c0c81d82403250705c46109034011000a8098070040101902c107103c125040481c03894400114450307920080d44c0c40f08040d1000d50341400307500303404580f14400c4007428061503000b400305292034218140180a00f030305444544c801d018240b5001c031214014840c02184001c05400a401c50303281004010700c3c64a9a1408000d00c01c1d0a010000042c46521070711420300d5220b100d240340c00342410184002c032201030f4800b01c00d106080040c400459000000e54044481c200c03600f40c81c3c1d81c3c4543c0c0c444420b111001d10202c0107000494512810700307119203040c81c40c034130760f41e810007645a031005444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 30489439 1250 30488189 30488203
    0x10e060415060b0f040e040c18050103170a0f05090301061802070209010b03190c0309080c072103050313080c07030b061503040807020f0105040f0b070212010c0807030f110412020f03 80
    0x4007042c008101c100000201002c4a687c01030044021108455a880384d4180c000072080203c41401d40e188014010008400e03010790108201c00d10203030500c25041380262000d141e010b0b07607100340400404c0ca50443e54094200801500e506905803c40c0395405000300041c2d00f00102c100d100c1c1034200c0000c200d00c2d600c1c00589100b0380c200a000390318044900702000003045011107100c20140c81e0f21040300030401141c020082c80e001301c402451480e01d06002c01c010400041d401045051002d024180071070740c4002a02d401840c04150080310350803070728207c04240700b9010640d101d4080c0340000424003a0841115205510a440b007070046061511542841e110440300100800401d101c00d40c05810300b4204d4008410041c101180b80a850b030264080c0400603620802e0301d8031380001c01d982141051014054100005402031229600c4414094040c51005020354101980c1d10031401b0728200da074005c100c40000700c2c0011036403030342c882003001680fa0502d5802d03801109038440720819414001443e07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 30490689 1250 30489439 30489457
    0x50301050712020307170114010e010e010c0b1003050f15090307020112021305131e0209030604030c0c1d040201031505060301050103240801020703020f010605061605010e060415060b 80
    0x5031080311850108003c2d000034202e1000c010100708560031080d421b000e01c1c1d002e40280b80e004205070403034000041c6a01d0b1148131140c1017002c0c141d00505266042103a1075000b585c4440756030143e80d180c03804051403002ca903001616a22619000c544c5e0700f00b02041680040c043e40d11141e456039164420381c1d9591203060002400142c19240d4803003400c81d55405050350510003d001c03000341c0e41d91000211041e00301e0840d030f0401540d800ca20680310316003200c1071580a104040550030910076a0000c4d890300700c001c0003c1c080c0b100407088041080f000c4054600541241c16040002f41c1e0500d200600610301203030b04a010034641041d035011036141e1102481110070040050b032a603802e000044014142504c01140c0b44c400706044501d40e80c44226107603001e400072100041e00c84c250350400a140045081d240c8210f40d02d0301d1002e000c5510740500b19003204880074141c3c0c0b50f50a03186401401002c0c50307108000d10740500d0302408100048501d011480040c244400d004140e1501380300301705489040c41c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 30491939 1250 30490689 30490697
    0x5060406240f030b0603010b0d05070513060302030c0103020319021303122c0102010915150b03010b0405040504110904030801060807050c06060d03020111040e04020907030209090a0f0b1206010f0503010507 90
    0x3c000040641207490351024014001261502d07401e4045400105142000c9801d600020414070050500300c015040f1040480d20a00c400c40c590b80220351664914040d1030704154000000442d91107401c400c07170099000000c000c6580d00030707034a0700f0506520781c4d001c12240700300e481c2000c1c0784140c401d5040c7e44034084103040100300d00202008101c003410203450030a06554035140c8000120740042800c40d144100da10b008210b14400290024140c0210780185540079003d000603c8000310540c140e8040d174109850019082d03d850400c00041d045030040c1c6580303c1802c000304070030141c1c010380d01c0e8102c80d42a1a025102d445403603003540c01d0b0042c24110b04840c0c2c00314001940a02c0c20142c0c4a01c01d6000f0300000480c407412108210441c0c0c002d80150b9100c40b1208140f10460526120103944001186421424003158800080c80350102030f1404e03013896190b282c0001207842a511500f02c4036070013020800d03c0030306500c4040c0ca840092007003540b1810740000010383c074103060080c103200350f0507551 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 30493189 1250 30491939 30491969
    0x10905060105010e090f150604030302150c07050312070c0206030c0a030f052208130602030a18030f0b0603010f0c0c06060509010b030402010c080d020406120506010f09051c0506040624 81
    0x7a40f0320006d6000340200920301040c03402c00001c6e25001c0091001d14026030160002e80b144045a062060f805085440e006404001013000300d00c1c040207503600700c6000ca01600381ca489002084800080d1b40310042d51001001040c4860030705094010080501142c6040c000076865000e440c2c01ca40044031181400d550b00d00c2901c0c42003020446400e442c5110791460f03800c114529054507a546034981015026a1001540340c100c0703508201560b603403a0104c0e080e141c844d41503586142c820714003000000c2101314a180410360b41c0d40c00f03401c052224055900d04000607461200e004104542569065440910b00b01c800304140c245007100a050710748202d0b50741d240d619164011100580c0440003603450742e00a115588051400e0b00042008008035900d80c8040481480039404a07a070181000d41400034540e032852440c0d0304a90800308550b8225401d00380d040b28080f18002c28400c94400600c41c1c0140c0040004115507a4050443c0240f030a80242c00a03040c1888403408003610b020708405419001c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 30494439 1250 30493189 30493201
    0x303010b07080705010203070c05161a071509030203030118110306210f03040e0c120106030b03010e030d0e01060b120a0911090403030f0c2a050703080705010905060105010e09 77
    0x1002004282c0c0318400ca80d1812a140e181c50307007243c00596103000003518485c0304030300313000040280183d101c000544480e000c40c5070444911161062a819455621001c1290310510411000903901d000c07614109000c640802d150007516544240a14800b41901424409140c005882003c4905031822031092468071101e0411056244404400520030541945501040000e00c42208094166002581c0741d90070f10300c8041450308003c0000343d0780c0b013050200b00855181e0780c0c00d00781140c450b030500040300d628041c0483d0241541283c501050320000840c15801842580154100700d940d100802040b41c980380080380910030070b6002001441d0500114550403007540c04007040310b100d1080c1940b154450000300c3d045110131641036001c25515070182143c0ac2840c02249030b40701c114036107044070f004400c45190060300326510709a0b6200358002102c08021042002c038000d160020403694450b582498400d0180540030000c4866020301000003030154050403a0204e00304c0700a040c0c0105903909 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 30495689 1250 30494439 30494459
    0x5060907170103023a030305150f01080a020f120603010c05040b180310090602070309060801050a060c1401051009150501050301030b060301060302060c03040504061502061906080d0e040c030e030301 87
    0x2117505000c1d02c480341101c450381c2e50303c004c0c0c0d1a4902c80b00d0201c0103043c01e4908001d8119040100b900b4003103504c415410166540b18100303a45503c0e402d007420801a202c0c0080c1000a015440600c1c641103400540c1c400760000b10410a4402d80d0210000e10131480d80c9401150940202c0c032840700075031001c2c0b010506520966010f1007019001400300d44201ea0f1204503142681c110800558029900282c0c030014158061201000f406090900507402d501d40b902207110a443c40c030841e000c01101401420412040340f10341c901401d190030080c082c6040ca01d42c60444001b42d4030445180900e00b000324104954680424002c0380c805854883c2142e03c0c589a9a281340002490503615550f9010080300503640c0304041d01c9840e80b00307001075031118200810f01c021180350790405443c00c0f0700180002605940081c072284c1c01b40c00d541545035460403c19107075000d00000d0300115554040c001c0c018800e00c0d0b00c5a901d581400d030444082c410480380c88001d50403609045001c940c5c0307400400051000c2114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 30496939 1250 30495689 30495709
    0x102130311030a081e0702030d20150c070602040e0103051617030d0b010302090301110417070506090f03160b070b0112120e031609021e030c0a0e0109030203010c030506090717010302 80
    0x9414007a46000c80647c0024240056582498049040c040e4003034080310303d00c040d036030408c0b1b1008010580342001015030280321400504d500200799002030000c0401485070103440040c10f4840a20815507100c0c50015111015061089a90035541a00040a003421902e403209425032001961502c003090b6000000f5182d9415000d061603002c104900043c0c03400d200d00400d0355080408941c40d00c0c00c0501900c0d405500c400c120401f540094414846a9210411030300800811140800c07150750202c00700e414000c00300c003041c50601c8103141c0083d02d20758a0009203140f910543d089e030340c1c583c0ca927a880e50503929000310181040c408800000710081c0541c0803007910b0b120080407116518445132070100510350980119000b10b8000c40c91180d00800244601200300c40b00c4c8c100360451501c250b2001c65405400791450406c21100840d103241c0e401800400055600a03000f4041e111020b003028015200503124140614202000260380300c4c8203030040c50b030500291001c0200d59107036400700240414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 30498189 1250 30496939 30496987
    0xe0303100b0d060b160309170303060603040f0b0c2a0d031509091a01050d0314030601031d03190206070f030f1b0f02060106050306060405011b050102130311030a08 72
    0xd66680040f4540f40c004c4090001e51008100400e44c060b40c902e00104074035120f038011000d078090340c1c4440348030802c00b006880e40100281c40441e200d0b81c807418890303c0c076010104041d1001c006070061149165142c0018a1582c6054410704203a6810542000e070110381000106030355001161144e00c0c46100b50400d10b01c0c02c43c6021590806619400c1ca4001c80e407115200700ca034807403110100d00300c82c5400c4a4881c014002111324035920121500c000c6c2440c4078102c0045070350000000003d0781030b03000b035202d400041c05422400c41c40d07002210469a40b82c0c44228608221082d80b1034045659100140701c52295119540d915040c2200034401d82c05409070700300e1a00200e4030b0f5411111582c400c0c07030f04d600596003255568015842e10726030203810204180c21250401c070701001003254a440d901c0488044803028613095500b4008100000c0800b4521200100303994000540018140050700c92001502d0280000211f44001441010360302c0302041c03002404440c090080d5040c8803003126410181007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 30499439 1250 30498189 30498191
    0x20307110f0f011b050910092c0f0103080919030b040f12020a05030712031508030a0f02010b0a0e0403020307060203041a06010c0f0803150402040b030108010e0303100b0d 75
    0x480c5040e020303400e08000021100c100d40c85400b91500710b0009028044101d00d10700940c01800e80714083c000c00910850079014015480000c0b403844052080c02501d00801c2c642c0446002904011440422010b0b445840c03002100039001086c1030400901c54035049035444800700e46020340d0001400310100c0e1000000b2040e0782e1901e000400301d004884034034071451164580d8080c5500034a04139507041411405c0703404540c4061072241c00107030000108c0e005190443d2304210510004802100a40000119040e00c01c222140026140784000040d2001c1c8100e5103c109505490000c00c900701c402c1103c0196000350005001c0101806010308907800c50701900c141d80c81d10300aa10703980d082e81e00544003140d504802e1038180303c2c601e17030054580e80c1081d000d180c103c11061103500c4003c2c0014903400003514003000003001c1540d88000f80c1d8401c600390f60103031041d5210b941e0b80c80c9480c4641c00900c0b6282480d400c0400e094451040401228130800e07042a65407009420040000c0c21604408000d2480c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 30500689 1250 30499439 30499457
    0x1d0c0418021f09080a05060606030a0e030c0109050f012007020102071e03030905011e080c09180103050c04061203050d0b0406090c0212031005010e060f03070206010303030605030d080a020307 84
    0xd0784482034215120381d0705400115003081007400080903ca025808076010745c01600500d030000c0c80100d1401d422038800c64009441c2d4030382d00b04010080c0010038000040b07110000f000910290190400c407030a40c05001078030708042070031034940e0aa4056070261812410500410106820b889000e030008600601c115070601d41c17030341d042d0342d01182d0003254031440d0480010304104160b4848100c001a040a02c1c1c20440c0d1030228024841c941010f180d40c0007800140c0c40090651245003056502030000103190540600302e50b050a00f00c070100f03010548060007951480501d50600c3d01a40c0203c40c0c4610420325404800d031001c81d5183c2100d115412069101c450580840d603550258801401e20004d0000e0248480340000e0703d840c02104005640100520070030454092400d04001190ba080c2481c1e07000a0720080001c0d91485507600c02c015106c0e02100380b01070b0345c0d40001e00c01d068078401c2c3c5040100c03039110700401d41d882c1000744e00800000d60b10720000d0310102c86500515001003950810b00d1f25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 30501939 1250 30500689 30500693
    0x30510050d0c030b0f10080102120c0a0e091602061003020109050907090e010e070f020c0f0d080706020f0a0906020c090402040209040b360603070510230301091d0c0418 74
    0x41e02805507803e000075080c005c00d001252207403281501c002e00c4c03c80d000f1450000c040c1080d00c0d0454009218241030a400708503e2800e2b4000d0108510411004000c9041440c02c2c03042000701503803050041380144504000901c0215141a40d0000d50ba016198018000d14000400112000c011b120204101703c445000800c0c000349110140641540741540326503190805e030041c041111650075400319030052110a81e50344800c0d05080c4124820703a5151a0070510741031805141c80b0303200c0018038140c40002d16031108400e400242080c2a50381c0c0c0ca07044603550301c1c20102d0762860322401c0303141c0c04034400f00842c00620b010340c0142980d20010340301056a18071400002e07898800d01004e4041240240201c0c1502c02150b0080d0103600070304980022581451804a55144458080d8500942c2c0d80d0031f82810003401842000d1280e4000d03800d50303854042c040c1c420f281d1070f0030a21601802c141456030740080003c0c06552015072005200c02003c2d000f4a8004100161114000062200740c0d4501d5042c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 30503189 1250 30501939 30501953
    0x130f0f09051b13050f0d02010c150204120b0402030607050705061609080d020d02010506061309020c010b06031f0515030a050c0c070602010504020901050904050a060c030213030f0210030510050d0c03 87
    0x7460310f207203990071480e180c82d10040c44418040700b04118402d010314204100182c0e001041d4250319a00501142d0705494041c500c04024891900900081902139010b042004808031000d0300c039502c25000d9800d01d45694605480345d014182009056400c01000510031404111320360008030820b2505c0c50341c10380d45480b0203060040001648005030442c0181e541340a809008150704a00192090345c5060400765040003000d20502407002995000a00e14500c41825040001d5201e4010300c2a40c1e2030030411810040c242c802060208000050907000400303280660000307544040c41d10b0395900c0d542d02c801003c00100300040903a003480d80c061202441c4024204031100113003402c2d40001a46d0f0030a8010044003140581c00140303d40b58040c200702c0000d50105050600d40d034040300c08248155190000d42c003034000d4844841d820b8680c0c11000092050030341070309100038000e480707040d414100c1500880a43d03004892640c00c95100c007000304100d0822002e0420814040c0780340d024455100c2c0d441d44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 30504439 1250 30503189 30503197
    0x2105070f09020307030b090106020309091306020309060f090105100e0402120d020c040f110a050a050405030d080f070305041e0c0305030409091709010e040b06090a0b130f0f09051b 79
    0x7003403066000c000c008403940c15115100364600201e80c00c400303a41c50032200075584d04c07036024164016001d003004950b6014013408121002d0341d000105540741c1c43d008016569034541260031046200510010134005007040c85400d005070840407441d5600e50501c003c155003150003030b0040b41c0100c0000600f00c10300c0402c2c802c4040146843d4068401c1a02d03c40030081650781b0130307404c02045803034004035201e0f00b9209011510100b4540c20302d1034a540301d4030015203c50180307a00c00d50305400340c0300c41d041901d0fa03c2000d8905c2082c032b0b5227500c801d40e290040120102d50341120014440d4600421111010041040c20910a441203c0c01d02c0601d803280d89080c15a00240d00400e070b455103c2c0740382410442541e549150056103222003904022403013000a0140c0f14440d0b0b032a014650f41c5511000325115107007219007003c0c010f410310071740c141c2d1a249940d495005041d40c40c40c072003100401140b1015400b80031000c40e84100912050789041c000240c0c01828040c2c282e80e074040010800780300e4015404094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 30505689 1250 30504439 30504449
    0x7060f080115200f010b01110303010e0702070f030302011e0b2d1e01080916050409060b0402031611030406020304051c050d050307030606050903030304060c021f02090a0f2105070f 79
    0x588205440c0e510344d1803c0d544e04070461418000c140281c40c0c402040081540c1c119200e036000410142c43d420b00c26400c100302130f00440c410f00c0d41042c0100a0680541051a105403004003a101000480220310103c03090401116842900a038000c3c2c00c0c003540f0140c00d01803841c2009110703000c150070400a405003002c031200195698054021840d070350b81210180340d00c460940e003d008020030014464002e88083c3c041e051155682c0c0c0c0d215414040c007503110b91284100948215580c1c00c01c082e40a810500610440c0700045103083c0a0b001d201001c015541118441e030000d5040c2070a01d030802101083c400180030618000c503c6403404903404005484040c51651601540c90504100040640305560805010302c81c00300072403c0142c03000011a03a0054014000060180041070f0481c2059182501e8079440c600740c81d803400740f2003201d500400c079055040f100c07000a80d030f85110315402d1025520596032500c80e40c000701c62038100c842c585c400c503c80c0300e90140e0710f4047d11844482c014443e02d802c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 30506939 1250 30505689 30505693
    0x30e01030c03180b0a18150905240f010519030807110303130e070503040f230105010605091906020304030807170403030512060d0203030307050a051c0b0307060f08011520 75
    0x140b0075a4981d07131041e8102e00d100504401e0552505840704c5d02060710309244900b507581d940523040b0034040300740640fa94071100421600c000103c07410400680c0841501c0740095081c01788000103961400700032400c156000e01d4a00d4800394559101e21040d0b030015241611b001c03482202140c2542d509100611803e016000110320683c28000a0b40b4040c1004001d0f42c1070140c200b080c4000300b1a440d1100c5680d40d80000c013030400034030000340341003644012103c0003560360030f203030004c50b0680d0000d024140c1c1180949400c00c0c164100c0c0c4003066850720606c07581001d80c000700403e1001c1040c0400030a040c0b800b444825540400c108445d110304d90043d44280c0c006403003c0340600320800c0d215030b09500404100c0d01c640068203070b030700001d44038032000d0011014410300003091400c480c010400d0300c0740c00240800581c000c1184107034020191071966035091090140c1c010200e0707072a000301f041945001b0b841c4e41c1e5800170383c24110116075012030711414409000d8400400080c660710521985000c80100700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 30508189 1250 30506939 30506941
    0x207060f020a080c040b0405150c06090f15010b0a08100806090109290711010605030109050d02060702030a05040b09010903200a080c010804060504020411030406090b070507030e01030c03180b 84
    0x200203240c040050300710b007507445040100300003c5007800203070740a8910444040709d01101c190b111240620545217440128010701040050b80800801c0200303190701803505440c0141e2a2010311481800240508404040d091004010841c800c0e90056880301348a05038042241c1c5a6045915181045078403171066910780003c42d081101d03007803000c035800030420200c0900d148410448075881e140200000c1c00c00050700d02401c0d4080e4250019001040c01034020084c802c0603061481e140c801c0e985403103000d840783c1700c0415515880002240c203101443d03660581403500301400000c260b4803c0c0340c1e8074104016070700e000c000b050041c015203c007075016240c0d03000141040c01c20f002c2080c29560103810039130450711542609982080000c0e512680c80180001d856880e4030001c0c0041180b100055005403000c0200000c02130139034013100c00c0c1801606000003a54507d54200c0700d80c0300301c14000b0005504000424a070754041d804c10f5003114010b04010818203440c4540703483c1c0240c148000d68420301150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 30509439 1250 30508189 30508207
    0x5010c0207050d03050a030b0a0f03060905060f1b0f040315020903010e1606080a090c060203070627080a03060503030a05180607170c030c03030c03010306050f010503100c030207060f02 81
    0x803503000100016a800580141c83e600d0180c0b1314024607000b0414140c462032030314040d0741d0b041100009014001c2e1180ca09545070306000b00140580f1804451070700c203c2e404540e03180400c10105106510f84081003001c0602030b1a01c8201d43c000e40600048640709100c0400046c8840b000740f0301d482c1034000e0050322090030404040c207503120315112840e150845940c2130702d503498040c00c072000e49645080c0407840d40c4030361700240300902c8004006040d068070040c02103080791b408001401414010f407814011521201c0003c0c07203003440551201d2821246070007140000724100083e103c0072645082c002502680d030808079085074014503621000400c00107100c1038031405114151001c0300155001e60509529070b0700e0341c00c5201140d001103c600c0012580021455040080302d10260080c0154ad40f64100f1824050140e0800e0204503545814000012804800002098100c070340c010010000c058910270031800a14842c8040e40c205034007041040c3c0818024000c40c3c0191450240060343c0710250 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 30510689 1250 30509439 30509443
    0x90506010e010f0207051203090a0f061701050a03060c020f0d02030a1403010506030105150c030d0b10031a010503060d050f100c0c030c0204110417060103061802010206010905060a0e0405010c02 85
    0x2121030241400707000c1c0e143c03070340c803560000303400080e9601500c895205004489200780346009a0608070351061300740030003240c9240b0308e0b6500c81c201c0381c40307448070135640404600c1001d130903000b40a00d82d04034904500c00c001007809034005641c00f541d00d0055030418001c45185500b04903a00d200c560248e4030001d00d046400e036110407800d19040f0f21406107811541490000743c1c1c00d210601c6032921a440d4002400c4841c00403400700c842e44494102204c6d9581104003003030740906102d0161a2280808040c41403006004c0d00031003c06050200c0b40340c121440000041d10943c0000e80001d030801e510390010b00018104104c502008440354000301071500c0d0004102041d11b0b240300c004000c00c10b8000101340000c3d0440c0b00107807980da0407100030514850302c1c109400a80a40d43c04000710405136603104403d003c0200b440740c1030b00d024035014001002c40c0078041280f0310802d180240160321540040002944aa00c050740200c4001c1c1070359200da035212002224601c1c1a5410398140c3d40d02d00c0650805501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 30511939 1250 30510689 30510707
    0x306090b160302270103060819030f0c03020309040e01020f040602010f0b0d02031504030203090d03050c0f0610090e0a061b03050106081905060409050d0c112b150609050601 76
    0x325103001c3d46885a2145840740c10100002d951580e190384481c5800180e01980001c00600b01800c101d89a1941004160495150044060380410003420602441511031102d03a886140c0613001181751109000c1880024200c03005444029542401800b580f60341a200400061100390b0000c140425040303500004c80b40084c880078400c82140e840f038001620302040705150b032541440f10222507a51810160300718030803010b445030701010b545140c8003055000009000b98464042c00c550440d403000d02815034072501031b140f412003e010343c901040302044940200ea0301c5c1c0714810039100215603558805090307400d070724142c3c0b4800d1044005880d40e20703494401c1c28010011460458418108050000e858060070901541c129031610009a1381d519242c00c200c030080d5008040300c0480a444074010315891003040100c0b550f110a02c11032109141c0a4070b0703004070300f46d4040d0303420100c101140d8100302078a20450840304855011a4003000841e1403040708010041100042124a4000001000401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 30513189 1250 30511939 30511981
    0xb10020304050a0f0f06050f191e0207061d06070602030a05010302090c031501050318060405010606020d02010614010f0c0c1d070c0b0402040c0507020405010b0a02010e070803031306060306090b 85
    0x700707003108004d0001700502d10400c9600310f081c81652503103141c85600e110320440d0140d00801d0380d0b41440300c440c0c0da840740c1c40820b07010240c107403042c0b19005d081080b03840d000c5510600c0001038180720802c001702451700007842e80e050000c04c11440c200070380d582c49003642c00c11120002040d03a500d00400c03c0d400c10140740f680c00b611141140d403842c03618003840f95180814001c414100003000c40060a101d1080c01840418811380c003c841161400e0303c0d040340030303004501a00e4010300074260031a50550050007050241c88101079181070482c0040011115284202040f02c00c02440b942d2490200356442c00c0c44020f0712400b650348000f8a804c8001002155028007004104050541d04001040b81c0c8074000ba0041ea0488001c6004002c00d00101e440d0b0080403000380d402490103000040410305900140021041c90300284070042c1c0e0400d8280d200c080034070a006450704100005201c000300c040200843c240f0544000525a40302d4803004102c62001c00211141c1e900602800b00b40c206001e42509124 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 30514439 1250 30513189 30513209
    0x160602010b0d0b0403200109150b0406060c021e0a06020309010e0f01080406090201030f1e06080601030f030311041a030402030c04020f090402090f0d030815030607050f07060b10020304050a 83
    0x102455640340500c0f50001c0c4040c04024444152081c0c0e01c2d207076a820040d0460550007032040344c0c0f050826072140490074895421552405030380c54042d003001c1c042d2030b088bd90b581d12000c0511003a034092004403900600d900c3c00c20714508044411135580e010405d400742c0000d500854450301000000340501604211031840f414900340c8080040c4c4c0d1000c5240c0d40294000000f144990301d1384016000340c000746002e04a000c2c1040341012000c82800307075060000c072507004180102d9554041c0c1030b40764242808054a000300311010003000c60b002c3d8111500c24902068003524044d902c0c001c0020486100c0403407000c0b08000400c0c841545400c211030b6801030401c0320700310729240e2031f8090030b05103219200300d103401990040341d224403a0351203606074860300300007421040358428035150040403084c0c01c8845018203582ca04509403a8100042c0091280c0c480381c4800b441c007030b1001c49030481030300114411607109485440040311510b07070750b210002108071600115140d6040404000304080a41c000500744 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 30515689 1250 30514439 30514459
    0xc080616080f010512010b09010b2502010f081012150b031b010e010201090602120702070b07050706030504080c0111030108071208040e0402010c14030d0b030c010804030f11160602010b 81
    0x91102d003140181140d00c111842c14845030b102200754050140c5110b241da01075580400000c5450012009002601404c0703007107501ea0034403c070346c0e20f884c101c0b01a0103400030794180b40f001003190003004d410342c1140c0302c506100442c60361030740ca00301d140700741c0b407400c0328141480d042d01240120386016812644070103e0240103417585084e14003082e4042c1617901810440d03264180c899030390003036200f01e5005410602c00d40d91103842449c0b4210b5003400b901d900e0010321503031800090320206401680c1c0d903140c2c01781c007500c0c0c59407070b00b00210040c1201800607038407880108402031307452100744290028503075000e200c01d0310780d03252032807150034086554855142c807241c0c010ba40300090301c0c0c0000ca030141c80b80c515155035107890307a00040b9581c004104000b031001d00c08600c00075050000201a0801d8031062074140921a000030515446034424019180420130407001f2030b00080c0100e1001c0d0074882e442c50665040000c030b100207454441c9031034041200e000d41981c244a071a07030a001d0500c1d4110305030313022584 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 30516939 1250 30515689 30515701
    0x30c06050915060103110d0f060f0602030f220b03040f0209060307080a08030a0e030a03060311220c030b060d06050306090102130b0306010c080307020309040b10020c060310030c08061608 82
    0x40450081c495410183e613107101020085459064555031204004100800300040048000402440c01414ac0e0102081c10003e0454800001c49007420741400b00203090080c004c4098692581207200070800440035a000b20325907503804041c52181d030055606030651000c40c01480f0a804024050703600a80000100384012400080d104121a0b400b0340015620b945010281f0010070310707010381c01c00901000804200542d0700d41c012209481c050200704010001100c20020098404003544800340c010040f508890b80c00e41d40800000a290b05002c18960600000242207034440c45a0600031981d561062103181001c00500e9445440980214600407056844d0300d01140548140080e40354000000358150344a1100052070640c440085500e030705040c20040c0d241d0304200042ea0249141c281803039924600007022250005264003d0314959558100703001d407542c0014215140f5840c0d00400000040c0d8410f0b08100030510035016002c641081031284081c8a108100c030300c1042992401d1143c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 30518189 1250 30516939 30516973
    0xc010c03180e01030507060905060a0e0103020304020409061805010f0203040503091e0603040606080f0a020f100314010603021b0303010e06130906060e07021005040f0b0402060c0109030c060509 85
    0x50903901801c0540200d010300819441100c0e5981001484503038070b000000820a00182c48819181c5170b464081c5a2921a004c0c44103a0003503904400008981e11060b45040d4086e030300850300b15001620110300b032a200d85a84c011307102e0389440003d00d401d107400000705000081c4500100e140400d1070640c51420303e51030b02c8c0d941c1e00809081c240724800318108021804160700715144000c10140c05540c5920300b500301400208500e100d042c500d8010307440c0100a140c00883c8220312075a00030240e8449102d464140083c20809a60400a060342d440c2c07801488960745141e0307802044c16070390269969000d4020054203001614006255500c01e10040c40420650341000d0b0307209000742c0f121010f0251010407507016200e6070201410040c50940040791016941b002144520000e0b001c88545e1140d46c070b0450201e40c2c0c101d81c064450303c400f00e00c4200181c000c41c00550171034001070130242020504c0d03014a0840f14452812030200b0350301c404a104010540c080e01d03a03c503a8003000340c6041c4c0c2e8541f096503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 30519439 1250 30518189 30518207
    0x70e010e040206090d050d080402040606050915130503010207050304030204060605071a0406020d02030907030c05121b03030c03040b040603060509010302030a03200d08060405090c0d060902010909020307200c01 92
    0x81c40f607030010070000300c03603151a03d801c2461600041103079881c0c03028403000340c420003003550305901980c10180c000c14494050401c5501c80320010701030342c8451203104104101500601c50800e22a81000000501d079a001d0010b8141140110059540e030f40c950300c100300071a100b0744e1040003808424012840415202c2e445910400c46200c03290185a880e441e00200921413000180c80e40d031710100c1404512100060a141620700c10b0030304603011a10f40041000709950b9150384625688200b40c1e2020310f000f00c4007906046000502280d040c010302c000b2441c2103400940013088a510b001c107040145507458090300008000c11f03640da5909506540209841d4920f9800180c03d010704105a0074003922900400e4500016540648401002401000b002c0d224280c0d0064450342c142808a420b024002c40d415100c05001042114a40c609aa90001030a180306c016410701c1403401c03000a0120482c00214460380c059036980340849070b000c10340c0000c160703080081e02082d40f021090031102d0340c100c4486 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 30520689 1250 30519439 30519443
    0x305070507030f020712060b090a021602150405120303070e042307090308040909030e0306070c0f0c1e0305010c030903020705130b120c0108130b070c11150a02070e010e04 75
    0x2d41e2440f04000d4141e00e014011390054080c10b0203066804140002039100c1c3d4034143d0f04039041040c613202c026080381030f40070b40034029040702a00001c030300061a1001000701c08040460f0094201942e910010b0300101c4100e007030b24141e8000008011905038090110901090222001c110080e1f112074040b0540a4082c96902003000c40c0012880072400303000c4080c01950b01c0031301c40d0764854481b0b80724030241500b1101100810b4012408190600e0042902032160044c1c2e80d44d030384c5400084c0c03901840d40300036410039a110300e82e800c0c0c04540705240400e42004141d0821a00700d01914603d000d42c01c6507103002d901010545040300700d20009034089000d0003201c80460701e02a03401c82110306000280441c410a80e400009002d004418100114041d490054240c0b90a1201d645000301c0e140711040b0020010315801341e5100060005004440100c0424010a90940080e85803000300c1e55220b0b00709103c000d006801b08010340e4159041200501602140703000110b2035140c0300120b0030030400a000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 30521939 1250 30520689 30520697
    0xb0103080d0905070920040b0313140304090b01110a0c050402030603030408060123030a0f030302070c0e04111207050906060711060a0e03010b1008040f05120a1e030507050703 77
    0x150a624429980010b9140da402101392000700703642e41410001491000c8045d440610b1254140812a034214290f40446180c105100c1ca584d64140d60540d45101851044907c450354400c0310601c2803040010b840030300407481c000075045080030005001040c0907903240b40300303912500d2040006001e0208180849200751805601d80e201ca000281c02d43c000d03500115018401c20380009240701c0c5207044000d01001100c10b95034170850381c1081c0350311903140701405003590a03400c4044002a11960042403100d0155583c0140c103612041540381121040e101907421038640d450034140b03031900f13500801d94008164020710440d40707400b0108805940013000903104240100300801440305042d080000e40328018105959240e04d140040d092001c400f05003402076180024071592030410420030203050520742c580d0441d50303503103941d520300b8522240f100b140c441c000e1410900f0181d0102c809000030808036190881c000141c1c0c1081130801e22544500310401d42480c083c041c1d0580c00400b2103a0143e01850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 30523189 1250 30521939 30521947
    0xd110a0c020910081005060a06030c05030103120507080304050c010f0f02070e04170a050c0c03030913020c0a0512090f03010c050a0f021c030905010b15090f01020c060f040501020601080a0b010308 86
    0xf6141080302c855440484103001d14030048520080315405607116080c101c50240b4134944600040302200c003480300c080c010450030401400420343e0100d1104016000c2d1414604d02801650f902020341c0042d02d00701c07610382c4044244176456800c1900740380200c115140421030001749002c0295611980d1240c02d1100a1641c046010b004c0320b407520790125032140030415600d092495008245d07038000705603d0782078043c140320032009140202c11518050001004050f03071140e01221030000303501c0314881c00080d103d0040d060001440a02442036143c42c51302c1c6040e2219865414801c10f0b00d04040b03024440d0749003503145075010343c001090f180720300c1c501d00c0c104056aa6118041e8a4032181c00f10040110002520100d591035264101c400e00e035205100030300c050700f034840500461107034661080040340424803034108581010840e81002d00e00500c1114082c00411001c10080d9011108a00c14450000b60501c003d507010014070340100142002820400300548400d103640c01d06000090407000300107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 30524439 1250 30523189 30523201
    0xa0b060a051608041716151103160302030301090e01050c121e1003060e030903100209010302040b0d09050d0f05030c090a05130f050c09030703020d081303080d110a0c0209 75
    0x81e41e0381ca90302e58090140340da550b4a4000924603000003640c0d411042c0709a81c0c070715240b518134043c00c030211192180060340c1600750003030551307044540116071a07141c0300510240f00da50301560002480340f0b009401550b600d50401405500b0780d0030203101c0a07901da0525060140002c89030040703c0003c01c0f00c1240a42c4c54617550204440c0c0c481e10201604101e5030101840b03840348401040c00100ea1145504010521074100d545469002d01901558590000700301c06d800c00b4200c0d0000c19000c08145401407500780c68485200749500484d01208010703642d040501c00b0040308100f061018284d90a041c003c03482c0c03000d00100303030b40720062010342030303842c041039070301007601c0300034080d805014000c0c480e0810444034182c9200415003045c000309900e0902c13010030940d4404500b110b0784008058040c00715603045400b44106158042011642c9000401041e102d0500300c0f03440002a52068485545d5241e0004504040c1c4690580c17000c0d201c03808100d000480d90300702d02c07186503056041d91070399850350b150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 30525689 1250 30524439 30524467
    0x60b0a0912140f030c0d09080606090403020f0f0109020f06250507030803090604020a1e030f0c091d060c04050d0210030b090709050109080c090f0c07020d0605010801050a0b060a05 79
    0x882c01000c49101c2d05441100b990008400350165403e144111aa45c10158904442501203807091030320b42c1d080300c0081003680c281006100c0d17000d4005d004072404503040070411460124414a02075959558807034000440c6009110040d50400846400c2c1c1803500400700c007050301260508915900380c015413800e040040074007900d0000d50304401035070348901e451107072240ca4000494003203100b00e1010f1001b24200480301310011500c3c181d0900708113140e0942c0d980c1407002017030710320070346000b480f205000071070440ca8010210303500072000c3d8480245140040680c5041005840740080400510003841940c40b46101c614074160100c866001101d1902010780c0203011103048907400035586400c00a031260040c035010211340c4203a07219290340c0e6490080c2d54070740c18240744c0c2d682c0c005050b03000f0512100c0c40034022900240088081032425035558005842d42c84844012510030361a01d00420802c04280f24095020180031400c0c00700d181c50100159841c40741c4180700080c0314001c21801540b01803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 30526939 1250 30525689 30525713
    0x608062209030504170109031d011209030e01080907180911030714130203010302030d11070b0a081e160f030204090509010501030c150203090f060c01020307080109060b0a0912 77
    0x1450008001114090a00a006600c14005d1400046096181142200052081441150309a920252402d070039902c0340d841c3c6412a08503d04001d501509100c08540c030b4030554180300c1c480d8584103100202c0c000054082600282401c942e070300030f81020003600c0d26881c1990340781140010000303240586450304001496843ca00759400d03200d19100403542000c0100104000b40b0101e4500180603100b05140041e44800d000094042e0001c4440500450080d44003000f819182010740d25615200c01c0ea80307001343c0106d00301100040c0040103100444141d8014140c140d04101c01040451401071007590821200b02909400c0002c1e0340013880000d40319505403030140c4411039040c015818500703101406014207020a48611209020005010121031460b070748406054010b035041c030a0950400440c407110f0041a600b0980c01c0019902d5002c003840114410201034561101c154107140149040362800d03046454035000c1040300315141904002a0320807601d0380c400e042c5070f10719189401c480d100e035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 30528189 1250 30526939 30526999
    0x3070c0605070f0936020903030d09020f010c0f03110c0a060e10020105060a0b0309190302030703020d0f05071401060b0a11100b09060405070c140a0b01050a060806 72
    0xc58002444142c036400800380d4241e040c26500c05840e240c4403071000d242c0c0d503c4100c400c04100902c00e201d1109074166220350103000f40031500103003011049800309042d503000000c8100312a641c0d420840c11494a43d0008203081c3e020320341312600350305c266554041d100c1c160720301900780250396081c4e5054040c10070240c0b03550a80944903501d40c0f039232100c2c0a0002d50700d10b0801840794002d8618000d0840c414455940f14000080c01403074054540000c3c0c8100764009008500d25024082e40f202c08400d881e410b0b01250b6202e40c4c02999a0221420000d00b003000888401e801c0240300110201229403101c107454640d50419801c000414284d088180101500c0d40414495a00403504405081d0441d041070740b451020b01c1594030490025001d1401c80d41c0000c40c140e44201c2070004100d250400d644802c0d0f01c10080d05188444a206032a07030064800079403640e500e02d5100c404010104495200100e0040c002503410790301c1141403140240c420031004102d64014160640c0d009511107100d030312008000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 30529439 1250 30528189 30528191
    0x1030222080d02010e03030601081b07080304080304020f0a05060906090406030209040c080607090602070911070c18060503060c09040e0307080304080d0623010f200a0302010c08071403070c06 84
    0x507a80c40c4490348600b00c14114901651030440e484800041c04001c0300d11410050f035a081881d565100c1807a03202d0f5854401948194050100d040062080801540114011001140c4074549032040010040390f101e0740320301504403030070104420381303442c000e03102d1014045420319201c182a1010400511080d44065485103903142444140038401d50004242c0d5501c60956070240e07210041500c010503d4491580140c2c80203008214901407039020040c03001c51880d0b5103183c980e503911441616040c40d009640702180360f06094111070b00320b11a00000f8a000e6000e031280745880020750b035403402003c00036400345484030814152624144102d405040e8004025500c0e418907090615480c0c01c0341d50703404982c5240c07080209507082c2c0e00c00b5403140044181040001d850501c4011180076010b107a80005000d0144074626818010502044900c100308005110842c55410001e096601d601c1210040c020140c00b8894041c0e03020b4551541040300b007000581da9225210b0481c3e4845000c50054199 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 30530689 1250 30529439 30529507
    0xb03010609020904050f0f010b03040c080109110406080106031703070c021002060603070506030c0304150209060a020606040b04051b0a0e060403050606010908070b0913060e0c040905130c05010302 86
    0x803980c0600b03c207003025101000300e40d0f01c440c1420301d21001502c40250b100c080f07400400400c8150401198064030070780d11030340c00340c1d942c0601d1400c2d503848010071a4043c1054245500780d08051240600821106000703115039403541d262a4429078062070b05075032918002001a60803070180e0003140341a54007400c0e80c041c140000e00c00948403441607400303d04c00d0198980c0003445183c0300c42660b00502d980740761189581c50f03d9561402e0f400708001d130f581059809124444c1d486c0d582c407018000d24040798000e42290702e007280c100401c94204003003a1740708a10380010712052500c50080d6a10a0b5507007440036594001d416010f5802521074910702d5800303080000c01004104001c03031b45a004000c281c0b9442040c9841c2c0c46401e4179910340e030280b01c000d0101031012542515020113070784001010450300040103610340c43c13403d13020380c01110ba072407000e00000b4080001c1d40f00c51040035131101c103101201c9901a00340e42d4981e0303007403528441c071410180c000c6450079204d04d10400c955000c5414602c03260304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 30531939 1250 30530689 30530699
    0x708180a030c0806070518040c1806030e0c04050403050a0828020403110306090622120504051306080a03030911190503010c05070507030b19020301120c050d150f0b030106 75
    0xc8003049000703880c01d60144a01080e100c5d8000c80940306855080940c80160b51440c00501008103550b454120400025480010850a440403024043c010765a0040740038100c0c54040c41c0740c07050f1031ba041d5005916103420400800d622034182c6603103001c50300d0a0f800380d84881e40d10110640c00c003c4145420360381c04d60070702c1c1b40c5040c40d4000c1080703c2c420b180540b0a850220101615081c0c12145c004442d00f111000900040000301500701d0309030720640007000d241c25a06c0c5e001d00744458480700000f00b00d00080921440c60311031210b0040c5801010103010b1241818035840d01e41a1021008050580704d01c05001040b403a04224845000041c1854100c0500021403d5502a4501c5014005e5207000c0640e244140310f6801c860076035030410020012146503a49410314402d000f040c511000390401126905152130703000450090108140241d85000c8509047c8080c0c1040e9000d580302d450a4800140050b10003032803160300c8208100005031846940800002412020328465415442d009002c24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 30533189 1250 30531939 30531953
    0x2031009060b070b15010801090b040f020d06030b09061312030f0e0a0c12020306040f11121b01050301080d180f06030614090403050f09030c0916030c03110708180a03 73
    0x3c00c9001384456816a1599001c1090521000755030380d00080a842c014000c10089400c411022074014100160710450140451b00301e810a40140030007907169541042403182c01707904603810001410146ca164103203059108400c00405500910302e20b0800229100700d0301961103881c140c05030242c00c0c880f121300d807034540303803506529282140c0d103181e421408988080d00309201301c141030303001d0024405611641c441f03810300d280740c100c102c410075104615824192074000032140c00c8a2004001c0c0035283c204108140b85a160040c4181004000e00041200620002c4c000b0b2881c5011b0406100e9503a000d00f108661080c16040504a1058035000203036141d0b25600c000102c0e4001410500d8100c202d2003002074080b416140900007403030900c000d600101e035000040c26006030060440e01c82c0d0790518046902283c0c101c4509000d005803100205030207805004080c81641701e85001c10140c25503480307502050044d40d0029265845c045400009802d4241c062403e8032401011031381072560301d282ca18 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 30534439 1250 30533189 30533197
    0x91503160b0a020d020706020a060902030a06020c060103200108070e01020c03160905090f03030106080a0e060106080415050103020102060c07020103020c030c0f120a080a0f0902090106080601030b09130602031009060b 95
    0x14464a4044c41c4164400f01c1e0030802d403141540601340d8140c035501c0355000323003508030700c240d03410300400c01101d00064042c40100031035003901000e01a298035500746020001100d588401041054403401e4003960f90092410f07034001442c1c01c118120161080040380380400d000441500362061039005117802140701103210480e07403c0302c4144103943e00c11604580707131402921070521325070051006001030b030700440c80316a00c0080d1900c00105a040f0f4000b00d0b15248007039000102040000b0144030500401000c0030303000c10802030041c412545503a0000b542c40200520007049000c000c501441103a1294049512140d5010704a940f28070118136100e40311000055810214458841840090300408040c0d0b00720307032010341356064150b44a049000c0680041c0724400251965000400010b030b4403100741d640603083c95074600c03032145084000503084500303003070450348102807580401a0000c5500351801e10580d2080002da100c2c0c41c1d41d00760318400f02ca9508400030503400c0590100e240c0d02444007074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 30535689 1250 30534439 30534457
    0x3030b040b01052802030c01020a030c030605010c0c2106020c161a0906070c0302031006060305060d05070b0906190503040312050106020c040b13060902090307050102010b091503160b 80
    0x100001040075005440742d11500191806600500b80d00f9161503a422240000f00c19490050320724001c44180c0183c2241c1c0aa605100407a9468200c00d801c10760612920018201c00e00342406803404079210030b0400c5503e48100c2d1440c0c1d07240c1041c68010300515004078003859004000755142c0312104d0803e41c455030300b400714035000308040e03030001030b1100081c84000504190344031042c40c20a1600c2807000640c0075460a031100c0c8200c840001c01a2400c02c14046910880c400000e070325810070000801742c40c005407100740300f9000000c400002c2680400d00c0d2040703d0806968650b251a440040b817400c0c0035401800c05000c1e02c0c5180000b54a401000a601c220702c20703aa42c440e49240c6440711b00444000303018110059104c54080110ad00346a400320200e2540142002c1d800b82c803030400101541c1881c0c01481d101ea80101d002070060804200300317400340c50300b4002446030310100004240003850040c5000c0d120405414045a240c41c188818151090400b0403086500e80752291038a49611070411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 30536939 1250 30535689 30535691
    0x130308090f0d120e03030702270a020a1b0c0b0a020a03030509010203240a0801020a02070f090b090408070606030605042001030501080706050a020106080303090a0203100203060a030b07170403030b04 87
    0x3900c621480d124644201407076003e48100b84410a03803070203c0307080c3c3d80c0b5200181c01d803100300600400b60755032281458140c074030b040e20318180000e041068112444040c0c60710f014103006200d000c41e803980200c9422000b00d4001181e02400c0c6250a040100e401240d0101d0303511003000402080c09a40072848200c80e81c0179850920240d00c410100c9030803440112a804d000c4d014a1442e10100345100368240ca2480004060110f00d075299010b060172a408820080c015902c1400104161591007921000030700a00c18100600103582021031180130008100406450000415000300030700c1d980102c1c044d5421040801a074a0145480740441d01110f1b05800605060a5106200e61090142606880c51381001d400528540b50b401d840c9138002016031010f6548454010405003000c001451050010070b00400c070220040c0103046c00c003a180c201c02026180100104007264480011110441e0f9014044146503a07980f00f00b107402c1c0420002d9141402c040c4030501050580c180c00040034100c4c2118 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 30538189 1250 30536939 30536959
    0x20616210e060708011406030c0a020f0706020c0f0301090b06010c080c01020c0304050405010b0a0c020112060504090b06010305010b0a020304050d031205070c0b010503010606080402040b0a0503030409061d06010509041113030809 100
    0x104000040186c40c50350340e001800f04000f0303c003d803810018141802d8940101c8240024090025080440c41d8120030010382c0702d546120481d1410b10280c1c1c44041d010740c001c10500300d03e17031111450200001d024078180a0505081010020320508503014585443c0086440341c3c031800c1640d4030381d84203114144c440c606040000c240c54080c10201c500d40c02c01500d55128044040c1d0056a01016034030003450282d82d03030f0f08005400d45690140307410051051101514511304900050200c03541a00003000e8100d05000f443c1c0d03115000401c40b01511002ca40c900c2c1d040d0a2880c007101d404034a95202c0c01c0c00350414040c011080c0d088075a01c0940b500c540b1010b01940c0e02c0d00140340c00c85001d44140c0000540d00000300d800360604c3d42c0055240b44020700320300003594880c00842d2855100e6440301c0800b82e548c00302040300d03d0304c170f4591180074955890007104034140180002c1281c01542d111a00c556902c0001e4010300400408960708800b014005503010366803800d20360850781004400358001e4903001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 30539439 1250 30538189 30538199
    0x2a0e0105011106060d02010504050301111c0506010f0c060f0c020a060c0f0f030b0d08070302030703030506040c171005040609020a0201050105061201031209050310020703020d020616210e06070801 86
    0x240490b10381070800b000344115900c132401c102e100900c8000030b9040c400208404500c070744085c00340400c140801c00e80650383c0c40302081440d412081d1100000c04003841d040c280700d901d0303a22119108403242d062a21a0142d80b050608500400f00d0b00f548070705803840c0280d4205042d80114000d028103000d00b00c01c001e013800d0103c06072011101c002040700000c0c2c0081c4412203250085d48010003141d4041c1c01d803441102301ea51100031303585c0006020303009a44046124020036505014256000d902038500340101c0700310a60140c50b4405040181c847c0389452400201440380c011003100060100610500907241d440400e1002548074440c004010350a00c0e00114041c20710804607440c0000340c003440b500d9a840c40e25514070541c0c1b070400c55801c201c42e01000044661b001c02007181000011800142e60307800300d00c1d02925100c14031650a00f5508644100f0140e402c0d20000c841c207214160409004122800c4008000c004d941c4841d8001a481c0c685d08483d0303910000369841c030520071512510b0580e6214 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 30540689 1250 30539439 30539447
    0x7081e22030311150606160c06080103021207030515040302010f05010b040f060e03030703050c0304030b0a060905061f1101060305060a020409050c03160f0e0603130b0714030109092a0e010501 84
    0x204c105a00108000428114140000103004104044003680d0000041d60f03a10380c241213a81d480100050785890050040d45080c5140d4007414400d0001040d40350315607640d50b61180382400032604402c01040c00a01414000e4011081022101d00308220035030319801403038250740007130040241c0411460404a500380c000c1c000c44c01c0c1e0340710080086081c11341c1550126041d80c400c0354094501e000600c40040000c9140328a035000d000c4281002c548241452100d200700c2d4002000144161030201c103c030000b00d40ea601544081445150030440f14000814003805041c0c5a807008240c0d10809042101d06810340c0e0141040c1da0f6419018000c94444604051150000703072070607001d5000303500000c2984c6000703200c00c2040000d9810186640704601d0005492078208850b020a22581c4c1c43c0150304010105001580c4041c0c40d060120030f0011702c2400c02c116000c14041d0043d1555603480c090240400600510100307844c201d50008528840340716204020a0352007034410360243e0000100701036000f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 30541939 1250 30540689 30540703
    0x616030207170f071703040302010c03020906071515140901050d050d050d180503130609060c06020906120412020601080604020108071b0501020412020f040207081e22030311 76
    0x48084209030ba01860344801c10740d0312955048082000421808001420208030550b4018054116980780d00c0c0504000e800d4031207080c4110304040c81081004016620b007810b450786c95804c4801e88006612400c1540001c10201810f508005220240083c01590701400c010305a217055070383c2c26880c0d076200288120840c0d022401403003504402001509a4403c8000e0a4076000c070001c0801c0090110304900c80f00d0200c1242034440307030030000302c109c9007451444000000b025585000000c0904d8210020802d80500b000140381c5500020200d00c90703501e0b9002c3d1101312400000300d030101e0805240c03d01c1d031192541c1d02e07440980503801c00080ca020001c40d0052003103406850700c1d0300b10350b540d44045880c408802e01000c0e41c0d0f000d0342c460307030041442403005d032002d03003040001c0745460000303401005605a8800580b900c2240100041b01c0007030000d0042d03c40d583d1707a0001c400b079064603040340080303140114014050320742c00b00d110b0040703c4981441110200c0380681c80d0302802d801802c1c559501c44003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 30543189 1250 30541939 30541943
    0x140f040c05030c03070219120305070e01020606010309031e090807060206010305100c180e1f05130c02031c0204140405130b18010912020c030703030c020d0804050409050616030207 79
    0x1d0140000341c16001242d00031a8004007510680701c01140c00300c904513881c03015040503180c1740542ca8442484035058803800da0000d08900342152441d203c000000c1d6101c00042c405410540c0703881c182410980034002485800c0024116040070070040d047c0108a200d103449402d41da48104480000c01d10700100f0442d050301e400c50090591a8030649005014004e03001150082015901250202820070416107000e05850a406d02c520b041c41021904440c0920701848101e60000c0390410071565039124030030301c0b20900040800c0d921100c1d44141d0450081150000040304100550145508180e00810680c1d000b020b40c030045012500c1400101c48040382c003081c2840e5441101404242420a019031041811005c02043c0c00c50076002800e49030014070880c2d101207094100d00145e034051000d22040c02080d4002c203c41441d60b180141103d1152902a0090345202c0300720b03081c0642c46c81154003410018105119220a52420301d5891504603019441200020060314004d8424002c030b543d829 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 30544439 1250 30543189 30543197
    0x1804080708030402060f0c101b05030a05090106150f0f080103030e0d02060903013209030a0f0201090c060c05061506040306050901020c0a030c0c1d13020102070e01140f040c 76
    0x1105907a074000041c0e001034002c0e640110107219004801e203500c1c00800600e40010701030b001d8041200b0310304040d1007140c070421107007000da440b90000e041c1c0d00400780d0b035015015003004140b507190542c41600400498000700c400f45042c0030000181c41d00300071400c0300f01d50180e990720800d580c03240044a03034030300a001c0100040c440c0c0c2000c079900d1410f908003452850000300f080d46410a2080002d08441400000c501c98825500304299680001502c250400b1015a1100d02d540360145c2d806449104540c203e4003445010005188410f00c00d60044d1881a8000c1c0100c0c1c0440e01d45401078108880c3c000d0480b69403151000255842c60a1502801c012402030603603410181955103c10240c20002c1410310250b5013440300d20440f4900300701d20342c0024000d444401c03c0d6109801d041d18520415000000707804240b00f030200804000c01404c03a4484821100c08104080a00c0102c1c2009601c0c0c0c800e01a1084130000807076481c0d102075400000c0700301184e81901c8014050300340810785030a044000013113 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 30545689 1250 30544439 30544447
    0x3070801030305360916020d0507110d080c0607030c0905010f0311040b03070f08190e0a020d050c03010b0409050303060409020d06050a0b15190f03110408060402180408 74
    0x207004902409407000b070003804412134424407100e140310403003c407050000030050900c00070071030420f0100a50080c5034901a101607255010010355a002c8a601d0f020070000e000407003000b0b20142004540140301c00604000c000049410030320b1094000c0c070280a01030292401103406203010380700300c040170605a225860b09070301d0040152090803030b07a542d00041c035446400816003000e45500030b002910b495110b240d01e90421000007080328140038801d106202100040c8039031003410410541e04904031000101d0701e10b040c1c01c800c0d070612410145c000d40040180143c1c07410082c000c0fa02c24440078069000b000004400c000300300a5549180007d840d94004202040304c1c1d08140c0c110359580760014000d0006000c5555070344040711000c90382a20466985c91900f2254501000c044601d1145000214104079064411030004401c0b01030314001e2000c41328000200c1c41c0a40c0180b5045038202203802e0300ea81d500c24219032116411075049200e43c1d43e60341500660100e180d1024056030b0445005410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 30546939 1250 30545689 30545693
    0x412170415020d0204030c08070e071b06020702030a03020708010b060901120e0a080d02090f0909100902031606030603020906060705070b07110909030706050a0b010e040209060702100503090706050307080103 91
    0x20300080070582180c0d035400700308007040041907000400c01140300d010300030a190b14221140d401e15a050300044440c841003014090a15032280d4034190b003d07015440d640490b031052901000911840074003d404d40030700b400c40e1051540108145d021901890001d00c4481009402c000c244e2081031012030200360100820780c01d41d40b00d070344100500700e000b500710b541c8039150b0b8a4410f9180c001c11881100c1980000320803410f824404040e00040707505070354080050804641c020340b29607048281d40810b41da10050541595410040c0114100d11041c00030000c03622228000c0142c6104d0000381d0041d0a950007240840c10804102d4100c41c0d04080a0001103003403040d1540258404401503500d09800b20f162112a030710b0880e50b070700522043c0015a61018549460001d4030002400d800b48c1c546454528100346e604690408041c40c021100182c0c0d0307110500c000382d00c40c001e00b00069004202c00d1040b0010070b802600460048111b4021240c00700d54421003128140700c101c5580001408903001000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 30548189 1250 30546939 30546953
    0x7061d070f1a030405010b09180c030d0903020d020a0302090c0403020319021008070908010519050907050609040207020d05100507110c10050706021c06090b010302030f0621060a0504121704 83
    0xc4c1091148001082690b101d00006201080646901d1800f8244145400459204010529035041d003600582006280148007804544481c0300103401140000f42e54001c650340c2c000034038060341e802400202d15040030310520225801c2404224040e00c6100d07181950000d25240141d1510350050003820714a030000003c4840c0b00001d4200020300030300301c5000c11101428003e0710701c1400070385078410301c038150030408006030b6001401100e51508007590a0045443d000e0446211480544015944114501c0030401d1104110000b42860180c034000800340c400740c0c2c0001d4010106595103000341001030070b4032915204403407039540d031040100e04140c6480740500090915540149001030400a11442d4007031046810304605038661b583e480f0602c0101018407070001b035288203107421401c600e810034071415200c8001c1d00c032620035010842c8001800700d4101c09410001802001d40701a818801c041c08040c10082d10121440f501e5200d140c0da2152007890014a4800c00706800500d54443d510717030503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 30549439 1250 30548189 30548191
    0xf21031308071203020a0e09040b0106051803070803040602060c040b0304030e0609130b1201021c0f0207050f0304050916080406051f0b040509070504080706030f0207061d070f1a03 79
    0x111080428404080030940d43c0c805000b9820080e02e0150751081c4681000700400c03418480b4034800c01c4a04280000b1a60702c0c059103040d81c0c15414065580c82c07424010700c4010f032000100d142c0c0361041c42c002281c0f0341c5000c0050b008942d941c2c3c00301c401c0c1d505d03410014030b03980c0224050404405014400070340400d2181e13000318030055018207058a82895400461800304404c3d0400100e40c0e00e80d5104481c6d82080040c90680c000341100860602000c03a20381c03818002a90b40d08036030a81c454070b4681c04504a5811544810307440400c8984070324400d4102510398205120f000d10648500740054148000303c0540c0c0c08064160f6240c982a0390390b07989000c02842d0140c0f01c1c0c031462410162241c075808451014078080c00c8419605030300c3e149041c08008500d4002000301c01008403d00041004203000550308054031443c0c140441d080d4641320380706009008007a00503007003e00303120200c80030304c1141140c071280c40115025115440d84940096044451034441d1401840d401c2404180d000c203048095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 30550689 1250 30549439 30549443
    0x70c0f0809181501030510030b0603030d060312080c041802031b0a030608060901021602060703110106060e040c02010b030709090c0504091b12030801030f05010e0f0f210313 76
    0x2850501a10030003084800a000140420756000402440710b43c0c4032215004040d200c0920341400503142400e600070070103201d072000402254584000c559030355001d006407200480d03602001c110307440c0c0e40d0502000700d041c05628400400d806201007940c0030300140894003a9860012209000e002c0c80c035442000354801003400941d003003081c800092034010500201000740b40781d680821018142000d040c280350001d00542042e80c410003109042520f1030715400e100c69011a5520f441c0c541c031b420140c400e020340c406611000d502e0f114002c160980c10105503c40f4160aa41c1040a1100d0110907400c0340c00c0d8600d201e42c541d20104042041000f290807292285105400c03454649a440700801e00f9150081c0080711044004404119801140400c2c81c2c002c04115011050410083e00c01501200042c0405000b2281c031940d0241408400d4211811a0b8803d42c100d4050413002160951100c24210728840c07035008000700c60000110f000007070061141d004a0042c070b1900c1c0c031001c1810800511500f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 30551939 1250 30550689 30550703
    0x20426061b190801150507050c010f020f07030303090b0a0507121d0303010b0403111e0108040c05180a060603020406020c042d020409060608090a020d14030f071a070c0f 74
    0x702d0a5001070b02e070b07524000c00b262030300c4458040d410b10403016106402c54a2001c00c20030240103c5001c00c40000746116104020300300000d5021000d42c089003004421100c582c1c0070306c03403010004101941544280240da016010300c0c2256214a0401802c0c2d41c4140d4038a000030f0003510109042c400564007800551041c4c5c001c08205c180782a90341b6085030001da00400710300c7d102040802c28848a401e449008031400c8072014030140b040485c2c00465240901414108040b00e8005010809205044000ba2000800c4a0101142060f40400c01d43d401c89021203075500b0f1000010b02140280207490a5030340346c4d0003806c0c0203881d89040c0720040c880c940100758001c441e9000e401d254528400803800b1941d06100142e5540e00b020003110030340751b41e6400342c030821400301c0030045000b002240460110340e0441c5d48040b0744083d401d1080d41c60300402d076060b003075010000b00f800e21791038040f00034412544150071102e10034848010040c941c0000300c1303401010581d545180700015400c06088501c0e2842000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 30553189 1250 30551939 30551947
    0x815010e12070b03060901050a0e0109050a0603081c110c0705121e0706180303050f0705070302100e0909010b060702010f03020f030a0204050f03011e0e01180303020426061b 76
    0x4190714140c42c5512208810030000103002c01d41c00e00140080c0035100540c0d04012803440d02c80c0c01104640c0c1403080004965958012502d050060b0300100020f5030040d000d50b850340721078001c04a19485c151101c0e24110320304441c8900d0840c2101c180e8600c044120041c2c5042c40c41c0006112041405168600e00b038012400721908030070b0701c9020304941c5a040002481c00750300704800070386403e01000448585906442080000aa2000031901d24900005040d502c1d0326140c03800780c0c03501409800082d42701e203004030000b4086078840da01c1c0552a8040720911859240d17030814a00700c600c0c42800c0b41c2c10a00402000016500401100c0262030051900600d042a090040c2529810680b98490ba29400080030484d9181c010700c01808034104034000c1001440c10312030801241120f2070000e401544840c0c03001230258080d031110225848a080d0b1031020000361500400075807160045503562000d000142c407580d903a07002103614182c1600c00524040e103410030b00441c80005a20081a039200c100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 30554439 1250 30553189 30553219
    0x60105061c0507090317040b0d09050a050d030506010905120604030c05070e010b090a0e1003060c05040e1305010e0316020103021806070f03020f010b0a050907030b120c030c010815010e 81
    0x44281e0303100f20041d03a1240e1810341945006004003200c0454100082400e01050088007e410100c03174003010702d130b04000b40341051481d01c9801c154440f4005407145c09003a010004013905a003140c0e110f00c100340d076070728180c40d107403000c00c0150407800d40144200c2d800312001600280c083e8070200911401101102c0e4400e641d00441a00c21000741c2005802c2c4401048084543c18003a129001414404115a81910380348120031381143e41480042d008940b02c4c1c040702055030040c8122000352452545880182c07030001c1300c3d9400268040000c030340340e61030803005503030003070010041d00c034046220b1242441040071600114042d400c51620030b040ea02010280081030340d00c2200410043d8868030701e02192001c00d0401a0810080301580500c2e40d0408404018a0b0780b148074010582d281110740c4003080e21086021402000309008a82c6c111410b9009451010390000e000b64501000324103c5a810a150b40115458038003070700e02c0c500d41801072144c4075842d030149445440454015100310a80c112903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 30555689 1250 30554439 30554441
    0x9180507030207021e100305070c110604080f01021306090e04260c010e010b0102010606120f0605030105070203070501060906050604052e090911090d0b070903080f040608130203060105061c 83
    0x24805d00b1105028007261441a82040500030701c5540e520304041000345091000035007804104040202028043c0f912101035230b070350f8000c0e280540344003011184611a11410913000b0352111404565981c207607100003600a210703035010740035124120644a040d0b1a0340c2d4408440004480340c4c5107001415020310391008214501805144145800209103502c01816641c2100da440301c845045904209081c00b1140e08003039904554000b151000500c2840d030440c2800821075504000d9041d420001031102a540c000082c2160a006a0003040403070758910078042114101c1c170846400c11402e1004001c18944480010200c3d540b045050119809560003e0010101030074240089092401d043c0204602d17407180100741410884050b1800550324006001c0c030071041030040a0f40045c2000985c81403240c11440011356110303d00d242c884003004c42c044002d404ca4000c600001d41480000b0b0138054209480602403500600980000d03400c2c0801d1101503400b2650320032150401080c0744070427440d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 30556939 1250 30555689 30555709
    0x3070e010503220309090b030601030b0622050705120901050f010b0703020c0d0b01090f02030c030f04021219062f03090106031a34081e04030810060918050703020702 73
    0x482e68500004134181b146600c1254040e401c194001d0388580c006000080d80160b50300e80000301152002562300950840601010500e078002c200300b8240000d0002f40307a001005422841e0402c110030310340e5510018480e088070021507420000b5800400104450001c134170007007090350701030701c191b13243c403034011010965407240c034203003154503100200040180c40c48038410b04062a64000c401d502d10300b48042680002e0201500c5880c45050301c0c4003040c1150341754603010101c803140e80b05907414500f141940a507079600c5c9003000c1d190b007420640038030142e00007034100030406445503202d5036143c0e16016480c015504005d03c1c1c00c03510340d43c0d0311012000c550345082080c8280e0500046040900e003150220f6100d031480e8610030410b05401d0784480b09001c0b29061003080640c98038025883e40e5132822881401201c0c03e00d44841254203000b480289580000c02d9445505070b0880c42588580c0c580080b5128042e5100f80d10104050300340207660716006411040d00b04546245c058140030040e000130313840d221 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 30558189 1250 30556939 30556943
    0x1050f01050f060403320601080d0801090c0503070f031806060f0e130803090a061d0706090513050a0605120f0c06030c040612090b0a06050901090203070e01050322 72
    0x44148010801ca18211a054500c06015542c0c2402d0a00c0c0d030751003d0001c060503019410b5080740c41c0654101c15204da10415604c0a0601141e03400c0d40e41380c0a0303603100c422122901000814440c000b00c0ca204940c0221150065980c0e19030389143d446040c01c9600b560711290b40b03410540c4466000c00c940c4074095043d401d903405094009030261030003645a82401e299800424400750303480c01c018210200020803401240c1268015680e075481d02d21140c205903c1a00003400e05241801404a00b900395100c2a00032286904171b07401e490f10b446041e506c00340d203449030641c03080c03c0e04503102c6d00703802e160041d9402544001d40426020384490004a5081c40b0021040c001d902c4001e410f00344150400488050314410b8540e030780ba500303225010140d10f2145024810074030450782c05c0303003015040540c03000c0c07030081c0c00070703842181e60401e03034000d00103480b49115151080b1641070000c60800001d108803030081c1c0fa00e440d58003140c4009001074915400051905d82900324a48a91000b40142103100302c0c054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 30559439 1250 30558189 30558211
    0x307031209081c080606070809040f0207200306160311030c1c0501060203070809131a150f04120201120f02040f08010c02060c030a0608030f09100f020a08030c0c0105 73
    0x50800300b0362403408071105030400f01201403c0100d41165002503205801680a45076959074240d40d0800c504079100c0d1011407a04145080c428902208103540a071007010f2060b440c06801110038500d466400003400c110075459013011012485000c40a41d011004014500340440c01c100b00d0030036204240c10840b803441e10303d48001286130001d031202a201e41c100c00b100b4070130803087d410110b00070f40d0303400380c11801003590300002003d9009648008050309034902000080c815007034007241d00b40c0d5a80386401c45900903126404510b10861554066610401c09024824101441c040d0001144001d001050b810306c10b42048401035003200f4061300c500380e143e0082c0540e4607454040500c0c80140d41c0d07440782343d00d81d1400c1c0f07200042c0780c1e002c28210341000c0e50103d00c0f6200c2d210000c1d8400184445c0d8046e1903107200008d19100182500c1010f07001c808811103507126543c20312402541d09031900040000142c01c50095240018003840c0038540000041c41500d0038040850b1a45086950503030f0b06038096 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 30560689 1250 30559439 30559457
    0x120513020406140111070b040b0307030e030a020d02010b0109050d0b0402011106130308060a120308070e0a0306060e06040608070b030702100c0e031c020c01080c070605010303170603010612080903070312 89
    0xd51704a49a0344100652030002c01030340c1d103014003244e441e004600034030507000000070108440c148a9041121902407036010350395510240c40300650345640e1108404050b5092100440d09980100429021114041e142c1805621155690f0a526000900403414001129030700c000001041001501c5030800f900d807a07509190701d050240c00c24a0041c0898450b1501e10402d0101b103159001d0242c49036458201a1020f0715918020341c2d80600e80c3c0e80c000d41010003c0390020501c442a00041c0842c0c44006c5140c117181c40e010203110a07640c45004584035035011440801c45080d1100003164098617500c1698060290303080c0030400d50395071340c00c0b881c000785031407210141720b00d414440316100b044500c08030100029001c42c0a0345840110643d40e041c0450440041c0c41c50213201c0884420a900280c100b203a90303103920300035002e0000221641598000e04000031001c2c00c05105003001d031307204070400a0005019603603003444ea51040b4030007074060142c401d0000004040e542085c0d90303180507494035511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 30561939 1250 30560689 30560729
    0x3091406130b06030615010c02040603080c07090f09031b030201060b0409050403030e010903120e030909040614090106030206040b0f070506040303061a090d030c02061c0c03180201120513020406 85
    0x1490302c0502014403e410240920400b40f001b4030034480410070a0910480c03054081c00044c0003400c1c80e50000e03002e00800101004500800300d44031007505c855100812624204160300c0040b1641000000d012540103801803400c0500d801c401e0b4183c82c070a100100d5403984514050901d070b0003a90010004a8030707030741400200b40c1c260040100395071455008205045e00343d00c00500c3c84d0b001408040d441591040b85d58000c45060044620301c101c081e241110504252504000408185406840100700c6401107091564103010b010110390b0018a0b031070400f030400e071010f00340d58019424004544410003010b80000c006011840c4101d0280e00c0000703c0354030300b800300108000034034208181d42c40100039903041ca03603130028443d0402d40c0603d8990002c49091012842c00c0c490785564000800d4004c1207640d00e44265002008240c41c1c5a03014040121100d000410f08480110024007090a2040c0e10019880d40d6001c154000e60400e020158400c1c1500850111521a00a8102984103c40e2034207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 30563189 1250 30561939 30561953
    0x20702040c0509090c03060a030803100f05090403020a030e010306150206010311010309020a0b03040201110a060506010f0306140108040201030b04061409010b03070903060c0909060e0a06080705100309140613 91
    0x4200a9402e11900d0b01620f240003d12101c001800480c03010400700100311f86403207500c2980040c41e40240f40903a030307082400310358001080600c100c100308501ca2078007240c0c504010309802d004a0381500102105012964190354580400d56090f04140e610316000070900c24030000c4500004554000d08910750550818000a402c901c11840c1414180071000b00140c80d140c480e0002c440d014402c1688a46a91004840c0500d03010140841d034070510059074207001042d406540110000d0b20340b02142443c010f000d50503502c0610800b15004003044542900c0e5011340842c6610178414900010f200303818000080484185800082c5105e801050f80801410b0541401d4094000038002c54210300d070501004002c1c82050000401d0b0070340711550290818090403a02c0d0280c28840410701001da01e507083c40503214030856028079034600380100000d8142d0b000c0307010010381d54090f29020100d024070500742e0203003041c036008881c0741c0380d00001109242070074403e0364003c07141d010244103405c0443c14401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 30564439 1250 30563189 30563201
    0x80106020105090a02010302030604020f040f090e12160213020a050d05010b16030c060e0a080309010b330408010c0237030c0f050604080a0f020a0f0602220303020102070204 76
    0x806680c940420722010f5200065005446542407801582d20f81e41c2c4400b00d00070b0300940740b881e0401c2d0404a004520008008112019603200c603004003c80108420a0340c0d0703610b50303c2102419080e04100c020322586103400d035200c455001414003088100c40781044401ca07801b5240c0c40c000030390003142142c4a81c000307001d030f9801071150500403400d00d41d0801010303204140044008003441074405850341005001d80011071b410103440182d40c0c6421507401d00440715030045445204d10751030301c42440050300d051340341200341040c3c0b00500b00100c189541030283e610001310592170700d140240f100003100142402051079212956018014166031600104606424001d007140358100442c031f1230301401c030000b170050695074061a00d050f00000320704200c06407140720350300502940900c200f044140303c0200010004074400d5a41c1d00240d1440d00c0b4220713110030901000514440c1520400000300b440c54000c0c2030283d0303582c441490421504450000406111f600480141c3d401007003220640c9401d206e60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 30565689 1250 30564439 30564449
    0x60603160506040b03070c080c0a02010801052d030a0f110906030a170f0d0e070303080603011503061d1915020424050f0f04050a0504060e191512030801 67
    0x110100c80d00702400a1801d00541c080c02a8015010000a407010b1003410250480c9400c440c81d0707039031001c22000103a04c8000c410f01c1a4007040f03030200002110b042c0400000350f002c18603500040d04030551007440c00c094055410107540b41c46040704d076a0120700064004004184503203010071448919000b40280c194000740528440d40100e80030102260010010b41c05d05001429101d65411004105103100d0245c1014414450300c2c1040080c10004006404d1040c0c9010303881d500107a95401c4105070a031603c002c0c0741465800c01000410000b585e0f0303084007107000c0051044a5800c640a1030403454281444001e200b802c80c80080070301401443d0168004000100c0000e61410741040003110950030910524400000e0405144201c148141b003503070f44138921040c8130303940e9290100002d0310580007801100d1040c5038002d40040d003031a291064404490711140350001a070b60314850101c01031580103206d003c4903212010102d08a0400604902401e80803291a01101d00d9050040c8980016002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 30566939 1250 30565689 30565723
    0x306130201020709050603100204030506150f0d08030c0d0207080301060f020601030b0402130e0102030a09050106090c0c0305030c090904062309070b0c0c0303070302030702011403040812040305070f05060603 91
    0x480000360b42d02090980990300e1416003c40c0940715140820f2600ca00600c07131422442c404140481004008580d19014220640c1d0942c51140307100d04000b20030180c03048480e071203204200e0f00000110488040c544c099010f008141c1080c06480096042c4da000c110204c500303180000040c044c1a8000340c80402c103420500c02060f840d81144d54070403098002070000703441844280d0790070f00c070003130150001c0704801940c1e0001e5490b8180018030380050708401c1d600f01c82d90b5080c200081a00d40091003060003010307a65845800c0c00049480075205648094201007002504000c806401d450310f440450040b4402c5d4070028140c50b03001c9802c956000510301100b81d0b01c6078081406040103000411200b40c6515401083d62280400540e610b0803400c0c1c440d480c0c040c040850064240340e004409045168001e81b6100e60002e144030703003544248011240201056802d01a00210031400108141d00a10900b071851810026071150745030b45148240c1150f0030b40c03081c0100301540c141800041d00e07030030009903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 30568189 1250 30566939 30566971
    0x11090901090e0a030e0d020d03020705010906020303090606060703120203070903151509020306190e07080f07080a0c03090b0a1d0c06030a05061908010905010b090c0d0504020a170703020306 83
    0x20502c1d880e034852120140420414074400907096445203508450306900034010101d20304c0c2450043e440310b03100c0c401d86012403403000c4002440c0d40080304603840b030108840540102e0351520100080c41e08a241d040c3c080058064000d40655501e10086001b06a0350315a071343c0e0740d031841c50720003400e407054000301d0100c9003003c0b0080c0910141203a08010361f40040009038803503540b1000b040c040c0146070781445002805003000100b1075042c1c104140202e840f541d80e490b407566120240f40c5220801e458400c00900410001400a00c590380138000002041c0f802261850640d03d910006031001e4400f4602c0a80d0f40c0d4682d140f5a030b0151910701c1403a61f01c006085640c074034400041385400020072040300c007512070340013580b1a510b00703ca600c941d419003040412190344030b020187c004d1405140480315503203804a60ba103c0d2400780142e5202d40010045545444815000c000c00b404020f00201c0c0c00510007800441d070112020b10f03203001c800c00315008145162540c0101840c0a0028056494000d8010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 30569439 1250 30568189 30568211
    0xa050a0204050f0907120603030809010b09070f050d020f0a08060f0f100c0c09050408120109050f040609060f0501081018030c140f10020903010b010207181a03011109090109 76
    0x100010000f0001100c8460f0250350340d860589600e03001e403000b84121490f06034007100305500b101a8901800381070b80208414080c0d4000c0c044000700036503840001c502c00c0304a070450076101e04020b0000c2a803140e005401d00d031120b500c410817034101d98076810100701c8e03a2013001042d0400e00c3c07282942580031038a18045c680201e0229000b400b1440c09903081000b6007000d44240f146100078400103129183c0b04001a103001c1c00d01181d690440f0110340d05c00c0d07104000000c0c1c03002040c002d2a0003a0b8000001c081c0d2621a541e82c40014001d480084800d20b49a1012641c03045030351003854001c046080180c2090380c00034001608868000d00030700d40300e03100784001c580031a5002d10302a007071070751101141035242c107000c04c91403030015400d0400b00580b1901c0408841c810740c50300a06190a81a002400610800401a40c0321041c42c0501c09140e10740401c00f500080c95500a00050303914005e4254040b0720103000b1034203644800e5080c5004220000b100c2070542040006c2a0040012070000c01c000203a503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 30570689 1250 30569439 30569449
    0x3090b0604090c030507060201051b12061c0b01030b06152802030f04030f0b062d01030e030304060614100c02060f1611031002070309051c050307050102030a050a020405 74
    0x501000d010310740c0d0b10891410091480c2904000d540c1000442d400300c0c0e40d85c00d0082c0601011540c0e04040c2066a011602901c4d0a905481c01001400300c03007442070742c0d1a03040c030040500b405a040b41d00c1c54040e2003030001c40e00ca5010f00d0301a50080c0000c0d080b40c5020014000003090b0011650550342040040542501c011200e4031102c4109510501c45007070007002c12032950281c41e10380c82814500103000420045a9803840c60304030b1140c02c0c81002d6503109030800425107407180300114a8044080d60400d004e041c203500001140050400064044171040070526641048a00320b620682d5042d0034003541c3c08110300b000c1c0040045401c00c1d070284049500606154415800030300a11021400b64041000300c2c00713841d01600d070003000c1e800400d2a41003240d1901005401d142c003a01904403116200a824000c03103d500da01500c8140b4420f103400244142c200b6070350227481000000000000024400740002e001040c000c400140c1c8130b09040312103000302c400142c1901d00303962040000b00529120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 30571939 1250 30570689 30570691
    0x1050c0604080a030207080307020109050d05040b0d0b031e0f060a0509070611030f070602070c0b03071d06041d0406060803090108070509040b130e010b0402031005130e0a1208060103090b 82
    0x22202c411511141c400c2001c0e070281c081c01000134000310002c0100710001d40e0550007030320214090300488210004461058271544924000c1c000031500c100700500509802c4d42085101c4240075007183c0b44100d0a005181d40043c205080301860b800110503500012010000340c0c0d00704031003400030406810301980341c5641c0c070300301d104017400d01c4210700c01500385200500a54840b880c015905581d19105481d04500a44c02508101d403401c40c1b0103004624030f50f0b14800c1d00c0c481c04d156180d14104012450382900f040306d480c0210b03076004108000c0400e03002c3c070385800019503150f43c01641748030f821301d45000170942c5e8498202034a19807040c0200041c80e03910400458104a45080c801d40d2140c413040850080c04003060007030303044540d1700b1449140740c400b036001c0782a4031610002008180035038070411040c0c0c481034400b0210112015001d001619054441c890300d41e400003070024800b118945542e00300814048150717005440580144082c1d50403030300c5182d004030241780802400c41140d94403288080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 30573189 1250 30571939 30571943
    0xa0209010e01180306090311060f0c03010909060207020a0308040f08030309060601030509010b100216080102031626041112010504020a1e05040501090c110f10180b0702070503010b01050c0604 84
    0x225100342a43c18280d103801072000d150040020300c03a44070031b400c014000341404940300000c1e08c034100c0005d000d4069031040d640202d04001800b440c591030100c0e401c000c1e224000040c0c0c0c2c0b0942c20030200005948410100b402580300780080c1da15180340032100e1240302d109500c40c00d85a0010000c100340c651300410540d5005800f400e00140342c0d103843d12258010078080f80800c1d00410b00c54074901646400280d50009021048030b82c0e1112511207a03d9402e07400191070744510941a190340194640c02071038411100c1e604844a9911044c17007400042150801350340030348460802030a414444e040526400c10640703405002070045041c550301044050a00d886140d10320064090014a13284004803050001c0030014814001d950315180b8140082401d507080201280500040d20080760000c5030030aa1a030f08030014041d12210001c2002c094840b200c03019244002000c000740018840c0e590b601c2c000c0c1d50300d60050550b581070100340742c02c491180c00700d14103000c8240b0046100101c006040350340300da = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 30574439 1250 30573189 30573197
    0x60807140103151203081609080a060504030e03060106050703140a08060f040b040903030203010e09150106031503061107120806100509030a0b011205060a0606050409020a180602010b090a0209010e01 87
    0x100180050f24804a8642200788030f10565201e403814198010111400340003c00c00a043c9013050341802d0b03400002c03070b100d0580c0c00e401902c500e1010031b9103940010f81c0b05010f4202500d10f81c3c9904002400c01d182600101d01041e40802d80c0350905500c0043d04001c48000d0f4042c40c0342c000920006420781c0e60080103180b0070a0004d407451240e03221600000c0e24030501620900404c1014940034019410034010380020106010026400b003100140301c0100140244020400e6420003508401408030700c2004030304d41c0c4032500000002800c521609510201817458a0f4459010746811040c0380c16540f2103c1c100704180c01031050540da82c12200003034003403501341035965203100d401003810916504c201130320300e0000d03000010b4801419000440d81d5031140080d100f035995051151011140307503000316400580240414800c4400343e81c02441700154500f004040001ea000703e00144014580141c0010b03516611402c00508250662a030000355420055003030100c4840003c10340407450038254108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 30575545 1106 30574439 30574451
    0x32f040501030f0b070903050a060c08060306010b0f0d090b010e060109091b0305071b0309080c06041202010c140f030306090702030702090105060901021608010b04060807140103 78
    0xa66030103030b002d010f1081c550716051000a0010014030034001d200d500480400c00401880d0380081c400c0c1c0e0085001038900100500c103420103800e250281d844400180140e800b404262011820400b80302a04d5400380101c0c10b000d00b480b210b02400440742c070000882d01c200b05002c0d02c3e204490070380743c121055903224803950844801e51001d056003510f000b50410301600c80c1d0450394008805191606580d0320601800102d02034040b8220042800e4540420159005000e15504030604072003041c200340c500141d103c0c0c203903031b1118001d0401002d25144020410724000c2c0014506518007141c03420441c1141c803d940e94002c0e15814400c3c2400e01c001401d1600c004104c2c1c407107642c050220b040c280d113000103004280d0080c6c1501070650084a03800084d0050a02818000306240400840d185400800f803108542840e0016075880c0c1001d6003e10030f8181e4403402420720803081c6000039070 = true := by decide +kernel

theorem cover : BRFrame.Cov 30395689 30575545 := by
  have h0 := BRFrame.cov_init 30395689
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30395689 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 30395689 ≤ n) (h2 : n < 30575545) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
