-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3345
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:23:34.606735+00:00
-- url     : https://prove2.me/submissions/2b1b3d7e-b1dc-4851-83b4-51c56e36cfeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 601438848 ≤ n < 601618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 601440098 1250 601438848 601438879
    0x2b0215040c0918120302070b01030215130810060b190e040e160510020c1011100615171302060c030409050c0c0d1d0d0312050108010207140c0d02 64
    0x1c20540041401524210380d900ca40a1031561005540b80300d1190288940c80810084069000701c1c08001d001000410040c070051a2043c04038407070028000c00c5500700302041005058034850795000079440e4110802206864801d4001d1901030070800c2c42071841e01030444986819183c40c5000d00c42000400c12401c04a9500d54001103981c85104e0219043c1d82010254181c40d00700b184191032040c812140301b007056500114240c824004000e205801d82c10031060f00380d501101c4514542118081c5500609400903a441182d010340410041b5100942984002404025092001d26100c00d0104104080d07011404c1c46020240e5054985a4840d1031040d4110b146002d0b681000b48102e00700000c2000ba104140081c0c501810786004540c0403c0801c4015200c0784807081c4400900c882503c5090307000d042c00e00c10825400d101e490002001e0444c602d0003030499200307070022260b40e500041c0e207405024203585400815030300741016245414007480002c40c0d803582150020b004160716003e0302803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 601441348 1250 601440098 601440113
    0xf03050718060e04180b0402093c0601140d022212031215050603090307120221181215010e1e061e0a0302122b021504 52
    0x90281c20034500011241e141c0e1030240910b1041600640618a8860300340c0300c2c8415150f6020740c07550081500b202c56256070f000c0c80400d1800030948240302040d00720300c6560f021440241c4040a91401420f2100000b050000581c00000340200c0c0c100940759840176045d28806d02220740d0030110034001030756959050100760450303503181c0b048a01c40c40c802e100003030030100340780344038800e588207907942c50140b011480114201c40041214488a4042450500541c01e01d00000d68100090108a90a0240030303681d408120007d403c0309401a00044011682c4240d03080c188003840b0350202c0580c2c1444152049650001300d0b0301c000707901c40d4a010550b109800d10030320004ea020021814107010039070b10f6000b003540005080d10b403400f0680100104042c0103602c10b1036a40107a40040c060824859450140e40c58001407076203c0e071b0b00c20442000040180e03034244200c06103405c0080a095807810302c04a218442c842304e0a00b1090702c07903444c403403100e00354042413600c80c008201540205503140c0b42003140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 601442598 1250 601441348 601441367
    0x9010e130506010e06041b0f080403033206030106080c06091f0f0f030603120e1504120c08070b190513030305120106021b040207050a08030c071b0302010f030507 71
    0xe01d00c1c011a03001080d9615840d50f401c1c0308210640d800d101e00410140000703040100400313004d000406032102c00c40348a100341096a08540a854085613500520300407100c5c203405031905d03502201e211040501d1107083c0c48500340d40510210300030415a483c1200b000e8480a002c0b003668420440002e18100560383c200415152169440d10201440400140500740c0c0035020b84900128440c2d14508505d40d11a0007214241e0794420b40039040c4512102041e240150b105005942c401020f0020030090301c0103e0150004140444401a07032603101d050405e00c00100343c1048a96401c195001d1288509120442d00b9101801c104514031056041045400d0b00548643d03c00e1010856400428150300c600030b094010b0f420804015141d03070301c10302032781d0f60107500c1145041e048030010700c2c14461070240e001d0b013440c60142d000c1c0c0c0d11b4112a5500c2c11000c0e8411503038005468004200c0c0028018451101c2c1e1912080400e5501101e0441d00042d040b6008145503408040c1c4800008164502c03406100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 601443848 1250 601442598 601442603
    0x50303070f02060d060f080601090501180f0e100b0f0415031b080d0f030f05070801060c0201050c0d0309120c08090918070f06030c020615060307022104060f020c09010e13 75
    0x700041c0c1d171200306d1140403541c0342c840c282e1288155000814809068840d143c1260301250f151528401800b03e80000b800c440220706c00c4107503075000369443c40039007400404411203040d100020030554900801407003418070280c041c0102c0c07906c400f0b0390b0700300d01401440c41965041104100382c43c002c1c0381004491002070300b200c0b00b03070300034a119003958540000d200309801c0ea20352014003c03004654030402c01c40e6001c540c4e4200143d000307001008518041c0c8400e1004500625006207001c402130006817400c442116110300007a6031700e8154042c01041070700e6414481d122300d44000c0c018896110890310340581341c1c40d01d20030b00e0740c0e03804a00d0b00c05074411540301d0b680a58007030b2a040c0d81c0e6417180a07064101c62007a280841d0174035a060741c00500c0411030510403111040c0c151910010182030003260707080200650117500c101c950450050350400d911400e90b042a641e01b030b035120b0400310014803a000c5614514159400507400b00e4699580030042e90540307540c840706022640c0c94100d035015090404401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 601445098 1250 601443848 601443851
    0xf15020705060105150705071401050c15010503010c050304030203030c18030d110706091a0a09050a030507050f04020301060e121014010f0b040b030411010507080408030d1401050303070f02060d 85
    0x14004018000c591a8122141105c80c035998885c180368120551180e0b180060842e00704000c14031850701240c00075044030006141c544d0608030b50701046860208410b0201d0981d030f41c8140100a00e140c01d0140f002071070403030700c1d140303080d400c05039070295490001901c050908540402e04101203070900548400c0b102c0010110f9030310214070725016003210000c0000c50300c2c0f8040c102c404110180210414022604031500030620710361402d401c1c20709a0859044801004030607040002c080da034503407242e0059400b61380a001d40c10310340010488503945000b040c1707000358014401008038982118140644000544180c442c4c12074000c003d83c28032000791402d000c960718120300d0241920040305414142c1d010403000d0010310352962545407840c042ca106145c40c0000c1000000c0001300010f103150000b0406060207810303d1070541e01d900498125803c03401d480c1c0d1000c103000c08416040d01642c01c006000c0d91000c091541810042616072058940240130754100000080840d16050100c645080407140c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 601446348 1250 601445098 601445107
    0x9010f020a08040b180d0e04020d05040539010f0e03010c050715020705190f05150a05060909030a03091703152b0611130f06020d0c0f0f1502 62
    0xd001e040d0080a80e015515907420b0b000090200c2800e0105c2e000d00340c2e1801c01042d91008842d001c81300520303120034a54106030240000008214a800f03114080c511500c05820002c1d034401c55403a24a01240301107490301c00e0350300d64031100f01c011841b8070104282840c003c034151080352400c3c1c4054010341031458056181441003070945a1000c05010068400c0700803c507201c1c404110a4164000c01134040e15a4110b880c44008582c103034070160302407a2288403c3c8092401607220366082105240791030035103540307100c200405c0d02d50034840c040d030285003120000000c0c1094020141d03a40070b02c034410818960b44070543d4091244015501118070710003008143c0d240741c44546240360080350640039008400c81d6070101854840c7d0005c11054400c080e10440e1044002e4843c5406400c00880d000388000d000c0002900c9000c1c41012a0b0140580701c070f58000341450300000910f4400c445000b41d00f01302100c0034a000240c8801e1052106942218000204c81c2050900901c401400d100000703043d4400507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 601447598 1250 601446348 601446367
    0xc081605060c19081012020a09140a050916061101140a0b01230f030a0f0504060c1e08010b0f09060706091106192712050601060203130e09010f02 64
    0x5000740f181c0f400d110540b01103e10044070503580b0300350564845605000030344041c030410010f0401440d006000400304070180f580e4419007411a01200c50600300f0701080c60800640805a0040c00e0300510900c000b4001110940750601c00d95110b8000c2c45c040000b4210f0f9a41c008509400226580c3c080106540143c1042034a0380001c02202e641030b8041505c030164601e0b2503940101c0001d00c5060062603c2c90001381403810519940003c100341c100c6580d603450301c59031505511a080c441c82c401c801c0060039010594014204410a40000e207545240281c0750769140d03401004a41101c440900d41600c928850b090340b031030381c0203611a43c0d0304502c01254200a00020390052201903020703000b000070b08900071040c802144220080c07000400c0c0400c10141103a8030410b030714190203042c030f01c0402c0c0c00f043e0704040e84460012980840c10b00e40101c1d9200081c031106100240c010101d90004526003000c0e880e40c5203012140d40b0446105141950001d11820300c213400c9030300700070301b1080d0841d91468003d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 601448848 1250 601447598 601447621
    0xd12150608040b070e060f07051203070c0c0b0306030a110301110a051c0b0d030c020a0504021b010501050f0d0b070c06020f03090c04090302030913020c0d0e01021c0c08160506 77
    0x482d02540e0000085002ca00c07818041d401c1c1d80c865807409800149031914101400009600c02101200c051003542c07503046071000e103400514058038850383c402c0c2e81c0c0f943c40d04098030f1034140c2e03800600032104c041040c8002c640c1d00150414a603035208070207030314075180940000e004120402692030300d0140050800780c030707542c4000280a001002c9284200c1180c24811507801c9813040140e01c0d41210031b401d0050007180c02070038011002d40c801481c0c14036480c0c0710340115041c3e8018912a8034200c0010481c0a05600300380286405841d043e6003c8100d40b203210002880c940f10400c0c060b01400c10703100802c4105219600c00704d446a04000f0943d034990048480d0980d40e4021501c502c5035019000a540315071525002c1c050280c5d8041e4010b45c14224100100183da940c0c0c08031402d88117a0030004002d03140310070700c80c00c42c2e07a1006489003c0c414200c0306c006410514041582c40f4038040c0c603c01c0105168001e90015000b580003031400d5103401c5d1500001074003c6880e0800341c81c504c42d0794200301800342c60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 601450098 1250 601448848 601448851
    0x80c01051501020d030903050702011d030f030414030604021c0f0b0705090f06120f0c090316051809030d020a0516050d0e01090803090d1a010f030b0c07050d12150608 73
    0x3c1e4201c9004c05450202241251040d843c002d0000e84204295005584559140480c075510702001c401031500c0349001a10b0691559181070442d040828108101c45800c281c0c00d649560603405172142e460240c0c009480040f0001c100d100100c40c88504406001d08001e8440f40c403035110002d00e8140c200114003600d103070440003000d48102c040001c00142030518030169804042d03840d1210070140c407113550340e030040d4400a251032100c101c00d09c20f00c602d541d0304010780140c4090ba682c4220145042409100760034032031454110f142288281486500701002044520004941e07e0040e00c401d005107084802d8491098100055429880f220087c4007000c81c0640e40650103403242e00c540b40c440c0c00103480204d83c5101c2d018080d00709001c5c4800504210600704c1d0100d100d48200c07020f071616041c00180600003a000001c450784178000500030000c0b140c0380365801400b030011640c02c0500316651140ea4680c446000d02c00c1142d82010b03e00d00452940144070000d44081514a0701e50b1034900062510b0700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 601451348 1250 601450098 601450141
    0x50306041209060201060f0b0a0e06031e0a0920121f05010b03060105070620041d07020c010e0909120705060f0105030a1502070f0210031a06120112030504030c0e01170c010e010c080c0105 82
    0x141c0d000c030b00c401c11243f00d458103041e88501141d40e10b550103007407800c5440f1010b14003600004050a05522820140156941d0130840c00d031011560600310f50440864405070004c01420104000740b101581c3c00c01d080c0d0300c1040c0d112001052001503c000c101324408580b806119804010402003812181d500320b01c3c0703520042e00c3d07a5411964070502d0403a900c04603c902c2c203010812101041c48181010410075a2018032041103849007800304000c40600c0d4000354007900c280d0061018026034098068242c1d004210440041003d6880d40c0c441d41000c4210380d04007000c0a9000440504010014502128643d0028100a400d0b50b1541016014000304044100410b5206000c500545407200a40f07120409448003240b9980c01c043d890b0040b90b0a01500360b0610009200010001d0940940e6102a2030980042c41007940f400340710b00702041003d59500c103180c0006612103c1c5903406140c0d00fa82e02000d113403030f1079240c2140c2010001807050aa2900042d4208030401423141d0455a04040390382c2c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 601452598 1250 601451348 601451401
    0xe07030e06060d1113140405070303170717072f0106050103050115050f07060e1e15061c0203030c0c1503010609050904030504050306041209060201060f0b0a0e0603 72
    0x903540d00800c000050502c0c00280f00850703800d0b03005694146041752801144044100090820280c10042c00c8003c0c2100c1c1181e55074015003003842059841404400380842007510290f450400b14400340000c2c2e1401d035440000d116041c001006a40305002c0a840c41c0c0c590115449220704880d00104031450010f20b114a40d82000d100140c594440d204260403503500b24009009044503002c1110703076a10440c249200c40700c09000341d10200d406881502500403000000300803034007003110400e14a406a03a61003000b41c201e001d110311008501aa030941c841e070304840c4000c2c110031030000c6a4040f00c0d0f551f400382d00b603c40442e201030114400208501707041404c4a020180070502c22040c445880709001d050b00140302c0801c02c010303d0600000c059081031090401038202900d85c00420704c0e0850440c1c040d11050441c0700507d80d10303900110840040e2281344001d019103401d16a41100700d07035040c031450032074240021f04078074401d2044d00501e5583c10b004013a10390b00e0811151109180d09221084003202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 601453848 1250 601452598 601452601
    0x1220061515040315090b0a0501080c01030209060703030507020709020408060105030c03070501020a06090812070201051e01060e0d2904050f010915150906080d080a0e060414070e07030e06 82
    0x240390103000e0700040d04008400701d1501c0e06598840400f00c00448241e0a026120015103000401041c0c1041c070900810f0b00000396585083c05e0b091030040e44001207410b00d4410031440d085a200e40c0c0403140204d406082c041401e07100c41804a203481c00513400f0090072440130502003101c0c0d4000c00d200e8103d0343c0c12821640c6a80e510010103850303000f680301c0c69000d07900038280b017000103049400c81145c01e0701402c0e2082c280004240c0304400034070308480120060b5036441c100003002c0410b40f22004048005185c0f94455814010046c240070850181588210b401c900c03020304128503000c20300c09028a801c560004007100034800361600c001907508617894020800e03002c1c0209414818580680d80198502884a030326942c5400200300101201c2d48000b110440402d04402d10700452004000c03101c010481054401e0b4000c200c803502a20ba84002d5051084260310403c0009519070425000301c502c03a100400040550b18020f0250311107031003420300c20700300075440740c042d030260001204a0050b942103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 601455098 1250 601453848 601453891
    0x210a0204061422090602121909050d051b0f0619090b0106031a0306010608220b041b080a051c0e030604080c03070813050a060516122006 60
    0x4102181c40c03074640003240c92001110f10f1a522200a103400c40350742c0002078a51468842005030b03840755100c0f0031640741901c280448204144817106400440038805c01c080f025958406880e600500340c14010400041074040d05c004152070600d032550b81040c1100e088210718501c09886100c1280e0104400032018105441c01c2514011550450b41c0f01301c03c40c10b00d07820040150010300794549101095994000d150b8a0364401f000b2841c003070522911107507810300c1c0c81d200015504111400c9c0c061191030500311180014603004800d504550b005084200700e20203079148441c07041495100804511070380044c1c03400e0280105014810054000280000d40780703079034040d180b9502c0320b84402c7e015403140740002e0203d0001c8014011036403641e816039140039102d44a44800750800170405001000768542081281b4004501400405c51170404078184106940540d0707091400100c080e090b200038090401000d4407071490f410f001c0050110886d102090b6042450785ca45007100c18072103d600000da8480d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 601456348 1250 601455098 601455119
    0xe060a052203030f0f0f032d14100b040504020307110a0b33150c1e010b040e100504020303041211041512031d04051623090f210a020406 60
    0xd03075030310710f07246d0402c01900701130202c000b8600688015400ea050a50070030b10305503d02008013001c00a50380c082016020f424000390726210140880401c41c5103c20100115400c000903030341100c2045400603141c0d6111103054070a41c08968100056006420039141000f121a0b800c501410601070030b48100c0301c64803040f0188041c3c1000101c2101000c0e100a045803500181940c0f03075220310000325050140f407600c06494035030a4095031036501d600f4400420210824803c41080000c122000c2c010040c020002544480c0c192024402050301e070030004040d0b40b02001114014020180c0000104140d0300380101c442c800c030039005106604052000101e00300400e81c00c000d80b02c0031071a00403400d0342c66500761141d003191941d1001203040304407441c5540e541c1c1d00c40e00388507259100818501d00605103006008030b0345607001d2254040c407a480f00b100440c044054803405201540d681c54110b91090000d10511921400ca00c000c441c80c80450026050204400c5203181c03007620140302154035100f130100f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 601457598 1250 601456348 601456367
    0x120c0d0905090c031b03090d12091a0c360d050c061b0a0803160503070207060f0c060911030111040b0307031808040b0415020d0e060a052203030f 64
    0x50b40b040e42d00c1c01240c1c000110b100107640100990300d003400c518129081c0125903070011540400d058004403e80040716130042a5401d07800741d42203003004207603415074400c0c42201691b80840f540e104680c0000d18244429011140800031040400c140008000703912040c1d03004104421008542945a04d13500d81440b542032507903564008050140720b555007090002c2c0d030b0418000400305c1855541448044034090050a04c981c0c01480c1481d6070f86040c0320410700c42c1c40c81c0140c10f801c01904004004c6c03142d501155903010f562036490f011020300c1c0340c4242243d00b15400a0080d1125242c4620403080000340780350000a45000d07002031122030840c5080000d280541d104a8001100800c00248218425403050185100b10104903080c0484c1d030b266070045800c1a00203641d032070000a02405800e11004400066401c0c1f0300c014444003601e4000280003081c0d02d80c103180a00008a5001080c03030141064904880c03d012580394460000161642c06950314441038011904002c2894076252046513100b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 601458848 1250 601457598 601457609
    0x3010b19031802240d020304120513180e0607020f0d0c020f040902060c030f0a080109050112060e1227030102030705070f030c08030c0a0905190603051503120c0d09 72
    0x14200c1d46180d40a0180f02d4802941000c2d0801c00c58000c00c0c0c005000c0c4c0058000c0b00c000c100011f03241d162070310348051480ca01c4a03900d014044240010030651086000800903034107a012190301002401c10500050194010480428001c1400b000140c0e98006500c00794090107404403032030342641c2c0006a07071110030380c00040d403c05c42040410700d40d41410741002046502c09042c5030f14103003a00c0311041c1141c00800910900721000030f0481907070350f8005401405440d41d51010441549441200781c4200da038120300034204d9803100301c0c1a00c02e202c18420b6001e0f2501c9148510741d00c030103c100702c18070214044410021080c05810401180c181482943d20480003912510b20300001d0740c13145501c0c60742c0814100e0802c409100350000184040c00918025020550341c503495a188032005000308503180c010f5402a108030090151030211507104104891a500780000c45443d076411041480c0c0e45c000d15942c0500c1b81126070048080c1c0c000c01400c0618049056641c0b60541040031100d0390024031a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 601460098 1250 601458848 601458881
    0x8070e040e030f03040507090c080103060e070b03060d0507030212030915090f01050d2009031507050313020a050d0c1e030c03080c16090b3c01090b03010b1903 70
    0x30460700e000c0d02801103800c00d010f07030211032010b907803118214241c0784649c000c0c00026040380c00410402c03095000c0c440d0b180c540301001d4160181400b00d010441d000c000c040c01e01c240401003100050140502c0300380081c50b00034154441207041041d6565aa03880211003500965520358008040300da04003c0d80c403103130401030003d440c0801400c011100c80d00400d5001c80da03182e40d07107100c5000c0c01a4801c80d25103540da1480c000c1d03d5030400e03001c0500b800310080e00c40014401500811144035840002c69500c41d032066034002c00f501031030000ca9081286034104a03000b41035194a1030502c08021141c40c12582c1c405003001320b100d9040307880031500450748002015284200c806200182d070b0b40001d416a10400b8045403940c1e5414030180c00c2d850001c0c1c1c0840e610070303907902d580d0100c1d081000000113110304d4012424090507041407909404400034656101050f8800200080390303100b000c01800902c0200c01d80c54495031201c11081d03055020041c4100350300b6102040d28a81c902a0080000c640e220055 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 601461348 1250 601460098 601460107
    0x1c12050702031c0f030e160308160c080105270a020618090a09031206030f060b03030c10020c06150d060507020115090501051305010b07080c100c08070e040e03 70
    0x41a252600500c00807039150149020a8000007514409034030714041554601c00d406443c00d40c050116440f21030710f1446500020741200200c000c00c0303680c10440358000425561054851407469030054101001000740039001c00000c1d81000540149010700d40403005003034403c804080e850000300c641e04003400325421481c0033303e01520705440035020010a01102002c3c4444580010301c044104690016800342d8070303040a0189a07010300380c0000800030700020055141180c07581c0f80106080f28005096586841030b4a2090b04c2c00d2003a00e400210320300c1240d0018100c064a8800303500880b801421502c603440005400c09010041c4a00c3d01d40e000e40402d41070740d01d0f81c03a4503015000041062042d0746d00c41800069218400c8203d07001480d0300a40000c075541054100001c0e4032080740c15031016403d110050040c804180d00b11a8807a9000c2183c1c0d654004443d18581800d0704030220070303200b9141c44a9003030003e8001c12001e03c9402e056403103540f002c41b035400b04411500b40c80d0380c18036954410321 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 601462598 1250 601461348 601461383
    0x3020d050715061502010e06010f14041407050c0c090402060306010c0c05030d0f0e030615010f230403060f0507081b0903100e100207080304230f0601051c 68
    0x80040410714060b48604900c02825a00b1500342c80d510341c00000c80c440008584c0c14403603030a20405032004c00480240941c4e51410744900391488090007800b00925280c0080310b10750396580d120850002180c001920b5078505a00c1c0a0f00c030344c01041500e981c50280301c04041461401005e4148140d500400719030540c1c41d0440111001092005c08032181c0d880c1a001040c95601080322031312074006070760bc0170340030749803400c00a1104405180f114042c0e4040303820f100700c08598641c241c0011200f843e01c0b24650852000c02c0344c0764800064107030304a4000b81c904035400040d0f20300502c1901d001301400d00c01039001e5900c000c00c480044980d000090300082c04182c00b00c20f150b01003030082c0100c01485007440d002000182c104070000a001500720b0391640388501c00b480520808400b03e071552070840c1001c03000e48844116210007000200014031032844807061280701c0340c205524141c05c0080320302e12000c1c420340c1030351071000303006191140c0c0c03d6400a0a0080c5806180c3d20143d901c00500810401c445 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 601463848 1250 601462598 601462607
    0x10e041502070c08010e0c04060f09020a1b060c030e0a020928020f0409050105031504081b0f07030b130503040909020114030a060509070f1b0501061706100b040303020d 74
    0x9208100310390200310038000f04500a4441001c0c0001c4800003501c034110000d12071a0041c25103070a8026400c0c0b410421009003415045412501c6400c0003696604413808111a50442140c500d884003110a200d8010b200071303580b001899141c40d032001c000368a440b0f401182e5030140502c00941c01070030600081c0100c00c40003500d034103041c44160406254201c008494040c1e07002540c0c40d01590b8000f00d0104038840d0a801581c0c01000c050b40a4140706000e080041061030004201820070b407000165180100801103100d804004410191400f00d0351041045488205900c801c1d55814684c0d0041490700c2c410f0030307107468103039880001186081d10b00382186002c4d10711400c0aa041c060402c9103440540c3c801401580314140320740300028418104810015481c1010305800c082000d040c9140714816040355505034a5845660081c901c80a0f500c0c0c520b0161030107070003141d00c005040300b101c0302108001540a000300c0350700c8411140e03191600c1409006024911010700142e10a410000c40e083c0035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 601465098 1250 601463848 601463873
    0xa051c031214070c06230901060501030912030c140406021e06010807030b060609120609150403050703031a0307060f02011a060a0810090903050304021e010e1201140c090a0b03010e04 80
    0x1c04c40400d01d51248006664180112045502c2c40a086d008008107140300b803203004050903090a04000c1c006494035101e049816101115050641c0c4050000445000b500d49140c4941041000c83d41c0d10340324007000351a10030000f4181801444107032803442c04280031507418161444580200080f500c1c2d51103440344444081c2c001504907804010300d0146894410810340803001900043c18641885075901c0c0c42e000c030754014842005802024000000d6010007100c12068041c54003061040b0404503040803000143c6460358548948480058040d0f00702c3e1b00508071141e00d070003c0250710002180d481c2a80346110015500c4041048403800369401891a0f581100b10700c2d070389400c8261034551030b0007210750148042e0081034001c800c00c01145040884a400d840140340c10001401e034140010f00301c5600d40ca03010b8422103281c803001030000002d41c06a644c04e00020807030940b0382001d1005c161a0380c80400840e01542c500740d80807400390824400ca9040307650304804100d071541c1c1d49d200e44920004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 601466348 1250 601465098 601465103
    0x30503070f12020a030204170102040b040b2511150f040905180f011b0c1a0c07020603010e040b01050909030a030b010507140d0e04090b13020a051c031214070c 70
    0x6610702e40550305580d032003e4400100e0b152030040e5618108011110710b042102c25507502c40e03004010610188c10042d05070350407a598481115154200a580c441d070008484204450300c68080700028207103c2c40480d9400088000e84013041d03039603540c0c00e0003c2180702e81e2080c0c4503660402c000810030b07403100e9400190701003000b51101e203c0c0c02d070b0200b1190400d080700c0c41c2c2210581d195091030140c0002514807650071201030400c0b00d0700716030307541d1034805101950315503510949942d00010f03508600c050440d8020b960042c180c559a40e1150108100b048050b1001c0d640a24a1400401c5600700f400300c90b80206070b036000542c2098005d910403009000141111410040305100644c0081d071342108006075404114080e041480d0b00000080890080907a4103110b98105040003002c5020100740d1034002e642409a08203114260003c150341c180e0a90007a600015690030040085100a074000303c4c8900c04d030786030030283e20850700b090140e41403803124800701141c00c8081901c4500840683d01c9092 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 601467598 1250 601466348 601466357
    0x903031b020d0203061003150507170603030d0e100b03190f05150f190b1003051b03091509010c0801050f0d1403090a050d030203090d0c080709020d050a09030503070f 73
    0x324039074081390415000756480c2541d8010b1030000d00410007000310850034441e800303004203c01e1411850040c14000c540550b50b46030f04950020a1050b02d00f40210380760607400d01c4060000d46600b00305280da80143e141402030491804a483c0214030380413551006280c5098041412520036444400d21003904400403180780c0700f2041e459903036050310311a251081c0d840600350f03802454100001d490740d80f144c0c010710a00c2d9152503c0191a99a03110800c1c00c04e08161600254641d10700074607840c0400c070070b500102da600c00130041109101d40065020641e6101e1460400c20fa15020100c5090714100e08140c4049444200140501c3c20010100304060400502d60f070f0740511320b500c03600c03001c904030701182e0803542000580c5491814003c03c07481c0102025101143c00b1285030310001d40b24055408081c3c416080b440f2030000703000e680070000300504510401d492000365501c55031313002540404550006541460006500ca006912440311000e8158984a00d9962000b0044500e803211185200512 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 601468848 1250 601467598 601467619
    0x60a110d0801080c15030a0e0102071a010303021203010815041509050706020c12070b030403170a0c200c01030f06270509030f0d021c090b060901060903031b02 70
    0x104100008019500c103916036a40c0c03541880c20f0507060034040f440440c05003034207003011181e030441030b81101c3c0c1c40080c02c040000c0c51401034038158064480c450000d41270400e03000915074100138125115040740d00c0380d02110203c61030310008a00c80c0c00b00b44586602c540040d0300c82641c40b040700da040e5038042c3c45100340c0e15107019a0b0780c1d07a4080b100c0000c4196000d0740444014045c50750100403c4610340310894420a10803d00b1403040c0c0c1d00d0b130a07809070720f1a406000c0b0100c2c0801d40203200c006901082000c0d420780510b00030415100401c4100b00740c0000440002c030101071807502c05040c00d200d241d604090910149950300540c09014040040c1007903070399030500042e41c0d81071018024128443c1e0719180700000000328054041d25030241c20070560350000c0182c0011301c0601012208000e40c05080075842e0f42807550303400e1641420b896882c11035400e0009000800031400500780c0328140071203445a9590702c3d460103d4400751503000013004102d0b4465080c079040444200348041c0c520041468900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 601470098 1250 601468848 601468877
    0xc08041809050606010513120203150109051603060e040b071b080d0507032706060e0a020a021b010212031504020c1005090a03051603140c070911090f060a 68
    0x58503211451600d6a03588070102080024088a40c01c5034003481c0a90400040282c0072409a11512824103c0704200e100d20702152014020303601c00c05e00030100c0c40382942e559400300001c3c11045410801c043c1913101d206609034020700c24501507860300c0084030080c1d0f9450750f40259212000e8444001d0003054489010741e4200c00740590f444c60312481006071542003c001d054207484003d001c45041c54284a100c0a045140c444000081030f1820925101d002060170704500605168100301107801612040094100c1c0b10b40040c05007905603401c071102003e585450301b2950101a030014010b800c2005100458110003002c1c6030003400600c410b22903040d00d035002404a80c080020710030207400c41c41d030486500c5001c3c4111a400305958000d1300c560152950002e1080c811a045031402d0a031201004d000d06200c1c4071050010010600100da40e03400014203540d407038096100b03400c042c908001c00a195090f521040d075020b04000b80550f81c0d0180c82d41c003044200d4003d0a580000c02c251581d22201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 601471348 1250 601470098 601470119
    0x70e0c130e07050403032d0f020115140112020c0106030606030308060301050c09010c020f0d050a02011719020309030903012d060509060d1b0605130b0a080403180b03010e07020706020604050d0c0804 87
    0x2203208158231489081e2101100290030344544048072a8513054407c001c00650300103130b0300551200c00074640144000c10090144009020304030503000c03035619000c8040100000c503405241501e003e615004c0466075110308050a031103003183d48a00054080c0407400072540604500c0e4a82407000342a05884540100800e203400304945003034030741da80001e41c0034087d941c1005610b6120b9032100552402c511f00940d000801440d400c1d0907000903540000060016007041c000d80e114050010300920551503045800c10825921b0000000d40d0900f918441034526003d108100440d24054082d040c143e039101c041101070390f421201501d9840b06484071040c0c1c1440091024040d10a17925410341344c10f1181004007a0b00c4141c0c001e1102c0140400c900b910705500184055401a494074286181c2c40ca00400b0300350203c80c9501c043d0850758007000104807051080403c5100740101d82c204c1304041c0c3c0d6400c0485e5518010f4a01900c140c011003031941da0188500a08640300e40901b00552034030340d84107400803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 601472598 1250 601471348 601471427
    0x915091f11120c1e0c1b0a0e0f0103030f0905010801030210020f030d050403031401121103011503080903061f03060c03060f06030e01050a0b0a09020309070e0c130e0705040303 77
    0x14a4030000145812100305102c9000104544880d080e0b08022042100507586e041d400e658605240410b0151100c07942d44101090181c9031416145078203040150030404402000e00003140403a2a108035481118400c09000d011070f00165100042d6034a50b4081c801e20032004a187d404502814805511045042000b800500982c0e240010b952a283c203004085405e01040c28142c2c010703490040003014682000a6409604240840f00b510450400640103080c84441c5182604900c000007040c019002d01801c2040703401d50585502d6920302080801c0c2600700702c001010b081d4440011f101003400c0e5480b412081d29071b030034001011519840011660a0b03268080c8000a0300c0b405e10f901c11200a0240c50741205e51264140480000d030400a00a41c01ca80600c032840c55002c000500d03508800c00c85100181b0321980400c1d0a4180020181d005521180400c80750070700e1000c0003d03941e01000c1d1080c2c03140009541d0941842e017140da0458404d601e140b0012316400016040e001000f00326100c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 601473848 1250 601472598 601472611
    0x3031c0e0601030b0732030a140a150e25020f0634051801020a0602121006090b090d03210e01181511040e0915091f1112 53
    0x203507024905a58020030b246a5450101c400112551041c034106c0540f100c0c1a5400301c5085442e0740384c0c4d40310b5514900a14090600c4002820300c17405001e5079806c82d81c80750f1100d1018a5120a5007501c8160420400398251055104c2407004044038486441c10021100000114170503200200c0e0086c9109103811410b4407181c28541c3d03031040702c110b2045e41c000d1080f4540f607803243c80030005d0550440500709014043c480800c9014000d100405680309000e9641110f501410840d110a465082c01240c460200c42011582040b490041071707103401607a800d0100c40c552041c45141c4601c680c184903000d156020120705002564032504c1402c0e64041c10200c072103071240c2c0002070032a00107007483e00b07607168498034011401c82c0032000d07000705400e403001c11108194a030b0081030b444102d001c0c1c0c440c0d1744070340d60068013000140401e111005e0381c04501101145002482d010b241e0715106030460701c911001251781c0501d00c2080082800001a0b000262102e01e85101e660800c40700000000c0b203100e08441c0c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 601475098 1250 601473848 601473863
    0xb03070e100806030a02360109060806010e130213020d090501180305030f090c030f100615120507120903021c050307050301090209190b0c060105040b03031c0e060103 73
    0x1900d014103080490311242081403404400b10f05100780401d0b1100c0c01c5800180c09104060000081c0c1c000040d46045084002810702c0c90400706410214240842805030060f80c504200001030020b00009109060350079000400300b154944d410030b51142c0d4a41e60040360400416506182901485d1000d00740745000f4440c00f040c03881841ca002801c65841030800c04141c10311108020100b81c1c000c060320b134028040701c1a820380742c951711400c80c5800112104682e151050802c40051366801007203555400c021408184091500c3d02201e00820981c121010f0010b0000d288494803c26150052a001206420f1140d002c44522010342e05817000036105a0140c1c3c42464182400380000e446018515054030b440c80c01c41c10036050043c00c80c031061091565180d00400c030242c4503501e51600700b038103d40082c806907040d40d9400550174640c10003e8017003801d0184400004850130b150050580c0000000c002d540341841814100e03804c90669013040c2e04050713a0f82464041d0340c80800c0424080c5004102c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 601476348 1250 601475098 601475117
    0xe0a021c020f1e0c0c0603040501090f05031309020301120201121506050c070b0a170702010608031201150e1c0302150a02072001120b010c020d030f090b070b040204020901090b0307 79
    0x381204000201c205a96212100f04074002c104c0c6400314486868150803a290341d540e0305c8600701140540300e01900941039446040440042100000040002610038170701c14201e0b030b070340e52840c20407400244944661211164080380040d07114195560803241c11078000210142c820b8000b01c40300c8440d80020022941c0020810f1082c02e007000031074014091004110b00d403216400d030050100001c550011000d1905c0000f00e03510038000c4d002240541200c0088a460b0300301ca80050031040428030901031080d980390241d0041c00e1040270241113100d006032210b5060110b213003121000e8520940e00b501140100d80700c0038034004080318000c2c000e5050544c003680341e04050812a4030000703000d040e01c0f25402c40e0240361030566003001d240d14008a4004001402c14200c2006856040304178100a41c030181d600c44500400d508401e412008280c00d40d50300088540b51082032019104411026140b030030b031000010018a00351b0006c00b010041032519000003603580705045101d4009960901c0800c50908 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 601477598 1250 601476348 601476367
    0xa150603050105040f020c0d08090a120e0a17120a090b0c0a17180616020301021c0e16030803060a03050d12200d1a1903140303010e0a021c020f 63
    0x51741000c0240300821858440701070551985d911800401d04180884000061200001400040d00c410340101c03280b4040501a903008105c646415920b0b88511894200441c02c0400780001151003840c13140105251410110008816001030a1640c104000c0f44004205a81c00c2c1029122a01f20b11340240a449400d1600740004070300c03000140d40341c102c00c1c440c80070b1840101d210700b1000e21090701d00b156101400c224900d242130f01d241300a501580000f44030403c1000c0408034500c2040300c5002001031002d1648204e8407500050030100380f1440c94807081c008615082c0007503410240c01030587d84050f82c0c0e50b440509100450700c0100220f10244a50284017006000e8a001414460301120113040e0f40300b9018010b014464804c0c01065036035202114200168001940e03103000104400c0c0816140900e440c2d1402490004991031344030078903224003100c0000b0640341170b18001c428000c000c0c0e4905a00300c001350801042481081d59040e01195080320342c2c4011714260340120005a41d406800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 601478848 1250 601477598 601477601
    0x30702031c02090319170a020a1511040e061f020d180f150201180309120f211101020a05160c0312030204170708070510050d05010b1b0a0308010e0a15060305010504 72
    0x74251180106c0007080301d022441e0740480d07403807100c6901c421203402c040f10312a2850300504821206031504c1c6000200890101e080f41d980030312481c0c0895004d0f14440031401c00104450100103e0000b581c00114414030960140001079100591003002240e081d40c1c0317110501481c50107a0000c02244c0c80d1300004c8290607030a00918868903840e480400c0115682c3c2d5000b40540114410303802407904070700070501008901409100c50f2a000351010224810003c0c01e0074801c115a50100003040c0b0302140700056010600907282200956140d143c00d040c94031810028800200504540b190321142d000700008054031084a1844a40c1d070f00141c54a041004802d40d103641400c5e5024544d0100344100074024000409034141c0b2000d071200c142040d910745080c5c8046c01040c603000002d078101800400d0005c103281c00307400507044a640c824201003504000035290201050003030002040d0200603c501403912401a03004811075100240164a1040448603500035800a038000382e229001002545000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 601480098 1250 601478848 601478873
    0x50403030207050709060e010b03071b0804050415030b0c0a091e05121f0c2d03060501110a11061903091401020c06061302040e01080307020103060b030702031c02090319 74
    0x1518170800c005400d0940c503c900c007038148201c405d5004004001a24a403050308045a00e4400e000b034428501d0240c0361107222500706004040c082d074034058081110644060140c000c0300e421006804494680e1020354a0320342c0034058a00a20180301c80014040030581c505042030131039562824003641c2444200310321070508100d0307001c0d42d0344014100400c4640c880100c1080c50b403108030024200d107410070281e0b02216103000c000007981ca0760300907212030400c0c1e95107050380004e20341d81007081a8854005403032419a43c4002040b9a000d4001c0a0018050448055107450010001d40c1084600468031130300175002c94019000039201c46803103040024000450b82e65111102c025405c00c2039074214281d4a59004001074810311030b1040c0504650000d0b070483d001f90008006c4040c80f9a1a084e0659517540034240490010340352140003d01305c5115400d5a004401030340c00355140402e139010042490780010282d440c1c5550800c01d900d0269000c20215030190180c0c02d0800400305103042c9120355560 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 601481348 1250 601480098 601480109
    0x50d05060a030809011d1503040521070312060905010815070f0f0315030210170a06050108062707030e0114060d0b2a090f01020f0303060607150504030302070507 71
    0x2104a424000039280c03406071340c00540700786400755020b07a00d9030f20f007200325440080b03050f0005108019100c8420304080210300c0b440c040c100702e8840d40900e220360340c24080f01d0002241c490030280814000030b071003494043c2512074103007000b0944e01d4450003c0170480380300780e03c00c030603e9005045613110402d5542c01658001101d040411090b00f020201820411000b042242015510551188841d44c0418904003458024011f9070a40400d0007006c1d064440444e40702e410203076040d0004a1400c09401140180d07007043e07507200300715150700b028440304074050308480703105410000540d00c080b8480d82c032252048600c2e81d400f260100d0902d890500310390340084807032941d03281c09c42048000e0b140c00005004c0590310138146911542c481c01c42006205804103110354080017204081d0360b04011001618843d90201c2e41c0701110240c0e00f0040e40e8401e080416540c0c581c0003840001e20900e401c001a000b65405030a0400c501c40101c8281c03070441d14221411004661b01240d1001881001c21010010f040b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 601482598 1250 601481348 601481359
    0x41a090916020d0207241b050d090e160f0201090512130b130522060602010b01090e040308190207020d060f05130f02101b030807020d050f0f0c0309030d050d0506 71
    0x900f0040c548100c0d00750000402d04410700741b68440310140c030500001c507190401890b656054070b81480c0154a0b4130013080148001203840700302065490080c139544d4011143d0340c007009079040d101007003641c0c854850f10820f010341d50b1351100300d40070620a1140100c460300d902001565141d402c6840000075000e031300400aa03500c00c0c445102002945103140d02034440496060901103c84441900002c4040c02c00a643c113003040c400086154054100c20b5400000362516210280c450b202c1c085004011100600012005008078042c454510740780b04c10625000e00c09072503d01c1903000b00702d840501000466501e5074900500c01340302841e20070b15410000300000d2080962103610f0765940c03020140d401a1003801c0995400e0400c41c00f800003809004140200320046a00300e0401900e003400488103e0058040c8408020080380b060b0102c0e00c4046064203001d04128051055020940140c014661144001c00510010380e50410016200100f80d81d120b9a03103101c0c01c0b025a0035183c01501350390103039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 601483848 1250 601482598 601482613
    0x152f0d0219021518060409021306080708061e0402070b0a05070302121506090d0614060f0312090301020f0f0714030304020127170c19030503041a090916020d02 70
    0x40c3d03104a588004500100089521505850510802040c1c0004202da12038400a00003a0100392900902026460030407107160103030381c5000039036044000b04d80d61400180010700140d500d103001c04030f0b0310b40840c103400d081140040550102c0c04a80c4200016141881c1c010100800c95105d0b006032984482e40e0300e025410041203040f514030003540504000c1a00501d0096003065441c0c880136101520401060a110038034103051400050610200806c0d2020f46d140c005040c60400d944400c18400024004000c200340740c09104e4419040802c825625540800080c82031481c114003800048c1c482c8907040759524007614140d1040d8124001ca45a60741060080001603a0808520341b000c15072640700c1140c41104c04801c2854030f16940280700c002072080e00b410241032000404028004040d54020a8010300a448000c02c2e00188002022540300300f000703004090081d007080300031550458103141444141c80000310b060200303c1d0656110280c11021000316a41040100d000e40c520740081e1040f0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 601485098 1250 601483848 601483853
    0x1621091112210c12090405070e0a060327030816020706020705010806011e0305100503070f03080a11060405031e0a0807030e0a02061206100504152f0d0219 68
    0x54601007195444050b800c072250158900301e081c101c500244504040e03904c41c090241102c1300941241c440ca602031850200011881c9000d05500144a50010940c4058905e40b0748220301501840303024061041c138044d0021541142c080b0000f800764465103e401c070528200e80a80300755510f524481045620140003008120707004603560702507070400c1c81c003241d040d43c07020016a0945902da03900048220003144401140c0c0d459813146016030741c141d0f002c000103952807003090703507900aa000d1816484811441007002541c0c010040201d2070320303802c100f5158403280b01c0c034030304008003182c0030303200c0360030000d42100c1d4001207801e0700041030761916001d0700308461410010030400d00103000c502410350740d03002200ea01100700005050664020a625030350581144490968881518034602600d03689e0201c064841c05402554140c4d201030340741d405103c410780c50813075900b0b180307040400d2840d0010800b84802c0048000c0d456140b40030400030010101d540350024601b49074528085807200d5082c0d0103000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 601486348 1250 601485098 601485103
    0xf0328111507020103051b0a02070f0803090105040e06040905060114150304031b0819030b040b01030204121515080a0b0f100303050c280b01050406030206031621091112 74
    0x343c0a10300081c1550765a007074403da4242c1d001a56204c4c01000c110b034901c3c241d00080820549007041440c00d0b41d913982d900034554030b0007000d00d01808220181b00a203d010717405590294440f030014400710303e01d082038566030300b0000282c20451210004d10303020400ca0800d250b51440719524103070103a10714541502c0050000344889801c0410b403050280c800c061003200300c241c4804820380c084d012207140b035401c1c000d8000c048401029005c0c5003402c1d504045503001c1d20a03101298001e51154107020b0482d41e4200034081d241c01d09890b203541e40d403249a10b500b0703641110800341c548030004004000541c1000b5044142c0180b486880c1c1c882401080040f0041d12866000c4a03418100f05448120794039046041c1f1801e001c45101016583e200c46500c50300181a801415019002c4a038440e40c0360ba062105440032800084e4010b00e08101040c03d11580100c20b850b02842d51603c020410150103010782c0380c0350612604455182c0319803443c4144000c1941c96840300e201207039002210b180b1044420b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 601487598 1250 601486348 601486357
    0x9050d02010809010f06090b090903030405060c0a1404060c02240409020f0d0e07030b0f0702060c0f130b0306100309051b01021612030e0303090f0f03281115 69
    0x707042150100200d10090000d40195407860144003052028613202c0b04440c0040002103c42441100e40402007508584044104c0f03000351381010242a01d40d9a00c18400015401800300c18104540903032901078080c50940680f010b00780503691403281c0075660040205000d201c00c0d11000700e050001d42801e0404540085904a41c190003000d40c4421505050421034060755065800c42418018000035010021542205480c4141c44001054962140c43d0f90710400450794070001d81c0c0b110000c101d00312002c030050070074904091113462408038003099484070101507a11040c0c45000110038026280f41c0381110244d920120f14081140c1901919203d5448041c40c240c0e4141c041100c0c48031102c0d03442480161100b034208608000ba8690b01d078400740c48506584010750029058030040342451401004441c00f4602c01801e030708042d0700300410060141280c041c03050b4584101c1307400d09840100e03a500b0700028403040121030996050341c10000d520000854006219112300e40f18580010403420035035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 601488848 1250 601487598 601487603
    0x5040b220207050304080715050a090618080d1e170c0c01060f0e10050f03030d053309100b0f09031e21040513151208030a060609050d 59
    0xa031000c44890030400a10403500081e0450100003404520394800103590411100192441c04080b40300e00c60848003405a11043c00c00a007241d40e040015501c1441607800078a6a007505c080b28a60701c0b9101c07031420902c1c058100214000c958032444502e01001c6800034440ea1381800030368200101b0302d041d0b80d030700300404425601c2004113654846d000d0944c41030f0045d0a400303945801e0b403612100a400561012100d0080c6071035015408541c0b070501b583d0122211802400031030610b0302242c4408060203005100d06510540016040481d82008452041c982400c824100c44851030708103210108000400101c00001a0341003001602440c50448451240c508103940e182e5444e0000a424104003100d9500c1c4005010002104054042643d2511259416000d4508059072003000d881e07000350f214081d80a1903a000c40d2050042c0d94021405a01c084e00000401603100c039036a2000f03800da00801e41d0b01884c080704000c0507500510548020381104d04001420b50305e0000080c990030b1790b50000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 601490098 1250 601488848 601488889
    0xf03110d050a0209090c041e030b13030c050d0e01140a09170102160b06040b0f1f11030f0301081e0d030905160308030a06170606151207080a0605040b 66
    0x1600e0b1011950540351090802007001240381809415000c80d030f000b500400007a0282c0d00c401024520501d001102245d40c81011540e9541d50700c0101200c41d0064401a030502048083c140c00240d020302083d24507100b25150342c40c03454400301c00101a01303810040c04104d0281001301d620704941007441c02040320442100303416005502c02e0410f02a001d1440c0005508480301c1283e401c01c84e15041d02c1c1d10940c0161010031180700c520b0200240c0d00000078400c0e030010070b8542a47c2d910032000a03a1784106001e402e2008000042a650603c1c550008840701020903000c03005204000c41480311000341c0860300e449044060014007056158148141100c05040d561050501042814000d4610741d80400e18404290340d0350382403943c895841211018200c500d0214049000c0350600c40e094000c0401030002c0242d07548200a02800400c0341c500d01c0c0c1303c074100b03001000403100030060b0203102d0070743c550703d07000d490406003421030a59806800052085040c00120030740c1e034481d0140150f050000044c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 601491348 1250 601490098 601490101
    0x405120c120301081024050f19081006080a0b011e08010203070903140304030b0a0911190f1203021b060c2e05010f060f0512070f0f03110d05 62
    0xe40500e8900440d01d0000322500100002510385808240c52070a00c20500c0d0070300c8840e4503880040c0380c0c1c9090810000c044280032070b090006007000460000195005006c04011503520300b02c41c515800030398440c250a42c8801c0025103c81c1c0c950199100a100d034070000c1801069698500c9914071050150b000300c1e41d0070b500f01030300c0075101c001100010150304008650341e081c80d44000306080301c940010f803200001e54036103182c25040002110b045a0304110049810346800b0f5100025041254040d54800e605007000d103c940e070f034114001e0410b1002e1001010040c5441e000c1c284600844c2e1014045000700500d940c0401c5d00800ca0300c20741d01104a0700410580030074005922400364856034401c9104c2c0610322824030206806543c1c0c41001c1d43c1c0c451900ea502c4100fa082503c40900031480c842492030b9040000a005212602603007040b41005801c1c040c4c4040d40c01e101d40790071181d4000050134090b521a50300c0c0c002000c05a01c0100b442e0521914100700440c06c040d1107550b0745409034969400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 601492598 1250 601491348 601491367
    0x71d07080c0703170915150f0f0f0402120a0b0301060e04030827011a0603150105071a0f0412030b0108060f1c03022b020606060904020702090106051e03040512 70
    0x3c40c5004e8001010304c4040700e41c24041342c00ba03950030020101d107050103200c101082403408a0208004007000003880b200c0c02030742010901c0b05007681c40100c4d5030026404600400150394500140c4110006103081040d18540b0018100a8401d800e80440c0a83d1500000340002140c1c10051a80a40c0600b442e4449844070200452200203503080103402c00c445030700d07040259106400c0700e903802c0e100c2846203031210718501c20007030a44019110743d03504030703c00440080340f5405040a0880c550152011085800c095408902a6070040383c502c10b040c41c0c168100000c20904528140303c000040c541003218075070303002c001782039900041e0000d4814070840303c90900641d81e502c201d0580001141c401015003d2a20300039580d0510410614814118001400440380c003852031102d0b002c41c294018000740d100c580c00d000d1300e40c0c8100c022580140d001c00400f000340c3c4501901c103000b8082644c806071b0320101301c001c240d0720000500c1a210341550420030301001c42c500003152480d0f00300d0524501d5603a102c0c0c4c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 601493848 1250 601492598 601492607
    0x1a0318030c01060608070f02070e01030b090f120405101d041508030c070503150c07151b0c02030705190b0a0302090315040b06061c0b01180305071d07080c0703 70
    0x2400c429070103600b0080f020a425502c402480c1c05241c09840b1401c10141c542010b0b600c92445026540016015a00400110700b10340011a0082c00c100141d64010f032a4070600c50608008c0c40002d149800001010041c0b4200000440065401c5151000101d00014201d071041441c01c0c0b0210700c5942c840c080e2400103845d60403680d004000850480f81c0d074074520880291150303400d100f018070900800342442c1c0c4804036800c00c0b070310408000070070524080c00c40ea15a11003100710380250f900e0b16504c86c903828503207101e074100504100c1d003525001081d8040388101464a00c43da04404e00801106c00c94450581810a2903070645848a401c81d44808600034220024001d1814245c1c1c540f142460a41c101851001881d002d24000d180d1380c60301b507540170103210310792142441c5c810000c2044100c104440c01c1540c00300001e03003414540300f141c0c00b5408049400d010a00c3e0419144d54000210410000c8900140030381e82d1010309404900d20319080c0d01c043c00340e00004041d400a0100000d0220070984103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 601495098 1250 601493848 601493857
    0x1020a02040c02070b0403031e0804080f031e040303020c06100b0901050d09080319051b18011e0302180f090112060b040207080a0806010e09070513030b01090b0a1a031803 75
    0x4441c5c1c8a6200c0b03a6a007401401980310b410b043c4c0304298a00c40d41d81c861881011071a220b60b03046401646450036500784040c59a100410107100780314030750401507a1030060702000c1d01844c0240ea0150f01d1703020601003d41804c00142c807924000e040960104111040b60003502c0064009007482501c541c020b0183c04040c2090200003040c01c280042041184c050384003d50f511107480943c01c001c281c0e6610940201081250009030024409020b01846948414030b900c142c1881894400340100060765210313032001c4000c3d103035030219030041004c2010000844807200c42e8001202c0303504000420a020450456041c0034101c86481080d850301c2c144000f81e041100003c0015000310350b1a001070400a2660b0400082c2900040c400000701e401580300700d100304824100100303501c0d526100c03008140e60310381c0301140c200b0400009450000c04580d51552003070003000c2c41030020a404034032400b008080c0c03c480e004407081c003c14000c0744050011600540341d00880180000d403001014010300c43c914000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 601496348 1250 601495098 601495109
    0xf0f020c0f0d020c0109030b0414102310210818010e010804050721020a0f06020f030a020c01030b0402071b092711010c0506010b0405091501020a02040c0207 69
    0x5a4a0011400080e034800c410805206a03001a0981d640803031301c0348040c40304180011410441800812641d100d407a8229110b1054409000a449003c40c24032000d1422501003da0300d0340d440030600221410701d520f20424800d000c045280c070084181005d003c030f0003954848000e0480001c00e504040001c55100c5030030803c0252164003c0c00d49244804400c0714040c00100807100418035940150700d07203400350754401c3c06800c4150030034980d60028810107084181101c59088004056160014650081e000d04852080d400e410110080d2030482c0c01160340490794400c02440c00001d03070200300060507a50174600403469083c0310002802a010f201409050b00c00c4c8000c0c003401d51030000215004071500070300140034903440c803620f039160300b501c08035841c2d1149044001900003c0f1906115040e400c1d05042c0940301a00c5611124640b010981040d0103240300018184071a00d415280954441c48020354607049101140000b510341d0506440240104d4030f40d0010183e5900038000c1e00701500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 601497598 1250 601496348 601496351
    0x2070215130b0d1a060405132f03010e0106020a02030316030507170d050106021c120f15080c03010b011e1e091a03040309030803040f0602071505160905040f0f 70
    0x6003e110f03c10014200182264050781d180945040d4500307102c0190340c12034000412040d14510010501c501520a10080484111102018000c15001000c2a4641c91180b04840e5101d41c1010108542703000b042e00040c080d98851064000141d600200f181c130340e00c4484460209280882c54203540301c0c06440c20082144901040c1040c2c03131300c159409000e1800030701e0828849030b6030b2424140c1c3c6400d21011000580201650340240f582c1c0110002c0410340442400001c0900300d41581004803000b4181405103074120300c02c00c10206070201300304c101c0214101d0080280318860000a040244680704002100311040f030700049007801070104d00034007042c042d000c9840808910380101902d100d1b00031407501005030010301c44884030103410b59100d1649034540a994904588598086030001001120f00c2c203210443caa000898030700160000c54030030f0f2150405404100c0c0e40c3c809a41c070003050714a20f0080d00c011110455400001d01c001c846d0300ba1000642c0040354510100604901300c00c00c080319 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 601498848 1250 601497598 601497607
    0x201051f0b0d0e0307080a17010b041421031c0218010e04140f060a09062313020a02010507080f040b01050613031b0609080d09180902030105070e09070302070215130b 73
    0x1c0300c034a00904291082e5a1150000e02040d140361201c08022b01601c03421880500007440b5441407401c148000e84002042003000c00701c04840071038038203407000050000c1e400109082105150b820070740d00113804280c1040d400c108010220030500785284a009040003945040a0b015840703d5000506c18001d0001c4000e0914111402c2c002d944c01c00c3d50340c40c0c09440b079550005a20545032103400d05403502000d0703258281d4080008900101e2650040b540c1c010038036501100c402c0d546200400382c4120b560008501071408040c0134103601d800400c04021000311f10200800240c840c1e100380e05480007140c0440e10750707450440b02e800242103a0801803081008001003605034208007a000100c035555550314408507103455481d0f45917580c5101c00c0c40441c0c0d0420080c442c1811413208000c5024100c034002445103500d80001303094030026541500400c1121060041604041031001d901040d00c0c10158075107072996010884043c0440f0b1045460703403000c903990245902110b91400208449203549840d07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 601500098 1250 601498848 601498853
    0xb0109090f0b03190c050f012c0f0604121502091003021b0102120f0603120a0c020111071518030b04051b0409080d0f06090216030201051f0b0d0e0307 66
    0x412444499512a200f50340c45140d0302021980c1d040c09840e480f12209158a1600301806011030850310030340d050004489855005c20721010729050364a40056003240f42706500c9041c009158405c12400f4000c910810080c4070203251000000384c0c0940c08070006148400d41040c070b41c001d0040035200c03540501e4552000324410391540261000341d420310036411403895039401035400c0f0301c140c00011041c0080b40000071010003c0703160305944480e0107029548126a400c1044000c0d5004c203000802103103040803903c065581c020303604001074050030014403040303050a6000106c01c1e4255001c208100c0100006ca440344180d40781d010086a000c04036015030b0610b032600603180c0000046040c031500800314055400c0c50540a0040516088103c2030f00c0c001040d45c1c01e00140180c002e080e405552201c0d0001008405803004084868204151550702200c3e0f160090a4660142000c28121040100020000c00e100c1c4c0c0740d000c850515000d1950344030450800c401400001c000e00b1011f000200e0300f9001d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 601501348 1250 601500098 601500101
    0x6020a06060504060e0c0304030e0d0b0106081305070b0a020f06010801090b0a050403051b0a0f0b09012003070f0c05030409151d1602120409090c06050307120b0109090f 74
    0x205a11621050098540364001d10080350494412082012100008541502d2081c801160000d0191509503500741402011810003100c44c18121440c07440203004116040e449004950000155000308660045075140c055881020340600e901c0d4640000c1c8644125000304424281d041c8410207031080c079039540700c0f614001d0025030307826510010442c00141c800360b401c1c85501e21540d4543c5401d4203041125401e00380500b00060000c05911800440402050f0b40c8000c000625100702d8100303c951900e02c0340b107400d54207120142c004000c103003d6554803000c2c1c60f50589074400141c4c5844905400c8584007200c00000039800074116000004012590000a0b0014941002c085192800705641d030ba62503202100180020404402e10f44049004800c0705800604a0b030540d1044640c0c2101400861001d5401544620505580c8254000401c9107612031200205000d0822078114900000080c1404480004000d00c299842030011101d80c052900070001e070641c50400c00036000d00001490 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 601502598 1250 601501348 601501363
    0x70915060f020d0504060509010527191d09032115010f050717130815010608010807060c0510020301150806040b060f0708070203032a0a0b011e0b040602 67
    0x1400658801c001c12400c034000500800e8030300305503607880c0c03806141000c102c0c0c141d0002072425042043c1041481321348882c0580c0013001e034405255440c0e2000c000410426000b584203581b41000d03a0210b010000381050240c0003510b046016000030345a42c820041b64118400c022010304510440b140079032030344040c043c03190b204148000b40c1c403404034540001500c14030b20400e1845e000600c100628000201c903e980c0529400c0754888250801c0701400c3c81107214041504466125480f5542124100c0640c442d00d034018101418000800d50400c04826101c1c4030b64003810040c072415a1107e001c100d01007040107814400c0200c1151203584075172111516580c0110321320002008000450030314a000d2017420505200241290b02d008160710000d401a000468261030315401405000c01684061008124080d0302c0021100390101c403510040749a007602c03906040c264840482240011489101d2a0540b0144130611101c4000c0100e10900841c641c0c1106812500210b00090755540018000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 601503848 1250 601502598 601502609
    0x1030506040b0106080408040519150f09090603020f010c15050414240114150403030e030f0a030804020f04150618090203100302040510030f15110715050603070915 72
    0x5030b51642c2c1c070442240c203040c09490181007420208001c101c14075000c0281140c04a0600d003280400342d544d090f00101c52800401040424a00010001c415601000f000081c4c00243c104006082c1180c022400001c0180c841078144840003c904040c84a105452a10031940300c109104514161404805079481d41e60148828030030301c1041d91403225040c0100c020383c088007180c48040da10700907807030781460200035006820100031100c0441000801000304041c600940310000403070740f80c6052501c0c24000110700503080c1c01030b407012000691700514079504a501211000c01d01010000050000e10480c0600610384481400002d8055001004600fa101500502a802c19510b8a00741d0a9110440c0d803c062040030f40420b000624203540a66004601540c2100b243e945a0391481c0c3c19008128041c1c82c500301402802140c0401409401c413050340005006060140d070380c3d11007415211841c81002ca1030b03114000641d0b180c0f020484580281502c03117003446031150b610f101ca00074407294040c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 601505098 1250 601503848 601503863
    0x1215060e030102030403021236031207050d05030c0c010504050604020103180b06040903051201080f0616051804020f071103010608070b0301031b170f0d08010503150c0c060103050604 80
    0x3280064074040c8281e9100d1a00358016109180203114540310790361203000b21034090700b8802002c0151644a079402041029010000c5005522240400d844d00b46080d8251804c414100300c0c1000262000c00c0b0100c2040d0030703051040d26610b6415140a10b4018070f40821300640c0ba00341044140030001403075a001307a000ba2410428102a1040101c1138001c203103000d84502c1e120300124580f400c2980c0044030880c0245061400c10340b071040000b4102c042a840398600f940451044a8410300c103124003070304441600700d00710b200d0141e088080d02d18006d0b0f01c1901e1424048103040c00d010703242c1f03030122003d04000c0030081d580c6005600c0e120041841d1081400e005e507103003070300209440200040c45402d80d80d42c0d00c40e0b641940c0ca5660754402c1d00302807084080c01c202d88080c000030040517080300072085400d00c00280c10018100c0d94903d1034511202c942000b017040d00c100400c0303643c9011501700c01000a101c0469410780c0d6065030b4240758481e000304500c5a00c580400001440404202e030781c040d6214001c6c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 601506348 1250 601505098 601505117
    0x2030721110c0f01050c010f0501080604030906051326030310230d120e060d0614011404050103020a0201060506040305010203010f0803091c03120e01021c1a040b01121506 75
    0x800340d42e820325503001030300f00c95072032030800c029030103900a0801c00850000101e0b10b03024102e0503809540c400e030710044441e400031062001701600240d403080542018501a4149116040c9820302c00a141c46030b04103900c5102822a40b006c0542d10303801b103140e02e41c0c00710303581da041001e102131800302184260141d40f2200d500c000398589500315550040d6400070804c05188909454401882504019203000d20180d04807860a60712034001901ca484d00c5410002100c5180c900780101a00404c85840e0421880d44c150031020200101610103071482840c0050b1104130404e0300b680101055004207902c158045000020800150010341c140c42000b2030381e0030781c981d441c65010ba0340d00641040c0b0350702003e45a0b0305039035211141d42d0340f10304500a11300b020900c1d952842c004200ca0b054107091000b6500050f0400d5045ca030f403d0300c180d42c807000020070001808407954500010030034141142c0b0172034039001c1e00000b0740e1264a411064080d184d60421501681551401060202e48900d00100c0d44920 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 601507598 1250 601506348 601506377
    0x60f090a0c33092c1b040f180e0607230405030106170114010303050403020d080904240602030705061b0c0f01230105100c020316031b090c021b0102030721 68
    0x840909501c4e80d102089a40d2606211081c1015444032020115141071100050f02e02d40103003c900140039449914140085100c100d4040c0c03a854495003845510500c1403091083c2e0003a101d4440d42115080456038100040c0544800d104a5101a90540c202000482e840c0314920307030401002da880000b0442d141c241d85100b24000401d21000e400316009220400250800c1003981003014460304440f41740c1100000000c0407650b19941c540d0351019144da40f840106400011071025204500041d801e22901b076462030b07501c60300140507000c822803004000d4400c09045042d10981e038210005c1c0c80000004d81c00f500d00030b101c0f004100440074401c02108203c1b03200943c90700d06075000074019141d46c075070754181a146160300090481c2c02d403040c0040210b500e00c100311910041d600c1020034900c56601e0241000c00012250020700d50586040c500184440c0c00044160040503072050305d51030760b0719140042c1d0441c0a59480030703041100550f094500308a0040580720036000e5500ca081d005480381 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 601508848 1250 601507598 601507649
    0x70909090308060316061215030b010306050405010c08061005070c08030c0f0d0e0f0f01090302040204120c08010c02070510020c180708070e060306010e040603060c02060f090a0c3309 80
    0x900c220401f0604e4814a140090440d401022801000b00d5285419558030f50318000c100e002640240c400070340d00c3d418401007040038018410403c200385001741041c1085400145000d00c0d4880074030610400144040400140a80080c01030580c170f02600d450b41d0403400c0150702c0e4101d207480030320b050055076154605c42d4011011500d44481c00b80010348800c899209000c01d42045058072414002400e00010040c2c2e1240010006016441a00111026989080703100c10f03203d90031440d032607410800b220790340039400100d11044030070031030341a05001c8411000380d003441400003401d504500018000c0803290b03d00c1101600400d915502e1941541e1504822103a05c01000300480e0f11001c20408501c0303a610664502d902c20b0002000003620300d82e00d9440c0c10448902400070009178000c0d038108144040a89002c0340c0c418400b4000e0b18100c2016a2004c0a1a00a0003091440350107800509400c0d134101c4074414908a44c0301d01400313205050180600020358905c24096400b0320b80500b9075121804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 601510098 1250 601508848 601508893
    0x206070906080405030c0d0f020c0609061e0d02031302011d030703080a02030f040801050f07090305121812060f0105010c051f1e0605011403040f02090709090903080603 74
    0x9954425050341032420840340303042c01070070584041c881445480b0504200703000791a207802060319012446003200b0406414032884042e074a11403002841030b104103446c0c4008644000156034000003001c050520303010301e036004403402c1c002c0c40ca10200800903070540c20020764802c10300036217483c904010b40042404094116444039901600082c00800c00201d00070090421038405005980c1031660103c0c4421054029034444003440e9114030a002c03406441c00c0304560420032600d4100801401d40c0c81d010303514800c40c90740416104002030b41c80b00d100502c240d4010304100003061b8442034a00303000d41d41d81e1030030182e0789030580c8500c00b00001080d60044100d50340c8958408007804c408224007030304580c20000b1580e08500e49890710890300a140090224041c010540d503000901070b8103004c0010403640031402ca01e10103a404009000200350505011000075504031810b03241641d070f861089903103001c1070388148551404d0040c03071420180c0210003103200e07140c2030381140e818400407200b030340a0508 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 601511348 1250 601510098 601510111
    0xa110c120a0f02010e12100614011e03181505010b03070e0d081303080301090c0201150b03040311070b04080f03092b0506071115070e04150b160201020d0206 69
    0x3006001c900041e041c1081c099000340141000082110f0050200e000500520990300d001e80004031050100c2a070351040d10040e00748907084105d001c50074000030340301c17651410b10700240341003400036180010300c650040440403020304c04800984855280500c2e59401c02d50f1480607003070401c0004598021031409482c071408940d0341e2400030003400024001c0400801d18180c60000c42085050404e4140352990b00c01180300b0030020ba5250f00d001903103c01c031840980c0e160116410015041d035000c040440700d034140c5003207a01d050341c0d80c0c4075450305549280d8540ca0f80c040a004c4c1e00e2000903610840c03006442155030300003c1d1043d280d804412141c0701c1c49620549a44034080d00e00b1054440541041d543d40354001ca05901c0b103074204c3c0d407a20f03890310740304541205c001445c00c4011405400d09015030700801c036903c036044100d8280303a000a0400009a028940200d0b0381d100700d010169031b01c04001d401886080c4402d80d0303d02d02d0702c40c0101c0c2c002164000340c2c0984a41600d040d065880001e03041e11542 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 601512598 1250 601511348 601511353
    0x3060b010f17130204061a120907050105030f0a1d011b0e060417121611100806060f0f12061f020604080a260115050a080a0906110a110c12 61
    0x2502c80f03ca41c036440e00084010780e0095034450700410310410010941c144221040003242e220300301e180c008580d504000304003510320307040f0950810080c0d8009081e260001e450124071241d598500e2507800003020361030450340c3c504001010210f1250019404003c08083c5c0b0801c04041c0c0c10402c07001c1c0e40401c40ca10178544c200034104020000070300032010360b0441840b0002a5407101d40c40030104240380d04007a20400e0b5116a1029240800190051441c92003e003510250110540518080d01411008240a010f110b00041c4039128000d40d030300f02c441d80350740100c2403a11202d80ca4442c2c449a041103500034055000300e40d4606120a5800354105805040d5006107015691a40d4003851034025505140602507081c005010065419003400151241003071042c83c150701d0f02c408105044c10b021025424400308202c01c0100d50fa01c032174030780d0b804030b0352400c080351055892811000a0600c1d11004182d4000418081c0b074040d484081c40d20401800822941040140410020106807500c041d4056a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 601513848 1250 601512598 601512601
    0x20708010606120b0402161a0a110901030c020309030d021b010306030c090b131d0105160e12070306020c0304180c050703110c030102040801020c011503030f050d060801020403060b010f17 82
    0x5802540000c81d07040710107003000d0304281e0600a000c08000d605541107601c2300c031080e004105480301090840c0d01815082050009400350b91940c4880d2142010150416031a6410928224000c100304c0344815806000c55607024a01003009483da60385c250b64000b1400c60002c208013640c440d0088809a030380110001050914002107803000b00801050745800900805503210060028803488000c5460398403a00e5406040314400c908590000700b00a06d590b107241190030780240c2c0300039420760304c1001707640d41c0710f8600310000240e1401d0690340c0002c1070749000064203860a4400300141c01250214503055266215006050040d100070010480010b1000d010500101744200410f1603a9250035080d60368608035100420709990240d041407110341e40004003500540024400c405000c0040c0c0020703c1d4150840d600200480d40194590701002404904c26100502580c007110042c100c510086591f180d4074034129016080d00c1c00340901241002c0c0d05040ea0a00071190304204102003014284103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 601515098 1250 601513848 601513877
    0x7030e0307062c030a030e03010b09090c0d081213050f03040e07120e0f010b120102091f180608070f1803020411120a050610020a050a06020304110d03030c020708010606 74
    0x3020030004203448580c10034680e80f80907440601c03920025500030b50720050364002c0001410b0039603041c82c0089003d0344c4164104000e030744001c600b2240d01101181c40c850315001504104905001d5084086e014031442c000b03111104d48403422502c4481e10903016035802030030100c030581d2680120300c0341034400d8500100149607203200c0e0203100c58982c800030001940300c440d4140585001c0898145400c143e541e09214416850030690452509005000030341c03521024034040fa54005d200c400c0c2c1a01c1003003810b1884a946d00500150008000d06986410403903071311100200310203025501c180125146142100002c0e10903a840040d4003500035030744030300300d00d181d0a02004088000c1c0d0b54100040500030400a01c0d00a500d40d409440c1641c008116420890108086504650f411005540c0007948540c00a031001c90ba1080058000c4401a1255124146155018400006241d0081c00c40d90014105505a4002c0912070400d600725904683c0700c00095003224071902802c07010481c480d581411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 601516348 1250 601515098 601515137
    0x2120c2107081501050409020304060506011218080a0c080d0c0305060a060230040806041403030609220f03080906160e0904170f0a0e040b0a1502150c07030e030706 72
    0x5032032045c903006113030a6460040c0030407078100381d4044a840381c5a6040c0041903a1140f8034010100b41ea500410100007221010403210fa41042e00401002e000b103004203545001c0d070305106040c2e80080c5001da488030841c504030001c260f0f034880030001c241b404010501d542801030b10f581c1901c0c0143c004140381a001c01c841000da805100007081c01b411032550108081c075001c030181c802000c810740205810f050a00c0c001050000026102c3c600740c0c402e004000003a40c69080301600003031840d4428882c80c0084c0030602c5106941d00002e44125000082c106c101640040202c0c49100c581066400d181c4440c030103519003031525900d410000e420705490021900c2c21424850b002445030118071076a5604444150b1240c220106050960300d011800320f0007075800c04040034240342c003250108403030540800051200d8000380034074000f60081840000401e802006052240d941901c403400c40c03032902c2d03c191305040d8800002140040c50040c040b410900b800075000d000d40d460358560b0901c51308807140340c28 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 601517598 1250 601516348 601516381
    0x150f0c03040b06010815281d011203050c03161506060f0311120103050a14010212070c080d060b031602010204080a0b061f080411031f050a02120c210708 67
    0x2418145a11485565a5560480626240c7c0d03602e901044c0b203140d4512a040c4141d036500c0b50219091305542c9111901074202c003e0b0640307424141040480c481820110360a0280c085016007a2000041c0a030582d082c40840058880c49401c03040e2480403103501440079202103110710008911202092001c580c000e03045819601c82004078542090766445180d12140b00a03401074406400c800c8440052119030745a0300700c0f446c0c1440082d8944030a4070340030320300306900070300d5072082001603c03c0004000c4101d0403034500032083c41080c0000d039118880c188066000342e03088081d032030010303107511441801802603404490540d005801d0540141e2070710b80d980c00b002040c05500000038001c081c0709158902032045100d080b6929480c0c245400d1070282c0c068100903404902c25409074038280386510a0741220000580b01c080c0108650b200d03601154060b008034114203402c00320701800c11920f4068407026040e6070760403000070311030b081040000001c0010140d40c4800007400a100042391107542c0035441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 601518848 1250 601517598 601517611
    0xa0b0616060f09020a0906080f0f06011404091b05010f1404170703020909010b0a0603060b072006041e1a030c070804050621060a06022d150f0c03040b060108 69
    0xf1958141c1d40c0d000440c25501e030303000620303401d90b00d007800c1c425540b040050302c0302d0341c0034940108882e02038040e86c0c3d60f03030b80e40512034640000c880e000912442d4546400640f045640444403451100380d50150020281c02c03405014001200883c200d42600e1050300520030022081065600d8142001004450722403076002808841c840e503440080140c40b0805030320f101c2c100540c0000303050751081c000c0004100d400c1d030040c010541040c8040c0701101c40c0604483c170341580a048100c0040b034007400080f040707200078111030b4064400f140000302d82e10b20708980c3c2129000e14407203440302a04c500144d000d42006100c0195001c0303050002403c44030300d65000301502d0340160300b05800d00b641c0d080058100d82c003060080c0c8000c2408a141040c500062a0540d00003108550b1440b40b5814000020b40e181d0707100003807044100c1c040c00e0f040001007140c5070f2015220f406d02c00303840401c842c0340617030100040c1c183c4403a150703c21014000f03030000d9480402c0d00d002e10740c049019256902c0c0d0710011603c004018026 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 601520098 1250 601518848 601518851
    0x60111012c0705031603061b080f071707110f1209100c020303180f0d02150d060b030c03191b142101090f05063001140a0b0616060f 58
    0x842d19584c1000800d9500c00f070041707614201c9017189031580c19210181d002003200c0c40c01440240400da0440e80440c3c4c4a03a000000e000306548401084030080440514808001610024441250707800310030398001e545c50108968944001e0802c0a0751510faa04007492030320402e004900d02d51a0034240d61810700d030249010b2020bc225a00028150307800302c8001480d404400c20031000f5070402182c00400c1c0300f01203610103c0c41c0029000f14008404802d0404d4241c18005816131182d00f25a1004010300030070300c9aa5144d00d01080f4030b90b800da009803481010f80070b00140180031007415000d64040021140703802220003000343c0065901d036140840c250001102405110000c003410300d881c80c410720135800603091030b500d4003105000320303009129918007081c10101000001d44880484503018980c01800540c0c0d0910701503024241c0610107800c100d035500304441d0a00071180c103500079000c3c0040003002c20008041504200c517a01c078800201400c05034201d41800414495480f94a4221002c01d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 601521348 1250 601520098 601520113
    0x916031e020a030c1b020613150c0309060f0e011103070c0b09010e0306010f15050c01020d060906051c0209060303090907030605030c0d030f0e0a090c08090105060d0507031202011112060111012c 85
    0x8800c030b44c00c0b14402742c020005e40848d031554185507100003040d000f40712034104942e41503c00030f0001d0030a0400c1c4c001c1c41c18001003540d01020207804000711000c8903000203054000c19110b0b490000305034000c00360240007801a56038860f061802203981412580c41c1c9000000d880e00d042d6a2043c9042c1030b18400c07051004c00e110804202c05c0a0008142d07107210707000009030090510484070308950498200038020344403005000c00e03048010f5486400550116008039031641c560340020b1540c1f244043d0035420525a10030300100303030b8050f08400113030f910880507035414006c42400c3c0f10700d030f0f015605c0180029562100a44100340241c1206560100c00341c0080c0f42c46842d11150000d44410340703000c00014100108104031b19000780b15040d040042152055840d201d0740c3c54030342c0d0704d81980c0000b4007003c1c40180e522078254000d40c024008503c42c4040130391a6000041c501054070000c540071404030b0f1903c4002c2400e030708188201c4801302014110100d1f1005005000c5408034444c041580c1d0740d121301ca1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 601522598 1250 601521348 601521359
    0x3030d09050a060e0d09080304060905040b030f15100b0f09010c050c0316060e060304050703020915090103060b090a0b100311070203030c0c010f020c0916031e020a030c1b020613 78
    0x25000e04c90285030041284c02d142400c02424040d0310340c01080c05400600040c483c43d64084400e0b000c0b20b8040b200420b90152103000a802c00800f806142c40c5881802da002080038203130b14115106144403003404014607918085036002e886034020885800c1c0341001403101c03541c021a610104540280100e80e8142e4100c3c0100f894a400b0400321300342180c00080421500e58450075010a400b011f0b610389040d07040c20f80d50166644070b203000003441403c0101c00610041520040185101c1c00100b00850950396414410014144041103d00034a05100054109481c5014000d04214040e12550300c03c9010710046000b01a501740424040f40e02300403032005070341c0c20006096007034502805002d01e25450400548a122520b45203400d540000020010664810038400e03407128221000304140150036000310300402c400c8100c5400450314003040d6240c1446a40a851002100c0e1820080e000503400d060756101c982449035121403160595020050a014014040b40b00038170015001050319003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 601523848 1250 601522598 601522601
    0xc010905060103110f0d0c0b030403021006090b040b040218060a2606030f071211010c02030d0c0c0b070809040b1807030e0d08041104110c030c0a06061403030d09050a06 74
    0x80c0e03c1902d00c4240b1302c100c0d00c030340d01d440144203d410000326150328005140d40d0b01e110080241d40304d480b44114000c000501410300a1084048034007055900700300c000d85818440d4018007542e00210700880ca0301c0c2c0382d90110b0138507100311200b5040140c451110380051804101403944940c80940c1008105003101e41450b04400c0a200948400741e4005c00a213040c0e420300d41362525025000c000e07903120201c2000140040994510300c550040b14404030300c040200140c42c0c46024600003900340c42004491648950f120303200b46456442000b0b9140c01036075500901500703009450010b014444200b1401c41c041c54141c2c80040300f05005850803c40e403e001380e8400301d000b8110340440120383c440031020802813052008220101c074600384003640c0d0a0070b40b107051050310f0328403c1d86e0090396140100c1c81010518002c0d80c20b00c0e0300c803904599075142c140d041c4c03035114245440304440302c0f07003400400700f400688010b01a003401e10140c01141007901c11180c91001e00700014040c1c5081c042c0074544400714109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 601525098 1250 601523848 601523851
    0xb090402042a03050f0a02040303050a05090a0b032401020601060e040506031002210c03070c02120c04061719210905090103060b0111070503070b07021f1119020f060c01090506 77
    0x43c1c80018251a09007065000760b00b00900000080744104024070000c3d4129050b1903070200d140c0b85c903648401140300414070350085600300c990b12010101c20040c220200070414490035010307480d412082c6956900580c1d445500f03002d10404140b81c09107074005403c05901c015401103000341155032008000303562a00320791041c000f503a00d100369521003414210b005000a82c20144000711103246280c0307100020102440080020f1095900d0300080d081034104000a4809180051003040314681e2140c01c1c0c9900441d0441c03204050054010101641040f9420a044260011822074508206030415184c07510444485000d002d4480404603460b150700d94624042d500c00c070000a029800b00001401060300d100b4000200da110800034082910040307040c50031501680d8005840b008030344009a210764490104c00015840584e40746100c2da800403601001030070600a5404200f540c4001d113074088000303000039400459030307104079029052610081c8010070360780d400050444415540c1d2400d0480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 601526348 1250 601525098 601525181
    0x50c100f2601060c030f170408090f0405240102160920040f0f050f0d060b0310240b040f060f0309020d0309030605010f050d080903030702090f04150b09040204 70
    0x10b0300c030b4070703005c041c0c00040e2003849000e50b0411400030040d400003c1c1007200010b200514811012450a182307460700750a6411041e8000d0081c4154900010205080c181d10200c50700d90246031031160301a94000f00c2d6040140741540200803200381000003080241c48562294070680c6110f10600700b15162040180000c0c0901c0c014551a07a880c214050041042c00c0c0c0000744100701401d1320302000c1c0d072641c0900548950261011861840354000a418003140449400c000c0f81031000c100c006240c031620f90000c2410111410600a032503240c820070310300550107004410f4903465030604c10a0b0041d1201d0040b1340f801c0c80c01090b0640250f0102d20705a0781c603002100450032003081441000785901a10303015150150881d4241454039000910030100b440010b0114040083c081207180c0f4240222280150050040142801c11521143c074403001180e058075114420800d0300071101890041000c0703110000c001201a40781c81c3c01300801403004a10811107030005c0e036260440e040951040c00318015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 601527598 1250 601526348 601526357
    0x705120f0307021b1f1b0b16030b06040608090a02060403060b03070b18040b040f05010609090507180e0a0e0105130203010e0c010c0b0c09040216050c100f260106 71
    0x5000320064901003051030f440418034076a06080c4010346684d41000244244c981d0750b017000700350b44001a1680140c4415004201c10001800011322071030301030304c0340500c001d05e42207458045655402c90813642200c10440c0c3c05042088104401031041c0ca07140d0f00004990143e812000880c0e0018071103610030b51084540d030b6140e1261042e10302d001e1000000a0140000c418a0480091000d03411000c0e82c044103441a640c490203035017261a15489000441e62a010400141d40c503002c020388480c52512400203600c2c1401c0002e042c6078030070500e1204101c0d90b00c040c52003548c203006040891500082003402540c0e030f211000c4074510001d00402d809982c05080c641d031a030905006050a440003150003d09561281c501d407006660700400d04100075400442c3d400c1c0c162181002d1800500c1207010450740b260001c00d4048095108412249000b88281d0403155003103810424440d072450350025001c085040f2040f07003c05a4000c82402d100141400c140790b0800c0ba0000801d610004283c00240024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 601528848 1250 601527598 601527601
    0x151509151718060420220e101409061f0b0304060f09030810051905060304050307050f011a030c0109031104061e050306100f05040c090305061509070c02010210020705120f03 76
    0x2d10f00320909000c54002661680381002910000136980e000404869220365555001f4224840050228111704481c1d16014807103402c4400d40800840380c21780700003019001e4032000c5034480c41c2c80c2c40c400001100ca101511842e030300d012074a00392600010425a49a41c440404c0c2188640e1481003a403010303c681c40d01e0015040443c400540500d15800460240304406115451310781c803800e00300120741d401c60f1340654903070320340c64207a0840c054598010010f00c1085000d03080030b4019040075408180e01c010b02221f041a50701003503942c216038150382e400701d6500d0a09201281c1540c41d1040004000b81c4042006075692040b180030303144980b03d0b03e01940442805214514050050541003100e11010070385c580d0803c1107840c3c80482501c1120310903a03848035010905030080c5496002160404182c3d03a9614120011700c0925001d51219880341c03203c68001800e2502030031031401d030a1303010b9000703180011074141154020750211000740c1c0c4c681b08551310b1402c01101d1f50010130701c40f81d000d03002a44a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 601530098 1250 601528848 601528883
    0xf06050103050c0f1c0c0b0703050406020c0d24021b0307060506060a140a0c0804080a051015030b0a09170c10110304020d061515091517180604 63
    0x1811007010a10b4131458513652074030b00954900d044886684442100b400d102c50301894081541d080c1540b000c001e0f00004680c1c4024540c00c007000d04100c078229002c1d2521851020200110b040d04448001d21150ba00c03802044403440f038015004151010703400062403c4000304120104214902e00681c556000144030700411413580581c1d07070000010759034031342410b042030400340c900c0d10844c05002c481c54022a60083d101d114140da18052908070803003543d102d4962004a845882d412002d41d414402d014000310030b0000c81c070034118440e00900600022500319524240640c2010f01603100c480c7c1c4460103080840c40a4007441014981c600c0c2c1e46a03500040b030085410070f100940344d00843c9162844e56180d40e840700702107a030301a9040308c03800b901c03040a16040340140751441c126880e001d10040c0114034940c4100c040400c6256542791170000a07034420380390541c1d41084c00c1050024001c1a03e0400e4001c159450b00d4001031100c500d00105c40c2e00400c01c03460b0a5041320155030100c200e01c0c40c00380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 601531348 1250 601530098 601530103
    0x213180c02150405030f18131d07060e010302091210060501080a0b0109060c02060d0e0f1501050607080a020307051f05180d120b030601090c0e03071208090a030f0605010305 76
    0x5801c164400c0e404083d281c50b464035600c0340aa0030001040707072000900103145103103050114030003a070f0040540c0e202c4020684440c00030510000411142840c9010101c0080c1d400503226045510980c0e4026512607810011006900244440c1c0c1d00a0b01d0117152000603a400c3c8110401c5490b1180c00085007454440010303c00c01d4080c009030202ca20b0500c01100e980d070701103001d6080e82c003d030520102058161000c100d46d44501020301210381d01c5d10059500c0424081800070000144a0031180012071070a042c0e00038a001303105195000300c0c1040300400180c400800380c031441003180141d81c00e0a105481e80313401c6c400b40316800080c1101c10340703e102030462a84103994021049540312031861406103101640c4048441d10f01c418801811a070702c0701c0c0361b10390700200604800076040e40c031a96035850a4001508070030010401149545c00a82c2d5642000103ca0b4225030780054074000440883d00c030342000c1d80c003008110317070800c021007000301c04596180746120150b445a0400240b640c5103040250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 601532598 1250 601531348 601531363
    0x1207170d0305070f0801060c0309180507030c020d0206040b041b1206061505090909070503030c0a020f0d150c0201021e090a0905060d2301110301060e1c03030213180c02 74
    0x10303c4000400130034007a61004503603040d200d260400082d03d408900b0181c80034841039000d281007500705842c034024500c2c1c1e40c1256001d04a2501c042c88802a02041030f80c85100e072400d01c40059000c00300040201e09810301580d00a40604980942161021407052160001d504400700c0804000e00042c10030045200310070042c2490586207507540112100140b0178402c46820380d01c15285000800c13880c00c0700380603000081a00400f120390700c0d94065004c0361101c05201c0d0a0744260180c084c521010f040c4000041d01d0a0b61201c0703400d20090425003488001c014546c581021992300780224000d4111607042ca2140c1c407407114401e500c0300600e000300000c441c0c403500035504081c02d00e0b041c000983c440114000041380d010f04084070101510200244248890084204640c20512026001600c460045050310b185a6550540c048610300b0712a01038440548041d1718000c3d20306042c00b10b48241c0c0905800190306083c0c0f0b604c6a603404150262800c0800084451a540d80e0710074030042c1c0421064 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 601533848 1250 601532598 601532611
    0x8090d0516020a2c24040b0a0603150b0f04060f050c06040c0323060c0a0e04050a1e0e0319031506080108070504150303080601091a0304021302181207170d0305 70
    0x110a98500085081c1400080540254241d604a5951141740e42c40c3c0e00010603428004c0c1880c1c141310381e81c84000340513000000b5100d0600035040b00200d24010400c0460742c3e900c20040d1040d10f07180c0b8190742201e8681c9041d00c0641008014005008407550034407840e030103280524164007045d0b0460800b0602070740d041904218141c0c120710510b010030800310b203066010703140181d0143c4030b0707000300c0081d240c8030002c25500b80c1c8146071204014009056621540040000b09a810071a032100d0f5080c00441e0b40078000b6418aa106115840c84080200c01c4031041046034600840d0703411514220902054107908018080303042040107026040040002d03200520048a0500c14a0030b21b529080280c4000d0002804100340800002c01d586d000381003900082c9540c4681400c410509100b15132a60400d4900303e10801d00005442d000d9103880c02950248044160b01081c00030401082143c0072150b04040e007082e000e800400900707400701d9400306881281c068081e110914400710001c0403240e000340303403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 601535098 1250 601533848 601533929
    0x703080307081e070f05040906090204090b060703050f03040816052514040203070504080f0d0219021f020106082a011715010203040b04060e010f08090d0516020a 71
    0x418a11070451468036130446668100b9043e1803800d81c0b0100d505214036081030610134240701c4002040082c0d03030b00410480f401d03c002001960181d1381003207498410707440c01600091040c0b1001d0304030f50340d0400441d0014466040c4600e0200d0a0b00f420510f6540c0c1c07142510203802c0b08440c5102c100c1a00b80e19545039421250164881e420449110308046040d1182070142d540400002c109500960031030b400f4059034000c07030340c540c6542c01c005641c8428584c0424018090040b030702e050f080c80f05180303400c4070394020701d40c0000715996415603010000e00035100046649a0a001480c910305004401034845004154400b042d01c400e41c240c0381801a81440303040040c6c99601d01e0303e041c011807800c2e80141321480707123035562080c62004030324600950700b007158081c4d0001800201c880d0003d004607001c0c031007a200e2002441c50f100e401d80340709004480049003604444d045202c103a1041c4d008003091011021400c55800c0a074020514151158119003071a000402c07010741c4030020341c40034034200c00b13800c3c0e032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 601536348 1250 601535098 601535131
    0x5070b0907150809010e0f0307050f0c0d06020702040935070209180a08030f0108060703110d110f0c150906150d111909060803071e14070308030708 65
    0x10300310307210090ba21000204204400807912014081d003100d10702012202c1100c00b00c8000c2c20749180c03244d02501c1d040300c03a48a4031003001c0c9040d10200d220704c030140009154100c401801c0c1c403644040d6000343c800b241d003d90340e81c20410005500d1800010f54840002400c03242a513103c1200820482000d0000c104210610204005036600c0324055404040c001c0071a0300010a06001850b044803048000e104082c00700c1042940d16107030b0744d024100d0ba100350484202d511144000d4040341e010340350034045880104000040d102a542104c0e07001c07240d020b0414034203c3c0d154803407a15904940d0a0144507006881d40444074107860b800990841840c401400b04d40c24441101000c0c0003801201a0099211010038801e002540705442119003001d84106031010400601120650241c014001c0c0d2525024005c16040c01c00002d0b212203a9111005523a50014800c0b00703180041200005c8038100d075a00042400d80c54203100282c02184520800d94603424089000380c280c078002411003101086214 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 601537598 1250 601536348 601536359
    0x61409060718210c03120201020706180b0f070e03060112030207060f08220813090516050318070f09090c09050606091224040b0a020703021b0105091005070b0907 71
    0x303a0b585044126055891103001c1e03440c240d644c8070015030018104e804d51480c07099140d901074008008280c82840100003c181d02e130b180c43c06c4c8030340d90325010b46007068150014100d007681c1407010b90480315500b00003140c103c00c03c0029180c840240c00083d0f030280f0401c0c403c07040640412100c0080e08440c00e02d95900c107840840240042c000901e442c032880c2e5103a58501e555803030340c0ea41003415600414010b80d80c8000340800400004284200804107181000041d01c40401e4480341d400c150f40f6035141451502c40c90084107030000c141803170180d030380165800000e11502c1d40c14003c0003072101d200041050a15420704040c00c4403a50f20661166041404000b459540c0b0000c840b040f450440f4001c14818070301100c6482d180e500507100901c450003810109a4524200110b48540e12500000d10f07190303908400041071340201d02005002d0707800740d40c3d0405c84401c214002c40198006142c003a007400c0304080001d450050030524903010a0000030b00d4410300040106d203590102041c1c0041071802e1400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 601538848 1250 601537598 601537619
    0x30a0c17061603090609020d03080402030f0105070c0b040c17070306050a0204051302132c010b070201052a0601141f020606061803010e010e160f050904061409060718 73
    0x20b050384000c00d0341d0303101c2803c1000200c0c0c0c00201413070340103480f0010390500c0e03140c00780c1041e4090b24282e10910403884011900c2c07205000d103503c01c0c034450b034400007030805c1c0f9a00c1c01004040900100e801d81e40003178002c600e40040200342410314a090004080381851402c00c00b085030310181203800d0b810300401c81448142c40703007698213110308250400142d0f1840d2010b0901881202c80c1c00403008401c0d80d042c44a400d2080000036109983c419001d460941d0fa21103502e1003911035002c0080c081030703080c0803051001400020700490542c1c10407080c070000411611a905007070090b000140000d90000a6901d00e06041d003c054140705444800c980d08020290b01039076a4900502d81841100d0000d900032000c41d5019180982c8000500240085002c07450103602804200d02c14403464480ca000d0241120074a20500d4101d451044800c0d000c81c0c188400d2000300200144255200341d00c2b4040b03c40f03414503140b0050b01c64000b01020b0030b09802c0410006240c10149641d80701d034010345400c14400340504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 601540098 1250 601538848 601538881
    0x1b0801050a050904050c0405040602091008040209040609020303070b040f030914150a02010603080d06060e011704060207021c0c080f031e0a1b08071109010e1302030c030a0c1706 78
    0xf21603407841503403985000c51900b6058a007040e080f80c1054284001c000d0203030050004171400b1030340c502c01c1c8041c00100311600002241c003c0d510084c020b0104011401a42c030011400e80007030240c9103030511586540c00b207044140e07001c661018502c810001410f5105203107102900302801c8081102c00910001049007401001d102001c8400107024150b05000f54410001140c1c8844019140d404d40d103403c070001d04c014420f80740481d5510001c0449584030b502124801d41614881441640340c41c0c9481d0000c1d0031044040360041c00440c0e05000c00c25600c1c040000c090f1148841c03610240c1004405420b1010120142510358000d114151000302c2c42c45841c80b207030101b03204454503441c103030780103c2d095a02204100c80c0c030007a030841c950922404070010031080740580d100d1307030b108040c1c0b009001001c402480303111403000700100803034a07083c103c030800d411032400141103d00c4600640006803c09a00f14130072500d03582201d10400800500100400c0a44044c80c068400303480c0c41c0c10102800f451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 601541348 1250 601540098 601540109
    0x30203040b0604240803190903030212070c0e13050c040c022e0203010807140109030c050103050a0b0915012606060c010603080d09110307030503180310020d1b0801050a 74
    0x80384c41d0705010106960218003162000941c0242403503503035140e115101d600c07183e032000180c5200c0f00c181c0c2c05140585003200890b40d03d40d000788248041081001d120790030500d41242c032913600c0c540010300c010300461198000c403105040d503103012100c3e14145182802d2110310f2802641401030580e41d242d0003003845083c2c004046510440152600c0a0210800310407103184000743c408400800c414000065800a899405007130403161030051006583c00031042c400100400450300090204c0e51194200d140c00c0540981c010402011200000d4841c0701c0c2141c031398804101280c1c046030150b0344071080201c40541c640c0c1c14a0042e5105480f01c90070f581c0208214024000000d001240e0b10f030035808100216007000e115603c8401d603040c01405000301e10806d491050300a20004124074011030004204c81c0e001005600c1d101d29920f8403031000800251055040c0102c080036103411b01d107030004041182c5003090002d820101c501c8180900d5040122001c200484a00180116103880740c40e030041d0740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 601542598 1250 601541348 601541351
    0x2040b18100206150f040e060f1b091302220801020a090f0e0a051e04030c030f02060708010501030e03162d03020309090c0c011a130e1f0b210d030203040b0604 70
    0x8013800100c1c0c054400c1042d801f1b414881c08080014510083c007905020b0341d4654006130081c000c4501071002401040c450302c0c1c3c82907041481c0c901d2a0040d80c01880030a004602500e050107151038a007403280d1180c2d00c0540075035000105141902d0b4084620b03c0078108460707020710903e041600070154900c000f0051001e49070350305d010401800d400b00310300090702807441c011416442d081c64014001d681403942140400d05803403204209030700210f542842081c184e610303840545c2c41c3c040110003038001030300e60500b140030800544e0701805144140720200f41c002c030200c040c5031100c00c290360000c4442040183c000c1e125403a0707900c0000c2d03020003280c04256049980f1040f0b40c40380e5501078040d10608844030540d628000c10040d0380032464000882d01102201c58140d5004000012001d45540341245d542039001442d41030b210011030350715018a180c1000300043d2258140300031600c25a0081c844010900e030300803500101c00010014004001e6140c5401d60843c1445c0c3d607002041d03400030306040d02c01d6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 601543848 1250 601542598 601542619
    0x409050a17040b0f13140904060506060c010207081309020c0d030b1912050c03010605030a17040e180106050303090d0f02040e032709040f030c0602040b1810020615 72
    0x40032100c00360b8014000c002011540e5046212821180f680407140f240e0b80b03482d40d0907000031440c0180d0b1403c0038040d000f81c412003c9582c2d540c2c6040041a00814582d8807240c14407100602090074030140498070b00c2116200d0366025000003820703031f001040d8095228240100140c010010012900070303c20a003e04010450403114400120501c0e0041000c0950030b09101c0300182340d201c40c6501c2c0e08060f005406607a0a40c9044091600fa20b040b405210303007591007030082d04001034035207840080d150400440c2ca400c140e182d051100004009031f43c141034040001e103c10034145420700c250001000110000d5140045640c04150103011740300c8041c3c030b000b251013070781019074442c1e4107c5071010581d90103503643d070380108040c0e070066050031000ca01c02080c070501b060041c0c2810040580100d8002c802294559a00c1d80c0403a045144850126001038007440000760b004290304c09060501d01902c00b03000740c001400c3c00d010320304410300e10803c2194480300901100311241c03c1361480d40c1c4019544040c45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 601545098 1250 601543848 601543883
    0x50903121515031012060519062102130e010b032a010e120609011a040510050f0607050609033016050c060c030105030705031f0b041e09030306050409050a 68
    0x80b00025441403001c2d0643d00445c4c0c00300200b95101030722440d20406a4982266071500c800100c900a0103640058555104907040d107005083d4588000303840100034804e2208980c1d542c0e0709844440750381141a030f45440d403244462400380320005130031000400030303042140452115910058030f12901b80c1031204040c80c641154035044042c04007800c0342d0080340c500f8140700441c0c038024201c002482030103502da54804e001d90b00d0603003d00c40c000c5c41d6039503030700f4040c80c00d210030003003806030031500c00d503102a0030000030300011410702c61644034900d540b000d10b48030b510040e00484d24403407010104d400301c0381081702803114a01d09004035400001c0c180401d150600e0326101540d56129040100400780314900422841c0304c010001141652804d41c10740f000540d0f0340c02450740c2d40d071605240416080000588400003106c80e8400441d102c0010404148800005960004155a00421100907031030b01000818540c260240700c0003004203841c10089000c02d9102e01e91145010007000300003482c0403005044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 601546348 1250 601545098 601545121
    0xf05040e15040e0f0d020a0b0a02160212060405060f070c150f02161712040326010603050a0c020c0a0618050a0f061407020d2405090312151503 63
    0x1209800ba008010400c8101d090750b030b8608484072403101ca8810084441e62161020400700f2040358418811205512035103a5036002e9040500e540f05030414400c0d0902c0560368120b00e00b460b0f809440060310803810503080c154180140101281c8640b4108401c0c014215070007628250301a4004164a00e010201e45421016103503540341b44100310300110b02609011404d094140f0070382d200300c0d103120b030000f080440c940081c0902e800801e1000410300c00680824055156803902c140c688100d66201e07155a80c007014407040a170851000070340da40c010406209880e108101c00300e4990f0004007000c01c60343c0d00062450105008413810000c10250f452100c5a0038118500a032800030038210065489080e400c018100a00c2454002490f00f0900980504d042c1c0c01c484c03004c0c2e0080c001c4000d4000989038400110b07440d0010481c19000004c0d8001d0041c0da5200341d60080c20322401441ea11462403035031403490302000d0101d680d2440200086440c6550f000c85c010341d24240700d14815282d640d5605d2405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 601547598 1250 601546348 601546381
    0x20a020c060d061d0115050a030605030d0c11030c030706141b0c01170108060c0a020f010906021c020913051003080a030f0c020d021002090418110f010f05040e 70
    0x9801c010082449460001d168200b841a1802078065402903a240350031850004028450407124142c0500c228a203240728000402c603c17551414041602903480001c00d1424020300c02020004949101030000c101e80140300c400005011002003c4020804000a80307a074207904c252814800c40700400d00b11081003d083e940c1d502e455481c3c1070460b01c1c0c0c10300c400d500e5224011500c3e00048000e10800691403003000100d0588140e48001c3c068bda640840100041d8005100107041d807051600084c0b441c1024000c1a1070f042c400c080260700e542e6800d4034144074101c0d2032425004940107002c454400c1d07c03030648101e85d0101c0660003241c40d482c0c04513148410201c036040a08076000c0002c12030703502a0140c0081c00c4001c601001000309084a02c03003280c0b00d050708018000141c01c46041281040c07210f401405030200024000500700c51110800c205c1100000e104542c0c822103070075442d0071482c14040c8198000c0003801c00310759141440600408a1080e070050b084054118000f14110380700400260 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 601548848 1250 601547598 601547623
    0x24031906080105010302030d02061510030609020a0c12090602030d0f0b0d03030507081303050702190f030501091406100b0706060b1c1b090e0a0e03040b030a1518020a02 74
    0x300001925144628060031090000381d0092180c9026090591700c0056402c0c41040b031204e030030040d0082c4108008850001336881010103807640c0002c02e051041b0704c0100030010064075075014013045071610611400803c5952014001c0d40801004074640100c11900c0303440c05040d001030b1024500d02c801000f0a458404680c103e540c2d02c0300a800c154244d440306014403403540301d007001c40d078640942900aa07441c04000300001c6c400e000c000c3c018202074840c950b000c038001e099110804c1c0c880c2111800945c0c40d41c41680c15039140c500300c000740140c500c58003000c94110f0021700b51910b800880400b00c0c441c940315880112000145013024041c441e030014cc058001111015036942601010094481200c0c0201e80494600341c612039034001c0d45405c540301001c40d0b4945000d110320b018090046000300409000186495480341143d03d2018030041014000c103d11141c4c0340d0501700b004d0b4007103c03415900d90b052400c003808148582102d401c0b40000f0030718480400b41c4d4400e0700000890502c42c01d515103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 601550098 1250 601548848 601548851
    0xc0d0207141603110f01090b0306130e03090a0b09010207030222050106050d0513320708030c0d03022d1c1b0e0f270403020615240319 59
    0x1204121441281c030042201c0c05480459084620a01041000c00316110201d0102d200c4c7c050402c11140035601441e40070900820806144540c0341d41c0f0016a40c008640c82860f410005080d007452810406442c0601700c18401182003920640020755584e020740406481240c0d040440c0340c4040706c14401d4500e0070390802c0180003a5a451034081c10340c1d004000c2c4909050700340000a40980da000244140803600b001101d000c034402504400e01c01890b40c45485440c0c8080321481c0c1400310108450002010f00700011039484008506080c1000d185481c01ca041600400001c00300c5041850692610324000f0f02c00e1034620380004441100d4424a020303441c00301412500c440441400307610005840025031170400f050509903404446072465403c03459801080360f82030110720704022004a0703c1c0b610b4058090700110480d59550f850301d130200c408400603071015042060b000d420b41c030441d01c03140c01035803400640401307034481d058001041b09141c0220301d00840050000c14446002e0307030080d200c900c3c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 601551348 1250 601550098 601550113
    0x30602121006170f061302030115032a14040512100f11041806240f1106070e03011104080c0901050f03030a12150e07080901050c0d020714 61
    0x1114252032422210007105441004000440d640103a00c100240d0445a4401d1099a5006110103c03028041c00503604004121404c0d0100701d840d100450180c8113540305c05501c262040b000409031201880402d0b462568003175220161504d466210150b01118207111a1003200e1054120060181c7c0d840a036200d404188200c64101000c01e1114600504800030300090b81510840703829202d0081c405030f914030702040b0800c0898144039860360341000c41c500100310540d89541500303030501d000311180c020004582c0700c4404039402c05d035042c0190080f81000c3d400d000102d0707503007911100700074441c02c14021014001000750341c0079030000da400c1c2101c01e45a40c4613a2a140400d54401c017100e802030040b500e40c0000f00385850034681c00702003080010021441c000c480d15044408441861a4401d2070b52a2982c0111108089c2c100c8005400352110440302860000c1c0010054803001e0803800c07051b4541014403501030084c20460306481410307103015030b4031403240c602401810307544424503600740070312030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 601552598 1250 601551348 601551367
    0x70515030a02121905150d11031005010303080108060912030403031d070f0815060a0320130b01020d0c03201501031101080108010b1e0118060809010f0203041e0804030602 75
    0x25080788510144c00410031050340c404100766100c00342c118403154041c0b44105c009001643d81440e91003084c1001e01038442255469404e141611020780041780850840070040c05640e10810a00e0741c404c0d22900141003880400d40440180e120280015040540354411307111030340141d01410081d26091011181040d07910245040e8000c9140030703024a03401000b08a0030101140d001d058011200200081810ba1031a0348001d880c240309000e8090000e203542c9020000c0d0b86007414481501c1380c144012801d4100c10000908100250030040c09022603142c00c8000300790b01082034510540f210750210140001440c116141c802c0d0701004203c2084044004400c2015041300f1030b200d0f42003070300d4001d0a643c90390340360f17800d0350216a001504551218100c51200102c4150203140140605045c1d0005250014088503d001a000311003c5840c040610041ca0310034410102c1c8408100000c41c00d50030140c0d07550601a11036400310354420380c60b1480b0800c0c0240e000c110340c001d41d0301503c01c560b140f60f0172 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 601553848 1250 601552598 601552621
    0x603010902100e01030b030c060a0309051f0903030f0c140c070e1602010c0801150f030e01020a03141005061905160302070524090d150c020c12070515030a0212 70
    0xd00d105030001e1b0820100e00e10301e05001900e240403000042ca60380c00e10580394011802860303a80c80c10352340d40c07080394011505488505440118404610400704100b02c841c1005415200e0700c00c0e4000070b46280519010105a10441894132041e1042c0c01d541e544d0001c3e0740d0185050303a182c0040d1842c01d20395003446000459400d8a10341050550001d00c03034503a06100a40f04072509124041c0d20381c003101c7c20061311920948009941c001103050020f021131028a1403400ca0b0030054020000c6540c442e10300c9542014650342d540e006908515800800e0f041c08c0114010f0701949016030030804003441c800c41c0160003617084c0c480c0c07a996030310482c0d0303c00400d00300250b03108903a00c1002d00850b903c0e114289000c0c0000ca8140d140100780080d03a01d08980a4184181c5842c1c00c40b0680700d00c04402807202e00b04100c0e0041e60103035055640104a00c4802d241044001c6100c150640025444043d0420040e120030b1040d02e04000d48012290316035440c0030042d0068810220b00c05002803030f841c100401c05581 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 601555098 1250 601553848 601553867
    0x1813020a0801140a0303050a0302070c2c0c03150112020f0c03070b0a0207030c0201110f030c030406081303171e0a02070b0916120303110f04051912030503060301090210 74
    0x1034060f584540c015400e10044490f54040640040d00c20015840700501a40003000ca0901c110800300b00182d4a40c600e00f07198010b45000b07001a15504035141c0c07030000410110380c2220308041d42d285141052880080d03034141007031049052202c00403448d120172846505441101d80c00400165542c0d1520070305039100da2140400720381d00d002020202c0c0702c0a039984240c4520319450b84030780c824134a00b038006551400c0d00036a11001c1e1300c42c0c0e050144c0340700d00c04c0c00685419074002d40159162401c0840113030000303800400080403540b8031454440400d030711841c01e075441030b0036110020b01034945402c06c400c1911101c1d0180208015041440340341e0003d80e00505882d0302515400e130594561006413900c543c000400c48050b6440300318103003d40c550081d03015a955100f41000203280c401039040e03040e16001006410b140600c0494104480c1c1011596a841014500e8083c2d0035a0700b400280e00410203c06400b80800401000107082c40e20300758095030300590010000c028101c5d4000005080080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 601556348 1250 601555098 601555109
    0x9090c0a0807050a0903111c0b090d0203120705130b0a0206040b011d01091d010501120b0c0a14030a0b0409060f060803070f14070335030c1813020a0801 67
    0x840e0710009101034800c00a882020b402561020380c07203441d6846055241d01c1c2007820592020040032284148030910559100103881404030342d85d9460003000d4241000302840c0f400007950400c110b100d00b40c50000f160700741d100340d01d400d000c0c0e100c1c1c03500d1183d02c0b09914113400421804500149000d07071583c00083c0c2c148503a00c0744082c1c507c1a030b03e90005869403880d92420f45509810540140115450b94220309140303444410307403190004208003130600350384080c0d200150000f4000d698000b8415000b08841d0300c0070300c3c440d41c685000410200180848000d8600ca01d01d400d01001284110409030004400780100400602c10001d00742231210041c489406071030382e540d280440004280c4004011b640b41c8075003001c0c1c1034552000d2170700c500840e1510040e42e0b64207801611000300000343c25040c0d460080313441841a82c41da00d001000c0c4000c070b1403800c2080c00360300d0040c01008081c0c04000202c5d0780000d0140d414211141c560000f290001007100003028030300303002040100155070721140c164100c80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 601557598 1250 601556348 601556357
    0x20409141603332007200108060a031412030a0e1e2e0c080411010c0b070f1404080a020f0a0303090501051b0d120c02060c0901110309090c0a 62
    0x703031402150203042c8090500b1038100f411000f400d02d030500c65501407510442c000d003000214491040d43c04003a5031211a08071090f106060f200a02d118240030744406401080c2403031420760920380300090b041031a034032000300342c4681141d01d209580002d104800090105c101c80035281d0401c2803080c4040c000007442c2061601c1101c001905c003910f050009800050841c0280603018101e28551410321026014a440e054009044404070b00c064030031341000203115038030300800d41854a014250800c00c2041141040660600340000c0340d0340010450704041603003003400c084034245c0c13000d0b5600300c11114454400c1901280015181d0004641400114800c94030360104044940c10401000380b43e0002800081030100244003550080000b00654100380794141030b0340c4034940c046454004217400307020000380b2103d804804030f9a240141440d00c581400500118a0410381c080f00700c0c05800e51040c1003040c9809010160360091040300c9541c08050901c51183c9403024440159601c1181c003000080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 601558848 1250 601557598 601557623
    0x7062c031e0f0c06041505040302030318210303010509340e03030415050714060408090a0e13060c0c060e03030709360209090a06031101020304080604020409141603 72
    0xc15010941d15003c050040641d0b041508000b03400042c141000c2c228800e0006c100404805030f68201f002c3c02d12030b0880d08a09000c7e4001c2c030180a0450f4022440a0451605c0084d04440c0807011040d40d040d0f402c01d4419a20607552110410302c6001909005009840344498001c1000590340303401030045c01070b0300c0e21080602c18400341070740c9105078031640308030560b64034003085100d2140f00140305c400e02033b030031520008449a000e01e0131700100b590100c03407007140001c00789098240f48400308000c10303807504a00840e2810800c0c0d4403189205400041480d80d55a9a01015070f0040b103200750020780201c07040240d1340110804c09d80c0d80d4026510300001c106417039400070710300b074024581c0020b5136062111003002d140c1c003100c5000404401c3d803010a12940a000b841c800b5103c0852061003002c00c44800300300e461031030400904203814102464110b41082109116800000a0301504181e0544002445520900340780c801409403200154441c05110342c40070090720500d40c181d00743c9001d809000f10b813 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 601560098 1250 601558848 601558873
    0xd05010306060611070509060a0815090d1b03082214010e030403200409060c08060a05010f0903020f0d020301050708040605150a0320030d12050907062c031e 69
    0xc01000303400400136600c0300500340042e04068800b0b58100310050f1002010984410901d070074140e8480705120040811410090b03031a0301040070b105140d11a052a040b049040c4504030310711800018041c044c0200540450600100000c440e880281c0b94070350ba40701e410152511071003034601007051040740c0d03003003e102c003080c403801000f08c6084036400045840c0c0d8111030b002500c41d686200f02c0c0240c1c4160784241c540045562070243c101c1b8090503030f94450040c41c0a00811084000a800080c1081003109102e00c800c0c0d0041c4040c8140c9030121541d41d11030341c2c00c2c000a2845801590300039015403c4c08240034500d500402c0d018000c0c0d20402c0e00780030958a00350081c11800c00071400a13880108041c0804c04182680d14403084240c90810b100c412600caa40484d117002122040140006d01f110b0070b4074038944041c896160040284005884500c1c03800741c004002584648085100700074000e103605105040722a003051065000d400c0c2e4103044801c03860103d1941c0244d0070421203000b1100c1c0e0010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 601561348 1250 601560098 601560107
    0x120109031205090a0b070c020a140108090718022209140109180b0c0d14100906080a110a080a06051b1c05070e03030c0d1404120201031107080d050103060606 69
    0x458610800144070950941d03d410045c01c50251800c424080000141c50140e00c84070204005003036894000c00c031b90310071040014283c110042ca2a001c45c2c10040e000d10201c02e181c041420074444074880585c80d518034400001070044048034102303236100e5412002460144940007540801088400580306a9a918a00742551031005125400c454040d0a8800045852203850780208240900300d0505400700e0707585040354461058120012603c60410507106031600c0220068544000e051200038541540155070b80e054810041004e030b030325117208841742c88410070140180b070004d0441d00002418180307007004110070750360448102801c0c8401e600e1640c3d00821502184084a04640c903610141040c1d402008050141d80c1080403400c030040c200d50b0100041d0940d43e1411f406401066039004000c0c0203186240b001191b038043c02d0108000e0b07d030520015641e42c81e020308000c00c1c5951401e4400701640300c0c2200050175100045500358180c101a40301a040c0c82c81040d00b044851b07141c51040d01d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 601562598 1250 601561348 601561351
    0x60d1d01180507050d060f090b0a0c030c0815041e1b090302010f0309060209030304060809071203080403140904020409090b09120403060e010e0d08040c0e06130e0705120109031205 79
    0x1841c0e50300c410404c001134207045582199030760003008000f40d0388958440900c140e4005d0760099034002c0b152028859055240d10600e20300014600342003050b980c80880180c0124401044080e801c01010100c80349031322260810180c244a00204401406010480d1030050499101800500c460901c130050240d0245410106694050711101f44c4118800001c5010382030041c411201540c0900640036543c904002a0001d0b1100e9141d5620301c0c6414203240d0303d00b20107580041025000501c001c00482d40007152181c00a4051801c41302d002400c000c1d40b50284141e546460300b0910000c4c2c0001c0d445259400b1a40d01481a40884083d407110080306541e001c8280011140400c100b008000040180c1c2c850b85460400200100d11011907103110b03400c001b40c4030381900214044400300020840740703401050240040500a14480c01d159000c200e5820300a161100b403a0b0756108001d0110310100a6030004100083c40800c114074000352442c00791003000c00403008100c500408401103906400341c035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 601563848 1250 601562598 601562603
    0x110c0a05190b060d2f01080f0c0906030c070f030f021005010f060c02190611120c0a08030612070b041d06030c04022104050c0a0b070203060105010e060d1d0118 70
    0x1030240d11a407041013106800014112a0b4080c000c410181400503103aa0041c0042d0b03000c0c440400e8103480d0005060340c080105100b2800b2011010084004490750070381380300d42400d41d200c5449940c1c50300b000b46d45104001014040d0074015030b80c0c00070594414100d0a51030342a500b84e17855901d10110102c143c070001e000707840c0903458500050240920030502d0706005800201311941e0b14044c0130210003100d0b029008540040c07543d0300d488011351002c00010750100c00c04c9826514217451490025104c0400c060000c10b560b90010109002d99590198003001020342c1c410f881c032680d50f40407114125400f920401e442482c5014001041e451b121095134400d84000d400340c00b0140d032050403c4003d43c4010341421858813240740384280c1000410700035220b107100e4001001000380e0ba10810030311000e25030202400d03480c20004880162000710720581120420300300a258211405e000900c03c2c080c1082e0585100d14006803584400c1b94103950444416a1070000c101d8803102c028151210800d00c80d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 601565098 1250 601563848 601563863
    0xa0f020d080402011101020f1902010b09011a0d06050324060103111b011410052409090c0f13030b0c0301030f080307030b0a060815010905030d030e01110c0a0519 71
    0x90b0165008aa03038690f04045003000525000221380c59980c0d0760020092010340d1444040d00105268091041c011154011a5184c41e650b1420100808801d05010b4070b08500001003003204a00b8010781080b0f02809005068405100d800c10b440c640d1401104c0c0310b240010742e0840400d2080d4040d10407444400c10703850312a0701c0c02041500801042c8000b80081c10590341e140503032994060305600040c0a00d00c40e00391580450303c0c1ca0200f0995076910020306480b40301c4042c01803100c51014084558842082d20110150307076a1000e8109980101110048020400103541c201c0c61010380c1074009403441440f04042c0303620f4645e0740c07051b54002400020602c40c01c01228001241401e80511352000702460b0100d80d022140001c14070610007644004c3c0441d5020090050b0345c040b00c0d9904031000c03800c1c40e00c0040c103403803d4006580d40382e11101490605a41d141c9000400d41c0a4100385100c41c0c0496116a8070013245030003999411003c04240d500c1c2c0600d01c0c00f00f98804d40b46400280c1190071011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 601566348 1250 601565098 601565101
    0x90a0b1f06080606070c0e0a0c05040609060e03010e0d050714030301031a0a11070807060b2b050313080303160804050604060c050c0f010506040b0a0e1b040e0c0a0f020d08 75
    0x101960070b0312000c0d1009a00c40010f01c59038002501c4206020007408980055620728100060b0000903035100301003007018440b00744000e122607584484070038211000d5150042410100d1004640101742c0c9201403001c90003075070041040c07a50880c0042c04107a1103448400140c55200221a4030390100780001040000404025161202d41c00c01c0190056000c03240051411942c0d1400d05599104a23012a6003034000304011090114a2044c18024141603c0a0181170144024560708a0501c6569409155014200401c1c49010401d49074040210220303101c032139440d01013039a62908200c5080d90580300310000340340d03410300c200040e03070049501000070142a1180d940d4100070740003c050540410006001c100074100301003050306481034a550000599050a905210582c0c001c0d0300d03010300524160340204501407215040507400200c000550303606140c60001500c051283c0e07030062441014210511200150a070001c0100903029100d0f1050b46105c5070060b622500c1111034000807941610 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 601567598 1250 601566348 601566359
    0x206090c04020c160801050f0609070e040c03150f03050601060c0f0b040222050406110c06042d0303020309100b0906130e15161809020a0201060e090a0b1f 68
    0x10043e092240004054804a01d441c0340f441a201495a1201c4496034450040c45480b03c0c041214641102095a40b42c0d001c0c585120068908c1c088a240180641e81e601d4031441040d1080e4004150b2050800c4c540341d0540d48c0f400003001c1401f8a0109452a0044100008040d4002c403002c40040341c2c05280b41d1140d000315100c4400a290040041c0d821107a1542283c1d6582c0308503541803e441100c0a00048904040c10601c0440318000190541c03460104450b002500d000a051039100e03078024a040103505e010741d4101003107446036a00d50075120203e02444201501900038500c15a052030460b210304000c500c81c1c0b425a4050b090f17a0b074011140c5d01c00716044c2d00b844000d001e003042ea580000b203500c2c031705203290501e082841021140300848120600141951111f880b5136035083d145008130b80141000940c80b01b500d0648540308010f0390028103440554001e41001005082c640c814143d689400a00a610b038401d40c042210948207070f4000030100302030203445a13503161440242d5540301d400e05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 601568848 1250 601567598 601567601
    0xb18032515020406120507300b030d02060109050f0c18030c06030a090606080303090616020a08191214070c030c0f2406050d111201060609080d0206090c04 68
    0x898050701d03545040c1112910454081c002000141081c1c0e541c081c61007030580d011021920003800c400100820321100340c09410b4032020b407502c03400085e20340d81c00950f5540700c00b2000381030001d8000d030907004c1c0b00c14800c400c580202e14541250b00451040c44103540e020070700c90022108403031260198006201900025900f4551050141d80250446000041d060300040841c0c000700c400d080c5070390301c0301915000c20407035004e408001c1c04c03000700441c15030411000c0a500c0350b5004041c403095007032802d10315240510801007602c00c140c20444243d039640c1600c80ca0740d00d42000060550224040d81c1d407400400c10140b0800f888095848547d40c260740311100c0032926115245015810031413404081404a0039003040c0b0311206214000c201440120200c0580107140d0240000882070316040c41040749450f060202009141d00802482070808880001103050f003103d80c80c0d1205d13611704500807451075008842d110581c2d0364131084640103d19146c040780d465030216500441d40d0013404581100d400d26 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 601570098 1250 601568848 601568917
    0xb030a0207050f060108010b03070501081e040203071203030606080c120115440f010909030311070b0402131109040e0a0506072706020a0f1e0b1803 65
    0x55003d07106490b035228041881c00c0402c1c1c1003140030b40d540d9002c0c000c01c1d01e0108030150080c1002e082041c0940303041607030002d5125616200305600c410050025003107503010711411000e020008001c503070302107150500030000e280c180034100100b0f0165000c00d0300000e140f410f032091800c0102010010380c0c2070101d0540820300301000e0303005101d400032100d11211184000340c0c90140c80891410f00743e105245c0d0310240c13542c402140ba109400c00106106090805000c1c0034152034644101052900701e80c901200100600b1031030b800c1800700814184104040d00c41400c0c00343d402120030300c84280341b5442c0c10049070b140c11120040e10390308025a103a0ba04240c0c1040030034040c550182c1e10f440b4070700d403102e40c03c0c0303d4111490f01c00030702e0f6030301240080b90a0f400121010800d0300300700c07910b5509040e0060350714000103901800c0c81c03415040d00e808000680c0c5e2038101001030204031140141d0145403000046100395054010740e0b010241004a00b2000420f84101000a20341041202c91031250324501c0d026 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 601571348 1250 601570098 601570103
    0x1031e030311040303050310050913060207080f0c030306031b0a230a030321091205092b0204050901200705030403060213140109080d031d0607020c030601060201060b030a0207 77
    0x40701c9480030702c50500d20000d0001903010380c0383c16a8034035107034002405000d030b05d4210070f110301e805000b408680c0c2504000c10045552040c001070791201d1078200461540142004462240000182c11044880101c040e43c0515010b40031140d090402c1c81c0000c1802c0b4418203a150001d0142004014210051100040b640c1c0300c241c1081203402d000020030000c1c5917903003055012134540e0040d280495030111014003104004039080015441c80c0c1e495142c0014444d010300c04102e0081510581541d800d0102c16115812141080100d010400100380d001d00d8158281d204c1d81c500000607c4502044c0212008030a1603070408007144011090039031035400c81d05041c1c84521040c000800090454401002e024000e20742507120140f1f4220b0101e51000020f401c10704218584070300701f01205000400000f10306c2c0c40d04001c6180302c1c21051100d1015051100f14400d84903940502c80581d4020540101010080c1c06440d03c6030303202c0c40140d0994459100d2030038401030400c00194466203990244c6855031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 601572598 1250 601571348 601571351
    0x3110f0d02030609071509050d14160e0a110c03040e070507060e07050f030312070806010e0d111f090e0705040806040c06020f12040b07060e0a0602130b0301031e0303 73
    0x40c12038010902d400e0341110220071640c8107400030302050181c4014682816901e14101344080d040c44041500c0903102e1600502e61841c100191b000410203000020300e25480c1c2e4104401d8607564441c03c100c402c4140c500c01c0301585401118505401d4580c01c40e1f001c1180c101c011490141b9044404d610f5100040401d400c01c8403c0c0910700002e6028011080c1440320f5000030406107003004108990301e200140c001703102c5d1b441003240c0b4088402130b00328260701807003a08210a6690f11200107881404200c01581d501c200003060f40410005102d490082e041803e540c0d041c800248802107540046801e104d24005c035101c04c004202c039540300a842540016145006400c040d6280009460b280b400e40342154000c03262001408050741c10004010800049070062415900c000c0e515a66482140151110140c0001c2c0d164240040ca40200c44443c4c1004100c0d110307448a41041c0000750020b400f40c40e8400500c103400124841404107a034141d076000320040c456144281d8105806a481940031410315 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 601573848 1250 601572598 601572619
    0x602010c02120f16060213050103090b130224040f050109050d0b04060212091c0203091c020d0b0924071202070606052206120503090907020712030e091003110f 70
    0x8000300e5590f04c07000d62064502680b580b510380261405c034021604842d040610704440c0002190300700340c500b6005980c1246048081e1001d00110319020b5440000545660000840301e20f0f11164800a00444032002c44810415480d8001158140003502c603e6600c041c40740d095801041281c0101038100748585001450a2135600c08018030000880314803d0a80000445141e008641c80d00c80b0182080751018514007100c0030005211181c3c0056038142d00044052135a04540700d114040959580000c0d80c4241494101c8003503964000760840f415001d0130001d210450780500706d8009000300559101c02d80404c0700070700294000d402011041e01c1e01a103d800000c2c01c1c3d12600c1d900e8105915801d010800194100d1507a41581c407513a00c01e20080810003203420210b0700c040140c0b83c20754000ca994640342d4540d24070032403502500340c00604c0540b106210179030416801c004405030300d50301a90398040c16590b2009540002035a4480940301d0f103c2001d4000b21440d2005501d166140c0c02001d02800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 601575098 1250 601573848 601573867
    0xd0e031b0a0636030320370605011508041a0402010e09010b040f0803401206110a020c040c0c0f140c15091c020603040b07090602010c02120f 62
    0x1014540710800300d5a411202482032681c0103200400c0307014035000100104a1072050790750358666030030b601000c4118507000c10801f458503602468980307001c001c84064a10301b504041d00201028072803007940c01e045a014140310f0f801007030309520a50b0002806108040440b01e89a10380038001c20072410443c3e52146401603540d40c8c101d1034083d00c2d24880003900d031400c00c9801020000303a50025a2540e100303010702c0c011904804000302109021a030018842081032031036081e0181d226441400218400f003011070003a1400800c50100d6029003000c0c4110703120180e03900c02078441c0f0701d081c10044e003041022915608140d0090030142100d881e0a205080e00c035210b22071441b142003001ca400811844050920110401106903100022242004085200b00c0c0420f8540f0543c503c882c001c03241409501c9580000c152a004e10342d4020700f0b01c07543ca207014079194040c1481124040080f88007030101140d00d0b0300c148101094003400d81c008044212107105901581c4d04101650003003c0c5040018154 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 601576348 1250 601575098 601575167
    0x314070f180b03041a06120a06020f0f040909030e0402030906150a1e080106092706090f030c0b0a18021908011b020f0303061e030a050d0e031b0a06 65
    0x4264054062031303d07403a4821840c1c1085c0107010b4512849600c4248807403480e4030b400700d05a00c0d1150310550050b55000c1c6101d0600d514042c10400caa0034100c04a00010110300641010b48294800c0e541c00070450710600820040340000c1c6c1d5100896480300c000601940100240010010070080401480b2681c0f00c101440c00360030b030284003030100c1183c40100504402402040040c100c1c100040c420984940d80070b84150504a4070072495882210080003070000c164001010300340c100d00801204909418081d000300a040c10448103403401c0400200d00d4002d40c400c160301a515001c40c14040e000070307020480320004210006400e0f0740c1301040052040300074483c51320104d0100201c090000e6046401a08080840d0252000350700700708100403580e03590210100c081561b04113114240c50205020034500541c0000c010030910484c0000c3c81d40c0b641084074503400c20b400301c00705d400c1d03103940030040c0d6410302d510030011b500144180c07410b01c5410b02503001c442030740116101c20a41c00101480141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 601577598 1250 601576348 601576351
    0x115030902150c0c010e040212070f0c0804060e012606040c030b030d0206100f0e0c07030210050403030b040f0e1e150f0f01050103180b10240314070f180b03 69
    0x80b816813041111110558200d280c1a03090001114210305082407041100d4000e07000400392800c001001021840003401a045e02e0000c0d40c100c0d40c000c1c0c0321030702e681020305010700b01d40c2c0ba1804940c20070900002075952403912240c0f0010780023281d9803511481c2c00e10000e4288a0301d20824140ca0b8042c0c240740740c4080024061601d104d6000703010506000300c01c0050313501e550b00404075220071032900b4441617120b01c4100d50411032500c12240e40fa1000e0404a0410019485504610781840305000515a01d0740004102500441e41000003c241821041c22140b044113000281e4102c10218254042201c03943c5c20501c14000c145c440c1c2c114581460700503403200311072401645148006203c03005120706282c0380508402e0804102d880b0180040c244010300c110401400e04502c1c0000561200840d50200001c0c408009201c85e100119608140600080024480001e01c0e044410300035000d03d0700c080d401452992649035162103c0f41007140c5803840c403125014400a90b400004640480c0740003103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 601578848 1250 601577598 601577617
    0x20706142115090f01330305040302010c0c020a030b09030c151005010906200c120102071109010501081803070210022b0f1803060603050f010b09011503090215 70
    0x2105510346a940c8214080e9502c403041d029819010030099640000c00c1c1181c1902d580c0890b1040d505444010702e0b1800c914422511403001c46e142d28410342540640045005520a400a20201429400440d00d10b11031800c044e52110302c0b00c0c81000421001d0301099005000075054074601010307170f2f034a54a0908403101ca08158900c2a0401c03178a10344065600014140900e031054100e0b10b0220700400b1002c4444d0074603001014a04007494800c010040c0181c131140160680504400500f000e074000d421850050798240300030034802d16240b41c080100da042e544142c68030080c5031905000d240c80c41854100c50f0b42c141c4010011000560f5421000c0716400181350700804004030f003003070042e181003500300d044800304440b144501506a009001482c03048071600d400300c40c604036000034160100e075550029007680e2924101005111002c10391800e1150000028071506810720f0030300c1600f040034800c02d003070300c01590401042107129030400d1040500040c400346544c0c82c41101c1484bc1d078400e02c1d19 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 601580098 1250 601578848 601578907
    0x60405060a0b090106080105010f0c1b08060a0c140d0e01020f1804060b0912071505040f0f1404180b0a02040602010c0512181005090705040b1002070614 67
    0x40000a0300c16000b014120b240c180c40a181c154034046001c4c200b0501805660f061110b907200c172030701ba5840b0380320500f141a00802c4400725800554000c04d031350319203406a08071900132400010010707001400307450302985082d40d170300f03a42e0106000d01c80c2e4250807512a915070f05441742d030b010903094002d001809040920860b02a942e65112010b80c007445411322610b801903081910812011005a0940302c01030000d54505903000780e1041014100202500816020901c0e41c950151290b07110300030384255519845503264081e11000b462800c121148924103030701c8184c0121300d165091940068000c002d030400b1410b4560083d0343d0700f500e00c2c0310850b40d28004613404103003002481d90900906102c1d544d20300345240340c180144028000020000c000c0381400203021481c0211104c20442c100c241800c1c1ca1081200d410958003240e260b04c807912a840c8140c1c1405500c403082d14000300c520480070400c0e001468401c0c0340c101c007070700c120b054084034140801c014054400c2a0b6800707101080d4181e10340304d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 601581348 1250 601580098 601580101
    0x80a09030c09062309010306050a0b090a09350d06090e0f0706171b040302030d050342040209040606020106080111430b150907020712060603020306040506 68
    0x307400051201d0384c02140b40031003049403800d2644900b48941e064079045070020409030395004440025010303040b083c6401809070700401403080c07143d41c440c49450b03109050680c0300300c02100e0746030350055042181403104032420340c03405099201d54008000c000d0400f00041061a80d030300349070040f02c1c1c03021921031442e0005020240c1449040c011070010b80483e0912585403105404884182c5100a000001c1038281445180550039000d0654008590003030480e1100306030510024141e8006513040c04511a12013407910181410b20f003e500001031314480f0b03401c40d0010030301c0102a2072405181a8009a0800000d04541c4450107020041c1007103070008038400346804100d0742161004945600b4024003070181c48600c00000c0315a4152055445103102c6803142404000012007202050b00d032030058181c4480100f01440c02540d100d46208542842c03240301c0385060158429045400c2d40068100407001c3c40050202203000c40f040c0e00609000480d5034483c4c0c046460424280c030160788a500040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 601582598 1250 601581348 601581359
    0x503040b030a0b0406060c020111010e0d110f1f06060c0308061c1e2d0305071b1202030609150121050109030e03060a020901230c07060320070f080a09030c0906 70
    0x30700c901c95065000001c00c094330001034229114900d402d140020080350740412034200d1003c10141107074241c3c242c1600c03410404e1500c40403c074007074000f000c580b0354204078000540f0b038013858074107083d25015121300c40b2a944e00c0c3d0400c01e04c0c03680e90344490b079070fa083c0d000014045044ca08411442e0394801e0700201034a8050305000e100d04000e10000b401304c00301030102c06421113240b0440001c40750325041041c0c40b07920618110a1030740c0741d13584103100b40303086140c00035141c2d0381c441100c802c1d98000e44c2562030750385030314600e103171200c003031001b1003041c030b90840010095103800f05c10f58076900c1583d08003044d040c2495541ca600b59034040b0015000200780f07103540c015924060090319000809003c1c1146000d20b100d001820661952114044080e940c084c0d4614000800003203509002080003900d103c1c5803510750140c0206071454076450198030411b0310000814510049400c40c6400074848800e5918659030071106a120740c00c000304100d01d00340000005a02820288050f000d02500072400b0360906 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 601583848 1250 601582598 601582607
    0x9012604111903080f0a11030f0417031e0d060911130e0412030f0b0d0c060e1203070602160206040905070813120e0102031909030209130503040b030a0b0406060c0201 73
    0x810308007002c0407981104100003503509080ba00406044403d00c1d0b291180104140d60500c954890f400c001d000020f0b44035110401480180b042c0c07a00d06144603000d0104414280e41e81c01448000a8040801c42916100c54002c40140c01191603130000440d040d41c6030010001a41d114021170401c400021031410500d041c1c10450700d01505610074003031380c180ba00d03480d0140c2c0d060b07160b4111028503550f401c0c00e6080318116000b41e201d03028041d0503000742500a150052002500380b1502001a80c0c0042220491400c0041da1071541c1540000314241716039074403288029400514a450701da0b4405e140000161a610080c00060114030701c001030518080001810081d40108400d41464114010744000364911502c00922159440d01013111405003006038a10302c01c1914000000a4982d5586041a480000102664803c0e51038100703907225484028100d2100000080c00768000744818040c02629030042c69006100c1130021078501c1c0807a004c282110301c240c00c4040002c0182841a0565802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 601585098 1250 601583848 601583869
    0x70f05011e020c010b04050403080a0506360603160314190804030606053a080423030d020307020d2406031109060f0d08192001020a050901260411 64
    0x54401f4821441c203a030303000327080680003051b0f45169556040800c0b0140c07550018291400100b40108a80d19400f22191007820155030403c00e6103403028000074120306010950300c0f2011205009508018116030f690841c94281c1b84070200c003440355240c1180fa020403036014006040c000d4885564070350031802c05d0810358459401040c080d41c07002340720b5110600401280e0807542c18100d402c40440701c921019951180d514000500030580105022550980110141171030800c15140800c1d1801d4880500d500c2d4481c030041800940c00a10036079000d4102070312040d07803080c403508001500c00385a200b061106041540313000c0c00c2a07039a0606108003e00341402d00d00c41e90044400005601c1c007000000d10718000201540e01400303205404500f005288425200c000c2c1d892199070303c081c801e00c2401000100e450908180f0802c0c0d10020b0f1040010620840381036541c6903455915000d0310100546844490710301091401c0c5c0c0c0c0f0b00402c908040341d041102e000b148104649041c2442190801284031759 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 601586348 1250 601585098 601585121
    0x1e011202040509010b07080d1e0b0a05091515070b221104110702040203040f03020601060903051903120516080903120103020405040302150103050309090a020f070f05011e020c01 78
    0x10401040c81141d80f0707114a28115020341a40c1d0741d888180740b822401c14060b05241510090034071141c080b0ba044200e41321034210b415401c0030040302e000d81040210201ca6031003441d4021003c00d010400340d48a40c1d1103000c20b854064990680250035403400c849650000078180c54005004c018004900e140700e01d20501160301c00080300f4940c0c02c40d29146030401c40c051509100e55031701e084100700c00040100790780407541c00400454503842c250030040c1c0c0b150b0f2342000460040c011070001050756801040c9880c140d9821030000e200c1400218603615020300c0100b001d074244001031140c205a02e00c0e0b4000d07a44144200e0400d120251a1b40e403024089000151240c04030fa001880000310466040c0107081c1103a4046801107a2074582e41010390074007044440484400555800100501c04000020420302d241510405880d07a22441e201080740078294039442e03060001c101e0300300403407075255072251501e0164000148403030000b030b0850066854243c080a080d80c004c40d800040841c28441c0307205009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 601587598 1250 601586348 601586351
    0x307031505031f0b121005060108090604060b0a0510050a030e01062d0e0117150103120513180c090e040201020606060f0c03040e091b03071802091e0112 67
    0x509140001e42c80d00c08503510f0303040328070100c2903561446286401482c1e1500000e0700e035100c4480405a8945c0380c1e48141442c02c0c085003814040f5255511541400e072040032140082d0403030703840c0d665625010f08940500036603c564610400318482d0303039042105031400f001392120f80d0f0b513024850303000d400d0f96440c5031700c460180d01d081c0041003412400c054100040d0458040c0740c000d28245080011a104160004e010b80d85034000003251403244140c411042c85c0080741200d00043d1340604d00910b6440c00d0000a00c602c10030800c18103107074000c2010300b100304440c09039414542c3d00c5a401e0b407580500008001031b00d6440300d07601609150402502805840d1074ac0e1078469600d0b081c1c0002c0c0d59054040c100d140504800504641c03481e2020042d103000350b6100e4252030383c85549080c010759820f4192040d1241f401404100660035032407080c103c10482015010348281c40c40d10000700090500ca01000c0580c0780c081010841c0c03580d4103100d010200c4888562a1604040403000618000540301c8404015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 601588848 1250 601587598 601587641
    0x31207030506040b180115090803040305030403020a171203071b21020111120408040b031906120c172107260301030206090a09020d0608010f11031609030c0b030703 72
    0x1744003001024159440c00650840c802c1b80314004560054080c1c0c480721407030001150200410002000520849000315101d105003620380400d074a40840c1203400300016440024184020001c00024591103442c50802803007200014109600310516840216a10660300300641115140d0f4442c403c0d18050740e20080000940391402d108951251070162180409241c1c0081c08010003101100d018001c01c401c7c01c4d03202e060401d41c0040d50540141e41000d018200040420488a2462130380c822a4010042c0d14580d442c0407056a8410701e00100140540a01e0140d40d00300d4800d1110444070342d007140c1690381d4170516030414030b04810401039561800b2610074013801d040030010741500e06494045a0f0507540308003582c0003d4480f10300d0f40c05079040500100340c40b007110480340d10940032110814000c4c404d40039103214881c100c1c4c0014009000f521028000318501b10305600c03600551500c1d9040408104c0d40ba6115917030403018a52112a180100100f08080607906000b017882d403698003c0c902010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 601590098 1250 601588848 601588879
    0x9030309020405180714060912240708010902070f2a0b040302040f0e060103151506020c13020c0304061101022a0708011a061c1b03050603210c031207030506040b 71
    0x80d807041c007238017510030b00c40420b44401644061010071613040258503507046040e4850003032000d4a4048034070001081100e40001a02e0342070b07000b2524030076400b80440d100c0c51980e540b800000702143e802e840e03070348800200c030810f0350b10018401c60190841c40e1030142c40da451481000141c408580b00001a83e05112240746084000a00385054a03031020300308440c40c0341c02940304020807201d141c040d01000c00700b20004000707801046545220106982c10100d681c5540c0304641a48189912080345a004210030002c1070310035152600e00b8295031001500c0c054860b1400c0c036010503500d0f2402c491070002c2041580040701040f00c40010548035000b44030408240082a12041c01e05241320b008010010f99042508804e00304902c1c02d1a043c2e20800000e091913110844544150800001091030400031864505d4001883d04861013500d070303110199a48036507681380302d4000c1a0410002d100c18451404c0440994814078455400e556001a15140c4901000150350f0744500c200d0141071411210080c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 601591348 1250 601590098 601590109
    0x708011802090c18030102030f07021c0807200106030b1801060803090d03110105010308030117150c0a05070602030705070b010902030717090703150212091c0309030309020405180714 80
    0x284843c001c603900ba01d0b0071301034050401500a001895a055100200704083e2805210300f0314020031680d030031038507024407612861615280c89d401d40008504428001022244601014103101a01c02d08500c6000880d26906083d0784540e0011078030300c800041003004060204030141c0b54413002200900c03980786005c4034141c980c82018180d40c0240201c80b40e150900d802000038a420003c00c0008011940e56030914661541007030207034070074a60078440c680103284000610301c0703032880e14103092840603100d05110382c80c7c40c2d020900100600009104090100d41d0510246100300640c0c2c071150358640c100e10f451001740e00140c0003100d080d4414014005055442084401c0b0303806c5690b580e0380282c91300300c2820f240400035440200880c0c0018008502e40d00690068400b99034400140c94003912380c58030103030319101e44002c000e000e40c41341d50320391480c036210303030440418180a41000129282140c010405903401200d800c0d4a05100c101c5141e0a80010012800101414111100c9441600703002a4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 601592598 1250 601591348 601591351
    0x203060f030a0c09270f15090b0c070302240103031814150d0e0a1202010501080d0518060d020901080c2d0f0c0d020d09050603010b0307020c04020c070801180209 71
    0x408495a5175000b107000005840c9884644124a020860881c07442c50031110682c0103050071a01c20381e0740400c61400784600d0150031150783d840081c080560703890104003030f8160130520040c1d0451064211a00c400c182000401c404a84111118103080d8103506000c3e000c4c00200000301654107000404000c1c42c5150000d0044801040b14000f9410981ca048002c40b4080c2e084004201407604041102a6100040d14511103208000d10300552241d420300760300300c0710244164003003074000003081030845104000808001d08060070356030b0b4100c4280d0101d46940c010307408100115600151102d40e5607000003400d07038050310713490b03034140340629020148031040000183c00d04000b80c0c0880e250080400700e8280c4080510343c004290321034624440c859590750304121008003601070042e480804610560800082e200c0281c1541d2a5903e00300c3c1825043e4001032040d0300714007c1c3c2c0c417510200e035224001850f588005100400400f418082410308640b4854410044861829445001a111844030a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 601593848 1250 601592598 601592609
    0xf150905010e040b04111c06030f12020a0b2805010b0409021e0d02091e03030f07110a090e0c0f0f0105070206070804091b18230607060203060f030a0c 66
    0x12010440c241e404a0013601e90b041e0032507070040c201100701340810803003405801d004201d00c0c501000c40d15451150411141e56001c003910040450b580b00c00464070002e8800307840038851044841d441425205e050041900b40d072004e122100c03202c51061014001d00840c1d4240984090421041d450080300624910680c807601100030740100c0c0c00841e0020f213a00e003d08280081d00300d541d6a4841c1440310000f0352000020740d01c0340d00039841903200d0002140740100040c0010b4025407501c06070b060b261b400e642207030004a981105150003142c56894030311051b401040103640101c2c66210440c041c2d41003005001c0010300906070400020801c0c1d4400002466000382030905940e180003030300100b070662140000c00341c09198001000510512b19034801d070148038030003107924101c0600c010b0403107424100c92480701c94142010428011842c410303000e820003202c000303041652409150003255042c0c120306c40950f078050b400310400200782007220301d08207000c1040b0040c2181c6000ca5440c40b484c10390740d0007203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 601595098 1250 601593848 601593857
    0x1501030506030703380a1d060601031508370302070b0a1107080c0103320c0c010905012c031e040f0b0306130b062b05040506010f15090501 61
    0x8102c140e0215203100c480f50321141e0003c0400302009007050904100346c56002020b4030b0084450f140320340311950b840102034550003800d02507c81c1d00c0110081d154144601b07500000d00840003482c0107080000c81008150102206081c0b0301d4010501c0000002d01d0604045090b403004c0c0100081d80411540180c030140a4a50384909810800301e44c800683c0c0300a80891148841c080703142c07040007800e440008405d0307805000c4420303c4130801d0001c103030308100f0300341189070010300c0307103103c5d2001400c41e600540b81c851143c00d20042084c0c481c00e5a403037071000d1301c1d181d5460502c03404a21124248070901e4910440312030310003030b940354069628400d60a035803d0601721880c424000340100d8045800401d07200b0491840d00f03440380e540f40c0e101e5005844061203980c8800c2200300f8003005014035000500024095400c01c00844600f8103201c0880c8400b11490041c107003a041d03441858800c030f6000e0b500440040c0110f41c14145064541d09051b0080c4d540390354141a082c1401d60710001540c2650800e203030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 601596348 1250 601595098 601595123
    0x604090c1722030c110418051c0e01030905010b0a090608010b0402030609040b041e080409051008070b0c100603050312070503040809042c030310060504121205130306051501030506030703 82
    0xc1c030703440e401c01134a00b0711b6000f410312006a010011120720031a0060051060700c00010444e5503042a40d8003940c00c240100c1c00c5e1501203400c0e507000794082040d9500880020520901390400550414001e4000a102035a5001e040c8607a440c24480c0c1c10705203c064404528502f040c01c001340b0f18030740081c002405058480c0010702005201c04103009072803562051000e00007050720f0a200030303402602442c64000c2c609000180d41c40c12241c01c40c8110b400a80240c04003a09020030031101c1e51103604007040720702c02c40c3c9407807000808070f110300001180620f0146803190407194a44140020250056003040000d20a1201091951048075036281c01290000703550040e0003030b03070341d8200018808100b081040340305100454801100641c410994142c1c214922500c4e10710644050055028403490302000c4030ba01c600044000c2800a03500e40c1505000b07060202c2403c01e5205808241c104490b10350301d03841480320368082003011700b02900702420305009034508000400d540d031000340b00280c2005440c12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 601597598 1250 601596348 601596353
    0x9080a0206030a0506060c120306011b41010911090c0301122307090e070803030a0b15130e0601050f160201030b030d0e030f16140604090c1722030c 65
    0x40440d1f103080751500554842d50412114030500307030412034065000c100d250980b80090441d0280e100351550b80041c1000c400e5001300701c80348085d030182c0c40c0610407800600c9031522081c2c1d202042c80841c54103a00100c1caca00c480d442c040c1d500b41004001d190242c28640d050020710120001900d040d20721840c0800502c640340d080403c0002e48c0040703813034024011030041d0b80b0100c001040c2c00c0b042c0c440a940c107020407206400c030079640d0002d0b8802c0d2000c40c2c10500100d80060025089601b079403200800c5601c00040821000900742d0020081c07184844610780c040100160460f910340d030115090030180c0c1400c00d0604030906c1c030b104c0c040a00b0680c0159081170402c580c0694001008810042d04990000e012000094902c54840302e109200b44210380c504044081d000805480001d04018220402d0349425501c01c0c129101c0d485059002a003400045910a8144100d004801d41d076a5280c0b609005902c09205000010780406100c1d4020910a604841007040801520b5450b150000340302c145070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 601598848 1250 601597598 601597609
    0xe010e070b1c02030f040b24010e0a0f06081b04031203020a02150a2702010e10020c03011b0806030a08160602070f050304031e23250609080a0206030a0506 68
    0x1080d003003150b4404010b0280240305c0c070001c0c2c0c0c45588100702c403500b01d458004c016104c15000300034802610511400002442d403044420000a5a025015001031030711500c004c03502003011f4001200082d4080c0400c10390312640d0340b42203d0b401c1000d03c014070300750458461300c00c051140d0b03034210103040c2c001400001d140c0c8200840c01502800000c480d07005e04040c0401c60192251114160b070382400c1064002080d9807c034046c503000399050f10f0700307000601319005000c41c4541c000021015801003a00c00802d0752401e0155410b111003000712140c40b039500101c098000c510160406021380d028407520340000b801c000c00c59071051030155690101000d649030950113481070700b80090a06c1c03900411801041000005071060340c2c0302d03040c0507090203c4180600402072892001a2040314034070141c0b03c440e0800c59910325007500010503100000340341c00d50b81d08441b848403601c40c00e010341080100113888c0e204141c1f50290071420081c0c540c0910903000180140405840d0701c12056941010a1059079003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 601600098 1250 601598848 601598887
    0x303040602070519030f020d030203010f091d01020d060302100509030d050c01020c070b07030e2b060e0a0b061201060614130807030309030213050402090a05040822090e010e070b 78
    0x300030030720700504c198540102080d00c48a504809407146603180c0307107024081e0080d43c0c140c0350044d000b424454a4400080040e02e1134410080d84030440309510a0601c1e030030300040200503c401400703e2450300d0b40c07041c00700c0e07038128404002c1000014054103d19070b0300841c080450903010702d02941c0b1688018203960091041d601c1d00502c0344100f01c000910008103034003030b001c003034084d03164010000f680c4800e00050a15001811904442d1200050725100201c0d0b480401c4070700504c000030307000c0061980700d4038029561b43e003500c0400c82130041000920380824502c0051481c9002070091618110000e0b240c800c0307060302c074a060704010070546400545006075000501e01c00041741c50080d0f80b0f00f400307050182c007804223034055402c034101841031000c0c0d4014940541d901600311011a690040c0c290300424025000701c1d2142c1041042061049440740508074910b03014103142496481c0051140490701201d52071751582c2d0419281e540c08203c04200e1004681d68090a6641d440141e48800e10002c2c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 601601348 1250 601600098 601600123
    0x30607110106050d0f051207050a0f03020a0803010e1006030b03030901031a0402040b0a0906050703052203080d0b13090c0b0a020f030d06081608030a0c0507050a0905220503030406020705 82
    0x40e121903182030290100b801420140200c00341c82c040e82d0301f964a01242e1050141c05001984104603010000300707954090b906990207441681c0388803000fa070b20303500180c0c030a03880f409410b40410181b0411406a9101500609007406c003000a19800b0010986030700a41218506060740c62014240000b03444024000f4604001c100310755460f1520560495a040782c00f007000050340340c00700410054044d0b42103414541c0c01d070b06c0c0c80b41840000c618024440c1007290010000d50003c900000c0020301c200054211424100400703d0400014801d100c09104804402c8400d03e04001c40240803545180303940d41510102d0800603591220070405030b00c0c00030303211f141a01c07512000882846003090765000100382d0f1404410345030300340c00700002c0204803c00350240101c123070003c10854102e5070180103030850b158401d40075100c166541e440015580e94041c2d008050b40c4d80c4550400044820301c800c04c04503c0811f010341c1c40c4281507500e4940c3d49020082000388015800540c2c501801801c00c0a26502c24 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 601602598 1250 601601348 601601359
    0x120204090212060f010b2b020705010e010b0f011805101e021c0302210709051801050a080a0b1504090b07020f010f0c02100b01050f0f1c050603060711010605 69
    0x4000180655032000100d890459804e042c80010481000c2c8504480c0700c01d9500c1410205d0124810003a194440d0403403512840c140e0820401000420078081c800d0701c0d075201000080c05002103801d00000f04002d1000d2410040c50744009804110101001001c0d2001943d003002e403440c2c511002e6980e28507901000002c01d0115460302400c3c0d500042040070001d400c0881001480c1282083e42170340a810300059081e0840061880d0408050141c16400101454034605941d03a50380486c450345c02c450740d02c02034042058018051400d004540400410840f801400b680c0768a46940c4c8040b18003920200090042c03241c000804da40382d400c212001504141c0819031802e203104082d55880030444d4102080d400c00c0741c9000741e004d041c843d04d580345c413031a0098050424036070b805400811103180d0b158103200301800350381c00c9401c00e00c000d003040c0c030034291003c0e69480401e1204030300b001102c4056000341d810700c020072103651804074940ba003005044c03d1411903240350000c0c0c40e001d40300f1500104c1e00704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 601603848 1250 601602598 601602619
    0xd02090907140f0f0d0c0b070b0a0e0a02010c080901030f1a030d02031305010e0411040b070525030305160206180f0a0b160510050c040e130308011202040902 69
    0x200895070000311100d8441610325007a0100030f000b0705411108009910030703200c0403000618208003454080642c8030703100a450f020740b01c40c003078070a40c0c1100e1811f82e480404070080005044480c81407480c1200a00e0080502740c04075400200b4080132f103c0d00504d440404038129845034001d0308041c2143c3c044020900407503000f000841e00d0303144030313210142c82480342e0b020183e88540084100d550b0301c41059146120070b4282001941e150141c450803a400c0b60b42d525946802c1e1010340041d00140c40100101d5a4490341c40c10410f244c42d10380e404220314040c000207911008890078081c40112030341400c0c40f94442c04270140d4070005071224000650044030004400420b014030300389403110070304c0c00c44000c10303a100090280030f94070082e030080c00c160207000c005002071401140001d0504d103124000700c075044880303060580c0550f20291440034203030703001080034861201168016548500440c9065040e00900e40340100303801410703c54010b03c009000e0b8290159151034104003032042d0041e000000c0b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 601605098 1250 601603848 601603861
    0x14090a1e1d0702010b0f150705030d0204080c100809060601080916080c150c0d0315080f0a03030c02011820090c03090c1c0605061c031e02030f0d0b0d0209 68
    0x507411203000005510b00b1800301c00c01c1c9000780509044502c050b00030000000c0789650000c156100001c06d031240d2006208183e051030090008101828810010b171803080c07902c0c0e0601403000709040304001402944000c0090580c0b0004001c0d61001c000d01c5d081c0040d84401d880309040c010100c0e00344010300404c00303001c540803c0c002000d000103402030714202c41c0f0316002d0000d4a1180100300345502c56070050000c40711800e00c203030031414520ba18280c178000316644d542d0080b03152540d62502c1d25200d0701310090300c8051581512400040a04600091005840b20700075510400b1041100a01d00406880688a41d0201e03160245806601a050314000d0503d030303a03e4185900125104d0490741310b912684903443c2070141000c404e00300002e000380803000c410303551240a04001011540c11001c5041081d1030440041800741041c0d010303031030740f0f1440380381755003540140d050001010003550300030071504078500d00140c200c500a09441e07070006949403ca5001500c02003681c0f001950041141051191 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 601606348 1250 601605098 601605149
    0x40b01060e01030209130b220e06062e02010f02040b0702100201060b04120807080418060f1d0901020f030705130e040206030103080309010e12090114090a1e 69
    0x1a24000d07110030400795207000044090340700d030007000c0350403007680c100e03800850351716801000607410010600f0342814842140e031300c0741c40700c0403441c05104e03901d0741600843c480e414001d40350003240c01d8a450228154000300c60255050014080c0000d031034207642c0c040b485100b9880180f03078410180c0301b55621a070b0362512451903000a10160712500059126207007a5005108010848415410250400e40303070031061011120040c8003520499410030140c00018402001000074010610290018104542c03001e03088039200e8006445156503000140100050100c00308052603415607000c4003542e403113100f980640110210304031441004014005d4164110700030b00072a000078500607031030b680e40d05808482c03034206641c042c1d0031a800300014000301d0300b0b134001154004d501500100b010a02c21076020b00d000e60317a19849500010100e0450080d6030b22099850380e88129403000e40c10074684d20000340a01080b44944908460801c040000540358034003403000030000d0b1614a100b8200c042c00c2c210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 601607598 1250 601606348 601606351
    0x8450703021f1e090503100507120b0906060a03090b01030c060f02210c1c0e03011508060601030b22050f090d0c03030b010311211e0708070c0506040b 66
    0x344203a5503103102046002c0403003492419206103544020503114001c40491070942d500264404026860b00041801d84003005414900104840f0010301840c045800418001c1c80c2200d0600c06814000350049550319101c0c21504031070102c070b50b0743c0d455142140c194000d006412000304038000d08000002400402d0101e41d084415940718080000341c450380032a00c924441c40c90001144d001d40c0340d01743c800c210b8005040c0100045089404203840542318000d501a038010250014001035800e10075418203000c0e4803e074000c2900321680c00c0382041e11850711000c0061810781007556810008417070340c0d2900d00d00700e04120000a01c0a881d07074000c680c8400b070103040b21141124074030000446e10714800040c0c40151496184d03500701c88941e45aa0490242005441c65410161107603a00c0d1180c2d000c0070002e00c4140c02e88002c240c14004031100424104c0d600502186808200b201141c04602c12191000c1d4402110b182c00e03001550344e2281542e545072a44005001d5102e9501004200140c40440a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 601608848 1250 601607598 601607603
    0x3061a0315011a0319051f06050a051c090803070c060c08040206030f07050408070f031a040804150309080c060405010e1207030809010609020c150708450703 69
    0x11030420a051019003a268020b200360a120a0300c0d52030038044203083d0000e5500003041502602544602c00c09800c107031101901c0c40043c24050321400642c15244070200001000c160030309a0411494078030142050183c03c500125000200281c84c04007001d0b644140d00c6554000011526410070b91001004108e032118121202d620f05180390900724003608840f482194000e008900d9507a0708500102182d00180003001800014440070800c01801d00050010f84080c81140802d5443d605145401d01d60105104c0350020104051101180c0d20400302c40c19140750100c180b40b665410714085004040e07600d0054001ea1010a10706048000030540f98080c0340201c00034428401e0804066440b03c090684001c801002007080000003802600315603488007a03107000281c0c81c0c1e510080382d420b903031200b84408000e400500c41e000c1c80385080c4090315040780b09407505d090649001c03000c1d0703020b6071a03c80e510118041749041115503880700400c60a1685c00498031000d2640140303100302d41d64441400308 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 601610098 1250 601608848 601608853
    0x1404090c030611181e0d050c0a06230405210c0a1205060a0b01082a13030b0108070b0a03020f0915030108010b041109090405070e15090114010806090a0603061a03 71
    0x1508198a8180c85c40032564101a5075400c48060705001c015800840e081d0489180c051407908a031071b40d85104170b020051140345c803001040320849405032350340d880410184a44103000d0109022540b5480a10320049007441445032000d00c10b8a2180d1802402061130b5520044000c80426500508124030341c0c114401c004498007134031100c40c154142c0c2c05d85418180002c07603000014012044114021100744088244020071b1010b1a2000d03506900c00c4010300e01d090300c408003c10400c20707491600c030b004042000c09015140d09100440c10140300307401000b01055004a00da006190664040b5a40171400910400c604242040f40c841243c0092042075010351130030f9561411428240110360781075405a034141d20b0a0842000c022881710301034030503a17180c03040700800314a101308540514002c40c21072154004e440402c13070030000c03c41e405800242c58840d0075000c04005036040318180360003140481d05d0146a6076002000b00003046240d1014040c02d0a0280440741c020520802c0519010709409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 601611348 1250 601610098 601610137
    0x10e010e0c1c0236041a0925080f160e031b0a050f0901030210050f0a0905040621060b13090f05070b04050904080306030313090e07050a1404090c030611 67
    0x802c3d0901424140f804d042051302c0c400190500d000d078002400c00031151001044640c1c280007080c07485d20110352486402808150054100702614081200c0074500e2a04803550701d06808484051031001e000324030031207101b40303a00d4500e0f4041d5000710300740c0801a080b074002500c011a1811700c01c683c402d155005031150720020409081a80401030000c00150000391541d00e50fa080c0b11200ca43c030491a820010207000a0b64054184801010240101ea5030043d001341000d0411089500350340c06455003c112102c441100d208079401e0041c0300e40c01010006400c1c018101181402340c6010b071013080b161030160603404104288010050b000d0060048460f07140d1103c0150000d44100d02403280e100e8802000100003d40d980c0042d603100c180501501c3c1050001001d081560703050303800c80007100741c6400c070740e42610b4070400c2144002c0c00c080390b00c4021185804411540c000d4944400e5004940326a81034007030005002c034010003550302240400c4124846154804650010861521411001d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 601612598 1250 601611348 601611397
    0x61008010c0c03050c0a05011d01110a120209011707030c031a011b080d05040807030f140a0c02030a08070605012102030601090207021816110303010e010e0c1c02 71
    0x424100700403225200c2c005861110b4600f034070720307401401001c41548207104101c00018400e002e40d540c0c0c0c03129000211100c4501c0a026800d651011b2080d6a680d0028040740e0246035000210302101501104016603800d90381e0012a440510000200644066407062054482d80340e404940c101d01c2d02d6908020564800a541d6070700095003a0700b5000503443c0d245144d8000700100442c0e4440c0c810f090491800c04003151413425901c04850030740381d040b4046407840c02e144c0c10600b41090b4101c10703d400948001c0c4560780b02d18900a0b4010201040041101b81c0b085440401c0081504ea03041448130703844080d54030300400545003d002d41802031521100202c032482c0000e01c0700c000964000c0c05491503030300b40100c010094100c510b0690f4000c1017818514100000f0a00541c015400709e01e40054446445801070300601120402e40c0d180d0380100b0040040c0c11991800905503010401320480b1901d6207a0f114945016030780d13100040249646842c0f8100d030346603008020396409112003d15545640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 601613848 1250 601612598 601612601
    0x90a080601050604090528020a09060305040b0a1d01050f06010f08101e15030603060b01260a11030702060708180c04090c09020708031009060b040e0702030412030206100801 76
    0x20302c2616041102131105100004142c1c00c000e0f8807820060a140f2007079101000c0401d45048410700035400e0394001038014110741c1c01030050010300100e0070144400d05107503aa00c5e90585c40102180c500c580d40d0701175180c050f95520768020110401c0002803040342003c5160784401003056030103d010442d58480e00709010701451483d8461160300c050915546c1c03504401500103290100342d110740400e0148013068586620713200040c8450b1503a00002d003a415840d1400848610011080c184000490002c08200b000280da40020501c00c64151b11030320303a5003c08010740850180c002460340b0220070048443e5002509034407888441da160070036030b15039041030729052044900e0140103810102150486040c2604014100d510441a0740041580c80381600226004010f049030340c034100005000525011020b83c0d405130503c110104015441c081c0340c103890744101d1066450801e000350004040c14024020b0700c1c018102031005024a00c09450000d44421044440c480c144205010216200805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 601615098 1250 601613848 601613851
    0x612060e040b041e0807060207110301050c0f07021302030112050106060e060a0804020f030715091e0e0c0d090803070f0e010e0d02210f1507080a0509011808090a0806 73
    0x4019803080d95103d41e200d101c04803266100c504043c40380d22074010001409000104009809400010f840b2000c0b4a080c6091141c0c100859119a04140501c00304942c6001181c3c1c0780c0c006602c0840c0c0e9107000c1c1c07010138007001c00701c04c0344049644040000500700011010b40b40c200c6d44554000c105442e29680c040d11000c1c01440341507081041403140c1d001c1a80170f2500150001c0c001803d0210168403240080e10b00912030304084580300382e00d00740e5000203400c031036030070b028042c0d8a514076a9810190521031103100244903120b4440f1901003c540c0042180d400c541c5886000306c004e0001c3d00c000d00708a078080d03005451540c000b44615010007951031154180002c011016910105a8a402070810688004034070050ba400754400301903e03820740b14100e12160500003200031b4080550a5900725050a074640314080e034010003401000820380d84400c80b20b500030042c1130b0008803515541010382c01480551281c02002d035402c3c44c04028001c0c02c41c090000c14408503547e03940c1585680510703844050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 601616348 1250 601615098 601615103
    0x80703050607050a2a060509030a11060103050604110109030f240506090c0d1409060403020d08070203031b16151b0804110316030b0f070306050d2006040612060e04 72
    0x2140c0345400d0182c1109441540d031311190460b0040c051417291a8401100c1040e06c5402c4280e00c0080d020050541144d850400001150041c00b00340d071554481e13940341c0000600040c10342103150f00324821030780a841c00c80d0207036801c4802e0010003861850300c4000c401405404094500c002892003224018a015951048c0400b5200c03070010303142c002102e04039412203108006990340360241c030305e0b8181441710b13014410b1501c00020080c07402c00d1304019017048006080d402c1004102c4041002d0382c0e800104590300441803581c211086502c01420880c01d014040c02182140307165a071071020f10407080108810301c12007840400c2044844a1080200141a1509804075400d0b00014011820705403800e100200040c0030746800c111180100c600e020b6190300100d412543c05024400c030401303107a240c1d55018600b420f00308007103410800015440041c0200003000c40003c0c031011100b12001407601c0200ca20058090390710b0795119100070784014000c10501c1415427406000041c030a07500b0040038010364 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 601617598 1250 601616348 601616357
    0xc0102041406040312030f180b0a0f0504020913211701050301180206070c03020a080f0f0604110603191107022e050c07030512120612031b010609020301080703050607050a 75
    0x809203c02074004d400098480131f0300a90b5001c092081003103041c000070a5074480e88076030320145401424142229405004214820f2402081000513156100e20582203908070701900114a03075868500c10081001d000440d600403041881205690014142030700f100f0798031220302c01681c039401071500301c561184140107103258112000c0058241040100102c0d07003e80041e03103042d91a500800c134540f41c290301c001c10580c0200b072a000d1101c01030050000b00380d805805041c0509240d102c400031540078454251040070000f000c074840c1410705494103100e88540340c00b801800d00d102e922000980040308142e00811501003103a034400d220f16000c882654807100541402c100b10101124150030070189203d15100b203030004030104000b000000f05000d134078140c2c41c0c0c0c1e6a034041030316851204003500d540e0144034412001a501c09020040e65222440c44c02d1014414520084840c098000d60340800000c0b0f10000000c5000f00c00401c40d0341c10349015030100d940640f01c841c012240382c4201d0440c1000035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 601618705 1107 601617598 601617623
    0xc030616022d0d080c0910050c06040b10091112071101020313060e030a14030907030c1404110f0406050706020906030a050f0109090f23030c01020414060403 69
    0x80c20f042c80c14080c1340c03d1650400107240030301020244119091030700d00c0d400611a00541d44043c44080031a41d803400c060406100e009001e07505111038440441d804a4480b0b00c6005640484826582c0305141403200021a850702c00064070000401a000f445140c0800d401d00145024000c074005010340343d841c51070030b0030482e4000f40d149141074006222010000f40c2107850f268000e920035950560326508d04145a062440b682c000800001d032805022881041010075168001c1c400e41e0204100c04942e4211004c070301801044510544081205004041c07041020700302075407003410054100403281002459681003101d03003103481a42c840400c209014021003650042075414005c201c41c1000d03840c0c05081c14003600c0050b180c080409003c5124000180905120224440640c0c1d1150f541c403201a0103075103d031180c083d21308421407915000c3d26148045a007100c2d407010b043c3c2c1d40e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 601438848 601618705 := by
  have h0 := BRFrame.cov_init 601438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 601438848 ≤ n) (h2 : n < 601618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
