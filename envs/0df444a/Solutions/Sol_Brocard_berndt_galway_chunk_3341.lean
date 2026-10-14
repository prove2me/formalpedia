-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3341
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:22:34.44885+00:00
-- url     : https://prove2.me/submissions/670292c4-3d2e-4826-b671-a7ee04f9481f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 600719424 ≤ n < 600899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 600720674 1250 600719424 600719479
    0x40507450213060207290c0c0d0f022d010302090102030c0a08130803090a0e09010b030106030819090509010302280e10050d030f050c0111030c0d0605 66
    0x1030366090010003000503503408002a115900482195194a019545400c500b03051065a026000b4850000707000803850074054604e80340c0ca41601012600c81c0c51201701c03600304e204190302d84e00c0b4050070384001d9102d80c40403a44440c01101440a43d02c0c003841041811101c01034085000001c0003070448504400c0300304000f00c80c02c2401d02585441c00e04004074658001c182d03c41d5040c0c41910401410310030ba85c402454580c8158224507540fa4440c011250740348142001a80c212190b540100020207554031002e4214480c40f0011520b02d440c0b10000c7d095806640081e51480030000c0c4003041c034a0580c40005040c2c1da5824444002490a4001161001e0511010740112030042e00000d4041003103280c1045592000035110f02251a24003040500800319000c04035214042008103103443c0c44509521280c2c2d03d55924a0146031800c400ca40540140074104030540d00c8040464034552081d003d10b10810b4020b0301e05407038030844c80884090320002e6028900440306415080744014804174403c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 600721924 1250 600720674 600720749
    0x606130c020601050f010c06060e070e03030721052101060e0111340e011404020f180a080f0303060306100b070602071505010306090203060a150306050a061508040507 73
    0x190044600142c0e07038001d0031f040082c1044d00e48070002c0b4034030701c6c3c060006018014540c2d52400d07208941050554a1140010140142400c0444c0401a200c040181300010b51305250140c140000d29844d4198110300000043c24201c00310300502c01d2643c406c09500c003a030024030300014000080090a5100e018444001c402140000034104c90b1240303070400c42610901170000401d599640c1d841461080000380980350783d007008000c4841d16484d2a00a84444168091502e85803960b81403004d4040241c1c545060b401082c00240014100001d103c0c581c1c0001d0244003a46e6a031a01200701410208018420480d4071300701034041c068418050b085d60103050307006000580d50240c500300303a80c0215003545101450340c10080003108001c11600304d055003d00c03c2d004c80d113441c1c42d03c602007416075803c01080300009440c007000b0070214907940c004540003249040f0000c0c02c56129401e01d0800c00f803150580b40854100014042000710801c25003004000200d80a02c01394141c16034580b1201c81d00c42e101c1e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 600723174 1250 600721924 600721939
    0xc0712030e0d08060f0d0f0f230d05091210020c03040513060609180f0c0f110f030306040f110a0504030c08030313080c0f07030c08070e062b0b04050606130c02060105 73
    0x302005140c1d04400c019035082064808c40c40058a0b007090820040051001000500d002c029001d00300095928080201070310351030306048650041c0700b9003180000c580c4c4130358400d0402c2c1080164140c402407126483c914090340da102d040c4030500c0240a032a5010100d05460501300308003843c2e01c194810191580c403c440c805c906512130100000d01100c07000c00340720b00d1a000c1a00c203140d401281000348406c1a03140e0307198140410304000c1c0c5580e085140e81c0780a800410004955252a6003c5021950043c0001446d0743c1050041c803429007104401030302286001809000f4441c00c02c9401d401090440300840c6540745c4103045040c20041c00344010702101d00031502c10801c4601b4003103644001080422501c2c0f00e540d0f400d050312100039521614220380103080c804501815202015403044002420401812800c40900c84040e1040d80d800301031041c1f2202c041d0b001443c16854507004a0080700140710900301501040740c014082900701d070600e03280403001c01744141c01144d204c0c1141d1007200c510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 600724424 1250 600723174 600723199
    0x31207080301050402130e0106021506061317070b0c0d0905150d0207083010030302030403140c03030c0309040f091e0c170105150f03070306050c0712030e0d08060f 72
    0x220801a01d40007041f00c60900c0c030000ca0030341e1f4002010040d0020701001009503840d50004e01009100d0702130042d544040d9401c0900c80500c1202c1481c0100e20f20500b00c4004035a25280b0220a4111081c114007580050301c1c56400a03902a04100140200315444003c040303900859013890b201e241c504200d0380f5004200344043c0002c1405031200112900b5001042c4000d00280721081400d40c108440e070340114101107401c0800481c1c1d90029290305400841c42c16045403100807544a000e09400074600c21000d10304210744043c0041d20808001d14015034440d0130b82020002510b40f20100802083e2821003032002264150340c00501201a84a21219801c02400c00903074407034143e0484061401004111070940d501580014490813100b4031000e015880b980400211701e001c0302c0d203181d040d80300c01402d1020401c16403105400c0b1010344065498920706960f01e59a040710488602c000c1396454030a0301c0010f4040c080c0c403200624a00e00540c00d460242c0c000741810214170f0100d4014003042104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 600725674 1250 600724424 600724447
    0x1d0105010305010b04181d101109100809030903120c011b0f050711040c110f06040b0621070e0702101b0e010e13050907080102070302030a08060303090904050309031207080301050402 80
    0x1040c094411f07070703000521402e0382c011607070b140c220700c0c0d560610302d140920b51584c030b5109000b82c4030a00f10040045241c1b00b550f110455460a0151480c0f4860200b01319100199030100b12164601a442400715200c041c0001c60074219012008803500080c0c5044101d074850f0391007400c645a080d241d041503504c445050421110440583e02000e030014070f0020740f072820715005a003540903074115108480404000c0c1030102e803652003d80b401080c1c03201240100b89030340b400c0050442c00c5447c2c61000050300780b5517401d043c6007503120f500115241d8620b1081c42009075060000220303402034540244090007146995003480062041e1007000c0204007a2019080c0e8420a540d0580281c010700c500d10404050860f00024074050b030394007039903100303012001541d64018001d4903031442d0540c0184d400e104810109969515004008981c90b0208004820156469200c51030055000e0001951251182d4061520300805a00c0c48004490705109003400a030017041128107403042a180583c907014031440f0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 600726924 1250 600725674 600725681
    0xd05090d05120412050c0111040f0f03230a06090b040b070827100f0c230d02090d02131a061204201003020901020105060d0f02040b0310061d0105010305010b0418 71
    0x1028991b9500749440e00c084001100c025000b070302c140c04101003135a0390715041c0e440005042d10004144030351030b005880d044040360159500c5c2150410645c0e8085080d6600e40e011100e00e104126003000701d41052000307210784181a260b119165041c040c45500f064a4118660400f082c545844403840c030250743c0b00303003609200c4941040140e8009200d40e4090741c1c40d030400b07011002031000008180480c060100702d01103030a00305100c207110045141106000d550700180d84039482042c0c00c1a41455a4001030b1913030b003400c8001000e05280061007404500c0e04500481140b0009032080400703214880c0c46e6030682c500c454200764045409841400c080c5400c0c01c0c80d101c8440090707071104102d040b26050680503001032182c250264000c201540c2c0d217008001c59205003407400b0348508400d00c085001170429a100034003c400080c01c030f400c0c0310704818024007079980581000c840da4a00c00d82e080000140300140c140900001d007000c1c03019604080c4030318005d0050384103035210320500c030500c00c0041801d03070b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 600728174 1250 600726924 600726937
    0x1d04020118030f0203210a0e0a050604060c140c031f09050616080f1005010f0c24050606160b130c150f0e10120b060d05090d0512041205 60
    0x1407040d40c0c81582c0b401c10501480c20b0388016070080c0102e0781c601000410803d10542c104a03000f05150410292010031680c502e440c0540c9030b007003032941c4070203e800d0751040041c000a00c002c0d92483d82543c11407503e02c03406200d1082203211503210004840a03030342d01048664121120704046407500d011812090040d1041d0003001c0c00c140103580138040d141241000119810101c0c0c2c03108001501d03084a400010b001c100da1800b180750160106004ca0b61092400c0315120307002c2d191903100800c0c1504c6490b082c000c18480741c103801c170412010400e0105140651075100a044508030b0400744290b550200205250300024070030a8140000b4104880201211500b10342020f81844410788400140c00c1801d20082a0350205000d1035000103110b100d098810b04043c4050003e1380c10362115031023921b0601e40b1a17104003003113843d0070300c030440c1d0b89840000d4805561358003000b003141d0404080960621400902e48002c1040030490a450a106920950303009a44a94102d007032001e080d030102c0c4c09000b0403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 600729424 1250 600728174 600728207
    0x2070e0c0708120408070b07170429070f090503030306060904150806040309050103180c0303030c03020c01020d060e0723160b131b03030909020903031306170c041d040201 75
    0x9401380000d00c04018040c000141c8180d00c00c0c40c0680360404144c8100d560685180190b07031180300010f0000d048840310518120f290f41f003131245052074510764000300c0c2c0211895400603600442c40060b5035800b041c003000802d03080e0090b42c0345041072800f00d41c1d54802e01040314041c6072200c00d2503050180003503d8800401c0c040040e6007803400d2615000701000f40314492980041d080154000c0400003401e040041144d0001c46200c80c54a16a015006003004100840c18561b007031000d2002103800303000403d681c13440094002042c0b401c0403148940e104016180008002440c40102a031401030184600e00d116482c0748542c841603050341e0b28044d243c3c24580100100d9a0005118410000c28030141c4550303c910072000c413031081d9007884c803503001c09440050002407030030303c2c10080d180096009114042000d003e03039240c08074a035520f172024404d951000c000914150301300800340e1001d0420035004058170016504e400d20f80302e180f0025030020400d10340500b40c10341c00328045a01618210380e1a4254 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 600730674 1250 600729424 600729457
    0x9031c0c20030d0f020a020409021c0b18030a020304120c0b04081f0b06070201180b0c1b060406090302130603050118140102120f040c08030d0b0f0102070e0c0708 71
    0x100603105101ca10000840d001e8442d09001e00303000b500a80740244026544d41c0201049841502000041c0c880c0705000c0c0d030440366068a01e141003030498100c458903409050b1a90348c0b0b0a10003d04070b61369008054030074407908284500340f145940071040718121813019107089241f180038101808154a82c0d40314100170310001600084c0c10f02c0100710a0400342c0c42c035840c803802c104143c1406040d07408006130a54072003801c006036401580260f2a070076030a6a80601c04450607201c00b80500294440103c084440c0e0102c045448156111808118024002e50300c01e4103252500a000d0240c08050000a1107040c0310700391480b110b0038a9100e2001903800000034818040f00c00f0345405200c40d109010342d0610589a48080500814008c440303400203900e0f2210704554500400000072071000d481165000d54000c40001e144904001401c0d00100e00800025010446000c1141004d0b44104103815500009820013281c00c21100055002c7c950401150740d854461908002d50702c1000f030840c3c4a4820f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 600731924 1250 600730674 600730703
    0x5090c041e0306050601030c0816170c0912030712141c15090b0603062101050f010e010510120c090506070623090a030516050d0210050c09031c0c 64
    0x74100090000c0700c0c000c071420071094681038011401d441c2c079030340b01d00c01003540c80c004188a64500b0510880f03010b410310f001340361001000c800d00c0d602d54042e542c50304000b002003a21035070361425955a00110085900540c44d00013550b48910b16001118211400e21050000c0210b0300701c0c0038000c4032011096881460702002c45107c03800020181c10300305030b030780c0e1100c1075003c01c61408620031641d0120b4010010750031552004200700d594518401000c1d01c05000b1082c2c00d00c50300c024003072640924106d4102031100d42c14601d0001003660140d0165210321200034128900c650030100c0442141c0c00c86001094114079144162a5406a075000300d800a90005410040c010664041c20041c041c261a5005074186540700c20425541a140400305030401144000024000c0005206001c0d510f51801c0703580134207850fa6130500d6829000030780035810000010130101214400d069100d0b4800c5015414a140000030030307907924401c45103201d41c041003160324801c24010b44071039001551065842e4100341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 600733174 1250 600731924 600731969
    0x50c0d0c1e1d0616231009020307120606232d0d05010b040501060f0203040b070204060b030a0b100521190e1e060f0a020304020409050601140117070905090c04 70
    0x10681e0095940c111820100705101d4000d05018420745d168a0040c00e4001100f0502c500624001804a07070520030f49038001903100d21190001c61680c010300c00010003900d49101500d0081c0d540c0050711121041040c03580113607560100c0b18190250028803a4400f440c500300a04410200c4500103500090b5510300340200201500100e01060042d501846503980c0c90509075856404403007442e000d03801c103000034005884850060700038540000c00107d02c07190b64072131629044d0f0091701c146020756141c031904100ca0030310300c000c3d01c0310340304919080d0b20385644045500340009000c64a060304d8080c04000c81c6031809251480040b42d06448030400060744950f012a03540e1016006484d00f0003095010045814008104148246203250440c240c0c0d58400800e50000e610080040768070654401d88440850000c101440c044c0a0700200e005c41c05102800141104403442d034203549030801a02004000c2c0d500403040b204552003a542d07005a515544089001360107140c03c074800710214a4110345844 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 600734424 1250 600733174 600733207
    0xf0f01020a0201140601090b030901183207090207030c06050f2212200703080a031d100c0203160804060f031a061c050c0d0c1e1d06 58
    0x1240729030002c1104000c4183d503086114021a49940440e0201c081080b6102030007000703590000b100000010315030403e604900c01d003c480c90f400d441d50840e03d0005a107466108001c400640300b02e8400c07840c0304019940300b40d0341c0c0d11140115841c0c0c540102d0f0a2003090b010b4410a050168814410702c99450840c02c035485d80d4004941034402621021f910781c80c1140c050f44001c1c3d40a03080030300f84001052800050341c5900e1a00c0032070708199520344442c04150341c00c0c00079901840c42462040c0d80c0b03405522004080da00208041214610340003c4203022150005105994101c2c1440200c2c20205c030980990940c0103183c0d01c0c0c034480805609810410001c0381c011300680d04e46464911002036841c01c12012500b00f03641c9a020041640e0b001c040910f030110180c03811200e80003001c0041d4408041c01011b070b800945041d4007030740002ca040e51030803500b4028901c0002c0d4074900202001c0c030301080240490803942c00f400500400c503038580d03000b102888413115150005040b141d03407070310113031b007040e154 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 600735674 1250 600734424 600734437
    0xb061e100c0b040b101509030f0c0b0a0801090c0302040b0403020f120708100f0608060609060a09020a0c02040f0c05040308030a0f0c1706030c0604050618090106021b060405060301030605090f0f0102 87
    0x39490965008102542d0708854190400c6c016612a8585800c1d0b69074458064100300d016104a1141e2038000350592000c0003c18080c050703969224000d500d400f0000098800010303016003031500500040c44213450400c182c03411039404a135040d08040005011031a904d246d0f1580074560300031000003041004000421803548440a501004202d0041d0132600480301640075074201a00240d010441608d002d000840d00400020182034003240d40d404040100e80c00700544802103041c0108d81010b62804c1e20801c440c0c240c005c00184203020f0700d090020424412800300a00e424808000324a51405035400a4172665048008000d0044500d50242844152956000c516600c1000081c1c0d1824007040744d907040c4c08013038030036420281808100f02650308440c24038501c5400c8001d04002903907c0e400c00d43e00034007254000e01041448001d02c0802003200c1710300540a0041040200003a17181c250407641169080354002506484114046041010021078000b1612501d450701e2840c90042d80105030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 600736924 1250 600735674 600735691
    0x18060c12030907060c0f240e0d140322030e030106030609060e0d020601060e1912030f0e06030705070f06141503060411010c140607020a0b061e100c0b040b 68
    0x8440d91907500f00c07400324182000a000510038100000002c94001402a007c074800c1c420a881c071a640d0301307142c02c5840603d40741480c1d6014008603142035801c500040302d2031085400961440c5000b0031000100b030030440013461014218803240e000c1c14800d003150540103038014003e008541e0341303040813800703008100310546800b440c2080000b8402c0000503800701c405070316006450700f030780b8250094031081e0100329500c0d0407644070503020f007c0b411550058009051444d42400d000000d07410000c0000840042007014002c03e400c80320800e0340c3c0d50081d031364040514580b00d40d5a8510b49049411002c44000040005040600c8000340c040c0c00070080340b0890345412360241601c9400b0416954410913070300035100403007084140b4070382d5200c1c9080d003031194011042003423400503501c00c071351400c174003203d0002c0180c2007030b0039404c00c100700c0399421500001c0440c3d01c80f0301c106d04003888520103180105020b10a140682d40035030203a0150240561483d00403a400c80d092825082008001208455410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 600738174 1250 600736924 600736933
    0x3020415050a080f0703110d06240903110d060e060702010b03070e060603040807200a0f2601060807060504050f040c050f09060d020c01020702011e0518060c120309 72
    0xd62180c407550598003040e0b00e9030390b0755910f9101c1c006100800c1c0c0005d46194105910f0300e080e03003080d40050009044070744082a001551074980903545440041e01c2041440b6021107013201d4a11640c05682c40e0292908128010541902d190000d0491145000300918190802100008516000c079a03d840366050b50000d210710380401e001c041c0c03250030b14020104a28034180100d14a81045d00256a120f071040421914201903600c03508400301c2c4c200b201d40c1c215110100c1003680c0e4100740018030000c1c92900403104189003481d1050b1300e6040d5410784400109101e0080d1515544250061740040500c0c07815900529200c03a00180725510a0107050b0192520041c28086420680b04010a07080c06580d44c60400f407002001d001c0d158401040f8070f81c0f003a81840382d410004028401030010070b81860005940d41d03280c0c8005010048070485030360061198101c124a01c94101080310040714010a103da07503030020800041a600441c1110500c40c0300b180c19071650040300d01c0c01107010700d10315002c44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 600739424 1250 600738174 600738209
    0x1e01031109070203190c061409030d060906030809040b01020a140c0102071a03010b0a0504030b131e02061b01140405010617010603080a0f020a212604020f1503010303030204 76
    0x140c1e40d81c483c0080181164841c005c45001c801e10421003020118810503010414580c0400e004c1d88104068070042c000b0f400c0029002550100c0d44030342d1000301100141409402d103952902000c40c0906400c0900550f141c285484103a803007803141c0c0d09595070003204810640c41002d0000c0c0ea5455695500d80988034005c00454a024160b15101e0038148500105180d0782c28001d08081c2504000c40382420b0100c00d110100c0004e0100c08072912501d0310344100100b002c0c20b41010324120307501112089007006101022005038441e0000c44920203043ea540074240544100306a006101d600068222204000d081c8410030006402c450202c0c1ea5800c40c07100e005441010150807a00d50707200041010504000416601c0c2c0504001f40c507800f21801600e201c1c40b410b0701c820000071000d003048042d5128a107803030b82405800004041d514070307002601418cc1040021201e002c2e21000c6c2c006803148011800c5460f0581e40c0e08800d902810002c600c89440f540e403441c01802a40203405410a03864000280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 600740674 1250 600739424 600739427
    0x20301051201060e0c1b060f4809130c020606031b0126090c010206090d080a0b0a260105070f32040b0d06060315030b1e0103110907 58
    0x2007034255400709800c0c42440d240c0760f44c00021741d807010308006144041243c48481010041c800c00f40b25000d021060441494440094842d40ca80c05600c800f01c00c1c9084c0c20321401d000300000c080a41209913243d004c2421003020010a280203003040d190344140d0b0881009011545900b01c402d40712159022076101d601c803002019247c600248090802d0556202c94010381d604c216009800080050311441c4492840c1d182c4403080f0204a4400480b42d002144044440d603041010716800180d0f0b00181607101c0030118000d10018018000314082034450b400c80300d50344e9589030300100512100918020030620411024a04100004407541075441d02c0d0008110502421030340c0800e149a42c1d91a07070748002d68440840b44410401c0268000d10600082640c050303c08000300090885241c1c00d50b00c8040c6e038040c0205903105900300f0410541040e9114000c0751340065801c00382c981c010403020f9075070756040d02012040341d08030403500e0f550310145c000400d008800e0000c413288802940d1a0a0b81d6a40b03190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 600741924 1250 600740674 600740681
    0x10902090115021b01030f060806060a170a02040209120102071506080615130e0d031d122b090c0602010f0522140a030207050108090a030e090622020301051201 70
    0x4800584c100f00d025007800401c281821241d201c05040c005900c0b0410112041161569000302c0b4480e40a0828032110707140c0f0302c8043c0001c045e07940074424001e2000c0a0603403600342c0d08500a00658000c58803003401c1e902c07004e040003801052070003191100141d050020003040400900c1c07001900d00903012400031400701d4014490f03400d041516a0000d201c406120074a003100a00b0304500c2d40e0fa540d074041d947e80c2440068940040390343e020030100c040e0341044c3e8401d00041c80402da02e0b80304800700498040000152040f00d54041d0907000076210060b101d1054a503103420301c00d019842d1442d00010032035061006000c0d56607941c02040240c0c1b6001c081c00131a54251070403800d5000024540c888140e8000200159510440da00780d2a04211511189016944a0120090b0f04001c400703110950b48080050b500c56074031802854030044540700a81401c0c20f03a8407543c012608400011159181e2060a03107140c980b410003880100c64a00b07020009402c02c0c06850320902d140040401d01500502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 600743174 1250 600741924 600741959
    0x5070c231509031306020609070f0e010303210905100b19093206040507050a0c03080601210501030516212907090501031b0e041d0109020901 62
    0x50001c1441d14100401c110380060402c1c44611080160085480c4550003c800800040e001000203041c0303c05c009040c006a600401903152400e507040010794108902e0a0449402d03040c50840c0861121150b0034004500e2a1074500c0c9044c984040100400010b000003103840c9403d007001140c0d2400100151259540340400210310f075200c05220742d500c1540001d00d406443d0316242ca01007159174108403040108a840c0c4d082c2c003c41000c0003142d041901600340e000d1001e1500703034500165280301a004078800382c00139040092090002d041030b40039900c1d0000700292a410350008a011071408000341809003c212014014018011201005d40c00f0140a844d100c1c415034214101c031202c20202034014440c16180c0411401c0e01041c4005501244c25101c0000c0c254410146080407001c2c04820096200c43c2c10140b60421108180d1302c40c1142c0e400c11665840d02c01030450391640010040e020380c01405011400498040c0b0222005520134a0450300c02c2d54101000d0381d03246049003000614a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 600744424 1250 600743174 600743243
    0x40602030d0b03012304060612080f09010c0209012327040507030209090a120c020a060309050c280503070605040b0f1c09060b310204030605070c 64
    0x61000007400074003500304041c5954060700018185034048000c4a09441c08100c02405c0e8000000340001d101480c01448050400103010000f0440c2c01d6403290740030302c5080f00300b0f520510003281c4e00360560300c02c180c042c1060350010041c01a5584441034651070111406180c3d014185074510001107040000e00741d4220a1030b4101c010340b01412110f0091580d4008000b20741c1802090b4002c00140d87e2504e185000c0d400a40c001d0000a846107805080c0e40c003014200c43c00d006c03c0038a0700c0f0041c0e88500c0103c0580b041c61030081400c0041e0300d821841d04040c3c01001ea4002c60140ca41e81404080701c07412050394402c2c0101010f203580d07a409141d11203850b03020791800103204000511000300c0000040205214000c040c1c0d2034980c842c3e03800d0002450702c038101d101181e201c01c01c41040c05010300900e510940100c81280701c14180246c031281c034141c43d02c10b00c1c20b0f140007a041c1224044540c1c0c1903070000c5800520510007468500c0780101003900c054421510300d85a6224010000422003000ca90050761 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 600745674 1250 600744424 600744427
    0x32a16030507050402250302031c18020f0301020d0c030e0d080c0304030e03030705240a0b0901050f010215130209010e0702100207021507050d111b0d0c030c030c030507090204060203 80
    0x20f00060101a520a980e030107030001002c00d4542107113908400c01c0690501070b0303001e191a00e00d0910b0340d4020104203d0038481050400d14260248019940c425814590488400090641e14800f20740a80074118806242c2841c00000c2521550550400d0105214680907070740e4031a00454181d66800040d030701c406030100103000003000a07008101c0c40141207030080880b420082241d0315030f840c244160624066521590f0078507030701812442c0050784c211481039004d22650319031078086101080c0520035141701c0c11400c05200c07202c0e4000c0c02882010742d40790083d0703141ca01d0455841c243c0b603110200200d0203807200d40000a01e6803106c0041502030000d550140c003c000b00d503c0c076075001c0c0d0010303002a41d0201480c0c2461030301e030200a00825001d4403581c060304482c54803140251814092140803903080e040310811307a0015400c00766120021800f1a4800003007011424a131100b0301107030300010b241551103000442030242e810f0385401143c0c1b2440803150f01a40301c203648400d83c06240300b20301c0980d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 600746924 1250 600745674 600745679
    0x1050a110712020705030a06091205070210080a0209120601030b06031f0522260a0e01032a02060115030615081e15040b0d02031905032a16030507 64
    0x80c10b05076402007184101c035107140c1c880340081d051011100040340c00d01d90300c03002c24040004090407d401c003a00350510909025254001c180c0e446000e030b50b140104a60403001503081084c0364156100b0420282c100341b8485e0002581c41c0d0b440c2030038002601c410101c0000100740b89400162a80c6800a0360005080310081c18500700203084080e100c070b440c2e190703400c04a9821080014500c10308034000c09807160080314200140d02c602460300312017181c88078100f04100c50150440c144082c501402e2800140c0005042010740312444100c040710402c0240c0722604000d0356000030b10605840f07122880644032050840c050301201d081384605c07601145550f100e840c00d10300412101c1d070302180c803001e0303507101c02c12681454800841c200c0d055036001881079403130b81d5603007400e04c94004070f02c0c004c0e1180c07140c0d25216000a5900c9520441d04900320b0301d00300108081107018003d0721401c0409180f1245a00400040302e8440300041c044142c2c14480d020145560326840c0d0030500449801601038100b0a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 600748174 1250 600746924 600746933
    0x6030207060609020721050702031c1b030228151509090c03020409030c060c260108060a151d18060f04020103050601090e0108070602010c11030a05160b04060e01050a1107 75
    0x201c010701d8000f0b2007024049503001d4ac4050100c0c030f1044003801c46014a09010610141612040d00d4421030601842d19511001035000144146c54a03840307400028170180c91698611001e88011000748051640182c0c1ca0807442941c201c0240c0710b482420b4901d11507111206503084030200c140140c00c51180203810405810720b5880004828001d260400c0b015000c2c3e195503040c1c480a81c0140c0000b8001e04550b9100403603103002c0385060040080c24002949002049561b6171005001619010360f030f090b0224201440c20303642001801c10b4250760029808640700700355902011140c28450f4644080089400c1c18007003181d82c484c07803c00300f101c169512681c004500030400244020b040c4084840c0114034075004201003030007882072000400c6061f00708903000342035031001d01004041c031074544c00c1d03264a01030100c25a82c0c08007291401d80d407505001440001c0665007040040d01c0310782c1c044140014070107150130008039a02200004d010342e0301c070404010700726a00c4441d041140f8505020040004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 600749424 1250 600748174 600748223
    0x1170d02070501182c010503010e100506030316030306050a050406030b070c02040225050c04090201080c16060e060a14061c050a2306132415060302070606090207 71
    0x10f400102c0014030941303c0102c0c0d48044407407072100c00c0f501c1030881d919840c00d414034005c5000d403c05030f0083c4152710110080c030f0b1390380c0301030b646040415850f240000c0f100d4500b042a41c19444040c104960001e0080c24090002c0c82c560181d5800791448110200d16820280507500031241c0c03105501020380d8030f00404541c05c0c205404200d0703116400300000560100740c0300f0581c103018905002c1440e48041e40c41c00a150481c82d01c00340c0c0c001d0b07090008400160703030451a010760000d9649821607540f081100c6054140681030002040240751440001c4221000541c061040c54048003c02400030510452201c1a0046801550051038064201200b40d6500c10300f000300d40c03080b0101d800c060290742d25626505154502480324005525107800c03142c000b003041300e40050380300b5a4045010301c50384849101c0614000c110106103940140d060070301f07409501042400c3e0395107502c400072940b6000c0050280d07000382d800380c0d01203080c8440401d14440c0c030710844000e80d50000e24000003182070b40c08403444 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 600750674 1250 600749424 600749447
    0xc0105150a030624080d080a050c07030804140a200114040506070302070503010203040f210e09071101051915150c020d0606030c0e0a0203041109101701020301170d02070501 76
    0x11352604c070790160054480a02c041c40544440d0307003d8880441d01020040c01e20000800c558110342c204000d0090200b21401240e8001d074061420303c030b09648900f8980002c0031060328004681c41500340b4141804991282e0150309118092180f0700500c1000044a143d94046013803119403400304002c0009190040090621510074019100c200e0340e41d000090898102722400d445401c2c0c0104440c0410001c82c1145144c036401c9650355034580804500104801000880c0c18041e014840101303180301d001c1d103440000043d2502c024855850700c1c590240e03024010340050b400c4581070840700e10000c10b09280c1e0300c0668003182ca0501c2d183c021200200c8102803100360a9802904056a03030300810590700403c1d0281d80584101103406161601c2c4880d1a14014000e00780740d031042c81840001518050103034004c4600315800c61241d122443c04900c000410344c014504242c052303003400501c80d03043d005503040f102520b00d0180c41d00d08015486445445a240d542c0058207c42400c0c4a00d6001e200c07951130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 600751924 1250 600750674 600750701
    0xb03220317150301020409060f050303040f091107140a060b040207020d02090c070c080109150501030210030f0e0d0c14150f0c0418020c070b2703010b03060c0c0105150a0306 76
    0x82e2080c503500440d00f268021380181d0b09880c2c440c0d10078022078540c0c00c5801c006110550040d441c02c0d2401d20101400070281c0903001c480340e200c003603a5100441181c160351819070400505028044d80840c040daa0f07507800c1d041291740314180340c074450441c940fa200380d41000c4d4015121040711a1250700b00901c07850010900102c126090002101080f2103400400103440007400000341c1000c03506145038543c60024111040c14100f100500c0161122a8658071100300c50402256070f40f4a175240c0300140490300c01980d65445041555604c00b948040400c130312074080e800d0888201345020745070b5240d82c11120301d00d02145622001c2a03c0850720203481ba401100ba4255a0405855104000e0000030b4210000484c540200d0b540c0038011040c0114801800701341c11040ca8003586101807540310b500340000c00040760446040c0c0005840a40100c0d000c280010306070340311440d203410010115001010004c2566280c0b070006403044004c00c1e00000307030703000090461301e0341441e41e41e40304042e142c0600502c0c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 600753174 1250 600751924 600751951
    0x30506060d0c020f0c03120d02070501060b0c0c0108094306080f1014010e01030e16080d2109050a020307150225060804030c0c0b03220317 61
    0x460101c0d10721420190018030f50240400019042d0f2051919152500c00341c881e4112290341c3d940415070004031503501c4101c48003da110049410258010885944200000e031400036840c1108a8049a04440464262502e01003501c0302c0c10101d5498003054604503000180c01c0030315518100640d110904940c1603c01309580c00020602c118003016160300000216000c801441780841c480d0421507800a991442d0400c80ea1404000c40480340852005605001c80c000e40c42410342d22907041101c102c034841e800c540c0b001e401e1030403030740c505584c52090a040d40128041c041805101c1d0f115007440c58001c0341c001c00e090380d1038003818008040c1118115400c0c0b05074a440401030724140318120080520321103010150700035400c040d00f481081c0141507030450307030074582440505118000c0c40c00d659a80c64148250340d602c1c50199807136203651002800e0001039010008100c402c08006520510045030507a0101005100d1036038644a91040113001c140a204076428400e0003a01c90755100384186a0f11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 600754424 1250 600753174 600753187
    0x150c021b190f03030203120705130e090a0b180d140703050306040f090336035c1c060f0906140108030301060801090506010507021008160503011503050606 68
    0x5448031035070b5600480150b0404198003a2808003546600d41c001e5490a2403441d04940041d02e13115040140960405803200f6000f082b0705405c1009609002076200181e9101c50a040c003010762205601700e290302c564400c000f01c001e0303900e125900c0310130a070050400c0b1505101440d981620241c00040000d50090b545401c4104902024001c2d0071406010392036080d00d03417249200e980b9110190210080b84440f207040704001101c15826120110381d0011101014090405004900ca100d50001d404001c4040c49050200e0524100001a03081c8040714101d41c02080d460041415a40984120f03071103414500300b6500211040001c0c15554803071000014401c4034030250a04582d1001b03029140320b81d960480042c07640400b01040e000d400c03071070020f500b5907140c0311004000c03c030140902840c0b1a00e42c0702082c850b90142c07090300d2034994024510000c9680050000380488411a001c80c043c03a00074400c4081c0c680500b0450303040c0c0e0440401004407010698050380074250180c0165042401080038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 600755674 1250 600754424 600754439
    0x602030f030f2a0a090504020c030d021303050604050f070f15320405030f0c030d0c0f02150307120603120c03051c050f181c0e0d150c021b19 62
    0x19080f5001019000380c8407a03103010014040503841d088540142d04c100402d208000380001a1423201541440240e5144403204000c24007070203a520042861007070b0f8050004002003ca114412140c9100441c0c01e84c5607503150a10306542c251040c0c19918400d000041c40d0944100c0c2003100c03030b044504441d021109090500f4406961030784e01c952400340c0214090007186003d00400810500031402400c00340d0b14100060b884040036080c50f014803000c0e400c204100f14005412084070764004001040c0e18144070561002039104540040c0043e8a5452460440e2101c0c8600c00549410044e030303280808248800741d0355202d03c01c0c1c05505202c2c0600c0842c0d40c643c001c01c0948110301802401088900f03000b01c0f841e4000c0030161240e0701d42e5090108020481d040007503c040044010032032600404407608043d102131035013000580d0400303007001c0808103008a88220456502d950b110801411503501401c90311880d0b2003941c02c00c500c0c854031015100f8500400c1c3c0b12810b2039071144030007071360b036603143e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 600756924 1250 600755674 600755731
    0xe0d060e1006081005040503040504270303052d07080915010f030c0f030b0f0a02040e040506040c120812150a08010519050402060d0905030912160602030f030f 70
    0x2000008152280020b00c5a201c051103040903081d0000c00070305c850708059031a40d03105c6c003c81c00340501995581c019110a1802c0d145494501140ca11306180074520900f0000c01500044800402c40c0da000c2c120016903030f403002000f6a011b603818582d4020381c0c503070010842d244140504260007a21907078402124004003030003201e00911003410701c81012461072034000138990b801d500000396018960b00800104030386012542c1e2102c0e605912000c81d554016035000240136a80041514480f00d03020001044000035075180142d0003401d500d0480d554802503402401e242e0b2400070a0a503041c004542c04140000c08950080700c0c140381d00c40480c1d94800811a11511036206c3c150350b0791070340140451001e18040c0d1280c00e0802080501c1107207040e8010070f50307074420030406000c5950383e4412102031010500c291140030100401d580c1c1c21545c0c00701c48070380c0c0b440c0d40b0300800d1104582c04400501c0c280000100c0d030762015004595415580c40050000150400500200c90750001c03520100c1081403840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 600758174 1250 600756924 600756943
    0x4020d171e0702040609050c0427180501061a0a0318050607020703060e0105061815040f020c012403030f1403010b0307020610060801210602030f0105120a02010e0d060e 74
    0x1540c0ca0b11801c00d0300402090781c4080d803100800c0b1385450700b4090034107449411501502e800a044c60004881811080400d804102c4410038141c6464106280400103181c43d0100500134802031000d1f607264202c2c0c42d103003404007407040040c0d80104150103011b4007940003c0b200c10369001c1d5080c0000019141c040c1400400c5543c440160441d12040c4104441407180403440c6030040000c0005107032100c04103171000f9180014a51001084000800b2524070440c070020302031010f003041c0300ca1300c03920100501039044003100000c65400d01c1d41c0ea44080440d078101d015050358943c00d4820441c50350b102503c424052844400400c0819561240d0045d0a07400950007044681081990380c0340103e0020709086002d030043d001441c1c0f400301003101036032249000c0d065440301652501404150600740b64104009100200700500100800045c0075554071039504899040d101d61503103201c1248120307181d001416009020812514018501c0d08240c850350055511840e00024848400319410b841c000031070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 600759424 1250 600758174 600758227
    0x70206030406020306100e150c0f0d02010c02010f090f020d0201140304030c030e12120310030c0308030a060512030a030b04020d020c0c130e030f07020f060c0304060305060904020d17 80
    0x1017030181501b401c01c240103800216141c25081840c2c43c100060031a0008142413080b418046a0041002414011015128550703800c4490103041402c003e4007030b22070500184055440c1c400d980700320342001e0251002c5039900070700c1107030621055030030014501501c8500340d0400481d000f212151585020045014a00980700c81092550301d28004000008400e85940107031041009003100410025160311552040b46443d5129030365450001d1180c585980040c0201d054010700005000070355004600544100005200181d240c6090000e000c0d0403030030000c583d80c000c00980108501c20f6010703600f41c0100400241c07626416032100000d9800102c980c0d0300070380088070b00c803006203002d2400000c4408001428490704035841402900e80c00340c00030041131918005600411540c4d003013903415009800410050b210f203440034003269039401a00468000c2450103021506070b05d4502801c03442194001c00c005410049542d80c01b0240f0305500612006100501c032141042c8602c210029982e11030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 600760674 1250 600759424 600759427
    0xd0602130f0e01090b0d020909010b061201090b01030c02030f09030c04050a051503010c122003010e010602061e0c091206070e09100302012a0602030c073003090807020603040602 78
    0x2419480c2c52140c1e41a03025855403440c0511201c4541c442d007001c0001c0f00e80440d0f1004107680e4001031a4003500300c00b102d407544000700040d1801004085074800d41618109042000443c4801c8015401c46022400d5140540c1c0180900c0100c20321020003804031b2940035080e0340045807064045000d443c4152000c0242544170001c010746500b2487c44410f620a040700240000f2404000207021047c188100c80354a0f901c40c01054503c0c0c02ea4220f000d01150500700c4195250b83d254036003000817100380114401070062402250754030038040c0c50700300c00e904065107640131a00c61070201e54891780a9462107810241d00c1140320060b6070180003144c41030003242c031001c2011280008200f81c101004050b0020308281f42030900150740d2000101001580030380c42a180c3c0310688400d550706000598004048074000010040601c2154028007403062044050031345448070221780d90b640500290700780c0c0514a1a1001d0050305110b03402514046000d51002c600e003103299008960305a03c00c660648400c1d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 600761924 1250 600760674 600760679
    0x50316120f02210606090d08070506070f0807110619150303020d032a140f04033f0e060405040f0207021906120b0a0504050702100c020d09050d0602130f 67
    0x34075854207504403102c43c00c4001c140b40040024030703d07000d1602d40340d0144558558031003c11800c0d07011500c00740e4002d000c0f03d0306031914410050014400980400c0000c00c01c0000c00d011901681404800780180006002c1d26540ca00c141490755084422074003c1681b126580e03801e58461b50020700285020b40d011b000c20035000440603050740c041c21aa90183c0b190801c110481d1040034400c2859007185140410f10f03020b10311969407040c001c951329416031020005001081211810000e64021001e41c1110404142684044080c90141040340d800e01c48010041440030720401c07902c0307040341e8010a101c0c00c00d915800404c5c12224581000d46119034002011000d52416000b003051030708510b0503030010340d4240390005050860803803000d0b42c0306440390205415561010a801c015042c0500300300400e01c1c2030f00c00203560700c591640c001407a074540b0325500e4240707101064aa0750300781d061303c031044201e29100030700c408800701c04001d40342c003542030102c2c12117080a5403e1340b0007400f641002144070760 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 600763174 1250 600761924 600761947
    0x2a07152c010510050d061109060f0d14040506040311120a0206090601090c020334050a030e0102030306150c01020f03250f080402011b0b0108030a0905030c01050316120f02 75
    0x100003034800004031009003c100b0580d0f584517202062203500c490003040f0040101c640041a000700d2501603408800490340400c07001046005c0c200c04110300350180066800102c81190214050f00d0140a5404c21307030010700880d016102408400c0003180031649021021500b026980e0011040080183c003c0828441d001e04104442c50140480c83c000b0000c0341c45086000e903980c81240710408070706104048142c081d44d01035601c900da498000d482c94087c44114a4500c0d11400740c0e11085000c034400e0160f1507070651000081c2c1c1d11450b0042e1109100c4030310440a040349410152203800755640802101094030016401f940c0a00c6040086065900084450044d41400e004d010020451503802c0ca0556542c00074500d5080354080c20702000d581c107800d10103000b98540719009406174105000000d03640c14000010f00e080300c0c00f075880046454076441010b480b00c80d100d40d07080c0001d506002042e00f1304694142403540c01c0050034040040301c3c00c04000c0c4141c0e04e182041d414243d60118070790384004c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 600764424 1250 600763174 600763181
    0x3040f050307050a0e0901091709011b0210030902030307060c08070f081b0903031201030302030405041802060a2109050705150c1f232a07152c01 64
    0x20301084001e80303881800c1402003885407400e0321a120408200303102185401100394020340700950022103011490401080c19829544014070341ca000030044030543c545074503841c50804c2010350080c0907442c40c0d44103200403000307420b0040050f030341400f08201e1800000d40c10301c501801e001d11601c07881e03264034096101401c41c4031040055020701c02014200450600130100007101070061150f030300e446000400210745940544048420784280c188008424941c002025004440c0102c1c0c00b0b1040c0940444503940700d0100080080d0008020b0020000316406001e00c4034009070403404440107241c1d001c030000161071034282c0543c2d0b19040907205008605205400c00704a05202407440c0c9450016684682d40e003511008601101104c4c5aa51032100b109820240014407008100b1070511030011b6803949420040d0707a20020001700100301c0d041101a900128004c80c001c0580c141480010b441d00b194052001d4445060b865480542d08120002010a000b44803000e02c04014040101482d807802c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 600765674 1250 600764424 600764429
    0xc041d040c080f060103020d031e030e06060307030302191410020306030c0a120308040318230901080a06021305220606030b1513051c060c080402060f07140f03040f 72
    0x103941040b20443c0d180b210025900e411240d0656204d40020098142160080208021100d128800d045000c90300c0d036042d001000004a08000d40340c041d114141010703a240101e01c80100941c10000c10600d221f000d0003d80d480540c010501410800403641181c1d081550181c0c0c4104425404402d002890504006185100b442950700c0e0402c1410700c0c0c00800040e1002c80010200103c4200081c1094490741e03224000c00304081442c0e901a80764000c1818902e1403903000314801c200418005190b14003d42036604841c401405001580e481d81c0f502e0b0041e604c5021038001c600c040707140008007502c03a020340c045222021152002c1c40c0c0c0149031540c0c282c07400359000c0340030582803c18004d255070f03400b24006002c0060120319995070001d6a40788112841550245900c010517100c0d050143c2c00d561540b04640384074920800c200c03500c1c0320081d12180801e440c083c1d00001c0070301a0f00c90020f520002001ba00b130141c80383c20f991a180041091400c1c0d01400394401503000881c5c1003282c08581c5490802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 600766924 1250 600765674 600765689
    0x111071406131a091204140f0901031214040e01260c0a061b0b1305120a02190809040510090b010509060313142b0c020f04050c041d040c 60
    0x14212583d0f2a506480c1d0141d40c020b90a000074031002c00c4450342c0402021104075804003050341c540d40c3d62640c1000d03421a510728680a10144005048a4130701000058117907940f2002c40b1500d05031218045851913510006040542d00c1000b001c505030340c000840313178000c14040740300118a00f006800c500904000c1002c5c40c00c950b0100c48041f0b070603074034145140191189880d0940700d9102c0101e025110040b0f01d000a0883c100039000c0c0840070794540e841d0f4040c0741c000c0b0101d41590801c0c000104951150051407001608403007400343e408940074007000300c200d006e1074240d800c0c041c180c4001400c0703c8080d503d00354031030030301001044070341c9040c0204454402c00742170450078100100080b8010744401486010580300f9402c0c690100b02070340c19507140c21040f0400711003000c0b000741200741900c1c4400c0c401c204e09030b84024540714010b208091804081346e0103440e403103000c201c0c04180409840c0c0540541003489090001050742c10402d560000c22840030400c42105007014203040420b045030380c10150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 600768174 1250 600766924 600766951
    0x50c061906140d030e011809020a0f0203040311060f0c1603020103060f030b04112205061f0507060c0e13020d050906010302150c030409050a0f0e190605090111071406 73
    0x70100c0d0b68103140c3c02c4981d60142400c074181d80595004803040302d84c134681e00020020800c000302e215251940074000340191038441d1644404800c0050361742c0d018a00c001454040c803140711414509014028104140842c011141003a801c002e070380303040181802c4a0084210303218810819981c0c0360003110f0050010740e640080742803c0d0703202c031140c1a10040012741054001960051240c81d04003003e8440d04d03010540411108034200e0100c098241030351150320410038480c04421441403000c85500c042c00c0380d254585080510307900d800213400e090442c041481030800c05d4281548a4a1111400c0100100300581c3d514a2500d034404440d000303001d40246030f02900043c00141c0300d03c28540303400404000d0780c985071a0051000c81c83c520842c0c002c04003c43c00c15041c03201c5558103411008000000d034800340041007842004d01e564004000e035112800701c0503c0c1380c40c0494100d900c100c2d0002c03e42d40020034000703c5111141900c2d40050002c8030034146030280544100001d11034180c000203040580d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 600769424 1250 600768174 600768209
    0x60405150103020f0403020603010e0403080c030f130528061407020a021e04180506060f03030d09030311041203200703060c0315031b06260403050c061906 68
    0x8801112425540c00d0500d039002420144600144080d10000c41c0d004243c2a5650f8440ea0103568028040d5411004a000321000c542000140c1069074854282461002031640c0c40c01010800399980c50000d441500504645800501e040c2100c085240c0400e802c0501000c10391900c0000c60b1804058144a20700003000d02c0030300d50780400d10340c00480d0103c03034a407850700c80b201c00034204007406041a44d0080c41e00380402648080c2c1034805580601a20585e40c59030350b07100900510300082024950325400411a8290b08217142e40039207201400f030320700000c401060b407410100030341c007940003480000020a0640101980702480801034404e80c410304003e605200c0038a9503490080c04010142522444008500d5220360720480044510011034a0703241e17521b0030f04084050116140b58242240410003007095030250080309800c0303101007a031540c0010610354030612008003a100310108241000b100482d41c004104080c0150340c0024200c02449805085a08079a066400180700307003202103c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 600770674 1250 600769424 600769441
    0x3030219051801141c060302010f020c03060c0d020702061611100e0409080f07060c02070f05060304080c010b03100e010501051c1b081204090c090e180115060e09060405 74
    0x20100b204400303007424a040e6a0585201502e4055544c40003600c035180e84c0418035000882d007184044138002e17200c040a84589030130403621100541d01058142d808240031a04107005e500081817280304000c001801d140d101c0c1c0c009074059014800c101c100d240e03080c2c040703428466983d046000208046032400401d511034600030f01510500512148580da88455a03428001c00f042126a085141904540d0b60081882d00e100208115072000005201d8170101041031405280c0c14020b1300c2005107050305585d900d0780c0700b1080f40d21006010410f5529040d440744503480421098004c21900c00b07000c5105080318001900f190300582c01076110380d4400300c4800690041402d40105070743c104640ca24000400851418800758030b0380244e0452050009141a445807200540250790310500c081c00b1440d02c0b00c4044803441d106006190b180080c220201c0c40154044600c2041c01000d00c00224202200140207188414590700c090080340c141841400c035442c0c0556000d43c84641150200102d0614101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 600771924 1250 600770674 600770707
    0xd0305010e13021806030106030606030813060e030a2303070f11010509010c06020a02010b030d0908070f15050d09021302041401020105041119171f0c390303021905 72
    0x400202130004501203250f81d1001c2d040360000d9a00450301b4444507a480c544414507600c4201151094004180c0124540b417044581c0302009400400404a04800340c07544d000750001084012a0240d001d400300303a200038140080d003400c60040d0b07004080c0034403600381810810011100c0364104081081450041c0c2e07000303038509050700e400007001625080c03105010380c01030500b50302540c1d02d4860b4420a030a03840e8006800b10640780351000366001d40341d40354281003028070745001329254501013030000e008280c4542c014044c41d501d1043c000c101e80e119600405e189001184481d01c18940005007031003204640b1480c3c40b9644002c2c80200b020303190540342d14450880d5903082c01d00c6505880550350744244c4105543e40078000002103105070310b00f1150419a142c501c400030340ba02c0360840002070403889092140c0c0d62180c0d10782d1a000c102540c030380744640c8100e4800004403802c444480301e410204589881c3c0c10009442030300c0069403140d11580322150400d08240090402c03e0811100310040d26141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 600773174 1250 600771924 600771949
    0x201020f0406110f01050f07020705030a050c10090f0306060f140906100309062a02030a021506151c05011202030714120a0303141b2205030d0305010e1302 68
    0x140100e43c6070031a0081d00c3c1040009032000400b0760920303042c811707040a400d800d035028240b00d40032038522a43d140d05050b20741003c0c001c0a01580c004803542c040e0790600b500c00348a00b1046281c46d01266031035000700e6454003004d42060791115503a0409018038007030881c8070400750480314004001c00001a001507107a0704000c10003806480c0301c0c050625500e01a802c1a50700700e034403001c140030242040d400540060b000d040c0d92040003194a8001038184e0000c0200c40240560b81c0c003074402c9a08011110920802c05000313aa0000d45d80c6944541000400780030b429440100000782c04140c0c800600750080e11030607045841e242810000c2080180d50008101048903031007248810b412070180c1c002a4080e024070109551805401c880304209549513018040c040c000607444c80e810344803003200002580034101c1080701c5200030042104220440034040d000030400520134642030751100302007410601e0414801d000b098942005000380c901e0382c2007050380880012092903d94420390001002c403100e21 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 600774424 1250 600773174 600773177
    0xa020c0a06090206090a0b0d0b0f090a240b0c100e07050409020d060e0a061103040b060d302303010b030a0902061b010b03010b031c121d07060201020f0406 68
    0x54400341c2c00c54035007000390b90500c3d500500b003d0310583d484801540c0350340a01c841102e10b600d04602d141c0c4502d014200ea108211001c0c185c0d03401c5640d4196100010500c5142211562210107440c501c0300c41030107203581c0a010b403102400e441c2e1422540c01490038064480a401e014189000680340050000e103910899604440224841d045800824441180b20002801660174610720920300396001507000381031442240100041d1144500d00180343c0019517009003031110500c01300744607180803100190b0940c041c1d40c0300051910515418410000001205035483c132544000307000d5507800c00a15003e450364050041400b2118206001c0644014003412080040210226405a08661000c4007103075004c0c181559a0003065001c0ca220400b0340407020440d82458148055810107001d40d01c40301780702070010111010764288400c4490200700d20203081010700c40d00c0000e0030103075016020315001c00300800a2516010000340341840499045031066a00420281c024148540c0440c5d08440c2076 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 600775674 1250 600774424 600774431
    0x1060813080c0615091b040308310501020f0606030307080a050d061409071707050a0216030c0317030c030c032203120b0a03050714010203070b090c090a020c0a06 71
    0x2901d04000c10303004551540b00b0034400d0b00708201500708096a01d4034071243c11103401020350780d5001c120041045c60b00d00f014180710203000c108000b070b41d40385c082d00349400c90220516060100b402480600d000010f0b1081750006d039039000f0010313560180000400c00141030f015180500d4040003096a0780702e0410002d14288001400c1e002052041c4141e400b100c400031000e214071036a43e844c030020041045450f600c5944503401244c102c0740148010014480d141201440b140d480c00f2090316203800620f041d00541c001c1005203518003000303000d0400910300c210400329145042d810720425007800c0f8100c1e40c001003010010b012404500000b565807002c0b582c2c0703809a880ea211149000001048501d400c0f0003800c1c4010f0800301138001d0101020251040e108000d004005c00030050b0311401484040c1013034000c00000d000e1200ca2142c0c007181000180110b03440c0c104030b50344960f034100c0201d8800e40c85401c00d00140910b03151244003140c01000601080d8204128031008644035514a00d0081c00e0030758 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 600776924 1250 600775674 600775711
    0xd150f0b3f03040f0f050618010309080405040630050a060b0109032f15040b13031a040303180b0f09010e030c03130803030f06090405010b03030a030c17010608 70
    0xa6010035103080c001501d88540d44d8640118410446010b2180d00007100980441e05040c071005031092022403044050170086210300640050000540c26a1901c0f010040841c80d03488901034107000781540c00c03005d0002c8044407010900c9241c00000544c2d034420007039244001c02c00028620040d030f0b8000c18002242521100107823440c181d41d5000415054078401c41c10940180a00e202030507665038400102415041010815041c468200e40c0c40317211003e00082c80001a803401070050040208000d0000c0c3c0c0c0c070794880d40f5070f1818410b2030040c2441c1440812040503814060180a110080340b200710a406ca5900c21008a000a00f07a00007a5139a2000401344042500020380c0c81c0700312400e807aa9a220205403a40304d900001d10f21101070380050001a040c0700c0001141d1154180e95400c00b010b0701d4081c00c20648000c040c2c400e0350b00e076403924506203450340d062008004213445918000745c4460000b00c09010304001c091442603c01440c13004101c215004841d059002401d01f90f4614942c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 600778174 1250 600776924 600777019
    0x9070903021003020901020d0206010b03221505040201090b04081005091015140a1805040c080f070e0609090705090901180803100b0a020307030c020d150f0b 69
    0x45680081c0d800b0010070b400c10495034040d0300801c1c000000380e0a030340d0b43d0000f1041c01e07a92441c080c8a40c084101c4c00300300241e09400f804045d8a94801141050103171854561034003c1391405035284500c03a6030f0fa40052008540e00300040f90028501040b40c20b08140c0361240c01c075161407002d802c0034242516000040e100744d00070f01040d114035496000c00c00000d0040d20220300007517014040d440150840031002c0c0660320703105044004030744001180446800101c010080a0130002d80300320750342d180e10b140116444038180103051034042400700800d2118a44030944c461040041c15841c000c02040062241c038040100c0c10320103841d4140c54600d4140c0390b54003998018201101d50002040b03244a001081202c9000214007842445071150109500c40b0368801d00380c440d4040113000350340101b20980000f07020b0200c103ca002d0000f814000041d005445110110110126001c40c0c281e40314034140351b4552030b11456030361000640300380d03c00718010480c00e500d50a02d11030408518400360346c5401c454 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 600779424 1250 600778174 600778187
    0x51207030306121209332607030b04090f0209041e11030d03060f06140f12090f030903070608061207060f03180b0109091b170115030c050907 62
    0x1000250100c40b070f044460b04069426500c0c007800c80c00090300003d80000d90017550840c040082c0c111840d8071030f000c80c0c3d00a409114800f524801000e0046081d0344400d4155a0202e28001100780340b061850745c5080900141111210102079100d989001000c0c0c001c29180100013441940c16244050b681d21607040c48080c1c050680840041b40412180f61000c00900071482c0c1c20340e440517022503420f003040c8641030f42500e070113004e00c8c61020a08001000094458a400006a4010150507107448800c1001501952003106500540150074060003041a8100f16420740e42d41d403903001d90b0425058500294482c440b80c807400081100d0304005c6006070740c450480880904800c421112040d5507507002600340d044403192000864944401c010300c1e49815140210b401d40d002d0046041c50703007080b48010040000c0e070020b940304508400003001c883c81001e0a000a424030507407150400c50824007040c2502c0d800d0314100c201400a603010800118881c0e00ca6041d2141141c1d0481156164001103604 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600780674 1250 600779424 600779429
    0x3070b0f060d021012050f090a081806030a0903110a05030306010507030e030106151101060308030402010503070e0a030503031602031305040207170406031401050301020307080a0e0a0b0a0522051207030306 90
    0x200c98001c40c40c8003455042290001d03945007185d010700090303480880e1404401012182c1c11010b4200d201c0340800500310400134420007401d15894060480084041030568204403903884849a550700c10009150300110324070b600400442c014003245100c1d41c4c65039141d0101405035810b000c00490000c04241c01900346030090000136008201d07440c2d664801d80f21400540c040000400c900400c585007420040c0600415203412552040c80c40d12168011a42980000c0c000001c02008652869069a0365008200203501a000842c5c903820070402005404441800349015075008100c20102c826a00703c0038411281c0841300161681d6803401c00841d40440520700440c2c840000501043e082e8042d40119005484082c0d035001030b0f81ca40052600300d01c030907107546010804400000b240085150080845018203c1c20768500c4143c076526a400024190f80700b080c45a12001041080c12a0000000300318049218180b44100305c8e131a01d03a01c54020390714000800800140c05001d040c02074010713400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 600781924 1250 600780674 600780679
    0x30b010c0501020d0c08061c0f0201090806040c0303020d1b0b0a020f040b0309010f06080a02190803040308090315060108011712071119060905040f0f050f01080d0203070b0f060d02 79
    0x5403111400c0c0548014840102d00385c0104603c0d80215603d4141002c54501c401942c1d50301c0b41c10141c01c0d0300e07400c0a110440108904110702040301241160f428420035020303620508145045508502d0040e05110007880c041c4100508000d01621400700d1000c3c0c2200d00c1e4000785291070640f500301d24600607104502d805c521403a0005400030b800350480d070040d4482c90313112000700403100d1444d07450010380e080c0e4451044039130322180c415409440c01c0c0c0c00c0b8180a0620300388071b04200d079482d8003490a54200c6c1c0d0042d100c510012501c3e00c4542000e000501d11058030545c01d0b8941c1c034003540064880368042c041c021107000f032000040c1e0b001400308200c10315208030140244e1140c01514212883e810301e80c0e45540190b103803012085c910f0300306a02c200251100c031349510b12260308013010b100003040340a144a2409841d400a8000c1e6841882841d0041e0310600740840725604200681e444c1c14819004503007190300400002020a03202945250040c40e480b500041c030741c4a040000706002d062400195 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 600783174 1250 600781924 600781927
    0xc1009060b04150e0105010305010e0a050910060b040303110f0307030c0503070b04210e1e0f19080d0f02120c010b030d03020d0b09040f12171302120c010c03030b010c050102 76
    0x220f1110b6103400c00002c40b102c5400d050143e80c0c9030030044003a03030404c0c0300c1c00c2880e04040c400308250107819041039501c41005402c0310700c2c85282d8804402640e1140c0e021100503040040c0900506d80c1c003200302580140514014031800d6130350080581d90b4418a400982000220341c440010024144102c0340f08580010351f054040c00c1608160341c1414113201460440c1c40040404980a401103403500c00c403110003070a507161a000c000721038988185084416074030188800700c80e025030760361003c0c0d62101c181d043d0300d0744241810400042d2070805a40c510805010041005600072680001c400754014000c610130361301c0706a800144d9000d842d9601240782d0500070401c51888040d41a4050b04200c0e4420400b8482100e400083c4440070384203560241246040c003100c5030102d990b45081c000300c0303800343c40e05608051400880056002044c0c8503107800c600d4124002041d032411451581c07030001640c016080ca07426150002e48290342900000707060540750703840c0c8400c50380500001e09181c0e41040007035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 600784424 1250 600783174 600783191
    0x60b0705032b050f070807020109050d08131505090705012a0f060203070f021b0307050607050c0a03120e090606071203021608130e01050a0315021e1c020c1009060b04 73
    0x180303031040c005c80b0380900150b0781d1700c00100e046105000700810240c10201030000746d0380c10788040f65601801414001d06483c03031144500080c2c1252081002000f5020300040c032800e06030007203070070710f0176540c0030307604200d40c0c21601e4072907402840c1c0541d071140c044c1000701983c02444c07070301480460400401516461010003001754207501b00d8030301860748260741d0a17105000d015100010362202710040340354065024040a00003810080010b10113140500704075480d1003a040001140c09845070400c48040c00c454268402580e00b000000b620110100c407601c24030315210f00414407034081c13000701621060407010801ea045010b64102d0340c0d005207074810301088040e0350806001e07541c40010703000d4003200c0700400004c00344d0b03521449a060300c00c0140190701032071850b110032031241c074019066040103600f005000000b0314400301a00180f00820645611003809800e58079410400341200c1d00410b004005c00442c110000c00c005142001c1c01000081c035414a09011006102018056410a107041c010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 600785674 1250 600784424 600784441
    0x1507081305120c0312063a050d020d11010606140a09033302040308121e010e07081b0901111501080106030b1305060a09030c0f060b04060b0705032b05 66
    0x101815544965500200d856030401d00c41d0305142000d041d00c244038504040103000310105500d4031581103540340000e51f001180c4519042200180b00900947d0000300310000003600108010000c40008008001ca10300c2d265001e44501e81e1001641d1000301d0014141c00c045009810b84006990018030f000c001e0365018901e44644202850450108061006100c881940600860342580c0e801100a030406040c80d44907090f0050103840301c038602c0c5007210707125900c0141c1d811241c02003910903445182400d000c100502018800781c00c0b00f40d10701c6040300c40301100030f80300101c81801c0f60a207030034411004085901c50034110100e910001c0004030100000d0741403015041002542e001d000000055103850403150a000194840240b998001c2000120160030f80d40c008111540641054a2a9a07903503444945500b0400000c40f0819500c0000f81840e0a040c8110030240ca0709105552610426842d400e03580e00940710ad40180b004404103d00e8142100304034094100e100a10602060801c41003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 600786924 1250 600785674 600785677
    0x10e360a060f0204141c1b150c060605010206100e0c0904150305010b180c030a0b03240c0a0909050c092d06090f0f010e0d0b091507081305120c03 64
    0x403580e401c5440215002d040c9813592030628001206c2d64090b011241c140d44002040d1005210211444500c800c0003503050304038a0b05200c543c2180c2c0e1461040b83d25407420308100e13540c617001241150f002c041001030781403031000180240d50300d80c42d00c024503a840030299944c0e40b040483c1c5680081c00c103e50700e10380c01101200401036034840d200a100e511000428442e141c041010001212072061011400388201c0c0002150401c090b04004107195450b003012a140c4402403201d941c00d505036040c4541c1c041e8000e42c10981007011401e50501c0c021801800070040d070000c3c000c0c2c0403403903a01d42c00b14096682210440e40c501c0c001078140a072101040c41d40d15504507002c4030107203d05030103942080359494100c08484a00100621464520050b8010b10080f040752024450621981c0312007101c0030703030314080800403191103203000c04030602e040704215007400401c28907041c0c9003038400c0034440595044200d440e07208a5068091b0300207851424020b117840000401214244000122054200380100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 600788174 1250 600786924 600786929
    0x405030703080c070b12070507152d0203060f0f1207080a03020601090207030507151d0a2616031404030b060429060904020c1005010e360a060f0204 65
    0x102074800066170b034200c034405840b4800e40f449016000700001a40140910080c02010b030041d0196074040c41111940780450700301e5034040000e840e20b00e03105000305807404101e41e0036401e054000e43c150300780f000120f00f01800324800749205120703100c02c40c0c00503201c3c8041071456440c0c52045038000c1d582c54024507100c003804002600180140b03800400c211005008880702035a02d60f81e100d1a086d03454403130000340c1c0706102240d2035058031020f01b14400c000b40c29404205980d000050101d9040520700396991a11115104170f0403411052100b004810340001d5801e0004144031550003a105441d0803a840180f00c041c0c1d860110011901005003d80b0502c00c601c00e0700259410400810f1582c64140c07060f040043c58101840c0d8024080c0503814014007031b01c0c0c1c00501400141c20082181102401d00c45030324190f000c4c0d01c1d42c480c01040300e10110ba08060300041c41514200740c54102c101079424056060140380b0703014070074900c1c0e61400102002440c07412600410f040140c104150a0000654842e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 600789424 1250 600788174 600788197
    0x5090109080d0c02041d010c0e01020f060105090a11041701090209010e040b070e060c150a0b0d0506010e04080d0903020f07061107150207031502070308011208030a0b06040503070308 80
    0x10804101e1410000b001c0a510348961200300700340c0902d500700400b030140d040050380102100d403c0b003403c0740400d000f141c400844a840d6181e0300070b6141c00091070320500114001959016000410054950355001a04828400c0010400a031110484400c511030390b8050103000c20144e1145860460650104021078422075406040b641d0760700e28041240800d45000c2c2c04c0140200200d41084d00401c094942c1c604094031150400780d0f20740c0b0365805e25074802904000807081c441000701c19100391140ca4a140001c40318102100d20b079882d013680d80c4105004420340d880c1d4600c04541172098031001d07103141040843c0140001282840d0003501c9400c1d05120740386071b08c41c1850200c1c01600500390150100707a41001040311030324085104103030380c509241d590b041d030203425004408150b051584481d0034455410160340c60610746802004054140c1c052180071491740b004800043c0c1ca00216078202c003244101103007003180040001c006100c3ca40c0015032501c14040d000080010840241c582c80d00e28 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 600790674 1250 600789424 600789437
    0x60b0f210a02220303120b0102120a020f06250806060f0d020a0f112e090c061202040f0306090204322d100e01060815011404260d050901 60
    0xc03542c200e04007403030301008002c10303441c1c0b06d2941d1040981e88040661001441141d0100b07081302c406d8030740c55200c8000703080143c22028130701c403c0d29000c110143e00712420440c0d140c0043c4e1030038100c0184142403240001000001c0d80451195602d510548106a10036081c0310341e140c0600301c1c0d5600a40c80284050042000b40054040c2280240d03000e1030102c8502010742544040ca4002c0d910f400c1c1115000d5405140b4142040c0380c580041c859151498840c01c920016141040c0700500300480141c98107540e1401040203002400e07500007444101e03940f048020512003690310024020307007003400f4000c0d4491a9041000310007271060361f42664034002e402c124402500c3e045401c01c42840207000c04890400100441d113103a100d0a55415808403500e404207594645580405040c11000c0e400003002490340c2040c880b00c500e071030000b54001042401e150041c080341c031501111500640c41928010703040e440c0300d591101107a503082c01d2180c4d0940c05032922a80802c1015125403c40155503000842c3d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 600791924 1250 600790674 600790717
    0x1060906030510060b2d030a141008100507050d0f061a12070c03110601030f150e0601050f182d0c160f06140402011101060b0f210a02 59
    0x104c2c441d04080d1100b00c0e5440d0300d802d40041068080745c05505481e080d1100003005041d0344401c0c03001640c040c152180021a000c0101580351140c00c00c040c2102d1b0050510860801070594001840501c220b000070011481b0f503980c1c10141d402d0700411050a50040c20880342d4428541c46a010030309540c601d52031201040750a903c0071400d40104111aa0843d000e58081084035002e200c2a5404504c40e241601c4442c0c504162181071003801e03441100c07504a1061084c0401180540f00341c513280c1000010012035000328200c07984c450040c07094601400344104215815107481c490303001040f010b01840c003003d040841a40c4854440181b1050664009140341c402c1c003001c010400b401f03500941021807c00c1702803d009401d51440e1101200c0c3d1400c0d00e000d01000800500804035051486121b01803685481d0002515444050100c0f840350b03454038000340618900b00701030f10000304007003140c0f40d12070007440c811403010051480311000b1200d610003080210301541d001801d41d1001e00500503498075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 600793174 1250 600791924 600791953
    0x15120606050403020d0b060f0d0602040503060f0610200a11030606030d05040b0d06032301050c0c0a2a080703051002040e010b03090715050c010b0a0501140318010609060305 76
    0x86010003503015174021200f40104c0d401c80d080075003101c002042e00c04940302200c0001d44603010b480007200c81039000314040143c0c0c5018020700d60301542c4c885015019207484000903211740e280402c2601400519030000305a40c803440d86110580d0400380c00c03151400704904140c00c080707000318400d501c039114500c0001c03450300700801c4503021201d0903100c46080a0408100c00d001d9048030291410b80e55482e040000414102d880c0c0b060044414041204101071854041d82520b070000d04a4040050030824141030341c000203060702d40d0329000940d408800d12190007424800c01d4802c101c20800c0d42c000c1e4003040105000c552482200d02c14030403640c14802118401c81640524403039035488401c0180104071310549507008590001da0b0600752603e094a4601c940c02080c80e9440d400001000810720800e00c400034483d01ca48124101d8507000d08a2520300002d21509480c04507218251000c4003050050342803c0884641c0e400381b10091003404c0e107a00f103034002000756100503a80c920803d001030760b505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 600794424 1250 600793174 600793177
    0x30711011d0604081804060e0f060d050c12121306180b09010c26041805040b01090b01050706051f090e060412300c020f251512060605 59
    0x200c011a01602c20307581c5079214914190402c1c0c505811050104001407950741d100d00c5080702400c400c2d1072910701800c12071420726481c100100f403e03001c1c0070b0071804031011500005003001203440880e000300745400c151140d01d0804e5070003104c036901014003203a9001c074280000c0c1c901c400d481e0303a0350f901040e140c4200d4117222503101c1c80c1708132a04c0c490200244001544988154406540140a050781d640e0356103c0c80d1905a2800d4072009010a002c82e080c807520301c46550b480c010100d0b6580134402270038561940004040c040c8a41504190f840c40e03007440e0307640581c05a6151a070003000c10082860a00c0740b07000c40d0807120000c048289442c20780803034000309610806030b03402d110200800050ba55541c42c840d00d023000c1c0b00c1d04414441c410601c0712010200441040303140700d00000100310703030b05900e00703e50a40304214146800d54001740d0604520104c00928080b501c20781130030440b00041c46000c00780072240103410001c0c17a00c05054210041d990001150b041352800301000700041d030b6075003008540ba03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 600795674 1250 600794424 600794471
    0x130203210406030c050f070320010e0316060603020306040609060c11060f06030f0304060306050a0801051b071127012309041b06020a12030932010203071101 69
    0x201801e00060000c1846a408500074032407038207060781340175400c05282c1c00c1500301170070440010341910150b0400e8408880174416005d02c29009000070120f5002103900d074054614606134100803080e0f00c109009240e0042001950082d0580301170381001e04181c00175155400c2c0c159140c9050400c2d90424511940c105000542d643d0090700040d1075290442c50f100c480a02031552600c03440f60b68000064090001700001e1629440008501d03150000b4450101c0b80c0d68080c68269141c0410000000c2d007110700c1c0c84551480c814080d0f5a0791252414040d49450180520741000b10076015850418000b404403c043d480d140707101d12982e9076008170840031040c4024001d00105801c18145141c14484c01182c0c0145c40f800f084d140505080c0c00c00d102007101c6911400040e440500107100b40004100d00c18140300f5a40360921020b4956100d40044001c0840640317125690807400b400c0c06940304038450702c190340d2000255038034100302d84020801421110790310415403a2071964003030107c805080015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 600796924 1250 600795674 600795733
    0x1140a0303050a02010b0a091505030a03170403030e030d0204030308100602120a110a0f170f0f0c0a06060620060112030f1b0b160f021f090209130203 66
    0x45605603607049806410600c000b03070030342d07498140341003240d914510440042c15a041000403003282c06100d1501c0302045500490280d0416460341010075400510034440003001815580503854500e0210010f041640c0300207128003021402c0c1440002d141c00920499019a8440c01142c4441c080018981000e20450300540d00030704007211280c1501d0068903840380103041c0710b4024801405614108a810301c030860700e58160400c151300300711150780080181444d601406050100341d500f03080c4144503d81c03542903001c5000c640c20488010412039903034969408103051100564581002e0301101c1c062514007207043c15911401c9107440c0c0000c1c224100c0d030409a00c0700c43d9080a4400f0384007040012400000c11100e0794100000307c81010070800c0c148d100c1c0021142074035105100f4051080401d04490402119400702c1205683c0010629032699084040078070310309412100700014424820020f400040c800b041080ca0078482c8a4859014001c2e000d49101c4010001050f145940c8005101c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 600798174 1250 600796924 600796939
    0x3040c2114060a1a090610050702040203040c05010243091b0e120a11030703050d050703020115080a0209070306081f110306150304030c060513060e070b070303240303020a03080114 79
    0x61880c41d103c031140d1f020902030306045182c610190003080583c1d00445083e40d491110000408c0156810020810b204200c540b40700d1255055604441032640403a05141070312082c01441e06e40f64000318041c0c0000c0060140811800a0000c409051090b04002501c007103051a104240d0604012841100c620802405402260569600c0d2024410900c00031501031140340400b0001a0f001c01010203144160340360742c1d480307919601c3c0003420744529805144610f9065401080f10000002c0c2c004040b95040b1042c0000c0d81e25601e084006000552140340c491082c26001c18a0b00a000c0c400180c5654805052003403006091a061841c44291500746e0005010005940850050005035800a1003481e00112031002034542c072080c2c40e8103640c0304d801402c0010180d01042400e00c10328480c0c4c01100d011b0650b03140781030081c2c1403900480d20041e05140e250b0160510f1136200c415001c1c61120b8000b580c2c4010341d16400c00a43c0c40bc01c030001200450840303000840d415030a07405007946004010b2106 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 600799424 1250 600798174 600798181
    0x1060e04050405030f040608010f1a4512060f04080d060e0c09031e060619030b0108011b0306080c1c0b181203040c2114060a1a09 57
    0x10041c580204140c5442c00240b05e0440b1101040300200b004040503519488071b94182410006071400c141d1003640e90018041102d648040418150340c4c5100c0040130030410202110b0700c141d0175100121500002180e401e032510070802e144031003c51006403ea41da0b9441d00c0c200e5081030b40d40c00007039403030510340c0700b2803400a03001546101c004e1107000700040022407207030340d5040541010441600d0042c250000466520010b050821507860881201241a600740d40003020090b01c03018060700172070043d5480025500b0719030400c42c1e030100659100b66440d04561351411054028401040400ca80090b0703400410303c4c041c8a40038101c290340024014003010843e00c01040981d208100070720903480303594034241011a40c1824120710a034200701111600f005110070981c01e000100c440c240c49090240180700102d030b50b8504e11000e0300c00d1303076102d0000f402c080400f6405084006000805000b0340030344c090304100010460b140105105941400340500d140c1004611142044400c3e40248401002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 600800674 1250 600799424 600799429
    0xb0f031c051207200109121202070f0605092109300a0507150905040902010302071202010b190302010c0303050c13080715170109050903130603091101030501060e 71
    0x9284003000315041031442e100362880781c003400c01c0080742c4160110f203009454401c6602080301320840c0b40c2e04035008100d400c01c6503032108100d040c4421131604020741150554514001c5038110b0b0056502300c4000240500207180c6100504012a1540304502a8520134541c0c555051840003045100d01070b5242002c40060600c2054110040c0f0440700701a02000003101c0301085d60f1007024015010090320b8081d20a0501c2460712440340e0000c1100c0e032300c03103180e0080300e940812100f0696008403008211410700e400128060b002c0c3c0840039050b07010b82030211500f542c055100754001351055030170b41c04001c0c4c807045d43c1c0f0402d581c03888040d0200d0032080701100000e02c01e622440d804403001d240c450a03c040c1424000392418580c000e1500f81d44681814410082a58078110381800e2500d406802100c0501d0030980c54281849445400c0d615007000c204940010300984040109021051500e1592650001c024199110081c2c4051006201e5041194464018141600c01d00c1c4c841c00c41e0f4548040c02d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 600801924 1250 600800674 600800713
    0x6072909070311040b18330112060b0a090e090a0f060510180c0306081c0c0302030913020406080a0903080711030705100203061c0b0103020105070201030e0604030f030b0f03 76
    0x10107507005035964400216070b900d10304810030104802108000a11309a481d0707071220004540c1e0380703007e01c04000060088203c0728280045102082c07928000201c008100b51000d0905500320820070a00440c5200d1400c2e8405000421644079625502003515122807903600d6080c21321025107018204054032020030040d402103034000e1031413509541e0700d565842001e02181041000c02840319145c0c154010400e5050050a025005000c05807008200411142d840e481809031800d081c4a10400d062007458001d0041ea4808207001c4e0001c007620701807401f4a0001c1d4454001c807404943c0c2c070008202841c0e031905c03070b401c034190b41a1501140c54440440546644071164841d1001384400c0042d040002c41c140490140a08101805a02d82c10080100058011800006507041c0a0100d1030030210360104446811a0340a081041c1d0711045e5000403006450f000401142c00c0c4500e5061000f0035502c000d00c0c520741c443e19a0200b00035000b0310100700e4450a00348038a58181e10030715030240902034010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 600803174 1250 600801924 600801953
    0x3030c030414010509010e010b0a0e1803040f0602010b281406160804031e15020a090815010302040b0a0e010b0f12040b100e0906180705060729090703 66
    0x1101c421000c1040000c43c2551030445050b141da9440718204181841c0902030f0641e40340b021580c3c018082c1c201a606d8040c10300c01001d015a14944e800003049204040c01254043e003d0b940501f09959125000a80a442d4405005000b444040310451920b052075403207612aa01101c2080c004904c0e11b4243c81c88640c001d00002da00c01310400261007009610510714038018410b500c445e4503030345582041103140d45000156940c055540c007062000400707244034540040e40d082401038940b100c0801c122007a1100c0c0c0c1000040b84102680d44802080c40c0741e00300d0403a4408c5505200c8064074500744403020a02d8071400c954040b8100c01401080402405030070305245080d44a4140f040d02c141085007000159011b858059010050110102550036003002400a43c1400e107101e040c4403080c0d65640100902c4400daa20400068104080d070a003c200002d000081401c1d444050504101d90410040210b00c070809060300c264248400f101e90b4007610800568010302030a9285844078800052041d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 600804424 1250 600803174 600803183
    0x506010e010e070f091e0e0603030f030f041a0a1d03160b0a020708040b040e061507030819020a05090f031501260307030c0201030b0406150c050304030c080f0709090503030c0304 78
    0x89004a003140d51503c2c1184046d80303840f41c904c806072400f001c048074100c0107801c0c1070081d002000112094030455040744c1d004025111500e056070b9680c10544152049000c21102d0100031005004a1007820340144010011070009000c8910003031903240c0e524030405c5269450b0707091221030003001c51440010260302081104026142004660320b01a0f654840d070400083e2400c081410b1000b141d0440125a009200391000c40b0401c0d45466040824050301d400141080a41000103c00c01003981012030f0681c2a038170155180c50706c00c4805042500500d40b0107000e40c2d034034000c1e0750f070b5803230006040428505000f07005010707039081060310010030320318000180c0043e0f042080c04814000070002008800e01a54403c00324190700e100040664a0300000c16100d41d00301601400084150200d214102d4402d080410010203d0f1401d01c1c01d5000310703440601b03814141500020404000716280c08000c03182c0082e140402c0e159242d10f82190b0020783e010380f10394028000500c540403884011900240076 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 600805674 1250 600804424 600804437
    0x30e0d0513080303040807151806051314010f0c0206061305090708070f0320180603120408210a09050f040f0f090b060402090603150d0b130506010e010e070f 69
    0x40b08200c41ca107610036075044429010004483d414024010b8480414940b410010b01284075114010040030314013440142a05690b038021130910313030300400700ea24125448081e1404164215280318005c1188105088a803070410031480226072020401a1050800802d101a0303044c10012031070040c80b0007061144244100711002c03682c3d520400852000300001600344c9043c46c00d601c2d000e0880c00d02c400b07010144111010032441903503203003d074546031520031f04c40c80207007952000e000070715200032000320500e0300c500010045a02580818400c10126170300022141410b207000d0790342154403445441000140b064201401a881d100f404500041c400a00100d070307028072507001400f01c0e016a81003400c0142e0703c41702e01d810004900802540b005045a08500780000c0c503000c90741d1844020805804031958401c2e0081581c0c8000b03404400c10780010305169a460001d4004c916069902c00a481078400c2100002e005641403100030b0680d0300c054500b19103071f204c081d801c1c0c0701e0b1820308a446050009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 600806924 1250 600805674 600805679
    0x825120b010c0804080d030605010c0305071709041104170a030c0b09031306030c030507030e150a1103160e031b12070306020d09200a0e040f0609080c0607030e0d0513 73
    0xd42c0080c101601055018064280c6d102d1805800c44089038007103414440410036080c0403035004015141d400d508081c2103034000d50b916402ca501c9202d000f0005a009103000000420b04111102810a555041882103800d1500c1c0940f282c5e24103511500a0000d41d003a0105000110406e0010303802c550080220382c14034605800d0410a0030343d603001803001a40d01e40b00800b510341c1c540200c0e5003102031800d080000c5003201d8050342e220404d803030441c03500c12510701c04141d80c10700707540c042400b10401007071080e10703801c02201d8000849004140f00c4c0008102c0031800c145480c0100b20311400700c6181400c100440e1020081c001c400c0c5c4a82e60112070b80c0200c1d0b4001001c9000c500040c103584040440000d040120b6240c100200c10710085030302030b1400045c4541c01d035034540c6a0040141c4408640706403d5039924500110490203844c401040a81001c80000030407690308041c044607070848060740e0a5a90720802181124190010306034250702034071680101a000350010328003006840e44034101c154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 600808174 1250 600806924 600806933
    0x2a0d03050d090b0601020105060d17130506071b14031504020d02030a1209060302120601030b1302041e05091b0d02041205071502160501030c0c050d0825120b010c 71
    0x1a481c0302c0c1503403080e800301c0030020f03e5a828465a588003404841c60281c1080688904104d41603902d48103440040c00281810028060041c003802000001c1605560744281c2c5010221310b811541d410155042c843d10200da03403810320901d8000014041c3c0201614101d400003604480030160081c2c0e0440c6a6400c10401350320244040e05031680174402511080b428090b000b486400c103540b2243c00c00d0b10520142007400585250150410300910300031481094510000301414003012250210074030000c1c0004001c81345840b0490740490420101e0f910702c0d0f850742400302580301140d081025100550131414240c400300f0242c620301c1401070005040c1522810003a40210b00258180c88550001e8810444552481254601d9251754405031040844902c0400c40e00442405060305068443c000074001c01d01c228600004160098229011840104e00241541c4401d44149a02c8690501e80034403810200b81045a41e54440c2d907000991044e800b592002440030708030841c10004030700c20444c00329 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 600809424 1250 600808174 600808181
    0x101a0a0516060b0a08010212180705062101060504050603040f1b080a060b04060e01060528050a11340b041e12031202392a0d03050d 58
    0x1948502d01c0080c1040d058810048244282e6121100b981c1c0104400021015803904075508011005c40075040302d001c010416040c80d00c0ca0b00016040700c404079030f88046c4419006a08074000c02d10703c1d100ca60340d0f25940111000d00c1140903d5801030810404100080e103004404402d15000b5050080c07410503845c03507007000000ea0b42c0811401d40c0030704244000c0c00858031960744001c2049a08109052804801651424052095005200c07011603091400740000c98140880d1303065042540c0c000a000101810f1a0802c0e0002c1001640105080305241d000103110011411282100d03050441601c42010003000d180150398080c1080b982c2c005060413465020340040e25070002140807400354540d0305480c001c3d165108030000317100030414501180d0840c0b07400c045421102c4001d40d90781a49030104541c000b00c0380c215034070304032040390701c0bd40060903100d601e40c40c0d4403403026950148581146045c40c44140c0305040c0c900c42e40e034113405e0380724502500183d0701e992003801d2507401c0045030b0b10114100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 600810674 1250 600809424 600809467
    0xb070815150903060f040c05011209020a060804030f0c15090c0305100518150c070807210f021204060509120a08030114090f0c0d060807030f050105101a0a05 69
    0x2110200700c11010f4542408481e6201e400140300034000e2505071a005114405442442e050180200540380344ca101c0b0340001646940191000c18170690f108001030010908032401d50025007901f56a007a094400c146030400640c00400c982c6030203103008204002030804c03100c12240707078100e102c0000c00180180b041c0a240348800da0000f94620384090620307440e040105442c4a10b410001e035a014003145400310940100750440010384a04c058030706100c00740700307420018202c007018407548020384042040050040045546043e0012480d08050342c1d1001c521240111490040c8010701c841e5100e200070b40300e91b8800500c40c008880383c01055500b44803000d0001d581c9081c0000052010300320107035508812032800d4841101c00d2404403d40342b015038000c0c012043c402c0000844032442c100681001014000c03000585002a030b9a01d030031140d44071400b0b0210390550800c0c0004032120400f401942c100c8085441e00c000059045030502c0c850341c01200303060180042072007480341c4c4c410307100c09c280b64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 600811924 1250 600810674 600810709
    0x15110c15010602060711060106030506060904091416080a0b250c02180702060711011d0f0606181306020d0204090207050c0a14091e090a06060b03040b070815 69
    0x3125410a034009003010001042d01d414007800d050700403a042d03800284541120803030b250000b0036464890024120f0b118051026500508201c603440a02201000f084103095848007241e40320001992805c1c400291072181c50080d412181200b4085054501e50551124000f072825000070313210082c24003421485c80d4400002841e18503100110300b004d060301941c403039140782000e02914081c0301c000d6603644003c1000c8200070b50315855040c0c00100350818820301d881c00c2ca032246109042100d05585801400618040e485070358080340740c904201906244c1c0840309600b02c1440e540f111704003074030b0480818003102c105a08100401a50304c0034809480501244a009607880d089030130a42d25102d002108039100b480f030700c1c4041107848100500c8203000c000039a03180500d40c1c0d034000440e25418258150b0041e1f00032040c2080300c0100080b48850503280301c0c00082100380d8481c1940040b03400100c400418440b0080080b840071070045004561200310304800341e0380f140d1468080303240300e90070034200711 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 600813174 1250 600811924 600811963
    0x1c060b031c080906010e042d060507020d080a02040b0307050a090e010303170901050606090f0f03010207240b030606010305041b0806010f090b130c050d231315110c 72
    0x300c0c400f02484a00d004080d8400e5881060400740c6610b421403402031b0940c00321510f10f4440c1c80301040d0700b941d400040e540161040100b0300c0d0062001e0b40f2008422100d4000410900006c4c010307400610076581510303080300c9068116501c0d10000c1e203d9620000000007440988040041c1c1d0b0041c3c085410301840c807070382d90030303694000c500803039245603401501c1e020059061800b0040d582d100d440c141d0317071092001c44400d00e02c069204080f61143d40384010268155000050301d80c1482243e42201100c0c01640c0d003644d10185130b01c5402001c0752030f0340c1d00f41c0394150400e00c0490038035031090700056045401452080c078030404903a07002d103075a1415441071800b030f00000c004000d06003a003800080149245203040c420240d40000041c691485c1501486440e43c0e00c954280310940704c2c006542041700c0140003001281103020000e40c0c80071a0000c07c8412001220000b08034a403e4240c91000550000814204041c1e0410f808064007001e030029001c008d043c072452007800801c100301996050410348a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 600814424 1250 600813174 600813181
    0x50114041103090d050f1209061806070504050103051009020d05090c010201180f030e09090a1203020f090904150c080a05070e0612062202090f1c060b031c08 69
    0x403007520041416081045002d02c01c10000b88004148592140800e10b02650b03202104410301855000e406400d01c40354a81001f080049080003545a0141191210103450b01a01c5034205540304400c03140d44000920038401081194000d821154010302101c00500b176850320340b8000012a000300c00c1c40c4d09400c3c0c072241070000d018824010210040001c0c40240203071a0b4904a4032450340d58400010009150b9030001d00615100349034070b00c040e100c010200c8080c0d00703029808a40d6a1140041660581d0105034521407050182c1300701e600c5810344141f46410000070204020305003c0040081e80e44516003820603c00c0d030040d1007800e01001050720b0700c000c241414064041120001080380c1d0900142501600c02c55954206441e405004c0503c2690300b60b8681c0082442410300061490084101c028120203500c0326030080d00000780159519690f00301c0c0c0008203c3c5450540250581603440012008040340d40b68008080814002d4201e03110500091248201000c022003c0f01c0021011002d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 600815674 1250 600814424 600814429
    0x120705030904180318050d0f1b0b030a0606031a130605190e0105060405031509010b090c0d151511010209090901140705030c18031c110c0a14040c1101050114 69
    0x2503400b411740345000400941800c012038a00403003d40e01410307500c8070031015020400c90b0041000c02880c1520340c054010b035034001010590300281c03100c0941c04d003010008504c683c401d1080b07003c1c2020750000c170350010749604180704070360300002c0244031210340714030b000304180e01c030701c2c10141328818190002c400c0c55180419a107503005068218034800c15040000300540d9030001680546d000e50700c050250070b62141f1902600401c240700d520f42e000600301081203a102080d5000d06013034459050140040c1d024102c900c00b1340301003400b1b48248807100e055000034091240c5d281610075480c2c00001890000e600d40001c0e031400f070031960fa007143d039103c2d41000442010517003181d030070400c136044c80781c1035041101d014071240c045c040d41d400c0c2c0a40e518800100030b5a0800c620350076500411800c0c80740b02c072266002081d0000c24269154144504914a4a281070144141c1c04a81000e002c0b0310220401008220103403c01d440c0860070072031807210f20000b0000030720a15008101c10300040001c258190103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 600816924 1250 600815674 600815687
    0x10c051b011b0b010b0f0c0f15010e1308030721020421380a050a110702130b0109050a0e070f031406011101020f0c0f0c040203010303021207050309041803 68
    0x2c02d0301602d0403009107800080b554006681510402c0c0c10b0240c580c46c40c80885050350280e030006440320300c255092000c090502040f2280e90b4a00445207000607a02c96014007071004044d81c0101d041802502c0442c081043e98003e10703007040d9a40342c1004141038400040700c1d402c0c0c840342d407010402c1d40060100045440000e075082d100e21500701c0c4040428558903016000002248031221403680e400c220a200c004900c6811100494081d07400210705210311030f240109804c460355440a0302d00144615100070000030784081980c001d0403111084c2a040d03030f80024000b200c1140341030101703101c0041030aa032004184409800302100758546480c0491000740360f402c0c406808410325143c00314002c0789025440351035610020a00303007a28038400e4620f1003130083c85140200c1da180140401c00c9400083d0109202100b040c084d030440b01c1c01101350301040203c0c40701713220003405680500c00c6046041e5940300a410000e001b1010381c1d040c00780c20004141a100500c000c200f000139004001c004141e0004c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 600818174 1250 600816924 600816947
    0x31908100623070302120412020a0b1c0926070b0109060b0a0e03160b0a080f0f0103200316050306090a120c0204090f0311060c0c0d0806010c051b01 65
    0x2e860b107000724654844901031404500003485525001034610103141c0204116120031501007040c2c5c0da25680d400b40503c0d03041da4114102d00c20110b20100007025410030b02035034130401c541032805c071100d5244000382005240090b021140000102510500b02c1c0c000303400c401564000030109580c5901c1071a044c0c25524050308004507044c90000240030300d42d02c520540d44400c541d42400d206041e2080b0019203407101821008078443c0b840308022949144020140c240b007801c40d201e00c01c0030745840124094540003210324010540d406801000030541e0755020008481c4d4040310f5120304d100c40c002090400d08060791030340c8109103031403003000075042c10030a1607400400000549002451580c4a10281010440b41070030001d010700900c09554440d0f004200155001031004044e1030217150103060701c80181d032407200c180500700016040038404001c840ba2918080040c004200041106a6541c0f60103400c041c1040f541c100c02d0000100100801e140301107a0a81c074201103104440014035034080103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 600819424 1250 600818174 600818177
    0x130209010602060c0f0705030903100b0109080606090a02070f0503130608181c03060504020c07091d0307021011061513020c1203060402070209040c03060f02030610110319081006 78
    0x10811141c161300300b40c582141300c0c524219554425410044c0c614028a51910340c10b00461050700113a0940e40c0c03011070840400e8030791040a541e542c0c002a120310003200d001d0b0b04a1007403000141031801d00e60042044030b100e1070403060704001c184c51b51483c5403c075541d0708891405a510a0080e10380055500754410b81c0561328054015007008803585859005604070961198814480c00240c000d401c84009000c014100319120307803100254a9a80100e4450310926a2a202c401810302e4890240c6d45121946800114546000350f4240320036503681400758020040c61030710b80204200c1c1401b13003d014800402860442c011312204000307080740c00011500600d03104110510420f200030800010608990700225100d58585000c00c1c00381c40b4450000750f110011104100820040c05802410b803070142c1e204015001d04c0c071907944120f02c410703142d242c2c0c091010450b4400151040d10140000c1d0000c00640b03052102c011110600300c250203202001143c1e101040141e400c1d11f81c5c40c202c1c01000746 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 600820674 1250 600819424 600819433
    0x3160c0f090609060b0c03070b061f090e15030715030902060708071502090f0f0d020306010b1902010b0a050f150301090902130b0a2610020a02010e06190f0902030303130209010602 79
    0x9106d405030392880341040c01080892010001103060f40e81015071026141d02d002550700110079603a006103041024019010002c0d0808045600090b510708a4000c81d407008c0c00415142d402c21000740c400c3e100300da900d0000c064541d01003a0040c0c9407c00603000140c0f03d24049615041245080f07900c1d0a14001500d814510522000c004d665405100c1c009000013554003010b42e44444012689541c20443c020b90144140c000000b000801c1600505c40e204030310006d082104140d0000300d090764070640f8000d0f801082c2c64014445403400100c51030714100f000f45040b800e01201150f580c03e94009a01c494a015940c100b40c00c20f605003221005011405007000300503000c0c56900040f46007846020300b0302000c1040c43e010300d500c01201c40740c2c0c203190b200004840b0000340740b0000c180a0b50000c96602e0041d400c04110310003912000540c1805415a24609420b41a400806d00000c01c01076003966440c0c0d40358a031030b0300961030500040d40125581000c001c0c03228070500611001050607070028045502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 600821924 1250 600820674 600820687
    0x3070c03060b03150a0e19140d0806030a080c25050102120301120633050f0405070f0f020109022d10020d0f050417070603050a0c0203160c0f090609060b 67
    0x41d032015840d032042c1400720000300b508510802a00e45416500004c03000c4400c4501c9005028004d8031a64102e0100f0044480e1074849c480b08039090030040c3c80807605a40080e0b00a00001c00712070140000210880c11a40d01598041608400d55120003101c40780c000d64403410701540d60b05001c0d0400d0004500354170392a552400d6080078125502640c0a400c1c0380c0d46242c420800340d1000280c40e8011b0021004583c040f540ca000c54030311400c5d510480d0f124000780d005c0b5603410b0805000307484c03040c40641c480850344441c030507054580398401a1601c0071550380e0010f0200503581c051090080d804140b400041900d00c220070010008801010399108001c240ca603107003000e03800246000d81c01a145000b84002c14801d40c03e81d0203010320303003201c0100b150700c0400104607540090030204665066400307124076151600d80c80102c807600e00b4043c0050b0020818121b541900c444030308650762141e080803907034560311510844200f5558200c03e0a00ea1100d404125240a138000e200140045a807954075100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 600823174 1250 600821924 600821953
    0xa09021305090d2f070f080706020607030525200714010309050604240c02031206100c030e1810080f060606041205010f020d021215010206070804060b0303070c03060b03 74
    0xc00a02162031080c1c00300285090410520000b4000c195101e05003440ea40c45c7c8132041d071500500d0003400c4c018810b140c00901c0182c440e00500d030240000b1019419600c0590380144801c00340705a01c8421b000c400f28200080030f50f007a6480c0c40a1510f0b00c040d1000d03c1c00c05080c8042c0c00d20b0442050f042504081c2c0711000f045000c00c07071513041940052001c640d0046401561b50710307500c40c2005d582a40c5400035002d153754020000b485c01c445ca0304c025404691307401c01044207810301e0f10b00e402c00048910741c0510000b40540308400c0000310003841c05452100258001ca25280121403100c0d000c030420a00f0021030310100a111107090341480507200324070301000072078524040e9201e18038840c00d0300003418060150a5004501c4d0300d491205c00c5d5500c06a60300400f011354040384045080c29100d030b000a0301170050b05051004ca83c0705a015100d1600c031000304071a0190003400950b11950380b15050490703940e0400040104902c00c4582484003403440c1060006c07a4481d000c014040c4d048884c0880500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 600824424 1250 600823174 600823217
    0x150108012702040e090c010311030106030c180311270a110d0e06150a080303150a090c0e01141602102c040b061e030a09021305090d 58
    0x4445514050114095041c001d410864038102a261440e10001d00070a400584803801840b038421340040382da46a40c0c2034011012100c5400300032103146014001803152501c241c0001040b1262480c01e840000d5203500c1494190180b640100e0702c90401c0c40b03c070402400c0c00880e400d1403010701c0c500740b17030300103019024015140ea00801580426a0794100141002501810f076056608215410021408415120740d640e02007920030000b00c8840c0c050303440c1c0302d1420b10942d8091b6908800a1811611a4100c2185038013200b030030540d02203112880403520017000d01c18810109400d5603014000e01c0000000340c20314114003402c07284000e0800c070f4000203541d000300c400d1600c1c1d81500c070b1201c400150385084401c1c03d1588100d000484a542100300d819440c81c1d020420880100e5040003484151402c01045100e01d412100e412485185044c5030034810030042c560050a0010100c9c03114031f241d00003804c51120421211906542d542400182c000822504009004504050540003640720070404c1c0d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 600825674 1250 600824424 600824429
    0x6060f0207121e050705030c062d07080d1a09070c0b0406060b040e0105030d090602060705030c070b01030302011505040605010c140c100c030f0f1407020d0b090a060515010801 77
    0x2000207110200204590001040361080c2d0240300401c20f120185041a12002184106840303849201c40c49006850503070100e4000e0020301880501c84080051a01004039001d10686e4006105000090105100070014440481f44201c0011212108500c4000134094240c00b1030143c4503090401419a80068480029075042405038249950b00d181c40c0003d40480d4200d070024110100e000600b411210f62402c1c10707500300301e0035034088000b103800455881c04144a0000184d1020300440c1c03003e40160000c40d00010507800842c5840c01545450306050020707801140180c4d59a48080602940d001c40722000d45000c0b60140102ca26000000306017000410002d004010f2010810f01322044c200310840102c41c028008008440031054090404080e0707000c2a004078055038042110a803003000220241c000b1038031100303c00303c600780908a0541040b03130120307080100c0015080100d260300103405c1c80740888034014021031050389003003000e0b070380080c0584088111071810746106a81024030303e810f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 600826924 1250 600825674 600825689
    0x1b0507441f1b0c0c4506060e0102120c030301050d030507080301030c091b0f030b030a1b031709060d0b12150108010e0f03070b0907030b070203070c0b0c07030303150e10080106060f0207 81
    0x120301c11008207003400601345c458540ca00620b06000001d5440c2c100c1144e0040c56002d03006c0e40d0f4816410590350455116074031320310070700d6002080148898501240303010350b428041c4c40c0c55810a40d20380c5d1011600e5000b0380080c0c2d803a5519400c1009601c1d002d0148116222070629161404200300d4805402c01e0340d0071603030100b85074940030329506c1502e042001d0691907070020014008400c04050001500380030740001e443c0d070440f04c4140d420300d51140c0c0441d00070b0903001c0c4c1001d1a003045610103000506000c80c40e940c1c0810740281c107240c030250170030490410340a03c40d0001c0d0b1951400c0121800c54007005981c49480d0007211520001890201c2552405904071240341160b03500ea4806d1402c01d651030f00003c003c6a44403003805581a40080a012014491844900302540301c4000344014010b01001502070f0f4450b00d000d000017880380d040300c0300707590804c04294000c41d25407041c0c540c210f5040b01c110b06130291202d0104803188090082070f008150030708040e06e0074110200001e4070703040140507046 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 600828174 1250 600826924 600827009
    0x1309020f1611030c03030301030b0415061d06130605010c0206032a22080a0204091509080711090402011b0507441f1b0c0c 54
    0x94080005408403000000c0e061800d000c0d141c541c1c07500d8010b01c9860040035010b072040844215850600208072810b8035004034603a0190354590b611081c00d4001d4110320340c03005031101c1c000281d541c0403850400d08101104065041860240306020703030318401040320b8440c0c40c100b072010406a604211402035458041da4000d45e03a541d603120304a50000c000b501580c0e034580e40e05040ca4405501c101400003109140100e1f21504c1c44092240314044030787c02118030310b070407540e0b4480051915a1110204601c51107a210724400c440388980100c071840078050f030352101c6c000707080402c102004001c448081c03000c41d04031600d0300340394000901d1440004500c0305a51024800d101c14090204000c0c4001c00b1400c0030004610411012903009040c6130b01000c045547c28000d402a800c00c2440f0190082d11160047c44240303e20071503180700b215583c070780c02c4400780c0c2e40c482d00d40148418180c0411403074250b291101132120134074007000300c1140c82c1e00c001c4200c01d0a00300a420303540c0d8000442540300e09103c141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 600829424 1250 600828174 600828187
    0x1060315090c02121612021f0b060405060720030d080a02030403020c27180a0807030507020402160501180201050f09040b0d0807050601080303130f060b0909010b130b0607030f0207170c100203130902 87
    0xad4051003a82c000341e82c0312001040d0201001454800ea401160b6005400c0a02424032004d140c1e0340c241c40047d0102050407800041d4034800c0c558042c41d1f21030b010784115504951401d01103126000442000f46202d5490340c40744091544206460f0342107013580c40f01560f04080c0c0e1003525220340c40100024440030000600b203052512038000e898015400030421585c40500200506000c40700a4040380d40d5401c252640024801d401200300d0300c00e0301038507154600049111003542d1035004141c1164420354490400d002d41d03d500c0004018139100707001080d9189a907052107442c04105a103d00e100c0d50003082044004075004005184031a4404110b404040d03c03860710b04c000d0491003141c687c100c002c6000f001665038054000c05241d500c01c0d64801e42c0b04030384220354000c1e00c18181c032054021108101c041e000130300c14071001805180f1841a640401c1e1203118942c5007840c03000440030940e0020707158003030320329100c43c82c20171184150004500d40b603440804140c2031142442808411580840c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 600830674 1250 600829424 600829429
    0x11706161107090203010b0304060605010f0e0910170a0201110619110409020c1011040506090d0c0503030c0a0638150d06080601060315090c02121612021f0b 69
    0x104806014480d201350740703960319941c0c40c3c10075803c00c0b202502c9140c113212001905501072520340c60444015aa4840341c181c01d0024002040401703050242c20140203c80090b5034084ca4090b00c940320000400b51840e2003990000402c52003a5554131100c940280e0709101a260304103282d030085440303082c0c0204010b03440301c900c0c903824006ca511046000c0d0000858030350910000c9025100400030341010003034482c0d00211030410b8007960023660382200f410840c05040d0703d0843c41c1080154810f100220086440b040480d0075600410840012688140740d4501000403c0c0200340803507030050200202482c00401c00d80d20448a908440c05007003400e40341800300c1e15980c410481180380c403000c15568215289014004082c140324104041c001d4100102d4a40d110340112440855002607804c070290a10004800610780c3d030303094500354840e8541ea0b0055074505405808040e0b00c1d4400c0007010700e5903050141449060048850841d0007000903078bc24004012440042580f1400000030140311381e201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 600831924 1250 600830674 600830683
    0x20f0406030e0c1005120106080c0a0c0c05041104140904030c060e0120040611010902010e100c0c0e060102060604111614030d020c0d1d061c060602060117061611 71
    0x103c1c01e80040100c07410010a60700701d001031401c0c0c24180882842607a031a43c2c2107900000c00d44030300409030010812120b4552080e902d40070110301455510340c01a0755040040e00b16601c14a5941000c034021804001650340e4122140303c40c041039880031043e24050b60018400800010300a2046a82c0d19101408080035484051041d000c4941d41d00300500c42000301c00603411920a1400013030300d924068101d910103000d840d1605606846106040c6807400c20449260001c14002e4200032007100d26078045165000c012004042480c5540070604041d000203040c901c00502c014041c5040000912041c0707036000445401200c441c0003030b142c2c1c4809292452041d8103111034146c26100c04071704140d51125990040601904003000c40e12495a0424142e6a258003481d00c01c1c140046c142000180e820030400409100803030910310030182480144203404c0703405e039400010040c2d0040d80144004175070321000144010310003000300701910b0000c0102008075180030710102007001c92214016801800c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 600833174 1250 600831924 600831943
    0x10c0e010c060e1506040b03010b240f07110a08011503080a02010e0f0706020f060705070b0a2d110405030a0609021903050a02010810060806100e100e040f020f0406030e 74
    0x10540f40c5400401e500e07148144c3d42070b02c1440c81a490001410b8040c5414803400c0c4107414058400c0040e980390300045408100000144901c80784104030421440d8105001440410310408605502d0700c501014003981c00510380207207850341c2c0f40440743d00303100d000c0600900c01c40b9848020942d645049400481c00341007c40e6401d401c82c4240841d01e205a01c021802d042a20700395030031192841402508195141000c1d69610007207501007050101051310150919806044054007140b0100e0680007546140600100361408480301004249040394600450b46840c0d0000b032482e00305414040001e48514011100424a96039254518210348480001d50307078540341d0303001028510390350f41411910390303140ca003003280000e0a40001070340741e203001011a801d442642d43c03012040c0d52440d041c410084191320b401d10a000749103401c05510303650316107030400d60b00850384d0ba8007100a500c000c1c04292240c10005104103401401500c22800102d81500d01304c40c107034a030114460f411820345500745100308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 600834424 1250 600833174 600833201
    0x80307060b131409060c03060603040b090a0f030804031403010b12041b271a09070c06050702030d0b06071208040c0f030b011e05090105151b0f0708010c0e010c06 71
    0x307807126611103e50620307104d100c410302070301e03000e40d0b076840a09203074801220500c3d8000320900105001c40c8003002e5036a0b2060482d0300311072404006481c7c0740d0740c0c5100c0410460015001100700402c16600c42c140440e07141c000c5030541e080d941008080c5445000f2042542000c00701200090288500041d134000030f03e842c1171031260825211410358000a00880c200c151809000710b0b144130400300c92003012001d00500c86a500e0306400c12081044243c1c0c05000c2c00100140c1c26101d20204002e8856507005003c00e4006660700c00c0c4140c0c40005a44840600520880741802103d0105110300b1101d1032484451414030125604c034948030300641c59641101e00205425030000c410040ca0150a070705a6140e806500400c400c3da0080174800d0566010b495040411080100094200381103d581c0040460728940d0510036810048010358002d0b0b56100803030361040300b000680f880300f4010a005411008002d0010046501c005098100d5910b2124100074035a065070b018000340f613003c1c0030b01c55401c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 600835674 1250 600834424 600834431
    0xe0a1401120f050108030c06150a03061d010e0318060403122d050301030b0a051003030509030a0813030b06030f0d050d0207060903030c2006010e060612070909060f080307060b13 78
    0x1200140b41c0d680d00300c00d540000a102d482c01089d40804103d01803144800c00a0107181c40600310b55075840607280034110403042a1500d1041401310350203004143c3c0c11a1114011134840e076050404008a08034048140e02407002008144042070784401000081c00c02c0b410a5051104a8110f0002200946040c20004044c00802601265101005504a90040c00d41640c0c644942820340100c9006413894180c9003c9030341c00304000707805280a0000003000800741c9081c19055201c0d0b1030190700c00034602a000765441000d0080001c9070403c690040030540041c42c590140c3d4101c0c40e1b88001a182100c02d1010114071075486504540413261040d9000d44144a01d0446180290141100080480c042808951480d04079030610003004251581e260040105902c1d054580c090800e010f44440c0d0448030030410807000504c500f10b007600603007596580d0000280380c03000c22400c541540e08240400801e0f04010010303030200105890315507030011000949844a48000f80d407a4042d0180301c080e9504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 600836924 1250 600835674 600835679
    0x703080a0b2b030305101419050d050a060501060e060711060712050c0721110a0518010303080c0a0e211c030e01050408070b040c0b0d0c0e0a1401120f0501 68
    0x1140b003100c65003842501e05010303035207803a0841985140140503411054007504071500d404d142c640c50154020944081030040e441e181c2000c22441c81d640303802560240c1c040d034003080400502d0300c1024010722151030b200c030340488080002803207031040c0c1d40080c110300455032041182d90355141c11070303440300d50204034281d0410f556031010748540c2210600c2c0445014654000466690012620004000740c0c5400d101c6800c0503034070911004180304055410011014000c40d140c0c0341d085051200d00d01003415508030351302d189801000c0c4a4012304c4484070071018000e400009401402c505100311007100c610040c0a108001c08084010000c0310101e144214202031032045003600c5c182141e103460f96000d00c00c0015108455003030319402d0750014542001040b03050042400c403005990024030445000829a03a0380c007004030306810214800700884c0d65010107135240360300020345244402003075400d00e10640c5013034402405040b1842d0740328107006400740140b41c4600d483d404086050420752040180d540c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 600838174 1250 600836924 600836989
    0x14060f0405090f15010903020306180705030f0102040f06030e06010e1305060403210207051b150703020309010905040b0a0b0a030b150d050c04120206090f0414040c06050703080a0b 79
    0xb14150740071404141c4c0944060000d500c078042000c02d581d000340c024001502c80d05001c0c002841426003405c914002d1130070100c0c440e82c00f84260540344031003000150711141090581851520036900c000149440d12918103520100451018110342d1080c400f06a196141c881e040c1071002c0a400091049c0a104200810150400e6100c1d802c030200000400c102500d51100750f08074850107001074045e5021140001130b200000c2c1e84141d40c03034006004150100413917201a29140c20000045001d44c10204a020240d644900c1c000c0061104032014040c084a01010904112060042692820000540785a0b040c0681c210030f003050009818114180701c0504900711035001030605081072404d00000c5034040c0500c2c41a281643c11f0b40410400d004515401c10425500c041021500489d034900072004641d08c0d40300f00039142e081d42e0742661203480e00b03140c0540120101e0300102c00b400401d105104c082540846e10030350125005000181c2114280d00254424202c001450307039045040b610003d000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 600839424 1250 600838174 600838201
    0x40314070f0b06030307020904061112090c150906031b0c03040f051305071704051c030506030d020d0903030c080403020406121103010b010c120306090204080d020c090114060f040509 80
    0xb03004100382121a1600d07000c064607032103290006540300000d00b0124000c1500f5500c81c0780d0704441000c40750b01d00485090703140601c2a040351100d015400103c000c0784203007080c00c900c080d040d00904025140005080008900e40400340003101164000350203890f00d000480300f102d400c0e141c540102ca0310355039608400075000130b0500580b800b5400c5050020380c480405e000e8240120718035201c0b8010b161364640210718501d0003c0040d82e003442142e224082221058108129015007035a021403107180800c2818985031000065200f11b60003520415059548411114107403581454405420000c0d41400029401a80c00c081e40c4035103021000103a4181000c00c111f60184034140403c42d40480c102054222a000890240802c0e44000c803a400101c5201011012128a00340040c030513480e580d0a400b02d80068004172400d41c031000f80d02c000705404204050702140e0442e018084c640c1010940310382c45440c00f40045c014503010564102c412108010384018180240408070b041c0303010324012207075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 600840674 1250 600839424 600839453
    0xf0f0905120c0f060705030a05160803071725030f0e010212040c0f0b09010c021804110411030c0a0c03051908010e0c071121100f06062604031407 64
    0x1203034808403494003410b101d005c4c0c0702e100b41c100740030314140b11103402c094480754400030816403080350103c0c0d51800255854081c3d0300610b03040c0e5680c0ca080f02e000c0c04100c09124042c192140d10f031451140440c0f1500a0035242c3c0001c009840c010407a02d03803003c4043d01408103070035403c9041d400031800c40301e083d141c000342c54820780c0510746181202c0d40d0b8040c804010411401a011041010001403007554040c41d0794001840c07000e030a026420102c0080b2015524007a64201d544c0070b54034070340a940346040d0182c0e4103003800260301c480c074506040e4508211441101c3c0614188000150340105150007041a1a200080340c0081c100c42c2d100c11200030003242c424042d0f0400b903864240480e0f0840c1601098038200f65101c0c0c0e11070b10301c041040400c070990402851141400d11940811140310b039050008a070340003a040790205604c403001a00b2820344c1e840f90008020802507503d00c41c0301240c004000d48040d01046222221925039050407607040e04140d041034401e0a001070808108060080511007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 600841924 1250 600840674 600840679
    0x160803090a0510080a02070c05060c06010e16080105090a0e07140312040b030414070801020d050f01120c090f020d02031302010e09011d0c04030b040f110609010f0f0905120c 76
    0x8545488408024003240c01c1080c01c4001040071000405d80040c1c0e500030000c0b140990074041450f079650707000076000c0c0d00207075442000f9001980100030704940018003680090000e5500324075500004c80c0109440030510035948925441008507885403443c1d40494803091501003075512507a21500232054042401300d0150080c03040207055260047c0003402d450694500d50103c61440d201d03511245c510220802c29900341d40201107000a000409100800c1c00310645000480c031b03840d14150700c821804050707101c204220b101c1d0784464009030040080c482900c1d01707100009201c1c010003450200a000e80103030800858800800d11010207980300e40c50407568404d0742d87c08680800c44081c030080440a01c2105820101804a00441340c00360081e82d600040c01440542429901c0d01c0d04600c070300060700d055590340c40001c0550140205007a010136036010a072002840d048420000030200c0e80c100c1c05000410161801401905200b5051040103001c02004078140004030054240c40d03840c1030109070b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 600843174 1250 600841924 600841939
    0x7180501022103070e090703091e0f080d18142b0c050f0a0804030506070816050a020a020904060e0d021c081b0301090606140c071716080309 62
    0x505584000b80402c0c414540c40090444254065190300007034001130410001d2081c9070800c4203168070b40341e100a1280131075a84c086160308050410101c0b00d10740c00b82d0100c0006034142c1c8031010403803820034003018560000455a445004051001c010046c003040d0380c0c4489600d0000304240400001959101012a8140d407100e414400d0708440c0503010326000400c00078000c0741ca41009006041c2490031500a2050b5482056408003540c03c100100c442207410180106060044c46010448207a000c82e090404129a05100160b1250004000003100401900094002e10340b4400d10544404540c00340410305d1a0030580b4011000d00301d03280340e040b820b215a01d044240a131000031140b644605190805241c085040c1f4100c0352410010a15070f401d0707400099a210140c280001103000300310a56001824501b402c2e80140102c680044010205805000c91100035002080305e00031a0340c20048444070280008810b414496440065041a94407103000940d216002c0005c244450048a280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 600844424 1250 600843174 600843179
    0x70806040525050901030e0f0303070905030d02100915050a1a0a03080d091e0f0312111c0b0409080702100915030c0e0d110f011d060717030718 63
    0xd8484203006401d884001448422115660f4001e50007861302407010300d070101d410030200c400b440c90a0740c0002c0c10302c0d569100208002105500040300c0c8054401140503160034108036600039500c0101c2c0e294056103569610189080004410307480c0c041d413224240a1290f071030300c05680720040400052505907880a019000c203685403510000042c1da5000030090300380512652904000e0900c141c00f116110701c500303205150b03090030040c6035403000d1140ba641c525400b00c520307008055241e02601c1e070b00000d051521141000ea00c4a094036001d8041c0308003400c88040400560016100e1210190341051505807001c0600820070020300146000341c80c040020054a0022a80e8035818440e03103094803000c1511405441c46a0081c00300380c0b400d80340090500b03220800188480c5211b801c200c81c21001d0b040e4413542801d00f110b0300441000d003420070b801201100c089000e420241228000d200d00c1000410404100010302e00c008242c0d100c4071460745901d01038102030030848041d4003000000100b80b200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 600845674 1250 600844424 600844441
    0x30f020a050706020c0a0b090313140a0504181b0509060a080d0503090f030d06080105070e01090b070c0308030108150a020306011b1e0c1401030b0312030c0f030708060405 75
    0x21900c44500d10780da00d5280000d1519810f00940107a11558070318094851441d000c114040d50300f034021540400911b0361418000c035010ba9100c1f05601000b4500403054040080c0d585402c025801c640060f5004035022000442c02c1088195400c0010494410907540901c400031107036880e41614800c0c1c600354180d490b1181045180d5002d4499580c1a078440388001d440f440c440c0c80510380105140d4121009401d0080d95642107412644070b1840755940c0d001c080015240900070b0035002000c0f41044143e44840318002480841980204d1601c61800100501000001e035041c80046400c00e500a4980d40c43d2b20f07400343c8514000c1e0206d800e0341c2e40c0c4408034941602604c00c41e8041c0505031141c2c1d00300240b54403180107642c0000e40c25142c0c52400b10111000c0c2060401103803e4a115510030a26a8285001011884400740700581018500b0000d4165914005100018401441c40c140d80726901c481f46c9501602c030314030b4190780e443c4000c800e000e44a40c10080d6580194000c0320148029a0b65500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 600846924 1250 600845674 600845677
    0x60501030b011704030c08160b0a061502150709080304090b0a0f060e09070c080a0906110c0a03060506030a0507030515010515070f0206091002060417040e0a050a200901030f02 77
    0x4003000005030303c804100000d00464642d80464400c161490a00ca18103100348002c1c160000283c4401e100c030020084007114038031404002d0074882d501414242e440d4200207545600c2c1d00f400c4449001c0410101d0000e500407401c280c011b004400c00c607030350349071125a840040c001d2410310a00540b0900004a0801c0c405040e1900341c0d13015a17100e15850500c5030802000c40c8010b41500213121a50030208049180c62005010b10259034441554552402c1002462600925908041a0041f9103414510743d180c0b1240c030f040b01c3c1c03c1080400e89403104000281000e80f4040003e05510407550b0000800101007480c0344400c3c8404113010301c45c1c1e6208284008004198400d40c403040b02041204001a0130404820b1210f00240030f85040071102400324503090004105000580e120404020800c00c0c100345d01c068440407521880e08003807401001101124026000204294a45c2c0000e06500c40c0c3c3e50085154031205200518040c80310103005015030701c00c05c00d0030b0010307040c441482a04400c500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 600848174 1250 600846924 600846947
    0x3020a06030621030e100c110913060207050c06032505040f0605070606050603010902040f090903020304060c1a07170a1a1c02030607050c0f0105010806011422060501030b01 76
    0x1901010403481071549140f050444400c40a0080074846040030361600060841c80b036406850740c01503000d181c18a48a40008144d40342e00c80c0c0d0170b007810050705003010903895442960210340540c44011518009060490404049400c524080300f044880710340100e464480d99290100120010601c034400c42d140d02c80c40c007851404620307101303040008a1052005018403402800300040035504e420000341168003e80c812511150081030a01c90000d000768028000c0c02503142c20041c6e20391a07178020b0f44070701840c490354051040200700c10080c0701500c0100f0200528440210780c1d00c2c5019000030b40104850084080c49402003c005a1151242d11070000c3c85500d913185001c2c584481010024070a00d0038258403044400c41c1d95820041c0c40400105004024070b850702612031a10300081740ca0700c903264a088010340c2c182401003214034800708505065403016030452104200101c0442c00402c0000d034610840260781850b0350f401d0900ea4000c4041c0d5070240d80c1401103103055801140ca0035001c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 600849424 1250 600848174 600848189
    0x7050d02151501051c0f0e0304080c0a0f050609011202130608010501020a0302060f060a0504021204110604030f030320070507050307061715180a020a03110a020309091f0b0403020a060306 82
    0x410807501176000346264400d411101c0e20300411704580c0c20b1189402d903292690080300c01d0b4804a818004c5000a020700030f1050130680314030222619280c072507292a1304500c2094001c550019005020364443e400c042c1703440c2460380055540d42011803e0900c1d107401032040400250003480003140c95880481e544c6501501039008084903110900071044416001e0900e43e80100c0060000407680c581d40080c00003d20f280858008038501410700421900e48211524850581008140001740307500c05400c0c8140e03018500090f200046440c0300d1104a41901c1e4090140000308004080002c009001d4003a50015001d595405a0381d03142600c0035031554a031080c91454040c0040c4200d8002c400460700340740000c1c180301d4a064049100040400c0c151144501140c0000b103124032903401d4054003a0041407460f5540c80c1603c420b400948074001e403c50a03100b01024004180d413090650254240e0700750003005454902d40d142c850714038940c8544801ca001e0b4026002c0080c00ba0b029104075011600c51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 600850674 1250 600849424 600849427
    0x50a06060203070b072105091c050a05030c040302061903110c0a02010e032d0d0507020a12020103140a0f0e0105100510030e010f0504060b0a03031b050307050d0215150105 75
    0x413552108401d8100801107001c005a00c2004c042c4507213840c40141d030454010000248a05000e00310328202800c2160928501d88407545040131283d100003140c01001e0349290042e01c0c0d480d02442d401d03561282da4406980150b0114003044c2110421808850011050701c08001c441c0081e07020410300e01178180402415040000b0300c0016500460307105092400040903903c54101c418420684010320b910030b100d695030354020402c0381d1038042020080071032060800d1814a403041e40000c0303041c2018040c005411496400e22400c69000e40c00000300baa4500040000a00d065854500101480d0458601041c100313005281060010301c101da0244a81118540342c0c1800d06c0c0a005c100084020b65204050b900c8bd42c0447c2c108081c440c58403110042800416141060704006041d1949000b0042c460011b0400410011360080c251040301c040c0c8811481401038242803003802d5000e03641c4080c1c024002ca20501130001e42c0400c000340362041b060310210454032013a81240341040d4002c9000c0c00b1960 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 600851924 1250 600850674 600850687
    0x906010206010308030121050114061005070203030301093b010f110a0c0f050f0139141309060e090601080304030b0406091a010501110c090619050907090801050a06060203 75
    0x5000641200309840560550b106841f81d03079580c1c21a100c41803038115242c4480c082c80454a018060006807200364901079060080c03513000242c0303c1c4030600c07481c0d02059540c0c44044150300712041c6082c090540004405142c4101489110101b41480c02c6210a5103020059650003041d84990361043d00701d034104c030342000340701902524518003114064522040138060b03031f000075008001c88590002c4460004c22154801303040001c008003c3c0850311440c03007a0b00c0c0781084880607107140301d8041c0b1407450814141200061000c002d4881d179400a021b0980b10040424200425009401190040d40c3d040d6000d40e5a0408283c03101720038000c00000780c20402c010800301345800c6205801034014107000441180c144d491124140402d007500c219401c0380380041205681100c1c1e1400703002040d2001c4c0c00c1a6030640c00042440380020451842070901c0c810086103041001c0444000d88005805500b19003094000500060001d218414156003480d0016124400600402013144c0c0e8a03002541480e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 600853174 1250 600851924 600851939
    0x80106080a060902030a150b03060a0c020a0605102313020f3016021b0109030b040f061e06060c030c020402090d02041a030106090b03060f1e0a0b09060102060103080301 74
    0xb0391100503031789480b80c420405c010a01000114400400004e00010119070760010301d420300c2c038000d00c0207688924100740d60901d2034011031907005040d131000c40000c143d07403080e04510240709650403200300c1009103603030043c0301c0318202c0108080358021141003410190500012082c0e110341c4143e00c503c50424410380400781980b0302c0c0100b40d00002046460301428010b031115003604200c0300d002e003214420160700c9030f03590180142e03030412800c0c4204400c0c0911010001c0c0c080c3c40c0c9072100034084200040040c0c14840528100030f522031b8402414050141c503401c880c01600c6001d130a4050540c030300000060158019800b500f449945500d6460101d271203a000c10000f0341103210400c0c0c11043c4c003144140181c0e40d80c0b14884003503441d402040704079100003081c14211411500512003062030941c1190507503a001402039032024030404c56844564030390424100c071000c12042c42c2030640344a0188881e4030529005a00c03281001d407034480c110b5403100012a5200b00a100c09820345808000510100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 600854424 1250 600853174 600853181
    0x901091725051f0f02070f060b0a1511030c070e07080c031506030603010e0a0305041d0c0702120708010509030304060507080f06010e0402070b1f050603040b060f150a1107080106080a06 81
    0xa807200c000410340b04042c8201305a80c0915003c503040004510104100103640c46440d16650303040d124400d2316401c0c03c0d03003143c1480c1d80a03c0482804024100e99039160401c00c204c4010003000c5040d28043c65a03105070f84400380b01500c030701c0080b4040a00162445010074150780c410f60901c403030100100c0041c1c09000c03031039101030008e54242d52500c05542c082d800030003003000100e10a40d94a607550b860314030044414507000401c6d60112040c80b041c00142c40303ca000750740d401501101c419807111116035029140980c260301100c0315500b410300f0030200d50400f2015511440c01800c042c00155a0105c084410070412289500000d80220100d46154482c0650340200e0070701400051510940b81c5401f0302454040340c86904c104c00010000c103000d1920600c0d200106420760b1800c7c114285070703441000e24a402000e481c09101d00d04240e0030f40d9540d80c10700c2c0c0340a80700d060056903501d5646000070000a03000d014000316200b00b9800040c0b40747d05215500c226140301002d010010015035509014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 600855674 1250 600854424 600854473
    0x307020f0d0e010e0a12050f01051605030621070303020d03230f070311040803090307050916080402150c0307200d240624050f040e090109172505 64
    0x30000c0340071034002050446072146c0ca006400600d0f2010381e5100c05400e40750000c2c0010000c40a000461048035007060950350880001c59910110340c000d21443e84d550759009042c014248208a8000103142c2c000c036851000700c01550341030040c10050711a14660301201011384e00300e0803020300042c2c800c0165464450308550240380115102805c81c1002c80e00e81c0154010143e140c00019400c1050314040104c03400814064614802ea0300e84101003004540c11801008184401040003504644d15165044107070450b18904039102c11071648c2e01940c980050700300703d130f1011400911044074043c200d0349140200300104003003980b440302d0785c401602d0070040c41d0a030072040c820301e85000c21060901030b190260600c1c042c01c400e01e03c2e014006138262503801c4445820701100300507405421b00040200d03400d6424240000007152070781071016004008108024050084100c101c80040030032100402d810418003142800015a060600c13000406181e402001e5030b100300d01100f2030200080c0c00144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 600856924 1250 600855674 600855679
    0xc1204050a050f0d02160312050708040f060c1a0c030606070618050c090a0e0604080903031c020c100e060609042303030a110304032703080f0307020f0d0e010e 70
    0x40340c1460b81c41615169004090341e00541251008840c42e030b90401240c9400460301c003800c104285140c5802001c0d50500099000b08280010108148481001118000c06040000030041540c3e8100185101d84019040fa01e800580c0400003020482c5042c040c0181200368007280f958948008100c201d900c13a050403200303141c48248d10207849951004180c079a0f80208017070f00c036140340402005492a4002c064200080c98250100c41030440000d003507070701035405105d4070f580c0c5204500191a5014600c200198401c06d50340040c0c040c2c00b1500908039185456049075119040c0000500036504841d44070a041d038070800001c0c10030300e07003003841941260140400b41c51502c02e44450412108004207045e14581c0000103020710f0310254850b80d0241f4407000d00550a508055034001c0a040c02581c0301e0310348140352060303451104c0d1000c01542c021030740090255658080d00d0409501034104898080c09030007560341c4290320318030100d044405000180e0712081081502c40040d00c05c0c40038040f0303e54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 600858174 1250 600856924 600856933
    0x6010f0c15060905091c0503070306180c120605150706090f0f0312090305070b07050f07031205010b0a09120c0504091401060b09012f01060b04080105010504050c120405 74
    0xca0104014452071004005001c650b860400c02d02c8400c2e600d01404078007040c0e0150400d00242c2808655041c0d40745610f01e80969241c99240f41103010b0071141d040740e0002344134000048900000f50b4440c0824000d142c13104085d00811074000c8084401c2d61103100c0d0000e01c1c016a0703030b4101e40441c0c02454100c0c41003c1c0019600c074280c03500350004080a00c115009505060360100749a000500301c104d80b08007200c107200d0b803881ca40d0010b01c0307409411801008000850b0100b01000d0142094800c103540b50580305480e008079003802001e414440241c1e40700c2c28508000403428508250895070700302c0240e140d10b911146030542e9012001b05110b815a80d4081c1e030840411076646501488203594088d00303c401c4030590741001e103400c44c0c2541c0d102e445205070402007092141d030804e4035296944480d0740106450300e183d001c0b05540c00150070102d5002e518000340407802c550404050012703549080000c00c02c03681c84806010132070f02c0c15a1000084d500901c8501c3c0c41c0c0d1143c0c134550394007500c40c9060700c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 600859424 1250 600858174 600858197
    0x605040e0c1207090603060e01030c05130b100c0311030f070f1502120a180201021023010b040807060206040f0b04020409020d0b01170a02240403080309010c0e010507020906010f 78
    0x4003403908040c0d0703007000004c0c0400d40400c03400d80d041c001c07140600744552101e40c003945180e845c692102c10750300c40d41e80200740d04800c9200d4098960312941c40300402a0a6500581a034032005141c442c2c60641103011462140d111690041c1c0001076481c2d203904458061314040c070a484646000568820480e41c000a02d035621303203c403290340054042c100464105000500740800c0c40b00a4800400c041c0c2d06003200242120050307030b40000c00c141408444040000d244014800c50404c04000c003182841e0205260000070300018001d0080c41103a004000b5101c4c0c00b526184103e88602c001c1d00c01030004050b402550340442c111518158010384018400240c04255a000c285a00d650706021b072011091100100928203181d030340071103c030306100f01400625500307a00050055071805070642800c4074441030804144044800c072800703981c100c041a40c4070301e0018405070107072045650140004006400b0043c480d40254103640c0d60980c010501281b559800c0011214103d8100c15401007042c0c24005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 600860674 1250 600859424 600859447
    0xf0a0f11120708060a060e04030e0108150301062d0303050306150d0e0a0213110417070302120c0a0506120403030c03020f0a080103050d17070305090a080406030b090a060605040e0c 79
    0x10b60700201044006401c40f468049803c0040700e1456001d10441920f64080100095012143c0c5919240909200d13019483c1c03c24000404503c54007041d130990301c0c00001180c04000c4902d50203031100318a09584110201d00444030f41e20f00300b44402008200148042081440c24000340c0d8184a00d1140c02401c01c2c2007100303090282c803c42c1030140c1031500440b030300200b0750419940200b0300710904003041c08400d220030f0084000c2c0c801c034492460f0f2a0004203d81c4481e20701444000000d50f00240f02a580e540c2031592151604021070340c0922401940c030001800d82050b4080e562408500a6408850b0350b07180c0302a000342240d194105c041682c01c00c00203540b030340c0c02c00144c160010700d83e8411110f9030552400a160080d005da14600b480000300031384509181d00c41c4a50340c0400a441c01241c0303030325010307410351802d510000c6c020444540402d0104403598142e120200096040341c042200e40c46008000040790701a000d190f0000d20204810302050901856254000d001e080e007aa140500002d030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 600861924 1250 600860674 600860683
    0xb1503031801032a0906030e0c01030b0307080109030810051c080d06080d020a060f110f0c07030c0e061804201305070302091002010209060a030c0e090403050405030f0a0f1112 77
    0xc10713072440007a401200d8443d940c420b200d880a0b01e401c1c101003219007200c4203140d6840c410285450b04254898241240d01d0700c052003804010980317000203110300d03003003854040c10005c0200c44040b40c0314564413000070700c1d1030048514100840c6071385448014825a490b0b20302168814410041c500303486110026000e00e0421280102c80c205901500c1c202c1d0451400710f09a030310840706046010700300005841c05902d0801194468613042d28003542d83c0c0c564443c000c0c1002076590000c0c000f00c040040000704e0f8009140c0840c882c0c00d044403501d01080f020002c40000910569001c0d080307100e07071030311825140c00003080c0d2140100f008000e8000b40f494100400140c500445010f0002900441c0344403c0b401c00381c1030011850018002542004d01c8180424840c5c024030548071704040d00c8204445400e4011801025103001c00750980e40d0320319007810060038030303403080c0308550082c403500409442c41007021410042c41544401c040d020203800c2c0c0c8803407034040040d00e00680e100b19107803004c0c906c0705810003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 600863174 1250 600861924 600861971
    0x90b09042706020d06060914060307121b17040f1101090b0c01020a09050a08150c040519051c05072603120718031e0c0801090f0b150303180103 63
    0x200051398a00100e0000401d4458030b074401818803142c03450901c68070200075406a00c04400790f520a0320303035803600c0342120901c0910b00051003d030304c3c0100d40c0300301d044e41e80f00c0c0203045a50b54841c2154103d0007042d6502c5108221406000d80f94284c0d1036100082525403980c07241c842c14036210031a03a03141c207400d0355141d1101410440c00d0f9800160aa9220380056000300104821181da8401c00d02d400840c80c6c85001c0d00340e00004507121603000400723861800040d100905005000b03842d403802e1004614003c0300d910b0103060703c9513909040703a071216001d652090342c059a201d0081c16840b86012038040c0502820000d0070252b44401d40c00d1400c8050400261145030401c50000ea01400c0118024103032003005003d00301d020b0040c02092000ca00346241d400703a1040d07080005240100c09041202c1100d865030040c44465082c000e0140606c101f4001c04401a409000c020020f03440d00c021100090f80280919901904180100356845151441d4200751754410704001c030340b000328280c1d890b0444000b207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 600864424 1250 600863174 600863183
    0xf09010315090f06090c0203190807140d020307030623060c1905030d050a05070e1c0506010914060402070209040f080706110c010507110c1c05010203010b19090b090427 74
    0x842040082c02c0c480d011ba5103400c2c1c0140003640c50003003240040945008407103440b03401c8c0002d50f80490542ea1050f4030444030151018000b0f5242c203e0046024040d52041c0c40d28400241030510103c2c0507030714081501d040c1044001c2c50384000c07003104180682074000780c62094003401543d800c006011101000e0060452180c4003071035991007412104c2044400280c61000600c2c0341c1030030000302913001180c81c00b140c0c1040361803020a040c20045005289860100140f0364000c620001440300080d401070301080a05034000f5006540300c4051004901840101940c02070282c0040303804544000305510341d417401070018038506a12a05c03804242d88041145034141040042e00303452000e000e2240503041106413401c5031500c035288450503a91104803000ca840341c070741d000c40410001448484103a015600c14001e5441e903942e41003285494100c1409500b05000040c5250102031203a461070341560451000307181803079a034500380702c000c00c00501c510f14402460519240600340c03a0000602c854401c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 600865674 1250 600864424 600864431
    0xb04051003030923061605010c0f0201060608090312100909081c05150402180a0f05010e09010e070804020114070b010f21020d02010203041a041a0f09010315090f 71
    0x540c0340060003c0115482080200c0b042103124401030160400300c1e010741412100e01c0c0d1180b0030030180b40a00802c0c1940100158a000300d0050030035023100004580400540003000f1250f502c0d4010351710f204040351840580d400c02c0204c5403c46030002035a54026400038403030b0440f0340d19000c8020840c0e501c0b02003994900f5000ca08001e0307080c20071174400144100e1440600176414501e840d18610140403084910035500401c1c0c40350b12800115500c072200f500242070700b01055841d21009102e8031903009041c0011070841105440e820004000b41c100c13400c035803401410750b585410850721005c0242040b4108600b205140d207180d59410040d2013814002d0344d070300b0855450729503010240520b40d07102e84205e8101c1c0c0c02801c18030422000701e8084507019a00021441040c0c40100e0031031155070062420580341c0340c0c4084480455002030000d035400002c5080764071842d446800d1050113282502e164045041101c40c100307500c641c200030300300740482007134805c0c4580313a005000c00d803000c505224400b1640e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 600866924 1250 600865674 600865679
    0x60f0e1e06010f061d03012301050406061407032601030332040302010503061c150e0c0d15090b01230a030506010501050313020406030b0a14190e010b040510 69
    0x1440780a00400045910514240ca070140241c6114001a25800040400200e040c4191401e40040002604c01c14003000d0a03880c03401d816807854000e000d02401245031070713804540d0500825465070526a4002200d06082d0140d80458101d44402207400030820420754203420b641070070f0000d5000e54842d4607203030b07002010201e061400c02604a07017524201c1d11168545901c000910480b001c0e20340a21300590740f651810017050282c0e10301808078030313421100074050051005103480300741801d15104040c00307441078841d4155a69140284107550201005c001040001c196500f07004240041402c0410021010748401100120980c00943e80c0d982803030142003010262482c800090900310f6910b50528250740f120350780c580d0140682c5040c000000081000d203040001d608002980c010001d0081540b07900e0109601002503440c52003650410b07901d80a0a110000441d210729509024039000c03010b42080313400a003c060030002665580d039007002085860340e0007118442e080c01c100c1503211740d2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 600868174 1250 600866924 600866983
    0x30d05040c060e032b0302090a0603051b03060a0b0d0b09070801141512090f0109050a0b010803030708160509031c1107061413050918010b0a080604060f0e 68
    0xa200400f0030b109422501035400300c0155200d00c0d1a81800b03c0c2c414440d00c840c010000d81c0207224490100d0f91050400c0c500184407681500b000f0302c40c3c240600310748692002000c0704034050109072000343e400144e06105101d1205000f0181640e0090100c000c19054404030110b5003860041d503660000920800043c441e9503262218202c142c4400e503550640442020000c001c42c0c0180c17009070110403031490228054501c10801c1074a4080084001c001504040ca04a03030f40d4405104201c80b03240d8103000001c0e1621000c010340e4031078840c0b5162004d5654603c2c82c0303040441050007240d403d211080c44011550f8900304088400300307100409195058082e0000a0036038200c00904100c0e03503000c00400e020311540201d820041d08607040c95141c803512643c0160703010303041940040f80c00c800c6140c1000301c0340d00d45480fa10b0170002c24200800c00d00800c0c405004144074603001c0c0c03100359801f21000c240001d68542c0a220740002d03d10340001c00c6141d25a0b81030916209000c12620440103055141c0040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 600869424 1250 600868174 600868187
    0x91212020c01020d05030412112406040b1f031112041b06090311030a0803090102071b0b0f090a0e130b070807080a0510150c0309080309060912030d05040c06 69
    0x4003400d000500b088813078031350010100d120040c001040c3c20140e0000d02e00c50790084260140b160010402c0d00c90f450055002c1c081040408604d88140c201c0d030101052840c1094850514041740180000460000c45070201c65510007122940302015a501c004d21540440c41c006048082401d1102d811113081070300304441d110030340c04071000c01c50903054000c1081640207880030003125444001d20075a002d1050000e81025440c50b000341c8220b50010070402c041f80198010b0203040d105100021814010140f00342c445c21541c014844403030800c01c10303065951107001c05070841c02c00007402082d01e65100c1da00d580074100161000e107800710020054800308080000c042c1e80c8050103180483c454a8943d038010004880039081c080d28598842c04142030242103170b0400098184099841c121b0700c0042401021003c0c0d20784180d001a24035440881c08403404411500c40c2c042c010042e50501c2c180740c00304154401c0440c0340c0456888104a0510100c2450090324410b6000e40030602c0c05d1860140e024150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 600870674 1250 600869424 600869443
    0x100513020c120d020405270402120a080d0b0306090a030e15040f1415070809060a030e0106030302030307090e06062a0601030b1006020c0d060b040908070c060314010b0a0302030709121202 82
    0x19004c7c24171061501e1000b09074441d40190121814101613662041060070701843e104041c05000e80081d510b00c610b82141c110f146400c40075002c48006a40e0f003000e1030713103030383ca046002000560455039a0066180610311281d2048241070b06602d01541e6010000021419500040300c81002014040f85480c01c0e002024071391400d42119407801c00a0f40d514a000e200d010300c003034406c0802003202025640b007a400b0741018000b800081240585904019640ba04210383c1d900000f20800300c041940c0c0c600c0300b1514019000030b00039904041c0b2103110342e29001854a00540c0e4185000c10200c2400402c2100341d008500070501000e8a0800d4003000380e5460349508034500759440200d01aa0b1703922881041d103030054212100280017100c02c00010040d00b10b00001815451000c1080e106100240300c9403011650a0b032801c2120b0074a001003a03e00640c244688401c0207028005003803003d0194009540c4003106181002c48182c441c0908404e11610080c191303004859800e00600701c54040003000803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 600871924 1250 600870674 600870709
    0x5010f06061b1709040f1b0309020f060d0e070603020711060306090402010c150f150503060c030c180a090914030f0f1305030f0f06100513020c120d020405 68
    0x4600800c9410010b00d65110b000080000c100700d0002c04545801000380d5007003074001002407012180300e01a010160044000342d10b45010085030100840f8000d00c20030790354903030113420424406440c00130081503401140c080b00310b440d22900c024888260034411000680304a480040c1c40d102582041c12802e0f5407422500d0054900b003003440178036602c1c1d0035120f90181c0d091030244100caa5a103081e000d414410f00c14248401d040c820000f0070145c241c0c1240e040315a01d4070002c012265541c080564401003583c0440000c0010800304000303c0c0035500809040444902004401e012800495881070050380070016150f0380d50340c0701040100d1002890003407a0148010350074030256a4091125100b0101400c503812070000305104c900202484040c010000102590b158168041c00306840e620b10030440711030380c00b42d03c3c00542080740700007005042e9100940414600401ca240d000000e60181120805502c20380c00840b021403403480041400f14800b1a015842c0d915140a00c403800070701c10f40741d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 600873174 1250 600871924 600871937
    0xf1b0a030b011217040b0403031101020304021f09050a0b0a08180705061b0d030e0d0302030f0f06010c1b08010606140a0e150705150c0a0f080612070305010f0606 71
    0x45480007012606640c000e5404603103203152880c00f8a8040b03007001d034503145000049800034000b892103000d48110384c0240c03246e61000a0004500e0b08070710080380c0007540300c4030000b440302c0700c5503447c0380c1840c4c240d240b400c2541c12940c60b4000110003c07441e81c010082d45400007125050694000040c0b90011307140702142440700d4046071207644035003090017800d004444c04600c1c2c007410350f079031004803451030100000c0d112071002e4070f80020b0161413510528030052150352000e214440c4030348201ca11030780100304030044d2512240c01d0112900405003046041011452500340821411024407c108403112031840b40a8070f040d07121070a60741e80794041170921801c1c00701c10308204211021107484002c18642000b105845500103000c3d007011203184041960085465410808001681840e402c41c40d6102c003e242d0300c0281d00703450707442000312610000740f40545a00c405130140000e42c0c1c101c580144805140803480760707050716021107a4011f40d8241e44588001d00505002d20504000c0d021514000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 600874424 1250 600873174 600873179
    0x4140c0f060c0111040f260d1b051e06070903021309051903020708070509011d04020a120308010f1a040b2206020f010f02031b0706020c0f1b0a 63
    0x15000400c0030055a0241e500010a020035002c20341c8a00f101c054102603642e21251603a551aa089004d07000342d0110601501d042c10f22199500d85808941c4002c1005003089402d00b44e046408209007a000c01120555401d0a0002030341400b481c0c00d401401805200c0e41980402c82501c0c2641c060b182034284001603e06002603190900070240308186080003145001080c038000d4a0715054140d414212040c0061300000c0541c0070464208032804801222021900c4100704500100300380300b46a156940b05059250300011500fa0603401342c0000c010798402ca90703a42200c8280c440510307040b400902650014006014180b43d103074098640c5107110304440310403220810703180c4214058210004008990805042021140c0d54110400301c3d401c0040e595603400f020b5540c100504500d01a54202590f0b0500c00440d84243c920603040a040c88405101c1003200c4d1a06a01041064400e5502000781a2070030780e00700908024101154014110411113000e4089a4444805014414418140e08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 600875674 1250 600874424 600874429
    0x905070c06050c070210120e0607050706090f05100204050427021e060a051207021b0f0102031b03070201021902010c1106092805010311122d04140c 65
    0x504030a03030380110009201c0d151483c2201c107602450b28029440f000301100852403903030080c54540c0c11000c0c0281803160031030114949131900310485880c03002170401d200038804070740690001031099010f58041d101c5004152221400c10001074104ca05c2d00ea0009420410703818a4804e141074206504014900c511100707521042c0d83d046041c0c040e20641d51401180c012080c413501400044100504083d6212107030304014101e44c0000e40c00c82480c90046000442c114000b2400350b8040c0308460311603000703040c038034100510000d4111581703045200512a181e4610446640030790071424280c0110313240c101d58400241b400c11215800680c541c40e1080e03e60043c2d07000300841d00c041c1e500c40245282800540d0115141c0d0090f04c3d142a03108241d4150b920450740030305107508121040020150015403185e0041d01940c0c1291801c1c4003446040180c10b2138419000404e1b030b0440d842c13109803905150414078400f81e02008000b04000c0500320030902040088640c0c0d90700503141040c010702043c0c0c00f803000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 600876924 1250 600875674 600875687
    0x203060f030303011a07080d050a0b0f0f090c0a09050a080c04180308061509041407200a080d09081c0605012c030f0a0302011a061903090206070204020705031201090507 74
    0x30569000e072010840d01b00b04044102920103040c041c03030040003185009582c180240128490306030040d10a079066080500340040020507041002d4492985070301e07404014400b44d03010905c01002c000042c44e010802d5501d07010207000a00380c0300014502460110b04000c119810900800d6402d60321000e0074000036005140b45500800413200744d040c031402c08400c0016482600c0b5010780c030038504050454155046540c0e1801183c0d142e8900da0241303180880000120b6100e100f134074082e0700090f902000203005900500c010031012801003074400c1d265403180e80c0b1390000861320f0001000d0381280480e0f03e0340d03842584000c207400d00c2d2158040a458281d456000030f800387c000c00780a02c3c20314440c0d4640b010040d0f00003200c085001c540d0071031300d01d0034000d0081c101e5075100f400301443c64a04070002d18101003500e060549900507914448440b02080d40100980001260410000e010100150341c6510103850218081c401460ba580181501c0d25010081600224019850b00052000341c650010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 600878174 1250 600876924 600876959
    0x6120f190203031227061302090912121902090d0209070c08130302010e040b0306010501080709030f0308061f0207150c050a062304030f080a1e0203060f03030301 71
    0x440e0840850740042400c0d0b01c110709403046814415003d11000f61100d10031030b890041004980c0007000b502c103c019031194401e4500d03000c0100c0da81c40070001352401c4000325812080103c00c0b40c0034034481a0a0030402c4d0000000503d8820f40c000400c9015900701000031441e41b03170720404610349142000000d41c071040d818006030050451000042e07543d03003d1900c1124183e0031048990b00d80041d160304503880c5150b408201d00240801c4a03030902130509015a0718007803002000362400f60700b044d0044400c103000504410411442060000c0800c940c03100f4442000e000e691003421900d020010b12548961f003040d108541d20040c181c0309012a404038620b401e446400702c40e54012100c10004a4869a081002030028003900b8000410001c00d07a0101d200e08000040c100606815030f070b8014800b020413180a000310344094141100c052090200e164010a1442c0c0002d415207103145086003201042140d81e200d40e400003c1c86220320740091101d100c15401c5008600d0341d0b0404010242c1c03484001d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 600879424 1250 600878174 600878203
    0x50f27011107020a0801110d1a0a0f090605040203010e0f071e03090209150a030602161a010501080714070204111c05010311030706020c090402010201110d0203010905060a1d09010e0706020606120f 86
    0x3480ca0302c00326061030402c0484410001c112490b456100c5e01542d0704bd0740b141c4541e904507440c144000417030b81058001e0300d04840c0e1100d810006640ea0382d01c01c0418840040103041000300144c40001805001148820f0303007051a40c00141424a9105104c000c0745d000e00340004200420740380c447c1554458002d0300c10341b94049000340c0c8600301ca907079402046100d080001c000c6006e4054640310b10301094211070407034009030703181c16032070319494002d949128114250f011a808108608405402c1c45d811002c654026003655601e8980303100080048024000c030500b204c0c540750f40c01001880712000c1d000c00d800004070050304c2414074102000e03669481c805c1e000c90241d106a0002400d41e8004c0d44801e208803c0030042039510b039211400341d0000c2d403090051440349440c01c000300f0002d042c68030000050b84d0340c6141e840c0d0880f000d18811080304800030000c00e03203592030340e0314000390103014400d80c0c0050803180c00030001d501b8407208204104043c450164001c1d030013500c03041d0340d250000400c060400f114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 600880674 1250 600879424 600879431
    0x9011704030525020915041b03090507060810120f080706020702100e10031508010e0f161406070c0906080a03171012030302070803010e0712050f27011107020a0801110d 74
    0x10808207028240440080c80c10420303c0e00b608c0c000343e070950031002c5494480d0003910841922078005660f00207041d2800d45201d0050201403101d0307110501e241c13000e00c2c02000072050b268240d540d03c0966a000c518111919034002c5580802c41c103090050b600341102905003103018074000404205a403000500940070142c0b64401d03143d0604a104001d802b400c044002884991380030800301ea692807001205200700d11416880e919403d180508140c1030342c1c8030383e11a00d02f6008000c10015940c0000c1015141098800000680c03004141f040c03100615500c406025044000c0c10050100c4450000c1c0000c50b2001c0c40401041c504a001d1f01010b544501c6000085640c050030103c000f401840e6004221707a8002002161060340c50125a00c180700d01c1c1d480c21004003c0c4c04070001078031000d5a00383da00c204903002142ea802d18000d03104a00420b00030452083c2c0d048070352002d007955160700082ca2300346030004409055003481992000a003090317000030301a1482c240c9035901f191040c9503440b0401542e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 600881924 1250 600880674 600880711
    0x607032f030a020a0306090c05030603120f04092a0e01030b01090b03060904080f121b1c0216150b010e030708070b090d050a03090f141302090117040305250209 70
    0xb0398041e0011f04141d83c0104401d03d2500300140c413540c030a4988921922036560020b0b0300e0500340c007c031044c0102c41030b005807c1c549000d41d0f0070007070b00f604000a02c000c0da1841d00c851030311032102130b01201343e1215a00c21030100342000014085881c002102410406100c00c14450395008170304498019406a54144040d0b07500c2c20300c1c8065014010707407800c2440e03001550141401001d21524020071b81c8a1010140b01d00c0c28100b011180304044030320800760707010b04014202d5070303280c1d0141003a000310540300c2c069000310391344070007618548103460764601d81e442c41c4030030b01540e01201d03180d0703c8541603004000d0a0706007100d25039503110510507641c00c0c0b04001441070385500d542d4480310b40030303a1000494041c110149800b514650341405042a00444500d0000d07000200e0002100c0c0f180001d0a403541064a0209041c0a175002c000340f0340c1800b02071080c1c102507001d08215284660b000c1d5132415110000c3c0030558058120342c0c0c0f0401c02c031031101a17024000d60340d00d800d08c9803c00742d001600d041c0340c0d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 600883174 1250 600881924 600881927
    0x1d0312041701060e0a0c0f0804020916020c060a2f100f092306070815060d060f1e050109051513050307090b09100e040b180607032f030a020a 62
    0x100f50f4100c0c10b840350084003840590074568101003201c08642d1a400d26544110703004483c1c01ca4210f0f0043c1d84503040c030b008240800c880000d030f84224450391060310840c0d80726801003040c81e8000032882d400500b1600350303c41a6850f0705001000300003280031482d918480003011b90303520036101140300b01e0203641b2002c00c03821070003c0d440f6100841d4440700c0540d60748854042042880d035607107000c2e0018040c6400188117030307201d020068440c40040c011401e0001000c000d02000341c100003100c4403c5a911540401c03107818105146000780703425001b004105201c80c81c50351420200354403190611420900507c056990307401d28120780303d90382d8040741d20b44250030b00840e401a4954059505400f982c1d03c00b042a0000e900304008480098485285540b40d0b00602003521043e445840c65003d804c0c0003040000c0c035a00c030b8890308140c0d10001150380c9081c032120b0307e08016082e154038020a42c3d4040c1c2034400c401080d44248040750480500034a4041200e0700d410510000300480e01559000a040b915a07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 600884424 1250 600883174 600883181
    0x3100b0a0905130c023009040f0207230d021005060105070c0b130b040b0f0f070506100e0f07080601110a0b0a060509010b0304052a09071d0312041701 66
    0x5002c024545030f05003802491200051000c0d034013803801800740c04d00501c0c481c0960300c1c0c4d1145010f01c003010342034a038000c0500d01400c0e8114540081d030054466a03811150070441c000351907003d014581004850003046800c5200045d600c41d03000c101e0b04003462100b069034020032004480c04808101007110382e52070740100c80501c2000b00050003920005804280300403802c2c09000c000c0b40140108102903200ca0017043e85005512655044000401c49140c007a600c0c00080d000601403118003a00b0220ba650340c1e01d041c00c000711015012800445010850314451039103458009244c240f10320000c0c109400010004c25008210f40c0c144039003140c110320940e104000a06003e50002e102907110f0900c006090b01400d554807079103104020200c004101c812002040324005c40d03103e00208140b03108102000904400c0d0701401e408002c10043d0724100f611400321440c840c14a690795020104010360103216544011409e141c080c3c1e00c081e952403004000d0008680c16075103910b000800599072610740c940503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 600885674 1250 600884424 600884429
    0xe06090a0201030c120207110405220f0305042606070801060219020a090606200106120605150a0b0a1211040627080a151a060d1b0e0a050603100b0a09 66
    0x1707940c070000d0f0000a1213142008aa40340500f12401d100603213455125070044000350000d100310800190044000818080d031620000d4480e0504a05081c1d403080400755109050030820381101080c03041107441a41481025808005800c0612071541086d400966400100b0038011400c5001a001c00640d90344800620052094078428400c3d1501e8280040c1100740b61442d060030034408142080c07500750180602029581d005114180d0380c43d1a86451000d000d025050840350f41c4012000d440d41e4071480324407005811130325035250b034800842c6001403140c0140411640240d16000c005864034188404403000c40c0c86903d042c10b80c41078030b81042100c90030031002400c54140c842c0030014103c900452600602d41c010f1800603940012080180700340c80142070599254003542540c01d102c1d14090000d40141d4281314000610203183c50380c0318004a60040352000403070060021840300b0715004507140c1c003800090303851303a0850a10030348603030000c9082d00031941e452501080301c1e80950300c00d00c0035400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 600886924 1250 600885674 600885707
    0x1006030b0d151e09050c0d2a061101090803070c050309040510030506011e170109020a0e061c11040207020d17040e061c03050d1508030301090e06090a0201030c 70
    0x50b1100302c000840010060030030540c2c5640d00c5241d2000c0708510038071400e107a05030814043d00600d004102081301441c000352003107641503207007080001c01c5c04581e6030300d02650100e06401d00c4402d0605201034076101c08102600340c2c5a040c800e10000040b600000c0da40c102e186401c045103080c09601c5e205045024012109030024a000b04100d030000864450030102ca000b61b00342d44250762940300e15003100030401540300c49040071083c100840390466241c00b000506002c00000c0031411540001c8188000b50300c000d604884030424040c01d031824203120142d001d00020003505000741079071170850501ea10a4598461980414188255281c201d015900950702c041a0000f038000e21009503c160020300445844814071000035105080c81e201c40ea581c0002001811142402c5035001c0390340d60311010001400503141e04401944086c0300a04a020305200b07800b40d5220341c1000704040849503030340403802c20fa61151051114004000c100c8040b001d4083c600828081380501c1c042d0340611400d4004d00c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 600888174 1250 600886924 600886943
    0x8150301112a060106080a140f060a12020d0f110904060203150a06020c1908010e0f010b0303040f091a180711060106050f0309070b07080307030b091006030b0d 70
    0x2580750503864000c24009051140c0214031182c1021048081004904041210750040b030061050901840c03d29174840c5082d107010a0341c20b01488805411700d0180ea40400d4a69200d0034000c0c24582200c4120150032481107001584150350006142014802d02c007500c60040214004240041c10a0011a01d03070060b000900c5814107142580c000e40c02100c000601c00760b084800e00c000e20302681071804980c10340e80207190a103150f10400848003400309400300512840500015050000c0c0a840b528040e8070b806400c128040d00c03581404d5a100902c860300c81d0300304110501183e46000003400644c0e050220001d14102e603010302c503d114043e4403549500c9801601400300d401101502d840c4100082d40d1340000014100038501d42e285000c1c02102c010400c2400810494002c5070040c6601ca81204210361026030350341106d6419500c402d10948810070004204000150940900e03402928242c82e1403104d890041070030248207020740030705400c042d141d0300520074075512801100101c035042070840c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 600889424 1250 600888174 600888191
    0xe01180501050f12070c060608030403020a090209030a290c03060108010b07050a1e060f2c19060c140f0711031e07050f010507020a30060c12090f020108150301 70
    0x1d041c206d070030703c421503c41e420864045291280402030300e00f2207070b0142c1070316115410160b4960207900312081281d01481680a044080b030b0786400e980000d041455540d4148801c1c0550300f0b100320200400c2d011300e0020030018041c00d6680405120704490000d82a1a200d036800e00d030081c14140e05e142d01801102c0c592104006010391402c0d9540d42038400e2004121181c0b0620a00c01500c00e40d43c41000000c4d038150201150300d00c03890400756020a81d5080d0ba031545080c00c4c0624014155000075290155a041d8504845130006010034510f40414115418002d090801450b01e101c0c4100042070105842d00703150507a182045941480b02c050242c40c8203031401c250701a65940003a2184a02c81c0a280c130200d5101e5006004075100d00750098484142241441c4400c0c03d918000d90010f180401d6035501c04410b40c04021b81c032081c60f40f04110110b2503020643e0b00902170719050207007451591500042c40300094000c00c1d10021540e0a080c00209607486855500c40303c5079082d40684c041d420702500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 600890674 1250 600889424 600889427
    0x2f06040f02211e0105090c12070504050108060f01050a0b07020423090c1c110d050a02120a050c09090a060c020319020106031502090603150f1c02010e01180501050f1207 74
    0x340301c1d010311803e0880790b90042c100c68a40c01d03a102541c8003c419001050260050308019190114004070340049900180e03544002c14101d8000b68095041901b10400340100f816412005078010101214041c00b250704180c1024454411224001d2080c0e036140079191104402102d00c0445070340c0303940e244e02a4a82103d1a60311103404e00e000b1032143d0300740030500c0003c0500d400c0d40300009400103241e00704855102c00340b001c0003030028002d5525100b0580900010b0781c8004080d4415402c54024012280305881c18502c0c08449402c1a44a40246800c00c80c201100244400985401043c0401c941c610900b0aa00318401c02e5110f0381e601b4404142180459015004001183d2254440f080480b501220000880c00342440c89c07039101d0030030070101e2400c41d400701d40d611203d03400400d119084c171003100010780401c1218080c07007500340d82115200705660b001500d041040b082801c0c00d109401d1110318029502e12036000d1141800320200b149444c400d00e11054030400d51000d02c4500060034184e10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 600891924 1250 600890674 600890683
    0x32b0c050c0607020714011d0306010f030b06010503010303140304140f03120a02030c070210140706090210080403390503090a0f0806010924062f06040f0221 69
    0x40c1800070344200d8020441092000415404541c10900c4884045005c900111800c840c1c12000d00018000c0c3c400d00d8006650600c851030080c000c00610304d280710b05d149020f4042d03c50003444a03040c821b01b4001000880d03007002c0c01c400c14000665080b0785e00c6c0d0342c074540700310704e43d45841c1d20381903c1c400d03620b00350010b140c00001080340c0e00c091a42642290b4034014200c0c11b1b48000c0317503a40d890000a005413001410108108804d03910709040c0444c030440354404c101140c1d0008601a9500c1e43c86003145004c1d0f0038400704100f0520b25628040382e039481d0645014200400070807101c541102000103d040b000d18000b203045e1070740b140c080780004085032401c0c17055590308010788641c400e8200300c00010f001c900c0c040c90710703084442d0000980381d26881d01444800030300240101014200105411601005404032014080e01490700d0740e20401d800302e10103408004640c02038402d07950701c50340d03046907104001911680c40340c1e01803104030703c800051011030440c18665040c1e5901d800c40c074420240c80040410b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 600893174 1250 600891924 600891937
    0xd080c1e070905160c080f0a030c03060b12010e0612030d02040f0b041a0d06050d050d030f02071106220f0503120327030f12010504061502032b0c05 65
    0x800711804240c03240c40750b8048510a589080d54400d44510304d5500302e0050b00c08803a418092507005041440a610b039440300d03803002e809400080d680300d14034001f458062040c00301608052844a00b03009090301911894070042c014071182010340d5000170300a56071384401d007170358205840030341c0d468440c8080540043c1d0083e00454100e5004020080340c0d0041c80c1066500f1244004c0143c842c0491284150260f41e0160b9040344001d80c40b0400400c458440c250040b0502e8410340c010410f00f00e203418014200d59484c240c0c03003a054010428880498400c0c41400700c210320031250b16a581074602c0044e42c40128101c00040d5400c3c0c0010f002031414a00182c0c0000c071142a000c1d6038080c108a8000207807440110369941500c0f105c801d09011200c0182c065051030381040084a08d0300c146013807803e580340c0180e8041181c1e88602401400340d8201401250010000040d60a0306030180c2d80f0040c3d10390040c130072041180c10701c1c008195518100c11401d1250306118003001c21980c0900c100040840d403104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 600894424 1250 600893174 600893233
    0x82e120809031c05121509040f030e120705060d1401080607031109060304110d061a0a08160b0a03061809020102150105030607050c071e05011d010203090d080c 70
    0x19003042c00c54504503040ca00c0403a4031503589030329100b003042101e00c0300c9071701400f481d51545210040c1c40113503d500c001e5500070340c0148420b001481c2e40d407400400343d09401c1e1200b030069480e003506800c00780300001e103601074030f900301c0e0345a4541c41d4007000301c401041c0903403902924180c0d003c0009101c20000caa00d27402048030b55804d00820f425020041801e100712103082c6d0300b00c0300820000300815664441e490402100030250b000035221501c1c3c0314140c43e01e2419149550120045a92062404a031044000c0c510f14015100111020301e207102c0e00c070001d1050001d01c0744000f402d1284144640d1018014012040e00414802d4100c1390160041c81d0000049003d0f10403d5403070249210400c444c4e5040341c6c4010010310455507010021075540c2c001041c40070291081103004503c1c2c50075a030741c05082c03420310610081090b01d00320004140c0c2580244800c86081042004052644e001c0300b00c4d41e00340d00079074600742140001d26000d0040c0c481d490030080300d8051011009520310722040310482a5981 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 600895674 1250 600894424 600894433
    0xf06072406051c020a0311040905010e0f1908070618051b15031005011101020c0615100801030506010e0709150206041b0e060904030e0d030c050d082e12080903 70
    0x80218019a400301d020f00a9480307020024104000766041c10b0036a02448003402c0820340b081c242d40c4842c01c1d1a4405007241264003c00418501e1020402c0000c0586001040c000700581141d151080716100740b000150a5035200c1030040748920055840c0412145e010003142e606100e0120a104c0381c849000985100c0d1040104102c0c02d4051501078a001c0c80c0d1f03120421203011700d020015248281040003400c61950240303d005403070b00040c024584105480031603082860710f0402085500c000f0044508148040c01e0011300110347c00180185c1924142c0150743c8003610f482c1d0b0151070402030b0754440303400e00c1d44070704400f000c01d540400c8450107188140f0540e50003400d1040001c41d40074083c09540302140351080001c2d810b25010007180c1c0c0040c0203040c50300702042003a0115400c0c01c60302e4410780c085841d03084001d081160400489422225924040d1180e003080183e0400054680e0201c0c0364104000350a42e0003010b0840b1204003c0c042000380720349140d0f5928144c0700ca0340100d03034400d01c640203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 600896924 1250 600895674 600895699
    0x9071e060e0d030f0819020409020d1812110705090103150501051c02040f090203010e0304030b1f05100207091a03070512070b07052d0c0a03020f0607240605 69
    0x184002d203103001562589940001d503d1480c4216862080144401c0fa00000620700c46000388843c8000e1000e0700c0460005a03072a80040003020175078442e9101c281c140800b81d00c241c2e003c0349101c6040090311a0920703000d03220400b582032484c502150380e0081940b0102d024000030030010170441078440302c500c03a0001d100684e031342e00420864860442c6a0a1003c030722070340d080f00516241d840000011419070300000e801442da00483e0841e030650380707030348200c0e4000503042c1705116078104480c1d40301320720508045240c4e0111055180c0120107101e194004e201e116244c1031298002d2161340007134030a0308810061442030301c03205c1559400302d21049001c0e005040e4046031501b0a18885107110b290305005044051034520305a01591200006480a02400701d0400380155002c1a640080a00c5142043d01d074a0b1000034905181c95540e0070780c82410300200420042c1c994246804d0f0440c0c00716a01e81c1c41d02e5180c2441040680d05003503041c007000c1c00145200031510643d00090540c3d00a50b0150203240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 600898174 1250 600896924 600896929
    0xb360a27150321051918030308040b010f080a060c05090405090c100302031519080d020a110d03081504060e0f01060f02030f030a0b01090b0706142d09071e060e 70
    0x1003007500f140300003181000b48201da804824540c030700d20b20880c075008890411851061745140296081200050459414801400220b4900e18007500100207608083d6281410440e900c100da410020300c21510b41c000c110203c0c1c041d4043d10740318039014200307004600d881e2018644880c0c500c46480d104802110701078482038400d1003034034462800b810b4075101c0c201e01c50702004801d030f41c104440c01b84011a194040b4403d03506100d191140f504540040c0702ca9202e51038903840c5d41e01c1b007280880c015580340c11110007003a030180c4080d400114401d03454000003d0a408180540070704d4200c6c802504000c002c1c8a2000704000080f4100c070501c3e52130103001140c000080340c691041c0014041e0b030744da0074000300d0503500c01c0e40d0003d05941014140850b0352039949004c414039800c1400c007038824076a40d8001044803a1100c444d02e50000e40c44281d08120740582082e404103810950b0761a000210010010b02c10442c10884400078254480c0c01070141c0182149481d0100d42e07900601002404244a01c00c550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 600899280 1106 600898174 600898223
    0x21f080c070203210f13180c170a02130f17190305030606040f091e0e190602120f2d04030c06060b360a271503 49
    0x124905400301d40f040d20041c2e04021f40e00c1c01c000700880f8507940001e4884090388400e440700c0711521842c120034028041e074000c01c1000c46505101107000f00c00c0104000c2201ca030ac00d10701e0303003406a4011040d16403c07040024030101e000303031041c02c0c00a0b0080c006135a000d00702400090400781c4c1e880f0100440d0155910020845680751041d81444120005807444c40031840014404030942c0610507030b4038061894213155107944001900704101c016011035004140c0c195040d0114107104a107400016800d50380c2d8501c000c80b183d202c0c40c0308a2490007000010304401c6800500340d80d0b50300c1c140e441e0305114908948041c2c0d10311010901c501c8a002501404000007080c00998144801c18010703450a6501da03602140c151450b620607a0b40c1c17800d083c0645100700401d0078880c031021041c0461542400c942140d090500c4c0c00c1c3c10383c160420305840216805203010a07042c41a0140c8040c12 = true := by decide +kernel

theorem cover : BRFrame.Cov 600719424 600899280 := by
  have h0 := BRFrame.cov_init 600719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 600719424 ≤ n) (h2 : n < 600899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
