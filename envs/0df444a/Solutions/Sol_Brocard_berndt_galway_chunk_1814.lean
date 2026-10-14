-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1814
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:46:25.267976+00:00
-- url     : https://prove2.me/submissions/a6814925-b77b-4c8b-85a2-5ebd10218c9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 326079136 ≤ n < 326258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 326080386 1250 326079136 326079157
    0x9010905011119140a081c02070308060405071403090102041a03042301060803120f0a2d0b030f070303021515040504060b040915060b0f070209040c1a040e070203 71
    0x481031a10040c0c01030031903007101e8491500d204c002418845401d080031101c04085986480108144085407070b420300c8090441d2100710114200b1007240c400a00c891009051140955130340c0c3d000c1075a040c8500d1680620b01408840180d481c200248428002d520610403101422102c00540d90442d5012044034006c5403c822603011040280b078080e551003241d41642c00f0235644e07999000411420070f2018000002982a236590280781034814446460001841c90102d240f500003040c1d40d800d801000e00d070001c440131182005000c0d06042910050080c10202d0350b140c492888050004040001d0240690f8032a0307007942d07150280d2207041a4807d5055170310b101404c041d2201c0f090396051640c081c80e4454092400800c00004100c0890100c504451042d81c6481ca440350043c403803052405000c00078078001883c1ca1070000c110721545058082c50200a109115000128043c8611501104003a04410350000444660f00c515200c5552291248104041c21640000d06050000c0103844e8010007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 326081636 1250 326080386 326080393
    0x1f0f060510050309070e04120e0d150b03010b130204060215070f0c38090316060504020604030203060c0903010b0f090f0405030d0c1805031f0e100c05090109050111 72
    0x410007041c0d44a40004000005600c52414005081e04400d0611405240107400c5001043d0340020021714200205d185680a6009001990001580011a28841c0c0b07500400024018449070000340540250032040d41d1014a01c11400e4494410340d0003041114116000c450b0240f504030348803040203000b1511400490749200f051000d450080107816403040c4119000150060304410b0980000403003604003821180f09645481c264034810303c203d030010040002981844000780c4200a00d203141e000c0100707425212400f0030304540b1500d0030b5401031640201598817034138000001503025084405d01d0b5100e982451500344c81800c0803e0441c0701030001508a003800c1d40d070385005000c448000b0f04121440e200030440022164210b00c0382000030502c90b80e50120b80c04040c020f4a5a011585e04140d1203500000400c61100300c07040b04201e01d000484030f02181c60344082c9000d50030700b94009081c0b1400c0c0e08003035010025540c0700c001816040000d0301c942c000c03039880d8001124408004c0c3c04980480d0b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 326082886 1250 326081636 326081659
    0x7022e0b0a0e180a0206030f04060606050910110708010606050d0605090c1207020f010c0903030e041104060f17041104050f01051e03010e1c0207090c0f0507141f0f0605 74
    0x3d001001030340d0b00c200c511048906181c85035000c01c88980c02161a4a000c1d410302c000c2c0010059036010b4030780205003604d451810001034500158181401410070401c0c4007040040c1200d0440c144605d80003401d402c0003c008a650b1542d000d00b5580c00001c84c0120907240c080040f0f42e45c80d12440c1c050207088100c45890500d440e0320700c40054110f01621320301c00d40c89502a01074a04002b40075002200b0955518a50914a9490051700103090390007a07900c16070608141c0c0030841850019201210b00d01d20740202c00400e246020707240c400401003400880a01041008103201c4031511050558005407001c2106580c0c001030030000c00750038040c00d540840031480d0303500d002603030080c0e0222003034008000066144580e185a0325140c0b01407809807240814200310755455030140b0020b401401802414801c140049500820016954101006101340030840c0014040d08841101c3c0e81074403082200c030764662600380c036824000c004050b88412410508500102850340c0100c504548000d000b40d400ca5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 326084136 1250 326082886 326082901
    0x50706030b01120603061d060c0307140f0307090f0902120106050d06090e0d031b08070f170a0f0606030204121e0b130c06030614040507022e0b0a0e 65
    0x10106640002e04000c0d201d6400300e03801180d8443c00c2c004601c1a0b6000030005090514401c400c90041d030f80222039003001e410420440700c040d0469500281c0c074a0035009035041c030032a40480d07000d041005441042c011041141c50f582022081040d20741c42d0301c4401c80280d0303418000041c1e100707110078032440c0c00203d80100040b6000b10064190f1494a84000c9003e544034180e2808580c0d00c1c3c410201142d01800119120a405105142614910341034480d01d0130540d04014000000251031101004240d446000059100d8200c1d501c22100100c80c90000c2d040425001020741001c1d4508202c1c1442c1440020342c03d40244200c800315180c1280e4804500001d80341e00c0d03a0702d442c1c0890342448031440c2c809040000c00a0040c2ca00c903107215022400141881e0804400920b583d800190505152040134800e04c0d020118192a218007110f0109181d501e1080480c04e04c07540140c0c0c050289514a82201c94000c0400700c41d8800c242d600b0100200d00002041000340002841038044040c011400b15012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 326085386 1250 326084136 326084141
    0x606041a061c0b1005040302100e1f03110301030605100e01060f050f070204060f0e0c070b0114030109140c15280c0b07031a0906030c0f0a030209070f1b05070603 71
    0x440300401c000042c500940f4000c5000b075030b001078402c000508005018003c40c42c24884490042d071442c5082d500f600500c0d40071564000064031a004070808000800047c0c80c800c0e040340c100031420303070201da0b02d95030740e8607007a1301800c420b030703206101062249000704c1c1d4a4801610035040ba095942d82800f924164202035074581c5c8601c034004003040042140c1409038a4900031140280341000c40410941e107801c02141c1070400140c01c149000508000c0f103c0410200742d00181910310314041c203150fa03551040068010071416400500c6400440103126aa000c0032521102008050b038003c403602150003c102d0b42c13072168082c5049110501e124008030760400400c0704101c200d0b541005e04000303130b143d241c2c3c8400c01c2084900e900002e45030040c040001000c000e11509001c82540d00510900308000041d403035050f0828218040e100614044020b680d540340360740b00442c1c001c0c10030403c60605031001010b16118403d004082250320b0f000d007001161031064016403a401c0000340c140b0300c0c20917104501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 326086636 1250 326085386 326085427
    0xb01020604030f1d0406080601180c2a050105161206031e020303040305030f04031401050709031b031709180f0609100504020a030b0405090309060304111c03020606041a06 75
    0x40e040a51301d20002075881d288205006440040014080f03580f400c04400312a90062420000460030303e104881802c0c6c0102140006a401080d0030301c00380c101a501c0c03070042c0e0298801610660a01007484050903481017040c0200c03000c1d40ea1075480c3c0348041403620070b40340d49100060000782d04250445140d100e6480c404061071006058900c0d140e0b50f51100c0d840d5800c003e0b8041728441c40040d0800401ca078065480c02d00e018140001d21a40c0341c00000602150414400a80380c0741e0000c540e40c001030280d022400203140e00c081106020650720200c2c4002c0d03000500c10500404403480c1e210141c030b590304941751241c800b250321075003650b8445040c0080110043c001c5800302076034030780c00308403551140041e04e4001030503500060424490b10070030003a0342e4060302030005900f04210840c603a80f9580200c96005030080210456900b5407404180082c1440b45080783c407444100b0300004041e800700fa064000c4d00e04490a02c20705a001100064110946000030782c0041c2c1000b03043d107142c000466450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 326087886 1250 326086636 326086667
    0x207060b0d060605100915030e01021c1d0c100c020409060e03090301110315150d050c12070201061203121512061a061c020418020301030302010b01020604030f 70
    0x45058108000c9810304405070001c450039512680b007400036041501034070210441d14a480042c0781d10b032421020800c0744840042d0300301138444c0281a1082c00c00d404450301c0c6451141005100d1a403203c11100a03c484521240c05003940820440b03031400c002090002650000c1c039226514407241020ba81d160204841240c00070744a00380c030720202c0c9851155404601031034001c0c43e42d607078030700782010700f15807040301d601080c10400e0083c020900c440400003c44000d080c3d5001101c950780b9145206107000b0030072521441410b010400580302e2030350b4041c00c482444048100e40f65240d010090f801d8518034010684814541100030703020070701c038180b018001713101900300141c03000382d0f00c809980e259003e41042c0030100c1c03815035000400c40c4a1080085814840350010002206240040d00a118250111081c0c1c07800b000c00c0031030071800c0c1e41140d00802036090840514044264414060b400921003034025510303141c0e455886500124000d403251380d0590700e016060307800354000d640800c0c1d0313050780d80c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 326089136 1250 326087886 326087891
    0x5060c030a201f1b02060c0c01420303020c0105030408130603020306030c090609010e040302120309070f090507122d020c0f030406050415050706090b01090b04060803040306020706 79
    0x1c1004070414031001d05044161180c400f40301120759200c209840a148401c1072400c103a02000b8a0786070702148954200350001c0314159102d00c41c46140e40501200d80d5850041003000b006034400448003040004403035150000744021b1700103409005042030151101501523000040301103201d40c4660b00643e40a8407441ca0075040415580400000780803a070042c0700440d03400002d00016103010492000c5144044032908a00e182c00d001080200704103100c0c0041503800e00c00801c1c2003500034803504654200445150362249881c001486d521f041c24440c0303110086900c03001280c1c0c550f10703000d03480c412042c50319400c0f001c5642104c100010030840c50100040e0302800c0450201d20031100180c3c0c02d84408a0700541c80d140c4031601a070402a2111940500b94400c20041081741d40140607102101ea2820000c11a8007000c54190740c00d10030004000c0c130aa18280c0e106040191803544203041c0e4612480411150b14140140000c035141c901030541d103a8030522003000068000d030010801e440c0700380f401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 326090386 1250 326089136 326089187
    0x30a0b01090909050d180f17071a0306150306010c020f010203160b01050a05010c0b1515160c0f080318031509030403170906220f090608010605060c030a 67
    0x70500721820583c08454540204036400589a8884c0707100f100301d040950886080ca240004500d52244144210742d01120001040011040140151401418030003d05500414480c402402c10f0f48210f504034860980c480310340380d440359a401540d02c5001e041e124400012800d808210210244152450451204001c502400802c42d01d0204805118001c48011541000200300600c820303070b0009410415070460410100d0040c110031034000000841020440c83d000c80462103000031030350203803100c24000039141c0040d02c25503040035060f4050104015140d0715810f004032100410310506c0896401404400000540324845020860006040712480c10400801c007160803c03c40c1c603076407544c0020030100706100c01c11913101c05080b1100e0f0058508000000098058050054017690b200c2d41e0942c03105901c00388003c42800b41c1040d84810701171035651513006000c0d0440380520722503542001030018039030030000251520540044040c1d803d02e051000211420f00b00d110488203000901d001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 326091636 1250 326090386 326090399
    0x509040507090c050a030b030105040f03050715090f030f02072402011b05130603050403050f03090c030f280b0c090d0813091103040f02060a03090c08010b031203070203030a0b0109 79
    0x1a2100342032662541511130745051741c00b40449444844031402641040c00b000001201550307001c0310300754141440d07070300d80099045c0040c207094900840194280b920804100b4480d10403018684148a0f41d1b0f2805e140c1c00e1000120785900043c820544c034030541661483c1042600490001c0580740c1c1c3c40001523001340c2da810804200181c002000c04642c0018040c4a050a66014000541417504040c001c40c203007980c00820b1442038000b0343e0300c24603000c404160030318418041402105401400c40c0c0010b40704e00f00e025141d001c804521075007403c8080501c041c0140e181911124207822140040140da155103004d003855000040b8103a20909803030b0404001041540588070366040050940066814030303503c60200c1c1c0407158450b203032040070300c01c010000d101c80c1c10900e0f409034142c401e107032600382c01031040d4050000600002c1403074181c540040354242056101c41c0d40c50800710115030398140c1c84103841c0c0b414070045d6051f40058104100180707020241e0b41104004140c10315200ca0015507441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 326092886 1250 326091636 326091641
    0x5010f03050d0f05041509030221010f09030507020d050a050a080a1b050a15110412050d170f06010c060203040503030f0a020f2d0c0d020f03070b01050904050709 71
    0x2001144102105041442480400c001014000d51203040000000a40c84000340c1a8095881032000b82100c250b400c0820130300c500704c80d500941d0302030442d0402403880341d85140b03550001c60300c2d03601c10340c41d201c1d4405041005020b603c0c060350301a29074034a0f1103205c0d0280840d41107000d80a49036403103081c146500140b010025201452700030013405484d1600e00c0c400420707443c1302c040c058200341c40300c1c8041c1001c28808120038070842d510102004c10075030765213500c0002d00001d014604070030340c0c0420300141c0301d000a0417160b02d081c442c209807040165584800d6030011503841c04201600b981d04001071040e081c2140841e08030f07a050408081c11015556550b080e40c2c01150100da03503410200c107010743c80c03654005450b0001840c0d6410360601d85041d481c0d403454050131003072041403024044d00e060011185545d0400503803800f001c0d00e5a0341a03646400b951903040411140061042c40b511503c011000b105581d001c951003250351885928000c00c000300460050400d9035140111000003480329060b2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 326094136 1250 326092886 326092889
    0x1120b040f1415060a0e340203130803030708010b0309010908030408071202060f0a2f070b0a05040807020d060b030607090f06020f1005190509072c010b0903030d0501 73
    0x2680100080c20b500c1400038841000648010300400c841c0b0003c2c4aa5000d00e108603030b00030f001c503e041840d800143d401e0f06094000203140207e48001c14243d8401c2580400141004020414030701340700d07a555201113549100480740b020005030000014480b11540500950f08607410034000704030386215440300360159000b03030380455560100190079030070000c8c0c907172070101c1289845c00540701ca4505010f01804802c4010b0142245a64800c0004031014900810310400b925080ba5102074881c801d808022135486000c090301e002d080c3d0000200c9012140c090a4031943d80b0603034040c00c200080d400c3c0502140200d41c100d4181ea101d50305d03018075880c02c014480c81652a565801485481d0002000300b1000b16005101103401a00450100c0c0030006151810b0f1070030003c0000c2e1a6a43d203103455255202c00e5402c401803070400d000d00007442d02c002004020b60b046a00198028600c4070a60849407100f1880481340c424400010803040451102808100e0703009002c0e00d2900542d0642d1600f00d80d404d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 326095386 1250 326094136 326094173
    0x216060c030504020f0603090a11010c0b0c070506222603131e02012003160308150d02180612010903020703122d121103071701120b040f 60
    0x55404110a504c0c285c145205120800e581e40d1349107040c042002c94880790300032400f400c918490248903141c0e902c103522544078990000012240d43c02c05a080800b183d01c004402c2d43c480c491100865004d800021480300c40d01c080302401e01c02e2542d281e03030300c481841c0c80e1410407001440c01c031051014001854025403040d01401c00d40540c034a414034208100c80f275440040c011000b500d6140000607600240130540c450240441d8000c4001d507200803078914413030b6107080c0280f1031403020390408041d0400f03001390003200702c0381403a00000303800c0d01403140e016800d40300a54420f140506043c244081032040039000000502100c115402151250b230a40d20310543c220016030051100f04140b100056071407000c00c6940c50240901c1c2031003c0441029441840b58a0303c0110003400000c0c8107000d5405210500080c500c1800310151540c1c80c5600c80d00115001000700c0e6031355640c001d0032024600c405040e07031050708040d0031113070650712041c244c50300c01001125040c08032516280402c4c003075024500100c0c103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 326096636 1250 326095386 326095391
    0xf020405091302090a11040306050402120a031107150f0509040905030a0e030709090203030301030308180105070c110901080d050703053c1201050f0d1709040e12030a0216060c03 78
    0x80c2c0348140314001e48000c0c48403c0a41c641040b2615203900c40003201c0131207030000c3c070100c1d607a00c0f980001204540159007a44980c40b03004100c03001c244d040030f0000c424146050540398101d40d12006406e0410030084039000090b5503c403064403d60288003c6c010944003c0c0000400512a94a040c610f0703200f04c13100da02254a042e00740410f481c042000101601170030030b00f800100360f1540425900d001c1804001d0901c260b481c00034181041c0c02d0365081550703260400074043c909001402504480c800ca5050ba0303613194a43c25043c4a04141d107903c1d0485210344001c140c800b1000f402101e0303d030002c0d0402c40070040c040141d04840f0300241503881580203503884002d54108812540701018080d48161440000c00340900055048001903407411114140d417004e80c0082d0910004101c01411031004004201c0402509032254060010f825031070b1065504000700d42000c140660344e0710301184450030610b81000058110751003034001c0c018515810f0103540e4402d000366500ca0a40300c3c90040500000e9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 326097886 1250 326096636 326096671
    0x50727090c05090a0302090624070c06080402090103060507110a05010501090e280309050904050a0203191e0f05071202010f0e060313020f04020d0e1b01020706030f02040509 76
    0x150544504160141c00b070910614020f20031011800600c07152101034800c541c0c000000d83c2c1e0342c0311220311191440752550402c12080307150310401601e400600701034030f2a60b506079010490a0080d21250300031034006154450503840c6030b98920281000608041c20080142901a2080010000d0a0f1070502c241e00204080d8104900642210108040420194010341c106400301140601c01c0b00040d040116000114031107040c252070040c0305034401600710b032018040005104c00842c9440c0b40c20300c00c0b0261084140f0082c054402040754040182000c0300c400c0c0f03450003100d00d0380050306000344254611494074a50f85c4400d404d0240941c8045e20070b0420300500c404660f0b0003c07003040b0b4045170341401961482c00a01054181c000100704e0b24082003a00a00f00648d600d02100c803080110051056681d200003510710340203440c104d078040003140304102603445030f4007000c0f2400c4000d44c01039000302080d500c1c00f00c080f07001e00607486041d1178940d4204004200303600c440403103d02c500f200d081484000c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 326099136 1250 326097886 326097899
    0x30c0102070b0a0b0a06090e06150408010f1d070621060305150c0304030807080417030c04090608010c0c021314040305030915010509130303020c011a100e030a06050727 74
    0x12081444c49521422800800f4000640c220000c030f02668103003039400711b403503507524007244414044c0441481c02c413001047c00103162005400003844805004010720484807105144c2201c60b06144505610350050101404124816800b40cbd90f00070f04c41c100154030b00900c014100844107981c205941603006082c20110f0045461134054100300d028100e28614605a02c0c018655000074101e5001c00000c00d01003000c0c0b220740f4020b1104400c100f00150703074130b04107102c40100643c020320031031064504160000610320010710480c4a400240d80300c0182d00d291540c00c2010b400324541d00c0c010455595140800681030712409584918404e13280d0340d5990500d402818a4a5100041d2500c20440d40c80180704c191602c899594208003840803918402e001498180c010703024401c2981c0c0e141d881c10040866491794034440e2520860241c0d40140c401405440031035451030443d2000d0f0701644031900540000b40143d010541c80390b10741c0b401d907004020455410801202940c0e001316018014002170008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 326100386 1250 326099136 326099141
    0x803240609100e09160813020609120a060e030406200604030f1704081c0b010f1101060e0f040311030c030306090a0605061803010b03281b0807060e0105032205030c0102070b0a 77
    0x20000301403070618440c623400a0401d2107101d14180c002c001c04030b02c1069401e07040083e165007550000d8184150446080815600e80042c400c5000140100c4054120f0964090800d07042481c5000a0b0005aa40d91400d4514050b803000c0841048180c88407489000d18407425540143e00c00c0d20b0301a81e0b001141c41c000d0514042c441034481462800700c00100e01ea80009000d502c00301682046000c80d04014640d40c0100251b0303005020f02d20300c860800000c00360001e0414070941c0f1a407150f15000c110f0500c1259070b8000c00c81c030040568410008200342e450034040c40c640c44525050b0220b001da8890f00030540941001030000303004078486580d403510745000e00480882c42e600394010920405180782d444c50410352000341d505c002c0301c1e05502c2000d02c19003072454010802c070144015200c0395609042c560f10340480c80f41e00c00258491084006035841b800840e4003441da400700d9541e0722169131031212104140242c00312a1840208420f488607030007170002d030280b00d00841440c0b5282c50a092950103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 326101636 1250 326100386 326100391
    0x20d0b0604180504171b120301060828091b0503010c1706060c0715030c090501051b0a050627010903020619090b01030803240609100e091608 62
    0x1080e1400c1c04148110342940e241c2d4100c0c14401c650120f007079180c0f41000c0d0305c07510703042c0c03503104150300d00054514646141000d9a105034a280c8100ca11f4294003070704416250000380a22400903141c03802040307500802070300c4052520303410074200107480e983c0c4428004940840c0c60841798008078040d2144c0b84180303400c0140090030241d00a1200c1c81c0704440041c90307a070991036241042e8034a200424510345442c01074170017841881048400c001d85466083c1c62034151924000002414000006502442228100110751040e19940c0c00c20300c45928280200340c4030390042015105281c102d2010981c04c2100900684a080017504400c3c050010075200060950300010035071b041482e9800000d500045455121070001c6461110203400b00c443c00113000103202c0a8884d0349144004003e00103401c000358014400c05c180e03d0f0f121030038001c030b80b10a0003440c1c400980c844414080c0c8002c6080ca40c42446001c48549490802c18104400003a1002c4080d59019850425001055641c680200b80c10343c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 326102886 1250 326101636 326101639
    0x30307060e0d180b0d020c070f080f0307030c02100c0510050a0e2a030703050105072a0b040206032226041206320f1501081b090a030303020d0b 63
    0x103a40402c441c003540e01c1ea1441d00c105901c9090021700c17451000059410341c0d01c4002c2d201d0913206401d6850814141d4450382e400f4960f003900500b20840d0243c0400021100c641c1e41c191501103038031096408000310112407150304010b011280304007a00280c801d11400c800841d0707407480010780d0304180401d00b007219820141c18556900c000303042d80ca45044e80384200702c0001018000c000f0700115030b001c207040c070626a0000f0145e6080a0070b12a5a0381c10030095180c4215000320340048040b41090b4038801d4031030030005409038550701c0115001d41041c2005541c441600051100c0881419030340c0c03d420080308005580c40c0804015501424910354181d44807030000c5000f0300d042074103140041c2c0407100300c1a402015070340d0f02d4580740c40b0021680302c158403511a60050408000d043e5414181c051412240d07643d50350500c400180660300b840b111640441b0040e0341d145103d5980d08000020801140d241c11440042442112100c0d80c9110076600558030a64000d038030b4900391380602d410b8401505205 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 326104136 1250 326102886 326102897
    0x30a0f0b100e15040b12030706050c0901080412020721020901080102030c03180c040c120c0207080a0602130e04051005060105070f02060307030902130902090603010b01050405100e030307060e0d 85
    0x402c500b114030321007150840c46100281000784600c4001070010200542010340040001c3c86050f111040800517100060050405001c1983c40f00c003003c08038030681c0c0031180410706050101d400304412492400d030070a01401140c540300c0c3ca8a854030140f81c440d03180182d80050240e0402c04509280032080d005080c50002035041d4102184c02d4400c1d4080100b0101100c8500524035108107020000700a074508060403c00c980c61441034000d1801c00c0341c4c81138460305801c103039480d1405480084c620b011108040c0181a85480d1a903802010754000305000c0360780c080b036100106003c910b1015440c01580b141c001400040112401d400945600030441d605020301401010b02069410080d040403e40c100c80c02d584c0e0baa5001d40a03401407001d1200a5008041c01104a1017a46507600650526000300d030344050341e036245800c0600b030760010990301d800114188020060341c100b462003000340c884036003008100041c114002c246182c110780c100380c400c1601c40405603820071041c03101050846052806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 326105386 1250 326104136 326104139
    0x30e030d0801050d03021614030c0d02010905040207060608070603050921030c250503180d151107061a150a0f0f1206030803010f06050313020105090d02030a0f0b10 72
    0x41e22012051080034040c41c801c04c080020140300b0b010000b180164100700c1100a91180851555000c003014003602034490b03008032144c14600a04441e4500d9070580d40d455804d0b00341810300010350824402102d41944900022591650500000c00501110b170380008040c584050030a1504a4a006141850421081da66142541d600c201c90384040d003405025030b6003404041c902d03000c046888001e40c1c5122002050347c1080404401802801c2c5610100000e400624041000b690902c0000601c0c002241000c00c441c03050580156011500f0312041900303080c4d883e2600b2040da10204d02a1004102c02031030340b04585400c03601000940845c14a40c0e007000c40b4030202401603407009640109104042c000c1c1d00c10395109824080c041268050241b180556901c1e050240d82c000f130141c41031940c8031610104520f8404c070b090368843d1788001039201c4100340507001528268402043c00e50040c40e500660000740c1c5040024401040c800e00180b161410b1500304541d0003807010f01805420354180d4030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 326106636 1250 326105386 326105413
    0x150b0c03070305031e04051c2a1118061905010e09040c1505130602010509070e0c1b0c01030c08070905090606190807081b2d0d0603030e03 61
    0x3a20300950b03250500780c1d5030f611014030b424409510700d99a40c0c0c208010304208001c0040100b10482c3c80c816030180046d6010200c4000d44c1d0750b05a030b1058054400802c00c40d00d113091815110210000e0150b4062261b07010400042011120030b40ea0404081d156602440058280a1030010100ba000059804407a080c00002030140d816040c2d0a4860114180424140210507034180c006141c1850707031120403500740602034910380000d00c059010003040000000c801c0d0060088900c9959020b001c0d00d0164100280301c900c0350000340c00c441c90280140040d8602c5d20030700103881c1c86501601e0040004840040005041d80d4120710441e041240d41d2081c040760b15041003004054a0707007120081c02035540d69010602c580184805407500d020603000f200070481c0c100030328601801d201c3c0e4a107146a556030401640c0a14180c41500c1022010400c0310510a840c00c00b01d42c085130b0346c075141c6540390051002c2c40c0c074076003101c8013514036150307158000c10070960894005511400300750050040081c4040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 326107886 1250 326106636 326106643
    0x14040501060c030c2d0c080105010b0304020d031403070c0501051311040b0102011b030e070b04030b0c03090f0a080c070e060303040b1b0703060501030b0c0309071406040306020409150b0c 82
    0x850050520a009a04008001034035035408810f8101003d07000814107251175803c540c0324060070131b030390300550f20401043d108810700400b4103944800c540c06185031200d5082c400b18020340102a820408825101504c01d001c0c0b034001c4d8028000fa0f552800c038004607040007800c5035009098043c14015281c9450001040041b071149103070790403500082e24080340c100507405020f51040d214042c02d44031030300c21030054055005c0201b03454200200d480807078440e41e100205110b90701014003020044c400080c0c4001c035010086601c44110025500c00701740e805082d900d00710010030708442e03041c4041407407101207504010a00040140004203480b9003031900211343c8910640c010b50803858000960703d0200c06039010304034100044c02080f140b4090352403c05c68003c1c4800c0c00101c0b11040e5400100c0d00040040c02505d000b4111003020f03240b02885c18000200c1c1c400c1085119802100c280400004180148068001001e0b08000812180802e0040b41d00840d0250015050402e052080031610a03000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 326109136 1250 326107886 326107907
    0xb030c0103020913020f04030b070809061f08060405060a050a2703030605091515030402100c0201020705030a05160807030309120c050904060c0e03010507020c0d0609060212011404050106 82
    0x30308005076950f00540209804507818000c00b02007600009001d1242c811903002042168010307440038001d5107071550101c8040e04d01351401a010390003000841c8124400306180ca81c42860900b80b201081da0740c060706410071030100d40a0300c0e0f40c0c010008010741c0465500507654400c000490403c9800070010030075008130740144080080c92641e070300302001c05001342d00140240500400c10502d518021f400e140c2c41d5802e0182e680d0040361004040500b044030507040c1d81c041c944c01800462550a183c1342240e00d80e0103918140c4c110701c58100001034079102403081110303c6d401030018004c481410301da1240852403641c82060b8503400480c08001103a441302198096030100018440b80d0b1809080c140401e80305900150b078003940d0003050208222881e40815010440350703e8030b030300071840041094204c070f0048442c04007580010070240720511f0200c0d281c03014144038103400a40040300c1d85404080360800109032110064000044c0855201c07124440128081103409001e198184440205960803c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 326110386 1250 326109136 326109139
    0x8160501081e0a2d060603060b0904020a1e020a03020c03150103080c0c1503011809020906010f020a1e0201020613030f08060303070203060f0a0b0402070f0201050f1210090608010b030c 81
    0x82d000b0a640c500c6941210000810740302600c480d5130220740000d040c0e130780d19080c0f004a142c03070000000b548600070700403c405c0700e42c03400e02c040c280301ca0380d030520002e944010804000c02004407504959880e201c40c8a00300865142c0c01005c1d1001c1d64034000e0301e018014180d10340f2907071001c3c0180b41d0304440c840420341525440400d0716215803a100352145044450264154041c0d0490101070b00c0c21a40c401550484464004a00405603440084011540d403000041e410603071107800160294001c8a540340940428070440303000c20f546480d4200042044510352030b50541d05c11410040d51307810804642c11032000051200445015500035104407a401d031030000348040d61001801964060098481c0540c01806039601803604a04401341c0e640101c3d00e8807e541d2a0082d52a100c1c00c0c184250b5121590014401d6403140c000d40064800f80c002840d80200c50204000c0300c500400300204150003540344040e0b0760b0015060200842c00c1d40c0041d085188140e2400c035002041b41d82c00500042c18800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 326111636 1250 326110386 326110441
    0xf0c0509150a020703050f280201020a110607020a030803160f020703171209010609060b09060405040f0219111002070210080604110f0c010e0601052103040e010816050108 75
    0x1100e1a041e1301309107244d803001d4214004d400401000d2030f000304014203c10800c50301d0f100e080740718582c07900401188610288c01a448071440c00300060110a5108000340014589420503401d58006110340e04035030002c440c4c03080c01009200c0c0c02090140c50b032008002605140718000c0040400a5a40c03050348009000220340014901103441000103d4030701c009a860f40510320b107885210907000e4483c5204180610303292807030006404040800b9940010b4008003c42c0c90039140c5400c01019180c42c40045121681c06c020903854034050703824201100d60183c8400e00144a00c100301c508110f22400c101c54000e004000030801039a690030842101d0241d070520aa072a110500030074001d05002d000b14915540c0011040100054203002d803034076014a000034010700d00d84d12840c98850b0710078840d140e0001d406080303110740074000380c25410301300326400100c9081c6a52240741d00340000080c2e0111441d50800200700d002c03400d0504c49000a00780a082002941c10a94041074211845825803c1000d9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 326112886 1250 326111636 326111647
    0x10c031413030507080904020f070f03020c010908070905090102130e16091401031e020414091008331e13031b020d0c03051507080c0301051c0b01090f0c050915 70
    0x281d5a0707050302c0389e042d50040816142c104510b0003200410105900b9005407050140740c180c00e62040c9142c074151070b00940600034103441c08070b40c4805864050405800c0703540911541c480a1fa1010344100185041121032445007009840040d084108205070010818508000d100750051000c1c087c000d0b880a1800280c004515640894048020629406500d00010b00000c08804817820220f02c12011982856039844407550006e00405030f20520015410101141199020a50090a2115100c1c5044181d03408008206040040403aa201144010032104c4003288a2100034543d02030141d821030200c80c03e864501a203110360f041c1c00e80341064030040c4a40304540740c4060701c1e2103042d444050078960545a2800a45403420087e0711081c1c400c2c0240055000d502c42ca401a001c0d949a110081c40e41c0d003842e0a1142c840600c40321194001d034140308000008420b0002d181c002c0071111000039200d400310b0061420384a041c0081810071000780480200c581d24072001101131000c41d00020f5484 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 326114136 1250 326112886 326112889
    0x14090607110315010e240a050d0c0308070b01170f101d010203010902121608220b0702160f0b03060d020f0d05010504030806040903170711010c0314130305070809 71
    0x10460092002000412100000300c000c0035401a50003402201640548211480c81c1405000b10041d4461f6000101100400031401d080302d0728902c039030140f41440500c84c2c50380c0319a08960300080701252203016602c0100116940400d800328003203440381c041c05c0d0303490f8195001a40c1c0c0e401d501503402d48031307035540c40f403142c2030b01603951007156180ca00c00a40d182d42c2d40f001c0100003500030506035608103251000040403044003c02d84150018103807961125900c0c2c1c0001000d00c4c6054480200049905080340000702e616114070360310407517169000784055010807500c45050321007544190251021303903500303004000c07005003038a80c01107094804506460080c00081c03a40541c0c40c1030b00d904400d013002d80c00300b400410b411442c80f690081e281c28240b501d640041c4022202643c00c0500007441040700111441c1001003901c2d0800384514000011080280350307142120306071485800420b40e101c00084200d101080c00a501c48442001001c400c1060344010304144507030b2000400f40300340040c1c1071069 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 326115386 1250 326114136 326114143
    0xa0b0a05040c020307170403240920030c090702101e090f030e0f01050301030303022a0d0201060e060607151e0e010e0705061804060312020d140906071103 68
    0xc0000910601c0602d280c01000794490780060380564a14803403070000102140c0703400845003165844014000d5119500d440586940e14070030f00030840548596080010440b2441d200000d050340c08000c04010710403a003010314100b20340c4003480c01900145c0400496075000701c0c4510006003000e0010401c4c050107540c0b414101d00da0003608464074940300285003400a4640a0f4181c0c074425101c0f04003180c2c5171000c100030500751603d0a40051800c00040c40020b1094000e08000c80e8204024042840f086101e8920f100240d080c1c2c18441d400021001100386d424040d14004000016507103403541014404510340384500400a0000b8100180c1d000044000751702425501040d040107010012141840c00060300b1500341c0e11440d9801c00008000703110011542e0341c2100c4000301441c0c60300110100c403c0e00713088103a004035070003580c0324030000c003040c0c040e032105401c2d09040d8003800c0385c9102c0344030140802d55248404861001c1c18070900b02592141000c40300c0b180d80201050f00340426220021f441d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 326116636 1250 326115386 326115389
    0x50321071e020316030915110d020a11010c020607140c15041412030409050a0207021201140f0a0207050304180501230118080a120f180e04020d02090c0310060f02060a0b0a 75
    0x112952401607105039600c50103620110b0140c1041c9e4000f501c0303480049a555403002c0c405032182400d01281015907000301c112255a42c4050155802e000c1c0c1601d9080c0056202da00b601d0340c4da00f20000c211020307d000d00b12a400ca2008491450900781001840d034180d01001ca00f41d1300500c50300c411054508000c0044e10018640d083c02030101e0b00e401301484010303405c03640d0101e005a401c508044100001030140c203107085500c40400d0920f64074102c2240074408094500032209171700f00039000114100b030004001410407004101140b1046a010300c00300e84050f070080403c0b000d80d0610348841a03d000c07580c64103201c24a040c2407440440244010421400da000311903d2003155900400c00c184004c3c0c4c0b2842e03142603162400c42c18030f80c0000f41d68214041a2251010285010900c0f44400391510160424009003003000c80c148a039010942c1d8680603649054294400b20810008804402181000e0308941c5003020b400807030740070041e544183c090408481d40751114048400d50b100d01003040c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 326117886 1250 326116636 326116649
    0xf070309050d17070f0f0c060b0d031706220504050c0a06210605010c020120060408040e01120f02040c0e1513080106120f050321071e0203160309 64
    0x444031070358910060410503011903541508850f03040000c465034000e00101145503819180c4000306051303800c003203d40856180d400c903102a9155200348107a03e0310303038081d170142d4801e07101c0101200406281c05400b5000400f02c0f84104100502241c0200101c881e2400d030200c2818040340c43c0e100c0f4130307089080c040034507000ea0304010070001c00507100d544200200060b1440720590720f448150b2075000400e440c150b0040b58045030f078611136500194800e074240784214071a1400c3e040356840d640c01c01f03400d1610607030b07003983e41035030100e030502100c80412041401000e02c4401c4003c115426920340c0100182c040c0e001c0e208558a48070346045c075001d031620203218400188030400501e801d41c030b18041500841e1640242817400f00c004161700005109450948911846401d402240703562820b104030069a800c440b40e001c2031007450700041c2007140d19100500b42c1c0307035085a01c1c0b41249005101711b0164084190062250140040c2c003500030049408032105ca1480050b400410308064401c00116030211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 326119136 1250 326117886 326117893
    0x30e0d03121e0b0406061409060d0204060207030302150603060f0c09030105071d010e150c0f061311090f01140a18020403030306060801060807081803120405010501050a0e0f07030905 80
    0x4148440300c00078000300490700002004841c40710f6040c081182e04601640010496242108410380d0000000d00220940240010b00e000591764070070041c0e0304075501020240e4440102401010f405004103021812050540e461034541000080c4c0d40d4040600f0f40342411041c0808111152166402c803248080027500034841810310380801040c101040809510080d942c2403201e80c89e6103e10200480a50300400c041c0c085401c8492030102039010342654906407143c0d80381080320b06424019280300300d1501803d1101d2035a01e050040c00d0300400103240e489036640130100600c42440030b04050645d0480c1c00c1031051b0185038000310307805c40303419080030000da40032000c45400c0700c989400400c10341e8800ea809001d8242e640005583c0b000081c000d11020030840d400045446110780b200c01d0380324030021200807207828031080c01400e40c0e014019030100c0410100030403040c064240196801858260340c000e8080e4034181d00c00c40340c05d02c0500b592000ba083e0501180f62140701e6081501140d4125003135 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 326120386 1250 326119136 326119151
    0x306080f160f080c0f031e1011030105010c1410090b04060e010b0d080a031509021209060c09010305040c030803010b1201060c0f03230c010b010219030e0d0312 70
    0x269441020026001030800406404242e484030710101c041120b0701d0b540200780342e03001102000b4481d21380104d519058031590380702409081c400b4003002003411004002c0d100503061001000295585c215011003080070803c01040540d03400038201c000c1c80e40041881c03480c106099565410300d400b40d0040095a4140329502e8140322400701040d0060344241010040943c6811030a800d80e0120020198401007a80000020882e00d80013400e42c25041d1400007068200c2c6120441c4400321904412112503002c200601900005000701d41c0200041d030051446103003601104030326206d042c01a604050325480490204803604900f840616813003041e05da1a036171500c0504820340c2140e1440107501e0141000010540d010710190b44c442500865140d40143d0603441c01e4505d402528400800c02c07080350368a0759803110b15009001010741c40400856034020031b1000a24012010a11703150403d50b03070321030400103a046008081c01074803c1c0c031034a80000741c604013650403810402c03008800d0743c1449507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 326121636 1250 326120386 326120413
    0x30c12030b040e0a0f140f0105010b0901020f1204060f02010b0d1a0f0f040f02240903010c0203040b04260a0506060103110715020912070801051e0c041401030608 71
    0x440910703001a642040350000200180d0354407100200045c110b0016000340300d0100304460203404419030040b046805900030b10080f2403c58800741e10002000c04081b40720400c946e414131440001ca181c0c0da0090861600700300080e81325104e00d103c7d040511038a1403442034024000e41000e500d00900501ca416104894141300420100c800b40c0c00400c0c440300c1002030a0f001c4c0ca580f10500416034620300c0340c0581d90315566620301e051000f4040c4d030303c131840c5d000c10103001880d00c080400641042d10700941300d840b0328040c1820340f50385c0890300e01590030511003070000520000a507400c0750b01580d0794a43c0c0c040380042030030200d40d444014079130368060103200905201c2d001031454002d0301d003a40c2c02c1003210030b05a01101103000f0301c10300510f00c01a008a002480c5c0003900a0008800e008203040038241800221614100c03182e0f000c0010351751100204101c01e07003201805207a10015000b181010b2508880d45440380c4210701401407403010000c07000003264170a40c4200d019121840460710442807041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 326122886 1250 326121636 326121641
    0xc010609140108010e060c04060f030b04051f051005070204090615030605010602120a17041514010503060610020a060504050a0f1a150303180d02031e24060d030c1203 73
    0x400f07000303608050414480c5100095814402d81c40c00d4000c40c1800d0400604032803040224048804040c0c8940800000b5a941c0c4119400f85c80e109941d40b9015441d1501d00c0304a20990f07018078032030700b08100742e03d150582005c100c0b15803980c110303800140d00906190040040c40780142c50807645003501c41c040304000c0305601c110f040c0c45840d000c803042c00101344070040341441000c040348006a00015001800c1c19070b008225009403198115680b5906c0d0218088111a404100000c00d01d1081c401046182010b002e865007021055172220140102444040e40c0e62400c1d54000703087c01d9440b4002814040305120030030340640c0c48600d081d05451581042102010301c2e5085c0c184240031000070598001150b20fa81e209030ad8080c0113503050513a068640d10201c0313003c500e203070780111440b400c0d000141ea003403001d950211150854560100115842c003803070481150745626018002c004001c010044c2100031030b074454000c03603450364182250f203412100340b80c5010000301000451b0360b0310784200380c068 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 326124136 1250 326122886 326122889
    0x100207120809012a020f030c1f021e0a09030b070503040203011424040b0402040b031017102307110c0a0b0906160c030302070918030e060c0106091401 66
    0x540c0c4005482d102c01ca07840307089920090740d543c191520040c4114403103519150650300700d01c0c5130051364011901103090318115400312000c00c01540201c240d2390854a04620031130800094002d085041c150300421380b40c83c20140d8801c240c0d45040c0490003065891180b44e00340042c0d98818030117421030403e036070003806982081c1e80c203c0c400c0d401d200038000314042d61100b280c0300345940031825801c40107901102c500518200e0843d60015114145500c0300e4866000070801483c2920340141e5a20f051010303118440300741c1d0040b500f25071140601c1541400d00040805072001c6a0b100080c502d03c2c104410400040c80c44050480c00c0054001c2001094106805090b901d00d03200559080d09101010003040418034000c4a840038014044002d0300e062040c054800d62140700d03515000c92003603441e0350b81070030225131046005a0144c0c5060200e081c45d07001d003a001c1e986180d0079004000c0c184d0f4000c2c040c5a10f0405150203064040b41e1401d41840941000b001404210000c1105a80944512010207000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 326125386 1250 326124136 326124173
    0xe13020a080411040e06070f0e0316090c1125030f0c0305100e0601090e0a02090103150c030902180601050412060e06090703030903030503251d060301180e100207 71
    0x40d42400d0a43e41464050704c013400d0801000750250303980b200c3d41910804020366021042218008060840e5101048050a51401394040341c10480ca0b080c010b20980368158004d204025000d121904004000905800c104103070324030392601d01071445032502190301142d10142840d80d0b5280400203000b8544030035030071780c2e0284064680d0791040e101d8072410f4441061000c0c030302e94002c10040040500990020075900c10402c00d5500d60396041d000510001e900ba08103a1b00410600c0c2c40c040e210b00a8411090030741309a013403d01c64402141c0005081c903400d12040b12804001200085050303105d0700803107000c1d01081e03690310751000071802c16400070b01080e024920030384507850120f440e420000640b01c040780c0e03041c0c2e940e009080c15590120b0b0036800260240c00c003000650348600b507a40c02b42a0f040c0c40ba8460b0b03a648201404000108141151484c1d0310a01900703013000180010300580e81d0010000826100110f5103001d05810241b42c01020340305c15010500c0480d2010030800c00d180d100f4074040c0e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 326126636 1250 326125386 326125403
    0x1806150605030105011d030c061306020f06060d08090a091803090915120f0602121909080906160204020703020304050a090e0615010e220c050f0a0e13020a0804 70
    0x4545030305540d544400e0140c540400c800c21550101c01803840d50048030b80e0300180079580541c5280005caa580c7d0056512106420200304051140d25410020001040170705030040450381071100200f40d00703600203540582941c200040401d4142c0b201c80d0310f40c000f0200300c2c2d1300304640030003003200003207222000404400040d02800300007070040c0703140a45403000b07400044250100b80b915820120084e60a0340444881030700780350020101d003003440035100c01301a4540e299035500d40b00e8000211078594260000708545030580d080041801142600c0644805403143e641c0c61103020450745000d549664002d41c13140c0001040c000300359010000c0c00c22108180c4051280546421074a0f0665524100260560303010200244e00760198040704040e00c813042c14202c480d8501140891081034440a981881c0d03e4120481c17031101801e0310a51148190b640307495070170101c40b2040c10100e8447c80070310704200050240c90080ca5690b060403810000d0601d032046543e02c00e17911014140e040e040314107030781000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 326127886 1250 326126636 326126639
    0x10501120f1409010501150e0a0905041b0308070b0609130201030b0f131a0307030506040609030512040c0e06101b2102160609031203111b010b030c0a030b0406020706180615 76
    0x1703005030090b01c0c1101c4010203540d04d42b81005039540c02400000c0054070f042c4042c1900d0b040105642d6100c5010314040d101040d030fa030480d810a11110400903004500a420401c10003200800c00d01024514550910300480c4540070240016000055501c900d607101c2c00c11214010503010075880307402010614045c0e0704182a03107004241d05c0d819103100162840e04200000790008919078065800140301341081410171042d4415110141812101141c040040c03030014040c03071480100480e40140c0032104e01e0511007135080024502001d1510716114401d08060180400480041c00741d10954664541144002c00d0360000b983c0364030740b45840b0704c40d1011040100340e403486040b00e0b80039282c0204945000307410212040b401007200d1380319801403000600240b042d200c40c500118900869100001c40c002840904050a10700c0342c044491060422560030000511501005607215400900041e240d405a007000b03009007200603610749040e21824414001c120055202001d6140304000091046 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 326129136 1250 326127886 326127929
    0x350f10140c0706020d1d0a03080f01080c09040503160b0709050a031703041b0801091a012402010209090709180506031b0604121a0708010501120f1409010501 69
    0x50015280c0c1e4811120400c9108007040302a002062640550354001440055000d03c0300305041c00c15240d11410742044100e0310516900c95552500004054460300d00780d4902a5000d54800050175218042c010f00f200050070b01c00240195501c0c10000c9540c50710105c5607160400951604803542c00c0440e1511034003003041c1c100101a0010390b030340054025004601d04011400030740004204036584000e00c00412510b800c0441070b50010025503002140c0d180ca64681072000c0d502c1900b0404802d500900104001140c100b00e02602000d00e0404d0000b60185100407806807050b651484e40180d159018000d900d0340c044491303000c58059000303400302204407000c1c8005580d0140c44280d41944020109440e80c18081c0d1042100e180003001c085c035182d550210990041c452000658000544402d4848001c0e060035415502401e285001c101560400d400a400b221000030740d4007005a031010003c0440703140d98014504000101d14014080c900504071601070301e03090040c4014004d20400c00e0307041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 326130386 1250 326129136 326129171
    0x314010f0f0e130618240c0e030705060901090308070c230306060f040f0f0c09121a0402060c011406010201150305120315190806010f350f10 62
    0x9031200c1c0c0f0200ea2810080d4403000e0180080030314a800c012851003003d8001442480c02c01441c4c20004c900400e4983c0b400d03044c4003101e03400d207542c2042c842e003040005060781d8080750100641c0e000b120055110045180100c900660702d0304010710140e000901c030380900030f1420200341140c200e581d0003e80700b005110528142e00b41c001b592501036010101140c12481c11481014903440041d00014582d052401c0443c29120301c20300088640740e8404040a420381e20443c078001401a9000c8107003825015074601c016009000c20030708140e2094000b2804561f03c2408840340d8030240c02c005d200d10009517100308000b10040c0c50b220301642c40c2c10241c50b000091500101d0480c0e41000c0034141d520148208200e09500090804800c04039145886105585495031100c020516101e8144014140008545000d0041c0c0100031002100a401c1007003a90b400c0358400080e4903004100c8208040c900c0821074145c00f614812102e00900e0f980e140314200000d5800582030202d0000d0214070134a45610702c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 326131636 1250 326130386 326130391
    0xd05070206091e190302030c030609150415023001060e06030a021b0718051003080a090e070e15030103030507031107050a12062004050f010314010f0f0e 67
    0x4114806010031802da140280011441c0b9045a40e030500580100c0d00155003a0391980d01c0c0401d04510703900500075410300304071405848005800820313030342c01c00d840607564641c0700140019500c0807140005040202200b2a0034640030151400e546030726004417006400607503207801e103407140d12032000700c60312268035081c40e4101c030450b80301c51000f003c06506029407039000a01c42c3d04413a4003004200441144072216000c101c00c0034019280c9141001502407100c51030600c3c4103003a900700350030b000c049080d03561604100d950020040d80d89036010402601d105005034055094920300808000c140c1e81c0144d03061818020403952400d91034004180803060780005c1c0009800608103100c9c00c80043c0c0210400d0310045c022008072180603595400049448800341c0040607a124a0700040c0100083e6001d403206005441041050134480c0c2541c070b20345030146100d202d00c580f0042000c401c5590190740700c84c802c0c1c074124981440039030f15090202c0c5035900b00e00c1002208101a00000303121904900c0107030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 326132886 1250 326131636 326131639
    0x2603040303051c1407050706140c12070c110f0102150702010e010f15050103090804090207030e10020c031510050a09020702030f030301182007030804030801050f0105031609050a090209030d050702 86
    0x29868803180011200713a00450001c594a49d0340b03061645940200085540c8a11450202d00d0b9448480582d01c094508010b007403c001c1c17040070380105000800001860b140103006a580c0609000c003400104d18049040703e00c4242410080184501c595042d000b0b2410481c404009104200c81c184040381210b440c511640b51a240e550002e10182d0300c43d4200402140c000c42d80141000d4644d4240741c120703030141c20202c0c0420328921041407182815040180289000d001400d13400c030082010030386801084603201c102d941c04600085850103840608409440b001d0400346055441e0780610000350b01000080e440713446840c1f4a050910400000c49042c1d45086000d080c08040404940024141486002c01c800040c3d0030400800c04525000d089800d02075614101a41041d0a001d86840d5043c1c01403806110749800700311699030810f003101d812850f0364544407a22541020225098400d5802055000140031320000b88900c2e180c001d001400001c80075500b60b13500e44001660780d0710826070001e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 326134136 1250 326132886 326132921
    0x606070309051212160221060406050a181b0915150e040c0509040e010b15070f020a060c0507050d0f350711060c072603040303051c 58
    0x30b21040c1000b0300c04040b801c0b1194101c03440c041c03124030900c0554100b41c0c0c100840103070341039030002549805c4810a28404201928900f542040100d468a82c1d5006102400a9132980041805600c01da8400511802901140b040c4014140ba00340d40c100c0d400c109480c4d450b5040a0b0209070300000d8030800c0c0180302240c20740c2442510b072003001b4000b251141080c8050204441c03c0610513119409020340c03100a40d034941d0350f40c4515001308400c43d500c5041c000d016030b15101e640c1030951500a008000203ca0000c2c9545550440c940708850714481e003c02500618442400103400f03400c109103010280c85401610710842d25602030112003203480300043d108140750304215002c640c02d40042500100722220b890203016203201c0118400010700840c41001b40c000540e80240414042541c00d9007200303c401b03501d001400d10149565140c1405041031403a003080108443c035159944000d0ac00071060700303603034031103940b414003038016042607071080d80502805007820081c515512550a1141c503031203a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 326135386 1250 326134136 326134139
    0x10506040e060f070302070602040b09122e0b060a020114150f221d0c0312041a0408011107121106010608060303040810060302040b011704020915040912080606070309 73
    0x1404103500003400c004c041c59401c00000c6c000c030742c503070004201a01080440ea0340ea104250300b0703c1490700071a000024190040b08060813810f280301d00710802d910702c1c000070501c0c00e0100034280c402800403c001e55480900043d0381c603d100d03019002250b0000035800074019941ea4140d481c2d800483d2180300c01d51004081c20052514908a0000001440c0d4100518500300c80e01c0003070821910700113595180108440701d84080c841003000403550021090b00034024004510005088502036801a84c0c031921001001d0038408140c85e05440040202d0f60081c014109142100030b1a42d10102060b205842d203001c4480f60117001d44008500c0007109401407186071710701541160070402c090300e0390303034140000c000000300650b0421101029801080001624a1541c4108000c0310828400281030040213039418440b0120400380b59445030301501e40035603503904c90301e0b60010160060740243d44a440c1040e10382c01d0000f5850300060201e020307186c01c4c802c2c2c1c84000030401d050060400040010302c14400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 326136636 1250 326135386 326135401
    0xd050d18020d030806040c0203090915030c06070b06090a0203011503090c1e0806070c0c03110117040503030a060801020313021903140d031112010603020a0908030a02070602010506040e06 82
    0x1422803519002100000c80c000c0368002074a42d080201e059001640364000c2c462546007520404040c030415000843ca8030301200045110440c00030100403404440d5200c000d0306850510244840300da00602c1140d54020a29000010000554907035001e200034100185001a0902c00c80e4140d903c5007001048922106408402610914504840d0103642120025403080544241e680c25118009001489400c4c028641c0c50024010800d0081042204a10380424404a10b07081500d821000380491034800c1c0b0010b8490b0520b410758269100b440b50100010f10001001950180d01059018041582d541c50f00c14283d000613074143c40f08407065000710005141100700c2803090514968260140ca9580d2034180505140d00340141d019002900a010391170b40c5403041040c400660b5072800d0400c41449260709420105000b90414580d0004c1c130b00c40b001d8001d107100c900910442d001c8035607801500a0007074440140c1c2c070500f4007560030000410a5803400740260400540000c6c014142590707001c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 326137886 1250 326136636 326136641
    0xf0402040209040605060a030e0f0a020d120908070308040302090901050103021f090302030a08030405150408030406110c0d11100506030325120201050402011e02071503020405030304080105180d050d 87
    0x1072a0a40c829a039000005d019180d03400034140e0320040d40c07400122400d0f41c15006082440e250583da01580245d1083c00050799400c400090258005002658000c07801c0700c0ae44400300030707400450581c40382c90000800c000b5a10003d0041c0e0f4400d4654500326200c83d1b01d905d00782c40081c04029880344128426002c003141a00c3c0500c0000000c3c680500c8095030380e0082030038601c40d24415542c0380303000010001404010402490041c400f0082c21802c2e240a4482c040c250102500080c400c1da03c07000684901c4000009541d40d003190b501c1550780b20400c10402074a020343c81070300d41d5154000c2d505003000791002c61050380d208bd200900550316192419480215802130460401c040d42d20900d03c10300450001c251035124003003250000250340c1003900014101c542d0840c80c2c002098031144940c2031036980441c507081100c2e0352805034185c41d140060190068044c54204907058817000c2000078800c05c05400c4a4060031b42c8640094040c14003100007612680c0000e04113010980800501c4000140c55 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 326139136 1250 326137886 326137897
    0x1701020c0604030f270e06060f0f130e07033303060209041113093b030f120604062103050913020a020606010f03051506130806070207140402030f04020402 68
    0x52400c0c0c030241d080c0305c0c0d4000e44010f20031030422600c01c25400901c80d00d50340301c4202d130300407100310340aa0806a1102d0004014402c004095158540204d04440701d0807210b06101e002e000119000c8070145402d21004000784858001503480c8001807404e10407a900301141c289070001c0c051940420740b81903403603503000396101800441d0410307520721100541110070303030103003408a000d00419104280380c040d5100607100650318441c0000e1850502d0100d4441c1001d2440084a01680050300406215610350a40c050640d41c00ca64040c0014110080c0c81600c0e000f41c41400216410801c0e10f0319261800d0803a000d01750560064800140c1314800700780a84094000000700400c00540d914030900d04070103a800845104d000342e4489000d1181075a00714011340c082e00b03030902c0c08000c5403a0504e501a69081100c01d40b50259000080350650301014104101c00b401000c000c48100d41403007074009586075a41e20a0404100c032103002008d052a25008583c0100d0050074840543d46440c0c0802000b507018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 326140386 1250 326139136 326139167
    0x30c08061009121b0f0303020c01030c08011205120c0703060509120a11010e0709050402100305040809100c080c07080708010e060105011103091e01090f0513050403050409090c1701020c060403 84
    0x21400390310113500b034503050782000c0c00514001103403003441c500e8081d00d0700d440e0891090500d030405200400295000030841c0c1150f105000c40f8810512a0a009041243d502010301d201d41e000540324034403090008460044038801e2904005d02d80d5070103000da0300e82c002c01c0c11200314141c041000c2503140748075260040800307524030000030b0010400c400746498182c4542c82401000d456034104015884c283d0400e500c0d660880c1400d01032482c0c00d0351f82e08118442c410f5074034403524100313043d5010f041c441c000084e401d981c800720703007030fa10105c001c441e69490025100786c1c00f541c03007446030200387d4000c1030140703082c40c0300008010704260f401c16005603160b0000d0701280620b40b005203c3c00c00c0079516a190b04441c4000241c540041d20312100005001e000190003850f40d07240c1d082400c000c40e440d11210900103100000d4001480d0304e83d85000c0f12140324961009000c18200a81c1e44240030042c03100750115030801504007985104204424280d0080b02c0c40c400c101c0c3c01134400640828003810001010211 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 326141636 1250 326140386 326140403
    0x1d0d050f07030b0403030b010201020304151a0d060e010e0f030a030b010512070801050f100206130602070b01030501020408060f04030f0e061c0b100512010b0c100c030c0806100912 79
    0x1641540514007041c1e548192401c659140c1803005154042c8100d980160007840250724610f41600d9440703945203200000946595214890102c0c4180b403401d82404c0103009040980c1c000b124100703a0054101c1d0350107624254a08094802803000004000ba0010000341c040d50801c090700a042c0c008100d9041c11a041c49010001c03494850b10300c5114501c112001d0300c881140d9418031051154413101071849500569505443e070ba07242e50005a5540d00140c106194049204146456000380c06401402040310a094001004019040d0080c00c00e50b504c00b8210f03400c0e0707660000c07113801039001900e01501003101e0f4910101000d12503c450901d2040280c40d4030700d800621080490468100400001c9003035030380310018031620b010a1000703400030040c03400d581444603020640b003034284e0600c15010107910018124400501c10b000c1d0b400154400c070400c000000c104800a0050501040000300140301400010307420316000c242d0500440c070503950139040c641480150181304504071019996203d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 326142886 1250 326141636 326141653
    0xa03140a120224060102070b0f071202060f06010e15090d05060709050102070512070b0309070801020d0203060906090709060c0f050d0c02011202160602070201030f0603080c0d1d0d05 80
    0x900703522440c03216501990083c51611084500e801000341012541220340c071101c0c05001c0960b90024100c02540c0c0c1c0c0184607659001d40070741c02d00e680d200b8428000c20040804503204800754001c030f09030344a00c0b201001c400f102d5450600460300c1000180e950b0764410581184610341051160140040860240003461440490f403034051510b40229082c10000c4c020760b80030320917540d06000c1c8034001c00c401e440c0b054500066041c03040d02d6140501503415410408030006003276007400c1120b407005240302c5008542d40c401006041e806940211000d6000d00082e4021031800d051901406100b481c05a980c520600e04182c8110f0b0700d0000004151a9a106d250391400800ca061102d901d4564450302d402d01505800d00c0050508000029801411841400a2800b0390301603000440300d00e6120038010ba4841d0944016001031035200d03807120b085880c00c90b001c010031130303428020007145002c0012a03500007840032048a0b111078403082d55540c46104075000355035050040030007402e01d20604c00c0d2403800e0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 326144136 1250 326142886 326142893
    0x1021b03070812040519110f060f040515070c0305100b0d0302060a051503030c0a062a20031306030605040623042703121112040303060b0705010218010c020a03140a 72
    0x341c0b110064072045a8401f8a8006280030300100f221000250303000741c10081c1021440700c0030b0190344503507070040e034120070b1050b00c1140700400c680d103203035000c68a80e000c945c40f410120303070701c08414040c10b042c249403008007a0355141c08000c003c2c116616500031300027691403220a402500e005008a0424480c3c1c07a00e25819a034148050b15443c030784c550003044103502e2410403006031460101d50b0b0140100561b000c0012403072184c20b545074800113013080d000303c090304084a0418015800c003081d40d40004605005c6582e4800c210204a075029601804259110b108000880700c2c50f208108003c400e82e4981d145a0110002244481c0c0c8000c10009241000d0b0340b1800020340c041d820741503101c0f000c0c0d28110070550014000f1316011040c0720108060140e800c0c50102c075100d000415102480f000c00041d0030944a034014201400310840f040e900e81403c1c0c84c0c03030382c043d4020048945054541c0690460b142d4031541003c034246400a04941c0e02a28540742c40e40200c9031030000305010b001c2c0321004c1012 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 326145386 1250 326144136 326144173
    0x612020607060b0102071203030f0f021903020901120509061509091b0a030b0f0106090f060807180305121315021c02010204051011010f0b090c0c15040501021b030708120405 76
    0x1f01406910041141d05c0382c084100100ca00300060814400d1041c000ba040100504a600000310340d01d041c0113030744030070120050700d48842c0d0b8400030001e6030424042100c19900820000d000381e400a44084100301000e0802004203001c40c0e841856a00c0410700300c0784202180d200104101010305540300b481e4490b202c1d001c94000803140c0400044040b0f00410a840c1e114a04500410306d40c0e009000050802d5002003984001a20f980200070758078210100004d1421410b0005651040841c0c424070504c1106043c19008004116840d003045100001c420044210720654806d16502405c400044903401d0035500300546a110119035091202084988540c00c4c442840452903d80b0700d450b02143c28203a003900d01e480300000b03449043c10003008094464481c0b4980250238152001d03100c54090030042d02c0c00c908410300f5050b415805e41448240841940141b6046526292031801c80b2a9510055964030441e44000c3c44d2000822044100c04424810075030001e202d107040d10854203918814030768 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 326146636 1250 326145386 326145419
    0x2205131e03090b1920060a020d0b100905030c010e1804050f030a020a02041a0102120309030d02160c1a0708030406060b0d29090c030612030a050703030612020607060b010207 76
    0x5400c880d51a000c0c645504403501021111850008651032152060341741c1c1c80d070380d01403c031950064004c00d803c07507030100d01c2d0000000c01070050201902c003480d6000c02807810320603116050090041d119440090f522a04c1304014144014019240d15403221075907a155035401841031b10b060107045103141c85114144020301c8114025030003840c0720706981c010041100c18a1b1200001740f4070162882010b41d80206400c980180791107000c980b00d80d0303501c00480c00d52140f40104c0031858070028000c034031007000b0041d0800c076600a9040003480d513184c4012011030060007000b00c42e0a282031240100141d2040000e50340244544008200955118a0100e044d00002442a41c482c2c540f50b044d110707684010395601d000603a4603042a80401d07490041041c52001038429441060700000082b12a00c0e1858000020f100040860b0b64508030154010200d8103d0b90303044000909100c80015100e22039070040c100c0d01c0d0014807030740c5000c01e00e0b96500020700d518403485040d402103490000f55a48200181070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 326147886 1250 326146636 326146657
    0x3092a12021504030c150c05151b0f030a05010e04021e0607021f020d020607050904020d02160807060e0307110d06140109021308060403140a020c2205131e03090b 71
    0x100b0909000004151405c001b02c10b204005803101003c021680010780c400d40d0384402140d60f0300c10303240c40520b50032450350001e016400f40b05c0010300c09800c0e8209002588180c0e80c4d03102c104060398a503c9107000181c82500d010754403502103c000c0100410401031003450020050690b440d00346198003140d807502c0c03824a08a039804c0d03030301c00141700c0940610600006038054406864145820131014000740030f503145007401a41d0105241070703800c01c154101c0356035510548103856511000d00c0c00c420168400141101d03040c7c10000a81403c00d400802c0d03d0005900c03401c0b0006076075082081c46040e60004001380c81c40c41d204c050100c025101c02c2c0d07285000e0000c0c8400583c1d1640300b803040045110b400d130f00c01d003015844140ac2101007580102000c002202002081340c0da0f814030b600032481c000c110a40164070035642c51419004c0c1030340c401300d00014001c8640c14481075854241b00e0141c0ca982202c00361541c40400f101c046006055000c10b5066842400d10008a940318003508481c1d801489085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 326149136 1250 326147886 326147903
    0x190510080a1709130b130b1e0a0306320106020325200103150806070302130e090d030b01050703170a060b030405030304020108060d320a0303092a1202150403 69
    0x107030705901b0540c00380131110020b0003085c00441500320109081944509147c80705115150901000356607841c0d50500441d04480144044951050940c65a0801c0c1e0f5286007114004140041072004038803a0354102e4003203030007950401106000c0c02070303240050b102443c443e44500c0004030001c0c0764440d485107009907043c2c002c282800302ca000942201c8a8801c05484410508000c1008620002d40c19520171018500561180c00190386150f41491541085540500200030420081e41c00258007044a2850b078040c006009100d00641c0c40d44a00030b005400075210b080344000012814500e250407010004000400c00d545d4488000c0d50780003640c086400fa00004188403c0d5039101c560305810080032140001c0c920265500e0614064082949400ba402a520003c031804180d403140d00ba000c0011040d910006031f80d2070002c0c01881801c20443d8003114030160400780040d00a4a040c1354004010481c8400e0b00b080b40c00c02c50a203c509040f0392090740020100100c4e0310141c00f50000758490201c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 326150386 1250 326149136 326149151
    0x1d130617061005120304151e0c020312030105030a020f2b0b0601090b0d0506010903020a090f0f020a0c020409080904110706061a0d090309080105190510080a170913 72
    0x4858480030030343c402c070310440d40000720054114002c001c4a0450303076804032088600e602e410741941e0369140ca0380b581c4480d44802039041d03041034008824a145600c05c03070a50f00707012200b803100c2c881804280907880e0540d0042001c074005082c260003100c8400c2000302480c0d042e41d03800220107507110002c24400c2c0912010680300c070812604405660304a1070034207003640c1c15420246c038801c060140c203200310070150f21203003c40c960364080d598890145401400620300c154540307035408068820b0402c615402c0745000410070b03000b8001e10969004068654407007140e95500d0b020031014040701502900d118004003e02d40140d40c440c45100003107400450001d80f55080c9040c0300d02110314550210311081c100b45917410940c08480101d030540000190005043c1103603040840c1e52078015080b101c40c0c0d40c42c00c2c0601c2828001d200895039031148200703042c443d55403201c00c120501b2400b0301c0360501ea130744424100f0340051049000c251503500309112031030401003c18000349075a081c402690049940d01c9a2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 326151636 1250 326150386 326150401
    0x4140f100b120a081303060606030b01170103050c130605060a020c0111160308030c07060911030c0d1a0726150f21030c0114010f061d13061706 63
    0xa401c0c01c14411100604200301e00c0d0202d649844808000820300200005d030751228440c40e401c68405982c001d80c040040301c0c1c032800084d008150b08080b06000c031b00d072400c1a080103082038000c14140ca90142c007400042e0780a17420322074510000145c0e114159299000400c0c80d441c1c0e980544100c600550040070940d0f080400503040084941e1102c1180d00324030111858aa181100d027404c995210589a603642d599078410701041c003480d900106414104418101403248000c1c0107061201e0883c2502c009960b01c208101403118a0000104030050640521045c0c0071a00c060640c08202402c040390b95100303005c030f105013500b80001c044100a0418040c010b03100c1e00c1c4081800c80b4a0f040e1140314401e4282e01c000303620703a200310b180724a0342c01c100d84640003841c400b48161035040308034034024046042a007505803010b240074015480000d60014000901900c284890700222840b40686106681100c061004403140d10b11a801c5154440900041940c000e05641c140f410300780015280904040b82c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 326152886 1250 326151636 326151641
    0xa120906020601270b03010212010e0114090f10120303140112030e2b0809090603190f0c030b010603021806040f050423070f08070f140304140f10 64
    0x20003020071075001000600c034007040f00e0b0340344a0101a1040355661510103201c0000039001076050f60760036500110741400c90700f0080d4400360583e2290f40c2041d590fa030300c8150a42e50483c8510116500100410200d602c2042e102e1020390424020303e904c0c2c0c841034480b4080d0f04c9007062414101c0020b6910030b64000349d84400b8903020702400d08014160f007020a6500c00601109034410914810328070381d0050b41001e0741341c13100180b0400d00030000b054060340314100702c20b07140c000007601c6024040984c0051001e2801241c100c90b5060341c001c24008491181e00c2c0e81414009628048441c140300c801c0c080007040440003101e00900706940c0150755032405a120030002c4030202c002d00d0003442c0604c424800c1074103481c0544142c5005860020b500303407100d07402e4040304840454142a801c2c0e83c9060101c446e501070000c80e40b019a9880302c8004e515849400c0700ca0f200700540841c001040400b0040c10303403c1c1c890046411a003d4640801c401d2548001c090921507804a41c03442c81c1d005180146e1041d0690 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 326154136 1250 326152886 326152889
    0x40b160c020901051915050703080c0f04030f03030f1b021b03060a0b060702061902150112080a05092d0315160215070302040608010503010504020d02060901110a1209 73
    0xd26081860082a5000ca6076510040c00307141e1060700f00c0750100206914107844c2e8002000003e04000513484200e90140c000d0748124410f50002d244000020b601400c248222107149201e1019246080d280d80c84089280a80a00071010151100d40c6d03903000144a014800085000c0e14a801c6202c00720980a80742c0242c4640388d007925042c0382c984010b1540c0201704d0f00d07031010b030340c80001c41d8410400e0b0000c1c0c600d100f0110000c2d400b990200350030304010a5100880c60101464085403518008500400c0c4419000d00c04ca01b502e1203000340c04c00005003440003600c100581e9040050a1082000010300c0b50303c04100044044c1c901680b107400f500c0316a00818144280a03400742c0080105100d075441e5007a001483c244040d207000201c10039140c42001a8440c00c0000102d032400e904205c600180603520900c04c00d000a103401c0008902e40c581031007030314091a0b004102c4519210700340c2c288a00d42c0c2000c0a0281800344800e050380041c00280724440069128511070011032810701d4000e043c96405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 326155386 1250 326154136 326154181
    0x1308030a08010512061e07090308030405010f14010b1608091215010618051903020d0302010b0108060a14040504020a0518011e1511010f020c0303070905010203090319020a030209040b 80
    0x11170144040942d24080b549049901590b00101c143d035180000d41e001d40203075000410303202c00001048144181075001e086c0784c40f106141030000c0c0080d031500f5002110300b800f0300702e4480020418012214110f841c00410f1502c074151a0f402c0c5081040000c04407989008444600e030041c04440c090008480c00c0e03079016000d2810500b00c80d41c44228503140d0030010f4001c0d035014074803108030404c240745407040310340096900603c045903102e201d1074000c3c080c00304043d8081c0403820600100741c581c608080c800040c0d1303903810000d00c003600e40c4404100c040c045c0030700140e8000096041c042a10744030388007000b074003040d044240d00555152040d070385990180c10003800703440c60800b8020301140d004945412481e405a2410001100c4c030040d0250052111851130115584009031502000341d000c40554803820603034686c00c05166079103005903143c3c4a0041c01903450f421420182c1c010002c0c20a00d51039842c00540110145501c03640421540d10040d41c00342c90406200c42001103103030006020b010b50320348 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 326156636 1250 326155386 326155393
    0x13030e01020726010f050403020a05060121080a1107090903020712020616060209030a0f0b0901140121060c03060509090109030e011d150a020f0c030604081308030a08010512 76
    0xa440c1801c07555105800250501e0800004403000b683c0094100c1d440d10440810100842d040070725001e59501079a1000720b440c1d006945c00010742ca081044007a0102d0440c42d01150300c00ea840e40c4200741c1d603001102d00414402c140c281040b198a0800000019140210002412443d90704019103002c8050b400751070780c0711290b0000c5006032100401c0e18105c3e5401c408036820b4100c540342c120040d0058a9001c0c3e00b51003007036440706c240501c42c4008900c40d402200ca503507141d1140d2144500b0b80321034102034003018410400400441c1814032203250b00c514401070b890940c820541c0c0303110643d486907540c1d00010b43c46d020180020314055100d250042e042500800420140c4d507000b801d04442d8824440c140300c8003480c0107801c40da1058009100000090001c034004044130800785242d00140f2804005108420014451140002d550321a40800400038552076990b41d540e00c00b15170019008512500800a00080d01d0f40208040c140c0c645030341c2c880702000e40c14401401400a10031a5141d6030380d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 326157886 1250 326156636 326156639
    0xc08210304110d05030d0e070611030909070e0f091f06020d09140607020301020705010903030f060807030f14030301060519050f181c11040c02120406030504150513030e010207 77
    0x100030514042d0820400d59400c0c00c14401400c0a030b085d4014030500c4000070381068850440d00303d010039580280c65031074132140c411703290004040c7d80d64041e00030016002600a408603540701d0007000d6504807118000c00c0006298800e0000c1819110142c0d525110b00c04100c0030b800300803481c0c0c1044c40251440d07100a208a4880200c01130440c241441403000c2044228070000040e16100d04a607412074019009555842c0e1380c2c5041b500030640c03030005400192410b003040a45180c80d004d05d004a4244000908800382161605c0508601d00d10044071440701c1034840719080d110a0003d140200000d8590984070040c99900c0c00d0040c44100c0e6400c1002001c001c941c285281c124181c4499203190182c02001050303803804101000007030280c810055981e00d00c100100a400d40038609140410f55041c46800c40811007a41d5450004841c01c010410620041c00024840e601042d8050b00600d00c02043c000700c03104003001c56105542801050191609250034550480a42010100c0a00c018924503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 326159136 1250 326157886 326157893
    0x9010f0e01201603141e2a030a0324030b010824070804021201020f0d15080303010b0c07032010090f05060901110d0509030d030606021f090c08210304 66
    0x83c51003000302804001254100c194010200341e550907002000701c024600c0f81c92a1611050b0442d609014080045060342c180c0100c000307820030406080200214101605200164050102d410040d41040100440c0c43d02c1290506040b50007107000308159120743d414841400d08085000f000500203210309590400909203240003a0f82c4414a840e08004603182d520010b2840c061540f4400c11a60010513410503150310440205100c41c0c0850080002c2e10b01100c1c01e4800300081c0c0704103d440d40090004000c101da440e001009140d44100684174031580f0f95403140154401c0080c0c10050101c3d2513184440d03400c0603050300c40e02a4240c20301c00c5105180502501d410466401114043e03500803440400d187d01a04040c0309420502c0c0a4139485605020001d040390003131002c0c07a1280c80f59644c01420213009108150031b58030954050581159810403c1c200d0105400042c40a160768890b0341d0041452045480050a5110041c103214114400c80844085410500c656404010014003000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 326160386 1250 326159136 326159167
    0x10e0a090c08091606110a06050403110f1603060b060c030a0c0204180f112b061b05040e0c0c03070506060103060602070b070b04140d020c030118020105070b09010f0e0120 75
    0x200c41c4c55290210742880390b881b13074a0a00e005040000c080d1130501040c401010b420440c01580c900703103101200c10707103001d60111650361001c40404c0002c10b09180c03014008224550421480304601401c485c0c45c059079040340300d02c1c540c8010f0202000030369240483c0214034150048002d8400c600f4a000d40c05015034603070844402e40d03844010900140340035803200540383d912052041030050300041202900d5013003151b224030701c002c008980580c03824011100881c0c005a2400f0074481541e00c041c1007170300307090a402c00c18001420040e0984401d001e002e4400346d041000340b00341c1e40f00d0b0001d484613051180024090351003580000301990417102040c0b2a14102505035200d140d0000106801609e407414100d1002007010101c0c0030900640d0819925140c0024284d900c0010580003001041c5102c0100c61400100500c002e0001c4c2c0304201a002258001c4c43c00ca0f000980c15000081c03040310845403004a9284000302a40c0d41d444d06403186c0700242c80a07015080000350450546042c4603c0e8440c1c54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 326161636 1250 326160386 326160389
    0x311040518040512041d0601020624030309090103050a020103150528090e03070b0106080609190e10060f0e0402060702010c0519081b07051e010e0a090c080916 70
    0x8400c1c90000041c24070004200500400b001408480d54864071225030441c2c00c102d007803d2100802c80c2030040703102d6520020312540704480c40003980c03904c8988008180c1e42210340019071070385448180080d044503600d01070201d00862080000303120141d03440c4000741c03d4680608104031074001000f010804c54590b4a401c0f00130009154130814111071000000c1d00201d019044010128a889030884401d00004000c00c030440c000c41e0043d031a41c1c0e880c00c08079440901100d440d40c000d640345011071104e080d40c102c0d044004482c080b000c940f0b0f0f030011a025207003000e010b80101c412034032980704001e041505d00b950005403c03500c0520030781b0300c2c20fa008a442071041034002410000f204002500340407083c071400e00e20030080070b90041d180c01d20341060f12081e00044400c00c0001c05110f01201c400000141d00811110040c0c07220315066064108400120315001081f4180040e04010107580d98460480e140a05404200018210065000200400001002075809611000e070740d04160346612420b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 326162886 1250 326161636 326161669
    0x1020304061b0803040507050111010603020102150901021c0615020c0a0e25030f1a0102070915080f010c2a24020703080f0603030a172d060103110405 66
    0x1664680c0c21900582542034011010f04a52004810700080220121b5042c0c11610240d03100245031107a500b415080700d45034400280541d001001d0312030700c40340c007140c525840089000018246440f004803051034542070988800816600c04040c0000d80c1d103c0700d521000d45182c4004c210b011035410100d070314081c2c1800785500c030541d6040081c00e003c40031f0030f08402560143d42c110b4501100300f80050701410005000d45081410003484400101c001c0c00701d4200d00c81c05030300404100f072034103211500030990303030071183c201e40c010b182e0110b41c0c1c00080140901c440307da803000240c00100d0643c018020406104014a480c00405048103500e198543d00094203401100010717450744c0c0c903510342d81005002180e100c20680082041c0050640002d0421710910320300e51030700703455a04c000c20540c0b00d1007000303124400714448a031242a00010b041d0b049500c0707481000080036604d002440300a40c82d203a00c0407481520142000c2013180d581c14002e0502d240100250a42404e050000203040d203140c0030505d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 326164136 1250 326162886 326162897
    0x3060406140c040e18010603081813022a0115180c02030c030a03020d141503062505030a0b0307120c05040b06180d0215121305070501110a0203150108010b010309020102030406 77
    0x400c0ca051700b0b6004800450b0701070031099542a80300c84240401070301600d11032142040c0700c91589256400d008466071614920142100d10030341c2c80600e205050002d440c068150359424101080003407a0315200c01400300310451140c102c141d06051425645a0808001150814480c40d0704101e400020313190141c802d400d0150320b0320754091440c0000c03c08403c07000305a400395018405040c200510303050360341e00d00b50207840741d590362203001140040c034030141030000005c0d4400a82c002407146001c1d6401c4403a1110210301d8140000c0024a4005641c01858640194240c880c040101c02203601c030040c00305135000c0c000340d008507000410307900500d41c66420a54002c5106400703035641c00d160250341c540c0100f9890700403140100e025844e400c000240070810b62030340003081d4610b0f14044840c02d910343c0800207101540c20400116045008403100003400c2c401d0041000040e64203001c00f00c0200206010f50321590704d40b02d0114207540f40031503c9814149060f1103c80544d07808012541682d1490610 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 326165386 1250 326164136 326164171
    0x17070b040b19050c0301050f03010b0105030703020c010605030604080a090e042103020d0f020409110f160201021f020a030506010512180a170a170112030f050903060406140c040e 78
    0x1d054800300c0094400302843c0340030104544d240d40301010354107031102500c01d840c8101d10300e018107088981040e00140400c00510008030460f10070f8000788104c2141c00008200c09540b02c010030f00d8444107440032545000040707040102c150f44403110030700070114403200c403403030381080e48a0309a44030982c0089610043d080c50010b0074603000342c0484a2442d0000001c1100e194a801c80d00004e401502075004803508010030002122145c4041d0341d07080320a04001c0b0b280000c1e08011010a00008508074194081d0b102010214005042803c0810030300d4280580e9803205007400404990000f00142d061000611142e005c282d085004c0d140d1212401c560b69038041403401c2410b1901e03000300801009001c00a0303c8a0000107060064000181d842e01d844410398620904500410424081c901c541e907400b004490101e40301d00e007695045d08250509a2801d00c40740c003c0390030080c00f200d041c0c03006500d0f0760090321006050f15509034000206a205404e0504055003024031a4000d811030043c0c4102110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 326166636 1250 326165386 326165401
    0xa0e0f0604030b070f020d020d2a080304030302030a0f060e070f0912030504080c0906011403040201050d0e0a0510020307050702040b030712050607020111160f0c0503030d020717070b040b 82
    0xc44000d103410043c54140c620b841d00d4010403601010704201c0050040c0c41944042d01e000040902044c1143d4072200e40c0f43c00382c000a41011820250090070f00140e904480011440b041c0046000c0d034005d0b503000d0303901d14103450002d094400721020034040d43c0c64a80200011280683c0081d0048010b00c0c0003d81d1015030101201c01807110780001f4650000c2d800c0daa400c054020008108558034581529020030b07550b810090340241c2141e0b010f001c40d892500c00c40e0b03a1454038000b142c0c05031050411908000b60481c4080803900b40316010011544411080e9041c002c00700410b1703001400f01c0e0700c213501c0c40c60454402845401a408003c2c0100d0700d130350715000986c1e410310880d0090901341680e503a4549403820807039980e000a4602c400594a00f45a04003613036201001c507900c00c0d091880c0390400344080e6459034600f208804003594031452034400410716507810320040101030b03031440c40980c40f480281840440410150b91540844204101c1d8000043c403c0c40042e9010350800e000344525902c095 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 326167886 1250 326166636 326166649
    0x10e0a0b030f1c0305150105120403020304150e040e1612030507170415140f03091006060302190c0f080a2001060e0603010c17090109060f05040212030a0e0f 69
    0x300c100d840b0b010f9118051404030228000b42d44a03d4a03a6007030261352210006062020b400c01e20060024504204a03440c6600040ca140e400c284a4412640b400c0e95030a00f41120b1040c5241e450b0010303004040e020b0052802d030145400b40543e40024104c19401443e00364003500241c4161000701c02c102205805050050040e00d0ba0580c001d1148054032b030070640e40e840c040c2c2c098050003a0100c85540f0b807034003e0348201e5524000e40f80c01407205250181e940b401c00c205400080c03010046109014070072136280c00368051701e0b0081260b5140903840b00740704c0003152410014a15490204440c02c40c17400013240b112107221510942000041e6503070450b1000c2226007504440b05040c04080d0364511000d00340c01580310f03a00300d64440b20603091940343c0030101400d07907800c03940080018010b40c5120004220b00788585420106c0500000f5604020b9030702c96041d203803603e4a000780d040d5280100008c3d41003140c1d01d42c90140428000c3d52402e2040440504120300014826010b00100c160344d1010381c9910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 326169136 1250 326167886 326167903
    0x907180605040515100f05122d01030302190309120303110c060a0b01140901210e010f06050a0605030a020d090c0b0a1e0c110301060b1306020c09010e0a0b03 69
    0xd0020f1006141880c04066080d84802c0268001c07030040304070121691090506000c100116551a440c210f03480452080e10840901004003c54400750301603101d0f540c000c089140190003100300d83c000d62448c140039080030b00e040a00c1c0100c00318841f001d00060362103075030b10f42603a5071160741c2c50000500c0c3c2002c600411019003208180400001c01d2034034a9000141d05201e03d48021041c4154034850004640100180041e549165010301c00a2003940c02280707600311941484000c2030f544010401242c06680c400300c0301c125140d6451099445200d1940a82d070050041902d60005987c60508002c04500c0024005809241d02140c6140c10040a4000e50748064003d1145400d00751107807410a043e0b030050504038045041c8498040e0070202c040260248c0c4905500c418814540d552100300010003441c680942c15540c40c00086000e62112000d1314954840100c2c0c100144e081410180c40c0c0540c10801340e10903000003004001d10f50048000315400b558000000c1003082c81000441d1604a10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 326170386 1250 326169136 326169139
    0xe010501140d080705010f0c020a1202030a05030a0c1e03060911030c0301060819150e06041a040e0a0f0506060907020105011410110a0602031005040203040804030318090905030904050f0907180605 86
    0x1d2080c2030810039800140c2b00c483c6401882c0060380003d80141c180da8a106240d48000030941c1400090380103a25907020460310f441c1810080c840d800c45011480980c80b8180340580800d81d03030b0000707000050044c82000c8401888012507071440c10300000304031103030005119071420000741d440001c40c00d43e50410302e088000020b40082c464038200c22010304048640d0300400e114080c0c0b1000052031480c0078000c00481460200c80c140302c00b20518180300240c00748541007009807141401280014901e8000700804500030b070050200381c1003d404102c000d10001d001c9604580c10100148845400c00c40d2542d034000c0304032500300701100f044038265001038040309110000c1c001c0f00a9041401a1a001103202e9890460049196511001000100c1c001aa4040c3c03005a00780014400280030b080101300c441807201180494642e1450f01700103a0306040f41c01c82e030780d810104040010341094011250081d4441b03506c1152442c5c00b0040c5a030340c03400f5204424100c030031220300c401d415543c1d40c0918042c010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 326171636 1250 326170386 326170391
    0x10e060a0e07030f15050702060411040f02040b19091d0a0b0a1805010e07020a0f08030604021201090905010507030606021c09080d09080f03121810020304060e010501140d080705010f 80
    0x1c03e8140f40f02172002c001c2c1858655410040040c420350b201080b40c0b4483c0e940609a50b20545115061000600d45801300c042556800c0001154000c000400b520b0500e9140c400303082d0810381c94600130011031455015400c03003181d601401001c080e000010340d511a158020010311181e0a1001803a951100e6024424462540881211000d115000780c2d06030f540c1d0425101050702e44000882c1c0e10040d14001806a9182001c1203000901400042d034210f44010b00250400c100340a60301d4042000fa401035080f29034604556082040c2800307880da0000c00703800c08116007464040042d40b9040320300100201c110020283d41c00950040640340c000d414003108441c0e5042c0540d0010b8240c590302d000d40304440c0301e07401000b420b0b8640001116030890310080c040750329480354064022005080c0e8803c0d1040d018160107085234940e0303440030310720550269002040341101e01181c207003102c4060700030324800680310700b0300040d039150824040506075210080361350781d15460402e240100300c1024100d41c01350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 326172886 1250 326171636 326171663
    0x2040903020c01020609060c0a181a03072714120601080c01110d20010e1207150507020d0e04060512210310150309060c1d0102010e060a0e0703 63
    0x1540010b504460b20000c0e021a89203450f4070100581c1d0305d0048402c982558420003594084504c144980d0150041c50802040d0494440d18103800440001e10404010100401080300c0d40d40d02ca20045080b03c1100402e04102241d94050700c6141003900400e151102440318036503c50319050140d0b110059803205031031030395856452041e296000103500b00c0c002613440d1900b81c0200d201243e8091807074801d481e0312241890044402850500411201c08195628030b00300004680611402807400000160103545d5078203843c2600e020750076010584003003483d00080012450f00010341c804c06c0030050500071440e8588000040260841e50012500840302082c8401080e500054140209130b0b00a64060a01c20a08001c0100c0c081140c0100703000d14034100802030454205c0c1000c5940e441c5184c0454040c95a407650400c0d143c04548100001350b450103409114400f0103606200400244000e02c00c0e10210404540d031220060410984555905902d0004250400ca0b840017594030026000741417 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 326174136 1250 326172886 326172893
    0x10c02040e0105090106090b0906090702100204030c0e1e041e060603061a091b03040804030b13060b010f12050c0c06010303050307020601050d0f1202030f042408041a0402040603020409 81
    0x801d020380b901c4d00c0d83d40c00c200d40810b250320305000d28a0000e0700500305405075510034040005101002e17021000794010804040101081400104080c50250407510516403801d403412030045001008a00400450a0381c040d8025009861540290308084c007007840300041d24541545201c2d110008110603e00240001040840e400c031500e0310f800c0c0c24060348406a407034140020f043c42105e84442c0314155500181c5c140700d0080145400c14001c0242a00b0035880c2c1c1d0741d045480e0021381e50130601c022100e400c0d1003009101c0c02420b010340300a190404003510342401c0a0310755815100c0b6151902d0303c0d6000209441021415a050300c5c001404541c0c4a507540d040107081d6070f1058030303500018022040040b42d00d080990ba1415203d9204154100a010907110100e007180e1a001c00011400100000c964a03503803103010303201800400316007600e8101e807001c4003031803004100b000c2006d01081c0c1c810000032940040d00d01d400c0700e1001001c14520385e500c1c130000e0300a000b40c0c6c000950181c58100d051050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 326175386 1250 326174136 326174141
    0x120908030417060a0b1807050706090b041202120405090a0b0901060918020313030f0c0209180f060c031306020c070612050609090c0607020a05030703080307140a1d010c02040e01 78
    0x1c603140c40041c2e8403251140d4100e134050328006401280c005190303401400c5201404040f095100425241c05400c00741103a0f80c00342a11201c00050711068001c606103c14010b03022641d0003e00218001090800181780c40d00c2c450b801544075003841603c401d400206410754a4000d00241000140800610b6031641c1000d800302c2c1d028010003000351080848104030f030855108880c003c140b2030481240020003940e040f85c890040c03650720b4003040f51680d41d1a00688401114034010202c2e4288c800d2840e00c1601c11a03e00201c0d074158001c141d00003000d124a060001e011a07030000da0030006100d1084690810320301911840d8072143c12032081560020b20740307070700c0b502605031888035040c10300440c1c07100c9040000000065074690060781040c3c080005900c3c00c2001048034601c09802d1560b003641c1c810001c0e04122641d40140c2d032856000007009009a403100c0c000000514907100c840c109090060700070290799070045079003500d1b83e40d6240c041440e0b01900104039100c0d4010000d015500010424038003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 326176636 1250 326175386 326175419
    0x100b0a0f0308040f0b07020f060306010309060e060612150f06180c07120309050c040f0f020304060b1f02060f0a1d070510030c0c02040c0302070203030c01150b0c0a1209080304 77
    0x10782e0b07845507001003680c004005c12205030304e030000c00303000050f400c0204100c020341c005008181416a00c40902001401d079008034085005540058803072450f00c2c4041c08800b03142c00c40c050f46d064000705462540030321b10940d22500b040389030784601519503c80000c504051800d078840340d01200c100c2c042040c0440c84500501490384070303566024a0403039406007501618100c040082c0180c03c09014407465040a600c4600303900001d203008902080321102560482c2d01c162029100130751203000411b0641000802103080d00a46498a05c50401c02d110007500d50341c0103030442000120880101d0704901c1560030851860168064207031420021040c8940c1d07580701c502c40c46010b5500f0300c030716028803402032044184a620b85d844200e00303c103c6a081000400d421a50001495030034040200980c5080010303204180400c07000255002c06d021440c803810032103034070082101c1c000f00150302c1c0c10440440c140329401e0340b04c80c02c034600840184003510380d0a10303030b0004207051002040008012010700340100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 326177886 1250 326176636 326176649
    0x1207171e031510050328180c050901080304060912020604090615020d0516030c0c12080301030b091902040207051e010606030506120706080c043302010e100b0a0f030804 74
    0x6a080101640c1904c00740022240800031500c810041043d44000c1c100410790100350f03400005e0b07840402440c41050981440d001d07181944008030a029030304102284074094400031008504043c03070850014680f1260380204046005a00c0700d100840d250b501c2502c0261081c0e1806005581c0c0b2105140c030081c800199410062142095510219004000b1107900d0a15034545800c100700030748090300d080600c22411030700e800c050071000510741c4c40c080e122441c0c24400e0007410342e65455411311010030980038180c8082500501008080003071401c46282c0600e07410307100942c07101310034200030b07080002c80800c0c602c2d0500803c0c804c0c1c050f0981903022030300790307505600c1c20031013a11800244a41c900741850315202c1a401002c041c001c1e03d000344003e560024000400520b417a4451000c844045a016200c4403600391f074100164000b08018040110810244000c10140040004407907441c4820b074540d401035507480b03007840d04c5601e0b18103441001d02200d824004056a070f901c1c00303040c81e501500c200c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 326179136 1250 326177886 326177899
    0x2192c151c09020f0d030207050f0312041212030e2814010507120506060301030f14030a0504030c05090f1b0f1810050c0604080a03090204140403021207171e0315 71
    0x200b0007403074580318403c417140e01035005100150400d4203110502089410459041c4549001800010801002000a0700d62800f49204004070b600d007001c9601c1c0340c000e500c1c0c241420300142030340203100001c0b0088200c084401410400248000c000c2101c0b85800014104c00c801e450307413854078101500060300600e11a555682004c0c1005100c0040754010380341c030347d4020410401040412001842c6c0700030540656070300b2159051410446146134842e504080c040741000c24204140801590100000c120030b443d40b20092403d0a00041c904a00030940541003490b013400895902a10080e02d1407028800b10582d6520a03a400100413417542c440c0c400d104460260300c0382d0310148280d085c0c4650784094001032070161902e07a00d0300a640c2107171401004042c2e64a03c601d0140c0d43e1030103900c1d001d0a4211012090b4105410028100340c0700c4014955901010800c0340d00003182145042102c061642015496004001c0054802a59031652083c3e010000c4107022905c403090450f000c0d42002110388 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 326180386 1250 326179136 326179159
    0x105030120090415120203121c24030303020d05090a20010212040303080403090e010605090603040602070b01080303090d031b0809070902192c151c0902 67
    0x4040c00c0e5a80302901e5208440c0c03030100c0054010718030000d880340740e4006001044240c2e5451111800c1c1200303611881c001c84502000c030095050a015609940b20305000591500741c0024100d8a01100182001000c80c0e4903030b140000360320f044400c4501c12902d144d50608a85e0ba070704004002c0d4000104008a072850b0801080c842d200029201240340e900c049241040b01c10340548510b58050355071103d0560090501190401c08200010005180700f600c07030a4490a250600400001c205c1c0c000c820f40720340c102e005101c1c0075009804d445043c202141c07100e9032903941345040806401441401425100c042001041414010001c0c43c820454142142e0504d2403000048050f101c248400c1a0100308114082a44038882c859580c3d11000380300c204c9450700e984182100c101d80c0f00204840f10007418050948000b81d0220800f51030200045c1d029401c5c244144446c041b1220f1950140d22404044510707010207003840050710b4101c024400d44650b501080d400d03040c0641902982203114200d201c0f01d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 326181636 1250 326180386 326180389
    0x614030c06030103170c030408030706020307030c08070206011208251a04030905060703030b031b033a1b060b150715020313020406150905030a080a05090111010905150105 75
    0x2641c2c1200d170450741400300b440c44d11a111681368001d07061200d85000812000c134501070204020110f180c03003040d0040c0da0f4030b011140282140c00101d00c500410a401c0c0500c4030341c0c1e50000f0005d040d10104503d865540740a858990030901c580c40b150707100710002d01d101903d03103001e8024a101003401014030070005420f0303d440c0c2d007420000b21002030200c2c00c000401d1040c0d040c9940a01102c40c82401d000601c03450540c0081e14080e0b600e408064000d107070240481a070300f010720031035104105529407030308544000002c600316580403e00640e4041c1032401c010009500c148500711003001001c1e11117245d5a020708104c0d01900304032211500800320b42003c1150300d02440e003240c130002c0d0880c203001100c441413080702019502c06410100c82082c22074074000903035030718401c45005015410100c412103181460140c1110789a80c03240d0311039000001e8502c00710705500f0444505a501c2d00e0910741c1c4540c5080140e4242000d07111742000b56203400141d80400100041000741020107601e45015030382d070b440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 326182886 1250 326181636 326181649
    0x70815070f030b0409060504060515010c03020a121403010b0301080d2105090309041109042706180803070e091005030a0b0402122406030105070905130603060614030c 73
    0x941050000305007200044080384603038000c16880f04000c10116401c0c81585401055800a03241641c1d119682d005200c009e49410f034071103882d46d0003804c0c03082288e1070b96240a500c510300040054444980c6812400800340316611001940c0550b0710300396100d503110a030b00445904240992402481b6803c040c0282c14002c90300180c1019840d243c1800104400d000316015000290041645210a11051080e0780d243d0084c80c6540c141e00030600d44640c0420304200558180303d000d80050b03203031004c1c9560900805042e007032000750001804624010500c10811500d115140041c050020100034012601d0340301c0f4055103102811075111a0310f03260240d81354980030391841559070661020340486c000a001c000c007258018002802119942c828441960904941110b1005070019002501c06055036071603032242c02141c1075008014900d04018080c010b0f05207402800d00c01c035441c94581003501c0c5103401030f0f405542c1c45402400410343e5003c078031501040802050f8881d024001d518a614100070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 326184136 1250 326182886 326182891
    0x20105070c091113060207120213060905010602030711040c20030909041104050f061f0504030807030521040c03020105180406090e0d0201140c0918130611031005061812070815 77
    0x42300d03420b071039405603800c00c80032501c3c1c0c0f80c031400e45607221310303000030740580e240305050090455070003641e40e400c2245000401e5100741d01c0c80b28451464070991019680d40115001030501400804d1450742052581d19071070f5004001e01180d2001c1c004042200300000214410125241541d040c0002c0d1961061004603070000c56446421036640c0764006d55824001482020b03075451402d081c2c1c90103842e40c070343c030100303a00c0090305038040b175030010305034a10032042004120910740300c42e0114084d0074680c0c1ca507001c0302c40707601c0003904004022980c0302e4110243c2c40c0000d58154000c0040014560350141e10025100340700c004400c0c2d00031010103e070f50b517006014000b51242c0980c05070080f503442445c210300039000000859005440f1110880340d04043e00d14030340c041d124440103c1540350f450300c3c110003030b07039040211202614000e000703000170609c1420002e002c2ea0001c0b10301030344078508a40b861a6401c011100168014038041ca0020081c1c00030903c80c06480b6408255281103114184546032030005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 326185386 1250 326184136 326184149
    0x30705030d060f051f0509010c02060310240203040603092d0302010501080c0102070905042105040e13080d0c030e011a040c090f0b07030c0b090303060f0f010507020105070c091113060207 82
    0x340e6405c0001d02c0c4a50300425000350141446c050740116074002ca01f2940084842e06500c180491040c064080040529001583c1d01200403211ba210341070000c0d281d0007240b0401061507200d104140420070103050844099040742058400c0300c041e54145001024440030541c0507510b8100085031a030790200e0900509041178009200c1641f0b049010401810001c00a94500b0000d5886062402c08e007910610b014945503203240c0c0700d17401d10f450f580010300041d2181c1d620b1000c187c0d4080000d890403090356039412804500044c1c2c100881000d4028101612011009519101c200310358064030300040340e8841d0041d00c040101d038104a106484802d094010145048440b19041107246441c034010f101041c40b9103014800c0c600326030398001c103c410a4a58407551b8101004202040c1007003400046520701c1250012000b000c2040080d115100b48013002e41000000503290060010320a001c40c010009140c0c20085200fa4812200041e00540f441000e80240407138001442440015180c0c2550381c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 326186636 1250 326185386 326185429
    0x405070c030e191a0c0607050a0201060b07020d030e0a030203100f15080a08160203060a0c0f03050106080a0e330903041d0601020f0a0c0503100608070b0705030705030d060f05 77
    0xd1600c0b0781d42001004e04c0e40e80301c0c25010400d5440c541820b000c1c3c0760040791039842d41929020005030107825140d0540000f100c842051100c48091703510107108200740c0d0b405052041084141e28086801c0a14542002c5d42510620f0b810210110700d45d80603800400d24010200842220400e21241c07410f2035208225155000740000000301d01e00c0001042120100040303202c00b05007582c0840d003408030845081401e03654911011540d140c00441e00b200210151404200c01d604101020b00200009412001e840c1d6881c4204000d0602c10018180d034501c208840f0010604800104241101007181d0040f002d201c8101141d401b0200205032420781718407050385203500d070403400300440c0c100006000c0b5045100ba4580706821507400d02c440c0300b9450007900d81c5081c443c2420241481c20b84085113010645180240400002201245440a50f4007180c0007560f0b40c0e1941c108540703180a0064003420500001030000031170340307566000d2012900e80006103207a042d0798500b003084009006030150785054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 326187886 1250 326186636 326186639
    0x603150f0501141b010606080105030c011e2c0f01090e060d170a0804051e06041b031b0501020d03050103050303060d02130c0309050c0a1805070306050405070c030e19 73
    0x60052401008640550f9402c5040c0b50716206000e0440c06a007102e5496130b552000c0034806264040c0000d4003601c400e400070451001c51800090603000d144105105c5c0c16a00f11945800e50b10518448008401d180034850890b0030850145a440303152031000c0b44982c645000b88107881d402080000102ea014014250143d80d40794180301e091180100200c0e45a040b52150b00751030f03000c1c10042c03c0001e405580d280803914042c40c240c0d01c1c0085c3c1860750404245070000c030944040c030000342240d115a0012001d040302d50180300700c0d8050300003071300014588141c0f503032000112a403084c03148085500990846868402d0348500740c08880003800040c00580040002411604000b001070000320701c040d00700d4941c1c0d00186203050448000303960a41c0000d440704062018000c3c108041c0b104c114040b1620307040c00345880ca80e201440006020103e540c1d131030301c002441e014041e500080044c40090002e00c1589000d10005011007281402180420000a100021400e040740e070021540b040605022106 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 326189136 1250 326187886 326187889
    0x105100207090209030c0a0905091e0a0213140f04030206010e100e090f060a09140d0f0c05010b09072006010e180c030a0606030506070305041101110a020a030302070603150f05 77
    0x4c0d48103400c0d40390180314034101003606032200d00d1560020700d046100020141440e020f01400e2250681004a183c1e40d017808181c401400400c40360380c070550444440c445030756030281400107000c1206103803200c404d403e4200245030142c800894480c03403203582078410586c3c90b000da10323084890903038650020401c030600502801007822441500103008c0c000b26070501c074210004519001007101d50707021030f54803041000100700280c460004101d0100001e0082005c0c40a0000c14900303580c0c00071010013016514000c02d001c800c0d8000e201904018002544074500904041e20b01528040803d082109100d15100c0c036100c04140a03040e41c9240d0022165516000d5921550141c01c1d00d0000081c0034603544e001840c1e40411845a20354030494001c10200d140d41095410060001c10315010300d41000704200009041da18410070b005024244491510f29480e4043d140c00210240290000f002d0080030060540008900341143c041e550144110044189404141480340c403940c4e08840c1807500a00c40d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 326190386 1250 326189136 326189141
    0x90715050304200d141e06070305340f0c030806010503070207090e0607030b06120613020d020d05090705040902090423190b011d041211010207030201060905010510020709 75
    0x280003e01c0d100c101d0f1a5031030030010303810039003044c4129081504000e0010022105004d80406201030741ca240c00380701072a0025039100e041c010b00c02d40130140e0303900010703603031840a424405181114200d5104000c010314040b21002000d1280b00b80840c40450801c050720307100f09981c0c0c130f526a0540e9585115201d050041d2880e402c0601003400b503001301840800d25460034441c0d0a0728100b82c0c0d008100c1400d000c0c0340541181e80030f03045580180c20400c0502290100c020025412200558407021401070010010f4000d005810402252a00009001c0390208aa404c103900909a8205684086540d4820130044500524000f500039a00350001004106a4840c400d480049120001220681840b4446c28440c0021a61403800781c03440601003405100700c100740c090001001302a80007010249030444e8000c000340b0007400d80b000116440c02541c0300b05401501d03090300e00c000f0354440c0e800d0b18000e4042c1c03685000700100185008000100fa1410b076050003401505070b00030f0420181409d115101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 326191636 1250 326190386 326190413
    0x40507020f0f0c130509190221010203040b0901061d060414010b07140d050316020a021e040b0904020d02062101030b0702101a0d0203070302040501080303090715050304 74
    0x55005201d200181d1810900444103001e0102014014900d240400c2102e403840c5140c00400840c07400c001c028480c06c0014828003030704110f021610305210580300081e6442c81800904000301411682500d0014054001d5802544150f0000c1600da03502a0314500700c940900c120f458440c041c5420403400a241030005403c10400b4101040d03a860103200240514802e82c02040101000036030030703042c070004022100440241c080508545188c03400001d1460202a0041c940101e51700808400e1030300030800d80301d2455026110388507040d9085480148400f0b4481c0050096082046411140c83d03c0041c840c442c1d54024207040c0203070348c19028040c860704580c1300203c0d5081c05120040c0c00c684021b511500940c07061600006910b001c1100074244841007110410080c00c0c500c81c204428802040000306000c2528041030441c0790b800000d2a200103944080d401500d84400032446240200041d4801c06600007220750042d91014440103072845002c115001a02c24404500015141c405404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 326192886 1250 326191636 326191651
    0xc020f011206030c060e090a060f06080c0c0708060901060501180608041a0103061d0c0f062113120c0308010302040209060706020a02011a03030a0c110103090f050109060b0a080c0405 80
    0x1480c940703d58030840507131403640089000c10005110040c0600d840304841c0c1d40306910140501c10245080d8811842c4207030760044005001c1d195000407000400c03501656900400d6800700d490550b6980704903a1681e034180c1c2c1020643d42850700218295001d030314501d601082d00c11002d804580f82c40b904680c1a00c01070001c40301c64402021610400c003030044d0141c080e50107440000b6020500e0306803940b142c05d0070821007c0c250010401148151f40d000c481c00340415007076a40b10b55a0349200e902c25003c40000e01c80400070344118050101003079052007a60043ea12851000301802018501903800d1044828000d001030b100000520043c10150040c0c900b102c80500390760f0a0444039526441070307800204911005031f642c1c854100f82c2039600c1da002d00416405401642c40d00b92548401080d17400d901c0301c040e0294884180741c0f55203900c03035070080007100e821003e0418246101c1c50400d002e852145401d4402d24100080c02c3c4075450a00e03040000c50317262000030540d030881e020510014000040089 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 326194136 1250 326192886 326192891
    0x510020c090411090f0103020d170c070807031514181207140706030501051806030f2a010302040b0d1806060f030b0c030403020705011d1306060e010c020f0112 70
    0x400345440d4a100140150320a4400308150844207007030000b8902c00030070075900380d40b03031100400150305c400001e1149280c0003026181c020504420407900c80c810701d500b001c1d2074030400c440003420000103e0030005483c4a0301c110b203840041e1400d2442a40c00042020881540d100085840094942140024034030050103942c0001401c0c800d00d04c1d42e402505042c1c0b004038414043d100c5401c0140045406803200381010040b550414000c152024580500c030091000d00e41d0205040396010044801c2c5402110201d480501d921921101c010000154500d008007403070144139000e60103402035030241c4203000002030030b0030b04501010000d0022000420f00c4010080310101c0815604d009210191804080c1c03041068518a000c8601810080034104001424018400060360208802003240c600340780070b011001c550707070700000c4120480b80440d0f808480711400c2c0311180745903000300d000c4515689a00c2103540b0b6420041d642204468802580400e9186031101c01e50b00132540403140c0315403481c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 326195386 1250 326194136 326194153
    0xf0f16030f0f02030702011401060206131b032301060e190b040509070503070b27060c030c0106030b090607080f0c0d0e031306090b0304150209030a0c080f07080601051002 75
    0x80d072086a2103107900d100d0854000081100c03e40c5c0902510111005100080000358034242000b5141c1e200a00740080800b0072071030324010b004500c80c640c030850340400e00c2103040f07540c5d80c50b0602d19001c1c100310441c400c3c0941041c00b0b113081018400e15040350300c4009480000d0713880948c60b001c00c00d50304031000070013941e650103c0200e0701c503441403a11800c0403500800d1045e04100402d4504801603014110106040113010407a1840c0c3d1940320031402c845031861840c0001c1c100040d980c1c0140e0040d42c800703100c0820350280c1060150050313812030b8000d9802c11820b88410a031940c0f03a000c11291200400c0c007400c041140b01010291031a4030003080004030742050003220341001640c04446090080707a0011a0074900d51030a002030300c0c0101b005084c0140f400d850042e4150650100400152401c202c0c58014101c0d0300d0950104e5036103800c01020359020008034682075100941034096141c5522a815940008200010f0311005442d1080d000b000942e191008000342169003210801c11030058021 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 326196636 1250 326195386 326195411
    0xa0b0403110109050a03200705130b09040312050105010806010503180111072006071205070804030f1a06010305060a03020d050c03060403022107030e10031401120201080f0f1603 78
    0x160f010090b1003030000c0c0c802d101503810010a9906819a0280c0c0d02c01001d00d404101d034400240c0030111030055030548000201081030348010f204462a1941040381c24042200705903010190454540340341000300500d0341c039000119002c01c002c0b105a8007091040001c01c42c1c042100922404400e102000401c042c0c048114022040d013000ca002c584103a0b46682176501010041c2241101d9017040e60464104017141e19803041140401c403c11044c03040000d03115091115540840f009160460700c5c03141c1d4600e061900041e9403d040c1814566086004049822588a13024060155000074040f251003030441d000c1200301247c00104640b00c0c840d1441402c8552000d01080f4812802500645010400c0000f0100c040400720101d03440039004105950000e41c2101d82c0187c2c010b4203070b545141005680105800510f5074a0308600900505400014441700f25881c14610314800e0b40c407200716490318140480c0510741512100c100d02080d90014442000220010020010624010494031070f07405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 326197886 1250 326196636 326196641
    0x40b0402041104151b0201050f0c01060f03030e091006090b0d0608062d0405030d05090c15040504060b030103080a0e15040e04030e09040b07050d020d050f18030301080a0b04031101 79
    0x284045003a5603244c50031600140c208070b04071000c002c03810290350740560f241d0008002c0e1240c04001e0078140400b10f000c80e064402544076201602080035465400c41c0c89080141c004140007108031701c2151904005030140140c10203650072103105464800f2800d050042101e02c5420444601031429036603480065022001c10042d80103035082650b10040446180002207801d510000c104620301115090000060001086a4000703510250010325501c6000650f0b05000c0110300f101d0307020700c00b9243c00c0c10f25403000000340120f8500301c81c20806e0710751310011410103010900c006010814140100a01240641c001e15030640b802401044c210f40c0a03070340000c10750015000b41d48860081c50810080680208902c0c40007407089a07119010b14107035903441d084c402d009180c40300304000810005d00d62181034040da60392400400d810310861800c0b070410307042c0c0c160440d850710086d141d0104c3c07041d00b00c0011084038162481000682241d07905a01c0b0401c100c04007400c11020843c15070006403d6200a2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 326199136 1250 326197886 326197889
    0x606090301320f010e07050a0c050f16050103060b22051f0219020f010c080d14100501050703052508040306050403021b1e0d08220b030708040b0402041104 68
    0x100003542c2205980710342446000c5000b0141000d00348031000500980020654440e84607055291042c0d035141d1000e41207803c0c80200800a0251251002d541c8081c4000300361076010814554403401e4641c1c4e01d80044040d6545882400d14083d030410255880d1f0300003405403041c5020019800c620315655401249485404590800380c000b0001174418409a05000c40b030710103c00400d1081c0a101203400080c20444d10891043c140000a204002004103900a0301d205401040d02002100c04494014892180441e00120181540031010a0a40c060304c1900c68140e01981e5480c100748044142038902000d078044030700c411450034042d9000440040c02000554450100801d036410a03140191a0000d804180d4903080c1e2001c1608500744c841c40c01d041c0c10324030303104180d010b065001404580282c4a2000207040c1078000902d0303107000f01c400c0441d0340c002410280d0000b1071581d100c00c0001d01c3c2c04140c901d6070010344400082408503040d2040150410300040000801c40020002402c00340e215 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 326200386 1250 326199136 326199191
    0x50a171518010b04110d0902041d0c0109050916080a09150c0e0a0e070c030512100518090d050708090306070906030b03010e100207230604020a1502060606090301 71
    0x40e40004007280081c02040c803a00e000ba1028820b025804490201a0045020b800d4200e036480211100390360365604403110b1040d0083d0b00c1d4049034400d1030204e458030a822901070201b1414100000c807420a98800c03403086e07080039001e014042003140704031812003029104040d1540c6440051001c00d01403029842c000300444400900181010f5010f807800844841c182c2c40398002d40820042172141091255110500c0d283c405480c2115240c1555503004041500e80004219407c020b94050054150415624102c425211034100448214603280d0100e42580064100390040c1140714001c4010300340c2a445030011074100020403002c0ba02e001c1007100e07520001880c581e410003c2c0c030b42511508034811021343c024881e8400b0f8565165460381034038840c5a0322680042c0380c405000403040081640703455000381c03456580c14055082e582d81c1058074107034031640070a0740000d030407500601c00b12030407070300394018004a079103400c00c2104903003000301199010354036001d1700120401d51541c80c8444002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 326201636 1250 326200386 326200411
    0xa1502031006080702070504020c1014010906170a030f09080307050c040f0603050a020d03140c010c020c090402010f0c06022b0c0323090705150901080907050a1715 72
    0x200000001e004509560180e0309200c640e42c14060810382c0450000140da0042d01d025a44400a00d021403030903111324040c036006403030181c007001c41100003190f950407107040b82001d10142d500d42d0700b14038a401c0c03c084103d01c554045100140080c6c00f50304c01c440c680c7c8090919403422640c075001d04c0d00b56444000c007140c0f103030042402028640b5041c07243c0a00e100c1261030810001d81180c1d10b02d0703920b011044020744118409803108040500c00c40c0c3c280300001e645c10303845440f180c948080c01c0c0a05200c842c808050b000340c85011829003860500148582d0f016990702551081081c000d41d5000c05000c02030b16603603001c2111040071210010350700301344882c1580e01c40b207400080e4402e001301d4520303034450f40800d42010701122001d440d10302403a0022190101c4100540c540c1c401c86031410585030b1109400910170000c403540b52850070041c100404080c2c8948805070b40350708450762551180d014042c0c1c0708140d00d40921400c0385d040100c000c6050080104d40b102070440140c0036540b11b00307c51b0b0b242c00300f1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 326202886 1250 326201636 326201641
    0x905090307062a03180807050601090b04090c0501120b04020408070e180706140c0a030507061a152505030301051e01020303011a0d090b060a120f0f0201020a150203 72
    0x1580c8500740003038602c040781d020b2680c224020310301060f000403140c0040644a0300b00d4041d20ba8010060090b840d8003620555540845e45030440c1c0fa82003d101e405800b520b0400c0400240c1040d01031054116480401d0030300c19420a401540e01030420020015041d544410405840e1210701c0208045c1c2040d40062808600d803140911080500810300d80300300102c00b004410449002601805440050038154901c68002803c40f5650198440b04030040c49286850000d2540160023000341074010403085c403000221083d04185500391030206a0440304007200700a9144040c2c0c05410f066a001c49a20218044005401448a0b803c003050303070a900000010400c0340384c00141d80d1040000c04010708500078100c00081e490f40014030520107002c4501c146402d030010340c4000c84019132401072041002c1c0450b824440c08410341259018020410b14801064002c000e8074003c2840d544642c55140c0752025a8030f0100c42c2c0e21200c4107d040d480380c50301d0300b4001a8082c403540c000e400889401a12813 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 326204136 1250 326202886 326202893
    0xc05070e04170d09062a0e030705011b120f0e0102010b0d030e06091201020307030b010c260c030c0c040b010302040b1c060e010e0708070c030e0d03090506070303140105040c050714070905090307 85
    0x2582e509603054240134a804047d04591404100101190400d0a11148450306080007801440e203000d801400350890b1007494032126000038402d98004280c0e5104842101140010381c2241c11135004154010100101170000900c1340c001c07040d40c10b44c0582a5800e288144000c22a0b202d1141805111a5000310411908540c54407d40540d88424038202126005549904c5c580404510240300420903124000311007a105c10116007614403440116a544c103688030f252a00d600f000b11a0511030b90808c050300a20703603ca80280c030305880c0c0c2c14035560b180251440c2800510640404a00015500c8202c0040d900307a110071624020285c0e514150034600e4a4440100780c201c000b00306c03105005540c0d5403000441da00c500302034603800065030103020010321810184c80169082d48091750051b4000342c890b04150781a00481d04480412030401010b0762500c04200c252050b91200d8800104203000800208140f00c081039820030f0741c0300c2603400d0303141c591980c081501c7c0111508c5002c0da00008010081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 326205386 1250 326204136 326204201
    0xf14030d0c0801030515130f020121051911091201060806090303100b0f03060609040e12091302090102060619030c0909050f0a2315070c05070e04170d0906 68
    0x755401c00681056500d001c610751503800c0c7c561130020342a0000100d524007164082c18036100300101d5600204c0c240001c8039600d41c003034181107a00c1003183d1140091400d01c0c0205010742440f000c03169192030704101244d406d2200e465031582c4592290f64a90000242004080c05010b01401d221005142d0b01e01c1e100014049626640d4001032405000300501c80f103503188c803801d85c1e070054011100c0d00d076690120300c00680a0100a948000c0a01a1040c25a0003083c144010042103106594644401a0020464089005044e012809604410001195031030150b003501c16080180d40c400f080c458403901d80304490080b1740c20000003107607a0b50400c01405010841504400461801803501c2003403030b40d483c10340e030341100f4070218842d01e912041203011000b4001051801c1c90415070074080d14003140020300860410030180c5403406650300119110803207446244c41950000049891002041c082d03401075401f00b8503440c06140c1e81c2d0078081c0010030310301481802510720f82c004107460804000b40b096 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 326206636 1250 326205386 326205403
    0x3050702062a07020112060807140904021c03022a15090a051e0d08090f0a080304030f030504081c02010510210501061a040f120f14030d0c08010305 65
    0x10403680b0b441284a0141c03102280c1008282c0707042583c581c4a90710050390080d402d80386802041c2e04007100481c003500d00007814421200c104c0c010b2580d203002e110500c051b003d000d940194000b8070b18425506004007000c2101102031091040ba07070703481e48507441040503031003021984051411a5110b00507504d4400d4101044500e4503444030f2405031120005105001e00744a114040d002040000446940311300e005005404060006031111100c0c1c40c0000050380300c0920207110701300e100640303006401c05c030030703000c099580d01001545032a06588480c040103142890880170004100b00200e49074806014000c0c00d642508488503c445881d140607007583d500501400b40444054020004100c8a02490700342e00028103e011b254840c40c28002e01501498201e050301c441414031503000205032000030400c80d05d0f941d402d02e0300f164451301400140041050f001d44000d5951000704003241d0407141c040c011620800c1100c0c502007900340000252000800b032500031031043e07401003003440f40900180d003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 326207886 1250 326206636 326206651
    0x309061202040e0601030507030e070305030301180207020603010603020c0c10021e01020f091c0204110403050c090613050a0b150c06160912050c0901030f140d200a0804060305070206 80
    0x10308050801420500c18a401011517040645031404603120714026844903d4451004040d41e50450320303070602994903442807140e00b003600024410105130325120b2098482e0207900a0465107181d203400000ca019421400c03035040c20b8004c03c4490b48455699402038035010103907401a00103900403102400340240a20681c140c541d004001c55152a1000d40407100c512600302c1d00e503402c10610034844060040e02241c000d4102d407800b0146200c944041e00507204680c1b09204440034900d60700b080c014400c1050710040d800c030002c0d01480112a101c0d420482d80003084002c0050241104c20000d00c103094000a40ca0030150f00050071603202c20184149580410010072980c401d4241c0c0800070a03140d040d2041030b9004040105c9141080814008001c03c400000c000005a503128202740200c40c6442d40111115202c41d244006032050100304201c4506e4507407140510006c00d580703441d800610b14000d801550054141d1080001c1e050b02c0900040e000680d4000390514000c0720203860542e0150150703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 326209136 1250 326207886 326207891
    0x909180b010501180e010e06100f0804020454080a0f02120301081c020a030e100309020301090b04330f0b3705060d050414070303090612 60
    0x1280494250416181120420300e030209580d1080c4616801c03220701d54111200201515000207005000c48991700d01071031044400d00d03850b00751101d05440802c40043c0140101e10fa003c00a405480c1c40d130701030a031400c03c00e00000907150100b90151030540301ca4801032904c48080c090304911401d075114200101c044003a01442504041c0c98800243c011040302008104074034404080c0d50b4424481c000480c4250700d03c0f542ca0f5615118007544800007031103036401d50817255850300811071000404081c1030b81c1584541040c02c04000510958000090791107003419110510040143c13000d20610b60150b007d40010152801c042c40c000c003100a076040e2621013406809800d0b015610008407040e141001c0c070800040074110030030340c03001030b00e141107130250301903821419403050140c80105031100150480ca50161046c151310441d9920106000b01e9420600520490756070310555444260030600501180e2404607402c407659140502503001100040c0000304100440d5401200e202c014a0074503000303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 326210386 1250 326209136 326209181
    0xc0303090816120203030c120702101e032a110c0a061403040302190f1b0b090904081e04060305010503060708040f110405011502060603150f0c04150909 67
    0x42c4005546402a00c81c10080480c1040440d903040085611070388445080d40e039566802d134508261a00180300586c045d06028100c1100184140d999045100c20200525940b00b10b0303900441c02800d4030610308803400030440e111803200944c488039002042c1603661790425000b0010080b410007004008450003414101003c1c80354a401450056240082d612920703101c0c1c2d00d03070404030724140398280304261118010140d5024401d0150344042840d000c1d2120700b81400700d050203404000354510580813496810f1211560034a40b271803000d5001405000140e04003500040807604800c00f10f01e0311031404600040803c2515054050680103000450242c04646000c01c1d0107413040300000d2004004a009151510402030701070042e080150021340208220345e11600602d40b521f6a94100700054410b071000210756141c0050141c10951103441340c0c80700750312001010011404068044040308905200208007284400340c2c1c940e83c00420b07075070601c0d01890305104808803441050084035411550f81c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 326211636 1250 326210386 326210413
    0x1201240801090c0b0c01090803070c30120609061d0109060b1621110f030705151b0a020c09060415050105090103270209071133040c03030908 62
    0xf82c2d00c08560b842400e40769034166a00c010340c01031403203010040003003d000c014072404580c0941e00c40f018903c40c0b02100c140d80e50352400e012900034038060001484060141d01600c0e91b200b151284c0d031285000e031011641030346425803003080c1c60854100d40414500d031402c44d003a041a007500c103801891041e030700300411414480b000c403241c4a050042060000300710454404c2200300350401a01f140d0305000c1d00c0300c8003d00c083c000c141c1c3e61106030108040c801c5507900f0440140110446001907440001410310b0b044401041c4c1c0135407001400350746080e00c0014205003842461000300946050703175010b420328200c030000300400100c02a0503075019078500306d94900c00c0e805007541001503603004d00b45070340c45548000c0101c1c050b142c1d54841e06100f441c415141e0603018251201880300074400c640440391030f5280c030821110102010f5900b52181d0041c4820007001c40c02011102403418801c00300d40e01081e1b0041d05064000058500b1a4201e00b41c01c0b04100f49036100050101402c07900018000107007040c072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 326212886 1250 326211636 326211653
    0x180305030d05240618130905060c0a0c060e0f0601081507030e0c041e0612020306070c021c03090306020406080f1f060e0406030606031203140601090311120124080109 73
    0x4408a008400004118209045c4665a4100c0000c0101203298021042e041d140292560b681c01302c4440c400c0901082c03030300000c40f050f102410100d070385054040e44130703840b0a00500000c0950302c0190141140b0a040c3c030070309002081c080c02580c001090f0085c8034136090500000300030402400c040c42c10384044091540880c2499404904803404079852000481c441c0b1080aa4012a090305103054400038020054200d80c04055001314103642040d6550607040d100704c141d9000013580040495140d81e47c901c20340150104450003441e1030721030240c40350348007412a841500800c0100c1c595104103d060076403980500d07405400c014116103205a685100c5024880e02d02030f901c03d20082040f414400d8031543d1060000315080041484500d95034244044025032070b02d20100040d0605074502e103117844610f085409080c041e5546031081d85035855030000b41544524035503000d21030002c1c5581544090007507909002020a0303604800126140000c051400b40d0300803101a4101114a00421300f0f10307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 326214136 1250 326212886 326212951
    0x90603050a0b060307091d100312020a051609201b010e120309060f0f04020d14100c26010b07030903080a0203030a050f0f07030b01180305030d05 64
    0x90401003400d4941c160850042d0600e40400b40c1c1210340801085007082e80a106030f012184000906003115440c6e5010668100e001ca40f20300012004c0c0d03c1c1080082c0300c00d807034011424020300c15a1003400701075881030b0802d4240d0f80c03003039079101d1031450a00421105100d00c00041c3c07003280300d04011614119602840e4000c400300580010201c104042444c482900071f0391011040d02c0039503014001c580060000c0e13400a031550aa64071a032000504404491803015004040c40814400981c6d215420402c4190800307504840c414801c3d13480d503001640c2004141c55510810f0b10126103864061030091003c200c0d54122041020320a07000031513815617000302d0b81501e800281c010f955900c1803d066840c0c1d030036030340000c0814000082c000d40c1e141d8080b02460003405413040610443d21048000d084280051784c2212041c0407080100702018003075071024840d24818108070b02e0403207030782e01d003030700c40b000154019a460342000403031030110f4209118a0354810f449117030344801580b486540c2490722661 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 326215386 1250 326214136 326214149
    0x170a0504051506010309021206100e0403050d020d090f0b0114011724030f071e030206181302040609031104050f070e060f300603120f040503072304060609 68
    0x101c00031401c3c0340d01c2a0403500f90140c0107041182c052000a00403962010115090800c1e00c1d08a040850401c0803002e40a00545d09540d031030b800c004040390460020f6100d0141d6110495640407103000180401765100202c1e40596110105585060840d0b0410b8214812030390408c42c1840442c028000c901c4051900051950030741c04411108018070404c4000080405034103201c0c101100205820004400d015110f2020b80a024140035000d01051280f141c04000c2d400102400744036014483d40352525111034008080c0b4001d00544018207040380c5c041d411000008107042e0040c024042c850449108541003501c08101d80d01d00074556000307220001d00700501b0086605500045a07540c80300b61081900d0b59000e01d9542d07103017810b000380c0841804c01480c0780d50b100800c46080c205007149855104507000340145c405207001100086041d072280306d244d6080f00c030510000c64262000c012400290504148401c10b691841c518008541340700b050480c4078500700ba40c18030000d9801010035084034003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 326216636 1250 326215386 326215423
    0x305010605040915051519050f18030127060b0f0604151101020a1d030a050705120a0c0602030909010f0503030a030504030302070f0507090c080c0301051c0b07170a050405 75
    0x541410140800900b940540d80c00040b0028028424103104010302c1c4030700704480e0000d00d4002c00c0d041a038007270140f015002145002072103091001400c40114040f41080200009803014124643c40150100044800d03c440d0341e6010040030001a4411810000c0080398401c48040654001443c54840c1d401100d22200d58040e41c031b040d41c1c0c040d080703d11948520348025034403011104401010781e0320b4001d002c1c1c08c0808541043c0d841b400c1c089403680075190000007802c4024180418409010304901c2c000c00340744a01814800800e80605002c0042c00e85580a1a5180f910100704007001d0410b0b00501d000303121041040000e5034000044a030b2040081c00c003c6036a076510b0500364020300948001800c2a10084105001c01201207007540544040c0c0f20104150310004108649003442181c0051081800300300601c40d624080000c030407010f0710364688541a16141d1741d110307054401542c400c0040f520b21011000d199086c03440c00365101c4401c11003008540b500c0d44405503680040c050300071821f00e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 326217886 1250 326216636 326216651
    0x2060a090f140d030b01110d0e03120f0702040c0e0901170c1201050a0b0616030806010306211403091c050f07090203010503150f190e03210603120301030b100f1502010c03050106050409 81
    0x1101400181c80c80c1c2003005e150307521a00301ccc0790b618560754800c00040f4410362510701c40401c2c141c0a0401c080c61008081c1840361583e0030703c41b600b2525481110611198400e24404480d56521803030307030300082e8178104008141800e002c8200030503900000d01301c40c40341005000c1400015a9211200300081e09480c042d115a214400141e008102c6a0440b03c14462114042892002041915208540b0660b00c1a4448400340c84d00c0c1c0d124025000510340c0410409090481c0c105c40c2084421258022800d8440c3c101420345c8451500c0d038250700540115401100400c1246000c1c400700290310200345907010305243c988544c0303400020080004c18002d4040740043c04c0300c0b100358400c2e080b0f81031002c00c413a80d0b0741030309101801d100018800b00d05000400c0c00000c1e414100812801c1004040407102800c0d642190f540c0c1d24402c000403c10b0100f295500d40004030640100140e100925121440c02000f2038100c100034252404200384006246c24040104846070303001040304c04030303100002c0002d20350 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 326219136 1250 326217886 326217889
    0x5010c030503060d06090b040203070504020c121b030313051204141012060f030b0a0c020d0c1e0b1602070501120914030a050408150702060a090f140d030b01110d0e 72
    0x40741342c003e80054a050388500810140c40382aa01450013281200c1c2951358410400080e80300d42c0c0310b02401c680018002c203580c010404060001c00d06580c03000d01d030714558003002d0f501c1c42d0400ca90612005844555110a1180a200520081c115074140d50328190030076540c01154059014854041d45031100d00c0b41826125550a080c1a084440180085070355621954004c4070540001ea5580340c212000c6803032040c20740300d09960000c02c0c3e00504a56a200d017402c0d668000d070f4041c240c8242c109080e082c070650b44181c0000100038401c8480c031700c69003489003502d0740c15002640c41d5402d40d4807054080c4116a00944c51100345d00c050300c40070612410320b1810301d51102440d09011140c0c40085505001c083e000000b81065a0618048030550455100959103400080e01c1500147e00701c0c0c03021503030300c0350030340c00c10004180070791020181c0c203d250b52140020f9003082e007420800c0d0001181200c0c519494001d10a1200d0f02f46800b84000d04402c1420751540742c000740302028000c0010300c12459 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 326220386 1250 326219136 326219149
    0xa080a020f150d0e060a0606030212060108060a03140d1209020f0f040f06141507030f0e041e0c080a1109040e0705030d0306090c0c110f01120c030e060f0105010c03050306 75
    0x91110b415802d0141c0c1404e4542c0580d035200c20f40d03090100ca81089804200b0a210b4400d80b5112144a40d0540c20740d02c601005590038500540090303007244034981c0101c04211041e11070341c1c0ca04040c8004001072152104000c01c49220203604e0800c003420b02014001503500c13031105500c0c00304201c03008905021402c0004005114441480a4a41c184203001501c60204040c4603641d5405807043e00d041691106034041034070800000a021403291030350550441d11460fa000701403000a40700040c1c0819440a3f0481044040fa0401846032182418403403035520202ca80c2e00007010513418066140380c8140c40101e070181d00852805a0755592103107081c1e0000300072460003000040e09481c0f450074110b03c01000352007280a500c206a0402e07451072035461081c80e225401640200c0b810102d0403041c42042501d048064205042040310060032003074440900c29603112590342d45000a0346540321b0301543c104440200030070610b0f9200b200412559070030002d42c04900340d040c0b8209940359242c2000550 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 326221636 1250 326220386 326220397
    0x12050c1e12060115030219050c030d021603120e07030f0503280908030a09050409020f1c0c091a0907031e0207140d09051201090b090c0a080a020f15 65
    0x2800032481d8410154003030007103440c9059803020000c50b076024040d0072003502070344201e04981c07040440010091100301e1042001e0415058400190782c5032140c203408103c140c0e00000d0780480c3c000005000780341010b40180301c2403140d20304928140b1120b4000d6548071384035801480003400d02c1c0c0704030b8060070030060b0a00480d9034500c507614504040c4064091034aa00198100340c44002c10000a0042104180001910384c0580255200300043c1d0502c0e00b03010107082c04040407600490b40c403c180f0a1513175281344e00b601000015500004000b0306003015240c00b002603015028403840e1064511001104c18151048008180d41d95a815100c18178124020310b87c621882040795034407401c0c04514401c5400411441d4040d4110310b0300c03034500c103a61580300c074184030403000806c1201008020340d0a0054004071420a64000000c19103107a40b24100d1080c0d0464964031a500105510121807520850318405041018000d00040c4d851f54089861405000e0619101e20305001144002c2ca0a4904899 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 326222886 1250 326221636 326221639
    0x50d02040605030117070f031101020f0607030f1404080412020a1d070e090603060609220f05121804020318150103020108160c1106070c080601060912050c1e 69
    0x190360300d503074410040158000b809040000d062500b0f403811242000501c200070b458020503c80c142c1d901d117541d208100c0e100c0c10b19060540c054102c0700b0340020400d00c502403061031241c07400b0420200340c2c03407520200d0b0711655440900081e400203120104100c0c00581d810743e90700c1900e411503c115400010600035a6520404a010311800e4004446021010b0380e13004000ea0340300c20f03d0340483d500810601c2401103d440d0740513030200000802515240c5080d5070041c000c0c4e811a00007400004034005903214914003911300790320341c50f03401c01044010004264000d02841206041c83c4150203000300d03402000450303520031342c0c010010072000e00d02c2c20b00d0400202481c3c0b041b209490501c03080e02002d81c0c8240300590114002c1e40010342c0010200700e42c048801825a0740da04c08600503a540311741480356200d5075030001014808480000d03000c3c0094009455640003c12041d854006c000341051001d8000380052070301015298001600000c80702030a07001290b04070308400d030b15040b14080b41004e90405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 326224136 1250 326222886 326222891
    0xb0702030c060a020d1701060c02010c150c05040f08120a0c110a0306140708060312130b130821090402031b0313020102070504051e0c040b042706030b06060901050d 72
    0x14102e031380001d9401c250350a1381d1940354100d9104054583d07102c009104890105c0c14501071440150700c2035100d0012075204000017080d05010b02541400c407600705aa050104800040606c02d68a41c51a04401031804000034080420300a46491240c09120761002c1030200354003060040120550512504880c0548074035016a070341e003400809000c10800e10200c508041c40802c0f2030b244a08a260b105500c041c000307248031049180c011506501c03668031541d12100c2c0444c0031510301e405800500324184290059088203040c880130a04100c0300c0501ca0011030101c1c03a0400c403d12940054880c08c0108480c0103803a0340d107504c52640a03450f01c02900a0080c000410072580e107807080111103086000780c1c2168190390300d40003030004452041c0e50501e2100801c0c498a602035001904480c0d2160300c2c00e82c940c0c10305a4800d00014140c02c5500715400103c8a01c140e503a46010b541e4180e00e038550112024003649141d51a40710702c4403030140102c1e000e0040000c007007800e40d000754103d80c43e441c07068004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326225386 1250 326224136 326224147
    0x1516051005070e01020d02030412080702061602120a050a030c05010e120408070503030f03370b01031802010c0605070c022121090f040b03060411011412010b0702030c06 74
    0x56800030142156094080f4509107050b01c0e06510000c0c0109015007543c004514140c14150380100059810004403403803a0b04208800c0103807580005060314080704413030310190003142d10400034480407104040030b181d0300880c5290b02003403002504002958060800481e181d04d14182540034188a01031140700c1e103d082000089558084010401c48080d80c00b82c0f80d90b251034604042e124800c8400043d4031a07030600c080b440b00e811540704c010311102010041e0441031801d000c4244001e403490300d401203141e0b0343d42082c50a542c0600403204540207403424110300c103100da4000380503180206806012655503500003450719010304941e642658008080700c0d10100d01c04a800e1142c810580c80c210a80511490301c2c0d01a03076113100c1d0301c0320307010a9402c441c14002018107104004104208844d8441e460700d010519640301800128003c90203098031032a080700d80000134044818090821107100c40401042105406c040d440340c2c151101290034954840c139600009142c40d005040d80da521400c000345 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 326226636 1250 326225386 326225413
    0xa050f070b040b090d0906021f06120c09051608042a03061506031112040c050d060203101703040614040803041805060f150304020a0f09020417030702151605 69
    0xf401d6100e03030004012941402d4080108403281000e40c8580720160f07012181e50500c80081e00340d4880c0b01204070300c0009003d0707034030300206000e554003101c03daa6081407400300344035a404902444d6404074031003d82e040d0210030440300405032400148090013144d000c5160368040d41c00b1208109a802f40501c55080f01c5849040c540024640482c4290398000ea413400002c186020340100c1c46483d02511082d800e02010542e16501380074024800c0310b000065040100d2156580c1c40d140c100103010b8140180c4910b040860941c00c01c1090300017050003184482c04070342002c00001118142c07031003882c05244c00c502c9640a44003601440e0800036032400046008240885e50441c9070f00100c900c10320038000358941c101880a41c010051486070044501020011021060401541c1082c400380440ca0b000d9912591041004601d03040007211540000702000b00c00301044d517201134580004050b51504145500085240399030b50b1400d101148082400b01506c007000490401c40cd41080a4964003450f859 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 326227886 1250 326226636 326226653
    0x5061804140717090a02030c12162303060103150e0307021f080c0f03070509030c03420601030e100e070e0c07050c090901020c030d0213080a05030a050f070b04 70
    0x400416540003c1c0c00554413038000140460b8094002c1c014000c1281600c06020360b80075020b44513407182c4076850401e800e44812800da2001001000404981380209800c0d154a20601141300341c400e034410001030000c40c4007841d007421041014107000611501c02d4105508500075090069448591441a20a5510380c4e010100110701c1a64404010703560744441e01d0380038001e100c4c11420003882800025480d5000703800401c4825801800c8a03489040500041d18120124001011031844111000ca486001120000c101d4240c2c00c07202500b10700112440000f603c00820050406850304001100c2031800d01109545884005042c0300440071800c2050369441e580c418408a07401c4240002d00c5a48802d00303454007241e0000140c52007030716982c104038000c000070784000c1c0555801c01c07042c10442401c0004000d4400d10080250f2541001020040e2801003980020310980041e900200068004012900480501d0034641e0f254514145020601e020b0744100510346901802032000340003494 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 326229136 1250 326227886 326227907
    0x20a020901091a030a050303041514091513030219030c1e0203101802090403091211090106050a05190302090d03080a1a102102040627050618041407 65
    0x71110724186402c1d40e0134180d40748250180506190400c0c008200011500d00a0005d91080e404000c0380c410f540d510b9000103814140c400c03040035400501d520140c024014034403a4030450002c0c000050386e5031600c0c080c0d00d0303a8040c0401003050907108444c50415009205000800d500281e4a1005c0a02160b001a012051039800d0b07100703101d002d0041d200c140c02030280348400000180c08484551180d801c0c41941c0a018004400f0b10004d5074022400b105444c19000c0e07110700540319074080342c13150414071000d8103040e0882001c01c0410407d945a442d000801c44485072080102080ca1000d0120100c1c024050b030707242182d025102001d21000c0c194807400c40c600820b50305008005007076406002c0c01c421030700f846549130400c0076007802e01082c5e0b01404890780a2001c5d00c00300ca0221201e030200300c0c102e81c0150401808100e0401031022105443c49110480410001860980301d061800141650007001c4164402d07800c2d118080c03845841d00c1d044440746981d280c03210700c1c60f801c004002510800340c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 326230386 1250 326229136 326229161
    0xb03010b0c0f07030f110102010b040e07050f0a050607120207050618010215012301110601061701320d0210030606030f05012904031a0f0108012901020a02090109 71
    0xc2c021a20508030001c58035404481c1c1c8000210401c4400791b4481151048041800f030540d543ca84015081d91154020701d180803c0d02c502070a805c1d4200800c0103044804000514080c8003121000c4c420354582104541010341c211007188010703c0d0016040303150880607048075401000100b4511144080f43c0c1ca401498035003602a1070b070a84200001a650407402d2296004940f921000502c4840e103041003001b5802041c9002400c030380107505100c1c03401c0002c5e440138000a8407000d103130401d1200c00c5041800340c12000c0c005081406503403400b035803140d540402c007600c0048800200d201991084041c11000764060113008200100100c090010b0955200b00d4012031b0922050952180307492003018140ea028461540040c0350394941d402030880a480701c034845110811000c030203e583c0303a0780c901021040b544942c9880c035280d000c48503000c5041c0c1c064402030781040d54103504900503d0040c0403003850552101c00c1c140078400100d2030000710b480040c5d003000c521000800c104445410030b8464100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 326231636 1250 326230386 326230393
    0x51c030f050f04150e250f080a15050c071202011a150d05100b120702010b0406080a02090702031c2906070602090d0209091e07050114130b03010b0c 65
    0x258490b0300c104442c4202d82c0140407180a41381529088001c3e4010f00500519000700c038243d0702d1150400454160000040a580300060001c11411800a8801c00074008607000b519200e410390b51809404c4c540c4441000c081b584030400102c403840c1c4d5400361170a0b5031b0041185070000c1e0a143c000380c020401c002c0a402403c440c41800c0c40c07a4144207091540901b20740901070310317020924038504007c210140c1800c00c4003071120320000c0d00384500c5c00580780001d04035401e0344503814000406400c4030101d00355640240c0c01cac060100a040000700d180c09209805807211122a55002e904900b14030485403107480c5005030500171206641281d001031500860301900300b120349001109421502e002c0038080f035200313408104a02c0080c15540161011072070180c0b40c44000107007640001c250305000c61302c07480c8075031001c1049403081c40c10524155a004012000d40402418040001c018603484030201c1c1ca0041d0001d03810104801c00004034000f810422131160b107030b5071110110340c4141e1011440b0a080d12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 326232886 1250 326231636 326231641
    0x705030907150c110a050d050d0906080c09010f0e0301050901060303120213120309050312210f060409080c0f030909010b130303030b0415090e280609051c030f05 71
    0x1200940c20200302d1805496000380c40910355218840d520f040c0322099008060700800240e180c40d480b0880c1006407060010b05036443c00b01c02d0044c14120554828070400c1004001d201040c503816017210740c80782003840c00420003140d609094a007505801c00c12030f0076628110400400c504103612003800c1d24460b58408020b500d40c0c0100740f0a07401400443c0019012440c0100501c24000c1140f0348054030a00704100300d00d0382c46000034241940240003040590b40041c5406440120500b408460211000c0e62059401c00501c40540d000005040c9409241d031400410203100201d010358a40381044170440350f224206401ea01d8890f000352820500801c01c140000c01e00d00500320948840141c041158441549907860403405480d00d481c446400c150380303080c50b001c00104896050041c4c2000751380400c201100fa44010300d0003082a050301c030b0821804100c910703c840083c8403034032601c2d00010003081400142c280079085c003418030441c5648001e070041c0b804416070103401840c1b1400e00b5101c01c001b00d6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 326234136 1250 326232886 326232899
    0x61409030a0e120303270303070206270d03021608040305070503010b060a020c0d230c010906020c0901030206180303270405010e0a05041106040305251a210705030907 73
    0x510f4512100c00700c0350030520011344c8000351888030003001414000b44801c0210584003090071070f80706580d9040103030000300410181c0d03248803003803c4003000264289035684642c0a406034403061109400010960001200c4440415026050521031341040266540c2c40d03480c90300c0d40d030705c0b0702500ca101e00a50800c0c1d2594240d241040c02e42d00912200c3d005803000c00201d88c00c1244910300e4520440390190500121a2410f03d0300d03908452802c0c040b0014695415110009094690154001021544142c429604a80368010024112a81905c1860302c0380c14840f0300c2c0300c10301611031b4040e40511000c100342500502204803078100e000702c40d0502089880742e20520054880034099503c420307451001103080c0b0070380c130b900c0158007d01030300868440040c0900040e905034002c0c2c1c07040d00e280d480070040020600110030780c0d03c1d07043c1a0300138a1400510300710310024a01110b103014800810081244d032a003481130040010041c1e000c5122128a161004028100390003c1d46c0241c7e041c030403103001050a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 326235386 1250 326234136 326234149
    0x50a0e1012020a0b03040302120d0911040e03120a0f0516090b130608060d050d090317090f120f0a03030501031b0810021324020d050a051204061409030a0e 68
    0x10990040c052003861810502200003585c0b0180041b030440c4294078070000c0c2014804041c00d2044c105502c0450304400600744101d28201d1186554030440c0b038481e611000810000440333a07010130300100ca60256076039a1008008082032000d1200b41801c110401c8070400c0384000c2c074128510251540e07105039488280070101c0e406000e03e00f212301c0f07801070028412a40640e100340c0e840340303005212690f5011a56503407420b102c40603460102007110b1070000c1c4200f10091402c024200d542980c201d080c800300c07800207141c1206003524079014001aa08001da01c88046c0804840c49410700115002d002d03da19000b4002c020901c02598003040801c03002c1031a059000072103049403031260042441c05d000804007002503103c0181401c0d0810384150000300c8001c2080c480103451018200030b650034402201c060300301035030080c1c8030081010800ca90100150481c003510007152401c02c4551065456140c440e0060060608188580d49100d0400000320000001032031242d091b035441684510340d1400348440b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 326236636 1250 326235386 326235419
    0x90a0603090506061c0f0c08010f140c092707120c0e04020c010b04050a02030405071e2c0a09060c0507020a05100302070f050106031709090a0c020106050a0e10 70
    0x50704a000403510b00d2401c1d440041c50100c8401c80340380902c0c102d940d03411003e00c205c0303811991f10351000b00800400c8000e10529544030f43c911418403900c18042811a80d1100c0100070b80c004d40408035004070b1549942094494240203a62402c1d01d940d9881c0860680341000c0302c1480000342c000c0040800c0a0250050081411254517081900c0031040300700700c080d4109100351074103990303180c40c072103529561070003000d009503056800181d5900305410b00c1c0741060201e800188125100c000c2400b00d9150200c80f40d82102c201018094040820718103080b02a43d102d00410441c1107100c09000302c2e910654402d0151300e100721070810a441c000310040d501030145990182d03000c510b0b0542040b0b81e041a9010101a00e2640750041c9000c1c030b07a81e01c1d010500800301d81070701d0310381d5145070500c104103003075082c004021a00c00d000b0f801c06100e40300180d4080c03c0180124141600d840000c00f540c1d000350071040103040011b2a180286407110345028201c1c000302c0c0d01c41c80441e0300000000305200704003d500c2c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 326237886 1250 326236636 326236643
    0xc040c050a2106030804050a05040e1002031f06050a18050d020112020d1d060709150c0c0b1b01060b0306030727020301090903110606010203160201090504060605090a060309 76
    0xd007050100103056a10108a005000c40c1040582c24408403a03802c0c42030801962081803555107542c04c1006014914100d130b049180036502c0d05034400d204a00010b48820800b410420150f51b950720741205000d40004100390f019020790803140400c2498100b0098480c4007200e0307455890039181201c01d0040c0e1130341440b078990040100a51400036501c100f0a00080300c090706400361034448821044001c4801080100c0c4107800c40305404072148a003440b4280d08070030135242c40c4a10b2807d010560800c61b03041041a0203000c02c084000c02004280e4140a0042042004085d1191111105500f0000308100b090040d0b5103081004219401c00d9402d890040741c000e00100000742c00d012400d001e1494000414100207048040151141034900045010300255039001c01c210f58140380180c10000d203061030180c0340d007003d0100250380e6400000c0e100b08d818140c00c50002e4100c1400181c40e40d80e0300350032058100741000c1c0c020030210341010050a0389201600c1032525541e9420044088030070300b04c0c004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 326239136 1250 326237886 326237897
    0x3060b040501051c050a08030709081e030a0e0f040906020c010606110c0103020c1504030c031d011e0c0503070b1506160818120703021011030706230907080c040c 71
    0x640481c80d4034120350313418803c1e81181c3d00d5450130f84a0080301d41080f41d4101c001800301c0414028000284089a840158408805010b0f000140003503102e0050386560010000140ca6241070f80c0d42d181707403204212901410421003004d141c14240081e500c664a668080e40c01c10000291052003208080300701516a07028010038641280118040c1d03114840d400142c0c0b007a000201280800f8014080c0258420b40b0b5207600c5220a103000381800040c081982c0104560380740c0b000890340c202c40c43c40510b50010042205400104405039140c070f00c11600a01203110208003a0100040040c02e18001c107402c0e40c060050400c45420482e0b184a1040b0034201c460800040d8400900010701a003021102e80303621206002881010811320b40b4004032061503540700762070410030760610004034401c0054501d0075a0500c003450f0391140d6a4860a04024141a07941e44003c1d0291141c00003614140c100c0107840c1038500380098419551196801131380942d004055203803215180920444c048260240c980 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 326240386 1250 326239136 326239159
    0x60609090f03040506070c03021002031c05190c0212070b100503071518171e0303010609140f120d0e03060f01060f020c03030a09140d0203070e0703020c0d0903060b04050105 76
    0x511001b82c111103c02c482692111402000503500e420504500782040c0e03004644900344100744a03081c044982e1060803691400007800042840c10000010407045130002050b4901d07880e10892500c024140c481e400c01c440818003030300300b0180130009405080303082128040c0548488c02c15403540000e00c2050200c41030750108800e010f0003100208041507800c07020b00311407a40c4007048505425551940e074102d401c42580c980300b40d07550343e00a507491040700000390b007590704210001d4074640ba103004541c2d00d5545c0300c0b24076800c1c0e070b103103500010f480c0d00c0a03041040d5100c0243c0c400d5510390780d40808601046039103516050506002500703d10503500c820f0921040d07483c100702500c1500340c00ba00307401140118030200443e42c8040006226102260342ca45000a14180c02c1c1d810702140000d4241c801c40c4c0c601e04074800340e81d000410300140c0e216038000345c0654a5202041d0000c1c0f16010086046020b807610700c015941c1c03c11010000c81c0c0c00781505000c4026000c1c10081241c00c24000c003544a030311240d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 326241636 1250 326240386 326240389
    0xa15060806061c06060303050901080901140613020d02071103070b07030914120d080603070e0c0d0c02071203090317121611031812060903040b09040914060609090f030405 75
    0x2400143c594035111410720100300c545884003a900c040d00290045540003d50700c07000d5a1214100340e002c070300b880c020005a080920300c0d5181c480003400340c1d80f00b401c4040c0316000034a650f6048a004403a1403e086540e650305103402c84603110305c0c6156522900030054000361b2003c6440840b403005078150388003071202e418695000b008811070f038892070f0032014aa0700002c2d00741d01002100c1e684640c58544e0581c900c0c00d5001c06140c03000c40d40002c881d240350352041c0890301c0204002e80d641014a105c000c40c0303181e8818000c03841c00c41d169002c00c010b0ba81191420060580003419041664042e035150102d801002d0200350706031203141e0240b40382000d150006410401d050003008100f50030b510709580a410b010710a149987c103d00c00c025440780a40c2e44d000480d1505d042d448000c068960701404c1c00340341104005407a40030340c1c03141218551000070346c24801d45e00d0f680701d108140d91190f2503c8001908401540d9a003400f15038140c020513410000c146415400510b140c0c0c20301e60400210324043c03c100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 326242886 1250 326241636 326241649
    0x50c0f09061b010507110c0301020c1203130c060f02010f0c020a0b062404090c0f050a0c020609090c0a0207060e0a05061b010504050a150504020a050d020a0f080a1506080606 76
    0x2058150740e115007004a11140340c0a01441c0d01032405552051946c00901d410a4140042407800034820303841000f1070350401802003881c00201120707510540c0c903503a88042010740200800b1004181407412200807a050f034000078540000b10b0650300820003182c40d41c100100301d0700d40710325940250b8042e80500002a52a40c03169a0008001d4042504102d1103e41d113180225075a02c00c1038186404a01404081c40500c1a000b07140910318240c082601d6003813000c1c0035842440e9043c8204010b5805020654840c1001c6a59085000d000318038103140450718920990000c210703880044c0114040003d43c070340f28024024240360000c018404052500c020003001da4002c40e12029059482c42c4e000240c100c080c440c851160380101c0103051683c207140350201c1c0d5005a00e0010300d0a03881e14042c000941c5441c0710351000d9807020344941c0361b002c0c141c0c0002680445245d2110120030744001010404c04800f2039281034441c440c0c6020782c00c404804c6a4007042c0c3c5c10071301a05090b41e00c0040003880714584003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 326244136 1250 326242886 326242897
    0x503011211130c180501050f070c08120c0f0607020618011b0206010e010b030906240a030c050a1d06012003030708071b02090a0f0f150801050c0f0906 66
    0x8052485100401d000451100298202040d2010b5a1050f07030f01c030416080480b901e200d4901e03944446004c0e08010010341107001d15411556012004951602041182d070b1719100070740314520840e2221503600c01c40c40080e84c440000c030841809440b0010740600ca000800c0c6000d07080640251442d076031070440301140c081d07440c2c40c400107641d00e17140d4070a00700c0009881d40004403520741c050403566040c41d02e801c40c0004107a0203680300307000400030001d0f410360125079250040070003150403410080050030207100080c03207810250b0080410900104100d80016510111107003914007140840c2c0c0c8500103d9041103240f41055211803100010b0001c3d840303507026054052200b0030445a25440d000014510382003110880c0220740c1007130034030101079000ad420300300142c1c01e076200c0c0c4080c0e80c2c2680400c030b02e241c019085400854582c41030303451020f81900a9070601c900350208200c07800c601c209502208000f4413640314507510b00004620406401d2088607c01e0032000040e51070400c50005002156010303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 326245386 1250 326244136 326244143
    0x32402160605060a0b040b03040303060b040b0403030305040f14010507030e010209060912070b03040317060f060a030b01050f0a03090209090604020901030f03030207080d0e0705040606121503020901031401140705030112 96
    0x2044d004113010301600040d00280810340c00242d241c3c90a0320b0090203e8445c0e400242c424007052104004103a40c5000700c0d415258540340114040d15145400c200c140c00f48800244000e0000903140070b01001584428850485130764113011040c4081d41081c00c038401d0042d0345402007010000d408003400c001c407007841140f1440f02107403c1c4c55034502800340d503038005036412800141200141c9407480030031500d0603004002150090901c0c43c548000612230f104208260081c0f5864420001250380148182c80046400300b03403175581e891078038030002c0041044000c00ca20507421f110100709000d000081c1d0511550740030b000c1b0030250b4210b484200700144080c0007202016020809180007a4075003003d40f41c0400e0051021800003400f9107101c0c14003c2980042e03000c0c500c0c18404010351a4084d41d80c5c0850304a4582c00a1506100289030075184140d4202035005603016000004000205002410380500c400081040401c94210460542025103001d00010000d000501c0082810324426211512 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 326246636 1250 326245386 326245399
    0x40611101e15120c0608060306010b0a0f030e03300606030403080a0902060409050601110d080109090c0302151216050d0209010201150608010501031436030403240216060506 76
    0x25101090244040100000c4074860300e02c80d410030005411206c00b941100003100030701403940c142450324a007400380485107020082c1680300c00c408680260320424109941c141a2641c030400700c1c105500030300040300050440e00d030f0b00f01607640300003442030700a00608008013420300c2c1da260340c0c500311001d54014010120869407003001c8801a9a502c004000400a004c0081660710b810070000d02000204105082d0a0f04104441c2c5281503014001e03c0c1500c01c01c3d100014445c4079814a408071405079000290000d410414030001c8071400d00143c0055040c034405941150350b0090100c00c0e1641c00b000b241d002c033710103201410904105402034500c1c010103100009032412003d0440300c850f0b01c90b60100f8081548400103014550b4503005680d0076001e00001c548a40c00d000120485101c07083d085600b081240d000d021164a4901740210700c101012002c0302d4503940c40741030105104030501900030a03a808050003965003901c600940e0350604d140e4203803000d00580c540350000a40700003440642c0c004e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 326247886 1250 326246636 326246639
    0x190e0309090618010305070509070810051c06050a0213080d050702090a02090907030506040c03021e0a0201090c080309011b02030606090603030f1c0f06260111040611101e15 76
    0x440e483c01450081d0b01410017031541500c1c01e428042c2d04e4902614003001c01c51007000304494065010485001c69100759428001c404045868510401e900d00d8000c02c0107080009000c920f24443d0050504540d03032445000415580345091652010356000303d001060051040c0710161502e141e01f650700c9a541100545415800d000240d02071100307c400300d0100b941d5505114160405100d507609410090608624098842260a858001c450800c0d100f400001900e124414400e421107041554070000500703180d6201d9502a44070b801091f0044d001400340080541d190964a010030702150b0041e003c3d086030f840b804c2c103104001c48010400d541610007080609601100c42005086801c2030224245204603800d00b800203503803545071000c01c06410b249041c404603c2c0004285012625260302e941101070600d10300e8090410f148036204191804580082e00355000742515107000d000f40c0c02d81c0d501a140000d0001140d0b0709101c0421a41c8580d208080180d40c0c560150a1200c03100300c202142e907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 326249136 1250 326247886 326247919
    0x1050105030907300f03020723060c0124030b0a090c06030c0905030601080a0b0a110a050309010906090b0108010e0114010611100f1d010b10200a0308190e03090906 72
    0x30842100d0407207110005c100880241941888403101510b0080704040301c0d59480302080c00c0d5103142c0940c051040c1c1001840c803400d0202544074104c11405081072074a10341406640e000c0c00380752071205440868041c000900721040e544640034526a2201d4072984030790401408400600c40b071090703282070000005000c1800e5404000d000d009109160052081d0006031922119440c0043c00d582800e030700b00050f494802c0c11001c01e584400c3c2c02494000d450f55220303000c0d039014042084020b40146d141860b203600380301c90701000e2416505048000e01c9413514072080d0740d08903a04401240f80540082e001403140360700c206242c05c1104c560800310350070352002d00568004ca401c0041042c4020f03903190001010240032800016540400c04000c1040300113160201e04607240e0102554100306034030413030080c25050550305841503240301c0700f1201403882030315001d8030110b03040d04c41c003450307400000a5000c0c42420b0300801907280041310241d0b05081e016410301c015510081c142c140d2100b020400700c85803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 326250386 1250 326249136 326249219
    0x10c020a0b0316090503030a0807170c0301060e032b030906020d0e070b0c03040b070c0806160207050d0305040b0a0e13060905010605040303232101030b01050105030907 74
    0x3030680710000d01e80e40d0421802800d03014128104070414050301840400881e035000c02a244141b003242000511039489135010ae90162035100e001050080c03410030300c500000304a01840c1a10b100d62514151300c41035108050341c440700c1003420065100030114510982c4107445042d00100380303070305010500e115140d480d00305907084083e403a1070b01643e4540007148518204041c1006280001500b4580140d00d1078480d240d10581c05440894400022484101720607110003000400c407480a954027400c20501e082c105120b40101787d401842401030104180c5010120f40b0311850b8182c8800f840c0c1880d00c00401c00c182c000355120f40521101808150043d241c000c40f014145060583c001035a13414040620220751068100400b0014140411300001e80c00c80b02a0040442d98951000114000c42284070700d8856199010340071200d600c1203251540c860b000301e5050740d101d000302c0c1203181e8070340b001119580411181c00290798040c407410040d081c00c11110118040c00d20b490304d07000c003689030708101c1d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 326251636 1250 326250386 326250389
    0x14060706111b01090b0a0207051015030b07020c180628050306070c031211251b05150a08130f05070b0c0c030a020609010e0607020909011b0e130902010c020a 69
    0x49135101d01c007080c01c02c00c00220003a4400c0c0c4006e030850814046888003903070380107980d207801c1c00780d5591062a141070024032183c500035540700450075140d21b003082c4000c2d00e400b00142c40764010200454440000c11100b000188030384405001c0300c042600c0c110000220308040b0103a064020703004080481c40740c42c03e000d030500c900c0303942d12000400581841e0003014401c0081c01520000c1c0b801a0001c040f0064104a40d0181315504107032900c0410307140b11665105e4110001094840c40c004170020420001444030300b11401128503030501141014003030800e1090746040b070b0019240500003081c1e0700203818100307002c078010460386c0d00d041140c0c0d0340c0710b10b40801604680c040c028042412145031000700500d15180200b6006080b2a0150343e000c0303500350140e801c800381800309030304000055071264803c0c0e903403907038000340000c0e4203007401c0f851103000b0240c00382c4000707c074070003103410101c1180114420754909001a041c008541c1e90016010000c041040080341008110f000440c0980e40b2000e81c1e60 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 326252886 1250 326251636 326251687
    0x11010204081e210304062301050111061003080f040f080c040c0f080a0e030909160305070504030c0504180204050708100f1d180304060c03091406070611 67
    0xe94070500520020b501110441c0e40d0100e03a01090500c4562102c002c1031812a0f41100320590303c9481d5032401501500b120011941600041e070b408083c03000c0e05005180c101c85080c2c0340c01c0d01c00c41d80700308000e84411044480701911984408200005000b88000b0002610701c0c9030403509260700c44401d04401080c560102e0030b40da103e10303044101c616141c4102c02400d511801c004500c81c40404018048480040c04401c0712a641d074000a088042803003100d8000200602008a9262206c4215501e00381008144000382c940800256500c1c01101201c056a030403002c1c100d4270310f10b800f0421001e0003001780e2500c11181508407800050302c1d540116030141e075940d01d400690745071041c943d030707207098180d480004549500ca908001415590001c401c4c00b8030b910f000740e100d664401d46071511030600365040328000d2000007400140141d000c104a984544640d0380d0740c09140d42d1f9076200c552104000d030081e5100e0401c00c160b60000b85540d0140c68480c03e8080441e042001610301c00c4001110410a107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 326254136 1250 326252886 326252893
    0x20d050a0b0718080d1d1908070f050d140307060203070e0411160618120f030c0e0a090e0a1506060e040207050706080c04030605010f14101407031101020408 69
    0x91468020907100501c000e0b20b0342e6043c010b803a058180f0360b100b040b046000c05215040780d84518004500c42e00880242c0068280c0001d8108101d0691074401d1500c65955540202d80d004500b00b035600240f40304480c8024001c092502180d26502501d011403c0c14902521040021000056041c0051407041038207481e0300560351300b40b0381400103948100382a40d040c0d10b0704201c03820080031007400c1d040a030b54116100289418000200070010080124090074151010001c41c3c540d07944540e80005007402651b00b031150321001c20303040e9102c1d840b000e4515446582c214061051000d95800540c04c102c2d904100c0708840880e883e807100200e540c3d54500030f00d030340b104001d0050036040b400e84100713180156000c41c40c0c5859511203584494840c080c402c01c00c074983c00401d800610b40e400340e80295411900411603540e5811006044040500c10710603d46602c282c04446490500d0900414a80750348070744288030850081b100140d40807210842c01d000d482c602c0781d08005400d1010304080c04440d4002d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 326255386 1250 326254136 326254141
    0x612080a02150c0705160e0a0216021309051005070f050a02031e09030f150402060901090801020a020109140609100506060403050319030b0a0f1203030209060a02071403030a1704020d050a0b 83
    0x360b0400c008031803007862200240030100203541101e44819230043c80c1200050311a11143d04c80f141080d6403000195001c022514005040421a40f00704101b5101d20204c5418081e0464050165135040b00c1103404a0403000072214483c3c0070350000e00610005c1d205482c44d000d00780d5205540780c490345801d080184000300700500541801c000101541c4103180c000d1410302c2e80c18480184d0004000c000038000c4034045400c200690003030001e10041c156a000a5443e00d5003210024024100c104003039818445245400444c10004291240030701580809850034511030b00048000d02400b030f102c1600001c04100c00808200144082e040e40b010001c40022407004c50036004003650780d00454944201d0200c6810420a00c180c0105811500601c00c003050014460805030024050451703a640c01420006018202a5000c1045401d8980150804800d080e042d001d25559015105840000c20340d5440031781c0c1016a55402d040e40688000c1540f0001c0f0810340e949400c0c003403840c1c821511a100c2409 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 326256636 1250 326255386 326255393
    0x100f0c02120a0b011701150b0a031401090203041b080c010804140a030302030406061a040303030902060906450d0c09110a020c0d0b0103110f100504180612080a02150c07 74
    0x144030958217402c8028000305642c0350350501408424031a061803400300003081104140a42c00440f81580503081d000043c1d039403030f02840007a51044400f1280e03815416851055005555046002e4480100c003c1c0307544400c282c01541c4095000c3c10030b5404c190310014900300e5000c20894100040d110782d40c0981c903401c19292030019512203030089120400207100c84c41340c514000080e28100c03500b6140124003a01c2900124841f8030900203025009000014907412444404441c0e0103400c0081c0e800344641500c1020817004060103060303060300101d981000848500d441c00b10b11450a006040700f41e10b060b56a0210401c1302e4010380c03c01100000810380980315501803081480070901a00c82c07924a05d110f5481d401c405005000042c9030a00c000700441c09a02c03080f240d6040f000010704400b0b0710441c2c000d0058482d800504c94100088080804160500d0341030040c00201c03010381c000c44229000560780c118640d04006414030841c4600c844001e00c0c0882504042d0280002d04159569900d8904 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 326257886 1250 326256636 326256659
    0x19030f060503031c06090b090714040b28080f1303030e0d09081203070f110a12031a0a0b070303020c16141f020607111203150a05100f0c02120a0b01 65
    0x1b80300c0c07120286025903104c907030303100d022000c0d92101c02c62828401e0304541e4246540140a2500b0920440c10081407124078203541d01c0703042010056002840c103990083c8001124144406c0b0b0340401110024004920350020245400c0400c51180c01c0c089081e02850b214189050051903483d030004101c940c013000828001e22001c1602a07603001d00c940740d883d024801500c6104914040f00400450300048111540d00b4003e4000b810f40c0040c06280c400000e07007004014100a117008040b80301416529507a5103450300302c400c2103c0000103401d080450b55181a002504030042d403040e1801a010030800d404406100c43c5c000c1c0c100700000f95072841ca984280036240300101051801c044000d5101444107400050095010010340b60050301c540550120314184901d440300901c4403034002c018403400c64040a0b03080d03d0850706031001c840b00c45d0782d0800c01011040c8004014041800f080c40e100d0818451032000c100c284c0064110041c1e0700450050310318001450405950020180c40140130100307810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 326258992 1106 326257886 326257889
    0x402060d091a070206010503010c09030206090102150c03090111070305090f060405040903090e07020c0d0308040606150507060b0306220c0914100b19030f060503031c06 74
    0x89108880c2d100191801c0c80035000301d00001c42d030390030140310b41980320009907a44e0285514503028001b130ba82c0100030140c114000e0021070303c0394412400c2010301402d10201142e5030380c64038083c0340d42112030b03200158001200802c8030078040f992250039075242e50400c0301c000942e0110200080c12a1040b54040340d001402c00704006c0505401420794000c440f0400c0f112281c5581e4901e0898590700c582d124207074002184201c1c200860720440c3e00d242d1083c130841d030000e0309a4507001d406001b080341c0c0316060009040001c4010420805000c2c00c6122a015401031400c0d00306816145100620050903003850080765048a00384001c11100310002e19260800f040400381c0c4244000c081e100803160702d203c0e4108104005061001c003001c440d840d1050070401c50b4241c44c51101240500318094a2098882e150503020605940a02c01041c3d2403440d42c280e460a01c90318180002680e406 = true := by decide +kernel

theorem cover : BRFrame.Cov 326079136 326258992 := by
  have h0 := BRFrame.cov_init 326079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 326079136 ≤ n) (h2 : n < 326258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
