-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0525
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:15:44.090805+00:00
-- url     : https://prove2.me/submissions/836f6b2e-e7e7-4e22-be77-33e6e2ab33ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 94244604 ≤ n < 94424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 94245854 1250 94244604 94244621
    0x601020a110609040605041112010605030103032313060f1d0a06140c0d02010c0e011106011413060308250302060c0d1d060406060801060b04030809010c0503040b04030213 75
    0x60907400558101071101c0368011980040d0415182c030720100b0987e86900414180f02c0358040415100c100c0481038510040040c0d001c40240b00c000c01c01400803135031103003100300030740c01c10160308018058815400704a480303401d8260841080300b1034003040075a804a15012040000d0f174990905034034480d01c20f07440403010380055038072801e03041d0204840c03409540d080703149240b030490a508140080d04030505080c04209440010307595006441d5003181c00100f40c0840150038601158100c0c214120305035280344c10b0062690400c514100b5000c2c47d9a004558500f0401c1d400e07080c000b003a0f491415201d250001001c0b43c0d0b0102c4110007003844455040120654107405500401840c1c031111400b40051344200040b00034a5210f40c410b42c0146081142101d80d0750704030009148502e440d040c10001c603810794100c40d4080e4102501048107400782001c1d1400d40b50803032101036484001c030f00140c1d1140c540c420300074124000401c0c00109036411602600440740243c031345002c80000652010100c40032034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 94247104 1250 94245854 94245863
    0x1031104020f07110102160305060105040f0b0d140c030106230f010203030115090b0f1b1c0e120d0507030f0201020a0804150605090a0b01121103130305040504150305060601020a 78
    0x2072100780c0c0030428062842084d4041130050ba40f118511102032002e040c2d007508241c42c15404100108114100782c45040b0003840a10702c20098a003600001402d00c4111400c05480225520001d1401c0070003407100c0002c4081c024001c1140b99074503a540f00c003403034403c088140316060351000060541170451507001c0c6136005178003075899603080c840c81e0540c0c07010048110080040600005c51030080c900700525802d80500c2d44030b51201c0d400307402c0001c4040401c0301c0031040e0304201020b0315851903030700c40e078031344002c042c01c0c00f03a031401580700403c83c450701c44009a01ea034070070b50800032101a0030100510050f8002d90307408036103185110303080c0c0c242c0c82032035102c40014241000043c08284d0912004208140115000ca0359660751400248440d0342500d2440c0c5040d5222540c03c1d1940c0c2100501c80000b180170407e000c49401c280e405c104070300004014461005210392090300f0503128008440c060440240104654140342c00005001c00c1c42d404100d40c1c030301c1280040380d500c2d030000a5107035a40b03620 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 94248354 1250 94247104 94247107
    0x30708070b0702191a101a0a0c0507060c0b0a06180b03030c0105010605130f0302090103030e01091d0a14060a0302241602030114010612200c0601031104020f 69
    0x15541e040c100c408020806021030154400c001007140c1c03091440c1c481180908050303580310084035001c60708504040c1011070082c6030700c0300802c1594480003804034007001c2c064a40d83c0340c0529120603544c0c600040c078024414080c4190100d02c098008400c1c000407405500118070b565116103500e0111009801600c2d01e0340c140c0342006012200035000f200308600040c6c16a418490844010303030a540081e040600481d0700032411042032103550f10340c08010200c200c10704d07003221320f1038020851280040c080035003044070b4129a200585d001d400031000070007081c2040d07150582c6907540e503146d09000b61440303d08142800f2494900c681c400a40c0c5008400c0100381021141c511340c2085980d00d402413039901c183e221170000c03006041421015103126004110b001c3d0700400c440c0f04141c2100c911212550f011881f1200500442d58023039000743d40b0300780d0300b100001c40340410410f01180f100d109200f208010000110301c1d85090010440c0c504032481405600e0240b116441000203900802c8a0706080940 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 94249604 1250 94248354 94248367
    0x1b05031306050705070516140a1d0a0b09010b0a020d110d08090f0102120a0b0411040603150f0801020705010b04060812030c1b0f061b030406050910020a0c050609030708 74
    0x300303600843d0055040e0030990b142a540340d82d11401e00c060b5842800000d0014142008a07034041c407020760181804480f504019400c0c0b4410811132440f10709800600d600300c000044070000e699020081440d001007070801c503503949103030101c403a90045100c18014001c03400c1d6070301628016610401b0744021400640b14441c1026401c46010030001c0c0307602014460800049100c61080c4010314408554404402c0e103441c144d000c000079a00c054008034000e518050214880e0008c0c0070503102680c69518000c245402035101d0307461600700a411001e080c015800000410400540c010071040784510020b0018141d003104003c01c9500c2c1d1310840800f600000100703542e0314a10401180d000c14050a0281464a0045c0b0b200302102d040345044001d0380310144014a40ca0104507143c1d00181c180301100d9000d1540b5101d840303e0102400050009442c0c4001ca4030b101c030107100b00030340500e00c7c2c0411900d07803070294801012901100411744403405050041003221101008a448260300903200514242 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 94250854 1250 94249604 94249613
    0x120f07050406030c05040c02010902100c020f0607031715031009060e0706050906070201031b051215030a060b01050d091511030906071b0f06020406030c03200d090f05011b050313 78
    0x528000394030115580e0f00442b031b0040e034034000c900c1c0304003042e545c48011204a0b44140b0012003943c840041c8148028405840000e6004030f455041c644840c80e215001e882d01001102128000300150307074180900352451640d112503a00000425000d240c06001803480b43d41010344496460288a00040c420001c0c215141440b0b4000d1244c28418034000855100c844403200208160311101c0340000c81c000f0700c0b407010080754500a500800c0b4101d0341000a006040003c0d03a400743c0080040c0b41d55218181a0030307030b82c000c10a681c462a1031180601280449141c40039401d601e0040c0d00c1200741c9030403050b4000903801002c3e20f10907420540149003036100c6503030555500300c0b142c030100b4000300241c42030000107034290003440b02d280c45800d001d61610309060001d019122a071202c203040600d4290b40800041b488003600c4103540c2c0d9896942d5a03038016003140c0001e06002d034005400c03160b400c20300804101e015403102c91001403070600c00007070788101c01040701d8a01c01640d0031260021030018940204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 94252104 1250 94250854 94250861
    0xf060d0218101205010605011815140c03030a0603120f0507080702030102040807080307060f0e10050702010609020a120606050a05180a0905040b070e01050906070b0a0b120f07050406030c0504 84
    0x100c60802000000c6030340310034a0011a002c03c10480e8240d4582c0000c00c0103507089170250740c45118503140a4005403c20000b44440c600c0e4007034140802214006c001d0644103010100c0346006031103019250341c2d151264989014011511045a40785200000301e0190f038407815940318840d050b665028584145a01c892980fa00403810581c1c2c155400c001c00030784034038104002d4004012a8010715154207035810035500f150f24078031f941c45032603080c01c81450310719502040019441403144000907041d2203d1900300e0040c5420b4020308a51031000820440281e0405202d1a03031070b102d80030912940340c880404840501400325404007189080c84400600c11843d000751a9400c805403070300c00d00503514142001520030648007521380c07007003403030a004120394070038810400380e0780c282030085c50b19800d07901040861040541c080e003a840303658085190407020b40c0091125000040040c9410154404002c0d01d40c52038034800142c0c0d128800f00012181024066042203a40040d1520102d074508030a20025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 94253354 1250 94252104 94252111
    0x60b0a030504020a050904230102070308060d060f150f30050f0703140606010e1e03010e03030c0a021005010317310614180126040303050f060d0218 65
    0x4945030342d4010600313842e038900311b42c41580642400486c00030280c01d00c08002400c14685206a4010804500804d41000740690051400e990305413190465003000c400502d042c136545002d0608000300039403070b0020b04801c00181d6408281d0030045075902d522181410700c4200700118010394200040308504841c0860f03c07031080c02081903540111081c01c00c03905008a0350801c440da072001e20f0034201015006c010140d8410402c0c24489507007e403010001c2c1c4000c0d4105294048803040002d0000d0b10b883c00c1d000756240301401c804036a2130703007002c407110f514581104407901d0040c0b00345241e8030b1650b0058010305040740c1d00300d00740c003c4001c1a101c05c50119803050f40c01c95101d5100c8001e03400450842031140035a03a5803092a070520130708001c0014081d42594980c800703002424000d00303010f41001414204a20001d0800842c0c82d40790351541061a41d42201d0041481002c5082105054054000910901c110014207544d50760388000c000113441e10b4680a0341009690b440c1210041d203071701002d0340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 94254604 1250 94253354 94253359
    0x90c070f0b0705030a0b061206060c01021308030306090912030403050a091e03061b05040909050708030c01020703030606140d0b01020c22060b070807030e0d0605041209060201060b0a03050402 84
    0x180090320340c907100c1d00c5080a641c1000010300020030400307a00c0d00ea204201645e2811102986400c02030280340103505000b9101d2881500300080c541006c540950490300304491083d05111150343e90f4458a8603a00101d68040c0260344080c00191010303000728500000003c1410070501315103440e02d08984580020740c46409120261501180000d015003094092060202c154003da0f42580703001c8c07069845071501c00e080d4042021260021075001000d0f5815120212000038403c10141040e0740352101c0d5a11504141c000015000c15040044d0000d264490003600c007030190980c1c940301119a0b0f0849001f22103d80c00a10605950141c80e0700310403103210052044503043e603548c40000e00c00840c66001ca00800300c200100032841006802400000c3c420803914a04002103612408100e119424004042140090380ca5000b41d65168030440c101d0303004401000136181901d040505020448000d80200f40e079000002a45441400f481d4107880760041002c1c241500c590041c1c025010140c0102c0c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 94255854 1250 94254604 94254623
    0xf0303090c030b09030a1403010f091503020a0e090f0705010509010e01091707030510060305070509130b011706060d02060409090206091003150b0901090e1e040809010e0102030306090c07 82
    0x8045000803c2c1d050103120843c000d036580705149040a00001d1501603071030b000580500041041d8000914944101c0d18100008200391818458401001d519504001d501404040300881d04507039076180603200703032104003ca40c2d84012840f42c080d40c441c01482018000740e420040c0000300d51280c3c0c406180c803001810028070040e198540c191b07008810303402503601035000c81001c10500200700a50128642003100801025055032546900d44c503071801160f002d45004070118014502c400048070850707800c84009025035841e0036118003180707a0404140c02c01d10415010407400d1528500a043c803070f1b0300601c0f9a141030314001888024200101099a00100c1404542500c3d290110f421a1040541c0d40000da841c5106841d00301103c52a048544051402d0009403c1039800040980a4551701c803445917180e46d514140c5200d61450304003650b00c51050405010822501c60041c0c07114080c01d881d068107400c014401244d59002c00c641030307940895164040750441c4507003002000003c0c010760401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 94257104 1250 94255854 94255859
    0x1e0301050406240f09050403020f0d020106050109051c02040e0a061b020f07081b0619030e0c1e09070e06040806010e0c04032102030c0109051e010501030f0303090c 72
    0xa08654040354103071051600e50302d1100315005070451203e0042e03c0c09098011071130802d4072520300128540181d0140c0380c0d0b5074001c00d080c54000c011403007001d180401113404081403128001e000c0c01e014450b05012686c10301c40460146040c4c94014039600b42d40300d448a603100c0c25000c10004d41a01916003112707029180e50940400c200c2e0007814002c13008514100f400e071f099524001d26104030f401e004802da4002c44c20510881070003141c03848420626a0200e42d00101c410005007c40c801e0722155207411584e04a45000103815130081c151504103941034a80801280040c85046001100c0380750790104240c0342001e00e0720b0141078050f00003905290130b6507409581d402080144c2d000703810100042d400240100701043c0302d1607450f40c3c0029219500d6042c145503507a1340429100c5154100d08040050320003104045c420415100a0304802000f4801080700d400c00580703510400d0090300182d1f039480f030421594841401800e04803980040154100541034504034020000c411007103809200640c0c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 94258354 1250 94257104 94257109
    0xc08070e0c0406050a0e0109121a010801020903100c091203020f0f01050c0409050a0906020403050601090f0b0105090d031107180605030304030309031203020c1002120a050403021e101d0d090503030403021e 90
    0x95030006441581c41e030703452000c030100c40c1cac601c0c100507800200580e004110b0109e990314003050901541401540109580c601600700f40e03a405025045582ea8816002000052503400200030300030010110581c1e0700c0011912510b8280e13402100c60654011041000700306c620500d520031790780604198000110040e043d9150001c0e40e11592095409900c0200103114440c018440c205c145032100c2c60400007240c800001a02500a58072054443c0c0700104461040c10f0060154a03075080c0c901d42514807240d240d0b085083d184003e000b500143d070745084804240c80c03c0001c03c4a056039015114120564030310f40d02e101e820654104001d040680a202a8012800401441305400c401d10000358540c0c511f02c441c1807040070014800e0300c00030708180034400400e40120305954401d81c0241d40468110301c100d5207514001504100006291401c0c0d180302d1680c1008030345542d141c0200040e544e441e20715a60449426480d402419070641080004200500e8802c0c00c034007500e81c0440704034107400c032103000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 94259604 1250 94258354 94258379
    0x203150d1718041b090609060e060a11100c030b0d17131d0703110913020d0e0a0b06030c01110606090a0902191a07030503010e060109030c08070e0c0406050a0e0109 72
    0x30903041400070444c040f1a49030480102c1026150905c0c00c00e181030303c3e040c1c2c01440800b171810018090000003904940c550b100300302c41e05200a0503422a0708500701071a03c00300424518098100291070300401040c0340c036040e034850701881c0d0862000403081e004440000da99900900c80d04143c02a150030002d5020500482041824410708205103a4644180003400748c41d5644c4c0c1501c0c16140403c00c24006588021060407010f254800040e110038240300d4100c001c00300d6041e5110b640c07090350242000c200c040c0f0540c0780b00320019000d656140b100100192001c0c42c008011450030b4000300300141480c20000c0501342e10090404000c582a850790b008100403c01d00d60903210b641407040010710400c000340f810340038010a94044d030351820f540c9460090044c0018007586842c10034010104107140c1c03140a0f40c00255800088140c2803c2d80c400c0855600c5c03415106070f0360030700c00d0100000c1040c0f042a0548044400380d071111032410f01101d00459a034031004a80c50705000c032110b804581d4181113039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 94260854 1250 94259604 94259621
    0xb040b0318071e0801060b04120b0c04091505040b010311030f060a18050603010c0212040501120608010c1211040302011706010908030a02100b0a050307032010030203150d171804 78
    0x522143c580742829140350039646030342c00a011281c000c002c00c00c4810032071000c05408581090341c014240e1990f140f031580324840c0764014180d241c2003155190406a8003c000d2086a10441d000c02c42c44107460015815500c403030041e0109010203100203050189424222948160002d088507035103030302c03588012408881e0b07091511000f961801088400c1c1024030841040d43c2c903a0008040214070411400180c0c805ca018490420458085000c00380c0300c641c2015000d048280300034040300c552044004c0400f4600c9444054503420010310000c43e4030803100300d83c02e4a4040c4e48180891001240c1003451020140c01e42e410402c841e5030000e401d0b042803000e0310036810305601038000d004001e05070809460b20080c803103100d0f880c20175081010fa0340001e001d0049a84c444c0c0401e01c521030104440c5608107080e048990041449041403120329810b0703005500c42c9101c110628400c2c44013070180820380100c41170051505405a064074801040b80016003081c4a8001d81c09440e25403000229054601c0c50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 94262104 1250 94260854 94260899
    0x30406050906070908030a1211070f02100309021525060e0c04020310061404150503041703040f021207080a080901030501170c01120b280b040b031807 66
    0x84003840000d880520801c3e070040641d26107402c50508101c2e0342a224480d4002c44424080911113140c84401d19030040454810b0b0780304e205031200858101140f1408d0b8407103007240b065000b40050740c07000d4000d00c0388201032500a0002c8482040040d8500343c181e1010f91012901c1d42e41062004520808240d00c02d015440717190041641d0300c030710003600e203040484504644154014420840c1c40c04c0000a80c8044640c646803a50420001c07110601180c0301340d800080e0308041408060103240e8100f4000c41c003491041d2041b10018109020100f094001a03400070070102200307200d440035240071000c00807250031043c292840316a648014a00d446900300e422144020f003c80c030306000b9030f018810709004151040008241601d409035075510396003821205030502081420a100100b180d40c010100244003a002c0b406400c8042d40d0042d8140080d03900003c5c0000100c00465510405015175044038980802d5504545482c2c0102c4200d42c900500007a540c410010000f0307454007070031203507550180d14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 94263354 1250 94262104 94262111
    0x1603060f1d0d080c160b0606040b13080d030606020c0f060417060f0a0509151e0703150b0a0f03020f160b090c03070f05100314100504050112170a03020f030406 70
    0x1000e00243c01920000c0015904400501c0101d40304820780110382c0850750720170b4180302240d48081c0020014002c54005142c590408502540c50b50440008101a110b9003000c541c07031000c0c42d240880c141c031010302810005801070107030103a407400c05401810303d92070002c01c820304258598180c5400e002140c1400102580b1400034021062500030000382c008280d5002448030741750125076030707a41d814401c15100410b01c2e400300060b0145105c1070100b603004c14620208841c2e04110744010043e1214008042250003c800002580920340c0b003202c41650071601d403401005a00ea8084d4000c0d0041121006428410441e150341c0c1d84503900c9088003a03204000b0a48075040c0810090b18189050140c00e000c0da010b4802030220344200040c08089130022160f519000d50005000c6000d080521140790400307075107209100600c030120010106884c07080c3d8080181c0d03a030b0384216580a4440d0980070b0b002c0d40e0801c0401602354421130040000f00054100036191042131031182c10322b54012141a0394850b907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 94264604 1250 94263354 94263373
    0x6090c1206090501080d110a0f0311150f070c030509060304030c140c06070b270706110c0d02040902150d0906060501111b040605030a0b0106111603060f1d 68
    0x1841d10030301000d0403880a04206540c102150f595680d0102d070440070600c00b0000c45850100d00c10043c5459150340031903480841d24051a001e0301030301d0b40a2001009000f04114111510004010203101e0100c00741070744400d4460501c156086242a981541000b0042016580319107035040114015417103543c41ca800c1c1d50480c1031400044070381e0002c403025a0004000c0e04503694441d400da5424a4020115840c0c41d2074200380d100140c91400c12800b00c1e03001e00d60900c0704141011800404031010789e152001e481820b804060703203803004103a20703940c0310909074070301c1015090907488900c0c01352000c0c01c800c07014584410740e24280d810043c2648031080c0c49119a20400c801802050b00420b0f0a0038180413076203818951a440d035003002e140e0501402c5054460740e66076503540020004200213020b0780e100c0c0213241844c0d40350440c02d020b2100800c00c07419080e8403103c07000a05054064112000f54003840c110b41d100c902400c40c09402c1c0c3c5071281c48003200c0b982608200700c0180e510304084002d145058 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 94265854 1250 94264604 94264637
    0x3080702120f190c0302060a110c010504030e130b09010e040501200a0e0d03020c1509120102071b030302060f04051005190f110d020c03041e03061103040c0303050d06090c 75
    0x302c440480c0c410132201c80c00d1034001030b4000179071680100c58100b0100d444a00085440054003900c9416003d660a00040c0014035802c2603610000d41d07025607152500611158031102074600c0b0500c0c250b08450135100400c0b107031218044c142c0c1c1191044002080440500c0146030080d004020145001c000000d050202550021031180340740c2c0055400c0000c0c40c2150714042d46075070b92944a0350069003a01001c0c05280107031801c85046ca0030051640c40c00400e1429900c2c003d400c800012038009440c0074440a1622082c2500760031207505034020000380d50f07074850040b150407010740121500e209002070b110312800035001e0a80f0500014186600c000c0e100016403080d41d07510503050005a10b00110001c250b1460b0b012981144031044026a50344642c00701c00b4a1485268000e020200151507019848400462440103d0b40141130500c40400d0f8400c50311003a2100355401006404908804c00005c2c0c040e0002c1c00108000d240001500c0c0d668004540665034460882d0001504131007801c2c40c1034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 94267104 1250 94265854 94265887
    0x7020c030d092d060302040512070e130c03050a030e030d0801081c0c05070e010e0c0910030b041b032c0c06030615070b04020109120f03080702120f 65
    0x1050840080144025126001e0700d07050701800f480c0b48031803580c02070894031a9605403940200c4102880d40303401c3c681d6010000d001b900301c1e0160521800b112906003081e03180c0014130b03805540c9030103030b01c0c3c06c1c0b44c0741e02c80c3d4000c0040d1511070442d2080c104010010104106100701030800b40680c80d10303140421120101410141200010820300280b00d0040c00b229000003110020880c1e00c60310302800082d881d030251258000180000d0282c03040950100e0701400340505281241c0080d4070010464a41d402c01113080d02030a00d20940024030b11001c0c40140d80b0a400c180c441e04405840091004610482c0b0400d00501c0341a10010179118104d001401e10301d041030001d08404407041e04800081e111101d6242d80c0d1400c0e80e41e00c9408040049030065503050112264000c0d9105403c1c0c0d255001d18015810020441e0260b003c14020000018800c02c8000b5900c0501d6101c00c0010070301c100c0355026500e00b00064a103404500c214004155043c90309402400c022041c0c0829a85605034650807072940e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 94268354 1250 94267104 94267123
    0x501020403110612011404020c0105090120030c09010813020904063c0f0624080c0a050712140a02100c020309030604032d03020d0614060406110111040e0702 69
    0x58003081061440100310512042d064500f64032041d00d10a1410000038003900074509d80305090352a0400b400280d807130540c400c101414216400c02800b0041040c1500940401c603007944080004015421944d07100380c44450f0b00140340d40d00381c148007080c0d4010490482c0200c070704480f50b540e20102c3c10300c46030301c581d001140e107075118240f5076a880c2c00c1b500400340c1c02c80f442c3c100484103803140810390b161491900980c7c00340601c50000010000c04d002007040018020b4455000300d160140071640448402085800c10031407911800d240815a68440c483c0300040712003d803c22010b01054505100d00e500100748628441e801444030303201d406140400c407807000380003e080d980f003000465102e4501261942d801070301428801c0151414004003070303403c00c0030300290000030300254100c00310b02d4056002d41229000c0540801c4580c0e04d4450200711000c02c007580c07550021041c00208140c61040d88040c0d00e8800c0343e0004645151503904204645c0c016400c545c40c0b115900042140065040202c00705 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 94269604 1250 94268354 94268359
    0x2040312030b1e0f0d02030f0d021c0503010509010b070f0803010906080f0109050607080a0905071203030507090501020c1e0a0909050d02240c0909070f02070504090206030f04020a0e04050102040311 87
    0x55103a80fa10020710f0b0350600018443c011889031080d0b006550781806509100810041603812622054034004d4841807084c0105509400d04540d01c1c3d4214401c070300b1703241a80c201601c4a812030f400d0446203030303903508030003001c69026111000d85000150800c000e14020500d508022401d203090614107406c00000d0781c10800070307a140003206400b00300009003443e0880940d081c000c049840c0d2001c0e040107001076480251041c8900c120000f405110440321a446a0180c0e03020481c54a44000c103c42d0091a031181a00503400f40303200359010725118510102c3ca0081c07103605000d4008013400310707800c082d40d44d2001104907950000103080c00014000060851703036038809400340d00c1d0850402940c1010080c4034100c00400800000c04000644084880310170000340301424510304014002c0a4894081004005004d442800140c901302801031136246540103111b641583d880242c070010300000208140d90000d0030407000550106207800301030165010714005603a035402c60510b140c422481c42c69450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 94270854 1250 94269604 94269649
    0xc0f08100216060b120703080d140402130e0309031015050303160f060e030d05010614070b0a181509021c050c040504170c0703020a0b0406080a02030a02040312030b 72
    0x1056a401d488031015030395101d08009a44881c4c1004180710201e8000c0c61452031080c800d000c410301503503101078103030100041800d00081d00310103402c45401000f80d40003500034a803401c2110080d105904590982c440d20b0003200e05000800b40042c1c41d018510764405c00580c0c2c1d0f213105201c3c03014640c3c1d40501511050b801145403900040695081c0c8065400c041c0c03000495100344000c001e8650050890342040300304030390304d03020002480c200070705082c03141401094201c2450601c4410076001e130340d000350300004c43e0720b02035a0300b16640c400707443e484240800d2010024800030004219110300c5140d58040c0c0740016846506205100c43c09070005424418414103000b100e0000d100010325070440170058801003403d03141c40ca4410240208140604504500440c000da084000010340c3c10840b07000312001030a05684041c088401d1045000e070f10300241c0c40c000040d640c0826071b001035400c0090250300514090303494442d521980d29460360180026154824001507190000000400b0002c21071086c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 94272104 1250 94270854 94270867
    0x71203050108030a0e0f06180405060a06050702040b0f030303070203070b0709140f031e0d02100e030403030f110303040812150a090b0406030803070903050d08090a02060304050a0c0f081002 83
    0xa543d6802844000d008001400c0071246441d01c0c1c4030300381e0034a5403000e051240c483c815090b00030f102c2d5000411060043d49803900188092034003040c402c08681841e240d281c5080070b40d8013030202815038125180d03040f1590b16500781c11a141040218845d5007194040e580701c1406250820310050007034000f8080060b4020140084144142202000c4208079503121550803882c0200b801c180e106200d1744990900344cc50449481c00c00705aa10400403e68261246611038407881d00071076080850b0780c0c8051340188410310000c3d02810030030403500a2400c180c040116401030b0549158011102283c60210100352a018088094a41c60f0401d40a007528100c20795449c01051251186201d0f11066070b464803498010b80d20703143c1c008000746030444100c13039880c6881100541640d03810f00c42215688140f82c46684024071980c0e01c58011468900034140941c8980c003003050b1600301420035a19801064201d000055541d44100700070b000007001070300807900d000899810404082001103d660041028 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 94273354 1250 94272104 94272119
    0x30902030d0f0203122503020901020709090b0609280b041a030a0305130503030d0608070b0c061518070305100f0602120703031d011e0c1e02010e0d050712030501 71
    0x1610a80406050040681d981b48010440190720303980c2d07042c0098000101c0002a80d61540051141d80070a03001c0705c0d40c2176030790611202160079079039001e0302d6500900040b0304c85150190100d5082200c1c8500e400758006025980301d001d0306405034030b24429584118041c40da0038180100c441980034403161182c06003c88002c01e07119040060010108280014590640003081e100301c0098540601143d4603040190003640082401c2d001e511820710503014002a4502032008503500d6603070072009800755842c0e10b00b003101c110032641107195202c0041c01000c4061801345140c20b2082e82d15680c04500380c1000c0420900550003034001d00084106101c080c000203800040a02d00e10103078400c1c0503581e9019090450080a00f00b05000300c0502d038040f020402e10054014007132440304012030a00c0d042407160f00300211039102264201280408440b40442c041c82200000d40f2112070002003410040c1c5c051160800c0501203564020079030104180c000e01540c0c3c00441c844000f282010800d65041100703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 94274604 1250 94273354 94273357
    0x712020303031501090f09060e06030309150901050904050a020909060319031b060c08090f010b0f011b060615030b2e050d0c0e040c031401050103020705070f0303030902030d0f0203 79
    0x1920008043c80240407507485106030800406949003c214281e480c0c90300300014045038401c40400700d40c207001046a501d00401280c18078a0b00401c403070000c040b800700c0301c0348030b40104000740c0c14080c01b802880107540700e41c012140326400700d000c0181e44224280411088801c0981094000c0c0d01001180040c03011139820307240c040e41c041c00c2c03506c0b603810044401c009180201c1002481541401c10151045801c0074226005c2c07540700e0180c40201481380c944900321240e00d810140e00c84081d581000721075000e2103d01603c0c820201c40c03110180401e0300e8010650303400c0c3e40141d40314041c00b074141202a5251040440c3c119040300e40c1465511780c84003c1c03007401140c8054507c40040d000c00900968061011603a050010042c0ac2c882240101b0700038008111400d03d8034052420b00c8800b443c4140704c0d02c12007001010841c003542c44e59091800440080d00300020031642d500c1640d002161a001060940004510075500480d09d64124418142440b503070541c4102800b1006680c8520781d5004030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 94275854 1250 94274604 94274611
    0xf0f0908041e12051c05030603060a0c02010b030111040609060509030a060209030a1221050405150c0c030309030307180b0403020d020609120c030616091203020703150509071202030303 81
    0x1120704107071a0500c001060748001d0750300c01e148a501a81c210f500304540030424400345c0183c070307807643c00131960a401644d8034403040711000c2c4e241e003008000400c1c02c240b50348004095071141c400002c4415001e408030742110082c0c0e105251440740030604000040c2d010352480701402c01c52800900302484400481e9681081103402480180c01186816031078400f000240c207aa604404c60244014000300040c02c0d05840f0300003003203d410740800d80d0003c6185805094007681e880801070214180d0b00c44a48034070304000d0045021814200211160070208001860042d440c24010b55a03a06000c2001340c196000041143d2081191440030000c80c6030300ca040d135046035019610603030751610602c00903003d8416a403045a1014124182810944001451b08c40c9518240c0848055468900b02c40040c0e585640400d030001c0c4005d4070a1001132103c03000c64403030901c40c0c0120b541d5507031a0754440c00300c202032080c00e1807203641c0c4104200c1c51f0501041a80014041004140030350740980d00426140c0c40000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 94277104 1250 94275854 94275869
    0x10506010e0a0905130206041203080606070f020127060302031f0b0a08060103061805060306070306050d021c0b0108160b0301060905061b010501080109051e21041203030f0f090804 79
    0x1075000170b1004c3d0103405101c0c000c55009008030342e20b5485140c0e0301108980f8000940005403e10300143c481d04007802241c001c070381c00c0003c04544501590045030b000310104c0c099410078168a61000e11301800071454405801d281d18007584a10b400c8220900c10b600402d000088582040d00030001084030b0341c21030b0b03040216481e001c03000d80e4450300140d01600d590f80c0b182c190301d510242c90700c10300b00f41c0f0b901990007290110181d8100c1d46520204609031600b90003021f034007030042d80b540d000601c1d000c2e210000304044403101c5401c1c20155111a42d140ca0241d0082030f054202da9003a25291503612444400f61024200d901e0840d410140b00402d840c009001c0e85009540005400e0540c0c0703071304543c490360060358400900c036079a12000000e0191030001c40480f614807035440301106515546503131048440703110f0001e004c80340480c540f0038007010151490441030f1604120105030144141e440c000042c0c002c0c1c030049590b0360fa0701c011500321043c18010000c2c40e840c10240c107000034100c2045404403045c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 94278354 1250 94277104 94277111
    0x10b03060f0138040306050a0c140901050912030406030504120c03050405040509030d0524030c030c01030b12060106020607141c020f22031118060405130b090f010506010e0a09 77
    0x2c400d60081c0310302c240c1d111043c3c0b8007030220300041000a560070041c4690320900040c072030111400b10548203003202651003101c00005211400d6039500c1100501500c11004200c000c00003c4092071030705640c42a003044000a403108208800c0c40200117000030001704a10f040301d603004007901c3c020403034000c074000c40380b040ea02c88011a584c1a4204151881030070510707402c000e41c4c145081110250340d0300b04290420101d54051101e101e29000c80c0c03000028001601402e225640040114020120712110f02d6100d02c1c1a03102200f0600c1c100505406440c0d00d40080500d4201040f02401d0392003052405d61038204204a8070707149001c12006440003400701800580c03510791912010510b8001c01d2280128510a514400443c50344802e140342200c0c001c072000700c1100c40c0002400001308203007000c00f80d070581d0600420f00300c1c206980640d502c04000500291021040e54980c0c10441d403d0394521034690003103400040000c42841450340000090030710800410081c00412000030280c841d00480a56 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 94279604 1250 94278354 94278419
    0xf04060504080702100f0207080102310b030c0702011d030d0e01020106090e061005030f0304170c0a0603020c060108070503190611160302010c030b09040b060a05030d02010b03060f01 80
    0x54152038259038024555124405c140400502c9080f00e1003030840144031301000026080c80610071a108181041c240b091405014100302258214591048048140514000420b4009500a18007031040c80f41030641d514210b0000602d01e8510000074440a0382401d119030a83d41e00049000301c0188a0070b00d11100201035005038010200c507440014441e0920052120420011680e00e100742c00c00e9091001c0d40341c0b0b03001030503a02c0044101d41d1140f40c1c81000140100c0c510410f420070252481c0f811148074900300c102207030488040da40302d40042500803030301d0000450144079040c0900088801001810701d0300340042c0c0d4650b0301a41902e000169942d801c81400150303044028111561300308281c0e100c480ea0b41141d90715040c500150015442c00014003d0700c1d22038011f102a8036401882070303403561155121149862009003115900032204027001a482c0c23030a200d03550038aa599000040c1316075003042814100900100603400f00c040c110014003211100120180035100e102210440f0240c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 94280854 1250 94279604 94279613
    0x80409061a090d030c0b1611030408060c0304060207080a08070e10231209030903070f0602030703050c011404030908100603020612071106090d030e010504020a140a0306020c010c0311030f04060504 86
    0x72241704014100c860541e040001103501303480301c250030648550700c10040c000100302c060b84030301460103200016004400401c56240307426000c0c5410501501d001407a003196684c84080071742c030840e00c1230040b0350100200002243c00400f101d1001500307454110055014081c02041100c5003000400c0015520f0b0003200c06040e08000d4420303990720010040100c4c100350308442e690f50000346600b07210344292000402e1403400c036003280048500c150010340c100440b80c1d42c2607031160803182d0321003081c1d0341e18180060710460441800707000c0c0c2e0007038841240700360400710b4840c00d042071030342150051403c00f00c0820050301c82404541c003440c90915016042d0f00e840c21f08035075441c0484040c00721071244d0303028042c18803400705150301d0f0402d003520100b0001507540106820f0301c1c0300b00d40180d803109101900b04042120415041000d002c000c02005529071655601401ca800240e50424140e40d030304a0034175603075014421b03010459600640c07641540740c40c404240030304100a00040c106501c03003000c0360411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 94282104 1250 94280854 94280867
    0x20f0613171c180b070827040b03031309020c01090f060212060a030317040302010f060906050907170c0705100c0c05011103010f1a070807080409061a090d03 69
    0x101a514071106045901c0d91140e40d54a0800c48804401a86401c1c0314000b01c0c080c82e03030300360300e0074010429200041c44c10b0907400040c0c0104900307071540d4100708984d40420a07907407440911507004081c4144007038454000d200441d0141c1105600a078000c00c0201100c2c642c00c0c1c011807c8684211001d0f0703407000034401d06805041c10341c0005085003c521107001c100b00494004d004210140c210401c40b982e141010005428114400540810300c1d194030360426091440890303911a000f4000469801d02c6d5480140440302d85601143e680c030b42d5101305122600d8440182c0c1c2e0032450134036024030701d681d0714055900b04201c040d0142c4110100000c0c0301080003001d0088140000d0060010866134030140005898a0b900d05070031102ca5281c00110300c8000c00407401d490698040702010100c1c582001010074401c28861509203800c08240701100c00103482d0b5004012451041e4007054803240b40440c01030075900d1980007050400c12030b14a040b180508001901c60728101220520309800060030159403c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 94283354 1250 94282104 94282109
    0x12050c04090302060a140c030604050604060825090c200c0d0305030115033b030d06030b0a020304080a0309030e040e010614040b0a0527100e01060309020f0613 70
    0x100d4105205002410b80204005100700025117042c4100309000080d02c6100400303c0344000702103030a002184107418241e1000b03502020161001901c95103800703045151543c14012003000c0302c1164007050700410020b82e01c0c0010400c8640a0081880c520006040c0ca00c04082840c0e070203c0c1c440e202240e0850402041121442c00b81c603004075005103040085c40d5a00034024640c4401f00e0751000d603130b00c504c64420f00f240d022003d9100e5460b81c046240060034060b4000400c403441100261003488100144018440017482c031400144042c1b440ca04580ad001c0002c20701c0c0200740c818010800892907001c100e440c3c00169240002d1a040e4a18003612064000300c10345400900c5e005840500c140158080800c3d160450442c1380866648000c01c01174480c03003129203400038110720301045113007031821000c60100c03030340c1c841c0042400c509015016620821140e01c0300c80e007403009003003000f0042d07803c01d80c0c050861454184000042600818400565050742c02d01510300000d8400101021402c010301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 94284604 1250 94283354 94283359
    0x1a0921070b0a0302030601110a03021209030a0606080a02090601020d05030403050f0f0d0b04060f03030504030611040b0703091e0806310302070e010b16030309110a03050d020f0601060912050c 84
    0xc440c1e50842c0c0040080d0800c5403420b012481e003100342c7c152030704001013881400d035056004142c3c081e10b0031803102d0706401421724290107108404083c2d0029165000380310107484600300424070400c03c0d00410600c00d0300503000b103056402030741c002c1c901c42d41e1100880e03900640506044d66a4610001001010310402c0c400080003040444c00c0390180c0b156821a528055007160b0a10000740c40702072038006420306220080c00308404000800004500d80c0100d16040c034403c0d40d0074102552610300f941d965100306070480000b148540c060080740e540c08030a04001a080e6940050310781414030059407072501800c6c00d40c2000c24100038015800f880c4101d9405400282903c0650060700c3c940607542d8009030141a0001464800220f00c0040040540f24881c024800035041040303681c40a80091900b64016102c3d11058850140b41c0d44030144079000940c890300003400030003401c20b4003d0800c6103010103031810360460001008565408600307030f429981444a0190595518035140345002c013000107694 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 94285854 1250 94284604 94284607
    0x50408030a050c0408030a030e0c0d031701060512070c0212030c0a030801120c051306121101020c03010504112101050a02040501110f0601090f0212010b041a0921070b 73
    0x400250502450161101c95028085529110881d40341c80c059401500d64540c4144980d5009501c240c00c40c40110041400b070341d008246120110751895046542600447d16604e03031099440103841d113450040c0010703d03000b03081a140f0501d442240708050a01d40410841c01201c50035551848031048c040440c01040703d9407140f0b06c40307003e034481e0071070321080d00031480e540c00000c0c41c450f00d802400020b40c0d000c1e042c0d14100d82444100448000c502d19500c500f181d0340d00e030100c1c000030101c0103151030764003903400e244107400c110000a00e008010941540682d042c0810b1000007125090b20342540c0904071980381011060140f2100d2140c04084455125800e000c00d000d02d40e2402e41c0100b059840c00c0e80c03141141074201001c1e950701c03ca55160510a0352000004102c0b09041e540045401010300c40094502404000315810120003a0417134201e4240c00a810401c1d0060340102c51003035030100d51510b051490420004601d00c100d0006081e00c002d9850755142080c40910440000d40401e00300c00c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 94287104 1250 94285854 94285861
    0x30b041811030706021617070807091415010903060b040902130204061707050d11040801020a020606010201051b09040c050c15040312110d0b01031e05040b010f050102070e0603070905 80
    0x3141c4004240c442038001d008442e400b00c0c150b4404600011050041318150400601e4200300060060501c200904a8024804082076001c810301201e0000d0190340d601003078000c0b01040202041602504100301c400660484054a03600614940202c0e50003a00c00918840074402090160030020b2000354410211120b0041202c8940e01910903a525541c6100002c000008040680c1c4c5003a1070b60b40128409100f00754003070000303401c0111100795003c034181c03c1943d215891426600804031a90158100d01c00700092541c3c248143c42e800401901041100c11440300740180910903116228000e0340c94004484c42c2900500032204100c408401f00d400180044401a014102c1034404800142442500c0b5510705200d005412501c03803440f00c03543ca000c2010400da001005400c01440c14161501c03034640010a8030074152106184491021407146054a0710583e20581600816034007865034a05002c1c0341d9002410900f900c5504000740c081e80c4840000070300d0001150721101030340382001d042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 94288354 1250 94287104 94287113
    0x200d02030109060801020a08041b050a080a050d03020a0509011d0d0b04050c09070e0f032506030b030a0c050603070903060504061a031b0f010c120503041e0201090303030b0418 77
    0x21412102c00510070842e6a80f500c00280c281d1003000303800000500342c540131402044110394207844e0454519195140c2c01da444c00450b0990202c1d5100824640000c901c01c814048203110307800c075980151504503e015000031014000e40104800c00b41044a030b01c84e030b0f81c864071044a40e10320b5400c006121840700015031400110000c01220202d5050140c0e440c400c40350704112081074003070350040e02c804039940e200d242846250300306000c51582c14410005209a883c40c9403c55100411911101400e4582000c9018064901d503401c401e010360310000c0700303174041621010080241d8008844003961fa8503501d4085400382881d07000a448030b46090b003800f0030018183d2040601407582e070310f15102c19000000b0552105086005103450610494040300c5a25090040b0404140b05060000d032050130307600d0701c1680e40c40707429284000c90000000c3c401131021003803080200a001095a1181e2800d40e0300007440982c00c0e20008060545070b064840c907036501c50b00300320002090900c000d017107a00079091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 94289604 1250 94288354 94288357
    0x20d0f120f060803071502040e040f020607060e061f0506070813030501020c2406030715031d0a0201080c030c09100903020324060a030f2009130309060905090406200d02 74
    0xb000ca58046c120440802280c0c1c03075000780d404440c140280500c8569440e281d04003040c00807182240d01c54401c01c1481f000803400e12594454412003001054146000980042c5071000a12803101c500058030b010031082e07850100b16031503d9881039030951192141541c5815402182c0c0009006500205015071303085400122285001c0140648a06c0c4801c0310200c0400c0711819a159500360b081024184000c485841aa1003405203600c0c0001e8000740e183d03800c400f8051800480407031a00684640400e5683c442403590b008107032004111700d14108014441510310402d030a00707000d0084a400c202c8024080d002c20401150080d0a6a41c00d0380075464080d034010100740c445441c40d0078840420b046080c000c4c030388810b0b240c1c0f00c0c0031010050a2500c4500341e0140c121031034203440340800240c0300315440302c007600b9024407180198451648075500e0050708105003134000b40c0130001c031900708000700c0e902d4110b09d540007030b040500080e00741c01900401621204202c0801844800022448d020508550 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 94290854 1250 94289604 94289617
    0x6090c090e06010923040305041a0405030f0f0a0f0c090204080102090a0801110403081e040602030a030c0201050402090601180e090c0a080f0309090a0209090c071101020d0f120f060803 81
    0x1420b50700c090381c03a10440c0d01119804042d00004040c1803c1ca01c01c040710880b08150054003a083c01401e003680d403c00300c102814120049501214045010080307414100070030305014000e08090009400f640080b42d0b91041402030280680b41d0201c200b000388402524018080c0c04500001d56585131110a028087d50100781ba040c010700318010001070b50001803060740b14200d90084403514141c40d68640c0000354103c1e88041c00140d81c440d80c0210300d940715100400c02450a6000344d0b890b00c20a15016080752030151280c425039041508110040e07031400d07005940900c007420f1807080f0003400031088918140c41c0d001040621170300750074420110340006010313070715844c03c0707500c00070298441c0c1d8000e4a442c5c80005003c03060b802400840340c10710304540c00c0d07588041c0d5881c0042c10b05081c6e03000a464030606403004039007040005650000d01c841c108010701c0a681c01c0c0010005025100c0d4001e26071880e1310003280401c0000300c2010000d0b802c42d04a40c2070106421000d00c0026140c0004c2d80d203d50018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 94292104 1250 94290854 94290881
    0x90d080d1802030f0a03020d0f020c04021603120506090109020c0f0d02010e0706050c03040905041b0306020d0b040c08010603020c0a0b0c09030105100f14131505030610030f080706090c09 82
    0x8203034010780e600d80002c0c948412541507008e0010400881e500343e4550328100a01d8041d4062346102d0392641d210351000d040c500c9150107542c9411000c508000e03001c0200ea03804654014206001c003c1c8546078800340e0342c1107039541b00f40113980f04d04113034225081c942d04103064000c1e405100c0c2030007603442e81500001d1500704290266a51540c0e10b10b0103413501d11a0342000d00c03a5400610040182d003800f03500040e403082c0203141804260b0b20b041c0e00b50031840010340080b201c695020641a0b4080b04500c20462200c0c01528208009456068050000f910500c99401050340020301c44441900c24000b40880e603a2200020b0780900b08940d40d688142c1009445a00943c41e00f0006000c50300f660040c40200c0310003541d4400c1c0d103824400351096a505074109682c016040740c4100c03003400301c14412500c488030079072018880e00742040201410400050140d15041d81b0550040c0081075400b650200e8259100d401d5650b540518030307003280a49004100501040c0101500090b0504242c0040c0c0200c1c1e801c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 94293354 1250 94292104 94292113
    0x209010602010902031b03030c07080d02011506080f06010e1003021209060f0103030c0c030b010909020f04020301080d0e030a02220b0301110306040f0b060a03020405010215010b090d080d180203 85
    0x300e80c0100d080310b4400901940c10707030000c3c6c01c04160620146da0f01600c0c0001405a13860601ca03003c1e294508559580b01c48282da12284035800303a6503083c07141406074840110080c00d6a1724204c00101002e6000c0c2043c80e0074030042e03001c611568010a0098104000989403a80c02c00d0840c030054003d40203808a45c1f0b10101034000a040380001049051040d03660b00381c1c0804507401c5840c12a80324075000da0880301056010b07000f00104940503c40c40c000c3c4024500440d45000910602a1665100070703a1030003030f401800140450100441c0d0300c2060a0a4900421a42d20010029150440e4080c0103500480460000c02c05400e850b11001e0fa0f5101d605014840d10054000341400c80382810003500e5413130400e03c08200c007440c0a0b040440d6121010001181e20301d04180021000d60040d080400402c1d80000d0400195070103203e0958441c16000306110b5030341c075024200d180d0340315103c010303403082070300f0060380003040822000c0d914000e0604070200a40005016078228500344004182d01c00d10a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 94294604 1250 94293354 94293359
    0x60609050f04180b090a06020d06031a040b061905041103100e090a0f02040902040c0e0312040f090c12060306091e050c06030a061d04060506060708390a020901 70
    0x30580030716000f074502e5448030048603030180c50b004a101405444152140074020407800880c400780040d00384400f0241c0000362147c91031601c9000c4074029a00300c41d041c007194007000003244400d0300c841ea018806a4201c18140c00c20110809198078503046541c1c02454140b01c182400d0700140070f10703c11450040c0240721143c8503514194500011a402030f00c139840b80158600245103025035011071440600041200b0b11140d000400360303002d100f6030000007281454a2402850700308690412802100202031405060000c0039129400030700840b031350152030701314894202d841824483c404511240007005140d480e0b103000000b0348416001503440c605001c0404107442c0180840070a00c40d4460001e200c0c0680030303801d02c06c0f00e410003401720290f5503450380b00107143c82e4420108001c503444c08130359040610f054034202003241c1c00948601e014042c00d020b0780e400030b10004110ba00b908000000c813441c0b510144000c114044a500605034400c42d0041d00b0300c8100d40010394044510b100b1107002c0c0190b81c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 94295854 1250 94294604 94294609
    0x11703070804050402210a05090105070f090e09030f0a050304020112022a0c1302031f030f03050c2d010e030f07020909010b0d0c060f0216030b060112060609050f 71
    0x564403001d0540d00041008202e245031a5005200501071400c0e1008442222074a0081b8440111382d01c180c555182c00410600321802c0c4102503010030710b1b08050409000000e4000c02c3d132a5140205100303100d021022886041081007501d041d10640544c0c15503c28420000403c1500f060303400300d000c210307000d045404641c074500a8030011070b8221b40c07110850003402e50300760703200e0301c210994000d5001da08120340050b12006101800c91601c000c0c05a070b00e042c8007440004d000308403450100b01c0c0c124480140001050143e001c0802e0742c00d441c0940e100d0f0208201c0600b0b10082242d1031000c2c1400690401c0c081c1c1c003041c501f0910f403a0b060001c1000300000e1007160b840f881030080603906031004100f01401440c0072000300d500310000b4400061851540004911211402601500c0c0700350003107000c0120f103901184102140c2c0d00c0e4409065140d403030705000b41006e036080c0001460f0344076100c0081c41c41e92003080b0303071061081c410509102d0255605d001400300406030241c42d001d82c021100c110b0450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 94297104 1250 94295854 94295857
    0xc0608060d0312090311010e010b0906100203070201050d020909130311010e0d1809020a0503010e090a0807030302030402010e130c12110714120301030b160f0207090c0c05070e011703 80
    0x3103416441c0c80c030410f009010070030020300703040100710240168002a03034a00b0009119009042c001c10000003400c100941c00c00100038001000709114840d607000d8100c1032a40801624003a40c0d0a080164450b008803625034040d00404a0007034001340103204210324944202c494850340c6000b43c603508404d0b00384075692400d03210005034000705544543d402c4800c080c42803107062156405002c841126588880c0a14107a0b8808100031002500120051100350320498520b40c11000074402025008602d654080f41ea000b0f11074041d040c5640840040c3c2503900491982000b240003c240100c0c400355030608800500a210070880000c99100000540600301d12601d0300c5412601700035400e00d503065130340d000d04c0c4203c2c2c00c0402c0b0b140181d80c140d00d0301c8007040014601030751161011201524003403120b61921240102458100300e0f0f43c010702030030b581d00891840d01707644c08581c0c0460802e0005109492030b0890890003000f600c2084000039041c0448040b85058a01c407030102c04261002103000f541e607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 94298354 1250 94297104 94297129
    0x30e010207030f051b0f1b031b0108041e060e06011a0d0203040515010b1c09081c06120302010504050c0a03080f03060103060510020d020c04020309030f03220c060806 73
    0x300e0821202e1008850240000e040d510210070401e04000e1085c510309403c15203409402480e07580071166460422201c030003140c12002c41500100350750200000981c2d01c5107107900000d4180004500414240b2a000d03074512222490071055042c0498546044401070a002100000ca4041c110001c601c07503598440c00b0701e8421071680d00508084030641d04000a61010b40102c403240728660700400204080031f00c20b4000e148800c0441d0308c90781909641c031140700c9003150004450380381503101c200140001091b104010f00c20b000f1805000d4000c2c4110000304100d030400000e41503c1400d1400300b60781504154807880c1700d0400d4031580708010302801560001030000078500017090082071050309081c030285030b10a00515000c90704a598001085d4150a0840c0110058002d0750f401d505031901000348001d400010b450451461418042164582c003d031400080000300000100e4000c1c081440b11340c0f089030200d051a6102005803816103103c1c8528400c0c03e0224424100081c0c16152100c0360004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 94299604 1250 94298354 94298357
    0xf0a080a050622150e0f0108280f1115070219060206070c05150112110901050a05040b13020d0204170303040b1302010c0c090501050f030f030703210c080403030e01020703 75
    0x807101c08105204090014911080d030700400e2080c4c0083c1d0094040e040301c0c02404040108500e0b941005c01c035904115010003001686015142801100000b03209403110f502e40040c900d060111240c80d0260001c0103001040352300019094034400f4121004000f001e03054070880752551440c03969540c84100c07005501c140c9002da0061390000e551980034260341c6000e01e20440c191588082d0b0018103202c40d4000380c01840310355101c041410100300801d00d0081e020030048801c1070b52585408001040d011030b6018a40c003450316401141c0e0282c84480301d031900c40c1d42140056440340b44001c030510007900700d803140702c81914151100625a18011046034003954011114042503543c0885e03a02c4540480c010483c100b003600121000800c50004810300604080c5002054551422040040002c1081d0040c1d2080e0026148d0002c040310000450381f00d580c1c11701308104041540f07070703071004180c180c099204500c5003001d40030540d240c2e0113900c045c4554441d071401c1200030a5295071508078081c4400060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 94300854 1250 94299604 94299649
    0x190b06010c1b1d0c160503070533060904060e21130f03080f0708210406240312020f030706020304021306030515090c03030a03091a0702070e0601050f0a080a0506 71
    0x50011750396002185007502a05c110ba2074034055980b840d01e880d450141201d400400c10391798191500c00003844206c0340411503d220f0313070ba05080b000038591200140004240d240e071081c01ba074032a1420b002901c0340340c11900407110b100b40d642c174002107035520201903a516138840b1240030810800400741ca030140d0750801026400c0c42c0c40152200507d41c8018400d4804031030070f00102000a4841140061601c04585030107854205860000207880d0380c0503104c1c844001c0440300170444a03405541d00c048030b400101c01c9151040102040c1c0c01e10100c45039036004c46c000021150240700300c036001140070742e1007902c140c0c07003100040400f00d0484155020040c81500300312498403002000e02c883d103400c1005001555006005040002c1ca56402052103c01082c1c8659502050201003000c004241d041d90b250186c1c180303050b400c02500c820b098081c0401c60400e03c80821003591059090700c5120b281400d005a644240b01800f50062508942612607282001c1c00107a003400c6c03011805095482061100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 94302104 1250 94300854 94300867
    0xf090d030207020a05040207080d0c050f090418080304051e010902180703060e01170c18011e0806070801170705010e0f040e0105070e010f02190b06010c1b1d0c 70
    0x218081d50118805a90004c240e1a001c91785941d2440248004c1c0e01c682c4041d941d40d42e031000d080d01039410016080d001d0003400d10180741e0021202d0100c1d000e4103000c48000035801100c1c04680315480d901980900046400300400081002c00100c034a01011408186101c40c10601b440b00d0907a100200001d4014885158a54900381040c201c5a00940c01e03003030220751541c50700045444010264051503014290740c1080d000c890b001d008144c000310302600c00c0d00c9a00242645c40d04028418861501410702c004c3c91070495030861380e00140901091800d884041c10070b00001000c1010a00503018a03c500300341952569500085e10000c90f2410b8540404c6269440204081202c4000b030940e00542c6601035040361020071702c0b49610428843d01c512240d140c020300018011200313940201c0555000c20340d9240f00c3d00301c440004080ea544608842150783c0d80c5c1004840c0f008641d40300900c1c5100380c4250041e0203100c0e40355001956080c02440d00d004078513070840002e400041d5020044180204582c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 94303354 1250 94302104 94302107
    0x60607060203220321050408071101050f130302040c051e030613060e0f06010c05101d030a110616081527100e071b02031e150f090d 58
    0x145a001c0000f100c001c078040c91603103030f00401e1032504004900090a4454414001c0700d0030144440500035041c080100b4900f65a9000d0b60303103e01c1c50064001380096490354082d80c45601118074440c8801d0066844520788942c074805d03042d2038007080b8411030a01d0507000403144510142c1c3c07140b81c074002640186140303569080d4071662015004a030011912024000092218080c1c0c900812594038400c2c1c0618081c3c0d0800700303081c1e0181205040010503a241e40100d540001d10003030b14007001c81c00203041c002000c0c1c07403601c440312002c2c041703042d0102144181e03010780c122103644011590a829541650b440e04903090501c038a0010020101d800c1c003000c14015162980b0f00c041c240d002a1103140c48800e81481c40c1682403806c444202d200b000c08040210a02e0030b01245001404001c00c0c18800382040300000c2c0c000e45141d5100944281852400c03000e640c1e0410141031400148035902ca010032038040c00907200e51103044e003100120081310114006941101c0c00900c80c40001c809040a6000e0910 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 94304604 1250 94303354 94303357
    0x50609060405060f0316170715110307020909100605060307020307030804020a030f08041505040302060d0c030902040f09030201140709120302120307121505091b04030b041103150606070602 83
    0x199420500004c080c2c922910f00700030441c1514406005204000e02e462151701c5c501410560841441d0000070082180030038070b01da60f214003541402c0100f80ca800c002010b0b0b19501031207001039484103600084c006184004500010758003040072042c0b1016481d0400d021483c4020b0b03c800e40107034420030030a0b0200c1e01c40c40110741c0251000381440c4856559484030074001000450035034280100040130083d11911001080440f42e9905100d03091070300d0b41c1c00240140c001d20050076a51610340c2c1100050070f200e60b03c00504a54001c10401a80003c900e940300241a6018118003641ca40016504070304016925584525007030340d15611400d080c250143d03410040e000c011025807050b0107409190a01030000355109055a650340a540000c504040d4162284a0b10b00d0032202804a000d00054640800d413360100d40c0c20960029000300785101b1420740300350f0b440a0410507009013440304100c0c95002000a0a01c11800c03590b0180c842c0e0514130b408441916041c0c0e018a040040e50300043e1140c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 94305854 1250 94304604 94304611
    0x60a05040305060903480a06060e0a0b040b0a03110619020c1804121b17071703010e01060f0e040c0e12030a0813050a050a081c050609060405 62
    0x9041420107640350365182c900380007138560711255000441d0041130500c03004000c5100405582000c02011071045111840e4582c0c079443d800385180c00b14100e0542c140400038005020751086081000d20ba4400304a6074403481600e042c01c5990910540082614083c000e824180c140201050700c00e500c1c40d41d54040c0c42d0184a0343c10781102c03051000d0b000549843d80030981c09144d40d000b506111181030304100c002c80c80c81308c0c5603503003007254402d00000c84c14187d00c0c2603104102d0b00704812080d6600f40b8020300108040c00085c0b203001e0080c6203500041e0920701034084580301d80c041944041100101d030440340000d00450b61005c07800c0d80100492846202c040440c0c1d01c542c140341200e117414001060075070381440e90340b0011620202c1006240d0400c8404400750314000c7c0f000d5800c0c02c0d80400000c2c0030702ea0103071030001501880365211090290500061445640c804100c460b41000e516040003030303030025800141607030340488000c08021003d004252080c40b00900c000c04c10340d2040d080000510300907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 94307104 1250 94305854 94305857
    0x504050f060c12040f050f060c060412050c0f0705090a0902010c080304020f060706020306010f0203030108070e06210d030608060601080403031d01020f070212010c0e010518130615080c0405060a 85
    0x8040030b04424408000a00182000c5d2075215011070500301403280d50b080c40e00304580100810010031101000104200e60040d82c41800c22018201c90b4808403480d0041c1640858180104d5800306d50301000040c40d1002c0310010385012103660368040240c0101c0f0145030000c0c2c041441d0082d01000901c2e510f0086500510091620001054480c04544160070505044070341a45c0001808260341e0020307034010590781e49200540c0b940d810404600d40300c1844d0b11601c041201c200c0007003211691503e14609070300c89a43d40d0344985400340c0c0c040650340c00c0100324010100740780c6035020852030300220b882440b07100180c46540c420b40350341ea021002850029065164004c645551566142d07080c00205403828203564000d4907542c1d180100900c4000c0c030020310381d00740e142003403003803060350001644842800c09003401c81e00d81c4410141d9081190b950321007190302094030a0240d41190081d800700085d03c803081346d810074031140402c0c15101c8540680b201c50580b0020f000411003803905d400144a030341c0d010b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 94308354 1250 94307104 94307113
    0x2030f0328020a02011811060f0c0609060412080403140c2407031401030b060d15050108030406030c0e010903020f010e0a0e09010c0f0e01030f06030807030c03020c010504050f060c 79
    0x3210315200300c5155180000469070000792240f41d01d80e09024003c10510300e8181c60000449a540d49245c11038219440c5010300380c0403d07860f0b840f8003440203448050070840c05441c0607240c40c94485840c1e1034100d40442d80c0040d0420600d0b0054440d1104921440e4103071141e40e00c2d40d00008110760300341c101d0a0082d48511800000040e560500c0c0e28610041c034466000308a01d0401180150568828080c08c4888840080042000c60200150150001c1c801e4070402029a9942020a04d80300015850500302d0b0904e0000114104000b008100300c60441e5810060800c0c2c0c420201c9200c0840c0c40c0785400281c10400610140c5450111666114414103118a03402d8502010525908048c0d1000240003540c004002188034207001d01c0c06110580d01d0900400851207001400302001e20805904050740c40b4200c014040380e5506c0309002c1c640040304036880350071038a8004d10781c840b5180308070014001c0700040d06265005200f074a042da8001018298158110300901000e504a100c80c0480c0348075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 94309604 1250 94308354 94308391
    0x91104080109030206070206060d1104050c0909010f0302030606060403020306040b28020405040606020c03070e0a021308030a0f02011e050a02040510090e010f0b0d02030411030d03020405011b0302030f03 89
    0x10034410b05025901c290081c01c668a0324410103410848014009405820515054000200141c440c40620ba02c12680000c00740c84008205115014515541c3d402031903600c0049240d6604c1c0700198100c0703108278202c5400d41e81d028180f066600551100079010b80c00480030a000401e400d44040e8401406c15080c99400884511a08400c070009810021a6800a001e21450510703000d00c001904050000704800004100402e5440645104801407039551002040184455804803a540240b440f2030030750070303034450b215681c881d400700030b269011074080b1120105c6640103000311a12410b40c1206200300000980c8110042c140040590346500d03070801c00855190307a91015513240200c1c641d07640b9011401c0c0381d060700300c80d001030700904a409184a803c00078662460100c64066114a0015860303449901d400c40b02c0c402e210311000e5140c0552140300085503070541c0900110b0700d09903680800c1e090701e130520300000040d40c10007070016003007000701e680490704240041d0b8010701014109868a42c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 94310854 1250 94309604 94309619
    0x30f1f090e0a050319020c18011203120c050414030105061c1112070807090212070c020303130303030509010609050402032d03030a0914030c0703030e01120e0a02090916091104 77
    0xd205d0f861358407a01011000420b4030b0341d41000201481070050754440c1c42580280410644503a0503c2203130b000d03c21100d203100c2010320504028076580c004100030302a50f1303640d41002d4a2a04503002d03240c265685003000101a1a0501943c2e008500c0074080c49a0386491884250720f00c401081d090f290304041d00c8404455444100d25241d00a2060015102d04e81c144209642040d0059225001550062022080da080814841d642007030607401e20f058001140d101090440c02a01d2010b40501c001c88e8000042c9505900050301c0740200c0c01c000c00000382c032110210708071041a00c0280d090750241241081850402e01c0005003454060713001d9900c0d41450a1130b524603401251707507829564942d9600070402100e44902c4641c8103002020350309010303c6010050f0341d10304610000e8204204c5114402c0c1a9008000f036902e42d190035202480442d00c03070f41d03200743c3d100d84080c02240200718171800900342490220720700002d444190041103e203450700f660310000c0d06400d428154003074800c120006451 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 94312104 1250 94310854 94310857
    0xf010309080310150807020c06031905270312040206070807020604090912080705030f0403180b13080303010501050708090a05090a05040c0501090602070612020d02040b030f1f090e0a0503 82
    0x30300c0044080f150440c20440a0741c60300f04442446010320031101d05110751b164001c41d44440c2c041040d110b590300d9030340e0380d0030140c81005101e518030390b40d603d0a4140034041d2014030698070030380c1244000140b0303170201c0780d20b0594910446140000c500100c6010400520b016001411004c2c002d41c0940d04002e1031383c0000b1150381c07056020121080c2d4400c0c0510412800701c0c9414880d504609010a842c5054000502580310003070600004070b0207040050200360041c0708951081c220b00740c15407078440c0c0b16140941d96500086140c0c107454140b1700001141d40b0000101c90603104180d440c42d007400303c1036035218031030f03001051541c1d440301c580c050102d0f06e034950503481d078840d4540700c0c0d01054900305030801c5400c000342c9400803810040003003014042d040e00082c800084804034613042403001e03c003a090384001e004621350403407042c0c00000c00040e5840c031500514010f8400c0705103183d00d41c0741d44480c0008a09507000728001203c030644100601007285d8002e80712924144151030a41e12075540f60f0303045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 94313354 1250 94312104 94312111
    0x1909020919080d1d060f070f062d060803040611030904050703240b0313050111070506010806090a020a14030313081609050402060d0b010203070807061a0105180f0103090803 76
    0x20b50080c001608929070041d0300b944c0400b0714102100b03001444070041800b505c80c0105a5032041c000081303560802c60300d10380310392079903401c203404110f10804c0340004401141041c5086803a6841148415401030b005e04c5101c0468403148000d42c5494a0b001058424403080c01d2100021f00060114800540f142d0140d607100b00c09640c3e000070f4003008805000c030042c1c91031400300700d401c1c0219828010b002c040c0003100c1c0c000000640c2c111012420703140240c0503040c0341291420031040030540c80704000000a10a042e00e40030b2050714116590034106c0c0d0f5869001d8031019600c400744041c10800100200780400c0d480304090240c910f81803c0c8075038901888210b038424040c81d0311204a406c14200482180c1c0007500d520b10701403156003000e4001274070034005d030f5484001c40c999411b0b80c425560300800407078041c1c5038089080d985515190030210005c022007038085200ba190141e0015080d880380044900c240340500803058205968024803610505141d100c80c141941d032160b82c40443d42d200e018510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 94314604 1250 94313354 94313369
    0x111912020307150603060c02010903080708061c05030c0c031609020d06080604031205010b0a050414010309020d03020601050a0605030403020d11030903070e04060606031512060b0a0e0907051909020919 88
    0x141d00e1700c1e601d4140211006030004000b164545011000002e501005039900021241703000d1742d80e40c9403440058003d100c1031480b120a094445948000c10034040050720b683e022813001c0e900800800d1052588a00136456802400d0681c0c00e02480000c0c40e40c0d000d484c00913416040012090303140e54001d440e010040c0c40503004120f500c411a107582101d801110301400d2281d05060a000358031001034098069800b402c50f0182c41548082c42c9a403080d8011103a4640086c44018045020b0602a494400a0080c00d016140000c40451120f0181c81240d0280303a040c0d0007092000c4091600301c1e80d0804001a103103090108020600386940d08101c0748024141c166142c0356203007840c0c60580b0803544940c0c0404c00f450304010320151000c02d001001d00c111040c40c411001041c1851508030b00a1051800c840e5100240c1840070582e86007000145228170a25011946e010b9151001c1090320407180b8024074800904a03002c0c0000919034014004901010b0040302c01c4004110182daa02e0f200c0e50000e40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 94315854 1250 94314604 94314611
    0xd05070216081c140403020103020d020d06060908010c02071a09030f10020a0905040605030c0d06110d05090d03050c1902070306020c06060316051509060d06030b0711191202030715 79
    0x3d50031550141d07074103081c01ca00708224459040340031405207014a1102906140d404511500142c05540465483d83c8418008010464492001070921045800f23051065807070010080960350001982c401980c1d02c616540c5666005084062403907440802040e826014404580451680400840303181d0411408050780b5500d03030b100000c00b000034550146124a0412604000544020410000380082038030300b042d4080b10341c00c1500142080c45400e42010000040c502031421150f4803840c0108685000d5400109a03503e0072401d4400556003011102020080c0105003c06520418249403103401540d80d081d9030780c1c1302c01c001ca0b0002d425005103a0009010450f5500d02800030100c02030700b02c14070a04103818440481c80004000704054091400028049119035910054603150020403d05012890700c81c90544804032083d0360380b81c00703e01e0f03122500300ca100000c141002c14240e203004401a800c2c1545640b00c0050203044c040c410340c001081a030f40410b015642c004400302d002130011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 94317104 1250 94315854 94315873
    0x32120406020334060f0b0d3203030702070905010801020a080115020c1203030108070815070f050c010c0e0306060109050f09040f1208040213090809010f030f090501060e011a0d0507021608 82
    0x350a0320300c0c5886c4540314103482507070540060004114003420002e00080d904c94512a0321220858040c12070220040744800300800c0b05856000a50400b90f50b5840e805100740c1c0da030307048003074280d0240620b15404503a81ca070061150140c0303013454074104030041c0704581250401401113140c500070350840310305a400001c01441710000400c180c00c01450b11070010500c1e0010981c0c131020019010705014100400c1520fa05c1805100b14180c0303608410340b400070486617080c4100540850a28000940240181d0000800945c000c50444007256009000e658401e9082402c1011105004008541c80d401c60103410000c01e01d050a03411700c9003402d468945480c1030074010841100c0300007120074111800d1000e40c5d0000b804d031030181c4158450a0829484100d1010000d40103091300001100885103000d40010500a0540080c000ca6496100310309c40d0340d03250012100c0c01403032400e500c40f4170070041202c40040324031640010fa2000d403500c1902d0701e406200e903420440c2c458a031702620055124076140c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 94318354 1250 94317104 94317131
    0x306040b030c0310020a1404060305091b06120a0908030903072f01030c0c0b0901020a110d051603110618010b040c0801060c3212040602033406 63
    0x452040e20310440c010300642c40b00c440000d90720204900000030040d00407680f03509440c0076088004009100c450207549480d1100e0000f1300030310080341c103000310f4401e000301c2e407400410705c4411011070a006400d40345005403209440b104403001402d03412b1440d0781d4a036004003003540140518012402c140181d50740720307000c2c00c000c3c0341100009950080310712601104040c00c50700e4180c0d01c1e0b803581b080c01c020a0200c0c1c03401c8240da4400c0221005050300703c8080811440c40c006600410307039810765440b940540c980f5000565580c8140922900207c0d00411082d07040204a492010030b451091a091102d02e612403015410070f2029501403c400003807200002c01d2031000c1c014010f078082c007501c042001d9070030fa02000305400c01c10301c20002800464403203081480240301800302c1854110445130001080c0f1041108400c443d00449120741c011406048603e2035050100c40072202254015030800318010301480e110540307000c42c9c03100b4545079003004408200b80038459540c035000300320005a0740f042401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 94319604 1250 94318354 94318361
    0x6150409052707050108040204050a0209150c120412110a030609050601051e0d120c050105041101260c030601200c011107292803110301060f0f051c02030604 69
    0x4000b030050b00200010f01c52070364421040d0b03500580448020603075071a00000c880080c4070304c50810b41c00c07103001e54100c44003494000c020607000040304206c4052203646140f084143c0a40c2c01444501d4600741d28481c04aa007141c808030303d002c802044482c001c1d9880d03039614102c0c0c408110441d0140c101000400aa190401a52031002c00708900d011540e0407400016202040c4800000c05002000240da01154414070b0744455441d40b0000801640c10181040141c0821055406000a0020014103050840344a9070282c03500c4220011481d038039400d1344900c00c3d030401444a810010341d0b0703902200c00368071a10300c0b07a031640412000d40480f500c41c600040c080b0745403586151640d0f0143e0010407220141000f0380f40540400d60346424240b11341c511100183c8034205002c3d10b10045c0c24140c3e0303a032500c013a003c0740c10624203450402000410101c441d5542c0000d10a000c04500c110414054460040440400982062400900c2d20002034007184c000f800000408490703076404820000c06050510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 94320854 1250 94319604 94319671
    0x10e1302010c0b15060403050303060918060a0e10020d0b040e1b0f0a050a0e01150c1101110f1905011104080a080d0906090308060f0d020105030615040905 68
    0x104055012055900082c1c40201441401403404000b8000260b00000640115403c0f036001041c860ba40d650368140a550381c0c00542d451840386442d080441c081240c0711442020700c01c40c032005003080e59503110581005100b00310405000c2c1c0a800d008103200841e510052002d8121003c1c00142c6080c14010300088460400003c6d040d90311070a1034011079040301e00c081c05610821194510301c0c40c10107000c0f80014a20f9400b10381c0101782e4400c0030400d0f05044030001c0c16590325000c040e0003621101001c46840c041001c014004805d203403410f11780355201d03010312004805242c3c11a084a00b100195616043c61044110701c0055408d401c10100502800344100710080d0002d1a4145403d11049540740d0b0a11f6070001d1003544c00041c030801c0400c00350030a00d000d5410401c00c12150900c0d0070050301045046800360300c00d01c181c130791804462800c4600c00b0300302d40c5c042e50b900341140d41e600300b844030a100301e81e41e0021400050000040d10300c01d600510f885448002003c4107085040c2d91200802034001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 94322104 1250 94320854 94320871
    0x1020436110c011805100b0103090f050309100306030b0106050901030b030f06150301020c030a20010908090103111c0e0304121101090803040810150513060e0627070e03030301030b010e 81
    0x22154001c05e01c0002c00a04140c4000f0000a040b9020f0340180e0090040510040106035002490014420080094411410103403032b000d1000720640e408404075400760000528445e0032100600c9a24420b5000d0004074006040008024100a00082c81c0810148900c9a15030120040004072212881480c0601006800035030074070f540708040c0d50300c0c1d00440b4552410441d400d0a1104035030310080e0780214244c850402017000e0312050800c01c840e58082602640864280929282a0703c0d8440440701c0310315131260382084041d80005103001030f0481c1d0170351546511007480003040c85058034241a010b40d1040b903605a84031400b60000d044480ba0b640101c500d900240420801181c000c0740400d1680c001c4040014412000b0031407149590541d003155801c40051965020408d00550226058590303009010f09542d036008100203540c03986a0101e401540c0c0188401c1e40c01c1546410203410008a00b098281e803841c81c00443e2a58000740d0080d2042e8046030010804442e4221034541c01801c0c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 94323354 1250 94322104 94322141
    0x5010615030209030c0f21030a08060a0302010203071106040f0b04090b0603010e01030f020a1512150f0e040c081c0801151704030e04050c04061101020436110c01 71
    0x101d80005d0710360b01154212402400460000380d9555580302d207080184290070581e864200d40708645540d42c1e0411400d803000b10364a83c000c600c1d14584080e50008581d8164000c1d450961150f466210816071100781d9038100e40144000b09144102d800350700060320350842d07400e0b196032070310007010f05032102020700034003c02c010001403050440c3c5181c1d4a0550ba0482c941103800d00051011910300c682a80c0a040f80ba00400c24000c1c00720b0b070004110b4000144005c003030004900040240076207006c00d2050b0540401c1580c4108414034cc0c034020307d03a00c02c1c090340c040c444240c0d440030302504200e440105940380d54003150304645015000924140904001c285041c0c080303004600c0505542603624080303480c0380f4034400043c10584503141c010840c581c040d00610290030030302d4002d1413580160103414049181e81d01914840f9505109407000c6418000403101b00c0d410b4031242c20b140e41d0409021041170300c41815082c17144000c80c00344900382e8211408056032000c4240029085408068414103403aa1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 94324604 1250 94323354 94323367
    0x120203060604030f0f0203012912031801091203081f0e01030809040b150c210703050f190c02182502150108030c0d05040312030506060d0504050106150302 68
    0x3074007002c0d0350503240d100100702c1001000741070a80b60a4441280290301d90700704103001c884030034100149030700e00240d0040701d4030b140d44034800c03c003110459403030320501644140490750451703554981250403c403040c1446040a911004c003030144140d0484188e01040303400c414001e41803600302580c203002c2c41400c01052080d04200b1a807201001c10700c000380001002052480703695a89900c40a81100010000c001c9181c09050103032490f0040540c81c60240141d540801601c840515907013404a4250310b00d138a03006151740c058807030390001d45481e0086403040c824051010f00c403c092036014101e079240c640c002141841001a0307034140404403044800400b090100c4d1103509080d0040040350001001110790070010224589580260740f08000c07007a140c0001000300d40800188000524a82500d42c4000541400e0b21144140d220082107403a0828404158501c6a4083c680155005150918042010f0850f401303a881c1644e054034940d42d210010020780c01e01e5480781400074440d080a505094 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 94325854 1250 94324604 94324609
    0x609030302030d1a1c03030b0102010204050906090c070b09030702040b010c02060304060b03030d0c0815030703050d0305040602090d05010b0901060905060405090c07020402030405160e0609010315290112020306 92
    0xf920212000316a264075410981c0f500e940010000c00501401502810181145004040c0c03194041a800b007032031302d02d0242c0c4c0ca5106000b03c0e42503034005001141c1a86031042404003602d030007026a60280400d00c04200042c1d09038002d01e01800d101402185c8900d800d0041004580002140a05010180030780000580b6100c0649900076004440010380100c0035022a01f140b017036030310ba001484c1c64113451585150b0001c807100e0003040b04120f030040400d009418950b54482c40e00010f00f60f9440416000c80940c800e41109034018412030002d400c00a030940415007490303440500b00d4080c1d4555441b00300e90304220710414010034092030090304091030100030964a10403030103140c0c000e244210003c1c01d0340943d402260012030740504115981c3c40d0606109860301d4200741c0e0b00d409d032080508005080422000075a0203007100510112040c1d18565401300d001d12100301000115481d030400070071105060b0310055000d03560380d46441c8030019850004102055840c0410010740c81032003400003d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 94327104 1250 94325854 94325857
    0x601061202040f051201061e061214061009030c06050406080708010f0b130312030203010e010b03070807030515150d14150d2d0308010806070c0b100e011509060903030203 75
    0xd0354242c0d0f641a018031759603e06400f501c0303960404904203109501c040c0304034890b005240121072403a81c13114008036800d15580107803a401d508e01c203044070007080410098079050241548102c460b00388070111070303560340d10b0b0034034810030342c1c81400030641c0810100a07103a0003d42c19540400245801a202d41c1021824072680d83c003406401c0940d000440d07101906503410880201641e0482c0107034070803420480d0010069802400780e1070202c1c20010000800050080c04c0e030b40205c0584d00c4001e810b60301c4c02c0d81100100801001c1e90041c4c0c1140b01c4400c800c2c0c6418076200001c4080d5100140e8500924207180c1c01c0e0344049180800c1e180c80d034810003440b125030300302d4100d03641403c41d411581480242440e0741d25611030800030302d0703120b445000039084404401100103454030a8a5240c1240e07696811185c850701d0448521011441000e442e400082542d0119a444165103981017410b9880340360100240b2000d801000741280c80040c01e404d01600302c0e0081004024902e420300d017a41c00c0d690000e45a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 94328354 1250 94327104 94327109
    0x50f0403120204030c15030b031902010e13091103061006020307080a030b060301090b090f01120609080c01090f0c14060f0f04030f060207030306090612020915030607020601061202040f 81
    0x70001584001c00211210390120740c011900425803243da00d03100c44001040414050820000c0b82c6085180580f908006c22000030441d001c4620002540840c5c0041d15005174a2002c0c69100000c03044003000800c0e14824114ac250141188401603030341501030529142024002c2d00380c02c0d854040400c5000d0307002046803207040d400708110783c80d040c4426059000d002041902a80004080700128664909a21900584004407414026611131283c15489540c0038051002c084802a180601041c0c4642007805070070320030030505280a0000d2190b50859411a50449503491090114400c1c04002003020002d492612100441e00b10b0141c00541144101d101e4030641d1100811350460085500041e5030003160801c441e55444040303454510002c1d489002c084005c40e14050020039920b607284191030a807810400e0302c0e40500016001c110140b48010000305601e0403070882c2d0f03805070310107110942c006e040980091030310b541080c601428454820f004440c159206000401191315040341407000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 94329604 1250 94328354 94328357
    0xb0301111602270a0c0e0604260102031509012103110712080a0305090105060105091e13020415020c010504031712180f010b0904020f061c0618050f0403 67
    0x440740140c1c80441c048003035101c60700034402c180750b0790000754801d0015094803078400702604110000d284981501d60003a102d42c44d5030051018401408440e1405015030300300b20b5a41c2d61021a200e0f40355010742641d20445031050090080c0c003003143d0300c0c180700344420302605125540e140395201100da8101e1500ca0340d0409010442a403040d44c0320120180007000c060541d4542e4642e144020341010b608507417141c807000001030318090009041032018480d090150405a48a43c5418076080400101c54440800154400030310f4002021036581d040007501d2030740c00441c0250700c1c1c03441e00610701c001003400408481075400c220116100307603030b00c14222400d032580005580b42050081100c5002c038027840c0a690b4400c194541400310340c903101e64100d050100d803041200c14a08100d00722070300780d03004681d605401050800c042001441d006224941c4e440303015020302d08002c5a816820325500c020540585082e80c4c0d4403082c898007075042c0300c0343c2214403c0302d8144100c1c14500048a00900b000300042e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 94330854 1250 94329604 94329637
    0x21e060408091f08060f0d020f0909010b1c03270e2d250207290a030207020a050111150c1309060806070c080313050a08030c0d0b030111 60
    0xb1400e903544102d4140704007903e0703820002c0181c000d00151000c1000d4821610851461010070b01c0c500d0500d4005940c15809049008601049030a1105869000c1c1854800b5500d40d01440c01a032a4080d000b41d114004009814003a40300b030034080c04105040d0048400040d240c403017850390300107810048003224801e540c13400c0595599805418030f00c0c54410402c42c01c44c40740b8030030f444a030381da4600c050051000045058900c2a500ca2a1040740042c0d0042c8000d03800c1101e08114020f01d00d90540c1c100364142c502020040c0d926140c03c041607020700361510120380d01060050550130901c0861020b8102824070000b05402c0b44a81070707407088040071000d144d4104800060400401109a482d040348242d03c0e03040258841c80400c01404840c05001c1d06881600c0010381d2940c0b080d0305203584550020764151a41e1240311600e2820f20302e201c025200b51058015580018107050001e42c415101f1941040e10303445504241c0c010354a807448454440e80c180034089881d82010b40485150380042a101e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 94332104 1250 94330854 94330867
    0x102040e1506040f14040506100f08130b040c0306181a071202041d0606090607030f021501030b010618050f01030b042703020610030308070c05010e070b0406021e060408 74
    0x2401d144202e0704804488851140d0000380c501070000c500e81701240842e02031000e0341d01c240500c116002580500d10000c0c4042c804a211240949101c80d0003001000150300b01a45603160700c406044251021545403821090400074041340c0d1048404c0c00c0e500d454445089916070712080024a125107aa4440034480c234049002c09020740080d03e04a00b40301401c0d500c8654a01d507104465001080182c11250010001801880c01104443c0d210300c0c02010141001d10035201141c400510492840540c4145d10024400c8117407a104039001b14843e40c0900b41541c10840c2c0145200d0008651b031480c6039074030030f0034005950752080100001e03c003072078002151224017000501900c0003c0c03880311100703080d1010090301c80c481140744914074080c1c0c08a50607510303129402e08030f00740280b00c054006074484005c15980c1d072196411450b12801f54002144420340410201e08210155100101c48507000a04000780d80c0c061290380e03541c003c54075503591440018410940c90b0400108014030030813001400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 94333354 1250 94332104 94332109
    0x601080109061d07120c11160506042108190e090702070e0a02090a03051b060f07020607170d1401230f030f0303070815040b030307060902040216230102040e15 70
    0x3e0701500c030442405000d0080302260182c1020011b80c7c4094060094203c8500e40d00241c0c00018202c070005448145042d02e0301d0801090291442c40e41004400c0c410860808210b031103002e0400c141802d24aa08500310661000d01200f5460000030f000d0200d0f0340c200a0010b40101da020100c0d034080070351140c1c581c2c420344000000d20800099513440f91103600d005c0b081c08000560b00f407088410a0480c0c05000d8180c042000034080d24a5040000100300072180c0103040a0006e000c00a1142903210405078030541e180351540c11150140402c5551040b00c1c200907000c4800141c01401d040341301101c1d030113002e14410901c0c9400307540707a8041ea01c3e4007006034141d1130030010701182205c00d8090f29142e060025000f000000309495601011601e000d01214a02c0c09102e114003d01e4010000c0d440c080450b551000541108101170ba48250b0034402000a65552031000424900c50b09240e504c01030400c2500365812400da806c000e143c2c1c4180814015941906040c64010610b84000760007070221800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 94334604 1250 94333354 94333367
    0x70807030b060a0804060b090405100c022415041a0d11060319061410030c0314090a05190203070501050c070305150a20040b0d0e01090302060601080109061d07 70
    0x203580c1c018a0000307502c10241d0703010010728045c0740b103003505006000052040020a01003a28040e006800c9150700c800c2810701c0354415142141d1303034015219100c40c10303e010304420031241c8031907600400c008200322000c0304c0c0c40106a080d2004032001c210401d09916841000307108820500d00990503000c080061110128104d030501c1802403959035a442c0c4488200762840c101e4040092141c200040401c0041a80e2148401c070080605002c61007030b810041100034000c8142541f0600d80d856180c0c00c40c02c9003070042e5520503002c074001460341500030300d41103160003429034182011900d030850000050341c011816030200d030803d10b002c0c0d46030f07201d13002c1c1181044450b9100030b115109000300d010310024010ba040344100045d000c204800c1940d04031145400783c62117600b00e041e0b8400c01c030070302221a0040c0606031141d820640000c20b58407100806003120303241001580986c5c03051040007125070340886c0c814003400420034280243c2d49480750340c031074260103402c0c102081403090002401c03551242d02e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 94335854 1250 94334604 94334621
    0x320010e090403090614092202161b060801050303040b0f0c03040305060601090b130905090a0204020f03010504050133110d0c021e01020a020f03030f0a12150e07080703 74
    0x1001d44041d41090b2034081d0881c886841440e01082d44102da071030030f295000003919013580c0090000351950382c00707071a803502c5420500810032400e81e003405080c004620901c3c0c2480000d2254580840ca0904107081c0d80780c0340e000b5404101001190401480140c8011090724100c070040c0084644404141032000d0180c01010701100a0703120100340082407110006540f4000d900c280c0310350000c55107400540880d4807803136440024043d11042c0412180b200f66124551186200041d102c800142d9070004082c2da00141020b01008008001800700b460944106401403240403540c1940c008618030345a186e88092000c00d0880d400c82c1c010600850242e20b00000840c0b030903040e00d60f20080380c50058901c0c1800c090a070300030b512082d0240741401000c47c481403a420141c0040c0380340c104650810110b003400300b0f0100d401d030106020303114044400390b029003806001c54556150075611007800b602101c0358170f01c1c07010703d558040704100000154040d442d90081030901c2d002c3c5103569088415806080c440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 94337104 1250 94335854 94335859
    0x1202010903022704050106060f0318200402040b0d0501050d030801030b1b04030b09010c030203010515130e0c18010c080a0509040605090a1e05010602070611070906060302041e0320010e 81
    0xb42008100300041d44103009450700d680301d5800c02c01c2c0400700ac404031144c40d929400200c2000240c00041101015810070400c0003e40043c10301028501140580c0c20581c00700107000d1001c41d8109030100c650040900dd80025506004e1320801a180240110410321010f0610031080380800e00852040c4400e842c8405d420219a03604e0780c0d070b40740c0580c1203001203e441c1d209502c0c1030080c02801344203000310b0f41200c0c3e009240049600c6070415210449d4802c00100b041129203000004501082c2c0340000e00c074002d641c2c00140c9412060380d80e4011504550b000d14100500040981e00082c1c440080d104202e50f5454402e41f076403507000100e0010309058114940c400c104004103c0c07980074541000b0180c01c062512401403c08000c000c030b043c0c82080c01200c0150304620400c1c8400f51107951540503800a00d02182e00c590b5031a10f143e41100c0302030304280d00007500040c040c04101e0066046034084012078030030300003941c5140c85042524450000d40035503514000d0030803c15a100d01012030845500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 94338354 1250 94337104 94337179
    0x3030f0507050706091404090b06040b030c0a06080405060c0a0f0c02130f02030106030e0105060a090203060315010f060915020606040b0102010e10020702030601080d1d0a081015120201090302 84
    0x88413070280c48445903100c0c4002c5203c4e4007410b440f55003094007400741c3c103a90020b8102840d44494040002800052122a03018400e80c1030411440e542c01805c0c4004203880e40782c0882c6802d15040940c1814001814400407032010445240400e0b807080c031940c0755040c00e1512141e4401c403480041c9000c541d1f01c0c3d503103400f181040007004100119600450485840d42c408014001e08443e0b030034280d40044401d80d038003071001c0d0340400c2600e550b07800542c1e22030350041c195101072154043c1204030341d400b80c0002c0e020b60b40c00e21060082e84e4200c108031019054403020104e80007070300032009680314030061460780a507451750303050809a4003d411003d00e00c0000c0040c0d6040040c1e220129000f504900c806900c40d100d01800051390742c1010644d81d0000030590b96245100e480001c1900516038658903079038014581c030000062125040c4100000792035541804240c1d146901610210324030150880c4d0341138401065900010713a08807465400301e9038141c03803e51464652001819500307100501c1050120311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 94339604 1250 94338354 94338359
    0x303070305010e0711150601110a03020c040b040209100c020a0b0a02011a0114030a020f040308040602160806100915050307030c0914060114090a242703030f05070507 73
    0x800da000030b03050b1200c900f1403240b15039490200300c444400f102c109503000e401000d01c61641c00e5814049039400441810241c2d0038480e180c0b4030301e141031181c21007178005030000c1625a10515250150284d031000071a403e50071b01101100080c00615803210240502180b01e0701d10086480e0107042c940100079002100b80c4800d001c60019020b000c5940342c01802407440d40719448198020611102092040d8040380c0c1540c0c0c0d1804c172913000350b1105845402000080c00004001081200140301902c5c0c658080d00000000c658586a01c20440c2c1007040b29400040c2001806981c09000c4000c0351781942000c5079951865080610100d0310760405074242c01101c10200503c0f442881c10300884607031032801c11003c124904902d24071784055802d980020700031170144070f032030900784054840800d00078900081e40340d6031900b070044480c101829041e401d0103030b0201c0003141d80044160041d41c1103060041841b414281c00c464150090b400024140000b071042251141c0c821020f944200c1e6000c02118022034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 94340854 1250 94339604 94339607
    0x307020714102102120423010b061903090203060f06030607030e0604060f021204110a0b070b180a0f030206041203020702010f0f1403040b010303200604021908030307 73
    0x3901501100c1c102030032065800b800d286030707601d51400c541c1d0f40d2040640400180e041045000f80c0120910a80030f008101c85140913000c41c0e40118440c00b66070b0240d0400c10303144100001c50300004489649031102060041e01c40c402201c40140300100f00d0304509110203010b034005c104424000e501485500300300602e4514030a021350003072504a0480c2d03600e41e542c040444c25035035210300c0c0c408150040300110780004c3d1607800c80e000500050b2009810000440c5002c0100c190845050b0741924414400000608000300b0720405000390b60011443c0c030203940c0701c02c1d640070000b50009600400381e2401c0c11048609205c01c24800d5804148692201c000d420700a41e190700c140c406582c0c0f52810b00041241a0192003104d50b42603040c0c4442c05075042d03c62040d150310300d10041c00414410200380426540e46c01c04001c500c254420036042c1c10079415406c0080440d00f54070400e4002c0e440f0515880c0c800900003035000c3e0301c1a4122141c00000ca14560701c241c1e1102e0302d610410b01880003005205159 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 94342104 1250 94340854 94340863
    0x9091103090105060618090403140d090312020a08010302060f070c030f03020106061d100509030d02101a0d080904020d020309060702060603030913110c12070302160e070c050111030702 81
    0x45240078000c0c030840d2a82d108011891217500241ca543c066043c003805114240706c503403954464042c3c02c140343c08061515280e0440d602c88040036441c03d994194507003c05400110001032141d2050046040441c0803901410314641030001a12842003c164a80300c07030100800c41d07100c20791140038086160345e41e02c0c5c0701032207100c1100e00301c0155003002000314045104100080c0c1c0c4080c8208204e000f81c0b03d100501038141d4940140c0c0003040300030015084562005c0081d0105006c040c0d00400c0d401c82d500d40307101e0840341d07010100d01e102c410008803034810755030701410760754000e401800940e03403021242d0015009119016440c03603103600100401c4200300010410030300c214519004d0f51681d68440c03041586a120f850b02455002d000781c540c030081703080280e200045c13111601c80e81e40c0c50b003100d034106513281003c216801410342c0d0000440d00109036061051a00f2103034202c07603c010441c02c00c104e52161100050001c030400002d05060400e00409400400740303804071900c031682e01e0801440c02501c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 94343354 1250 94342104 94342111
    0xe1c050312011409060607110a030222050c0901080103170c010c0c02102115030c0807080f0106060c060f14040c050315040c0e070c06050708010509011203020703030f09091103 77
    0x200142d2103460f00c0c07404c054502a00c40e10004001d517280200c595a01c80d01507110b810f070550094400c1c030022006031a03100c084052008407084081051010040756801d4400c010301d60b10400c1300611011300306980001d01c081c10341c0d41c008401b56500e02040220300c054026036022201d25801c014421180d19000401101d1b440d001b45d68100b0200c501c400e09460f030319071051614a405802e0b020400e440d00050303000003203c003448910500f500c2d0362903c507040080d00c140c102011070f41001c00c0801035010308200c4644200c100c2d4000b44a058580800a440002050700103465642c8482c51013045c10301c0e6602c2068400d034031405650b85420181010007052542e400f500c2d009105181007480c0d00c08050184070f02c02c540c00200030f00ea890030304202038200c1d2805070000007400f0400c4800d00c001010350207080c1c466400b559030000151308d4007041101e207007010f901100d00303a0a001c0850022a6022542205494050416110ba582d040303608644400d019070256518a103002e41000c0b0010341c94005502 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 94344604 1250 94343354 94343369
    0x301060503010512010e0624060f09090117120a0306170705010906180b07020102120309060f16020a12050c010e01050105130509101a0d0318150e1c05031201 69
    0x4d80741514240d070350881d08445860a0a41c0c0510001111941002204d0381d81114210b010360707840061074041103181d04296101f240914020881060a0038900725503801029a4040000c482008006140e154035010b212054008070015140c05610301035081600102158507040c00c1c940415070303d85071141c11300d001d03240c00a0800040050a180b084243e40000000c00d000031f40e015107402c4035008254040082281903004603030071100a45142e10185118003818000b4106a1a00c101681c29680c4000c1c8240070914002070000101e6900250f0b20400310785c00b00c401071880d84205c10a03113644c092296600015801d180c480c00700500c06401c590704071035080d80c400d140103509d1a000016900308680c911000d43c0541001c13410790280c3d81082e524083e002014142610922020985040201c0e00c1580400c5007180411900403d02c2d00280c020024040108009808041d0007041ca407032040b102403052380c2c8200c88401b6819034984030b240855009044907555031032203c0d11640910248180075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 94345854 1250 94344604 94344619
    0x2010f180f181409100e010f020f03090c011e03020702190b0a080a02160305070602130f05120a080d0e0705030607030c0f03140601032409021801020708060601110307050303010605030105 82
    0x40706010400c0d80f032805140c004000e400c03100c8921010800501889240601e65901c402d4640a210042e100a0042c1c1c4441c90703201e507680c5014034550f868070f05150003607410401c2400d8030448415160000714108403c600d0096910403850001980000c5011400510b0120141c070024099104000414402d40688c0710a200d545c2d850280604901030301000100050036018188002481100101165849480700604014107110342c0c44808d80b0503008103503000c0c5a03500c00c2c0807610b4031150140030000b00074000e002c0b0b001c04d0b981d0010300b03016440d9407501e002c1d12408101c03031182c014400361014080180c2201c8080c41c2c00c00008002d00000141540819081e00c111070002d4802e003c0e1000d01907424040c90882c2d100c3d04d00450052180c0c00c8400b460190201825103d4080800c11b01c00901180c0303c0942c43d9907081c5000740e529081c181c0000d046d075002d10f604210a0f00041800743d8007450900300703109200d0700d9060503402c5100d206001031280c040040045842500700024506a520544400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 94347104 1250 94345854 94345871
    0x1d0c03010f060302090c0a05040e040c060801090504020a03150609020d021806041d07030e010c0e0102120918070203090901031a180318121b040b030a02010f180f18 72
    0x90080b03440c14000a034028490f80c0028150103188001059005c030140362561600355075081c00700b200c0c1016503042b2054088400e0030070215500500b140e0150000010402c401e0a0680c00207002c1d098510005022003140c00c40300b01e05000c40e0380240020075108009540c0c51042d6505a402076102807040d580c00d005440c10155581011002e850a581a4020f10f1154001101803084168001080c402c101f503103c2ca07500d0b1079813900380a52080c0000c0d58640303d0288180c40300290902c241401001c80c1d04105204403940c80d070302d03411010031050416003801c2c220b40f20303040200d0071880ba5029454004518400020422001c4040c0c00d02d10246d0481300441500c440c41c000c2c00000051050703000b65401400030020110607481c107082240d000820705101c4141d40811241404855600c00d207010910800300700450800f8061244005c42c100c02412503540f07142e001070820340810361800c082001110065400340d00410106010f00581c072802021070740c0d1816103217000c0140f000720030b00050501212 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 94348354 1250 94347104 94347131
    0xf09130603030c03030f1b050c060117150402040f02070804030c05010519081003020915010201110a0207150c0204020403080c010e0f071422060503120310060804061d0c0301 76
    0x40d0300079030340d00d60f076480c8803007095850407000303090044004640c4c69520365500812605001c54030642d1901740c0c076825228040302444504160b4145c0c0f10b03512003501e0041082c540f000201c3c0c801034a1a0ba241e94a41c070342c54a00105000740082d210582425100284071000c8c40b04003406001164454061240010b4490004503440e0142c12125040b035105900d8001c100303401400c2d85a807101b07030489658040c60b0780e82c00040111609884c00c9155140320010610b055074207001d120401482d0074801c51a02e090a203000755150a40e2041c4401e8a260040c1c01030b01510406223210082e400500039910b40e81c45c1c3c20088020b500886403c0099841d2840300c069803c80071425801e2840c07100080d180e29850320391404104e85080b45140da0000b13100d903598038694041c0c4daa1010307900007407100081c024140010300d403a0401c102004220060240104542880c8142114050f2405464601002d85403807500074003030000d0404c80041e40c840200400c21110f0005200c0c0c1410070110000d00c100c1e510b2860 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 94349604 1250 94348354 94348361
    0xf0c12030a080f09010902040504060b0a080a0f03140d020408011b0809060c090303120a09021810051003020c0322051203040e0403170103110411090d02040b040b04020f0913 76
    0x10114041020b500c00500b4000b55802c83c035030300070120344c0046262a00355000800300c52049a0844410381e94555840c0c0078181b03000480c018180c1d130f10081c0f01881090b03ca1486071540700400604000c40180321340c1c2c10b801c0320826034405481d002c0d019511507480c0d032a80c501905180f5000c41c0042a500406041540f0403150940100d400c1000f4210781c2c0c542c41884543c5a22030315100f40c0621007003000c44084000d840071ba6106106082d80005e1078450b5204101c0450300d85140c8000f144504010306c0082541102c1c4c5900300d460880740304e10b100443c2c180c01d5002c1c0c000c50641e642a8040852000b0017001200420417001c45510500309130070f5200c1d0200403c6940c6801c10741a241c3c0140006e024944002140a400034001c0c02c1c040d550b24540309003d1204882608100d41081040c041640542040d01841071801c4402400a062210f404085000340743c20302c1002e84200e40381c107046030460326554028018132a018105642e54020b040120056900001085004104400180d10044264070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 94350854 1250 94349604 94349617
    0xa1406010509090702161d0601032a170a0203070f05040602070902090f030607020f150f0402130608010c030c0e030a0807170c01020d24080d0c030207080f0c1203 71
    0x85541d814000c10741e081c8040b03d5002041001988150703565035038074444102c5550020107000c0b688403000110031010724140c0d9030251809062506000c0c0704052040b00715070050007507101e0442c2045000c0c4040f4216030420b2401e0005881c1030700341041c05a2401d0a400441c030542c4503484412008000440450b07040c401d610420006802444050121059580003855115001001820b088070b2000c00070b801c2500a5540f200942c2c00f1000040d04035030b081c84010301c051104c444015040c0342c240b01c0d21482d0f5500802c001c0c4030f60100707032240314801000c0d40f203440a0700c0e4210003001102d842c64000b80041c802c00e40d045004c256000090318251030001162a00a81d1024403a410244d0035650481c00d0340441c2c82014060030144505440e6023401d01c081c0500b41c000b4440403d44c4011207003c0a2502801119134444911800c810f00404d00001007201510119103822881d03016141000c0b424901640c11090043c081c0c0362820030a50303000115a510700c03a0454100301140c1502070450360304e20404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 94352104 1250 94350854 94350857
    0x60403050301060e03160b0301080d03020405030a060b0d0c0303030b010210050121050a0602070f0605062403071206150207060f0e0d030311030f0f0106050a050d05040c0f030b0a140601 81
    0x2040140455441090754880e41c4e84003408903804050518203800c00308800b60407420041c5c0000c001040ba10340e08006007241c800040c20114076060600c0007194846107080d130040d040716101c41c10003855444000c4c52030f0140c0c1c0c000800c1541d0980720f150046c081c0480c1610300380148140708101044100e076100c0c40303040301c01800002c1030001c4085820882c22404510595080c095002c080e00450900c0c0000c00c47c041c41649112074000ea00d107065000c440014111398010720030700081460400f21010180781050750365900c1510307030b55003500c21504100d48215000096041c60000289421a260510342c103030110b4081e15645502e0b02000c44209560810b088005200b49601080340d00301600110022800380c030f07011403414445600b0604a42c8181c1c2c0058841d05071000b088010151004020301501180c580036103804200381004003580a920810720347e030b036500c402003010481209400c100030300d803140300c050945590b400d25850b115001c489404034076091000715000035403010202032041005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 94353354 1250 94352104 94352107
    0x10e010c08011203020c030610050a0909020108131b03210201050402010f0c020103110a021006050a050d030327080a02010b03120403140f010e0309030f0d052b05151206040305 77
    0x309000341001d149100404d41c1503000d00c181e070341c800703440600c041842a000c040c0140c1e4403c0c540b10500110031201d520041d0700b1460490310600503030740070251917042030102402102002c501d08080262003442c1400b040c0e0405000400030030040303070300c2500c14544464280c208403620146416403d94908440080c0000c000030308042c4140d000341781c17404403e80107140c00140504002c00c0150640e2100301a03401590094074440103c044c3c5025440180c202519003110710b0740b40202048460040b81002024103440b44851080010303803442d01190f00c81c00c0000900140308504014040f0b5100c101c4c80801542041c00546460400241c148011005034403980d1404c0c0ca56110038210103064882102c00f801482c0c03941000c80c00c00d009004034140c2a40103182e8a1244408042c90590700c078240100d90380100d24411001a0084152991500d20283c110200d5509811640c0c030460041e004413402880c080911880206124094808080a448050720115001c0640b0b9440004444c0100082d50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 94354604 1250 94353354 94353359
    0x20a030b04140102030f041115030109020a05090604140a170604020f030f010908091305100902070201111212090114071b08071b050604031208060105041214010e010c0801 75
    0x440d042158841d004032248400b016400b00ca060999006aa01b1110ba00c8a201404280711851021b03c01d6800201d400000c1610002030fa05140d001c140b245000466010902882d214024402c039010440c00038001c03542d07a40c4078410400c0f868551011140528903204012a00316009a0002010510b203401010030355181c0c0d00b00400c000c6071124003900741c0550415000c102100340200b4403460b202c2ea110030303122000242440000c030101c2c0380c03081110b418803040c4200d0b4150700d8804403c1d51400d00c0c001d680c60f445800180c0e82c41c50070904002d030303600c0340c622030042241140e0701400c0380c2040030102c4015600c030450400c2c00d0b14a000865280d102d8910701207600540502071a01000c44201c40c803040c02c070829111007030300e604502810340d030b200a503d0448170020342c0640c0034009800c0440d500ea041c0307410350301c0c0e0000c4203550b071540c102401075080118149030300a0050310001d2051000c02ea503410071500e01b0100c070310b40c000b20f11140b640c201b11143c241040180245e80104186035030ba904140e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 94355854 1250 94354604 94354613
    0xa030509040b0619030c081003020108060904050304030b01090603050c011d19080102181008010b030109090302070905040609061109010c0611071202030c060705070b0f180d0327020a03 81
    0x640206264005030400041c030a0801000d66000c46130703c9520b001800500d800000703000d58400801d10545200910760900050381c00040b0b01d40c2124080d070f1110410b90f00ca03e8403500c2c42c46070303400c080c1c80398201d01e000091810254101d041a00d2159040d00c050f0a01c9038019580901c0381544e180c06032580c0f0181007650301b0304010f844030005240e0403d01d5000e50301d00c5501d0890740007044045401d62080c3d5200300c03d041c00c2880300c02c00c140902d090a219890702095100a000601642440a4948201906040c400c00805019104e204410492400d1924120b4024900d2103421111603047c809006907038403260003075030075520060f103892030000c000340c1d030f101d005092018034110720402c10320840d0080f0380201e64202c0c00040315001580d442050041c400e2803e0401064901000010000980040c9508070400d4010005080303807851511100310540100d030312040c2410191140308981c3d2521070741600315010510280c0611900d250440101681000e01414041c0d044428400d0800009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 94357104 1250 94355854 94355861
    0x1103010603120507061b0215061f12020c1903030c02010506030303010612060e010605070b0a230a0e0d020709060e390c0a06050105030a230703050322080a03050904 72
    0x42c40f070a0000741c00c0510000b44880440c0c030f20380d00d00048e40444800e40711903209020030b603004042101d54520607200c03010065005952020039204006001041d84415000e5806440c112442407080c1c4010405030851000c500d442e00109400090a02d0004805180180f107014020a8041d01843c90b50b82003200c03e94000d00c06050ba4070050745c1c0c810b800610440c0040842c0d01808099848507540e4510f03083c00c885092020f804421810700d0401340e00000b403045284000303020700c40350300e4051a99030007080200030700b5134801818842c0144410450761a602040c05016a60014000c01c4850b4039401c1c9154500422642200c6011207044602081c1d502c081c10104a0004825440b0b10a03402180c40e1840c0e0b01300102000c1240e00c1560140304110482c001c50340501070a4004000c01e040540300c20ba2208490702c01795030303400015041c1200580c2c0c1030002c0005142c00408a071354501e40600042581d40e41040f81001d844181079012468440100b608080250142c1d50355041003500000c11008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 94358354 1250 94357104 94357117
    0x30b090708271608030a09090b120607030504021002010c02030301090522030e0414190507030e010905030702040c110d030b03070504060801020d0501140604060c0206070209100311030106031205 85
    0x100420741c0400303402c806440244000c0150008650200e01d0711088106600500a260824015074601d1076211412508a030401440400c1d001c0c413520104100d2000d61207400114000c51040240301d0703401d078120780d000e00d10984d07a1803848400f00008a00301d4510400c06801600200010080301650b03070001c0707401c14000c0c1d20981803541c4010030103180c441d543c0c0e400ca010500d40b40c50412586014030802d150b002c51440c4805d2180307808400000e4101e004154210402e580d10082020340d4840da000340e6070310382400300030498803825040550341c0790085502284030f141840070841c00d184c413480603500b0038290400144050640e1680c180c010f80b55000350300b030f0140300e003d0000500c2e80d0303103000b800000c0141030001a902c0311010050000c0e514140c05c1810016501c440d94400c580319403044500710f42052800c000304d40303d244000303038251194100c080e41c4843c3c0b4009100c800c010585591003141d01c5100c0d8030050a14001c103250036140d107448042c00000161030308080d12070184004010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 94359604 1250 94358354 94358371
    0x22505070f0e0702010e030310050607140d0c14010204260a1a010806100305030405120703060509060f01090b0303040504051503010c050319060503060a0b190e06040c030b090708 78
    0x150a512096000310741921a031004035034220304014040201c0d020b22440c040c0300b01c1100074603e035103032400702481045158820180224000503000090003000118120140f1030042030b94500003032000010182c0d04071075001e481600da001c0c0c100011803814400c90302141c80c4588060781e0b100c0301080d803c0120b151608016501e0140c0382103840010550020989100d90706503e042c041e5040142c458074040006101d01c06800c03143e80c0078000b28400001743da0440b80e040307a13004002c00940d11540d0821003117600040c0b5890a0070180f01180f00041180d80c8107a1220310341d950b403aa600c003c01c000f80d811104031190144c0013000180114207040c2c2002d940104004e0008185013071500110782120180d02c00380c0700240b0040140a910072048680099518140006021040c00d020020f5100d56018000c0395407150303507002c195640e03203440e40031014202c094201d030b0220315074613a00310a403058222100743c4107910302074000e02c5860191050400c9100003400303405d003981d2210710a5400c880050003901 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 94360854 1250 94359604 94359613
    0xc0201020423030d260406090303050105010c020d080a02190f020909120301180b1306081b1305090a1506060207050418020d050f160512070303230708040e0f0a022505 73
    0x1411017100e0f0003a80a01d104201c005150411410b000301100e02c10b070050381c104002c4540220241e40c0315448401c2240d081380302da070346d81c0c0c40e141016494903e03582000181103081054000500003500c10308170181707009481c5000c440c0d0310100e45644802c44100c0703580c0754020a00060100c004089007190101900180000d045110700d000252a18080071b540d86010741c66880074000341000344070071040c0d03d0710300c510350400c0d10100c0000307514402c414010960407941c0341c000170380000c41080703080366454003c0020004141009000806480c050042e14054420407031300103024113080c13041051610600c1080480a030183d0300308084484209000d07a44c40c825440542c21810013032141400750010003e121580c075107480184810f28401200f42c9070b450308100020008290461002003202c05840342410048a8848007428580a81d05000d403100348045000b01d001103030a18031500410707010025401c269100c1150782c06070f1060141e403105508a0b0304000282031565124030b02c040f441001900d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 94362104 1250 94360854 94360907
    0x6031e01140103080306030d050a0e091b0301030b04170315090a0b0909031305060a050406141612021908180f0402070c170601030c14060d0c0201020423030d 69
    0x42010700c0a8100303482018001051040324507003000b6000d40d14182e0308105040c0000f141d0042c0c40308252140b00c1e4040c464030b00001b8005d5040103000200050106038031902c0356140d05082d0b03200c8800b01e81c1240c1c4407003110001d0308000e400000742d91266111050590b110b000c40f1040c400c9211029003028aa991107400459480c0e07241c00300b0500c1860910300071900c2d0303105408100b074078404661000c0c0c0250002c119561506510400b16030544d07026082149822418001804084c441e1604940b041e81c0402400d40801c00d070303152807007007448480c1e003143c111140181040c19a40b280da00300600f40f20f410400319400750120710204803a400e0050454003082140004a0700ba0b0f40030a004459510120301e003408041c0041081007034081d00d113001020b0fa0342c1917a4641b0080c40441c003510303003c1804185241419a602c604460b403000d000c0c80c09001c1803160600180c0030f90410701803440d5080d200741c00003640700c895401455a181d0001c00a049000c01c0300400d0b2403020b56407450840090f0350f001c05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 94363354 1250 94362104 94362131
    0x209010312020312070f03060f12081c0207030507060c0f080f09030705070308041505030903090d08090d110f060c0616021603031d040903020a060c020c0d030c0c0e06031e01 76
    0x40c50b1140407280c0318600c00c80b046d408018221000c50b000751041002d082011b0100344840500d0810701340d0f00c2000b00c0e40d60481c00c420f0880c042da000e404555124000a1428101a030000141c41e006218075400d01080d40142400c4d128444200394400000340240001009003101d880400c1d0444540016a440c000285e1030f4030341032174204d42098843c800001030030004124402c0c0e03640002c100c9841c116003113043c00e2030707007903100d110f10145148113210190b101000e00c007000301160120203005201d40c50100b298902001e214020702c12241c820b001186018a05007413110458018000150140002d43d8070311500501c2c062150490008601c1010180d11264900b2401c4001440c040e855880c4c2c2510701e41a28080c8240940302c060055080c040d18000103a00007034504406a0b20440218040c014a0b10407480d10102c3c400103030b40544038909480c1416040740160301964015020301d1a069144c019041c10050140c640507095800100300801c06c032160044207885510300c200110b5034803540e244 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 94364604 1250 94363354 94363387
    0xf040603020907032c0102070c060c0203030d0f0b18090106090e030909150402030106110d090b070807020103110412050c06090109061112041410020609031b01150611070602070302090103120203 85
    0x3c400780c5c0d1798005a02c0c000e0200d4407800200900f02403a05122091465000c20703101e004000044008a0303c414001a805003944c101002d0244040c003400c424620700c0c140041f90400c02d6520744040d500e002c1c00420070811038042c070314031220705030300444c5003486400c1408040000181026405031000d0200c400c40d82e103a00045000342030035070b03803106208482341e00d060400113011481c50030b00011180401000d203100080d280340a40108407203489845a00069000e000c001550003502c04001070701180c0c48602035541e44081d030144044070181c1040100b40300081c8100c003201404141e441e0420030105114014000760b540201c1d00f9208005020103c4019980154112000007103c2c5400f0700ca06080c807810402452529100612082c02c10f0740f0314a40700e1146441c0192240d10b94401c0a565080035000b0340c0c1d1201c440b20390560042d1313440d1001881000003000d00c503018002c02034001007071440002c2e142d007601c0c0c00414a008592031552106c10002410701c3d51030940c00309100024900da40c501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 94365854 1250 94364604 94364681
    0x40303020c070b0c0601170c030106030c090c09030506011517270105071205071403010806060109080303281407120501080127050a020a0b07020f04060302090703 71
    0x480150321088200540d42c00d100c459000040700920502040410040000b1054111414082c14503482c04048200c6810300c03402041c45609503080c076800004003c04560010100c9101034000c1102c4d038401101160b61064a1002411b030b07034031590050010007280740d501554000c9600b0b000792100415510500c14100072141c5407942c043c010008044015469181c0b40e9424604d4000c000781c2c9400e2a010341a5800d100c10385440c1c41d1f4541c0019280360040415400081d800d42200d07480350394800e0708642d00c4400f112098002070350507100042008001080d01d000d00d0b6500c12550301c0000300000c0747c01d88601c540040707001b90340350b80b1b520300c200e10b64009445c0501003d5407200803202c2d0715890f02041d04d030107900004c0e290b03140002211f41c0c1200c40c014256240d0a0100c51949405c0c03504295190980860019500503030760000096504941001010700714401d40752030607a0a80c200800040b40c0b100d1102940000400000a000c98829440074203080c2d51a81c400c10200c43c41c0411a01104504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 94367104 1250 94365854 94365857
    0x20a1b05010b010305130b040f05160305210909160309080408010b100503070c02061b0d08040302151603020c100501080307020a080f120f120a1a04050403091802070206030403 77
    0x940402c1da180d60706018150b4440001012003281c080c01e6661100c01006c0100050082c140f425401810440144018000c00c7c15806003415055103d04040da1a10b004901c41d01c17075540d115500444200d05581911079085000f08100c00303981d07596010065186a0680340020555034544000004141d60060006031107401c0000036403154200c00d00032042400046074051100c1401048080c0358400e940e0304026a0541e10b4a031141030801c140c200e501e030320240081030f5014104080030515031120358107114500030b07070880d032546010010f24030074080c00341d41d41c4480d80b980e100c0b819241ca000790020301500d03500c3c0f021602c0071105140b98200b00d401c280c10101c1d0075003000440d00154540f902ca4030004e045820050848102d51902103942d41d00d1006002414240c003182059540d030400003500d40c441100c004000031480c001120700020f002d403604000700c0c008003ca220049042c140700b070601c140d0b8181c4032201880c1c14854140f4009060b520040d25650b000c00013803006840e001c000d18082d901c40d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 94368354 1250 94367104 94367111
    0x60d120819022b0e0c040e1006080f070b0f160503070605070206011a130611100c090e090c0a0b40150509061e03040f1101020708030409020a1b0501 65
    0x400c3c24880c5800a4204000d40c02c00c491341c0b150110114915071000c0040340c0000d20b00c1410a8102e0078020b250b034604e4901842c044000900020100358182076006110a5450594640450328114041c05403a88000034040c070968502501844c4003440c0c2c140154110390070641c040d614801620001c41e0302c24010b0300b118004022200c400440150340300c04402c1c20904160480b82e0852602061344203520401100400401c0d0403442440607240d0601c1c00b120500c08441149805492804903109400a000305031001506220300820203c510070b030002c0c8069549072901c0c01c1c0002c3c0d074000c502d10100302d802c1c4129003d54407101740343c0c00442c0c800c004582080440005c44003414045107901c00840e81160a094251103603106044a00000e41100c60325106c01c0c150340c112040d0390b0400c00e56401701c00c0000c10720090000720340801c3d44203403080e40c0030400108900e0049031101c1e0320f0f1007418040e600a200910042c85c660f0041c0112040525210383e840030b500100341c1200c0241c55094030705954 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 94369604 1250 94368354 94368397
    0x7050106050102100603050303060609190902031501030204030f0308040503040801060905010f0905011d100b0406110c010219150b090403050a030c090e010513091415060d12081902 79
    0x3010300400301c891084420411070360f0711b141c868649070700c8010007441c41803c0c0004c6901e0035990700c242c0e4440d03818010070780d03000ca03030b450f40c90b800000d601c10340d01d94410100c0f0440b43c00c01c41d03100c0d00841d000e890b03000041510340e40b4140c0e816144200d001d0000c44042c0402d100c040f4102d2400d114a1004200000001c10316500d8040075561008180d000b01189604110041c0498101090005415000d40310701c41402d9545842d0700c10300b001942c006606028001030005080f82e44240c0003849000e080040d0b8189040c000e00590b40c440c0310307100414010300024050008503115040038003c400c4003840201c1c0c440a0f80c0300007091980c0c01c480c102c000c5800480d90b038003d140d043c402c00c00101d11074203014200e503050400c48402a9070520405109800d401c48030803009002c2d801c10440300d580320007107524200e002062552108049026249090307031050005a00d0716118158110068203c0c00616000c4c6007907808443c0034400070914903084a5900c4488007440403032000f05898441041090103149 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 94370854 1250 94369604 94369607
    0xd02060901113c030705031b0c0406330906112d07080601120f02010c0606030c140405011206090309080613060506010807121806050c0405040e030f090906011202070501060501 77
    0x81e2803c00e101580d61060011000041000040f1512543d001040b5000c003100d0200a0307240c400c00d40405a00541800030024454041020b00100f01c80060102e8100500384480361489403940c8140e40d002803e8400b0402a0501580e149648446183c055030b00d44403112440c2c000c888004105111074086401042c48510300502441d0044d14048014142c1035141900e542030000002001506419541c04250304580c02202c612540a9021000340032180d81c074241004041d96038403030300c5800019495038a00c0f0b498603116850503a849015540400b072125140c4200910301079104400340540940082690032013000300a214400c0300c1c0c07007414080c04902e80794040d104082e0615061140101c00d00c00c3c15508814001401c0d02d0b0501c0010b480d030400e03c59484002d036001405010349180c90284000e407541c41c802842030b50342c103842c1032200a001048035503481c03280c90003101840d0002c0c04900800d2611140d0f094020f24149410050030f02e2400c5034100300c1c2c2c4041000c80c0d85070341d161010081ca5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 94372104 1250 94370854 94370953
    0x509150301060f05032a041d01140402070f17120a050702010c03060303020a03180b0c16050604050a15030609020a020109060b01052703190302060108010b0d0206090111 74
    0x40f030b8036140c140d0960608041130710401070038460080c3c2c0300c2022041c000f0218544802e5800503e4850303040c0650355810305c1c03040c0011400303000796031751100c8d5440901800d080c24000c54180550140e01030a85034041d81f680f080024207003404802480d010001c1c170a079002202d2a5600454031104001007904242c0000781c01c5418442c6203400740360402a041000c25008144000e0080c2c05092411400020360148030940b440b42c5c00c6490204800b140d0f41c180d480c00020129040318121a00c2c088040d01d41003044018050752044662041c1080000e0200c0e465640200303400d1704a50a000c10351548650300311041ea0465042c440060703569152020600c1100c0c00b400036080c901307081542c9000c1c900c00300420b504006146140809a0301e8405210a880810105a99500c3c0701160750595460b46002925030000388a100c0d242d42c04e011480410345000d044905040350b004000d5071034044141c0c0159142c0c031180c641122140a044800385250241e840c1c40c0001d11080700c21040f454049030549080c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 94373354 1250 94372104 94372127
    0x70801080c0109030803090f1902011215120f050601060c02090708070e010309020f100315060207060905090a1e0c1709030d050c0c030408010c032306040507050915030106 75
    0x381d500050482610340d03003081da081c0c142c0e41c02100e21680ca0382d0b0080094034001c02c0100000c850310618450041c1e1003aa0703110765450350301c03da849650841960307a00c84161080410840407401c0d00c8003003001000c12000b0301d4501c6038802c80960340392813001e881d0141862026403005020400720382c41c0e5000c43c540020929445a4142009182800e202e07a00034400b08060803403070306140c0d454410905642e0b40d052522444040107081040703280740700d840200a0051610032103000070b42c420340807a4060000ca29182a075075941d903100c00040c078002c1040030301c0b000036010610b0543d82d02d202026824000f444001e00090500c40800c080031145401000078041221900c6c1c0d41000c9002c1c0300e080e10001c003c580c1b401140203c040340c41c2e207560311104418801d031a92003805100001e00080c1310007040d0444101d01c856514100326400c0c2c0a107040740211982c40c1001041c501400c00142145050741c0510780142181c0350150070f0003240004101480708003001b4540148012004102090380b1a040580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 94374604 1250 94373354 94373369
    0xc100302030403020c0909161e15052a1c0206010807030b04080904140702010f060b030c07030f030b04020703020705150f04030809010e0a14030f030c0d03020c03160308070801 77
    0x380d880c02e500c00940359942c0416440c071445424000c5078409500304400042c0c1092943d070b4101c03d603505e400b00c58100c00ca0f048001e945115200c40090390228428000c03035401c000740c41d01c03403411413050400c18140e5081e04050000440d083e606c003024010030030130000207286640e040c0c200e81c00184c101a00d000c80503408401c10742d1042c0b070b0500c0001e0b1040080c5800c5a480781e001611000d6402c0003034081c02014a2401c45079010700708025a2036415001201c21411030381d8104252512a01300b02e0062208542d880f84194040001c030000034813480b200903c4122506e4001000c8d418400010180c1e4000e04c0258016070081000340514903241c00c924041c90803140f070311843c0840707440a0354410b0040380b00140032a0030100d60121142d00642401d83c94417001861140043c4d04d41d065406030314030042100b8020b204660300c50342406000803c64540c143d511f030090071407070b503003c4d4124003a601407900c2c82c0c001c0c0400e10000c10035100234030718002c080d80309440e110454a00814024110f80c030580c0f0445 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 94375854 1250 94374604 94374607
    0x911130509030417030f070b0f0702010504030c0b09010603080f040f0e0709030816020405010b0301080c09060307050d020112090b0105031002090f0402070f0c03120e0303120f0601020a140c100302 86
    0x75900108540840b41151100581c141c400c2001a0139400740540c0b446c0180000940c0108001540c10f0651080b14038a110007401c0d00c601400b2402c803a0100c0d00180410718030300c0b01d040800c00f0694040c0c0e01210031400800ea0075101c1c4d858114541011006062490700818184500402d802d2000c000e417816044109043c90903040c0141001c1003031002605c81c2000181640d800490007a0742c1d04040e402070030501c00c07075a40b00d844002680c4244119a0507001358100903066103491880f45004140050090010504080800039900e5102c4000c03410701c00b90314181007003046140110421640101c98071099985050149403e00002d00c14400c1d0701031041040c2c15050707035107900250700741d0004d950044c0c580c112031820200307001828902402c10b6010b80b00000070000b522860908000e5a036950f90600340050003415a0b9004450300b240492031202e0020700e641212400d02a409801403041f6100d03907405407100010380c0245955010950403c00300c1c5111401e02d0500c03000040904d00d400c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 94377104 1250 94375854 94375861
    0x40c08160e090c0304051501081f090c0e0c1204060c08060d05060a050709120b010f0609030203030906090609060d06060906080103051504030306170a0b090304211509111305 76
    0x14082d040c0c020aa880107800100100b4280b05c010071903403601c0e10181801c1605075840c1c1f0705199607080c015213070000f00701619900210380c0d11a4001c52040380d62000f240c3c10782034244621082d028400402640c00c0440600c150f0303a80d01601c0e24200d014130302440c0002034411488000030400280104920b004418621800c030020748000344c1aa802041510b0024164842d40343c22101da008036404080c0302c82e0f40d01441c1d028002484a054100d5443d01807a907103ca903604000d070703640100e512010398036800c1804140c10300c0c100f0b03a00030304c55007200a201078a040c0968000401d10380202000145040d07803003400f0311407070b50082080006055a0706054038a50314554440703036900045000a034089008001180805000344c00c5030b4094a8481d01140c09607404e506100ea503903403074800640c0c900b146500400c080d0040402103c2c2520103d0100d003541c8680a1401c80c0d8045000904030750780c40d0254840e900c03200300e40c880c0804061183c8444c5d10003240c11020080c0b0a0040600c3c101081d18000a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 94378354 1250 94377104 94377109
    0xf081b03030f03040309050d1506170304030201120605060f13090b0d0f15060b0d0501120308060105030c0d050f01081b1f020f100c020d031a060711040c08160e 70
    0x40d2214044480b0140b95203941d1860100e0340001c40d6484260059109400341003000035503100039180c02c0f2414801c2001d40d9035400b20b03010810740d03000c2d8600103400422050000d540f240340c420302607e184100100d06240d41c2d8005c2000e5511680000348601c2000c1440b900d1041081041c4c0b0040010300d500b4803025882000007001c1005444000304000050b041c4035040011078a0040b80d101132032142000030a0340c40203090000d0f403110400d02a014a048000300300f0002107524a00c603190150364040300daa54103001034410364030161600e11002424810354001100e40d010b880c0c41840b070048404150751624040a2070528011205188a0124050f40c40580ca400b80007848500380022801ea92224911060f400c0490503540c0c5852800754202180c0b2043c0d040d0042c544046641e0300303d0f03952810003c02101100c640240742480031412020000d035a1600501816201d409410542e40c0f0310340b5903000804940350b44110b9008581400c00b0480710803c5d40d050542e40304802d050000320340d803d0f50300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 94379604 1250 94378354 94378357
    0x20901050607060e0d0503090c010207081005100305010207080405131a131103090a03081b0301050d082b0501090e0c04050a0603021512010f05030c120f01060f081b0303 74
    0x38690080341e000c80e424081c81515007003d040c3c035440d10142e4103416001c03880100340384d00407101e5804501c50308149814035403002a203003040f6031510f0302503c03450921401c1440a444043c01d00498280c9800c00480030440a20041542d00d20551003282c4e01d40ca40400e100743e404a402000040602d0410900c8285070441110a0644000c80f4440303c440000c2642d10000d143c40301070400d5001c0b010040000c94580000d00e0010035000761100d283c644d5030303240a95040d242c500c1150400b850103000400260800150b150401c1c1e10039001c050604143c00d600910740d40350100801494000c6c166580c1d28480f0b980701e0140503144505007480085442d03452076950312a825084c5004603580c10008204031307100d51004003d1130303000b407121a41d40725841005019402400500d00809003a0000003620314030364004a00301c4a010300030b802030610201c00c10040c1c2c811100d4041c0113000b01800620030039000e124a03c0036002400a000320b850178a00964540103013002c0034681c0f08980040c44070603640000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 94380854 1250 94379604 94379609
    0x309030905040c0e102c04050a020304020a09050903210a060501030e03040605090a080f0601170a1a040501090606090618050103080301210602030a1e0501030201090512070806042102030403020901 86
    0x1700c1000140500b00b0040741c1e00d640d08040300c9101e5981208140d214940000360100041c0b0499061105488050340707e81280b0007924002d5100c0141c4004001801d001d401059025400074181d07810041d01d490400388105009007880034801d01c000800407403a0143c41840082c000c00e1808201400205026540da40305602800c4140039010070322009940e507402440c005400c1c1c07a401e03130f03a51300d0000d600706039101c07802e0180900712440e0b8040c003001c44d00c0001e03c805080350800d61000c030f00d42074201c218040007800340042d591952601003510101d401402140c0040102503400112030349030002300126446c4080c40408030906150041020502c440e007582d054501d00c001c05101c1d400c900c075502c160980b482c0f80c0140310600110402c44404801c0d4000001c44070100000b0041400885900d81164424000240030400c958028456414105449049160b1080442d06c00c641c484000516104040b142101c00000c402014001c181101c1858110a4142d0004605150460340020340c50346050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 94382104 1250 94380854 94380859
    0x80303150301060504020a02030a0206070302031b091206010f050111010905030901030b01050c070306090c12021503180109080304030f050a09050d0614070e0306061c020f03010e0d0309030905040c0e 87
    0x40c00c4041540e081d80f1590003400002c00840d5117054200c4c02940383c0d00025050000350240d0400620700300c1c000d000316071040980035500d81c1a00060300076080540c200851480e0000c0e0424101450040104002400f0348640048211100e1416000405140781402c81900d5641011003004c0007640c0041511210340007402c0119820081c40c00488460146040c3c0400a00c40c021000080c0052640611001c078041da0740c045009440354002e04e5581e49043d4025001039000e07070f100b0b42844000018640040e038008640300e015000da55680e080d6101c600307003078407001c03030000502040580248000c8107020345403c002e41400d07000d050240c10301c0500d20920340626030380601c0504024143d070041c0842c08058803803030390908100b1401800d034044804001e000b0710407130021421f50b10340300c8940c6000c50495800b00d0140842c9a00344003034180d000c0110b541564803404042d8a00100784031103050000955000602c10031709050041040c60603038825409a4945400040095480034280c151804c0c107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 94383354 1250 94382104 94382131
    0x82b082701151205060411010e0607060209010905010509030a061d0a030801050f010816051606020a05032a0708090f1203030f01051804020415090507030207050c04140117190609060510080303 84
    0x30305005079042c072180101d0960051001906d10b080283310750240220746804e81c0c4c0c201c140d03501d8200548082c42000c0c621589580a22140300002d9880d412000c0c0c0c001140c030030104c3d4001e4040c5c49a00e0041d4640f81180811011380c0103005a003000219841c00360000d2034540c425080c8810403001c20484002291b04020000800d40d11a4928440c5c246031194010421507840400c0b0000401030342017036442c421268506141c0710715660441d801e44800f0007581c0b80b900d240240c0b680e61010203a000d5007072590404d01c4c0d042c160003155181d038a002c5d80c0c0722507240a150341c0e00e041005c0c01031160058000511a04400f00021592141200d0035540954180ca0000303455410400c000d00290580d403100740d500341003900f00b0800c0e69254001e010858859001c03100b1040f68000ac02c002e0b00d071805d81d0850455400b0b001007100203034601c0c2020050721341d0300940d0030250007100742030300020091100381c0301c0036254494103040122901c02d09a024a000e100c8505007070078030101c00d403a0b04c0b0141c052001c4814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 94384604 1250 94383354 94383383
    0x4080a05030c0f161506150309032003120906040b060d021c0305090310110f0a120903030b0a050301090302100b0f060d0501082b0827011512050604 65
    0x44000c2119072858036450040d4895441d08460703c3c0d8244c010404031100500c00c200010300d807030940201001e80d00501c04403011207a10b104100e00030617501c0c0050342000318000208212102c40114886054a07503c040c69840c1556280420b90f07500107801920711f94072242c204004503030100e4105402a5048441d45484030a600009041300320345000e001490100320413007001c250b0010000e01c1500c50030740544410641e858002c408880381303261600c45080b000c010b010208850702c0000c08862250303080010075450200301c041c2c1100c00d0340c601240440d5031032040280758a451505200240401c400900a041c1c003a0360007900c6402e042a60081c1649800c1040c1d1103039108030200c05804800f404141e1100c032001e20480141000f8401d69106000300c401d0789404621030b08940128054465040341c182421690403075200703c008051503c9d5480c40044142066a04207540810440075000410710480c80603540b41c405100343e0203404044a080c1c01003000500c0841c400e0781c0280c106114035440700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 94385854 1250 94384604 94384621
    0xb010c0203010203190507020a02030a080306030115080714040e0d080a0204080a061d150708040302100614030c0a0f0302040207080415090f05060412060b0d0c120204110304080a0503 80
    0x15184001d515500120400061440b1400140199a9044020301050311a2030041c0d0300ca0b00340d42406501a0400e14598000c02c1d4540011a0000006000010900da01c6a450a15101039030011030307250304042820491400460740000c0303407400c121820001c080540340c031031f51390305040f01c0d0010070b1104c2c8000203a0b0714991742e81618004c05042040e108940c45c03625018004200d070b421a030700c214806d01203035104000006a400c0100300b443e00b0302800c980315494180c880704001402181103100e0464410000c0e503490148000410880510a00c1c0390303607010800d030416400e002d4081c083c2036489800c012607181d00c40c002e02142d4054030010390710389840c20529402e12075034204040c0c50140c0c4204058059020408004031095040c20710217260b11001000003a118511030074844140c600f441c04040381280d4031509031000014603040c0c0401050b62420886485a07000d0700341440c4c05d90003141517041900070010142c1089014034038526059440c48018083c075080103041200c00f1000a0400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 94387104 1250 94385854 94385867
    0x50604151103160c0615091107050c13090f0f150c0912030c0f0b011a040503120307020a12050a090501111221100609050906030606010e06130f1403150a0b01 69
    0x54110320140811058806c08001d00c1109100c1e50400d10700e403803000c20380c10348054155511550700602828a03200282c0403c005812681c10b2035503416a24052400000c0d082000300c642035108449038040c919081c10140013205240c002210324a051400140034a0b42c40054903040e41d811a500380c00c1c0210a06088030420b40207980200b15900b114044800c1c40803100740e99048540e42c039507101c8106102d0000740ca40b40624412180c1603030142011940c220701d000040d65104901e48101e42c07004400761a42240c0700001e003045c4000c80c030700003440c0b201b15a200d204800a0402030034400c0700380d008882040c0d605c00303420040c00e07007806010a10303040d02031800d203400e14400d09003555040107007000c107440040c3c4021440303440003040d107130b440010705070a02078400341c81500c0050181c06240c0e02c10b0010344004d41c00342d40050744104d00b0031007000400a0b00100e60003804407980c00d51212401e03c000344107500302e00d1895500c00e600941034a51102c850203281039000ca1b0700040420038881c800c1c01660340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 94388354 1250 94387104 94387127
    0x906090a0f050a090c05031207020112090f0605041e0c030b0408090a1403010c030504020f090a02040b1c0b03030c0307061e020703020a0b0117030a03021803060405060415110316 78
    0x72800d0805004040e403441d0002c0341c0703550103400300b0003285a8070810141c0d030703504607071300e4031100c4105100090156000349600007181c094400702052480700e41d56506507464409000b214503070343d50414002807102ea007001c001c1a41c1c040074024510041610355000801107407100801da240300d40001020020644141e0f25102d40180c010b042c207030f0302d554655110110b400c00050003980f8000a2110282c481d002d058061034000e0428011194803000b40502d21750014810030342d6680800000506a003d140108110103e02031007030000040320003640d0540c0c2181e14a54801da00500c840820318502004569050b41c3c041400500324800020034920360449440e0840c203a0b101203201400c3c16004500040114070034514248140e80360b060410301c1e600d01490008590780148400c065a034023981c010300d01240c03482c41c000d4001038603600007031a00708211400c0341d40b5002030f0140070411072002c555122541030850103002290020320711040500000780284080c12a40c03500d001d070315000700e0220b0380c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 94389604 1250 94388354 94388381
    0x1050d0b03010605032b050f160c05090712060902070b1602011407050406020f010501060921020603130b070e010e0f0609040614010e010518100504080a030f0f0203090906090a 77
    0xb0b10001d120401280340d40a41056000c2e018120350f1b0300059204204944404440c40001c07414601414828012460040d000300d0782d682c0d03000d802103020b03500d900e03580c5e102d1a02c0d0341e03076500b013088005c00b207200382c9403143c0c8034124090041c0010703800104015841030740540c2251300c5a1600c603460004034054241d0440748034041190b0307001c2c080c1d1180d0000062054030456000c40d040d0200003080c0c01d00302c0324244200d0000400c8041e09020300c031800941d0031401d116041c05070551408076000601d280d441650800c441c1014150307140101b0107a400c816134000801c0c10640320100700b0130f0018082d16070300e00e0720314030650a41090100d945da5102c01c1c0c400d40c10015004124481d21680020320090100c40500e020800c19800b0900b5903200344111a00810808402003005e004c0350240568401d1400700d54080c00320078000400d80d40380821482a446000340e4602420912446000d0162a050003080341107400030024040d10f9111445016041001520700f00000d588014030040104501040c441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 94390854 1250 94389604 94389613
    0x306030a14060f06010c0201081b09060409020d0c0801140d02130903080a060f031a10050d05030409140609070f0e0d050609102708070b0a051902030601050d0b0301060503 75
    0x3100d10000844502c40c40a0f07009100d126250f020054418041300c020007800111200c000840c110481c402c0c0c0744449807880442410320810340b000414541040c2c00441c0eaa035400308181c001e281c6103004e01c2c21505140c0c101800f05505216402405142411160f07001e00c0076131a8200071920b42200c0107403580c8181d0760803c03901130585002032210000b40c6440704050705151010a601c0b9422a07000200e030360003511000340001c02255900c650b28014128000c94000c030200151760346030001691142445200607583c3c40c0c0c2415400821504000c1201c58082e1840e2708100e074544602d09090341000d2903003000d4074680345290341202c102039581e9483d904000c1114041c8100040000c3e4a03006008080036110000315414001044440030058401c1500c05991081480f191944038200c20900458401d8034280303003500c400f00715407400d45401e5580d59546042020b49442c0d8070343d520300c00c0002e060a515505282d00002c10314022078404a0030683d4800c240c4000b65800d40c40b1030000c1c20090240c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 94392104 1250 94390854 94390883
    0x306080a1407090603080309060105010503011508091608151f030311070519080c0603040b07140702032a010903030e28150f0e010903080903010e0618070509100306020306030a 77
    0x12046c5400030384401041c0e20a00001140640c041c509807030503229242e104610100c0703146411200e062010380440c3c03050098a00b0a409241d65210840250070103400400350114800d030340715a00c070401000f0160200d1411008001ca240c0307406010102c1e0f0705441e00d004c0410000c46040e0808030258042d940c8400a82c01c074507601420000c0107400c0741d0b009e070700fa035003801046800d110705480100c1d002000c030201e0300001282d490080e03080c00318142815112a05102c03050380802c1c0307070181000f4100700101045080800f803140601101400200a28021000c035103150b8015010300c0d07a024006100302da141c80382c080d00741c5900d640c0e10b415089400c01c44100d141d40700c0d80f0f20311248000c0c03000400600140003515206014804441f00302c00e06940e1701c90268510703182d02c0a581c010b010303030b00e605548480300348480020401049004103c04807040391a2a80c1400c500e1803c181c40e400140600c55560402214400c52180113080301e13000000981e403551404002818000e900b140200700000c0c101c0c12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 94393354 1250 94392104 94392113
    0xa0b03010614040e03070b0a09081935010e2a040501030506010810060f030209040203100e060a06020325080406030603060b06180103090204020d0c0507120306080a1407090603 77
    0x4002c2c52034010343e030401010129203010f940f81c2c0724a6502901c21603c80003c5000032071658032145c0d41da40915486410200c1e80f500c61b001d4801c000d04544005507881c411580803104845006911103a00e140c1340c0c1413411400c240c3c01c0304120502c161030150302900c000414030005441804602103810364440e0f500c44902003100100c2e0805d001c1c1c1e074000b0b480c04c4001021540240741850103036800d40b5090500501d0810201c1d4900d1803404042c04040c1c0078401c4042c60f0703c5500145005004001003000c001f405c0400c11403070290300030182c5210b07100d20380c0c0400082d500403041b1120700c2c01c443c01d00c4018544c06480710711120303086030b002000b1640014000a18681c594080d0782136a215171030502004444108024060191580045010f080800d0301c01040d030013540300e8119503102a0001d4144419902080300729034030a618840441d40c0040c540007008101c02d240391111000c0d0404112035030802803504d5079044407503402028140d2581c005018150b042201c00014421000d041c0440d5489191 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 94394604 1250 94393354 94393379
    0xc08062e08010e07080421052b05061c06050421020f0f0307030504060f0314130201030b09090703080a03020418020703030c08060f13060e01150f031a01080a0b030106 73
    0x5202024162070045a10503128040146c0a1a00a9010004050045c486c00d000d0350181d68840140181001103014541c3c4641c10b030303034000b81550081100c85c0310030100c1c0740944100a150902c1120704484d1200300641c200e2140141e186c01240001c0e0310741e038900d03051421041c620b0404401c200c1e102d00c1c0701803095001640c0c0c4a4662500c0540c0c2d1601c012400423a03490007050001400b16000740b0040c8801e610880303445a1000080c640880c0c80103092585604054060f103031818140c0240140c40c095503051300070901c414806841c1c414052604000c6540c80702e1050000404005000940c50700b220f110341c0594001e840340e017580c030300388c414114001002903011480860200742001c8103148010301881e074040c07056902500040100c00154104030170304421001103403500d03944200100c0c10300c070f80d0f205c1d003800f810100e00b0314030742c0c4507100034054040d042580d140b2040508280004c105140801d4101c1100c00b800c0c200f403102610341e0103c1a02a214842c005030b0150b00c1c024000400464209 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 94395854 1250 94394604 94394609
    0x91003020a06020c0d0303050601020309041401050f01050315010e360c0304170c2b09080303010b04030303022107020d20030f0915040b04030b01090c08062e0801 71
    0x2185074001994070b442c240d0b1100c81c1e800319103520000b240d01c2c140c0030a0086c0c008581c4000d0501c196440d01c545500001e00300e0300c41d00780c410000084000144040d0524113500e46c034160090a00703074110701d810918025251402450b2504129005072840c4180c2c03182041601c44012001d8007a04101c1003020000d031305809034000040300240c80c404140d2200d42442181d010b40e41250318a000200c65131425110382d488000504054450141941400400d0f4021b0540000380c8000040c080e658221b8001c1442c2469001110243c00c00c00041040e03000002c12941142c1d41401c2c05038032103040248110080040b2180e403400d94525034208030f0a6035001c1451800b16030703503480e182c400d45502d41090070090b02460b0310840d0342d0310400024440b610701d80c024095000e00282040b002e41450294640c076504181e025212054010805008215074064000e02500c141c140400141401200081c40b0940107800c0320f025400d00508800140c4404d5861010030a800a940c01c1203c0745c100010a03402c400d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 94397104 1250 94395854 94395859
    0x50a08070f0c050108090a0f1b0803040f060e01050307123b0601050d03080a0e0d090612021204020910170309010207080d080c030925090b0102120f090103020909100302 74
    0x600b008503031580900f0505000b000d00034010b201d4441665100302d1000f03000b000a480c08640d107006118030300b0441031500050580880607548592802c032a1504080b110b8100b6024072130807040c03903880340e60302c04190307030340000c5514040c886009103107552001061481c02207070a00085c0c110030780112010b8070801d0380b00c0c00c100c5403d8061074050384100e9102d00080c041d243e40241b2018148020912903a440341e04405690000100e00386412946450202c52425080120f00124020000305030070804469810a01a406515101c01071f4500d280034400200020300c5a12003c000c40c0310111101400d01c0681507402440303901d0318050f59500d58a130001d00c030160040c40741c00c0b4003090741c050105045c1c0b210380703290301c4217440d50f100c03007101c86200e80006020038041c1c4100038400c0b120480034800402c01c00420718442c00c084d4100501003069403a80005030341590b01c8003000002010900003182e0031981c5c040d086d15110304480004030080e101e14899107900410250521488040160740381044900c03c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 94398354 1250 94397104 94397123
    0x13020301030b0711101d0a060507091508010501050a030f09060506040f0e030301030b041406041211010b09060f0d05070b1b071a07020f090901090615030816050a08070f 74
    0xc0b1803045a0a101050341c00010707800400111125407059040416000b86c00305440c0b154240c90100f480c500310b0311040684440340c0300c109000c0101d0700180307680c02415000e080c0608042803840080c10000040c4100d40c100000000c1d95254036109a201618840c040032050100720b005050100141200b51580f0340326510f000702413090f803403051140e1034407204030401a505580c42e40e22030b8445628028001c0c3d07031200004c1c106001180b0244002c5105034803508000412141086d0700804d1545004030b010060381c50310004c110190385001c401070344524201c070110907100d0480d000c18014802e02d40018030030302c10903001160511302d4101901000504811300c1d9000d45011107655621076081c810080d09085d940b441190109000c0000c155542c009440e411505241c000410050b44044440103000e954500e50b0000300b017100c5c0140c4802902604c090002c450441e2181042440307007100300001c81030aa02c2d15010044144840455584c12420b002d40b03d20759801c0505013201c1d040800c68a5211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 94399604 1250 94398354 94398361
    0x1507020c010302120c130503060403030c02060f06010e13020d0e03041505190503090a020d0305030906060906010909151205030c010c050703050304140c040f06051e010f05030c040513020301030b 85
    0x100f0310940d0039140982d184a400d07626a1800f1032a0390740300f44281c5090000c480008501da0318108031a5010318480e6900140340170841200904000d03000d481002c04405103003e00c80e040e039000011400c1c0a40c1110b0b241e442d4055910814000d00c61584030140b0380c2d040042d0344803c0346c4040301400481e501020900588980ca041c111000e11428240f0342d0b0f40100d6603048050316100310013460b40803800000700c0b8900c1d46580c0010f04440d400c140200c0024100004020902d6070501000c2e411610075200500141412400a014052907025416110350f54581c110b92100300c1804c031030001e22055203800b01518140c20001c1d1250301000082c0030541c204900179003124801c804551784280c1503542e09065031141c0c5c6e01d12400c40c010b61418070151040805d440c220303a41e40c0c4a40501028242000210300303140a0230f00c0a40780032840b03074040400c504022440a0707608282903119a0f0054940745989507600e140c1140e05015603001150003444113502e100a0801550046050364010b001d186100d0b074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 94400854 1250 94399604 94399607
    0x31504060609180504030f200106030b0103060b040509031b1911011115060f0d02090c1903060b160203070e0c030106030609090c030210020705090901060504050726060a081507020c01 80
    0x40040e00c00074002031400c46c00421b0780e40b00764988d5003c20041c481022109445c0001c075401d490b204c0d041034031070501d19001041040b07094890481c20280c151000d104034600040380c0c1d0344901900c00e60102c421071182ca20480d459042c40407418500c414261804641d260342841d0110003184425180414112081c200c0c0b00007000070000d032420300c41404103a1075643c040c2484000400e0a03900d07a0460700c1c09540ca030050f540c90840070b110b110485001920707050084803c00ca49051800c4400915107032032401e100180340070f07049482d03400d0350fa04904903615503880480e14002d116400480484500c07418451401403150080d8101c0720b030ba46d010700440e5200c100100840d00c00d800e0040c4881e6807560100018140402211405400d50041d03030101d41e07840000ca0f0490204071407009699560300024007107490300748601c0d504144c15141100ca403901c494010604000c001c031001e00010f44110000d415940e03510301c508064008a02510300001c01c1181d845c014410541c2c8020141c001c401d006a940d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 94402104 1250 94400854 94400861
    0x90a05090f060f040f080d14060307060e010c02061e04030b070207060e0607030c0c05060d060f0902250503040504141008030a0c1e050106061e0507020f040203150406060918 76
    0x19540780c01040c3c03442d183c0350307110402000c0b41c0100b11042c1c0e100b0f220b2280c405406114010303035041445090401c500e0702008160400c0307001d030404c20a024040c101d05a80d030340e02c420214101036043e200b2940e05c642000543c11001c41d01404c550411100060100c00c0001851100303004000039001c41d00d50303130b840d4001512065016584982c2082c0103128a1000c00d02c00e00d04114082d000e51104946142c0760004a0540c4d40401400c12110352a10401c000f1024010302820003040324070320460034103a11880f0400c03100307403c800002d04009488008030603c0424030481c3c0003007100400400c4501e2110340050000b1900f00c40c03040309015140d000140e60540801140c0c1c46810a0b980e0310362380300307896444005894070000c00f065404080405030b0001391003489104080c01d0710303480701c5980300c91658000013001c0c91902800d007080014480c0d02c00603112122180301e203120071113001d41c480d5103040e117040c1141003100340154001d040460014025030400c2110058454030203140c0d11005031001288140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 94403354 1250 94402104 94402111
    0xb040f0b0301060c061802191d07051b010e190506160f05071a0718080a02130c02160906320409080403060908040f1203020d0e0f090a05090f06 63
    0x126002075200400030b82030390b1002d82200c04446c1522190170298000c81c1c03100ea2854104403028a8000c002e002c02607814030701c0d03100c40c0503110701900e017441c0c44c50000340140641443d600946508400e0405460030030b40200d01c1006a03c8215a0031041c652286045d00003ca8003c1e1030702d00915020035901403a140081701c0e440b0054a4240803600070002c12079140e40a003509407911960781948212518a0f84031040c01030559644500d40d03c01c0c80e80e5074003280d0502c0c0d40301e4019035026403a20300040c4c07900440c08030981e000c0c1a0005000404a1003a0306001304241c9444007540b0403580461121480e9208409480419201c0307a044101c0d50400c8074542c100c880500941b55448068a2561401c1e030009802e803442000307c0c5040a0343d958400040d1070a90104482544000c201400324603100015000148101d0180c003461426a48000c2d407100200ea00300c508000d144c0110f1a02c03a12800c41c80c80d6100e02c06400701c1514580b81e403030280105406ea419191030f01401c2d0b8241c03502000010014017 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 94404604 1250 94403354 94403357
    0x14090606060d0e0a08030601030b0109030b011a0910110601080703080d020c0304050909060f0c0a0f0f02010b0307080f010c1412060d0602120f0a05090d03090611040b040f0b030106 79
    0x449494810401010381c0004080e948071039190500344542da03c05000c80c1c1003040c03180302001d85900380000003509545440003070301d0400c000041d041000c1580d500b01581100c0f4281c24401c00340002d0485000d00d403180350021600444644410380d9400d90012900074880e1043e002e40c0c09590301d4110342c0e51501c031140300150a034202844517480581c0550300502c1019509030490346007941e0344001c40c0c06010110340d003c919801c114100b003004e0f8001940d150b8002000d0107028580000218040d004503075800403c0208012000f96821140c000d50000b1186070004003202d04043c0d46140342c582d207085140c6540f11079420729400304545402031341c4c190548036045895600b0030440b203501182e01c0c4c000030f00040c0e0152607050080b011a07805c1c0300800410124180c0d804030707440d280c0494034041c04058244420240350808000e810072020415a84915451502288021090502002802c480985241c8800000400103001e401c81001003045800c00388010039560358404800031903020900c907410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 94405854 1250 94404604 94404613
    0x210f0f090c011b06092307031208100308041203091401090501050d020d09060c020607020c0a14031002040602030405150901170c0706050702030406020f07050d021014030c0307031409 80
    0x10666014400d04004405950310f14002c80950b0740b2100c0550f51520820780b443c601d10480a034542d0b200703031041c0d034009070f002000b064114a19540e09502c0b0340001802010400d805010035a070300c9007000b54900131a000407680342c035240c44041150312259450411400f0600b9070b440011220302d101000d081c2188141c40d0003800501d004d0041d41e0991040c0320300a00705900700003500003880a8414141c0c01406000001500001280064502007015100d903055601024880707840c2d1755200300500079030b040c00c1503401758180d4010129103004503495402503a10b00104d80841c41c5a03000025008455040303030f80310050b000d001e5551340d851194804036800075840c207048030103980150f51841d4101e420701c62207a1400001c0d0f1151402c81e001541d66400581000600300314240d0304110340081c02420102500240346840001005120002402800307000c1175051014114010304802e01c100d400d0000341703a91391600b003002452662040342e800c80428a0701e0246018030142c0313111184105d04d81d40061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 94407104 1250 94405854 94405873
    0xa020705011409210f010606030b0405061338010311030708010306150b1201060e040b0a0504090203190c05100809100b030c120a151503030302090303210f0f09 70
    0x2102c840f10b07000d213426030070360030800320380700c01c0410811010200784d100c00019a42d4144200103095030700000b0b05902c614185018480540c0c0d51000710500041a0400040d88014500d070b5054803058203580c61044400c00000120004800c000d5110b002a09a80c2000708014280e031158981c00300759480030001d5004001400001c0d0a54411000c8002d88504a9196961404044181d506c103803a00103660031104010068642c0046000c00000d000321410300c241c3c8000c2000c150001c0b0f00d84607440c8903a4454410340305545052054004a201103002420590030909280049051902c2410b000d5100c48940d01034007403103044414094242c0c0340141001c0000e210103000608000030449902d4007880c0c1400c03031240d840c02e1070b10501100c107001814455440b42002614088242003001040d800e00d10114501da203480ca683c015a941410700688803014000440e165000c0d0318180f01915100400886201d502420214494200c0410709002503450881d085507140003611010200c2c0d0100c07401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 94408354 1250 94407104 94407109
    0x70b030906040305071a07031401080c15030a09021507030e0d080306010f0905040e0c0f0a030f03050f040b180f030106030203060105150c060f0417030103030203030117010b040905030a020705011409 87
    0x4040300c9002e1003052102d601e003080344816086c0c00740c0e0710a02182e41e98402d212428144600d2500500e03000c0044c0080c048020045800307612040852050701f032000001940e200c0c120b60119200b0340d0081e125401c1d00c1481a415031069000741d90a40100b1b800301003801591510000807090198091004c50554446000640750210360384000b000344500002c0200b1691181c1c45141a600240e2000709204c81c4e064052140d20350b5103014803409550f200100380046a00c2100b00032080c0d0345440d002d56610360558440042e40160341280100e05000a01e45200a1090044802c2a50126420380c8403594800400d4225200ca10000350140c001000410407842d10655010f0003d1580e01c07030703910344031405000740c2c1002c0301190b4000c1c1802c2140140414800226031640c411080c14020724615415a200a990780c0014031842403610000b0f04441d13003240d001c0d0007203101450043c2c010b1017078203218035019407030740c02110b0042c0c01072041100001d001c1d803181c060f10308850308041403580b60030104002e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 94409604 1250 94408354 94408357
    0x403050f1f0902040b030a0605010603060512060c0306130c1d0d0c031103010b040203011203110708030409020f07140703030806030a02091303020114040b0118050903032707030b0108070b030906040305 88
    0x10144da009a0300c000300c02141e2802d108070a003440c49501c0c00103907581440409021100c0c190082801044110005a6201c20008807580c02c0040845550b81f29900c400020700030754809000407062506143c02d200300c07103400041f820340340d0440d1380c10007464055500c1801901c2200072805040c03210384000800c0495400150740040c440064008a002c1c0c1500c00841c013641e1003079000c04010052062044145a4020010a0702c050540d01401e1401d01c0c0408403903a80c0100c2c015450a50350000b00d4070303045508002224800d50b031010840c0e000c148100c18540c0c46414902c02607002c95038a000240c07003803901142503844590f005103019900d842d01d89110001c1c1c24915003c0307041d990380e0660f103411001c2c080c0d4074600c207038400c8001c03007070395030400c460210160000c210104545081600f4030200601c04020b0303d9001aa0298a050442c100da601c1c4a800aa000c1c03400c449025680000c820310608071f48150603501c940c0119281c040d510101c070602d0b4030080300d500c2d100f500402c0204000034403440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 94410854 1250 94409604 94409621
    0x3060506040b0102031914070f050105060d05061605040f17060601090f06031109061201080c0301141f0e0c0d0e060702030a12020421050f0a0210030903050d0c03020403050f1f 77
    0x904400c80002e001d48119855200d42c1e81a275022480e941240704000302400f0781a8802429552144030b0f401a42e121503842502a11581b01c20100045a42c03196202e0001d4074002e014881d41d107440030f607403404288800c003c6100c00d0044d07406140002103095001e4410346088800048200c0301507450070004900070704089001d440110000c0040700711503070390309001c0c240c004c5501e0403821a0794540500c2038942014120464002d904003204810206041004980d02c04c0c00302d036000c0401c0e2488601c0d00c031084001d401407031324001c20b1410311129038001009444a881420300421403d405140c1e40e5507903000403500e102c0103074401c1003080f90092044a5407103002d0a002400342c02c1c143c03030b01c5080302504034450b11503010341c054132051030500000f0046102180448005003810403c03d0700400e08c94503050300c003d400d050703c0f4640304080601c54411140c4581c038840c4101b0050380710700e00081c0690300910003070710340780f24001d800505140d010420002009083d940484038914902c03244010305841c1c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 94412104 1250 94410854 94410857
    0x60b010c121818050f010e0f01060e1f18061d10050c010204090b040f021c020a0e0a081e0304081c03020405061204020a1502100f1b03050103060506040b01020319 71
    0x6100009402500445416080b03c0488021880e8a40f00074807483c400c07016400940e6600030b110602c4103c0c1a20502c80c0d055a40c64035024404000a401007070700d090507000f0592110400030002d41600358031040407880c0c00d481400484030310b41da600003126146114920f942c03150340007010075811303032500903184c0906620300e080250170090f10450550132a0000d5020481540d01d030136082089240507c200d812030034660200314100030400001c502c00d03105840751806007540c00500602800d0003114034440301d1000070545080c2c50b859100c0c1e1919584904403a030000704a80440400400b404406c2c4c41c10340307510800420704c501031842654200744030b102c02c103814594200f00100d00354503140700a000132401c1da490030b08641030900c18800d11036000e80c0626a03440000c03001c2e540301c0e80c2c01f086080c00c07034007203501c00b145c44106403003004004e056400030800000d80701c0c20216030307107a0550460f40c101ca01840c01040190744801c20301095a00301c00f0546e005030010171120966100be09058440d5031500e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 94413354 1250 94412104 94412147
    0x30c0907020f060108010b0103150b030f0604060801020c1f06150503060a0e15010e030705060d050a020d140a20070605090f060c0c0610030804030b070c150207060b010c12 75
    0x24920360f814400d0a811220b01c40c0d445020090381382d609030185524140041e0050440c071751412140c640c40d404040c2c4860710429444c0c0c0401e482b65a2500001c0c050302c0c520000b150341c0c08000c0c0c0d07425510581010003007051404010519030200c80c9100c3c207421502940b000c0c0b000c001c560f41c81142c8a030310080140340d015403c40750214002c21046055072080c0c901c02050241c0604c6803002414540c000c02001c0d200c1e6001c9001408641c5600050f42d0001c0c4103041d01099644540c800714002c0d00030305801c00b0840c0d141c004607994441107070820314015400c1e5901006040304074442030b620311045501507043c0440c20801e110024404c0e9020581c408d01c0d0909480c00d0183d40c1d45e0140c146242651103050f10750b07002c034404d06a002c0c14049603800019020001c150315141d60707540c82c0180500e1001502c580400b070000f03842c43c0d011301da4800c0c40030340c8040034130590450700300d190000750000d04080c0c40c5280b503c007400c040f650103060b0260410350484024140341c00e00e5030007107816100740420013604082 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 94414604 1250 94413354 94413373
    0x50607062c061f17010e03030703021b0f12070f0b1005031b030a0305070206040b0726031e060a0315020307020f070b0f0703140309010c020c030a02030c090702 70
    0x5500d021802007698815014000c0d001012814a4841c0c040c0219188004007407401c01501e6141d41250116582400c11880f6a810242c0460051000c00e0071900c07240400010800c1c560380c968002c001c0d412841c079002824990181c038083d581c0d0400c0b10010b20350750003001c80102c01c1d55040c020b40000c520480707400f90710700c0f071035a07861f82030340016100640c001c113003030b074080c4401e10b002c3c007010107070040700b52a0400c0c40bc64440000c0d82e41000350f80c00740511074001400c0055403503081c11503018010200c105c6903100e90a24014041041c4a94505841941060b0080e042e80140040f24001c2c141358503031000321425028070841d107680c0030303003000d621038400040000060a00c0039a82500e08580c071005880789005880603080c4140b0002c2021542c201d12800d0042d03081d1041914200c1003150881900e46807035141c141e550142c640b0070040e040f6004010058078100540007420300403066400d039002c4120180a05550f9030b1304090007581500411a001514141b0424240d400791482c81222454034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 94415854 1250 94414604 94414631
    0x51309081303050c0103021e0901020f030a091509081b040b030f0a06050f0702300301090207060c03020307050904020304060b060a0c06050105090402090c0c2b0314010f05060706 78
    0x5001c01224070407810029002c006120050180c00c0103c1d030f003820b00390300c0c00100c0c54050921201c00310b81041110800701e600b9140b40d1080040f00b00c00512142100d960343d840107405000c100d9603100e9a019050704040421449101f40000d00840c0d03002030040085503880c90110042989180e0200d400c9550f59080244503034040103142c0c03440014002030b1619148504140054400c020110333865000c03540b0230b00010550000700e51080c00b0940c60060881c207040e0740c00750001300f1b007204071a111000204c00070603102190b074010310341c0d41d01c1210b0070011410805002e4040c0e02085920b14003058040c00f444c40c0070b05054001b15800344c411507001030f445205000107040e41d08001e4541c00041c812000070810420244a03090140c0b130125024022458260300048400304c0c01001040f4040001c113400001c08010001102100c05241c4080b05601d0703110410300c0e448140c81040740003e802d2610712520b099227548540d0580e4001d42c44e124030203042c042841307103079409103004540e0107503a400d0910468 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 94417104 1250 94415854 94415857
    0x10201150609030c0506040e040b15040507050c0105150609041802031506130e03030a0c023906040506070b06030a170d27060509030f0301030503032703030105130908 73
    0x148a951103800d003143c1181000110083c85810290003601c00b040140228800d904850750711940c030000ca002540c0e120384140b900c0e105030205054126040c2424800d585800201402811800100030411035680c0318104801248182001d074100a0412402001d0b007816001703c0c1e0300111600c5508941071840c4c0c00b0034a4070b4010780301a14011000004d204043c9003402002d6400c0420305018440506101d801c3c80d268170014103080b03c0c0c20340c0d610620403224001d000d01c07684955650002e41d801c184da5003680b20a4100c16003412000341000401c154a807401006076400c1e0f400103000503060980b82e60f1070f2405000003500c02c0e40e1612445900070000f0705490050340a803030002c45102c0d1108504440d0800f52015440b83e1150022500007022b24044840e0348007160640091000c00c06444001b0702c1c1c1c0c15485400c0c98818480340000000c814420008001d5005a54828001842d1010140301040048040311070100e190020001000685804845991030720110440001d0f00d40f09550360880d04e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 94418354 1250 94417104 94417109
    0x30f090f15030b0a060206130c081009140a080306120102040e09160b03040206030604110c0d0315080c0306010306020a18090f050105010e0f09040501270507060c2001020115 76
    0x21041e140090200680e854014940d80c0700b015910440c2c07240c1042c4001c0e403141c800801264146115050000c02d20803824601c000034040d42050b11001e0380014812030103842024001d50360086005030442601d400040c803a201d00d034004900a00399111202000380010040c401d2a04564007404049040c001c411051401640c0c01b000901d00c01000c0454400552042d6000310340e20a0248100001b50301c803035044030b41c001e4044600040590212200308558015003d442c4618801c44800c1d580c0160182e0242c0b090034280400001210340e2948169a904801103203144c145e040036004000248460300507100011030380c00e1a011210400001490540c181d50040d10300588848049040983c82d1103103501510003881e281000201002c0031864076a000b030550f078040d01c66040001c0c1401406c0d4044101320b003081d00e4010104940d0628000e441c0d05017107043d501030051180008023203000e40c0401c0c00013a44054030220310000c500040d6181010a01007078155501d03800e0444110190f501108007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 94419604 1250 94418354 94418369
    0xc06070215250b07030c0503070c1704061101050105060702030316030201090f03080a15050303040b090a09020304060203091b01230d05160e12121b070815070309020d030f090f 77
    0x100090b45060007200058043c0446003498a46000f04554541c030208407944020035007881080f90020b4136001d040540000030040360f0840209000c02c1480e40090100d01710460700c4000d1082c1e90700c40b410003c06208030b59000394507030b10410007a030000800040100c00320307019000001d14401c0070b480e50400d440a10004400090602c000c028012840b80301c0d80b0125111090010066810100444d5407485607028807440c503040828419069914207040c540a0310f07440500355164282403a040f00613420035115000e060044222080c01141303030544900205105030340d00c0c801541480c080000c1d16005448446028604010132400c070340c114000c2318041c14070543e0b0500383c0e00000b28010000030000e00f600e80302d0011038680709107601000448031104103800d0380c115034528010240c10520660000c1080d540d0080003000034000902042400101c85c0441c2d4005180c0d03a81c0c8001c0b0220f4091410003903003e83c50b242200c02182c410380080c107105402d410500c484070349807038906406541039840f488 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 94420854 1250 94419604 94419667
    0x304030b0a15080607020d031d010f02070215072d020306070206150604050604031506031407080d140d0507021009050601080c04050702030f03060d020a0602010510080c06070215 78
    0x7581d804010242c070005103c1d120240482c1d0900c10402501c0346141400001007540391801602061960110b825600d00e01500030400e4840034501080650030021040e80b00b00444e507036240100c45842c4c00c55089540c44034a4a8507403076241510200c98849040f07400708016020f840f080180c4040254500602c4075400508a41c0f80c640102c44030419a464a0707401110306110030020742d100d060507201a00c1d40252441c0d4154000840c031f50003010b03154805440c2481e04075000343c1c0e0301d101240c43c105443c00c00c6d00703035000f0f0250040241c640503116500088003140030400d210034401c856000d01d0b0000c005106803002601103400b403205440701300805980940120300104020242000a0101c1d0070003034805100f949032480c0c000e9140d01030441c02c4901d8000c008002201940d445400c0011682e00419071540b0326221f4400070b00820f42201d04102c02072411102180325080000d140d6002000244138030f10306141035090100e800110f291840c0082e00520203030001a99000150941d80c290b0309244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 94422104 1250 94420854 94420871
    0xb1903051b030319020c040c081506190e03010e03120114030313060302130504020d020a031b0507032109060b1306080c060f070b0705070218010501080f070c050609010e070b09090f0402030304030b0a 87
    0x75000c08880091480c2f25410401c04091401120400120028000d08111a0455040010a02502c1c41c0359043d442c078040002d4603210221a002c0003410b07900180390f40d2200e050356a050603500d00c28031001080c54040385400300301107403083d0001c08512000030a80c00081c1d03030300c5003c6002e130780100c3c0c0307801d021700e0300400c44207040395151194558814241e8031360034142c1007080340540103224540010303040051000200780d02c50008002c0b500e519044820030001e410003801c3c561700408040340d030710f4403c0d040680744003008101801407209580d0043c020340010301401080200550102000601001e028007242c0081450180144d2040403940c03220744d69609144100b007101000d40f504116000502d000510041c0d03400b806550780411051f01103941500c3e440001d4689107440782e4014817511a88042240c00071040d006420304610044c1114212600c4910440c0c2500441c025242c000f109200000d001d8900c9203651b940184c00030341078901d05a01c0f52584284038104480b80c407076040c3c0303840d0700c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 94423354 1250 94422104 94422121
    0x40f050c04060b191701030602030702150f2707060302090f0d0506060418120f030e03070309050909070e061306051807121802040504060b1903051b030319020c040c08 73
    0x44075a00c81450007a01700b020710a5484500b44060002030001940071002601203802008403201c50160700c030b4030602034544000d104004080403101141d01400c40e80401c5a0805080d00710503440610388090020581458070840c002d4004a8448e43c1c0452140c0d600401500d401c445581d03164000d201411403440c0640610080c0c4081411684100f1901040c1c1c00115807400c0c0360044074140c0d0724000e40c0100c6200022006040c40040190441c00005008410141c0100d102c4040b030b001510440180d989102c8640e4030b0fa4031500c031b0400740310442000100d942c604244410a003a4041c10300184290300c520114001c0b0030943c0c4411200c010341401d221f54550000f080982c1345c015804240503002a80346009074291410800034081e030f8981e4045004c011481d005000300ba0405801010307122500003e01c1198007070341c4800d0b943ca002d810104e00c40c1c600840d52444580c2400742c025490030045480c013103106101000e0b818214041c2da000302c2c443d503445006604400c8020364860300d40d41003520300d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 94424460 1106 94423354 94423387
    0x3020c0307080d0c020c03011104090902060c160608060a03030c110d1401060303120c0e060310030611030919111e030d17130b040f050c04060b 63
    0x49070200700d455580160b58210a90b42200d821b000300406050072212185000403074508200f0050007400e00f5504001869032010300214a84003031400643d050600709402c01580d200c0b01328041100a501400c4503400507030459220400710700e5950003401100089400605015400c4c030100e40c00e03500c40a4031085140c00150082242c00c200301010b0080c80c25000490225403120768280100c0210712840b07018410381d4483c440303c854014201b100ca40c10050025003580e4494101000250603400f80c2c171200d909150900361a030410b09244c5060a02201c1da4070f002442e40025103000c11802d00040c03004020984203483d140c1061640d00c80b48480002095405100d030f8804070303c2035076001c20038606001443c00c0603012500e40c40c90381180c03884481400f401c40c0c0510710200d40485c50341220f1900c034034800c001703c900c4034825201140031703510a0391240b8588075010a03001c24200c04c414 = true := by decide +kernel

theorem cover : BRFrame.Cov 94244604 94424460 := by
  have h0 := BRFrame.cov_init 94244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 94244604 ≤ n) (h2 : n < 94424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
