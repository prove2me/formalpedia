-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0651
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:56:33.906983+00:00
-- url     : https://prove2.me/submissions/ee17e828-06ac-4b26-9293-d050a3c0e7a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 116906474 ≤ n < 117086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 116907724 1250 116906474 116906479
    0x10c03080703200a0f050a05040b070c0905040312050f0112060510050a080a060f09081e07060c1d090c1804020403050303010602030418111204030e09090c012304050609 74
    0x30650403082000342019541840703010b0b00c20000441907001303a00000c11310b000c02d03410b141590034658804005000c0b8800c5029403d9861400305118080214090032a0040c245011080c00319080a190282c2946041c0240d0880d1a0078000001c014090760380d411812100e28a821000c2d00400382c69001c0207240142c50998000803118010401d900c84c91a8200180092001003101d10840e040c490300310344840c04482001d90038003a0003000f03d4940d001740c83d01d1804408030410114001a8880940d10444600410550403d0158203200f500040c1c1c20f05c030f00390310460080900a0280070422400000c03160560b101c0000e000e48440380603410a20f075908240a040145402d0b21381c2c640e2440d580091788010010390000806021140c00303030411009040d9600710600c00704040c41403044180c0900140a2060040200003a00b4188514503000c101c8401401518850500c560300d2600c6a403107180040c046021408a0f06000c5001c01c1c40100d400341100d50281440e00b03005c10080c00c2c2d4403030136450f80d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 116908974 1250 116907724 116907731
    0x4260f030c0d03090f14030d0c050f04030b1905010b090a0905090a03032018010905011e080a23010312110c1002070e01090f0b1e010c02190602010504020a080606010c03080703 77
    0x740046c0590380305000003400c42d13001310b48a1048a401400b600c040d40f1002d8100039040c840030300b075038640c0c0302a00d0a60794060a0007e26642d0f0b10798640b9450742d4a0300d02c03480e042c01c0400008108005400414015605407500e1070102e40341c40c5a103068502c00da5002e1215841004c0c0e5a020a10a5020140b0b44115500446010b030202180f06083d802c0902406079440554954101d50740e003100011009103020700340f17000e182000c1862400f030f80b441100071509001c81080001d60101e0117601805052496042c040c4551000b06205075001c0802d000072508441900c820000c068000d07009120101c580c5070041c8007040948082c4440d41176010500000c1d4030074960081049100110054041d124003c000035805510707500200988074021441d81c094a151401085031099401d01104540c1081c2003040e00300605201082158440c05820780c10720030a110b011807000d82c1900614042e60007180d110040c1034072400300603261001542e165000c10700e12020403001900500501c0d500c0061800d000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 116910224 1250 116908974 116909003
    0x6060418020904170d060504050106300603080406080405010606031509180b040b0405071e05010f020f0f0a03140c0c01080705070f11040c09050a09020903010204260f030c0d0309 78
    0x140d413250080c40026042580700c94081c0000d0600d44076031070050072149001b00100d242d0803041021070126a842110490040c85501040c48a54000b0002194058070580e52140d942c50010303d103250540d011140f65013412030000d442882400350020084062070348404040c0752420315001480308107130788039180e181d1040c200082070300342c60024400d5004090707580080c642441d1140c01e080c030b180c0180d551510b074904200080030002515500b900c000b03081460a0420446050f803400c1c5d91100c034000184604041074031121004580b42181c00c0c404d0b01c5101640580403c0c442040c090880142c074958805007400200f50b00c01c94605400072001e0909a03e4221903441d9034401280609007900c0724004101096502e0500e4032807600c00301712a241c0075281c41d0520340040c44100c0c4034415240c0390383e00031440001c990707000e604650042a0200d50380342240c001d040c041e140c4043d0034440620310300071010034505801b008011900f840134046c0c0034101b098403154064001305440700050312501444c00d0b08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 116911474 1250 116910224 116910263
    0x8121608180a0b0f120712060906060f02070b0d020f041a03010e0f070807050c01020f0c06060102010b0307061202030a0e0a03020c0319110607062403020306060418020904 75
    0x189042464644801c100e0340285003404801c01c400d50080003003003001c02c444d146810070041a0b488400b4140305000341070f11450000c843c50f01143c89100b554501d000000038620109030b1001040340e4140d204d4120707103201e02d02d0a07600c039400b0384a0322a05007000c20651880520030740c010801c3c40040c625050500f500c0b01c070320304003850100507501458000080107000726084154401e038816551007420059140012000f02219000f030000340a112000c211405906001c0d01520301c5481070011264032f44a1103680c00d551680305136505409540b070a80340343d40da0f007404107002099401c0b60311000071888504201200075800280100b40203640e0b100c264a01500c280082e2041e0b9020b0790091601509110806090842985844c1410111a401130340040c1949803804200c044c1166540e032101101d081041c00703001c85006214060301c5400c10044414050f82c0307900d05580c0203804660030355a0340f0b0140001ca45030103200380e0348000715a0810f070052400091440c3e105201d00709500c0780080c0003c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 116912724 1250 116911474 116911477
    0x60c12090b0c150112080702040b040e0307050c0901090501080325060c05120a06050d0807050a0f05060f0702160902090301062c24060703170a020703030b03060108121608 75
    0x416160355008042c8002414400d000c5003409005d50002c009503800d000da82e000c80038440e10320000d0065403254546120f07a990741c2e000700d24148110058940d241418075015458000d5107034680d02c140104000130600300450700c00c4c01d05844017034004518120303000103002600310201981e0306040040d007200100244043c091160385569548801c2e448000000c030036103d1010007420740389030a01d0b01008000320359500c140f6110054024030b115542e480b2030704000d420b10310600b801518101102c81420b04100c400503001e8410340750040410415107981c0403c98484c002e4402003581d1070344408040c0000c2103598010070703d183c0020000240c3c559100389407141d011044c0f0190303000c1d401600340c8000b110545c00c14141e0100c0d0401c28901640c05500c0c50301310803020011143e001d002c0c0070846508150040058600060711105e401c0d0345490300c0e10701c0341e01a40c054035044000030b041a203020075905000030410b0603600150081c29004003021510714203500710314510784103054008800804075072010b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 116913974 1250 116912724 116912737
    0x150f0a03020903010f2007021f1119030903030e03161701180206041413020304060519140f100b1308010506150904110903010515010f0504060c12090b 66
    0x31000750320b8040203810107017141c821900b40e07801c29080c07030341c0ca40c17242402c0180d0124010810701e180e5101c6070341c2e0002c03c42c00710031202321642100c5040c1c854001160044985c40050720800201d509910303000402c0c40040481c0c43e00200450014103050001a000d40705951503650f001d0111190040c103800c01800004840e40505071040010001d810940428042e10704038106e00b01404103c8110b03640412501d1107184500c002e4244101c5046000d5a1141d929641070000c2c601e0664603410b082c10b11100070101524551390070301e58210610407000c090f0041402040800c104241555158140318489060080840c0d05422402c41c0228000c81c005001e01101c2074044220103031103080481c15030071140081c01161041c078028240c0c1e15481026800c80740d04181c10749010034880b02581c0c003038105000d510070840c2c0c503500309401c000303c01c9040d2090f0b00c182c00d001d81e80c4104080d4a01e906403400d204901401e00010705140c158804a02550208038080b02d01d1718002004550355950a00d4680045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 116915224 1250 116913974 116913977
    0x331305040b0105100f1b02030c09010b0a17070c020103050a0605220c02010509030304080703090e0703052418100f08070609060504050f0f13060f050102060901050405060402150f0a 79
    0x1c0005101c00d0816003102400d1a103d420002c20039000d116000c3c0110300c0002c0e42100c1c079460385904004640b0140b058500400c0b016180101c90f50f19210300342c1040d04041038000003c0ca48054601a015034000b8030342c01410b040d1200b020310020743c1c00440142c40c000b030490b650300e0307240c0000142a80782d40c4500c0c001c00e24910300003407100400c99500ea0903500c020100404580c1440180201c501000c0704980d040396105000d40e80e1040b96203005c1e51480880d0788256101002310f410001c5442d09900f006104d1015032003805090716080030303140402d0300d00814090704400c4800d070224844504901c820703049076411100d41d44160f40c8812030202c90426400000309504004810400e46421000e0759010f01468149a4145402c001c0410f00b15003140482d03e01c1142c03441c5080c800c1d61641c84440c001142c0e5030300184511910303a441300c0c40512081c40b81500501c5014006000501c042c41090700450f840f50207051592a41e07020054408464042c07440c03c0c4404008001790310384031000421681341c49 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 116916474 1250 116915224 116915243
    0x807260a061e05030601120f060626070b09040f0902150705060106020c0303071709090106021b010212030a0b01140a020d0806060703201609060302040533130504 71
    0x7490081d2541020000040003010015101400f099401040542c155044100441d00c1d5054a080021a1000e065009404949405004207070303c0d0f405030424032407042c040c440c03e10181401044d55a242d40d944561a41848280060f001b1840c0c00d410a801b42a07001d03001080d480d8440d000140103c2c000b41b003d00c41c14400246400400106000c2207004040324006410404681c90110791688035107800200840c0c9860506100c1441c10010ba50f50781001401ca00199031711084065030700d40c490200395045245180100c4429840050003441c507840812205003141c65250b031010181408264050501120490f00c2c080c82c0c2444014115941156004048440e0740b91000b411351200607003803030300480e81040a0000b280d08801000c440200d185203078840c400e0800b1101f41484017a04c2c0d10071524104040010700b0f841207030410801d0780e000715000c00103074580086601d200515030030b6140c0da4855503128207400354040d0349904064040030700b8100d1540c040e5001541100c3c02240c0450303c4c46403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 116917724 1250 116916474 116916479
    0x504020906030d050403080a031407020f01050a0209031f140f10090e0606100e120a050708010209130902010e0d060509010b010201020a0e0d08040302040509030a110c010807260a06 79
    0x1800e804140e040324058000d0140c109042c3d000800900c00e600000c0d050202c0000c1c07170f81c03809100c0e07030120700c4103c03011015488500380660025260842152412010343c00d00c1d0100e840212103100f220301000004008100d00c400180c182c001204840c5042c2c94065aaa0340321071615007080c0b0b06520039200d08095400501d40039000340703807000391600103110a0303103094107000e0590030002d10359400c9041260200c41100f2100d4048421131060a0b402e40c10840d4411080030002000170154016032080c1c09036100c07192103070505400c0740a003110f03441d84500252150400d180244e88000d1880740185032440c1200156000708591070060403080340c42d2541c50041000ca141c4c01e204425103200300740b000754a4400840c100420340c0100148032441200c2403c100800c0000d02000c8800441c1c0c050030510280c900043d91319181d0300013103200d00108000d50030740f085101020036400c440070016110700400d034498000c02c840c0c1c0e942460034081c142401080004840a0702843d07584104403649020403083d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 116918974 1250 116917724 116917729
    0x1303020706050702102001180311060601020a0b180d0c1109040c0b0901031b020706090b0a140306130e010c2a140a0804091401050612010b0309030403050f01050402 72
    0x20041d03100c04100a824459400165948400059850704074901000340350ba011011651200900c01c15038029803812030703a10f0944441d01031034a201c0380643c4850009448040f44030f6114042103a04a0040c3c003c14040f100280415820a400406401503c07840851030140340f0302d002540120745011617201072031724003007040d040e82c0300c04049010303038000110b81029651001900c0080c007603440304050100340401c4036442944042c80e042c1c2618040d965442c003c020194482c03505001300c4c00007408070000410000c41c1034044665880185d40c0d207645c0350110325040345940c2c101601a59004031082d440910000c86070081000e901c5080000240741c60b0045000b41480c00b2845100701d203001d00444000201004914600c019508802102d54040051765510300b02003040380000c01070040860003250001003a031001d480b15038180001e1000c0c1c4d803114100310f154021541c01030000c104441c0140700d40e5141c08007942d0010100000c4900303180c3c499884908110b2402040c184d217a55403010030041d071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 116920224 1250 116918974 116918983
    0x610032403030e10110607120e1203060a050105032404110310090b0a140d03020106030213020d0f1416050f040314010b0105040602100c0504030c031109150102150a06030b130302 78
    0x1320b181010706003010410b82007612488000c0c43c160034410b07810b402e41c2050b100340c0c00080c07444100c2800d848030442c0c4602154040e4100f500ca90380141c24005000c522035018004884c000d80903000c0c0c004200702d2708081c1c40141200300021903005034540954012508510018500813140c2d1031b2408a09800c02c2400c10844405c1001c140c810b40741403800304181d0b448032141840a880135106801149014107080c0c0c05081c05500080d0814400d149440001a41c0d5001d03003030403454601d0900841e21044070f42401e880b441450000000301481c086038007410003204100c00c090b01030410703070f051a41c2042a0181900300c1e91050b950955000f45c0750201450a105807111001e003401c0890520b802c0c01c030000e5a07004030425600c0060755030613203006101c2c0604290b42c0103680c002c0c844407409440e4605901c01c82e04144950340103407a802c0200d16810760043c1d44c50380c07111040e401802d59901c56058034001081c05802180103d9440d4004008507440b04038852150445001c0901c000280f4540285070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 116921474 1250 116920224 116920249
    0x5070203100b0f040522030519080705180102070e0a061e03121b0611361c0503160308010806010f05064b030610032403030e 55
    0x101d0310300580c2082a544007041c01d10518030070b481c00101d030ba07150050000c0d2020850f440506464a0301c01607010568003000400e258444803882d5040c290080000ba0f80c508403e9510740e0109034140b00300d0307d00803002003a000381c183d0141304a50748550394800300b480203041921100001525100c0c00d000e035202490760103810b40b860b00d8140c0981c9103141c503880d241c10a07441d40c0004004a540307199040c148c66001000505400c0b000c1001940260401e061080c0d202035501940380c43d6032900542c50031502c000300c02d5031a4081c420f01604d031f0540c400b04040348035510350308601421032201c1d070404144100094280c0c101d590b5080030382d91299040150030040142e2207040c065002000501003607280034048400c45100740c2e1110380b6400c0000750400105520201080c1e0b0140c0d4102c2c510011a210000030f00e030760b8941c0c0b00c50066402030f40300c0044510007120410f0300500c0944590b4001c502c41d9001e083e28514007400c80c00000903552a044416080c0cae0300c01c1d4005603901003c2c996501d0b040188480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 116922724 1250 116921474 116921503
    0x1204061a09040303050a0605060f0f0304050718090b0703090201020d080903040902030108030d0e06151011011e050a0207030c170403020a090c030c2609100c0207090e070807090b060f0a05070203 85
    0x2000030ad440000168852400e40c10481a0b021010030100030040007454082c20302d00343c0c00c51800d1800210b2100400c1541c60a852034081480030a01060180c41110080c1b42c041e0301401e000d84030b07814250b81400c00503091015901c020000042c4041c9039202550180038043d000d150759000e40c0c0c840c1026100b00c0b0001c1081600b00d9001d115200b94422185808120240d840c0c509600150030306560307040104580449550902c3d10307190041d0407009000303600e02c0090804200c00d03140d61101c5401c0340504d01004010440840460b800f02d00c100e2102c64418a509075000d207171985aa02140c5088031036401140c41c41e4035500660182c0d41c050250200000c9280b070030b02840b004148060b828a842c8403d407415114080d0042049584284840b100c0161584000d020b1000c10910080d80d4515034425401ca29144c500340c81b40c88480454050f04840e2410010203d107401c0250803c01003e0060115510200030094080411110b41c040c24101d202c6032141a110003403401490308086030200e04a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 116923974 1250 116922724 116922727
    0x409020d0f060b030a230f04050708060702030f030c1b070306050a0216030f0c1e0506061203340605010302010305060a0503070603020f09280b1204061a09040303050a060506 76
    0x100c0f0320741c60410703240c0c03081c2c00c84030200360140c150760383c01c10354200c619181020401482c20032440750000d00d41140594403c000325071015a980341c1c001d071030303150558410005030401c1018210f403030700c0c0c04050b540044804460618000700001a60b41c070b8841000c08800e00e400c0880d080040c402e05202d03090380301c045440190b00d400130b104c000b994240d000e40c1000b014400000030940b002c601c282281c440c42a8000e6030b0010906505410907940d41000c0d900311818411040080c8076030400c041c074000244640c00c019401c1082e95901034008a00ea1104e401c504003141c81c0341c081c810354440c419200c4601690000030954194000107040c0d44005004500603c03030b2003410002520000b840030203d4510340380050f260340300101c4ca880c00c0d1145600c0e5070b50010282d80920340d0b081703903500d0416106000c1c4003140562580c894800701640a03805c4040078a4032640c000501240c800d402100c0c91034001070f034408100111348002150003100340e44c1070f40001c0d0394508005400c89540706810203064200c43c0103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 116925224 1250 116923974 116923979
    0x5010c0215040c05040911040e0303091912030b0d0c09140a0b0906090a0b040f02030609061c03051c0f0605041113181d03070204150605030a1a060409020d0f06 70
    0x1003143c2d611441094000c0d50303540243c2d07044c807112581ca0860088010402c0c440b012180d00001d550b40c20544000080c3c3c0500e8161000c2c0079203842ca03102c0c4007640a841d102040c00b96040c00d500034440c034503801e41c10800034508a00012a0044030b01d002c0c00d81f148000444054420101c50a1031000741000c0310103103040b0303c04940c2c0d941c4514040d40b250b42201e8006179903031080f0641001d4030000c00c04e0381c1c1150500320502214089074001e944903880a0720021003940c0c5180400c220448403540065143c4100520000401c2c410070040801081005001c0326a50341c410001040740e220319129600d080e0f40d200180f01e10700e0240100c1000c0014101b000303083c4940c154202881704641d10a050300c06440c2d041d803c2c14403400e0b41000d9501d0004820318480301300c62141072070700c0368803481d000c900c0341d0710708004200400e0710b0081c00d001f5103280d40d8a050441e0348000b40100244882070200c8694170061064121030380e82c42006002600c22070700090b88408045400c00c06550b840f00a0103101802c24405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 116926474 1250 116925224 116925233
    0x7080d022a1818070e04020f01051e07082701020d02030c0706050715150303030b06040e0a05191e060f060c0312020c03070b0114041406010e0a080a05010c021504 71
    0x10b0100c45210000c01032054544402d10300d0b03d4164889696024084c99400117500c40c02d213203032544564000c0d5103540311004840b004607205d104258102182c00e00302c0c21060040301d2138034042c00c18513200740e90705403a20b902e075941d040c52130201d50300c0316414101c1d18920300030a5a0510007401c1e1103020b40011414903113048407180e2640c00c82d0240100700040488c80400744030460218404000d911081040b51a00c0e4407003202c20b07100a8001900481e00341400c0450318200203049800301d036485a54a462038854000303410203000e025040c10710140410740fa48000018078032441c440383e50000100001c2e601380e0101d61041e206c00e40c0c000408107011358403c02000e43c000a60400f640d501d0b1a00e40c0b55002e111051030028083c1444000d170078840410058200800108000d050702c1d580039000d1703d050007120030003041c1e420030000404c0300b18007003000c69825400f81e2544540a40002e204042c059240c039640c0e4685001800d099805079110031410108030307018482d02d52300c814000f500c3c001034501900c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 116927724 1250 116926474 116926489
    0x30a1e0c05030a0b0112020f032703030c03040f060606050c1e0c060c122706091005090402120c07060c1719061e0303030b06040f050d0507080d022a 65
    0x480324a00c0d110b48020300c0c00c1c0e100e020401c0003901c40d81811901c8600d420000e21590300111140400b105401404088450340ac001210060031074500652031552004058111500003802c2103452540320b2104c100015124000c2c0d4000d0320b039030b0340c07000d899884d40c9400c0c526041803e00140c0c0e4142e03445c04000321010740410b10300a52001914610b581c0c000202c1c0e03c0303140890b546400310040b030010802c214146400403003000e4a81c4004171811188000c5000c00105100352a8038541c4001030f044483c03400c1d401400a0311580900400041c01c0c441c907640281100c08045404008028002848804020142c890006000c41c1490010304c04040e40841300c0070300740c0c0645403010210260440707522080590304210f01403d45111700c500750051080503440f07010024007089012906250711828141000d0090300e08456200103441e2603586409c0500c4030003002c10700107842c9401034001c08078403103604101d040c0041007554010300e6040d000342c1220159414076480080246c030200d5500080b5602d004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 116928974 1250 116927724 116927731
    0x10501090614120a0218060f0103020f03070c060204050a0e01050a080a0203030301031e0c080a0b09010b130905030705060403050301031a0403051903090c0b13090225050111030a1e0c0503 82
    0x40300034014100d0850f680e8607014040400035031020a041030840300a4500c11074500401095505611400079100194182c0c010001104820f800600006003080e1194480b03529080c012000140f034a600c90020510002c050b03000452082d40b0310004001d54240000640024940b42010385444103469000949900c07042c80040c10200501c800074810b100340145141c049135000071000c0d00903954120301505c40401d50b41c00c2c3c407000300c5800007c1180006008808490390024540034515403045000b4008107184031091305c0506c0305010b4900041c1041000c0d6000b41c0c080c1e22190303100e602d180b40ca0786d410b010703410369007010445c0b280c184000a41c0140948816244440701d0017400c1070348a80c100e005140c0341801a1203824040c2d0300140c8012000002c004c0c2010703500c081c078503140d103c000d82016449011014020240e843d12035402824404c00008121882000040355400b18914444541e4000f075408200d06565000c00000000d0143c100c141801d0030290300f442403c5004d90301901500005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 116930224 1250 116928974 116928979
    0xe010f05181b18040c080708011205030705030d090c08010b0105030703090503070204061701060e0103020f12030d0609020d0507020a11060a0c0609121803080301030602162003010501090614 83
    0x101c08111201a0003007020b5516010409041d101e00044a00e4000d10281d4800d95000b00d180c500303100091889038a40307600c9010980c441410076442c01d0000c1380e503002070300c4054406000620561000950a00090014a40c07101c4089a03044107400e260a442c095503002801583c0740215501c1180d821100382c031b40c4071040e0300f40001c440c905810418114421000300035806071030308030003203070704440030b903e4001245c254802082019100d20300780b0742e0980701703000c040e50040e48984180424030b041c80c071785070740e0822507420760f4103045060003040c099501d1034000d079200540104035160020501d00c0740540c030040500c020007109640d5200d00c8900c0c0082400d0713500440f1700051034001540035030107070090540d010400700070440c200c0c104040921148003582d40010380040c05030050030314400071001070743d801151151440c0d1960760744100941c081e070340b4800c4001418441c03002042e00102210b40d00030341c0501238803605207140304142c01c544050304140c441d00e2a000040c0060350035110001d0042206 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 116931474 1250 116930224 116930269
    0x4060206060108130204050a14090706091503023c0414010f051312050105010b0405100c05070b1204060f020301080d0c06110f0a03050f0f06010c0c08060903040e010f05 74
    0x10044130304091254500d0182d04a4201820700c0350300e0b1407960042c3c2082d00d00c1c0f0035813425510783e1001c00f600d80d40d1074410640040c603454030600c442441010040360700d01c2103050052a04005540510610b10b005d80a1011101032400200c4201c42d201030003d004503407002c04911b05410242805000034881c01c5d26810000320094102c4c20300c0c02a4211750000000c4c400f0b0040196440b102e88260004c04c0c00121441c0d402c01000196218014041d102a220010942c9000c0034140303000301c60211001001781d0340c61144090000d00000d10030010030f00303e05e50500342e1702e903031420b400d100b400c0d6100c01c05041102c0c1d10400040008500218000c8807002d00c5282483c22003119040540150248070f180c0140c0301000540c10764010034a800902d1603101c0758505000e2540e89c0c8000790408281202c0d6507940c80c0803107001031019031290382d4011280d0b1003415440329503902ca4803040d2403e81c0445416450340e00c005400c0c4940c08100d14031a0044c040500d1406039142000085001c40c80c8036948003582008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 116932724 1250 116931474 116931481
    0x6060a0b070203160b07030207090507020705060f0d0504030f0e01020d0f0c080d02030109060314070303090504050a09050d02060105030c09041a060a031217070c11060306060708070c170304060206060108 89
    0x20f06100750041c03140803078a6201010b450303038004c1a403076000c1401200036200b01c62000864502c18011144240304c503402030300401d481c000c00e010180d480603030403080d0370350700700144050741009108050041e8000c4d82c8007aa4550002d4024040c0e100c00000740e81954440610000d007070740e100d8003c0e04116000d141000e017100951400102c0c0f400303080c0038400000c2c008400481d0460301a401075046074010704d0f54001c2c0e804e00c002015224002c03404040c00045602a0034001801c16800c00303070f0000d801d248000f039100000d03111682425070600702000160030030801041071380741c20000800c5d0340700211103220040c02c040d1380d101042000001070f003000e1070252000402d03540c0d40f50780c40380007560440c4e654100c00e016841c004000d9070001c0310120503c1d1080d4041000d5500c684041c005082c5c2c0304140e504524140300421069400003003110394803e03010030010b400981c2100c0035004040c440c24556a0b06400d20079085400312031401404201d40c0188030400c660f55000404c160000020300f8401c40daa07c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 116933974 1250 116932724 116932729
    0xd0e0402070609120215010e1609030203060403030605090a06081902120a030201050708010b090607030e0f0a030b06130c020307030e190e0a0b01090807140f09090a03030b0306060a0b0702 82
    0x1c0e41001605052070800e91000b400740108000052803c00e9096422003000c040c45c0810103542800f079462400e14450004243c9500c000603180d0b035680034102800d140c0d035a980003074508070048404500003600d54600304030600380302c040c2507088a4010b0052028a040081081d0b90312070f40c0c20740203541d0040724000400d6449195254884401041c140c6810144905011740680700c1500c000300002c80d00000020300c1030031241502e035074101c002d101724030340140740c1c80c21500018480419503000154907000c40880e44c03211010001036108010044003841c007001000703a0790704c0d0203100316001030030886c40780c00307881d40070084540322503140c01c11070881c1440001069172040380c6100c83c80051020400440c40306c0030b201083d44a4201c50b00180420705404004494a0301280708184160340041000c0c8040c1c0500c100401a09102420786226040303903000141040c40c0035519010381d40c000303501a4040c03540c10701174500403d6043e0010241c40c2001000f0404464540c0310700494240d0110304002150b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 116935224 1250 116933974 116933977
    0xa0b060406080d08091506011e090503100903020f060c07020d03090902031014010f050429070f020310020306090a1e06080607180807090e100f051b09030d0e0402 71
    0xa08042040b00c1c4018074032440030341000c6042e50614090b1050540300a02d001d2098407487c401c58040e03651000c0d089100e10462000351908425005000610707001042c0e0380c504001d40300e5002e4002c4408141c4100740c0c18040c0c10305101085589254001074200310f10320181c10211480590305440c0b100e0424003a05007200c41003800e4210807100342c000401d02c0760090803030f03c542090300c0d1900d40300c00422004900640b0070384074082900f4007041c01408104288003400322040c4507000d660403035110b602c600b040c410401e940541801c860b4a045650720b01e056040401005071240241c40c011071450400f4070009400440c0100381903042a2140350010b403500b441120301982d2900020180035144c0c036940c2c29601c5034421038601c800509042c4103142c0d42008c10b410001100d1b846c0e4042e00c4000e05280c1490301034208002c420f9018441e980a07000480c42d03500c542e015a941e0060006401e0801c200b44000030056402c556522440502440546070b5000c290710401d400c0c2030500a11a09081020401a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 116936474 1250 116935224 116935229
    0x2701141905070f0602030a060e0c09010f1b05120d060621050403171006081b030a051e1603180201021506011e0309020f0405010e0103030806210307050c10020a0b060406 74
    0x41d0001c4140a0001c21b1a0008e2090b01d0b0b001c01020502e03528903d007604980152410103000070b035900d140b01001030103040c0c080c048001c0b100400c074004603d138803a58948546a000c5a00080b40090481c0c4294858421900075001c2c51070681000c00c04941e00008002d56081c203140d41039518008a030805010b10a070400301900180d43c490f151404001c05050125148980c0011560701c200180b00800c4001041c4440340030055100c1c2540c0380c640b00c440042c0301c028107180458465921300e4598040d103202c9a48103c000102c1914092801e03a0000c00362441e402c007161242c2d100810700e50040c2c3e000300b20101e146900c2010070040d990b401004840519402582c4500ca00840340440c07600d40d4540c20514010b40240c5115003440c01580a0100710b400c248030f0780b4580c0c0101030040c40007d12402a80703400003030080030340303400031070f10a00f40000b02201d11034564143d200103001790800c070090090b103400010807625121361400c01e0402948070384200030700070074100b8a80005503041d504c0d40e209001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 116937724 1250 116936474 116936483
    0x3140304090f150806010506160503040504021201030309050102060c0a0f0c120c0314040b031b09030303100509090a0c090c02150a050708010909030903020904020102032701141905070f 81
    0x91150912150b01c01840540c41c007603042c00004001142d40007000030ba950480b00054041481e06410900c051030b00481c9480c22038040c00100000107444e074441c0090f010314080002d6002a0b949545009401e4510039442103041d07400c1442008643d1000000b034803143d80c00d506002007003030a17800003150071240509004182c0500241030059291f4440c07541c18a1b14440e485440720102500414492800ba40c8100520307940b041000503480c240100110000f60302d820302c240c1c1811050740c0000c0c110f800450381181014203402c03013081940b8001081580240d4490050b0510300d40036107410a0026040c02183c074030507103448401e940755200700171010b0100d1708060707074012604003003054a02406060360500c1c0052203071740c004074000c0c41500c1480d0400d03600d51a81403841f40b03150700b448101b0310010800d03819804240500607420031141007460b00b1418001c0606445101c1400152414041210a01e01c2c40414090024140214a807601d20742401d03040c40780d200d00311803a01100d880c103100c00050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 116938974 1250 116937724 116937731
    0x809060c0a031d060a110414060906070b04050606100302090f19090207141e060a0b040204081504030f1805131d031c02090d03080604022514010b0a0314030409 70
    0x41203030f400303d0514015010040c041c0040b50740c4a03020041d0b80140d024404014080185200c010b00d006402801c48a001a048604005c0261121001c007030b0125001c0d141c9402c050104000c0b4a02904e5000200c103080c1411410420072402046008002c5008079000c2e09544507481142a01c4900b0032008104d510340035541c4150500e4004401000d905070042c5c503101d29020040c012510103001c0c0340503915040106456540c00a0010250611550140c4c205501304808a10314800744048541e09540d401c8a0300141054540142481c610a50300d000f000345100001e6040000541590121203040701d0421048909031160300051010350302800400200b010035000c001008006029a81d0004014404090a00700000700382e1241103c0240d1010f00c0000030000030703014214032508154054401801d08001c0085902203021b014007404000c440e180c0800d040003045200d4441d400894402480b500031034034081248848103000007803101b440030700d400e2041101002076074000c01c0c4428060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 116940224 1250 116938974 116939021
    0x71b0311010e0c0405010b040302030d050f211005041505010305090c06130e0901060e060d0f06110d0b060a0503040311031201170d02070b0a0f1b0c0e070809060c0a03 73
    0x2d42d0b030309400c40c641d6010314140800010b08005c0001581c08483d0040c01800c07808180308030448541c0d0015466244d50901400032407000b1000b0310074142140b84042c0b41d19041e00307100b0760141c0c001d8400e5000030710407400d140d0060710741c0f248000d100085034420b00380414551500c0307003000e0405007007100c0c4940001020078200100d0310014002c1e001c584c0961006c0d4240e840e070080d00ca00b1384205000704990301e94118040359280c00e24910300d0a481d4080c91100c00b08110594920094520041c0401c00c12040031401c640700c041c02d4814410060000c580f001c0c9450350a540142180c00001e2019061020303ca445004114044c0201c50041c0090401e00201c4c4da1203c1400c0703200c0706900c030603c040b88506016104040d00015107071003070f102e0b592540360403c0e005030003c40f60480780400c142d082203003440030144860b116410402e0910310402000c0d20990810f82e00c1e02c00d16000800c80e108200c1c0c000300303214a0a030302048498000091662881d541d20025800fa030281003603103c015803a0b110b60002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 116941474 1250 116940224 116940251
    0x1c060e040f03080a090206180d05010501060305090f0f0705090618040803192a020708010e0d030b01020d140f19020109031b050705060c010b090a0207051203071b031101 74
    0x80805248a529008810340b50001c4d40c2c41103d0790030300000c1d0012030130803180d5025100d01c50341c044480c800500c3c40c42e598105544007400d4800a80c80703000401d481d41c0c2807022440c424051222400f01c1f00004000850a036500d4941d0b8107a00e20170680940c0d0f40c1c5e800f1074071035142e40d20700c80403402740e0301c580001506252410a045a00032103100b54181c4040e503c1221400d0b0a00800f43c1801d0100030140c1d040a01e00f1000c0402c12004104000b5441030110000d00400f081c001d00c02c85078010b00150000095088000d01030342d01e040703c407604541011306442201504010040c0c04108501c2c022611440d10458040d6544a10050660001e218040320811241d0541108458070710950b210045040425900c0601924005001701190080d00307040c001c40c10424040c01c6c070340d800100081a5540750710041034a2404c1580c1000c3c5c000d8000076090705000c030401120292a60124441d441c0d480c00c14001419041c0010203c0c0d407005000c4101c0c801d146c400c0c15843c212140c584c0080042096401c1e9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 116942724 1250 116941474 116941493
    0x31e040303020714060306101101150e060111030f030403020102070c0b090a0803040b040308090a030c08030c0d09050108040206070f0606060e0a0f0b030705071b0e01060206090a05031c060e04 84
    0x440c0148030f466400308a00d020503079000c0c940c2101410050854a402d020071001319048005a420400b00500725298401c00f40078401c484507044000ea0091800c0080325815103000030310050502000260380f10321064000115040c210941070201c0d166155803904901920070076078040c105a480340b0011890840410040a68181c215102d60702d095980f0007661301c90240f80309003010311405101c10000301d643d50000b8084400000d08200d0500d8036036584681d00f1525401c8080c00d9427010500006e0003000b0083c01110351124102042c0c1c26282c8000201144d00c000c00c004e005042c085184c1081092603a8002d00e110b0b0b000d8820b200d1581c80e5100100030468080c2518410780000000003241000c011802090707038440c0103000d2070342c1e0b02c0000668150788001c000301d41450020b0749460881f01019481005400252440101545019002881e001c0040c3c107107000d80e08201c52242c00100c00104855600c940c50340040501c545d8424080000c0040b9401840980000d4003040200403038081e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 116943974 1250 116942724 116942729
    0x4030804090e010b01031505040c03021b06041406040f02060d090b0a0f0b0a030c0e040503160602070b09010513031103130f03030807080106080604050402040f0c021005150108010b030603031e04 85
    0x40200400d05200c00118169070951414541f0446c050b1401e100509041d0040420899141000341c50007840e0754105000d0b6000003c5401b85d82c002c9810701c010003452a48070a1070b510204010200c508064460304802c00c500c5038001e10444000568000c01410fa070840c0304440e4000b0003148a500e040300386131000c0c115529400c0b100500e031408100140c984038401c0d82c2504c2d0810309a40400e4280a4410300b80c45010b0f0042e5084d100601c1703d28100c3c91458100300c5094420240981c5403030351031406200f9924041c1c040b044607410141007140c010f9141550106c115003600e044101009902035a40c1584141d4010021b805c01c0c0c058041f41c50081d403540b45003160b100b03a0782c011041d61031035000c642403202030003580c001a00c0c09001c0b130313000d10301340d0405a08140000e00c0065a81540e0740d00c94116010341c1d0704000076800c440b58032445c08010388a80ba47c0140b0600d8840740c1c1001d0071700020000d000c1400b0361908a18040041a800d44040043d02c20a100c9032040040e6104901141c0b0107a80107407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 116945224 1250 116943974 116944001
    0x43503040609061505030601150e0603100506071208060a060203180a08070e0405060108030a1e12050f0f28240b04030c08010204061b050c0910050a15020a030f02030403080409 77
    0x7000001c01c0c0100c0b052700320322170141c3c0e92030f220001845420070000740d0024100110418900d680425142d031090000e00202e0300c500f8118021054904014040c41c4e4002c0c400c03031250b141908100030f0a90080b003120380340c1f90320a1012030322920000005078854525008068284221070001ca03c110030041c546004502920440700161b0340c4601d910f980340b00d1085290001420200301100788001401e08500041c003e051401c02c0f5144000480110b40040710800d003e030a1480c18060b1800031980302da0b8200c8925104285038020203100b41504450305d40b10040c0c00c560340c3c2081b4280c40031105030708a10780c404c40440c4200ca9070740c840142c0e642e00300e80019034040d07440c181c001440d82c80500c00c650032643c541d150241464418540c0750205d85450006441d00d000350805050355503106901c05201c5c45e030b000031120955090400707118035603105400c200f030b0708807000c0c00018a15400242c0792103150b9251801418586202d24100c0c00e42c002d40d807004000d1400400d000c145805180c0001c40308a204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 116946474 1250 116945224 116945233
    0xc01020d1104081c020102040801022811030f0904020c0a1b060305010f0512160315060b091807020f01020f09120d0903080f040b0d020304350304060906150503 70
    0x200800304858403682c81543c0c80b40d4020665580c44242d00070b440c1c101601c0b180001414569124540c40c2039a214508800c40b501108400168000141c94240c10314503403854500d00b910754a011903640c074070688100c422031510101e2160404d43c1c0da6012507403803104036002e841c554500da150250320400b644c0103907080320b01103a00200c0c4552103442542d048603c0d024a0350703200707803602003400410ba07400c039051410350180070106500741c60100d1982c40110310854980040c0015003000c101218000c0e0407011070f220040010f440380d07913103410904462050518254a960b242d1700070603860006050100f07c03280d40017003541071000c00c015003e070141c45000e40304420800d241c0c1126503164074140803507102240303507200140701103001c1401a040c4002c82d803100c5851300b500c80040004680100340b207034036080d0f0004100301c2004222043c3c880f00341081600001002051001c0c08040d49071120318802c0400b001c000107040c0a0329400020f0b60325045982080141110025940e200a2038091103010388136 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 116947724 1250 116946474 116946491
    0x605010f020624060405030f10050f0c0f070623070207211209050307030308010e010b0918060f130e0c04020a09030308070311071a06060f040302120a0606060807020111090a0501030f060306020c01020d 88
    0x1030491b00bd8494441c00c2001454440303040c001e00f5003900502400c0c1c51039941c8021243c1100440030703591a0b0150300c00e00008882c98002c0c8028986031083d0083c1c500da00710451500180003160300c00e40304903584120079183c0c4045030034007200d200c05c080e80029403500c210303c000410705801441d2a41030f50300300714420b1081c0c1c0e21848550814440c15000540110301d500c0790140347c05c0014103603a0003400050142d80300c07040c3c0c8800540600329548180d0503280d03862040e0741051008010352042101c094400750b0030002d4110b405030065015108c081c040c0a01c0d01d00003050580300380d000b4107100000160701900c60000d820f1580042c80720362912020219100040744040c07030a03e0641e1401440d0161481c58182540c4c24081d80018210710802c00307100f800b030b000c0c0000c0c030680290009000c0541d1206507925040c04000d0039201405240140c41004010018041c2c07500001075040c0c0d002801c0210303030494000441c0740103002952010300b001d0320200700700700c06c071806400402042d402c1c0705040c04001d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 116948974 1250 116947724 116947741
    0x150b03090c03031306030e0109061d0705090f041407050306010b042c060409060b060a020a0b180303010905131b060e0f090403030c0c080309010605010f020624060405030f1005 77
    0x30039200031320740a0fa0030460810071240300790003880c4040b0845002140413034080d540c60080d22400c4242c004200000200d09441c060204103407801000126030101d02c40c04d01c01d100c621105409800a04195202c080e10f1640341010440400141009011200307190f03910611459a0b401500400251028111a08100b440d0401005201c40b58802203151243c60340c4007080b004001022080341c2507501c59860311540e03034551028007991000341e00034107000c47c541c1c5001c00c0454802003106003030840e81003402c103807142e0000680b030640e207854400040d00d444281d401c28185005410040143c1c40c0201e240c080003554040000c200c640a4584c442448006001c02caa942070703100700340740c10031040030008010901c0b07a00110031510003403d02d0081000c00d40c80703809241c2d20440340c030a00c6039102c5038200200d590108950008290f5840070b403c00d41044928580500b00001c510ae030038030740b4280c11b64030603030b1060105d03802040c000f0119040788034a10381c11601c65403401520072890b46007038009862103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 116950224 1250 116948974 116948977
    0xa0809040515090604150513061e08060a150e1e0a0902010203120403051b030408070b12060f03190606050a090212161202030414011d120d150b03090c0303 68
    0x2c00003002411190780781c50034440180040f00700e111107050071000c0041c0d1616015001d442e28100d0341c0c40411824100140e412803104111403102d007050201c40300708164030012445941200740400c1c0407400d414030b81c103041c49038405900541c0c2c990042200b03001808025a852003004501201d0141550f40c2d503c445004841c000b600190144e0810041c0100d07190f410304609902900c2800d03c5420700c0022541c114031448440380c150380301e900001d8284140300c0200040c800401e18200300511341341d100294042e02280c0549120f000c0d14019141c400d4543d0240300040c1080344010380040c240344c6905004000d00080d101d20303030141041c98008a180d50040c000c0700c1c490710084100f9074503130701c1d400240251005c600800c81c00700810f00c2c0c01c60241460320300085000700c2c0280c42080c5071000c1400360720308440f11600c0c085689007400c1e150812242c00400e0b02c2c592809a00300d061b0319001801d60b20000361107600c408000300303004828007294040800000e50701400462007194405200c00040c150b8a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 116951474 1250 116950224 116950261
    0x10b01090602070e18030c0a050f0d0512060f03100902090603030408150a0e0a03031b0e03060a0e01090b010305010c111501050f040b03010e010c1701181104080a08090405 75
    0x5070820310f4144145035600031540d030810015800c020041c0b02d452212400e542198014a6894201039520014401d00b000010b0001c0c000c10f018040c40c460504000e009031081594481246007074000084040d950629001407060006e030503904054814840b41c2c00038400414103e116a0b50300f0b01091181c100042658103039981c07030b40245000d0000b018121001c181c018007403084035407501c02c00090320380203101d80034065200c4d80700816910106458142d21b0004001600204008038051480c0f95800040700340d00100c110500080b420148848079024003400d04000e040e0203503850001040100551020b03559128540e0f541a41c0d00010345415150390305804d07000c001c10300d450014003a915105200f001040c4000f00000b402d41e004c100031a0a458401480c44190307551201c804c41c40c82e41000100700710440404904a0075810481e448501041004414404c6c568030120300118120701c004680150501c003003140c1d210368403031925019070390040c000c0c1e030701850078000400c00381c2190303c0f0809035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 116952724 1250 116951474 116951477
    0xf02010f05070816030203041104090c18050115030b2413031506211707051c08090a02010507120c020303042309011d19020a090305010c020c09040314040902030711010b010906 77
    0x1e55809c03e07003040b028104030300058038104c0807803800180c2035125a02072000d60070b040c400071609624014040d0180c0c00614003510625040c07900546290307540b52250321003a800c440c041c500d81c80f8040c001600a01500220190101e120140841801900c0300c101e0102c0b15050010710102d40ca074011103181204481c0f11190700c0c05100302040000b20060000215110760755425800c082c0140c4805180400001c070700350400e8062403242041c0d81d800034180303902c100340000401c142c400b02c3e40001c005211b0404080c101144880344c03080b07400c5c49100307000c0000c0c1d0000d084903113607900e607041c05441202503100d89400308821841f05015050908440d8121900c2d4003417842c444511240780002140c004043c0d28440ca041810307108000550b1000c1c1c81e411030141d0b00c0b80300103410342c03410f20708450507520781400359031049210000c25558100000c1d84181d141c900518904241e60b100307580d034003e981000e0300c03003070020040004d81e90380329071200107411400c0c0080c070124140ba0015510344915006070300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 116953974 1250 116952724 116952743
    0x30e0d0306120b060f040903050903010c05160602090d020d0318050409150f0f02030108010c171b070606030b0c09040f0509030a03090201020a0515060102100605010509010f02010f0507081603020304 87
    0xc0f030082d062407588401c000d03140c1c0001120590002d81150414807045010440c04100c175040c0d0b041c00d10030311200c00c0b10740c20900c0c07a0a52600034155141d11580f0001c0c203007a000030f0350310f00941b1502201c1280550182c6030808406d19854007808440220400362294843c09000050703c0c0340c24020910481c1c2c20107101c1c1c65501c034800813403014040c0c503400c04c0c1b811600c41006600c001e08170310040d4002d003001c80000440070b41c0c0103002401a8101109420400808000e200c10048008481e0403001d800343c1e83c0030b54072809460058080d28041d44007034a0f260011041002411021000b010ba49070101e0782003040d003030740c1020003044510a49150121b1350080c060074880c0e0b80607900c600c174401d00500407944906082d982e101e20701118101c010006020160a0bc071807960100072000040100100911115041c0400200a401040141410040e20b81c80c141c003130500039030040c01c034084000c0c0140010314203884007404500059505640702e1498407002e8048500ca4800e403401240d1100901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 116955224 1250 116953974 116954009
    0x1005041e11090a140412020f060903030a0903200607080903071101081b130302031216080a110f01270f0b0603030c071202090a060b03061e030d030e0d0306 68
    0xb08540100840c0619a9030000712071000e11141d92140306510034000520b44212140009090428412030b6582c1a8468420700c0345008010040d43c0d405100e028002994181c0390030200d9026500c4026001d41408800c9034140459001c0707001c034416007a9403103040e1281c0b10b003108559a4419040c01030041242c41070038010540c1309850301a0841c00a0790803009261070400c0c4009143d0080d1700d41d090100da0f62004000f107080a011640c50402c4102c0194104400109003030703030507010710000501c010300014540400030300901038401d0060b2000211440d218082a5113402003c0c03c560b05a07848246900010345104142c42480445500100d04200703a0b60a9032940542d910140c00c0030341c540010301140d18040420020350005285480d04503130340003a1070040c0032004101800401c28181040002d01a010210040380d4110405a031049140c2424083c18100301000014140d494001d02650200c1070b50b068212010005a1801361800d80c8070000041c0d044404511540c1541444031494 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 116956474 1250 116955224 116955229
    0xc07050d080901110c0309041a0a12170309010518010203270a0209040506040c21030503100503060c0d0501080c1f121104030b060109030816141005041e11 68
    0x80c94000b00d0b140008070b00719008042402503600300034140c036086e5101280c2c4d0801443d26018540440d0b000021094032007071402d0225808030003e0048000394541c0303004c44820000c082c8801000c10000c03118094685c00c04544081c00b80009480010322000041000d01d034051040c400c82e40910010007107441103d1500a03461b0f4862445182c8000c1030050110003809a22240c0c2654440c0e40b00d50302924251030a8582003e44000507001502190003440c2c0c5003011180b0740814841c01c5402d801c02030b849588040071080028039580213150980107020a018015008101034020004401c0c000d0101c6d1307890344407031561181c03076910070f03540140c0c2e81d4207001c3c0c185000d0381c0c0041e100600340303461031001d485402d6080585040b6003207241c0d80320300000e081081c00100d83c040340e04440d0918100b41d20514540b508540350154080038506040e01117502c03002c108000e4a0b02620090303071300548070a02c08400074040200b400b118152400a02c51841d91002003039141200c5041c1d41c031024810510303020009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 116957724 1250 116956474 116956487
    0x10080606090c1b0a0f060e060c0c0d030b0619020106080f0610140613060f0f0309020d080f0c1b09011502030a0513090e0a05010c030b0a051c020915090c07050d 70
    0x2401405000703007000c0002080d9007442081001780503003004200c040c3c021f03561620340f0340000e00710f03800c0340307c1032040703410702d840204111001e80924507000c540c0b400c500d00014810703c11013104c650b0b0041100030750300465806402c0201110801c1003550200c00c2c1d1030086940b5030004841d140705d880c0102d042848903241d0050702d0a100c1c080030344101e05046800a049a41d5145600010089200300601118696005219840504140c501400500401d901103080540da00f40c0081241c0d401295500c1c00644160a96615040e81410ae070302c007940c81c013100038040d2a00d400b40c60062030400c0010800250b40681c400c03911146070300035403800d40500d208482e650031200c28001c41203100301c2d0000744c05500b40280d0410008010140030340200500c3e00034215000030794080c0c141800e0002c142190754a5101c0d410440300140e50a0030324403501e1010341214058848025070042400c002d00c082c05121a00e000c412200030303200103c890711505407140c4180a0320200400f40d900421010318158807c60 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 116958974 1250 116957724 116957767
    0x50111041410030b0d050114061215090f0106141302120f06041b02060a2a1101060e0403090f080a0f060902120706050a08010506070f02150f0310080606090c 69
    0xd00041ca1512003000103400502580040c0d825070346a4509060100300c040c041c2740c1015048401840c20703050180280e441d2400c040260150600c48400901000000c0c02403400415048000304602511801142402102c0304031083c05850301e580000c0e4114042c2c400c540003084003859891982d80c1e2510003520b4a4401014a034106403200c201c020440d070312080401804046801610640c80d1400014041394010006205802c9005015840144520546086030040d900c0d0105440d06203100c400d01602d0261b00c00791254504000304402c0c194040c8000e0245c0c1d5060f00d40401080d0340321030455030303800255400742c24074010b205040d0008901e5807260076440c1c40900400d03010031502c10b03d50708040469002c00301059000032904d880d1940501c4103400b4090481e00141800000d48480c000810074900081c080c080465026076807c80c034500382c0c0c14443c0d40800155403490929480c540304041482500c0c160b10880012813000c0ca4094003452280e85001005410442007495080c080300404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 116960224 1250 116958974 116958977
    0x90212040b071205040c1d01030c06052a01200304020303030c160203010f050601030f09230709020c03040e0a020a0c1212090c1401050a050a03021e0a0309050111041410 74
    0x205512002c43d0141d000b518425400f9800710b950452500026003143c2e45001410000c0041d404014400200c403201c4074025a0020b1526079141c03001c14004500c0b1605042001c03038054405a003c1d0810a4150002d8030040e07a062400c5240c080103008140c2c1c3c2780002d6074000d6054100b88001028900e040307018054110b640e280c2803040c034041707030040b0b421118500845251191141c0800840b941c0500907400380d441c091004202c0f10078140c85809002075003103200400000800d24060110a0410080001e4100703504115526454a03d046603254002d12440540c0d1082100251840e4024030940c0c850754000e49480511904035902c1031003508500111506100058400000c0c5038801c2c4034020314a1302c034094044005091001c1c000030802100c581c07504100d0204202d00c1400d40c4003041e110820100e003005621b601c02440140f080c4a96219520404800800c901c5022540740d00440741040c010402000304c0c202c80b8181c03050500ca1030040e0305800a801203400642d0411480d920b4181c10175 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 116961474 1250 116960224 116960237
    0x509040314070201051611040509030f07020607030509030f0a022704060902010912060207060e0319030b0a050909031306020d090303050309150103050304031103190615030b01081006090212040b07 86
    0x441c480b410b505c000c5072407d48209407042d000200b141424410940c2080c100070007541005d10841e000b014600c19030170001e0007030b200030803030300101402503055642201004082d900394030b80200805035100d210b00026071050010024540c901c3d14080e100807002c0840c940600d800d661343d901c504000c3e010341481281003040d01c0d400000d00081c03059000411501c2078801580d0790600d820301009440c4400c042d00f0180d002041080b049040c8a01e5042d80001c003070401140580030b880010300c840c11980d1001d034000f02d1380010440c0481c0c0101c0201580700344040e9680c6440c2c0c8030203040781d039110000900c03000b01c0c107541d80c20b002082c001d03400b0355800030b00081190605081d5646c1c03040c3d41d0000380d10844042e13001050034010006406400c4580c400150010590f00c00d501b55600207d00c0c0c13501c0081c0525564110005001070301400b5800a1500141100382e556559903015a656a0355400d00170040d00e03041d00030a800056008842c95000ea12071100301c00e0321103448014101202400e90814000d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 116962724 1250 116961474 116961487
    0x9050d03021e01091406010509010e040501060504050403080610030b061b03041505040608010b030c0f1602030a030f110316030f09080106180501140a0320090a0501060207050904031407020105 84
    0x280000142051075a4000450070140c0e620381250030880c170408114654005030018007440d15002243c90455965141c1c90605484900b05a40108681e401c807a030801c3c200b2080201389504140c02c4d60203040e041e0307002c1100160035401141212440c1d601e80358041c80421403a143d1031101c9078203c046800040035680303010345e10403c0d010360030542d47c045000308101050401215410500450042102d00305142c95071802000000031031041d03000c507a806020100d400c1b000d03001d810288050082c1c0c00b034112428001c9030b0070003600c09000720a04400040380b104565004074404401d54915460010a00902c082035660030360b07450480541003010000c8040000038090024002d02c0d00030150700030400c40880c1c8152000080d42d00c16004210700705003840c0700c42c005440301c000c02d0040340c2d00141e00704144550180c04055081c0d0040480340d00c0200c1d00240440002c05a1205040fa030032902141c502c0e43d03542050051402040324013802050306181c9041c0b005034290024aa5507105142c01c914280 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 116963974 1250 116962724 116962753
    0xb06060d180b0603011415041508060f01051309081606090b0a05040302010b040501030519030318050c0f040509030a140d09030e010e0f13020d0e060118180309050d0302 74
    0x114003070103450030300000d401d00a850900703100d03100302041c0d0101c2c403000614003504c1040c0ea401030000d04a00a517030311280f0740c404400d0340008002503c1ca00090300c0c1641015088542c1c4004280100fa02c614004000160f264803503106503014254401d000c3c3e41004d4005110f01c000c2080c1c0c0005840058a40b00780e400002c1144400700d1040070321040000384c506080c14001e084450030703c81c4034080d40c90701005202003000042c40410a5035800141800180b030785c6801c034081c0c1a924003c00159500e40d201d4001c02a010a0400c84042d00343d640b1450b9607d403500300001e40350169442e807850b0300100015100e135841030161b08035071582c20700150300c0c0c812071070311103012502001d4040c0c2c0080e40c0191066515a4401e4510440e050211452070100b4002c10009240d0960b042c0240307800c1d5130000b5140d8080c10140c002c5500000c2003026505590703980d2145100641c465400c10294604d4450103000c0c0013128803007860055055500d01c40a18249002e2044251000a0640a520610b0075660285 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 116965224 1250 116963974 116964011
    0x2180f040f020406121a09130302120c0102040608090106050901050904030903050d0509190f09020921060402090705070503040303080c09090a060f060201020403080909060114040b07020901050405040b06060d 91
    0x2c01e010383e1054405411000c09000300d030031525030b00f044103446e494400d4443c0e582540c01074004c00b0007810403066013902d10b0141d00e4103c004404403c5d02c10041107040380d881040d80034000715450b6484002103507840702c154601300c507014007405500240b00c0740148041d00740503854641c0980310741482161207460381c840318646044e0448100014500188001050605194640c12325080c0c20810f1541c2e420101e9021380b0b01c0d05c82c0201e40c0030a60204510f161070303540c0c0100103008540416a206003a5049181540303e000459060b4000e42007140826503403442001210002600007000c0e509150031540e044034030140142c8083c030040c000780020000c6507103c0000c280035100b9944005a11480c25180c0b0504c11401d0307008a0a5901c140300801c0400c0688046661482c000c580030710b00e80c1d48404c010f03580d00f03a030101d1852481c000170130302094039600180100740e810300813902c0c058503030b91311001c02c03090b1801240d0090110b0104d1020940c40d040c054040d1038154204400400d411407448080c4811 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 116966474 1250 116965224 116965229
    0x70f030207090f0207020f0414060402090117010b071a040c090b010507060e01050a050916030b100b030c0a031b05180a27050a0203060d030c0203031207031b020102180f040f0204 78
    0x40d1307030000f10281146071880d603040407140269414089102e110700341036042080145143d0240790001914565a0321403212064280c0c00c00419201d65611191250f0807500111000c82e010340740b1020b441c407501403103d5003a110f268021034503400d290a185807034000d082e00e4008076052000c24404a0000380b00c40c000c0100d4070b040300c000090b4502c3c290041000b521800740080a0b15040000c0c4c50720070b0800c00b44c01c0e10540ba0401e6100d40305072140300f01045072581681c011504450080140712480c1410300007840d603109a59400c0c40904550700030030700f0341e00400c0c103d07101140040000280504140d0601201010b00030103041c002665590720030b41c0004484070740e0b481c4216002039604201c00e5441020b0b040b94070030400310704600c0c0a00c0410300305001241c01405000c01110180210f640c104201d41070010001c14142807820711190140c041c20003010001e401401d19130440000a10500c00d60f20543c1100791116a240318040c10712400d91113095003150070a461b403602c081c1ca20400c0c00240300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 116967724 1250 116966474 116966501
    0x101e050108010c020c0f150715050903030a0507080705040608060102120c0106080106090603050c010518030703121b150903090306020a02061e01060e0907030b030d020304080f01020c03070f03020709 87
    0x1e045426980003403d2990754205c2500c1284e07802d2440e10b140d1504080c1c00300922400444070783c0c598003810510b84082c454108528201e040404010503440e010015502804100c4024419920345060942c0d10f00c00c11102032000481c02d00c0100040c0d40f04078040da42014060041d100000c0c0c0c0201c0c55801a440302400c9107a6a445a0040008040c00d01c0303020b00810054030300b000400d003235654264481c07401c2da086504000010a1010b8015000d00b001152031000034101e55002d40c0c1d0b031a018804240301500807012500703205085501c1c0d400003420440042c0d10030300c5585005041403510005021030201030b0100011040003200041d4507200074000341c4044e80060890f442c2802c1494042080c82d10075444602c3c03a0700c0100041031300007101e41e030b0340181120801803907941d10808500a040c80144154144182d0001003002600032000b03005586903001918006400001000d00b0707841130800014003a4010001400400c12007184507210a00c2403041e20340056640d01e03a0002c0d40c039413949095 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 116968974 1250 116967724 116967731
    0xc0b0f070906050702150a020321040b070203090901170c030102040803040f050a03120e04020c0a0c030b06010f0c0209060d15051509010501050a1101110c010b040f0b03101e05010801 80
    0x1454541000800000b008240b0340f0030310b0a44603901050510b061180850582c83c00400c485054038028001e41d4262078201c07104d41c1501c1030110250318811010f031401d560b0442c025010841d01032020046600000002c0d080b900564a0221404d10034841c056104600d1702484042d20140c0c0e03001e000610041130b4820080d81c030755007071045408038081d440c2d001c01d05c41d00e00c940e0708100081c403801c04604c403203243e828848444041e881c04100a842201c038800294001e0451500030041041d580000b600d009504000300340d40c405005680e600b540110000102d08130741c4404006141c10407446030300040180842c0141d540d15a101180c0031075842900b00d43c943c89104004c000d034151942c105000307134201c1c0e00901c6545030000103891842592a01d0341040f0820000c1c80c01110250450b02200c0d19143c072095031841482901402804e850490300c1c801c42c10300d04280e19640e05030190400c01d48009014100ca02401c43d007800007482030560301c07001404105210300b81e4407090700c039142c000c085020021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 116970224 1250 116968974 116968981
    0x40e0609091c05030610020703030c0b0601020a08220f080c12010f020a0c03080604020415030c090305030a02070512060c0f0a1701030c03060e16120c0308030406090212030c0c0409030c0b0f 83
    0x81600b914545012045500104003007020a5024903038004c0301f9000100cc103042d4545400407810884030176805003cae60800200016407801206014602060580c1101038203503c80b0b4000600348000d100301d0040798410416055145055200c165482d03070802d000140308001030b1010f5041c0c2c2c006a001c0700128102003c03035001d01d40c02460069200104031000c601d020f0901880f8400300103580340c124201580c810100c08154099041072000d035412404403511800e03d0741e802540d0740d0311030060314000c40e034803498bd02ca8030301300158440c00303041c1c4090100e080c120700541081268004100e201c04019070001444001441c088046018500030003190200da8254240722054460408400c065a88001c01144441101c08c0100e803d0741c090040708200c000441c101000c1ca03c80300c3c0c001a04841c0c0c004280310401c101c5503c003080d054825075510491000c084034007a1213004840000c801d0385c014400c0c1c202d1b5443d040d80f003054200d2090a01745081c00403500c922003007203c21100c184c40c080d801002d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 116971474 1250 116970224 116970229
    0xb04050303040c09020c0601060807020f0f0105011401020c0a03080a050d0212220c0e09010f1104061112040308090409060e010b01020c030c0d0204020a140703030903090b040e0609091c050306 84
    0x441c0c02400c1e03013482c2540381401100110399668014407600080004500210320701328400d00142c0b500d5030400c403c03520216010b44d00d140c000c05081c81640704880b107c2100d041d40394000f02e01251001c1c402070070050420f01c2d40e01c44403125400264a4400c000c0200201c030907080b072610160850b085d003107182c02001c2c075020b0a00f19103c800d02c04006440702030181444d0000b03040c0c201103c103854121900c031b1000e4843c1d40d50b180c090240c09840784851410b00340d56040840c2d110024008551aa50361a940e81ca1407121240d00c4000c41400751140075020001440440e0308040100100000508002264500d649589046880310100e4000c0c59446410420031580d0420411607100c5044000c3c0002c510140d001900c007940d0820028041c5030003140c01946140a5a41c2d41c00b00b0102c00d805d103070784180341d243c020020260a41c0840100d41c1961002c40c0c651460b1060750141c8004500f01c40385c54a400040090708070b4002c00ca85400e1003180c1040034a021115419041010700d621200c0d107a04040c0c08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 116972724 1250 116971474 116971493
    0x5091603061d0f070813030f020f240606030108070b071a0a09020406051903020409020d0c030803010626040312060302030d05070b09010207051507021c05180f010203250b0405030304 80
    0x480313000c001c4c0c05010702c56261030078144501c01a41c14248903036050f45010301079040400e10140b40042e401104d891410481000d4240e10b02e807070310040704103007580c0c4050400885000c2801480c03c3c0b60b020107824041611400c00410708240100c112000c910311400f1584110201100c4803400740341c560700b604046007068011000500700c21555000f41321410040071525621621000e8403441d00c4d0141c40d401d5456884690303113219000601c2034256612400c104009030700c00e03c103120010320340c641000150325500d840354040025004044030700d40c480791011601002c828100c41e0102d42d5443e80000140d6041102d441b040f001034517000d403111041d050031060018010b12212090b401003003403000240c40407420043d05894810b00c03031015161186c0403440e1aa803070f1080c10007211140c0035000055005000740c403603000301000b00100c1ca15104244407090f01e000581901503813040c00900400e9105504901602c0808031501404480645030703852807110560701a13856400000c14002030101c500d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 116973974 1250 116972724 116972731
    0x311010b0102012f040504050103080c0f0a020d0b0916090605040609050603030a200f1e1546150e0f071205090d0207060905091603061d0f 61
    0x8000c04c0114001a1580b00c801040094a41c1c200c2690b010000007080180c4000e0980900104000d684034075084820f0b40c495030328a00188920361301007681100c00510380703260940c040c11100954040e540c1d8003000101c0908188814068042c0c45d4404c1c15000c52540000c00800402240d49860201400200c0302c2c203401030204d0504240422200d510000122903040c440b07071501759804121000c0008030455020a0760700c50703000344460060707030300c50002e400e821030105c40c041140c00720086001c40f40e48502c2103440f00018072440000075000340c60100100004603083d83d45a0100300a2061190031264580390300050356985000a000501d20f44030b500b808110022300342c001c4a040842d602510840141320081e80b011140014102c1e07440f415030310b0424100e84800307020604015000c5a1600303c0444024018401d18200140d81881000e280c0b0849101400701c5815440c1c04000403c1c901000500b1414961074550005008041c4290002034002085600089040800740b80c1e40810028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 116975224 1250 116973974 116973977
    0x150309030504180908120f0a021602220c0c1a010503060a09060b04140a0b061e070203010e060903030a180c290c0d1e0215040f050a0311010b01 63
    0x48551400241c1040440d000d50b1040300c400c10302d080078a40840043d209046000b4182480030070ba5100c03805c61580500d004018a03004111076540709451320080b0702030040b05c584a0b01400e0080f50250501c400c0d506400034018240044000001c241c10b000c1d500700d02002d4000404016070442402841480d040030032104d881c0c078840e01d5162200081d0303500c0000d84041c142980e034000c41010401554003030801104003600a000300d03080d151441a41200c101c5801d00c1180c10400c0b03005413841d010046881d8000c0d00d070791222910b03c0900d8004082c0e0001d140403078156585482e02e20042d01b0410103948250b41d50002140d4030301c2d02624200943d40d0300741c26482042d0701c3c1d203800000106501211801d0324034200002082c041e41401c0d689140c448004950058000003d2010031010301051000c41c125154032542c0c1c400198203007076500d0b04402080080103070070143d480361858045000c8190002d000703c40c0b12803036221940780c05080c01ca04078001c5020820489074400c0343d4000f80507004050009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 116976474 1250 116975224 116975231
    0x9171501030305131503060303020c01020c0102060a0f020c01051f060201150317090d080903011404020d0803070c0512040302011b020d0803070c390308070308060d020310061503 78
    0x40110112115006000c000c0610402151604102d40b40010400051014002a854140c88a1000350040c0414081079005020300d43e1020070a50001a40011008041e07005000c5a5180e88000b801803c080043c102c81075000c002c001c0c122002400f486d8050380c1162405041103140f1414040c6080013036101c103095906001080d41c0030b9118000b54021039070000e403a4050740440303000f025024031071840c0c41640800c41104d41c90a115614000d0314005070144c008000080036607010b14118602160020743c8030022143c07840002d000c140c0034507000074160505c2d06081d0590366a05080c6400064001200c03600030408009541e409442240a4210200c5040d040241078000ca000358001040c050540000040030890381841441646c0402d500114084403001007109a0a2844031943e00c2d040c42070300c11024107a1070313040801c0e60012030358001030441ca402810fa0382035695840051440ba449441100c1e02e01c0035884c1070003081c4503100c15080024a141c2004540f244410b80605690205842d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 116977724 1250 116976474 116976493
    0xa06050a060e0f01090b01121a01030e0f0705040c0201020c060f1005010302091c2406030606060206060a030330050f0106030209130b0d120f090503150c0a0306030804060917 76
    0x44940d43c03815038025420101e540003c0c10700507515808061500c0445a1071301c0784114441c0c400b44404644024240e9060240306000054680d0300c12482c81d105c02140c1004004121502e0a90b02802c49032601d4000035090109005140d400c0c614116142280c1040207010080200c01e090102d502600003420110704010b0700b407012070504d032203c2d4050046c402036641c280091003011000024480080c000714042000c04190400140c02103200c22a5000d06159001c6402da00120756244111800b40141c8603041c43c64404940500000d84060114280c2110031000c0c03c55191112004050700d4a0110b0309081070705c000c0400e00d105034801810184140301c2e00c0005d9a40301c0c0b41d80c01981d082d01c80803901c030710f00c88000360150005040003010b015031190181c00d501e8104801e500042059140c1e03903400d80d038031401d050b2204051620349000015803400140c040801d1405003840920b1440c0025445840381c0c1c400300b80b039000c1d41200e4041050104200300d107551111000c039030303800c400c006080300e4403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 116978974 1250 116977724 116977741
    0x2280801060504050d02130617010506030a05060f0a0b0a150e010e09011401030f05091501060f0f050c0a05070f05031002120402060901050706090b0601140c06180a050a06050a060e 79
    0xf070fa00409108011100c00c4500b03654070744281c9601703080d4100d005c100310355890f8600481c0251030607221042e0750a240001d44145000700e40006055000400790030591f8403111405041e40000b40700c00e8440741e507a4000515511409018405809000720090141010420244c0403003420f0140c18104200c3c0e80240c8559180d050398203046a01c403500e0000e850807401c00503405008000707e21800305250000b04560310800041140250a81407080403180c4d8a820003110110001c07012800829110515081a00c0c031480c01072412040c801c003030710111802641d8042c00e0203460f0380035040c0084c05490034025454140f15003035030ba4000d28011890901c3c0307162042c10b203d40003400680702d5140400d01401c2c5034003980c00c49602c0e590080c01007180c075000d4503000c486040140d0b051400034903c1081d134410518442c04450350801441c005169541c0d030501b01d0185015041486020360081a0140300010410000744214034803032071002c68946403250440c1c0489050368400321640c0420b400f44005c50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 116980224 1250 116978974 116978977
    0xd020a020414240607061a0a1a03040b040c0e0a060e010602210703020a0c0902040612050915060105040f08011d07031205250b060411180f03010906022808010605 71
    0x140c503c11074442ca8201c51400100a4020344402826150400020030a9000c000d224030050360000c99903a2074003030322046a003038411041d10011007500310400205002c14a40384a49074454803802d101200562580c0301c058417044150385500000c1d44a0000307002111442c0c00c0a80580f03542e03c002c0c2062024007800c9030064407816400545c00500003102003c0c14420310001d00c0311034200c0c0c05410030769903c24800000798090b12880b0005260103100b030000403440c0c00307407500900200d4000c1c1101c040d24000c0420111001c0c1030a070502c90100070000d002d06c2160814001070030034900000314241030b881400300702046c01140c0001900010420310004440600720813891107070789051070702c0e95040c040111110006216104110034040750b03010800941d0a02e0620908050b1800d000b44030035107d000310305000341c21507547c44c10340104420700c0a041c5403c090602090080c000310301c07150310707441e01e9041745e008000781c0403d00b100300c0420416513018802600340301204c4c41d2088041d132600e170000300b0a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 116981474 1250 116980224 116980261
    0x6140609010507050c040501060c0c0b0906180103060305061303140c0d05130503011103070f09050f04090201020109140606091f060f11010c0302031e040b01060809030c0d020a020414 80
    0x1802000f01d64007040c0711040203402e4141c1e001500401036075031580000350070a800c401007250700888000001c100e80d0000c00c1a0351170602e0280c0350604040ea00c1600b003100d0f407030f107141840c10940e07181400804901e00300320744d5004425004c800701040d141c90138001d200100420300201080e400300301d00c059900b07000030516a49121840d0554450103000c14001c1c034030750341781d21055056003400d480040c155640b40007503008500646030790b2440f0889032000d42c2d09040520a290303024916a800c2c0c400c1d82000c4d0846c01c41244140700014011001d540c2e11050303814442c40112280e4809402c05c0000e00b172030f00e01c103900028185e4201d9000b445400e600700010702107008003404c00405950382e03c0301c103010b50110b5003424443c000030300c00c900403d07030010300075001154400d509001034969103050a910600040c010b9400900c042810380c01c00d0000e6621803400341940046100811001c050203c0c10302c071404111a540e4040c1c1070007070160041005890342104200c9103180c648090101061007032032001e21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 116982724 1250 116981474 116981477
    0x712050a050d03360206220e07090905070c020415090f090b2415040e0f060906010302040806010905220c141e0d020a08010c080610030908121f0303050d0614060901 72
    0x295503052040e071300c280008428200307c560b03000c40c002082001150001d1485220035070340e0503d1341581c400c410400c4e55010384e6500c001c922500c0b400c03009400c00da0002c4c420804403031030385c0c1000c40d076442500040700e8a64000c000640e42d207120036010458910a40340c0c0150b4500464050045103d048124031401c104003544200395403020f45040451640036900140782040424079103180c40084c1da88a41001c481c52807051074204005003040d0301030f02c00e0740d0941d103950005240036030030145098010000a0120700071304140d2841420619181009028914482c1c106441110316001c4100e0101d880b103c1a14850301150380c032004582001d9010710000c400850b0005940d40305400811203070f40b0b0300c1d041118030354200340030501659082010740740152002d41c0c102c0003035580f038402203003203400218000b00911802c01802e0101840307880910342040180c0c20480c095000305050102c07401d555442100441c4010034025102c9006100c0d890043c42d080d4000c0005045100000da420722a0740030450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 116983974 1250 116982724 116982727
    0x3071b0f0e151302120c1c050c0c01020a090305010b04050c03070e0d080c0a17030705040b0703030b0402040f05040b040603051015050d0f02090702030a020712050a050d03360206 78
    0x540c0804009010148904060000443e5070504111200030307521840300c130340d01c0040d00b001081c0010281070850f4200f003504115425407a181c000044064040588801c405000c28410121015020b1000f00341d00c00c1030761103042c01c0b1451890202e01303442d030000305a4401c502d040200244050300740304403584540ca514082880f410a02d0008040070b907205c0c03024102c840c0c04a510b11032802c0c00074560143d80d018940c1908a14000b8076210501d00c8200c82050003d00180030801c411501c207009801c8940c440d00740031a00c4d460fa500410100d03045035002090120080700100407030308240c0b08940c1c0360141a24140605400c503214990f8610226a1400d0030a985503209074400680800c0b20020300030080001d405034a140c20f00d41820007440906070300c59206900455032150000048440d10030081e006411781d01d00d4940380941034500380c401543c882c02010841800108284650900c20086460001308160103140c94280250200c01154201441145107500f24821441d400906035044981e00e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 116985224 1250 116983974 116983981
    0x50c0412060f06141806032808030c090405060612061003020409050a09120804111302070602160c0807030308060405040503040e151306210305090303040803071b0f0e 73
    0x501c024140c24980d1240386142080110303000d003020501180d100310884a444a00400f0041208450b00503154540e15a11200c848000080c0400e07170f825031407245c42078480c000c0d109034480a4035a842180c1201041c04000b40a00d92071410713110b03c0c1d800840945000d070030002c0c1018079000344803014217010711402c200d0a0341172115110b9011613001d031a81083c01c0c4624103015500d1000380c0503100049074084c60301d800e46500c4900c201c4045210344c0d0010700e81e43d82b0b4040003040c03000c011120355008075810f400708103080100741d0038001801c40500c4102655904041428503050303808081d00005e9032904004010004250f02041a54200c41c0c01c4400240d5525246040ca1462140750b008000d0542c04604001e50310121f4200d2502c1c00e00700b035400400c25181151910708860303040c020071206650108115007807402021002c41c400e84a030418518040c2c00800092540d08a40c3c0312a20903440041e0880800c42e480c0e14000e403107200c40c1d07441c00c0703020300340101100b8043c3e080c0110103081a000000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 116986474 1250 116985224 116985233
    0x603100e010f09030801181808031b04080c0a0b0a051b0a060c02330c03040203151512070803070311030f07060b031920010306051503040b010603050c0412 68
    0x2c0e03880d10041d0301c080201001c14600509078000034420380f00044103e1001082d913007500d0142c0e0a95010030000c1e070080c00056990455690800f61a01485041c8603004442c028201401480a00050001032115500724010000300b00c41903048001041c80500050124940210956840c05c48054100d05036020b4a540c0314508a00d641c0c002d001a0f00b032548564030140c0101c5e9106440146054070350401d40c2c1c06000e0781240040003048166105103e0004196101020103140c000384003c065074401060b03d60440c21003501982c45440c92a110401a00c0a184c5240c44601c2d00c60078901900f4640d141601d41512070061240c00703000d0042c000e00e518000c0c4000c2c4101d074281144440150344502d1035003400c00040c580003981d503000348544c185582c881061a150700094035030252041c1106003102d840c8101d52074039608490b040c9504c0d008045990b982d05002c90304600803140400f038a80c03800d82070082481d0010380c48502414070b00300c14070110b441c003e81118165400701e0706004902580e441c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 116987724 1250 116986474 116986481
    0x6030c031e0f07060302030f0a06060c03080a02070b0f0603010e1614130204080c040b120a1103010e0f060702010506180106031104050603180d1404050f0103020c06040803100e0603100e01 82
    0x48601e8901581c3c4011440c01c0c0c05901440c003904500d44d03040c01554881540030100c07400f50042c0c0e4003103421000f400c40001c0c4501c40c12980402610000360801c2129500c080140b40103540b4240c6804583d001c000c0389003801d01c074415030190000002c044040116070180d0350004207000e03803030010700001c405801f19107912803294211000c0900c110768a55446c800c45445c0e00c440b410340c074030072407d01600824500d06450b51010110982d005001c1c0c581d5155030340f00c0c050000c2c54a050b00f554803082031200748002403080c0f80e400b41c03e0f0b001400f0180b1f07110380c0c001d00f1100001c10840c400c42c00a0440700141c0406074405054a8403800c00251811042c1c032540d040b130182ea405170b070b400302c00001000095103045015512000740782c02210451080c00009550f250040541c0b020508800d01080150307103018440381200c28010b0400604e443d448030186410030800702e9017a5034a080000c10300c21007580780034030600103100b000350a45045c06c2150020340c65240c1c50205036040c0b52a44000c4903024003c2d031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 116988974 1250 116987724 116987743
    0x4170a050601090911060403081b1c0203030a060806010f14010909111306030b03030906070206070c0f14010906170403020f031309050c0f090603090304030b0109050103020906030c031e 81
    0x1107516660b5030b0400c101c054090a1012030701400380c6500e0001c1c500301030040ea000d90342e108078680d04084644013500c0c0c801c018004034048522a4034200f00360600c203c501c4000c030b00016405103079246010021a802e6404550250540d035002000402000451301d10702021345118078003183c1c01065880048035080b600b500180da6003072400d0030004c0c0e01030481c0c00404c801d02c4404d9a07440e40300d0b80c4207015803c4484520780681c040c0c00800428820b840c2040084c0482480240010706000f003a032502013101c803290708000701d2240480000d100784600d200c0324410040742441c01c0d42c5010b04002008105601d0310301c00072003035980100800c0c1054024410540921700e80d4013102d03126400301d0945151200d00344181c0f0311161801000c60f800b52030000446c4c030209a60107500e8a424042814010b150380001c284808030300040c0804000265001d031054001c00340c07120081a55411401003000707141c409001c4a203c0da001c105140d502d510040f5040034020b44800c5010313845288280c0c2c40e4100501007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 116990224 1250 116988974 116988983
    0xd0305030c0f0a050a03150303021e030c0d0305060a090903090b07021309060506040e0a1703071815120c0804080903030f0c011b050c03040308031b070b0106022104170a 74
    0xc00d00c203002a034800c000c5c1c480b102e0540d406000f5000e04051104104507280001f500580142c0000c10701c0c45000a100130402800c0c0782228500880d400c1a5800c100f90208901d0010380c80390107010f141d24040320800003601c4000d1f4100011880742d5401b8050f43c82d2441240012200070030203106660303821000c202120700e401018800c0766001c0ca4114003c10013210414861898251119540c1d0000500c00c1602503020007240c420100b030307500034021500003d012508004010306440046420322010300010030010707940700c120341c40700c140151400042c030030b0180c9100e01d0000410f4a20b580400e0960f00f103038016999a61301c04100010034150707c1541074008418200046200c900d14055000c03c801c1030045440d2444001c85d0b22040740c103885504400c5ca000d50040c402400441d9941000b150840300403462030011071006084c04e0055040702100b81d408448003c01044003d80500c1805a000d45201081030f0740c4182c0509200c003030003a801a0841c400842404001d049010055041a02e400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 116991474 1250 116990224 116990227
    0x10221090906061b0106030c080a081c2021070c0212121305090705040305030703030c0201090b180c03060108030a030b0628110c0105040915030204050705180f0d0305030c0f 76
    0x1031080c00d4060291b51100312801042c801002803010404507102030f0107980907420a150083c140d0383c00e9204202c0840e603081250341c0782107184001000c60480121542c1e503440d01c945503503101904c40018042c2030100d00080c56040300b00040140d200c1610b542059040381c0115a828980c0c1100d40b400203003030300b6800b28040025480804e00b008048803401c5480440740100c0d2130341d59150440701c1c1d0244e440010042e40c0b0038486540068080d411103411400c1e40d10000803441015119450701c03010954440001c1c41c0400c030340d4403483c88144103900001d40300340d00802095142a00841e942e00c10445100304060342c8101c1c01d2943c0ea9402c0807101e401c40d004865029200000c039015006480e50030000000ca01045c0784003240400c08102c90a0600c030584a15041902d031441c00b00260008042e92100c012400d0400300050b955442802c1c00b800c0d42c0d43d1056210000441419800c2000904803445000000940c2000b56a00c01c8400c00240d4549800d50722604c81e003280b9000b0f806660184a1120230 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 116992724 1250 116991474 116991517
    0x6130618090501230301060e04020108150901090207020f120c1210050702030405120a0309050d0201021c050a090b03061f05040810020307030c18090509100212010501022109090606 79
    0x1500c580c4a12403d6284c0c444c00c0c000200c14101400c84c0c0c41c0344188035000c03484100040141d0f001c0c80220394069041580401001086d83c00a26011003d03040440c0b40f542c00310390756080d820090511800300b5010b0710300e00401c0403032b03d103200c0e6a251000700302840b40c0140807105224040a00007034209050b880d40a20580c1803075800a0344941140c010036015041850200251000005420250a8058a036241058140b40c10710828040c3d581c0144e05500c50b0301c4400e0300d03245c1c2c601d04085020001d13a03103043d241c0d800c0c100020180c500c00e41c080d03120314505009011a035503981642144203640c40c1540c80074424142c006541030f003d990302a19280c02001c2c0300c1d41070006e0300c0e0000d500c44d262641d0108500c114056042c0d440c4100b0810f440c920103d08041802810b100c2c2c1d02840d044021b0070b040710440d004003e50101668010f0310150042409040100081d503010811441e07288210741d250589444900342d01c0c5460f0003051441c030b01c90070018000c80d0880e16050100c508440c40011460700c4d890 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 116993974 1250 116992724 116992739
    0x6020a090911090117010609060e040204051003051501091805040f0f0803070806040614011d0a0306020702090609070807140d0e0d020f030a0e04090204060506040f090b06130618090501 81
    0x400200895003c10780e1501d40000001070805c5480c1038512a071180d4080b85c0c00d150080310581411810540c2255080102050315600e24090001c1000240d074007042c50720b002d070b4021141c6000306201a0510400301e400744041b00118450b81d0114074482800103407507966060914080c0e896903c00b50101407038440310f40c1409003840055200395480d880b0700070591101010301045902034480c01c0072030940c0745503c0c00c007584500b1702c0006041d04100c051002c1341e05000083e04014440c0d100300c0b0707015800618401141404610a076000300d0454140304145054200600480c000800340e0007002200e034003030180c202104065890401d00140c2c2000109a60b81c0700b665500e08010f44000903200300c905000395000c0010403102d03818030a60310741c0e0036094540f0510010f40004c10302264001d480740e1000c240d41d110280a8402410783c007c800b100760b0b00c0c4c25003100c111144691064000d0b88100b0442ca00940b00215a000300d50440c82c0001070148a0200414404060740208401600304000040c01c1e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 116995224 1250 116993974 116993977
    0x1209031801090510030c03140901090b06030307031b03050f0a090311090402010504150c050d0305100b03010e01053d0e060301211b030c1701090c0306020a090911 71
    0x4165980301841000180401540d0701d075101d101c0c180d4807a40072030400200a11035040a80c1440680c1400f040001c0c0035144681c002e0001c03103030358085079500c01500041c020002005500420260091840e0401e1500e00411410952403a124041c00e81c803049020144101c00701e9800a0030307500c00700c0e160f180c0b01d20f0060480c4050711056813803004031003030307660030746000139001c0d001c1d85c1c0c148c5601c0c3c40c04c0e107403030010341400604201040a000380049400e000c10700a100d000048007480d5000a60392800c21002c41650309103400844035040c0500c01480319210b019901c0d4191171040302c00f051141110000b8203001c121a403e04460012200c7e0906214500d00040504151803921102429803c010901c0001d0200340700e00421011280000043d91140005100c165805000520303240c103108001d00036a04071640c0708840d0f03076041607001c1002d803050100c482c080b202c18800900c1610856114000e082886d40406841a90b00003800d40701e150091150600516074050240090072100301d59038020b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 116996474 1250 116995224 116995237
    0x31e0c0e040c0b090108061c0f0503070b0f090d03090213090b0f0c0c07030b0705190f030f0b030604020108100807060201050603010b010903020117040f0c0b03090c04150515120903 79
    0x11804003001c18540c951100341c0d20740c0d07001a511b22050f0342d86c800c00c01082d00c10140300601080c840c450080003050241e02201c07012030003040116516101841d00f1200d82c00001d001481044810007440a40340e004101c1207048071643c503010660481600004008007446038850f02c07018640501c202c200031000e18460b00c2100000da4508071a590040882d6441c481e818610205802c00c60091000400700c3d01c03415085811490034504200c44041c412190805904060700851202c1100320125540750044010709484004184174042141010955841020308000e06104c89c5c0c20000da03400428054101c01442c0450486905c550355000103402030009540b002c0c02542442148030084d405400048112a0306940e8020b45032690301c4861045540a4012a0141007078203240001c0740176800d022024201c24805a96070f800e082c18814030b009146d0302e03070340c2c09a0b0030b2150401103541006254012110241c03a2542019190315001c545c80c4100c0c1c0302003080910740303428070039039502c000040d004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 116997724 1250 116996474 116996483
    0xb0a1206050109020a0507230d0c060e03040501140a02010e010c121802030d0c03030b0405040c080f161206111201050111010e030d020a0e0409051015050901031e0c0e04 74
    0x140d0700d8955540c113078441c4001100101e1020440c040004044000001c1c0c0d800c0840c0202694030b21402956082c811403010007000a9000c401740c0040c043c0f01d214410b0304641002c021844c15103040000f821240d08403908404409000c65898000e5000b900300300d031501c044d4002000b0190801c040500044080704002c01214a40100100c0034142c100c03003a040c050b0001d004290940f149002110704ca945250202c04160f00e0322081c1425444034000d06002c1c501c0340710311554040c00c02c510300d4500b202502e4008010b5100410f8040c244610301c2140c0c090759072624500782922498249240505071060003949581c0c400924451011002402c00b4140c40091b6100c001c10741c600c5400c02d081c0ca24000c0d1114847d0003c100080c440303540c40d40140710160040c201608000e0820002504495803d1000c1c0c0d1a604580280d001945a610858203000d44106c8030202d4142000007041030403074140801059840080c241784003c03490034043c000050b600c0248406802d0f02c58a500c1240801950300304d9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 116998974 1250 116997724 116997731
    0x409021206240f060705120c030301060e010804032c120c010f110c19150804031223060a0305030f04030302070e01050d110406090911030f0115090504060b0a1206 71
    0x11402d01d115020304400100034103644500402d24100441a0b100400031142841450300b00c1d80d0440d078103000b405c0c0c07101210014580720b40c9018000303005180440252410456414208000260041502c444092400c842d041540c281d40514400300150310410703617405440781041141a2600091021815400303030380700c05003240e0070802034540442c1000c200b12140c0119200c1c400a0a0034042c5c051030072401c072010038030107654600030180302507205c9907040001c203800d0401080c0354004c510365003130080b854420890750f26080603c195960031091483d901e5040c0101090b11941c1c1c0c400440080d54000c0c003641c4e5514850741c07202401c0c1e4401d02c07040340940601c00740010503a0080d085a8121807003d48030411100380760340c420384550f81d011442e5520030741d58803020814070030390710819495920800d11945c04124403000c240c605070741c5440c0d82c503036681060303d0b08044202c4000c0c82c82c00c41c1c003e50790200f0f0b9601e40749452005003400d0821660009000100050110050340c4c1e060401c902402e0f080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 117000224 1250 116998974 116999011
    0x2041403030405010c03120b100e19120605090307080a08100806010e0105040203041406010909110a030221010912050a030c08070509010c020307030213050405060c030403120b0409021206 82
    0x60700c80c0564410309020499161001004c64003d20505048842d084030004114080a000884003616180070400040401d44000c2e8141060300d8076030075100c802542c0a0550740303040d07540d000c03565400600408031521200071800365070041080d20945913004140544440c5120001841c0071313400c4880041c130100450001a58150204640d07040e6010030500070181c0e8201000e01001c0d40c4064400c0b1fa825100715a041c54038501070100300e000e01003816012030500040e0074040c0d07a043c041030490f84107500e040c00420050b5a050701307019181c03020030b800b00d90302940b51260320b0051107071030350190582c0100074101d440d50340e0150040203080c01c50380b4100701200c0d00140840c0c02d614202c0380c890114004114031707402503000e0180c080c0040d10040031203080755100d502046483d40210b054000301a110340c00e010401c0418040341c1e512080c40391455003149841c0d02d0080840d2040e021703142415a8503114041f040c0c4441e04561840c42d006030610140f415064441c954070601110104c00c18000500e01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 117001474 1250 117000224 117000229
    0x102060109140103060e03130303091401020114060904080418090b0c1603140408031201080d0c0c05010503192309070b030604022203050c130513060902060d0e01020414 74
    0x34090000b42c55401d544450707085580b004011301e0480b004a03030502c030a0003d00e01400041241c0c0000d14840e9466845080c0390070540c54441e10094589415a41007040552144c500800229809582102c3d080980c7c2c54030b081011161007280c001035100c210b00c0c0d400303408611003a00001c0400b4441c14410350b01d81d4030300c203a29580e4041c443c5141600300f410700107500400c0c03207840d43d00004108402818174143d9a040c10754a180d0103040d1800c40d246196004000d0b01303105021420540615041040605429a8500800d4100b5000c0c05060290100c081118446540c0c1c6c5256504e211840c02c004001c08030078160303020a00b09501b0022030341c5110004051060100300f070822180340c0c2c07100364203540310641000040c0d0083c4020080196440f030094200304032400c00c440c02580200b001c4c14500300181c0901520003a080b40c0341400900b0071040c42010007500c400159119084a0001241300c06440001c142c3d10030b10090050241c1000074080c25424190b0042040310300c0c04000c5840d0031401410f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 117002724 1250 117001474 117001481
    0x905060f031302010e030708070f0501030c0504060305130206070f020415050102330f07030c09050d1401060305100204080f06040201020604021e090a0c110f19050703020402030a0b0102060109 84
    0x3011140100a0020a02c1c8010205203001003030320504000e41c1800402d00402d21380441c60340124161b07032061070100001049a010500900320070b20303051002c541070300009000303445140324540c2019501d400143c07481641c030840081695006000c59655030460805500340005828140d1003a0714248846601910180c150000c445068029042c2c0b1510481180301d030920070500e20f03098500c104c01e482c102e200f4044400c2c0c41002460100d03e001d00780700788010222407800300340300e0038054085030500c49592100c400580c3c4591024109a000003603d102c24050590b0303902c01010340c0f0501d443d442c0c03800020f8000d00141d518542c111041075400c522525620350040d0360203030140c0c0106002c10050f0409800c2890b411900502c03800b8010300c04404140540c901311070032087c1c10340d40d031600ca000b150701c4542c0700c130081012002080c0203851045800d84407480f801c00b6103074111800c0e80c120f04001d030038000000215001002103442e850290120380c040c091428401d801801240c00100d00030300e00740b2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 117003974 1250 117002724 117002737
    0x3080d0c020f0c210601080703050f0a02030c09040807060c020715210e070b0f0702101d011d030303040614010b0a05070b06060d021918060206150f1c03090506 70
    0x2001080b145035001c00b0301c21138259400b6002c080c5044d04031899860401081158020b001003001481c0c040d14504059060610011411a07142c100c1034a000140c2d40c0042c001c0c0c41c1d24400c071840d140d03a440724500324a05100740706000701030905000806507019000f1488104580150f40054609608020121102d10a84118001425070720300f403010085070741e5210100075010602291000d64032608030455980149420301034200380020400114100380d40348814040c0350341000d40d0302280d504006030100b1501480c250402040203c031510340d440010040c01040809010340e0703641d04040c00c01802500e5031442d08145440d03084000101001070008503031a00789680c0e0340138180303440c554440781840c1c4044c3c50707142d0009060104644d48001031004004282004040da40c1f00d2118040141c100e64607059030106800d28440c0410910790003041c141e40c0310405540f40a0a030f204a80000e40c909090300c4030304c5d0400b0250500940d01c4400244a8074a64001d45400484960751401c0260520800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 117005224 1250 117003974 117004003
    0x80402010246050a050a1a060904031119050604050f0d021b030106030b070503060f04020f0f0d110f04030308060a051003050415020c070311190302091b0403080d0c02 73
    0x35110080c01d280c02c1e40364019444114040c00c1c030a2500703a03c0343c900d4a40000c90640d00b641204100310b042091800c050003c11451740e2070700301c0c00d01d4214000f03200e03031030010700103010710a07401c840c0741c80d044040c0000c040f0548640010603200304503080071030342c4003011201124544111000c00d900248000303240541d00107180d0040c003526004100052a05c0c0340000c0c174503010741d220301c0d0100c0080d44820380c0e40d104100075a203680d10b920341602048000609203204078001d91040000d800c8060300d12084404c207000c001c500990b950103034907a41000305801503000010181c0410102e80030810360380104100c80c0a551071155944880c010410103690741d1042603802420b0825613201280a50000c0d87d125002e041481e040440d45d4003080140d0f0b0200c80c2d0042207070803005d070500c00c0203901a40144d080c0e0007038500a81181300c4500a0840318481e0101034840c01c01903000500c0810180b400450604c410100c407034aa03aa203181002e80d640122801e080301c9170a0120811489100091800074007159 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 117006474 1250 117005224 117005293
    0xc0d110118030f09030614060415030201020304120f060509030a110609061306021306020705040e03040e13080d1b0e030f10020a0507020a0f1a03040507062a030804020102 75
    0x1d550242d41c00034103035046009106018000002103200b500c10b0b9142c0d041512a16403540c03404004000031100000f034814400b190020701440940da0000589050320b0700703100c1c0040103801c942841182240011001427030036003820f007003117103011010000d003040302059203c0402c005103421000d6201c1804a03102d100c40c0e403025001880a071401d01d14001c8060290744010b10b40840192800b081e8a000d07005900940d10143d01081242881d1140610070540d031405141010300b8a003c9400003c805008030b92215001d26100c0c040c031075002c00315548803140103001c02103000100c40e08032840481c1c00c01c100c00b2034070700920102e950a010504d0000540e440001e8602c00800311088802500489002e404104052051701c00588450004101034219076461100c00d91030701650a440c1401d0a0001c40d11803810300508c000500000b6402064802d00d04001f02c0c41d00c2c0c1d02c00c3c3c12498a952400c1040b00c0c0c00818014400d154100c4c0700103001e24000c0c4e00b5036400307131300d54030b610f101c4045900c2242140510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 117007724 1250 117006474 117006521
    0x5040b060f0f07031e0216090e030304020d0503090d060603060c0801060507020909012309010f020403030c030302090303070b04061b0206151507050d08250507110d0501020c0d1101 79
    0x145040241601442805d0005241080c1500c60808001c482d44142c056440824944104140d042103240103001410052201c802030701a02a224040940028091448080144200103060007500c02001c809442c03901545003508025000e040c10344800d0720351070b2500108540303451180a10310705880094980030300d0a9801d9003807040000c8003c04174041950f1b202440e60300c413101307160b200900b022083d022011500301a09400e003110380c5500801d42042c0b040108100003908682c0c030348100b42d014140180ca0340d03602000700e030451068034002414085284200010020244d00014000720340c40c0600ca0102c96100c803e0f03030b0b1000c0a60302080380140311540001a86005005003e010140000381d505000140d5079640c5010340f40102503000c02d0442c810004c0c40d66200d48103490a20f400c18440088400481000d4082d10030864080c012700103000f801e9a0329200e19101c08181a400002195180c0c0610001034035140106010700015801022482e4850014080e8003118002c20050034230159 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 117008974 1250 117007724 117007747
    0x402010e09091e0a05010506030c0f060c070f03080c010c0f05030112030507020d050d02240106030b0d020307030804180b0a0608091213050120100c0c050307050705040b060f 76
    0x500c0203018580d10300c120074000c08181c10f20441906404944070041c2120301e0300d498214291440184424000d90001c017081d03510b965050300b20584510f060390080e503a124604403039424500035412440744030000303010001c20411060028009801c402c4020000010700c02e5045440180030b0f00d5190015200380010300440a52010000d80c5500c13034105103152000039401304514080c150b40c1070350035401c900441c102940e01031002d401200f07400c0466510811a040700201000d03c107000342d108041d5103490344201d944901910300030381038006048071142039503403400182d00c0c0d000d4001c00303030144541d41e91000b141074507000e12104160000c0c681030209040075030440e009400107105010070300c108a0850401001c5000401640d01d803424042001800c0c1300001d072441c02c807500b001c08050b0014550307810302c41c00440e5800c071148a600c4003041212425100325030210800d04050124013000500700304101d00010f8680c100c5000ba6001c0c046407000030104403407800340d5240603c0b8018200100d12081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 117010224 1250 117008974 117008989
    0x9032713020d06230306010602060c070f0303060b07140d030903020c040218061206030106050607050607080711071e120b130201090f0305030702090c0309070501050d091b090c02060402010e 83
    0xc2d10074040005440d580d0b10b0100c1d45421003a030610588440548044585080501c16140903001c280024151810b000822a603c1c2c8610040940100f8810000b00f0805120b50000c400503c1d80c041130340c5d2200c4050138044400524800c64005034440c12852000d102c0c080d014001c662030b09500500704451102c01440003a40c8145628884c01504619100c140d6580502400b810f0341d00d6900c0c9512850050281400c41e62950030032403082c4400d100d2507000800020300b4945c00682c920384110075481d030b4001a1104501603a1050342c5028440c0c0101d500200daa44000a2012a2010122895541a10a00c6250130700c2028040b400c00c00d0015018400d1440500c8030755106240003207a150341c615005142d0b020a400845240d04005040d5040d0328101510f140c105411220346c5140d810034010712503403648240700e00b505110f4046203641c00c600980c0c4c04403e002d80c2206a0041c148070011055400009500540c91140e1604030b040013214800105a03114079410b8603007104441c0e4800c20400030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 117011474 1250 117010224 117010237
    0xa0807080d02071a0109021201030807020a05040c020a1704080a0803101806080c0103050f150616030c03020706110c0105030a0e010905011508060606071b0e0903271302 74
    0xc0316801c012107000c0101c184010300900d401041d083c01007a51180710440c22100607407024072407a00500400891800c203070041d5044135400252903a0319180c2e48046a2840802d500050b072103803400c0c0c44001c0303841d0082220440f5038030030503008500c041a54a410f2150207103000c0da90b1607500401007100056400c40085130407003402d00c2401c242e80d980314401000707a40082203040c0d13696181c1200300071441040004014840007407e061040385001d609801042c2c10007000082003211210845002d5140d1303008840d01c1c080c0402d4410b01ca49080e040141c028041000120014440d035100058403c3c4100302c40100b000184020700034075800c0c81c004492507080540340888280d50340d01054852a000d00c030312800d4902c00c40000c69403012440c0d0940514a0340e90002c45180c000c8420800c1c1c654800b0116200d842c2c3c442d00b8440c02d4400d105102403102665000100c450300c0712070070300c40d96541c0000584610351311901c2010702c813031303960066803070304030030ba80c015504011646a0941084156000f4204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 117012724 1250 117011474 117011483
    0x90e180a0c06031d031c2d0507020d050c0d0309080c06161206050d060c0e0603010807030b160219171209190203121806030c09010306050906030a0807 66
    0x420220030344410460721810352250000c40d94450440c03039100607500d4018440c0c20000065424891401d962441441490402d818260b90f1134035019015040c00319042442c1c0b6001789841490500103481800a0000351203500245c8140107006400c50720810407141d20141a201411031601408004e502074000a20200ca49000c01d118000c1b40003420000c0358815124040307d00142c2d4903101010b403106505141340c00d80103007441401d024980700d480307a54240d00d80c0101c000611080c200400c03520200c5401d04030394003200000000914040c0002c004042e030780034114012040d04ca0506001400010031980c20140e00528044143c0032015001c1490050180c0b680c40740d40c5030104002030090740304240c40c40d80c0112040510417000ca08109a0030310705c03031419030400325208540009a942010340c0f142d4000841c000303005a2070040329100d01207004070145c00507460341080e23030710700e44150443d802a07800070b85002c1000509241603d8064040d4101170b0207040301601d1a1101000c90340701c10700540307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 117013974 1250 117012724 117012733
    0x5040f0b090304051012060b0406020a08030a091b0e0a02090a0608041505011215020a0503061306050603010b030430030908070b0103030801030c0603020a0e061b1006090c090e18 78
    0xa068442c4100d500b00c4800c181d0f64451b0f51000d90682404441c81a04915100c0c00c00b40804d10080f0303000100c101d641da4209003419202e07611400420081d02d1100c400602c0d000061141008204000810400355030600d0b07030000c0307203582e90914441280101c00019030300c80742e0035508100850041e0443c5801c01d00441c3e085c0c00d04030940c0d1482040d60400e0380481501c00341c0d41085418821b5041401042e0101044c00b540f819030081d400038200e00000d40303001c0c46072585503123070f4042c04040d03802803006080c040c0486440c0c0d80d40e10302c1214140c0040f541030700c00200382c804035500c1c11949a80340d29222a00301907180740454660313044000b40030362802140c810341d0030490b2a012622040c605030007140f02c2d41d9415515810351400d601d0a02041d8032150030315005110a680350740c5c0144020041c3d03d4256030540e1a40030040d5028101200204c0c001e0990040c880b101001c1141c54100c0d03420b0b40d0380c1070028004020080d404941d5032000e4455106801800c01c0411500300c20940c001c00c00741a06070454 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 117015224 1250 117013974 117013979
    0xc031103120108060114010e0a05040c18080705120102120c0a0e030a0602030403030b1c02010c150f200a02120702040b060a0e100f0816050c03131805040f0b090304 72
    0x1000038000307802c035944560004004101d4040030a1b110214800c0c28039110b136604401c103007c07900c0703d0f000f40110f512494803009230b0007940d4854110426a80400342e80c141083d6501c030086510b0304000d000300c5009031481d01401e0320360007050084550109041901020725541c550407162a5080068007030f0800c41003101200450f503040000100040c01050700503078034102482c0207070840d0442d000140c080d8203000c0310590026807600c84298003940a01f04002050664909400309400b410300e180e62080c43c050a0480401c6c1e5030344035450190b018601115007854890001504e0b010b28034840c0c1c0146d11200b02c01040c0703e010b8024000007071018001007240550080040c5040d0000068030300010700c00351294005140012050348003d005003014400551b09281c0101148001040f01c0e00204503d600c00d04494811400c545040ca89003003501d40303071460341b010305480c0c100344c0c81098100e1100d806034014600d554802c803401958048803000610289540b62403082e44000e04036030070742c001403000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 117016474 1250 117015224 117015247
    0xa0b041b12060b03120c1c030b0604091802040e0a030207230f060c010c120f110702100207050a0b09040f0204080307200913021206060112090606030f0605090d0c030c031103 76
    0x43d2004003ca180507140c0c2440141d0702520301541c8000090405049c15a00d0790305445100c100d4003510344a1102180c05466800b20320440d8076030040094104c3e15140a80c009441c000c154003001c10312030340c2a11026655610101a507204c90410f00d1104007004180300c05074070384017150301c520b03c00181c1540c4c101940d81c99402d00b141d03240e22101000c00c40324154a0480b5030244642100360030640400c108101051018150900404800a00400c0035146509076203008008000042500512900409485045094683c1c012015040c090360a103200c02c1d032290118026241601c0343e21008500307086182d201c4003480040210041c40c1103094031a005000c3e200c400d0312070b01c911111850625148401d1051201d588541052588103410907424030800340e900c100c110080c0312000d00c02140036503041c01d080000f0821607000034042d110301d404903000c01260b82c000c01c1c4289100b1094498505500a05440d100d80202e0010001188135042c2d900082c01000040c2c0b01010345012282081c0c0120314 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 117017724 1250 117016474 117016477
    0x1b0f030b190e070207090c0206011a07020a090b040b040504050a020d0c08060702071d06030a02130617010509160f0b0f0d0e010e0c03030405090f0a0e0a0b041b12060b0312 75
    0x81d0b002d110800104103a098041142500818060400b0044034404a100039242c2e40c1c18000d240d0b0120303098105120300b107090826a00c4498000b0a51b2071511f940c2c5200c4001080d20311078a6002c0c40c1401824101132405114a80c411031f0000d024041402d03141c0e00300400420b00120880d12428070b440c0100c0c2c3c0c81820003a5034800c4c0321940046c981c1c542010700054486508106551440086c50200040d0b43c0b40480c060541ca5415140c11100d449400002000b6120030307005400148080746c0d5180c0e840005400041c000d4402805031405032000e07801c1c0c0c03203210100d40214801004a00c5040029850003001412400400305e401400c00800140c44800e40d042800b161410360b450340b550f15180e01040c46100d0340700104400a61030039181c50041000d2620041488a14100b400b00140080101d030300200020304200041e110103000c0c0740b500409c000c000362000e03900c0740c0c0e48811080090a004801c0c40035550702d041c207080c02c20703007940d618006804095102c1340c06d80034180303007000c0d1920b1400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 117018974 1250 117017724 117017729
    0x60103030905090604111b01020c010213030c0503030a08010b070609020909030a1413030219090c0512060123090d0b07021014040c3b0601031b0f030b19 67
    0x81d01c14900d10316050810290280c060403c40c40340c0e01d8161110f220740c1c003400880b060504602c3c404804e0f1801541c107907009020b0015054815400001c002c204101310255001c180c1e481080f0b2198201e441740c0c140341e80d038000e19403060302094074030005100d4454544080c20f6118402c0501098141d000d0307012481041c826581e641d060740c0f012900b8661319400c0726660141015200109050202d10031b01601c2890f020b11029001d9450400c84c038901050a00500c0c003d41400b240612140307144100042c4580c2c03000407200450040b40c40031a40c25032003150320140c598081d00e000d4030301c0c038520a07030040340d03501076407440d58030000c0480104000b90895406600c00c45858021744900304084000303409031070b54a210024030074100e004000005104840031015943d43d030540320084080f00c550641e5000345a0b51401d00722034040301500346040c09001a5100d014207aa0a1240320100c0080c00c140544070107280003c03da51007604040a4800e5000424120008000e8908c0c80c0185200c21b0405a040c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 117020224 1250 117018974 117018977
    0x20903120406110a111003020f04260a050d140909240102010e0703060c09080610030213140f10120813050102150f13050d0206011404021c0e0a0506010303 68
    0x2003010042d054100d40011224241d840203411038580035901d4420702e2225030b619905c42c0c2e170045a0540d0b4584264103507452185841c08142c2c0c0d50740c5841c2030045400b00e842d4206109407004109030030341140818423004c1c0c0e55010f801042442c160f80000d5400300c1040d40442e20120301800f41c101d05585014203039003c0c4a01070118140c0c860282d8165021007000304a040c1135a05160828100d803c000803441c0c2140e81088001801ca045c0d03a104035070092440e031060311148100f81c103204401101d601c07090f0071a88200d60034100c1d00000f00300d44084d00d0189000c00c042c09000c0c2d0008900b000210001035000051710350b40f010b141e80b2011110451030604c941510340050205216001d4101d018228001c5c101c240024210741c00300070f178101050000280342d1005c40c1d0f6040e021400700d28410400038050b40d0b00c0810785880c5003207a00c00a580311070034071034011519000c0104070a9400d04e0710032a0a0041006014418030442011620140c0040c4018090303074850303201e589010600c02d20446d40078521a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 117021474 1250 117020224 117020227
    0x70807291602040b0d030e10051b0c1f020c010e130204030305040305070b041203030906061701150609080c09060a030204140405060105041515090806070306080708030403020306070c0602090312 85
    0x1401031100b00c44d200c10840d0301581048050b000441d400c45440f04414030103c1d6169110609000d00311860b0280c00000c002d4902c0c020303081401d149020820f140c55032015910000c0c000d00c1782e2524180e003180118400e0143e0050a20043d15500c14a403607562a03101402c03035401c400007461210201c1e4001c0c1d1040c0c0000344040782c14010084c003401004010140702003800e05107401d0030350700c0c41d400e00f002400070706055a42e00b242041158980000c4020304550307400e050301101c0703034100d140a4072005440550f441111000031642d0b6020707100802c2603c41c00c000030300260841d4000c0c040400c130090502684855201e10000050fa194041c04400d10404126100706090600d0032901e02031040c2c019a02c05c2d4100a01500964941d80d1500d0480317444801c021200c40d02d0070301c02d88400e5000c0d04003d031180990000c00000a415030030000440320488100d49020343d0300c00b1540d459001c0d0340802503145d0020740c00700380d08a105001000c41c1c54041c000c01840c0060210009150400410b0313204a0340700f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 117022724 1250 117021474 117021517
    0x307090f050d0305220503060a0b01110607210e0a0804050a0609031502030717070905010207080a0b0c0f04080703060b100c050a02090702160e150307080729 69
    0x90020030000402003038918a08541555402600500500f6a0948448400d030840d0002510f00070b144001000c01405071a030340d080004020018205139101039010a00079406140c4500e000a40c0a01c41c14166440c00d4220820b4041d107000c08010408006801e6200c0103020301d000000d102c2d410003140300d0110b06a031586040c1c180300c112030943c0d10a20900c00d98107010400714455510100e03021130b988800603503903070341c4803410344900700140b0015036203d2903030f030070400455000f41c0e040c0140c480076001c07100025628034495540d00d0680c0c038000c1004110300c0c080b07201050403001403c01da203c003030304140c05e254070340c9001498500b49900a480c141d454002030f404c01d0501c03400983c0c900500d03141042101c0c0440d142c0c0e9aa500f8036050017406421000d00140c5014802d0001d0351003800c8801e0354400651b5155440101110140e8841c40c1c1c40c2c440000c03043c400d1070002403480443c0d012401408406142808001016000c82849243c4146040c0d0291202407420700801c1c1100c2015030b004003900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117023974 1250 117022724 117022739
    0x4150303180605040605130e10030204050c09150a0c05030309060712050402011d0103150b030411010c030c1101051204031806020c030307060b04020d09032601050d030f0c08030709 79
    0x245081585100a104007024811668444101c03810b8a04a00b1b1242e075903084004880550701541c0c0c4010030918810051000148040764242c0880b4022101800140c40d00c02c1121118416003a502e0341c440c08082c3d208402941c524003810604038641840307034013220191109400c60784121203100694200000b000016070304a120000b4526691408006620f065400a0201400c0d810f0740410420004100c1603035030302c00c3c0c0004e02007a21244480100b10b03611800c0d10425001550100d42c40010b01940340700c20751284246400558040d0784104505901d07031a041c03910803004c00c0745410480e00304280d540c43c0c450310500c540210300c65038030500b24032000c5907505006c2075541c018400b107402480650308560740c0041078a44090b003001c000112072040f0170024000b4810007500c401b0031820992140249034010b41000544110b600710b240e01640c0304198401d16010034000c880d400450695601c01103032003001d00359094040c0e403e045005c0340b525158082c1541003110500000b8005400520845 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 117025224 1250 117023974 117023987
    0x804090f501611010b010804030c0c18020a090801090b012105060c030f0912030c0f160501020309100204030f060c0509130509150405060609060d0803040303090303110c060114060904150303 83
    0x6440d800200080d05d500b600080c07150703401400c00703030410440300d14070420320650040a07402002c80120f000d0f0741d20002d8042d14043d4010308207000200d00e242000184050042c060003580c0340e840140140240c0c05d0400e18206982e01040e0400045040d101d4500028000c2100300c0c05448015403954880c07914400525510310010700139841508844007182410182c901501c0e00400b0111b005601c9900c0443c84440b14000c1341904041642c45080c040b081c414103600a6000f542031400f90307a522440076515509920403440010009500e000c441c1e400300f041c03544281c0101081d032504618000044001540110052140110b019941d405108505008009180041207184001c6101745440d86070039480c1c042c020201800380800500190781c0f591889405008681d0295a090b26404d142c10024010700110790124046440c0c5058402c0103060501599000c002c09802000c0301c0e03081c85030390180c40014442c2c058120340103018030309240d5160b0140070401002e0241e1401c01c2459801e004114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 117026474 1250 117025224 117025247
    0xa050c150103230d120203181509010c1b0b060a0902030f0f0603010c091e1208040e01240c030e0d06050402030c04020307080c090a030804090f5016 65
    0x9a8800f905000c4060340185042001d400103807801038923580c680041400301000c90380990650701984e813000c104c2621040d00e090060515000030041c0c850300580c10759590040c15215269882c08007079400c0003507081000d40c0e602c5000a0320312421643e4840e105000d80e0000c1c1c40034000b401151040090b02c50000c00001c1c2c3c0704030110000d1140703002054002c0c1c09a442c81c0210507156801c0e0031082280b011001051004054000c01c4042c0b402440c10070410030741250068242c0a822603000090300d21106021003102031509072010740c5094400d80684291024403400c602b4030480c92400f2450341d0710002040301c2c440c0141000b00d41c61602d44101810b01034500480c920803881071050003001a848030040b50b004028900305680c0b00000703400520020910780c401800002d0019011503004500e4000700e0070031030504018411f1f00150960004002c100c0028a80504a40303040b07003481109542081c1d0841190032a000c000303520f07843c400310750104200c0c0c800d47d4814201d8100792546501210b403848 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 117027724 1250 117026474 117026543
    0x20a0b090c0a030b060402040308030705040f0626070c0606060e09130b0c0c0c0d0f0b070c050c10030b09010e010303170103080910050c1e1e030a050c150103 69
    0x840303031201e41c0028203007005070101a04070111400000e12a440e00d42c1120081c5400000094881ca008240101103a005014109404082d07070030000e40d260241d0703140c10032060100b003922500c3e10241c014010103000100b00c8000c0144000c10074002c0781141c42008050002a618860780c10410411b011510101802d40d106201d5214100d00208030f51784441900301c03040043c6190382d8000c502d04549008640100603503c550840e10320703800c02007140c40403070034503120b0311810348580c2e01c40034143c8080084c420040d003e40c21000c840b0019142c100300700d03603401000d41000a5944040000300d030f45400e0981042030180652401403040c10b4010f00c0781c85020710030080c165240d60540e59000c03600d00030444001d0060040d910751f2040c8038050002c2e120341600090840e20030380c00710344041100954100e4504102d008a0911801c0154105100319812011724021071601002c58800c40d00f9a01028907001c00d80a41c0c8030114590140d088414000c50040c100c1c03414214070813210005112a4400488 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 117028974 1250 117027724 117027733
    0x20f041508010e1e03190203040e0c190302120105040e07030b01080c01080c04030309090c0306080a06050f09070806010314030408070f050a0f0302032d01091a0a0902010507080304060615020a0b09 86
    0x202c01340042101c10351241c04210050324010303804103034550301440d0071203a03402c00c0a0082001c05645940a001681c0b401c2c00418100c10b9182000e40407031140b501d0315041e031011400144024106500700d006184003102c12511045d0b541c1c1c40d884503003c001e800910300c40c2c1210f4160420f03581d0203c0c646420000f000f400754034040c0355a4001e440740d28544111520161600748440d1401d0281d0f0050006000503000d0b212599190b00c0d2100003010200d9200d0084070a00000c15601d400000350070050710701820040203280d0950b01d036001c41102d214000b03d0700744070420020420310400d03c41e040080900030b040b20155400c0c0710801020350b206800a6184044644080015030b400041c0010040007202c0400d520400c49104480d011801c00d144008075030901810400300041d01035140308510108a010038142c407034616407001e039850041d010740082c00034003289000c00c81c01030045400612640d0002209641d070040036840f0000341140300c0c0543c10159610b801d00482c0200b403580003d2b0030b030161 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 117030224 1250 117028974 117029023
    0xa02010b0f0f0d03080c19050d0609151208070c06090e0106030c1b030306030c060f0305010519170709050f060414091e0309040213080f0604030507020f041508010e 72
    0xf41c000818808050200104603021520b940e082c041140c409840c107508114040104204c003134016800500303c2085207160035000160585148100710398030000300c0030401041e2407c2e035602680d0001190513680b94408021b8500050041c21440b801044d203a05d4111086203015064003e00c541640411305060900001320200e40d884100c031003801c6402841032100c0c641504040b80101400d42000784481c5103401c01003222904101c400150140356641407209030380310310078030007061040c030f4a0600096070b010b000e1294032100c107101a01d241d80101101c1036a59038040c0d0109513001501d900142d045000c0c18010345003040d006604090178030701803044444c01c0801c0084e03070301c40860f441d00c80060740904054000d41c1041c011500d842d04021700a64480146911081080c1041e20171040c16114810340050303014404201c840c03003281c064607164180b0b0480e030240a6012080d0b0b17003035079106a650040c4045141b55907145002b07410340e00d0001943d0070000ea24030f0f2800240184401d0040c02c1e94280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 117031474 1250 117030224 117030229
    0x314090606101704020d112206060c050a1e050102120103020f0301090314030c04080312070f09080307020108040f0b090607031d0322051f020114010e1311060a02010b0f0f 75
    0x3d0740156045d15440711049041c1010000d002e411b503421039000d11480c049250b02101e620420078034407400700040000560340c24060700c2d42ca519140050080e00020421004504030102103180e040c0c0f446050041c480080d03a80508a0707200403506404800c01400502c1941000c0c4a000a9507070107078001c002015090302c0140c000c091010020158583c00400180f2980302901070354000e0030000c003100e8030380940d820180315a25080316002c000440b41c01c80803e000744280d540008445811001d5440c007055074004444c01c040040c82600c00310220074030940014010000c1c58480c0c4807c002801c1203041c075000040c26280d40902c070384030745540905003140904011049603c00756010000c400454044403280c01561100c0d803107280e000080300c1400a98080f8810095411000b035402084202d40040308204040020b010303a96041d059840020104603940034551900c5003d051605402080f076070006030941d00540e424030050351a03a41a90329400c00e00c40b0038410b13220850b109401044030102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 117032724 1250 117031474 117031517
    0x8010f0315090203031b01050603060601020a0b0a0b1c052505030706050702040605040608071703160210140a030902120114060105030a0b030303010e1e0c0f0a031409060610 76
    0x104880c49503030301c9140b80119a0108220303204440203490034204a03050380303403d40c000c09089a5003402401140c0000c1c41c550310120fa40c0f48c41c0c942c041c40b00000380e1109080e5074000c00c2c3d410034141d000f1055840550710400825500c2d5881840b40c4000c081401d4406500003a03002c007800402e120400c840d0042c4250b507000309941d07084e14510b161003600c4004c0d0b0b000060184c0b0181c1c0c056070300185404000314480d0b001207031090a459980c24002c1c800d2101d042c41a40d2842281d2401d2141c0c12400c00440040c6081d80e00d88aa00605241605490803e0520008a944002682ca0100b6a210000ca0071414491024406041031100070413810707004502501c503509000300224108840000010720482c0340c1d0740720000301c90000e01120f80380d607100d243c5c02200342c60603541b0b20104140d880e0b00c0751010325500309251040882c081c3e014101072142c103440000f80c01400700c0c00103064441d400b2002c940001d000fa648035000c404020505030901000b80020090950580400c115a900701110b41c03003508003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 117033974 1250 117032724 117032753
    0xb01020a031b061e02120c0301051e0105191107060311030f060a030b07030504020a12020d02101b0c060e15190e10030e0601120c03120e120d08010f03 66
    0x41502040941d9440c0050007002101c45504613000100440c5100d18010b074060100d04030301040154481c0ca500c04a151580024400d0982c01448001c11214103e92440718990044c018107040b070030403030201c80e40c01000600c0c0f09454002840c1000c03e46c0100b40401800340180f05c0c40c10100091042c00000c540c403844010b024821000b500b50214a03691038401c101401075820810150300d074241a4402000340034250b030168403920f03050902003114002184118a000d500420045989641e513080c886040d80364030b084824086054221a5180024503422035464032840040d03c1d01d81c18010050240814858214081c0c85001c240b150f50b03c1c030410807035140307101086601c40c046c40a154100d880c03103021042d06804c5080b040181040e030340c06030040b44441c4104400d40304035a1322202c61074034550140c03102030041c0c1d0100500b0004920700300002088007101e407412881d21040d420110750018040c0c3c903124007a5006078512101a13030302040840c09008000c1a070343c0500d155071603c040500f00075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 117035224 1250 117033974 117034007
    0xc08040e1b13090501152705030a0b041205090604030f0f12081608150103020d09080f0d06080c010f0302090301060e09010204050a09090b071103070602040b0301090b01020a03 77
    0x1000424a610012200000252010710a181d038681c08840e4841c0c41c9110b07481458040384c2090004074450071851544420444166950762080034203100500c45d4880c41c1c00c801044206010010526440521420710b02038040c209101244c02d15150400d029810f016401e0304101d001c1c400805140c0d40d09041314110b1750464107189540140d810700380441000007070001d0200715814804551031360001510b03489900b42d249403c00e00035105a041d140d600c01100c80da1a2644000807440c6c00350b00a82c0030700380703a1114420004401c0d4090b80c0d081015800f1920300d500a4601258820030560280113100c05006401c010306442c4400b000080c0c84c9410b144540c406054021030030844a0b1001d60040e0024000e040d040f00c403d00700000c55030300071b40c0300e8000d15010703501c513074000704414241d0301405003900c0c0e000c0b1603419541d440300b60031038100c582c003011032209000800c120000300d8a9400907202030400840d180d5540d52611382c1003011507070102c07001c605542015400da0042a00240e01e40b254200c072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 117036474 1250 117035224 117035249
    0x6010e04080a0203130609030212010b0a052e1106130c0e0705090409230309060403060207170304030f0801170a06020d0609020c0a1a01240509060a03050411010c0804 73
    0xd02043e4218080c80405080700809038a0000d8a268004040821207009840040c5405240c114990990f0002c034a01500092041410402c50130000e10213203ea0420058072415091040c003454607000d030045044000408050980c820b01005000f165040004840b0850208602da61074a8600046221b0100710200540000d103660340a4021200007c17402081040440301034074003455000001c14007140c15840684000c40c6520000045138401c0e10014400d505007446d42d13032448040d44c0300b2079089804580c00182c4010303c48612004d580220f03c40c3d160880d42c40c1c05d034000140110b405074404c80e900c0040d07158915000b2004100c548035181c008001690390003020340103030060481544800d15062001a0417030314403030f0100d0242034581c400e4110866600d042e4504825546003801980700191400c10324141c02c01107940e02d0b02512459080440c14058a500010100d821003140c800119403201c0802c41001100801c1c05203810b42420003140848403900c800e000b0f40118090000c84484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 117037724 1250 117036474 117036487
    0x3030108101802031915020a09090b060903030a0306050f090411011d060d0204090b0108060303040b03130804030b060909011b0318020301060b1801031109060d0b0312120906010e0408 80
    0x3038615503042d89903009011100710640356944514401c810420642d20000e40003514001103105008a60000141c2d54640b5040703810000c111004080300404264002020411061152414009130030084150b480002d01d10b4039003000d0010722403c8101c41885180680c04000015005070301459040c182031074010b9482c074054041c2000c1060305140203510100c0031814110340c0b441900140255440054140004002c0400640348000700b03a4420750b0580040c80244000e281e540091030f030060640030300800c3c80059841d8107a8691107038000381c40d51011241000800e04080080036040148040200300e00851000c110021080340001e59081603210720842c0c0c1e68824848202e440d4a400030020862070f40e940100205661005e1107070308080b41803090801d12580a0f09c59050341d0400d46100e580ba1501c841c1c10007029601c06200110700903a1040d4042d1552001c010012800d141c040c0141d58590305a0702903681d00320001c10400035503000030014440c0b01c6d030b0b00c00c1d601d80050b400b05c4800e8a031403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 117038974 1250 117037724 117037751
    0xc050403260f09220f0f0c020a140102040f09020c0d0e0609060903120313050d08010b0403231614120d0503040312020c0604020f010c17030a09020409060c030506030303010810 77
    0x4c04d5600c202e00038a0100b440da0301c0105600244265550400c104280540120194240c907a0300f200e85e000340c3c0146d50034201280f110100340c0e0349039044400046c40e040d03c0e07021008419103076801480c00c0030707404201d800a201c0c0c01c000c1c40030786414a00b40f22089007000d0000594600c0342e440c1003030041001140c1122541c50801404180500b0795101c0ca84030f05e48074131014500c1008103425130321032045482c6030310018020003000341070700d2103030812510f0a030440d103403454018400240100c03543d42c00e580e1030303040344818848400c48000e26110081c100e85444c00307007960a2100d01006224903c9400d400c1700700b0400045011a418003418007076100c5d0350b181015200000e0308000380301142c0c00080d44036407041c004200d42e0b00c40c41c03013180c0c420076010800e00111528001040300400120082c2403411003001e4201c055544010700c1c0c81e0100340ca03119980030601b5194640780480d4896112030803040069090700500b03501c500103030029411907140c1801c059a840300e50700d400d80c00c96980e500344182c88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 117040224 1250 117038974 117038989
    0x10905091b060405060708120f090d030515180109050916051903021504030c0902030408120402060d0606030e100e03070303020706020d060b0705060601030615050c01020d0c050403260f09 82
    0x4110043c1420780381c203401e05290210b23130701c88401c1019440c64100020103d42292520368003400501000300911818060190010328004c6c10594584944541400c4035948500000d01c04204141100040e54034019802d410f482c40500b034052650007030102c2d8020000a1032188007118011208000b18000e00d107d80825140c0325040070f50045214000b01c06140285801402103a10132850100090742c1c4825a404030701047d50020300c0100200714680c020307642085000d411600081034140b03010504041e83e0100d07081d651090010948605090f04a49400c1c08a000503910300c0a080c48080450003841e5160710270f03988000c080c180c0c081003040610509a05498100b41d10550400c001038613034150300c60680200c0c10445a600c038840001d003407944203003d006c0844066004900c4001007400c3c00351a240c000254100066500f80314030381d40da1410b0b0080c6030748000d00b922001d90f11815410011751b041c4481e41c1c0c0308030000d024038002c112402c50700111041a007480c40e0058527a00204c0001e03500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 117041474 1250 117040224 117040229
    0x20607030c120515030a120809010603020906060c010e0607030c090b0901051c020423040c0309050c1003020903100617010219050d1503110103200301060503100807060e09010905091b0604 82
    0x741c800e49240c4010802903000104407c840c43e16088815501c0802a900ba00c031540802500002440040f4640e810004058102d4a481c00000315608406480c00c034600345007110044002070715030040286c9a031300040c0801c05010f40026651400c994000040c20901c00c2510704000d45040050f1640c02ca84680e054402400315413810040c031100c0b5101c00c21440034554081885649001c4c4030b20307a00f600901c250a4001c3e07212010b0500c0030f10810402c06610440048003051540030403968902e41c4d020300c100b031400d2003500400aa03489c20601c03140c04a2520803000d2b065688100f0000a62541c505943c040000030b62034a0750751070316542c0307140029160180519400f004441800700400c10810700700b802c010002e0764200b01401c0c00e8a51240080031340410913071034080810040c008284101c0043d98031450300c0c00b10055a9685040162801031a40c2c405e00000d441034a030090a45480541c0754014070700c4205c24821814174000c120f0b190108003602148000056581c08815210807040d07600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 117042724 1250 117041474 117041479
    0x1060312050307170903190c03020c12150c04030c0608070203090d11061315050f030c091903081c090b061908070e1501030c091206020405061603020607030c120515 72
    0xc5c100400c549540c0d400c428000030303407205528080c50409110750a20801c3c40c0d09079009080c0d03042c51b0030a02c254800000c2240310980500074041601d891110500f03402010038404035556145142007200001034a41c0060042041c0c030000e10920b00c0d400016901100421a2a010300031003d2500d004c1d01780c0314501e02c1c1e030403c0300402c000038004421303903090003194200d0102080d50421180121740901c05c0140241c1424010310109020041d060702410355048060442c02c050504a030b0130320341c88159540203c51400c0b0000340152951020001c50400041c0400c0074040101c0030760303501d03840100091000d8010810a084409145810b450490080050105a840e01038482e550030282c00c604403088618462590b2410721075521905c0b500074405030550300c0c904400e04100101046560403a019909542c00b404003041c00da8501e0020158200c116910481c0102140ba010b07007800fa004140505061910034560300c51038114800e03044c0200c00030300c001810798412082d064030030b80804840b40c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 117043974 1250 117042724 117042767
    0x10306110d111201050303130b1312050a05070b1801050702220b01020609061b030405030403150911090c04120203071a0403050f06061005090301090f0c05040b0301060312050307 78
    0x85000c94000804441d104912543c10a03030b00d45091541c1d074403030061000b200808102003009050300d40c501608040c0c0700b00543c1500c4aa030b4000d40d1004100c02202a00d1a0308600040c0d81003100401400c0c1c010200420700303a04000c04540750340c4d8100313074440c0c8190601c000001c103030382107613240c01105400080c10040031400c00c00e02c20990000f081c41c2054180913100b0b06e000300d4251900021102d11458550703890700c0700c401d044210040640c0014104407054401032201000251030009003103000e000074000003800b200107081c07012400454038007641c010301c0b031036090209151060013100c0c00c0c1c0346480c050100702035092000c203142c10116448030103d24099902c603400c0340b500c0c1004008890040e0100c07902040c24860b8603031076030001d0340c1d11640270041d4034203114854060000b515590302c00500024802c46140c0b510158444907400440b95600700318010700142c80c00b8400d907011810160000c11255041d0340d10800c102c1076417451074081c090080300140215100783c40d1000f01c0074802c00c1c07a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 117045224 1250 117043974 117043991
    0xd0f06080706020106050108040210030c350c0a020a03030209010c060e030c0609030414010e0d0605090a020118030213020304060e0703030c051c02031b0712140d020a0803010306110d 80
    0xc0c1d407908000d02a003401542403c00000e100d40c410f14460703000d190010104400144a00d07410b0740141003003c01e54083c400c80d03504180a0225061019840120800e640a004100800c150580c1d41000380320902a000a11164402c50742c00501c501a25915080046e40d426411005903072518240000811290030001c2071040200e010014041102c3c18204641164541407210b944030301a44c010390558140b0007403034190541c8110000040d54a0140689000c504c1544828007642c204440422940d0700803a000c0e411540d000c100e0340540c20301618015842421a8002405030f040c01c051060f660750080041000c0c00f202747d00c5a154403202d80b0448034929600d14003d004100c852030b01b91100d0003220840070881045142901000c10298013551a1414400341d40081e2068081c40600b20321900c0e4010480000d50412116542c0c0210481910141542142864501001c03000000c64020010000c00140c108040e02d066039880750021802506000c182c114501a980070201251f0505010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 117046474 1250 117045224 117045239
    0x3050c01060f05090c09041b0806010f0306080c01031d0708060a140601080f090f01063b04030f020a050102030705071209030816031704060e100b030d050d0f06 70
    0x6110510045009014103035a514400440b000c2520401c0c1d0000c1c0d034600001c500d10317581c0006141e032160060000480d06500070002601c190001e490f90b02107452101801003039030300288170000d68005840c2c1486074074108a03006480b00e40c5880c125050685070100b6014560403812569114034121044820103a85d40d00400c0e80c410702035030542101031400c888202c041da100310701184218410b03122845d05e42c0310610b1440501c58002c24000c0d0340e004442c0e8258030280203002d170a00602400900110741d1240803044c00000240c103090071020140c2d544004040d07201e1045e1640d2243d054140304045580a26050303042c50440d0f100140316510000412a01d01d80001c040c0c0201030242910170702c0c07010000d00076a150701c001e000241020340141301300706032030001c4e44030300560302d1003882c10161090128040002d03114007a01c003114100c0d114072189840440400c01c4189400d20304c04140070306d1840b072001c03949410040c000001000070018840c0c01e01e01c02c0e0f030003100320b0045040041142d1070f0358160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 117047724 1250 117046474 117046477
    0xe090d2c0634050c010c1104050c0408010e1c0809070e09060406060b12150d020405040807050105090a0c0501030f020f070309053604050a050a050123041a060301060f030305 76
    0x2d50320200c09603038040c1c101c0d00c040000b020702010350090007400808001c00064a840340703a03540459090904244412981c0c40e50301a150082d0300e4240c2e055102c505081e689404d403081107901840b44e90120b1500040c041d1902a041000c2c101828900d0154560b06889800c10807680c00c101504940e0340140060035800080c1e55201e28002c40702001341c1038690160010911a580058100300c40500c04201d04101070400c40c6081c802c010040440003885a0101c2d0540c0e40465058840d06404507024090200c01c1c0107541d4032405460140059144a0742d03215041043c03409003504141c0d59115926401c6655411910a49a150031564485101d840d000f0440060340c0a01d40c019801e0280e4250440c88034588036035000340762802580905807610032400c1244004100792020701c03e00181740c004c20000c0c002d03d103005c0c0c005c400206080c021246260b00d021080d030840301c41d9620f90404c0101240c0c014502c2c00040c001030381320408540b180f00000b4058544c64001c0743c541d4027043d00c0001007580290 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 117048974 1250 117047724 117047767
    0x90609020319030f050307020c120c1503060a08120d0c0306050a030b0717070c0f15150e0105030303010303201e0a0506060f1c17130e090d2c06 63
    0x10346140504c0350000040380e46010503103444015034041c0700003030003500d8800e022580403280308048611b9981000009a103000c5034012071005a5400414040d460408440a5000d0180385004003002000784004800900c07070407141082c0300d55122911841a07101e500224000c08008260842c2d40b500ca050085441c40140d80e8040400c0740c4540c80700540302c00d290743c64881d004c240c51302041e8003501d49030240303050000c400c111248e00031100854900d1041c1d2160150b001d06000784110000d0410f00c480c044c040043c0c10071031280d4814401080000c0c1d202a80c0c950401d011002e40c10640340104c038003864035444841c02d8901910f8400c3d0318500e90300001b06451058010701c2200c840b51a407000380042c1c08119038031a50040700640b225401d40c080c254810346564400e40e0a840345011110401c00035030002d0034504d8a5441002007001185850200d0a42003c0044094064402a40c2000e001d402000c03020010506610600e800310b0385002070101140300000e01925178641104412807000d1400342c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 117050224 1250 117048974 117048977
    0x120906020607030e190c0902030705090114160206090d211b1203090311030a050409050705090904060b060c030d0605040509060106050f09040e0d0e0102120c030d09060902031903 78
    0x100c00150b505200b8003540c1520100c0f10085d10300300c1c02c0700d0151340402d000c0810650b45201c00301c000142d0b03400c25200440c443d540f05da85490322034102c500014550039034031800c0c2d05485002c0c032141c5510489a41811142941100d01550300c4030780038042500d0030038071032014100744004000c034400408c40f400c085211080302d5562102101c821131100044089040001e0100c201d500030076100c540c082d130b1010002d81d001e4113210000c2400b08240302e142d9030046c1c2107400000c4003c2010003c4034103c0c000d0941143d11400d10070306000100300803c40c0210018005403409485200d0740806845002c201d07880e0340c042c041626541c14403907190034054130032403050718042da00c0c1c500000c1503401d0204616058440300c2d5181c0e0316011010340340710b01c642c0009045a0307125a40ea00060b0040000700403454420072540c423480014419840064200b0122100441c400301042100809805000c0200d82d400343d030503000050704580d541062801850101c0000f5050f1041020300d4590303142c94021142098404d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 117051474 1250 117050224 117050233
    0x2040f06092f030405010204030c0314120a05180a12030e150408030703080618010603140601050c0a02060c03070803090703050106050d02010e0d050c211e071e0312090602 75
    0x101c502912494000040081c00b401c0c101d00d208492034000740119001401a80098281916070312040d0240402d40d00450703071400207401c0e179100484180b2450b40d902d0301c11001941003214880c1c01415a01c03e0494038681501d0607441002d29640d8980200041c00b480b0501412a40315403802038100c1c0255080c81d481440c0c400118150301e07540700120b07070030745031100701075420001e0b40e035425115000d010303103000d6100b440001138100d112166034115000b0b180c950b802003800e19002001080110f0007030329460400c0301c100078901c1d40d010300080c42041640c0c1921800e6a842115500e2030031401004401004194000288444d00400090314020340b40500c0003044450354440c10800b0609001e00c00a020401d400244c907a68a0300012009a050090b4284c600a0006100180c00d00d00310200f400100c1003011700710581c1107010051041c4401c2194417850402c0c2c1381851166552403d48600000172840211912801200c491684004c580c0006c44558045044a000e4203000b0035008a00040c40b9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 117052724 1250 117051474 117051491
    0x606171608070605040b03040c0503010504240515060d150605070201020d08011802070203010b04090507090b06040308031b0d020408011a0913031407050f0a050f070b160201030902040f0609 83
    0x9011414800f00c800a444480c546031600360300340e0481d00b00034002d0b035814050f810005000d0700c0c01e01845128074810717580112070341d250a030000e803103100d0b5044501354a450030f02048080302c0665030015490038221103540c2c5410174180d5010242810382d105e1420603800100c0010400d4200b000703444014070036029a06c0c0c070020000212a400002d10400902d40ea0703003114070b0f50603009035005054884c0042c00100e1005000b00114041e00d08100c01180c0c2c9501522040100400c58800c1c0f40504600305da80c0d0340751038074640702e58190f400090106054040881e070305a020902a1046079468021440700b55110742d0b9aa20740ca0080440c00b00d407201110f0740d05045002440c00442a070300c0745072510701c07907800160755407402c40d0750b400902490000c8550821150380840c60400c00d003a08ea21500d4010304600841d40741c20b5003050448195054a580071200070312100c058003060394400d00030701c0f80c800da0019060004070044c080090020f90414945083c82c0100c1180da001700082c0c0708086400c0c0900d99 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 117053974 1250 117052724 117052739
    0xf0703050105221205040305160801050c09030606040b0d170a021c0507061e020c03091e100e06090d1b0b0f041a07080a27031a0406061716 61
    0x100000c0540302000903180da4200003130043d038101c005840a46002c0f0b0800e81c5a50720305140242c0609241e5030083d61960410003a0310034003d540d0322845202900741403618280119960341805020181703c2e82c2c5400309541242c40c0c41a03415807541d00511a020300a1505641500b1940f00040c0030340140a038a45049000a100940720754072422a84d6080c60040c0729150035008026144064008030450000704003050200d0011744280510f035405581c2c0c072007a043c204040b9480c4503006114040c11610a40300c641d868030b51400855046007821210805c0000c00100180320303900d0887d60003400d11608001f40600b8542035081030342c052a01600385911400d041001380a144528075118030100018050054002001206801351603c81c50501801d550703100c2203a04000a07480c00964200d014403c0318a0300300090002c4484050240b145c2c0e81583c4440706101c0920904c480b000c0e120070301040400586521075002171004203000080f000030600c9581e140c1400c04050800141c0c00040032803e503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 117055224 1250 117053974 117054001
    0x6060201060e010303050d0609020c1e0c011e02120d0507030c020a0209070e060c070e1b0301120f0809030a0b070e0901080c04091515050108010b07030f110703050f0703050105 77
    0xc074115410b214081e8610354007180e032a03102c5901e0000240c0ca0b500c00041000c818000f5044004401c4003412450400f130140e080399038003071802060680c1c40004286c103e80d03005055001e046810b10790002e62000010020707850b212990b502e90380408030000b003121580d01c056100034003603c403941c0d00344042c0c0380342c5404a0380d807030b01003402951001c0c0b80340100350305c0342c02500c418260400182ca0107007040358060025007441015402030b0200c003050420061a8400d403203520800d50b042d040094215414181c48a1040811007030081034000221002030034862032000340d89240400800f1035031890b000b445c01200701d040c26952040030440c00e80c10301519282c0030346c45a050704e03460001011401e0207042000084d102c01c0b0380035107600141003080b1f100401c640c003a40e50002c04118000e4280d600c1c0100041100e10141c1c13007030103028001e011071400130b61f1003441000f00c582c1c5440e04078510303c040704103942025401c1d40010621b12801c1c1d0030b03101c84a004606101100d000d00002c101580d104c9200c2d01c100c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 117056474 1250 117055224 117055229
    0xe060901060c1208070c020a1e06050c100906090b04060b04060501050a0822050304061707050c0619150e04021801050913030507060204091a121e011803080405010606020106 76
    0x49a50703060f11010920700c20b02078258455a6450304081402550b000f040100c403e90700f00348140c641d04200c081078201d00030200da00401c2c2d2480d0407403610102126440d00d40782e0030452403448070384a076541014001c80ea00b008504542102d10340b0000e040034640b80005011a100050155042402c006400d600800545440800c40d0322910141e540309421500203030f14000f14002500040402000890800c0018001902080d2140580c0700c526070720303410034a04018002d0080140c10040d2441c140b8012410a4101c0030700da00c0301c02d99202210b00075024085624030ba0b51001548107000421080c1011020300a50095408600340c4128051100d28104240141a00b20803c18003043e00071140f80200e90032580a854440d05269443d0f403901c05990069000703139001d42c2c55064805050303400d0305040e252010200d88090043c9140600f0307030b031103a5503203a07008484018013080e07520741282908040e402011460410384028072a1030084c0030801e0a48050329250301e00f090118403180148181b07810f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 117057724 1250 117056474 117056483
    0x408010209360901020d290d0f1101021c050901080604060f1215020307030b01111c050d14040c0e0108010c020c090406020d05042a050a210b010e060901060c 69
    0xc0c001410407104001c46006010800150341c200000c008038039042c428015003c80c03045450080b0b0340c002c1000070f14607087c03a100c1032080211351030110014a0120301d8a24450748045950192a41e00340140e040c90940e036000700c0d0000c9903000c83c14030a94060024600c5100980341e40308030ba2642e000344821510b49000709030514036840400e014070031102c1840c069240c4502c0c2c8504a07a6800081c0700240d030011340b02c400101e910b0380200d01440d0b810051a142001c5500c0040000f078400161500701e200d0081131400c144100000e104401f1000c0d82c010690303900e51042c00340748a044c585454841f400c02d601ca800b560900800010680c413406010380e0303148100c1039008143c18100032041190800014008a0390145c1c02c21401e180303030003030b4042c040c4528000c1c8698500c0445400c40c0c5046c0c1070746d0003151541c50609500600c0b441d41c0d0b030f000300016100500d6240ca51880310f91f0105001e01402800500705d00c104200024503040580e00320783c4904000d0b905207802ea661100140c6044080160040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 117058974 1250 117057724 117057799
    0x408040302191701060e18070905090f120a030c050a1205070e0d0302100b03010e0721080d0b0301060b0708071113020a12061e03080c0c060408010209 66
    0x7518115412480c0c60a004400103039803a40c0300c0f0340981c00350200816048594580c1003c1052485114115621150918010300f0111411034010344448050091791030041c0d840d008181a05020800e0000804000d01159040907015000040c1c1e038201038840400a03052000c00401d0611840a8810840c0070361545040b0f9000080d1180281038000c144600300b1603104030541d136541ea40848915090700a0b0064940c0d070748040e0315034060301d90744001d80f0300a80c1400c0520415001c0054a14110741404aa148050342200c958903d40041d5030b801500c216000304410090085641c40308a0b0114114001c008050f92050100c1031350280c80305c0034140050901c0442c02207103507120072203a0108000c24030341c40d030043c0c102d1080481e001003103240009041e280300e1840843c0e140c42040c0c040c00186600c0c2814646406082c030141a903400b008083c0785d0b010580b81c407c205c0800400c407949100a000c1a2559102d880c1203000750401c0f200c1e9446018409141860750100c84902204641c1e07003030244 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 117060224 1250 117058974 117058979
    0x62202030607120902040204152a02010c02040f0524012604060e06090703031202040e011a070611030702060f0603100e07180603020a06020304081902010c050d0305090706030203040804 81
    0x9403401c1100f101112001601c500d006001070760b5a100420141200d1903480c0000c0e074180400801044082d102c214825002e12803841c0c04002d83c0c03046d101c1e050707070910b403201030342e13400f440800c01506c2441d0340ca050017400c15040c42952004402100c808103428517004107688070190046031420b1522031940c049030104088004000b03102e00803a03030b0040c0a0040400e050210394202440c2c4030044880d40e280b030300000c00c14020594071070041c0000e041071000c02c0d820241410b0324202011010f00c01e20060b0035581e10f10850b10744c1d03036105440b00d01b600000d0421050000d008480c00c150303c01c5684400500480c0001184d4503004401140500e41c05030080840d00118060300000b051160300315245441841c1c400039920b07844980c1c64002044098000c1580c6244d44188844c841e01500901d0542d0003c1c0000e108200000583c03403a9221800d0421000e010301c1d00051364444d1003414090410302441d044000d82c5900f5802035030107212070b88100c0d0419551148120b08900068900418511081204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 117061474 1250 117060224 117060227
    0x61f03060b03030c070b0a0e0609130c18030606030b160c2301060b0c0f150a050c0918070906020c131d1b030c011d040903030e030705062202030607 65
    0x11030385101408a03894111135010796860540d0079807180c00c061200051001c0180d0380205107104220341503609a04080c402c00002c0e06031641c0100000d0340581c0c030300e0002a030304e1060072040d00000f00c1c0c4011340041900c0342050000340c03110380402e5596049040210b040040c00e440301160818440da642103a500f86580c0c3e840d2803070f07404c540004003072080440e0100035040a2048000400c00044801c1c5e80d00c040211850401000384500c1e40340f502b01940301d048040740c90040590100541100080310b691f140d00801031401440708154100b01600443c140806034110f800d0700540d4a43c980c0110300e60307603500413a034074020401000d800440e110003c0a4a41c6580c001040c00740c0710b01c00c40c21021100100e11403400b459690100008050b02284030340324102400003400c885028a0000711030131418000f182051030300c918007802555601095802d02d031090f400040301c1030800f07003a01c0d582c5d280d60a0103a503515090343d640041601012490785d81060a03007009a005501402a00c3c041c0d4070000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 117062724 1250 117061474 117061481
    0x1903060b0d1a06030f280e070e0106020312070c03120507030b040b040501050f0d0f020d080a030606030506010504150306030506130b0c09010e060a0c02060a03020307020c010306050a05040b010504050603040b0603061f0306 97
    0x1d080c50094450341c0d0242145620700800480c47d071000d0041c48103600c4c0c400909400030040e4800d00c1550410445039090462100f40241d010360035040c882000c00c400c2c40c00f115900983e0140c00b01841c504000d10180303035410741004a19250440c2e0500003017440d82d0422048070400c0c4695030f030040c400e0308119614207001850007800f6000300501313001078070b407a0080b49070103040c01c100301ea5130800010044016505031241c207003d8040380c5401c00003442c1c00b0002820b0f6106070300a1522003400c0354540004184a60450005035501038140c9540b8100440300c0d105520400c40700300d80307078010040010020090101070340d003d00c0f0140d54400c40180d203142440142c0d80f240a100701004605074500c00540c5903000200306e1002c2c00d9400581e24074064500a080149030030040e4101810620100190350754160650281d0340c0407200003a481a0280040c5c0e00340c41181d03c0390f40c10013400b10403c07050054032190740e44100c1060341614150b503989880d070b0f01e504103511810000e01c00c120f60240081400f070392 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 117063974 1250 117062724 117062761
    0x8060a090f050d0201060e0f090712050a120e01110105060603060d05100c0804150c02101a0a09020403020301060e0c042601020705070503120405061903060b0d1a06030f 74
    0x480c15510902502d50900b05682e6401410150307440d05020018005a01003959010788011283c01c140c2c1000114261211450b11074165407034000d09821050003014003104484a42c040c0c5100100800518054600d2505403140c60105400001c141c1d012403040c0071f86845081c0090446185688507000c2246d44020030900303032460f00c550000b035000303043c00d4402c041c01440d03907481c2c0a03c1d80c501494844c2a1045501c01c10600509080035005415000a2460140300b018a40800e540c03e01a00d0384507a01031039070300e45520a5002d040042c60b040f85500030320035070b402503000384911500d443e00684030010a4481d84492a401c1004100d03001d05950320100c440342c0c43c0c1c8000b044a4100d030a442c02d80c0c104030416200c580100004010307030f14041080c0c01c0c48210204545081910b00400100e607805500000c40c0c825510018201c6403520036441107019002228219413111203e800610007000c03980510701008082030b401024a2801d80107480c03040310000030100301580e40c050040740c042c4154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 117065224 1250 117063974 117063983
    0x10210151a040e07020c0915090a050c090409110a08150106030209040b28060201060612050603071a030a05060307180207020307050a0b090a120206040303110a0c1d1008060a09 77
    0x10b0002081ca02c2d40c0150082c003520550740240140300d4588100a09118083c191060a000f690b040d1100b5072140d510340c0f07a005080b2140040c8994030b140d280c0307120384a50145a81e006180c4603014007080304000e09460704501c10394111000715107502101d6914450310044508520f140001006140e1003900288003590001d800420310f483e640010a91244050388807203204c1400310a06030351310118002d000018000c901c02403200c10310f40800134120207040564501140d0301c0f03e0000724a07840c2044444020b00c05030f6004c118000c4940300b101000d8105032400710205040001080c01d9150014021040e0f8074500201c10400001505040096010f08400ca826010701e903400515a96003020020041c44105c401598441d0a5410071890102c0c80d0040958251800440d04c050307120707081601c050f6541420018018945041850301e04440c080001304400d03003004022417a801070810182071510040726a10440e142c0c19412481d49000b40500c401560105001868201d1603400c6101c655004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 117066474 1250 117065224 117065227
    0x506061002070b030c0403031215060302090301110d091a06030706030905190c08010b1c140a050d0201021201050108060102100506010c02030a0f050c120a0b04080f0a0e010210151a 79
    0x191075840820b5001205d01c4800d04101041c10010715070019420b10100d40c41d00d00c10469a10b49002c0040101080c1c056081010381c0405e400c0e01685095000405c075400020340c031900c1c4d5403c0e040d00e00107080200c5085031004c40070f44440000740301d071120540c0210401070181c078215041000c00c400600d044002034401d841002c0c0300d00300c0c10ba5510000c4200078013034074440700390a040000720342c00c2d0760034854414003411400d50019601800303140c4031070a0f2170b40302106e01e0001002021040c81c0110303043c405404d40c0501604c1ca0003540d0154020443c1180b10061081c450b070b84c132001950012000c83c3c4050150300442e01c00b2200b01e002d1707070001c1da0080e01410104890803280e004a0f15051541a04580e0400d0203607071101030003804c225049081c20100c50480704c01e0898000940c9418049000500032070104c80814200a82041a1102c0e009181400c0c1d80711425084020804030910801d42c0c09409036140c4011214464050b0b07903440b42c02003c1e45010103150a0590542541b03042040b10b04180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 117067724 1250 117066474 117066479
    0x30b0a0b040905220b101403070504020a0311040603020301080105060405011203110115030308090114130b100302040504060f05070f09140a1215290d1a07020a030305090703050606100207 82
    0x3070345080048090300a0500305c11303d01d01486103800600c07003070b00621a0603c501489070000d070740c002000d00550742d041d0b80241c1c40301c9241d041036002c2c0840092000c0c0c002c001150100d0181c3c0c1c1940694100c42c00100240042d440d040309010440e84c080c0505c03500c15601e0292100800d028914003061210684000a4044c00b15140c4408101060704101c1c0000c480701d05220040b1710074005c01c1846070300d1200d41c500c942003200c05030007642108480280301802000c0041c0303050512281040040d60050300c144045e24052a043c8002e044021507000c10074507200c04649000c0c400c944c0055080020784903625005d0400300844000c04004256650120710400e01103005008a45004046d5129078401030500100041007030503101117030400440314054454000340320850702d00ce00003501c0155410810a0345606111661078050040d0810903060ba03400c0c02007090340095420849070203a5403c100780e4440400c0c640e00d0308034901c40a0516800300010071480e140000503c044640d4500440320400d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 117068974 1250 117067724 117067771
    0x513050303070309051606020c241306030c0207061b060f0c080f1308071203020903010e0601060f03050c030703180609230102070b0f130212010b01030b0a0b040905 72
    0x900480320b07040043d448501340c2c0304000041102d4400000010001042541060002542c850b25543c0062094a1403031802e1892400e0107245903180c003031600c55990344da046a5410b180b040592090000091810b42c01e54602d80c80031680070103079907499a0386155211602c07103116214280080c141c43c26566020300701d40c101d03d140b00307080c00d010154a61001c10301d88103c040c031030310300020890100d8030304d01d001c90350010301c0540031a402c4607480040c1e20780380480f0680440003401002103032a015843c02d850103055072070010f0801c2c120703521030359004076410380410100c0560300151b0300380100300703014004103a5041c081d40020404011400544175090081e8844005650700c0070400da03061400c4840382d14100100c00382c48144109050025890801e0315a1500f0501e10003d0004071148624804a0081c401c5025103910203600141010408100c011509009052420f0341d603000c0303464070f8918503c904001c03290340225046c81d60b81e6828903240c600711101800b402080401c1c24040c280d000040d05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 117070224 1250 117068974 117068977
    0x10e0303040f06050601081501080429100803040605040311040b060d020a030501090504030804030819090305030604060807050a090c05070f0f051002130b0c030c0601080f0c010302070c03030305130503 88
    0x2036014056150020b449030034070300202d40d405085541008440001c00907030f181009802040b900003840c04820310b03a140d0420840002c80c03c000d003d42804080c0f8010318403d1070781c0c68680a50b10ba40b0524098550b10040c2036175074030440c8a01408148140410004240544600e611b074001c0608080b54103243c441c0010010340c04181e40480e00d5a0215040300500c0d07141c440c2c05e0140c440c4907410851800c142c3c501401c000001040102080a1a000034000051000888042030500c10042c4900d541500c2d001e0601c0c1c00c2140e03824016481d01d40c0005a00400003048030454038003070540060749042249520141c1002043c038814400200400e02c000703004e8004404985d401049503910710b1889252841c2866090070024003c1801031280c9401030395280140000c481c0744010b4143e8414001445604601600a148190b401600e0002511210203c0c80004070008041035800c2c00813884019012800b507440c0140c0345036518442480003d000c4c2e40465000040940c129403a01c844e642d0b01d40c6103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 117071474 1250 117070224 117070231
    0x150f06020a030905150d150b0c0c0316030f0318051503091e030d0c1106010e06090a050f01050906010e0a060315050f1f0c050607080612061504020a02010e0303 70
    0x168003081c44602031541c0012030001808048420304001e0804022021140c0650340c00e01c0e8456656014480c4011040c0900e440104100540207840e1400c864500b40c440d50100d808038000d000f05004502d810080100d0781d010f90341c0c40004c20103190082c1d20122000c0c5c04040303034807248450030503010440781d03500c030549555518003c1025940780f41c03600680b418150211040351721012005890305c00c2100c080309807600300010020000e2001d0541d00300700d076844c013101d410418601840c4000700b83c210041a001e8821036060300e8000081e11001d500c001203a0084488040020000005001501e8250342c1180c12a40c1450503d10807641d020004100c2420381d0701520100b65248402c00815007280e205c480105811910810008a0316000c0b07032003c00c04104090500d00e10141269103140513040c1c0341c0c01150444203c0e24586080f41001e0800d00c8141c1d18280304104811081c07080a100080140c03183c43e407080342d900240d0b400c4083c08003940000001c4015552911a40f100700841040510721 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 117072724 1250 117071474 117071477
    0x603070803070f0c050102030711060a0203070209040f03020708030304030905100e040c0201150f080a0611070506090d0206060603041211030c25060903032c12010c0e04051306150f06 80
    0xb000c403d403401c0900840240c1c02581950000c0c23200f54041080f440314985069025240e0b0741e910341c40424124210700c03907500003d6200010005020034420900e402c2b0740040e102c0d4003140c490315215240c1c2c1d0703500e010482d070043c0002c9000500780501d05102022800c2c007502824107407414401d07100050280e8602d03401160041c0c0d0342e4240381c141d18012a001c3c400906405074503e541506001000d901c030548070307030046d00940d00c2d114034181d00200c5104840000340c00c80d0036070f03101d41400348450342c503402003000071b0005224010100e040f515010049034015a804000c000c15101c0c030810654482e14a803410700040d000500850764413072024810111a050021183d041d00c0341c500d411103401032034030b40040c01004040c41c070a2001a80003030001c088403000741a00e426080c0081c844000d01754129503044d801c0001321710500e044501c15040611220314948a101019044034240b1080b10401ca0301000c070100d012000380049100c82d80403508013001002d0401605441d01090b21018030590b02200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 117073974 1250 117072724 117072743
    0x9020d0618060b060306031005190603081909050f09040f0501020d060612020301290705070e01060336060b030d050903071707060f0c02030a0c1502061905060307080307 74
    0x10400144218421203c08075070050441c200240883c3c3d0720885d80881280031665280444e4004034803d80c1d86889a4104a080c4140c5450b450200700742e8200d100090132020001a0a1071a90f0082c00030b030007607030000740103002440300392410083c006002500030360309403441c1840000410820300060580d02917003540441c500b031030000000c018840d0403410524081c41407006000103590416050642225401050300c1e100901e00225030901c500c110080031403042120010b017a4082014090488255480400c10440080c00e6407244400c12807036007a505510780040504a400442c511000034040ca80c00900e813009080440d1402c400740041c1c501250703000c1425512441c040011202501c0c004019085075090320100743c2d03503841f40327000341c90610159440941c00d052084c0138a1305c80580080846480101a050807070182e8070324018074002e40d829551b041103030f070300000e0242c0c06943d85150714030345030080c1c100d2100142030140c032159041c0101440000d01000810142035840d020785070302da = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 117075224 1250 117073974 117074021
    0x20906160b1503030304050a1b0e0a06050f03031e030703090506040c140d0b0408030601120f0f06120b0103060203040c0b28030506030c0904030219060e010b190909020d06 75
    0x140315180c2c012069100c0e51080042000007007000c2081d508450344007074184e84001c00000a03106055090300102c0d4440c600c1001c0100c05200c0c1d8014030126081600c5202d80c0c0c044003414183c880c440c0c1821703550184080704015844074211801164071000e54680014400f0b1076548007414400151002c1c0c0b0300140000c001e02001981c80c0022071900400c03124490f009540b5510011000402032015000c0300002c000614140d0003940402200200c02c03104001d0001ca01241100400d007009840103070a180040110301d62003103205100707040e50081c040365402d03031843d40d854010b03610041c021541981106800035120788000d0150a45c292003442183c500c564260104018540401e41c180816041105128035510042000e02c03480c0015143c0c114a9500c1d410107a280624202c43c0d0760b8010100c1c88110309000c01030744809000c01e0100003d00013004540e0030840100c0350f4481524200d49130403002c002d1200540e110955481c406001c0e098140c8954a500007210001c0000755010408070181 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 117076474 1250 117075224 117075241
    0xa020a060801230303070b01061107091517030702060301061d0f0607020906030f06130215130b0a110604031d150a0c03090f060525050d03020906160b 66
    0x50001500300c40c5080806503151100c40f91040450144448142480d9901207845403024800c442082d030f0407100f40402540c1d20381d00101024840c2502d80118000e06ca0040760b10030b0380e8000c584160004440040d085800c1c11181e0500040c0c2c10355010130b62000700110b40c01038641c07401650081c07190392076030100322440620701d082803101c10440521990040d034042c00780f6560241a901841c0d015115101d0b61350b0340c007020030301d8002e60310000b900c0c5124213010408c2400e000a100b4003961300c00d03105100d02c007a150080d07124601405074100c01c14619040280035100b1580f02504115203d0310f0840c030b041e9605a02141030060903035058001030443d0035004070b402c03540d1420100100c400d4400d01e102c1c00b22200345c00c4050240c1041201003007010035070b00040c9442015000302600140020f40c1007655500006840c40c1d00c250003c103503100d845044680c40c452a200642031490700301c0003900f4004ca11000850095000c00d408a6021006011072100700e66804001f8500364818000d441d09810440340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 117077724 1250 117076474 117076489
    0x5011a0a06030903140306010c050a06050106030e0606180c0d02160c120b04030e03010b04020c032113060c090902030901090605150d02040b01020307080c0a02090105010e031b0f0a06020a02 83
    0x1104041c0b60402d81414000307a800001040f421034003000c400e4070381e110741c030049030551004007000d4014401c2c00441c1c1e042c05440d40c407080c12500c007034404000300130004480d04e03199501160401c0d403100e029000038000f4654404e9542c0c1c0000c3d600d4000745840c014020210403130b0020b00104a801800100140c100410a400c80b0040e06200305000d1101403140e070b845a02c408010801002c00103a201000310703030b0320250481034120704000c0041d501d40561801080d96a00100030140d141d00c0f0840022020341200c04045000f00030300b01c00340c0400704c070580740c6c803020300340700d204403010080740d50070001364a406403004d14010901100042080b2191342455010313281c01070706042a00c040740c0c14508841d1703100b840844295a0640d00440d15130391010042c3d0031070203401e90141c02c40d0400252100e0315280803641700f0703100f4801c46411100ba45c0b6030004407440381044810503003580c44412210241d000d90825008030190051111160f508002d010421620310f5501c0b11002d6801180d45034110319080b00d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 117078974 1250 117077724 117077729
    0x8040f050f010903050318030c0301060602060402090c03100902090a0e010e04030816050d0b1503072c180603011d0708010515180907030c0f0608360a05011a0a 70
    0x2a00303c2850f41940c8a0b541c80c0d120304a1600c501c038854002c6004203440a210000e41144014001c0143c0d5545c1c01002e5210f5008030790032441010403200244881d0485401c0d2805068a2268801c001d030030400035000039070108000c10340c8140c1c16180000d800480004540c0a000190b6861240341802d00c0d0250040740090041d801c4240e8041040701c1e5a68858140d030101c0c2050680804c024030540c0101d05880701148010141c0c0000108100703050341c101c0c1560701440c1c545900c02a0380c00c0b1050b80ca525070340b070709241d507a400141070040c1159408030058858014500400000384611070340120f000801124003040140d400248041140843c00c0c0718069104940850807100701d0548000200707501118180000300448803404551040d00410510010719440000769603a40d4582c418004103030b000d4032400300001e040d440083d286180301c0c0802c00402d80c204400d1080515804000303000070000f015504164410800c030040030403800d014a10342801c2d00f03000049540513180c03c1c03107004011078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 117080224 1250 117078974 117078977
    0x9090604060e062101020c0c0111120412110a15121401030204050403110a08070605060102010b1815130606030e06040302100203061c030207210f0b04050a08040f050f01 74
    0x181c0c2000006000c0d82501d80c8610700b03c1c1e0300c00a900c0303181206207100955800c44907442d0b10100751007080c1c1c40300151444840704240ca401c03680140e040d441c940e0310b0841c51070740000e003c410702082040c0c83c048a5000ba025200e032001c000c8a22029010405d1801c995001000c04443c680450802c9900070519600c4080b0b2060280000200466204005d038010321000340180d60b80c5000034107245c03144e4401ca60840b105800c3d200d48840c01d05000c540c0da0008002074880d10b14100c0401e910358014480d080d80d6020103071118000c503100540360b031032850008155101c620100d07003800e52145c0d0340307070001d40b440e49014400040b080e0602c480141201e40904c0c008005500810500002c240c0015040b9202c41c61003e0141c0c0d41c4e5100341c04610b014502e14800003a05c9132000c4403000b0190041040e4069a500c0c10004540320003005801d2814045034034007810b41d0345450f4080b0041075031142c1880c0d005000320200c60b00754100b640c641540780d01c56400707642c05862a000510136890a40844200c10009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 117081474 1250 117080224 117080231
    0x80304032f031206120d0810152f1207060c020c0102060a020310150c0605070206010b16081201030c030b01080c0a05040e0709060602010c12060b09130e0a0809090604 73
    0x1040381e40e6942d1042041400d03000c1c1141c8009015a65519107008441c018441603540403000712101402549040d10140340c0704007440c43c007003524400349083c1d480c214059610141e250010b081d0b10989154844004140003000c04ca201140320820041254008a03a1987e20341c1e0b4a030038180001200d55814055045400c51659100ba81c1e900141568200d0318003880140d41f91218540b21010840c5640306411095107603100808064204604411107402240144410307611010204d03202c010134010010f180b60144200c01080c0400854184028840c040103458003e0074070324840d024070709034000c8601d1108180c00340200301484c034610780184229030051032020300010001d00f402e42c150288902a61f03a03154020b0100808009840090006d800300b002696142c01009000c2c040c90f0072014045541c1141d2080341d0002441100d0071104080080f505210b46c0208116100d0080800004802c0e128400c60442e49018801c5440315031107114290381c0d649400040c0007252000401d001d210f1881c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 117082724 1250 117081474 117081557
    0xc060e0f0414011e03020310020315010c030f0f050412061d03030c07060905210903120c03040303030b030a120203042105070b0a030906060e1b07030e0d08040308030403 74
    0x10403034a414155100400130381990000c028002000c0362640e40040d6151040102e081c0d40050198000c60080950342c0c284041040184015646a852844000c001410076104e07801d8240c411a080c3c15039041c1480e1161403d91781c0d03601450401c00c100d000b42d44d095a61810708910080d0984500e04854014000d141586401d10719010940030318000070b40519110900801000000d11004014102c20104030144000720b00050400d40c000307541050191180c0e00340742e000b018000090744c80e0041c2c0c0c08020343c5040e0640c1c3c3c085014000c0256003542511030400d9100024200341d045a084080f1a401192030364a4030301424809680c00154030744d0b10b91004410004240040f5420058411040e111795840c5c20b04901180103003d4034102078030440c903120022800300c4443c9011400b0344902800744c0c1c000d1052101c541000d00c629000100850000495488a41004910308550703501070b80c13941c1d0600e075603600e0b008025030040f9001c030009201c0b03c110800311102001d211080780f9044003a019000d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 117083974 1250 117082724 117082751
    0x3030403030b0103020c0102030f0406050112021f0c0f030512060609030d0305040201141204020a0602011e0b01090306470603061201060608010e070516110d0c060e0f04 74
    0x4409000642099154481d22041e81d0203501191b95401c4030100840d0781e890500e242c0c0030b00e0340003a00c04444003407c1400000da6070b2020944400130075002800070552145c5040003041005140b24242c0500c00d0300074041000c1100301c0320741c0c0500e60080d216255a10414414010090002441603214500900c4100c03500c0d10001085903a2103103030b081c000780795121400180c4140e0b00381079031503886c0080010343c9024003800c4140d0501a078420303114284801d072111010703030980d806120f40004422510a010f201c08400f504140e80c611810304118040d941c403a16039005031418082600084041c84201d0826412800c4468140c0d21003002c191003400490080c1315500f820305048d2501c60040031002ca00255182c503c9520310078290b000800034a40d0310340d400f501c041c40910a11452400c001c00240c81140548226120b40f0040e48e0070358040912030781c64600e40c03980d40410300c1e0000100f9094400080d54560940301078038a5850303440c0080a100f040100ca50007043da00c81c0201d080a00516894 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 117085224 1250 117083974 117083977
    0x114040f0206071b0602030a080a0b09040803100302090a020c1c02031801090506070501050601090b0f0a0c140105011e052b15050f01060e0919020f090406150f090803 73
    0xa6030440d9280d40e105070f142441080c0c200024080d0a8000040c0c0700094610340000080150003038030380701c207020341c1d07601040c0300d040f60b1138a400f098010600c0000900005c1d5000003d65004071411400148030381c90381c01242080c1c0d002c50b101443c81d5400260144140d40400194460340d0b8a544010180404100025101e0090138052441500da40050380303441d80c0074052840c0600400342045494001604201c2d02804099410b54041000d10388040380c0c9990010445074400f203d18045c6140c4012401d04844000302002e0644028402500072274800c2e5080c016503000b41400c001c5605610090101f5a99440c0560b1105120b80e1142d200844200030940b0100e84036400c1103842040300501b0300b0509031106540b03070803230031680c03601c420040340784680c54916060316015510064100050750512000d0007003961122405100f0284075401000550000c040090f40004554180700141d00800d00340c4000303030003042e02c444819107580f01072a03000749503010402d10340c40c0c99288a4548030345940ca9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 117086330 1106 117085224 117085253
    0x30b041103042006040f0308030417070b0108100e070519030506040b0708061e090a110703030f0507030605090403080c04030803070e030c0906010203160f0b0117011404 74
    0xf60030440160380a9a80c0c05d4051040e4604507240c0c00c415400081040315001d01070290003044031001005001444c1c401d850407401035041000c4c9505102c03e145000d00890b1502c031500300c0841c0001200c5040b40c6081d1140742d0715100517030041c441e40c0807541001c2c1c210b21480003030008000aa814061203208a0307500c154850b00d80e282046070300100c0090b1000d01c54000a2060300702d140c90300304280c01c544443c83c0020095a03480460456401012040e4040384e44c508503103006442e0307805699030200f1945030800c1403504200005100c6000504081c0401c040400011864071010084801840c1c10000107520b0349400000200001c0701c50803081c0c042d005d040908401030030b0200007140503140c140c014600700074515092250100160005030b0395030802e007202c00c0100e4440d0f8100d9018203801415403c40a125201240c255a0140101075550141004000c0844c81c505ea12903503 = true := by decide +kernel

theorem cover : BRFrame.Cov 116906474 117086330 := by
  have h0 := BRFrame.cov_init 116906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 116906474 ≤ n) (h2 : n < 117086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
