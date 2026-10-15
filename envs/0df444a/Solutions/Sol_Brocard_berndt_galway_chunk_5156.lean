-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:56:05.741589+00:00
-- url     : https://prove2.me/submissions/fdae935e-8565-4130-8ad6-8898d010cd39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 927158273 ≤ n < 927338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 927159523 1250 927158273 927158329
    0x605091b1c02060d0b12031213030c08130e0a0c02070e040305040e0a060603051308070f0309120614060f0a030b070c080c0c040e030405010e012f0304060f0507080306 73
    0x40c600041000b520f00d00380c00222106001301300070b100003070206e414540f80c0c0180a015284101055425000b450340000109450b61301d14084414880008005080c90341c007080e180c031030180340344010054a4141d8404140ca40e03891054000310b1b8210049000182d020700f1003044404034400e40e65030030038041c0c902549000e4a030360840c03142c17010582e0100d40095841c001000610b50510078540c0162000c0d8640700241702e1a2a90341d841d02400c04054003010800360f1800c10035000d0b8110100a086981c55458041c4035800c0400040c4a54840d1151000b010300024901c0e140c6801d0030109014000c05085080e41180c65001c0d0045005080c8030a2003010044030000ca00207030082e003201d40220b801003103140b40703c0c0140401c0e194100008801588240001c2c80541e0300800282542103080c601414658100c1881400304407030010780304443d004044511003c2c401c04002003095a0031078440569008580d081190140310703125025049040a00125800b440c1548114401c018010080512008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 927160773 1250 927159523 927159529
    0x602010c0f1206091e0c03110906030a090605180c090c04270612200616060b04020c1c021507030902040e010507050a030b0d050703020f03030705190605091b1c02 71
    0x30709007044070429405d42c1c14410001003030140b00300d83c0341c4910b41030100e9410b40803c108103000342208035204c0c00700407000a040f40a42d6203c0c041058024900307024904000505450342610355900f00c502c1e006480c4540141e00740500720f10300440c0d0b4800070310b150507d0001100d41030b01d00782106060f8841d8015008103911100d002e00006000b000d1021006124949031008076040f031003024610103444098101c0150340c4001c1502c510110401c11441d08820f18030388000149081005c03168054030100d10b220140f400001e10500b415038816a00c2d0100798010802d0341d035191041d1005c0c0d0440c3c01c1e6000641503d00c130b500095911071020380301080c40319500d64030900b03440080320b01a00003080894a580c0312680360040d1081003409880180a04900c0d843d4a03803102a9800301030301894928104507101c1e20200100da0402c2d40240c1900d41740c0340d07246030b0003600c6a40072509039849820000411002c10300480c04008460791009030407000841d500038030244900d00095988403580702280880962 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 927162023 1250 927160773 927160781
    0x70b0a03021305030d0e01110c0a080c01080c0c07060c1e12120c0c0611220501021e0a02010c1514100909050303150a090603060e070602010c0f120609 66
    0x2400980300541c903103900110090301c00107981c0c00607120750302401483c0d03031480e08020794000c00a420720341241c1c40b640c5005000d1500340d400142e070382c01003000c440015090b000441c104000c4002607907908075644424985a055000b4200070116035000840c1c01c111250044c200010050700ca00484402c0314908000d091100c04402c0040e102072616109202e0303800d6001c01458039070240004208a0301154100003071080450100082103196101c220001c02c906541c2552902000030340700d40600391080d801003082c00c00611034140548a00c0d82104410305003104500600c005400040513910000e07001118020407000c1e090b00d00c10101d0f440140710314880e00076040e00a00d940c4d070702e180a0800d50342c0d04c580074004d9800128040d01c0d2040c0d202c005500841243d030840703078006a00d03141d5600b000008a00e40020307403016401929000340001041665000030715900010015240d1495980d84141d09803011280000002030482c0501488640a00d152070101d446203000004c00545465041e0111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 927163273 1250 927162023 927162037
    0x106180b0301050903030c0a0e0307120317010b121303141321030f05030c0c010c03050103140604020102031606020c070e061504060206060424060e030f070308030408070203070b 78
    0x29448105201440c182405a0364100c0b000600451561030600f00c1444640160400d0340e003000f040c02412100355604200c450041c004c1800c1040036400e50b4a000703000708107090100c80144a000c800003c042c1e20390001d8036081d007c80c0752040100c1c4d071859a540c0c1c0701d680c41c2c0700403410310640060f083c56240c2808041d0510865010117201800d0405000e90b0489070350700310350854071006c1c0c188000000d07405000b80d038494456040981d1a82c03205d036550882800354220b080141e41c03078034035040d10702903250b00b2450484c0c2c0280c0101c00c040000300039958448504460190160b07000b0440e44081d102100094002d0034040c980040c10191002d4505081064650046900702c03c4c00c4107010b800c0c42d00340c1e107040c040b003011449186030921340702010792580b10050900e4800c0c0d0343d0300340b0100b041c070f0440b01410316000288039040c40c1f503458400c0600365001e08100c0e68020302c1400e070409014080015504160382d005811a4110380d40c66507002d41d181e0240b50100d17010b014a050020314401680058070381 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 927164523 1250 927163273 927163319
    0x5011d0709090f0f2d0b0f01111f0c090506091509040906060803030108010b0105181012050708040c0512060612031b03030f161e0201112a010624020106 67
    0x40071904035202071240c484002d01c110340d07071030074049128547c1da0600441101e03800b0300f06450218046108103060000c580d0001121112282598100c540903a00c620000003058552461030b91312013003441076038000d83c040550042411444084051300d46c001400d85014000c00205210906582e0f50042c4c580c507a0100780d40e60302c00b0005104038942801101c101c1c0c00c00f03190040c1404225901c0d0081c120180c0991405500641411202c40f4440d01030419412448003050000d4201001c009080010032a415541d01c46064000310f000c3ca006504040c0c2c240401c001030505031111400c0048460082e1040d1046e4401003008035a292540381900c40101c42c90006036850346020020400312020080002d0520311b01038095038650360b00008010011107154900481e101540c0009030f004065060102c504240c2c0403071a168200040e00d1000382040740281c850700e110800c8103003642030b01c0190240d407065081c14140c2680901040700a115201d01c1440040741c0c8035500c401c030320800510710342207400d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 927165773 1250 927164523 927164561
    0xc170c25050f090a0504020f0616021809100e03040807062102040509040b04151d010f060605071412040e09160e13110907020105011d0709090f0f 64
    0x20803a800038204400610060310ba500e0405920030008103412801400661003a0751500882c0139500d481300d4120301e20340040c111076551031400c0d400c1404512410320407480f40c0350701d0105407103282c20300440c030b4004c5000400400300d0586e40720703000b230203400c850a010300d8502c4244000520340b501000b825004010a0b00d515010b00c088021041c02c51100c60502418240108010405504c801ea038031a07001c2d4000d86254020b0700d03207141c80381c0301c02000c00d4541902c904003241000e5401000c40703040e03540d000c85d00081299281500c650300a80309540725903000700e41d0901c00940484c8003e07140c02003c01400003941d80c444132050b54611150410740100c2c0c500c02c20002007004100e0304022507a07501c018910f600c2e102c9494002c021840c0030009291541003015100d803142005101e205000e031202004200759014503040a000303009000034030030014007801c41c03402080b40308841c107199409044240e07202e800c01801d015100d40038214003411035034582c0e650240f15402d20070354440c11619030b5064003820 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 927167023 1250 927165773 927165823
    0x20a03020418020702060304020f060d05070210140f04020f061909090f0506090118020906120a05011a09100e09070c030e101d1512040210050a0c170c 66
    0x11440b21400c006440711103204010b44805030b0b07034102c00c2da94090b604035155080340e120400403d590340070748084141550b051000388251f4540114540690807100c40041002458040b080751403880146c894041080e26034001c00d015045c91031540c404e410019120030310300f4a00c981c020300000e0b500c08040740056801e207401d00c8211001e01540840d0042c0c1c541c180a075082c80d400090003e03d042c8070308050140304d48203e007100400e50f0156040c0c850700034515034071800d100c402898800e804403402d4407810300d030038000300b100c810724010010443c0c01000300c2c5080c40e8060050140c4500c0d480e0341d04040c0114603000001070307035858030000e21420141c0d3b24002c00d546c141c9809030520200d914058070800b1417581f95040c19a0101c00d824000601d2000310030021400b501081c0040049a600e0520350000038450011031000344204d80181d00c01ea076420f481500342041180d1a0052030100000602a81000c5020940300090440810b0042c91041e15048001e4242031526128504000340360021a001c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 927168273 1250 927167023 927167039
    0x303020703050c06040819021201090521030c041401030605041812080c07080f0d020325080411100e0316080601170a03081504020304080d0b1009150e04020a030204 72
    0x41e104100f0956040f0300741070a064440f51102d0043c4200003014241e00c0c1d80000350342d5091802c1214000801c020000316103541411600c46a02012014140300065200c00e010340903081104d102d8070410015030700b054104003154076400c0794420560b0415480b4100030070260340703910071112a00c070540c8000e12403240c40d141840d0140b510030308880034081e000b0100303c0034480b404125402ca50b032001b400b658441500c90074440c54004d007200080d8080c404010424940d04405101c00348110091003006004062a000c47c0e00310301c1150000e10404808078a003030103007000e00070310500b0f0720107040445007083d0f03060100e840c29654a81d440e0f503200c841401000488400e12025003d8001c210810605560003251560b8070001c1c404014100014940001c280384100c4d90004074400c0010300c159540d041ca400c114600d6040791920281c0f803483c3c200101e0061030602703a02008a40c01e9100d00d00c40a24000e03e4548010910070384805001044100c10b00660b958801000d00340f24a48005850303904014034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 927169523 1250 927168273 927168283
    0x12040501030e0c0114070f1401022106060403060e0c121b0102124302040c08130b0604020f07060f05060604031a0a0912021c090f030b090f07030302070305 68
    0x184042c507040050402003d03603103d110f9141204042800d103650703074864a4240050448694064071a61300d41c02002107105064004100300c01541509410320500001c0c2d0034480101075809561051003000100001441c42d001000304689a006640981c211140402e4020070740b19010005a00130601850b668020fa11401b0030800c001c0c401020250f01c087d400d50f00c203200c1c0d8441c0c0703075402500000c6c200740c01d40360f11024021103e02420f840c401860310072240c0e046041030700e0100c0c400d80c1413000070314050784604807951207107040b8039119407174211a85078420040000b03088540c00a8007081500c1080e501f0400074242c8900c21400000c03c2c5840924640031031b480502101c0c0305c1c010411007080860b444059230308501b081ca68880b0000d4680e0b03240300c0c00412038030340e0042052410344500724106402150350744c0701200c045640004a2442c400c1100c0c1002240215802800410802d2012800c000417417a403107150202200e03009071100281c2c42c40c0c0f00b803540c82180168481d4105000b08402400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 927170773 1250 927169523 927169541
    0x18060a1d0613150b0906060721050c060109020c1902040f02070803010905010503031c0c030612030f021005060a030b1b0304050a0309090506010c020f150307030f0b0f061903020c1204050103 83
    0x1c1045184e4940d8009040800094002c41c81511b011840c5414090b51511100842400c0d802c0c000400303c5201000c0c0141d0440711420345580a00d00000450407418021580740d00310000203001c0c03074040c0b01c0c0c140c06207031400e55050742c010b551813016004164040c401401501d00903030b0029203c5d0300d010815002e550301600198003079003003031003600000d00c201d0400c1e8680003c56900420b5803000785404600034200303584602480511000e8800078160800d100c0414100942d090316880500082c0032000d40310150390054000b41ca0403810000b061801c40080d03044174012400b409500710100300002160000d86040d501600202c3e035410405801c07200c400014600c0301014081440d010001070a00c40c4661070103401001c049810041c980d445260084000b240554040d842e400c118100400034205251518005840e21046540782d2500ca1170716040040001c0c070403072400150440340c1110342d4100f181d0009058080c400215495000d006e2007000c1d004a25030380e80c42d1443d20f8001004e46003440303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 927172023 1250 927170773 927170813
    0xa0c080115080f07170f01140f0f09060a09050f0601060e0306010909020a030f260a0f02070f140d0f11011205040203070603020a120504050a02030618060a1d0613 71
    0x701c00d407a483c000202c0c450007200c03000c004401a640000003e10b050210000c00c8007103035441c01c00001c0b001076206442600400c9203180d820116a038a441c10811b92500f5a80940c040e440040024002503940d001400880d01c03070b00546410750034a1008610300582a00b007103020424100d0000001e080c20090680106001b90080c0000043c030b8020810206083c000a0255501e0400c00014001c03568242d00700c114401202154080d04d02c0405011904004a2170f40090b0b00000f8419100d440041c0d080241c91036000403900962802041040d11006c03003400e10341140303c0801c8880482c1c5a14500d41c42d40740a8241c4440d03003032591000400345207400d584042c6076807030308052001584002032014140d480034203005a4515010006861301c2c00b4641c1800100350a1404010401c013011400c1c580700c138826402c9403425100c0d500c40c00c610f01164610304c1000ea001000140c0075019541000c0e81c102426100e5200009508070032a0404008079420791400043c40345010400101400581c1415050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 927173273 1250 927172023 927172033
    0xb0405120f0a051305030d080123030606041a0d0516050901060e12031b070302040612051c1b06050f0a02090607020402070c050d0c0303030c0f0806060a020a0c08011508 74
    0x2160328030302a00605003200b04014000c00e440c00d03080c20106110b005810000c08840e46811014001050000e090040885001400f03041c418081904940d181c90502c0003000703804581d03540e509110040c02e01c1c264210148410007010b4440d602d92240e861210350003000a004858500f41c6c003030344034040b07a44c880f60041e03600c00c0040004582c4903005000460007110703800c0c02031003d883c0c101e146000d20000c1070032a42d40c482c220300c00c02d800084c02c0340c12288280d40600c0307099500e012030744001c0700710f07030340541a40c01c19880090300c0780141c01c05020490f103c1c01c04001d20702405610071940d104d049806c681d02c5030340720140034801100c001c44960000d0301c0181507290010304800f0504901821200a000d00c0c0c0101e00101040520050607010b8140589240c00362182810038a888890a10050b000f180c6410b004590951156904003c41000c0d5110341760542c8405c002d0048039400110508114004c1454820000304d1042c607134030040c015030f0008202030500d000c14607603480407640070800c40d0b840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 927174523 1250 927173273 927173287
    0x30c06011410120e03040b0409060f0308090d060f050c0c0c09070914030a06020a02071d01080a24050a06080c01210504020303070b011d0109020a020c130204120b040512 74
    0x6080040d6842100a28000c00c00544900300c40c3c0103401c01c4003201410707000100c2c0104804440d0030244c0120b900e061000c2c020300b41d58411481c48640c0500000e40100c108210700c0c0d1444c144034000e0781400348030383c2000841140300e10500080302c80655194004090005000b000200100280f6a040301c0c1202c420f00b80b402d1400c0040c0071036810303120b814210340848400340b803680d506200e540b040c550801015983d4116154000351282002d010386645c00d0b46807180f100c0401460b1942034140e508c254014100c01c10346440d4008180f039440944008450702070715004035041e01c1c0c05268000c0b0b4041e8004180c003814940100d003024075500e80a0304001c2c2da20650081080307211968140600054000540340d03c95001180c1144903c80c005044041d01f03100014100e41c0b00481c04256005900f014811b60b6245c1c800340e01640704055200c1c0060344124500003041ca001c505d18400700c4044171005161558801d4950014005c8200540744402c40b102000305201e400d0103451070a24040e91a1880d00d45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 927175773 1250 927174523 927174529
    0x5070f080307050319140703180f0f051e0a0204020304082a010b01030b0a170708070f0503060c120708070909060306020c06090d14070c090204090b010e0402031005010c0809060705030c060114 84
    0xd4020302500400d40c41c2c070525a0414100f485101c03409400495141c1c020b000c5003012144441072a02c0cc80d0644980c0c00d41504a410b103c102200c01040b08018100000403a000c0001035003014206030b0f202d001c100309401d136070001d0005801c11007001c0a2492420070364120080d0071288001120340c1410b0608561000315921403d42c00166030a03255a000700c03080c4400164a00106c6403c034100c00d11a0401c0823a0b0010b100c1c0f0b01600310b1702d0880450380d5668407101410110301600c035a09805010760310200d420306000d001080c0e8030422514148031a940d581c00315a0507140c035644162000e59002a2502101c041402036550000004c0002c00700410090001441070403440d072080001500801e24004000310003405000074a0000002d54569883e08040c000030048041094081f85001304034078940d080034000e50340714021900418044e50300c1e002c010758050b107125a040b03d803a5010002e803c074544d62540030744149402613001350b48901036094050f142202c10b03000846900070340c00030800039075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 927177023 1250 927175773 927175811
    0x60930113a0219080c03090603070903170a050a0509040b13060e060d0507061b0c1512090c060e0d060c0f09120f080a02030c07030b19150605070f080307050319 70
    0x950180310036a032445c1c400450b80c11070280c42c0025070300c130030b000040c040082e91042d00401642d005031005074415550b2100b04040b403050203d51008180300340b024580f4203004101409d00800044d001141340503a000008829041070400c9440300c0d0360342c010a000d503185140546604c46429647c10014240d1034847d80d86c2c500892103090300b08600048800e0070740c1d15100e488070142d5070004194007041d803281040014220510040c4000030182904001142c4580c0181021140c200f03004042d09810a13008640c1552210102504280c100e80e503600000c440313100311948140c6a6640700c903201e1a45030010003c1c881d96000820000200c800c3d21701064980d0789210702035501c106402d58400c0d07420000e0b070441c010828842c00ca4002d1007070000a002d1402d890a1066061010381c40c101251802000304465803649055850000c2040521945010310010b003e080e008811400007030401c4d0b5181b20055004449007000644040144086444005110107504906800600c052806075801590038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 927178273 1250 927177023 927177073
    0x1e2e0203040c0e0114152a07081c140a050405061b2410030b0114010302070b0a02070c0512060402040f021303060930113a02 55
    0x1556000010504201d21019010001c003052001c0300340960303480d2218015040700076501c9010b207211aa144030303450300d0081103d6041150604003c0505142c40c002c5100c40302c4031841e415944101c04000c40c54840c2007118410710300745019200d00c512005c90006000481c45030907401c0c00d020602a00308201c1d00305040c0e50a40302e0135100c03181c640c0f00b00580c40d1611100321030001403502545240038542e021103100110009041000c1280790b481d2445032300314108051201038141d20110006100350018010300c841c92400c1403401600b401640d4407030301005c0324142c0b1032044190340065000108600d0144803401814229440c001c03c004202040d61a200001c200901c00c5640d0003650b00003034011340c1074401c0326400ba01040603082d100c0ca000c0d401002c3d41e40041c0c820a01d02009213846144080200e01c15000c8400304a1890807943d9055031015814151000e06004401d8480c441061341c2851081c1810610480c88129071090042c00310904103070171403400c64200c0d54680481e0b000120002c950 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 927179523 1250 927178273 927178363
    0xf063111070c03150b130203150a0f0b22060809150415050601020f030a0201021e09030c130605040c09061106160e01090906060315060905090f04030e031e 68
    0x100c1110f50742d560010314109148940c460002d11b29402c0c42c12082d07002c2c61181d44400c000c20000140030080203000c813028404e0310a40200c03001c0038402140b0800c040c0c107060102d603004d200d04072440502c0701c4180750b89801c01000100350100700440318a041002c09500c1c21590050b06040c00d0a4030780461a003501e10f4950300d00c1d03441d800403800d1640300300150391041465005894a51004200080c0030b90310074020582c0101524904030540c13601d40c0300312241034800078000c03e0310383d84140078000002c1100740c41450380f0355a903000140c40d80300d03405114210019a690940114203144014045c5560070032500c03401e44c03080c402c20030980ca0135020b10700ea101e82c50070030303800001c82c0c200102d40011301604982403107400c142c4001981030301904400c0c54140c500f0b80201c0245e03100c9a049505900740c0c418250b0050700d480209110600504010b0782103402450700920300c0454001003450190105880e40000c0c0880030178009000081c49200c0c00d282039141d0004103503400d42d00c00d07071100800715000b01ea = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 927180773 1250 927179523 927179543
    0xa060315031103030c0a0c1a0f07021009030506040f0b0c13030308100801180c0e090a02011b231605060f0a1b0c090f050403080f063111070c03 63
    0x1070ba40d07000c205448080400034100c070702c07104007841c0080e0500d40e188100c0c1403464004032043e000d0000041651b2203d5100c240c01410003041c1e030200b004a004000f540c0040c0545000d003c000704609010041c0700e580240030000785800140b900080780840100300301c000d000144021141d12107041041c07400c403030f0180303031541c815298405807026203000f55200c00c10b5503103040ea80400f01203800030210306c40360082d20300c99200c0d070352040008030f044001c45a88400b50050119000198003c140c035071806a41140452000c014903503584411045001c2030b00082c10204200c01c1007080d00f048000f1182c2e10015110099528000228880f0702030001080300c100d00104240d91854410700f1881601c00d800d40c40c1198a80490030008840c008038000c099610b4140700512110603030f10b001d002d0056a050f614190b80c1c3da0f4400c1f80b03050500000d801d660780b00090200c03201c5418120462901d00014061100e4850100303014000c040380c6104c210340312041c01c18010500403030700021256049a030401c1c0c46032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 927182023 1250 927180773 927180803
    0x40204051c02120a0302061602150117010b09010605070c090e151e25031104180e07172109190315020a0807140f09030c1e0a06031503 59
    0x750303640c0f000c2d103950020344100314140061590010f10a8040e01c00c0c0310b003142910121850482c2c60b03040507010a0413802025004220300000b4494026520420b0000041e14015040014205050a1b40054009240402c050003840001d960110040203401d00800681c03041c5c5042071388404400741e002114810302c000048400039200c81689a4101c0100000d1b80c504d130155010b030710050040c0e0040407160b407046c0c0081da054068031403040c0100407998070301c0c02d0916004411440b40c01429005540c2602d48007005042c4004001d0b9501a18402c0e001580058699802030310303020000c0070b51400d1b513030000300b20070500301c04004503441010280c55003444005496014902500141c0c002816407100540d000d0803e00e141c3d015103842c0e0b9082d40d44540c0c0b5120004111415280c941499080801c2000020f0b0740c05400c60040c00e0007103024003a6020110400002142040140e00c800300c0d0038880c1031072a01c186030042c0400050401414204905680b0880c180f00880d140d010050034407402000380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 927183273 1250 927182023 927182029
    0x1009060b0c014b0603030c0b0f0609010b0705031306350c130807060203090a0509060916090503010921050703081303050d02180a120b0f10032f040204051c02 69
    0xc0d400c0c800003520188030081d170320700e00246802450207042d60307440702e0407011a000511045946000f00401411f1481617400d00100181a41c02100b00f00ca15100c00c014205080301707154504001440030351120301d50000051440c00010582155203840032000c010341d01440a6030b816110b030040300c08541980c40d2003015a03050f140c441d0a0300546410b2049400c000744881c0d000005181e5010142c80c5005695952030034440780032000d59403540c6c02320f00c02c4d0014842070482909c1200743d9132240313015100295914042800c440c81000300b92207211001b045e800c4102c98483e110122010103107003840c03a113000c944004068040243c00802d04c02c0d030400704402030511030780603585c001031103180465440c900036891060142940035018050502c450000541a020000410010350400b1120a82e560b801c46a00040440240465410f0500720f80c0800466421300c0b1350b1004290804000041070325050310703c05800e8880010b031b80b08070f00401052106454002a40c40760301d500e4150192201018400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 927184523 1250 927183273 927183401
    0x907030203030c010c1805100e0f0d0f06050702030a0c03030f0605090c03040507080d021b1c030503011d0721090602030c07150515091009060b0c01 65
    0x101075414807000ca1050107034035040d400b4030362001c1d0039158505082c1030005022040401c0344681039105030310710400d101480c0501071080589900505216a0b0307004140003078000000c3d1841500d0166045150804214403807090541190b01800254140034400388014260004030354010201511110401001d283c16049280a0302008002c01c450785403e001d8411141c100300d81c10f4880d0301c0b80c00d0700051b10f094041000702c400180740c1c1c0646018100348050700c0149051042c4c4941100410035a0a10041400401c1044038481d0340c42c2c0380d59516181c40d11225900400b4128900016241806444c64020000c0c195844866004480408480640d070004241c101c2c8050001400081040047c4c0b400340c00410802e4803424245040d4110843e1400483c0c0040b903184c020030001c2c41100180346003402826031310040440003101e41b031341c0320381c02c0d00b054898643c05100300f0f54020521032034962081c06a0000c03008030004d9480301d6082458410b44e00116031111210000c04030100f00d10820803c12 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 927185773 1250 927184523 927184529
    0xd09050106180b0103060807090b06090a140a0812030a05251808071202040e1002120115020a0b0403030b010c140703050c1f0e040f0528091a0907 64
    0x8000391036440d841c020310414801e2419400b5454480b00c1400b941c0640300700001e031102400141009420003c9040092020000a940c040303000d021a80c03ca0f031f01c05000e40040c081c81070031100681c00f500107000d44401d4540180c105500a03030f44007030000e0284001d030303544000020004691a140c001c0f078002d01c102004a1121a21003102140300f038203800c0500050b040701030522110889940d41c280c9501c0720b0a07401040081d0012581050140c0b8194122140301038203c01580e03004107800c01804101d0b4018203801d112091404010004170308880340a05190b00039001034040398600c1d03910070183c000014001024075954080311086640700713005500b40103511200386692504642001641d0341308901c412a030510900508500341c1c00c014003c18000c95482c0e1340f12210303102c00380c07007910701b0010030b504030350880d0395082101d6a030982805070701c0c01010351003000039045011462401c050303080d14022008840c1042a07039800101c0b08142030114040100413114941c031124092820b020203a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 927187023 1250 927185773 927185783
    0x91b06050703210e0606011e0e040b01051c0f0f0c0e010c110a0f03060509070302012003160b0609010501020d02100b0a080105010b1c0b0109050f040b03030c07061713080d09 76
    0x45541114242e000801034003c4402341c0350040c40c1c600c0802984480307058408c1c100c1c005428030340306480f9410076800a242e2507005051047c06e03c10b00f00700c0c15100800c114030351194942c0307802c0c990400c0c894611071044240a0084140610560803030701600982103a00c0c414100a0f82c2c040420038081c01011401820300c000304400501982c0700d0000e042c000d02030009903a4140390a0120780c4203400012241d00b1654180c41c1c29480f6101040a0072550604d00c0c01c10680b0b000030810f85c00d200e01035012040f2040d22541c80010907017030200620210780c40c16001681558410107400e0b0300250001800924030041c4000403c0d2402042c01141621039164084203066080c400003042400101c0040d02c2d40880c228100c00714500c81814003415920700100e210f01240e0ba03080180b001703007041c07540402107071000740010401b680c003040800d103991b12560109105801141050005da44d10810f041d03940300c940c00c078007901e038103290302d50500032208040014010407001030800b8104801da04245003ca82213 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 927188273 1250 927187023 927187031
    0x30a05030a0c05060f060a03032d030603050c01022a03010612050a200d03050a1e051e0304110405090f0a0506060f030a120e060d02030a091b0605070321 67
    0x6540582000c1d2500022282406824006844505d403506000c1c8510700061100d648035142d602d041d6440303203092841111401c41c070503142400307100d42c3c6182810506503076000140c841c80c504001d07052940700f0035814119004066500c11041e2807400c26140c00e100c090b010001c1682c00e42c0068014042130780303c1f551039810414000144030340410854202402982c10440306045e207194000c2c02030500b000294011011000800031030b1142014150016090038000442c05900b541c0300d00c045045844000003c1c4001000441504030201d00c81c0c42240302c01200e401c50038a6520740d4400c01580711980d004607545e07000561980010000c040050500b401a40c4881d00356052094032108200ca40740e002d44e510801c52200c1c0e0031300080081300c0d00d0704050800c01c810034105048035806c5c0b600c01c0c210303403111043c4076000f80d01d120781c401540140c90b00c4000045845844c9040e00403c4c04100d544590280c16510030445607802400315100740b0f6140c0303420780d50580c1c5d4010051182c00e0b144032240b8800d2030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 927189523 1250 927188273 927188287
    0x130e010504080d0c0912030507170c16090608251701062903131b08030d0501050a0602150402190e060f10202407030b010801050f010e030a0503 63
    0x14000100401168010148104c8140e042c007074840039090700c11105418140705620300824403820251040d00d00c02c408544402c02c000405110035003141c0310001c510f401c050384850740b402d60004c00100614803480240f181903c0e10300042d07120114552010b820308645152041106400020034003e0409441c5031a00020348a004500130149409140141411031b2002030030082001041160400400b58051550344c603c5845c800c0c154050030103c80383d0307805885d03c6509208894122004d031500000650715000e00001039800d898040e4030a42c01807000340024070866a000c50088003640d03064555a41c152181e101003200d10a1505a82d280401c5416001c9406085d81c40c2190081c1d0701115403290100421003008a6001003180d042e002c0344010740c800818404004445403081b410070242d4880d064103410b01d40b079802d0404112451a0715880400c11200d4052041c0c00f001802841c20340e480b90b041c50080f8911061000350039041c40603410120001f50350030418401c0da554803009803911445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 927190773 1250 927189523 927189533
    0x1c1a01120302010b090f0c07030e130b04110408072610020c1b0604061b120f080c13050603130c03030302180306060306010b03060310090f020a06031a130e010504 71
    0x28038100c0440042d403d002001030149010001d207401506508034800481d01c070b00e01c0c040d61941c41404120103010703c1920300c64132036407103040c1442b80e50082c05010901455400420040f600c2101d007814034810280014007400000040071400e4540340c011884041c0c0e00f12164456207081f59030041664801e04c0d84910303040c5d0690f009082e46c00707031610884810140911356803011308030008900780c0142e000e100c2001041e00c00c0c0d5101c0e00b15104182c11940d949070300c0c0c85090303100c035880072560003007483d001c08000341c030380d0245400390b1140103101c0050502e03441421a0307245120074480c0368032680c40400404d448032140d80c030764202954040d0344c0500c881d50301c0c60050007941050070060021100c3c001d03c44a14200400d505203e1000280907020907800d16039080c02c2c03a00050b0081c0d405100d09408110304451500c0340d2241c0b6802680d1aa0340c040042c4100180c024040e0880000c0500f4005114100c006a0140d941001d004072001008a051101920010030002070511801c5d0708040074042448 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 927192023 1250 927190773 927190799
    0x915040605070611091e130f060e0105120c010c02060d020705150a020c03040b0f1c140a09500d08060a0e22060e15061c1a01 55
    0x68443c0d0f40501c41030100d07140c0410306029a140407a080306030026040300800c018100e42c0c41c4510001c0440c0b90310280c4200d44000c617240c000050b880542c4d1242d0500554060060140c010042222009a0000901d01c9551540c40c024519414082c000400c417045556560507a91000413030b000454803030042e42002135941194404010841c44c9440118036001101d00071255440da0b6100110b180602d014201c000710b600445070604400740c1404290a4a0726001824028034400d04012480000101c12720007a180701130314181e00d89240810f02d6001821b4032a00341f908955002d003403070002840814403907100107040b91080803981c8881200c84070600501805084200100442c1c20405c603007042521400000d4490310b40c80b080420342080421606016268072a0803217500950012503980420102a4210021100b1544550517814108400c004c100c1529442d52069003003420024085109410402203241c071020500c0898007d103d902c1245043c210707001c20000d10150b84d203d202c1031101d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 927193273 1250 927192023 927192037
    0xb04060b0405010b0c030711030c0a06020601060909090b160201110406110708030301030c0b2107091e05010905041a100206160801081902030a061103010f0608010312050915040605 79
    0x40c82c41c0800100303c400300d00c0d090b545c10201da64020341c030b0980540c50703079503c20852007466680b501c03c1c070990b410280c43d0364120900422160f001803107694180400502085040c0c3c11240005151035000c402283c03483e5039480e000341c02001001038904002d0003ca016054094068900c084001000291585c0c48000c0f0030b18002c800080d150010744900403a5202c0c442840045c009080c0840c0038000c0300c0b0360b24001c020407480307400e042d0660070380300c0440c40c1a500d0803180c1c40086220000d080100310100a281c0c000c0070340c1c0a4002d1810b80c2041c001803c541e1490213014043c5e40c0c0d440c1d00b100303902c2441c0704010101c8802070150203100f00003030000b5940c40d0304854202210b02944a0000001c0c01400414141c0d81d4072000781c1450f0380b90701d21032908001010001daa051044460300e40104407503108940f6608140f2485595960401c1a50302c10700e034503a8030603800c105000004001140c4004021000704519140c5540d442c0e41d40d0340011011180d19083c51000c0b0302c001000148030303030040c1c010101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 927194523 1250 927193273 927193279
    0x711190503070b16030807020a051203062e050d02040513090303150614031015030617151902090901060c1e05060f090f070b070c0f0f0b03040602070b04060b 69
    0x906440b00c1808040c4c0c0a810100300004507414041c4001a000702e81c0710307070f010300684106c8840600c1ca45072035240c194034281c4603070b80c1d200c00000d000c10740c08c010810300c130560500001500c046100f454a00800705a403e1011b0401c03c011030420340303028207501164010b1800030310110a418190051000512080c203048022074644903503d0880d0b0803481c2e80382e04480c1a038950040e10300003004010800d81c0001d01241e8809140d100c081805646200c00440403003d5a40c000350f5141046075011200d00b0041d0680b002d50302c90b5020f00c5102506100050340414200b032800c09031a510180796029005600160b070f0710401410012a801d0303803114480b0b5059000d40f0a2100881c03045012840c410341060016105410038000a8502d007d5807900350b800c400002e048806800c000340e040b41c2803d0054000001e00100090218144030007010b0006c00b602d100a00c00380032502d0190810f0a903100d900c5040294800400006d0a0010303e606507445c00b60400750b81001440e2500c0c08034010104c01c1480e81c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 927195773 1250 927194523 927194533
    0x210050901061d191b03020703020a1415060a0b040504090c0506220e100501030c090806011401120203060303071e0b010311090901110a030b0f0a0f060809160306020711190503 77
    0x91520780030300403403140301e00c1d0b14003017001c901c0c0c60842200a544005800d030306600c0b0300c00540c070020f544000c443c0f0703a01646402030004070104083c910305005001d49400d10941070540140070584c003c004075400c4410490b8001003c48152a00814214141d8001d81c1c1c055008121b840c3c0103500703008184511aa4a6000201c03140c8840b04c051880e8070584220040c2d44041d00144240d5029a2180c0c00c0030491382842d12a2565030f03407031649440c200360014820f00c119180710003010b5800000441c030042c0c440c0029030641c0b4003800031a41da40aa40800345c000003c50000205d00c0840d4940ea000d1541c02c0b1200350040c0da12400c1002c41405900e280e503006001c0b0070001284a030040c4980204500d03418095071070240380320000c130040c10a140c1d07010790001810700d080117995072b40c064400040445a10040c1600d24111014005040042404e00140c000c0380e101015403c000c0c0e410130943e6802311006854400a040a0100c8121030b9003550b001042190761400300f228a48501c000c44404404450b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 927197023 1250 927195773 927195811
    0x60305070f030e15040f0b0414010b010512070c15020c011b03090c0e1503032809060806041d010903031a0105071106070302150c0c0c0f010210050901061d 68
    0x20112544000d0718201500304500140c64100ca040401d030300240031b2101e4100d180f0864440e803000381e906817130481d10b080b00786803400040c03032080c00780c8402c006003400d005040070003038407070424540b0006004004004061081c6002c001100103c100b5100c1e900030215102d0402d40843c5001703011500c0c1802010008086e1012050311a00521a0f142c2d809200c16009a00d45640410080800380400d40c841e400046129400c0c0c808201a121205404183c010500c94184900104070014560304017000200003061113015001051203070007080559001550f0b00c4402401d5070004400e030313078000300355090050b00f10a140d0715420240801d0740130000055121700020041d591403183d41801440c1c030034043e4802d01240390180207000005c8c0240180c0707d9650300800d20f4015030808075440700e43ca150100749a01040310410041031000e2045d22103406180c0c6250010303607290a128185481c40b926480062495107003900328000501003c803100000c03d000100c04007921204489143c0c036008840604 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 927198273 1250 927197023 927197027
    0x114011b03051204021f0314010e0f010b07020f040e34050105070c0308133f0f0b0a020d110406050a080406090b0a0506100e10111006060305070f 64
    0x2444881d850340796a490300070314480040512000400c240c4e03006900c040c42550f00141880e601080740d80c159000200c50144d00030f224004c0006030070100c04030f0748401c10819000e4544c4812410364a001030b2490b106c440e60300c00984400c0c40b035041160001d0505114107482400002e0f04403103030201000350440d541c0300080340900103c0352010104110b0050604100325402600200b640134090b8600041003a20380d102c122003a8852605480110b190078001c0011946008800110395095484040781e80000100c0104004045900302f803209903e068010801000318083d00f0a0f650000c0c00300c0d0130380b41041c1880004d42090445850f006d04016114107603200f404200e900341ca503241c4a8504014101e0780444002c0e20046c42150f4003981c4104403004100c041012500c61854244041050301d0070009001c40c8000f50000d136018003198034000f800658403411001c00b2501a880d00700034800408502d240307411000f070441e200300d03854036001084003030f8150406882034241c0e03110f45c4000d110a900c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 927199523 1250 927198273 927198317
    0x2070615060e240a0504090e160b0712140d05270601030b04170c010e0a020a0905060f040b031906020408010e1c08060402041e0305010c050705030412050114011401 72
    0x10541003c021400ca11001c1c032454005454070004900d0081d080649421240c0200c0e04000300c80780150303020f45140719940c265120b006026110b40a405404c2444903610501002a64280c08081c040700000f844101d14807041035480082e11402e080c40307982001901612a0080301e011243d034002c100380043d0100800184103812207a008607400232075078a640300e281c101c565255031200d03080c8042005c000b850609009440700581804081c040000035441008805100c0e903204800c1c1d5402d140030010741d43e80d825116941140145c402140da60308100000c1c3c18002410080d10300c264412488400b404020b5010300281c5503000000c011518004410560b40c0c5005c581c644003e5135060303165401c0600c1082c0080d013101000e40301609083d16420380344019480901483c440107240501002882003d0207801e0041040f410000d107000071986800b81c0728440c50051b80e4510000707012003001c101003548043c01000c10211540c48558440c0344105041541890850009245581c03a000c562000b00b0b0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 927200773 1250 927199523 927199549
    0xa050a0e1b0613030f080301050306160e0f011b0f050606060f0706020702030a0206030412030501140f09060d02040504080a030b0301140f15060c01060906230d0602070615060e 77
    0x5007803062882088100451688490300345000030602c04800000500c4080503c1505481024961b440b5810703c0c1c1454035040008054045a220b140d44d50701009802000d0881032200c00c0d10086884c800f00c3c0016103c00c1121941d0f1081540b01215410605c420602400b4080c1e12442c01e45078a80c50750300402180e400303414100802c0d1401042900c000450980c010030400d8030144c191505514140c000880c19042103c06403202c480207130300b02074800da241c0304c1c080c0580a0242004540d46c0d029000c1020b00f028404118000e00300700c4081101e0303981c0c1051020005900500c144010300c0c0074640038034980c000c613540d080403e05104400e006d515040c02002683e0f100300c854480360f40e543c01c600c442094000740a90b00841c10004440e002030316490300a05400d00102c0003c50a80c2c0350410500840d5106d510110140c0071446080301c1c402450300b560100386508941154140e0007504152000741314070b41000b0400340c80d00444040343e4000040007012125543c0720a13480031002c400340080851380d84 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 927202023 1250 927200773 927200803
    0x93c0a03080c130803040e0f0f070905060c0c09010306090212030403022407050d0201020301060e2202250f030e0909070b0f070c0f03020913050607080402180a050a0e 73
    0xc00082c1031010381001400901c24090003580f8041d0340d8400e128116881070f00075420036820b01c0200107210134500b8400d0b0300701d80c1c201c410050b11701e040300c401045c000140c042d0360301c10700f8001038424000c00c041010f41c6a80400600b03090307040d6581e10303200d401010480b404034010040b245048a02d060040241c0d811a034024201448007200c03848549a1300c00010050b11400005000a40114808021040030102eaa40006940394141100640345040210489100380700e100902d140d40102401048180500604007507103c0340740e25080140083d5580b1010041c03c51041d5540900c0300f11104954030a0180c1c4032415508142414006511801c41c0e440c82d0f10383c0100320070072500c0182c1000345514140030310814100b0b00c0954134140c18813001e0717100c00000c12985c002441980b800411894110411100d4000465003070307910203480307442c000d2090742442091400902551241742103c1c1714641c0c1d10ac42e1b201da500e091b8481800034001038400400c118a010400807400c0700c0010f0b00440318482c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 927203273 1250 927202023 927202037
    0x3060e070f0b0c0d031107060504030c0501110705030708090a051302041a0306030a0201120605040e01021b010c021c0504051816020705030304050f06070204020408031c060e070503093c0a03 83
    0x203070006a0150881004465210030101f10150104005116442c06180700c4d40c0c1d00d600c0811281003182c2034410310308260880c000d0404c0428000780d000812100000e0f800640303180c41d81149000681c0e40740c50369000580100e242d8484a44801141e4000e01c1551840c40c0810b0703aa203c0030300005140d01007103030b8041e0540d010907041d801540c002d04160102040c00200421712076100c90220b4103866044510000503900411100042c180d406c20743c00c00d642ca004020401c0517500301000750b8403140c00340c209480f03480c440c1c510702429220f13204a401500018107020001e09400062003c0c6107012142d02c0e0050580082c042c40352407010030410111800200110300701801e00c0200004070042032003556100100300602d10050300c550000d400285000c1c4d0186450304c11807000900c10f0020501c2da038003401d1070903000348500712056406503007046141c50800d4480c0e03a441c500c585498041e4140c4941858950fa00400465010742c40400e45480c600000d400d08210703001c116550400c02d10000c02041030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 927204523 1250 927203273 927203293
    0x1812090614031009020d0902040b06070f121101020304120206070915050a0e0406090506130b0907080721270b012106090302064c03060e070f0b0c 64
    0x101102030741e003080043c12419440c80d41c0302461400c83e4092030300080c0c45074482c45040198600f900c2840b004040c252089850034906d6940da00b00340c00043c030f0052890a4070101904440d00c41c400034602d0300c1d000402195641841d05007181051140441ca2005210300000194040e00ca4039142085031000001d1808a041c3c810b4280d9641e000502c0c800100f00c40084a207281da6a0382c0210002820792030000100c9042c04030500c0880001105044402e074104903119600391180301150b0361014540c0380086a03030315281d07000c8a405100e20400c0c0e400841024601841c290580e011050000b050312061803142d0800c034242c1c4441090075400b4003d600d40200411403039408004a89850754003642c07020468000d0303500d000440d00d8011040c2c0059105508010303a41008180700c040c04c41400c1410b00454060a10b026020301c01c0700c00d440c02c005030700b400c4189801c0c0c041000102856000c4d0301840070140c50b0008079621b032030700d114144c00ba10f104803001a00032145011580030102110140c400355030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 927205773 1250 927204523 927204557
    0x28030b0709030215391c0806090c0a030506010c0609060621050304050d080912011406061206100e0a0e04021f1b03021e01020307091715100918120906 66
    0x8444a582c0013403601c04800d0390044050201d03400400c00510071846d1607980b418010400c501c01054980a41410400e0055a81d900c505442e41c40c103040c40c02040766500d40e40101e0f01c2c00e01c007190081c816420040043d0402c00150004c405944c0101001c040011002e49045020282d036000940960001c12041c4180c5c1800241092514003c0b035040c1d00d4950103002003030000c80355040c6981543d40d520707424030103000008405600240c00b22485400d020204103d201144000340001d03108140303040000341d5141c081c9003d8203007040f005049211599030703104032140001049808a201e0950032120700b2446c000300060041d0505e443d503890900079040b0882400d01d05020900368250700c1403561013110801140d0b10b00c02c222014000141e1641449007018100e15090341051130f035800066030300e603a050400038084480c41c8840038109419256894141c1c69403901b41c000301d48607411f08081805410202d184102c040780f0504c01c0300c2c40507070469807c075240e010b280683d0b000540700750100707410f2031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 927207023 1250 927205773 927205837
    0x106060504290f030a0b0d0b0a022d0c0c09040b0402061c2a0c031407030908010e0102120c1801080a020c010903020c01031a28030b0709030215 63
    0x1445916111840b4580d030041c8941141c440600445400000c00640e450180900090361340706480c41070303203518150b0b80d803180601c0003841e4003411036001c03404001080840c2c0403030040d034500660300c2d02e1889581c800a10075070f002410030001e512a0340b8524102d800d0082c201e5201e00c2e007051507111143c035607a003000840c0e13005050441114800f24100c43c12100b0703a20800c02d0001c04801800404294100100341c01030a40120740103101140010002098002c11919080d1001c480007558452007480d01781c40ea42095040407880d07610300200c0801c41e82055000706036080a0130720120550b50780f8418581ca603c40c0c0f0188a0794611000041c0c10154020344215811026003c80582001d610340c607824211082c445090340183d0007564403022950300352003480e0300c0030400030309400320008100214090f0700c0c0e02c100c002003084c0d102d40d8201c1400381c3c910150020b103500c116066858107101c48000c1110059010030b0b881500c2d0051861034000c1d07a03404560007007020120540300e000f407401480a9103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 927208273 1250 927207023 927207059
    0x61707080c15070b010905220308040b1b0706020c121603230a03091509020307030f0804031a06031501140904170a050d0501060306030b0103150b04020313060e0106060504 75
    0x50b80502001d4005110072071028064584007200040d103103460004801880704031003415a80140d110810b0010aa100c01030035805078110003980c405480c0c0101c0646c141c403d05500520945000c44c2c103000308070458008101d0089828104c0310060300440c0310843c0361144000c4501c0f5101e01c0704010340000d02a1010b400c03d00d9120400842c007618902410310180c0c4100400f4000a03034601848040141c03c0288082d007904030801042200c0c0c02d58003081c0c1c1c4010500000d071070020000b03107420412048c40c08071005141d00403606252101940104000d01ca400d80b40903110b07008a009411071440e0a0b9201c178105c3e14080c8500815655100a02c084203402400c161100b0b4580c124500d01c91030000300400610003150f58142da10b0002d000301d030080380c07010707003064040604106081001c0703900d024915042d25003059408101c041c0220408000300140503d0316006070000c820000c00c5407042a03c2c000c5c080c0581401d0000359100b0b1102800c8403098040c05001c43c6d07060200b0f2028480101e0a1540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 927209523 1250 927208273 927208309
    0x5100b031501020a021c0c3f020d0b0f0702032803060b0406120e01180209070e090708041202060106021207060b0406090e0708120a050306010c0213061707080c 70
    0x803001369401052001c00d0290404603140010000700c4104011241c88038020001484c0404424842c02100301c0126a1058029220442144002140004016241d10840d0700800e40d001d01d5445203031030006c914048440b040741841c0d110010380311500100c01ca400781d082d40c3d1742d125034404520704407449100d0400d180100b010b9841002040c0c008070b102c0200046c210680b074072248041a22010802d40759000c103095032590400888681c804000315416440130b80c12108000241e9480c001241d5a54200201d240d0229800f0300b841301341508010f459015a0180c881c805200c031a01106a81c0c540080c454031005a02030f10030000801e020101422034684148000328003031b4020000282501c80c00d80003212026075584290400c17034001c1014000818545001c0d24050790120220101ca0050070701140903c4000000030340305a100b5104030342c020798001d1109a1100346100400000d20540c0510914001c000741d01041c80710300041c10100703c800000090080140c0102072045c0c0040707840140003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 927210773 1250 927209523 927209533
    0x20703030c11090f0613091110050d151502030c0c101715100f0807030b0a0918020f0406050901030609060b0a0b07051b09270d030e0105100b03150102 66
    0x8550f03590038031070902a04018410003903e08040781008101100405408251442d20b00d03020005048401d150494420854040207044044481501c0520420314000300462030420206006403d1355611001d940501242a42c41018a0401d81e0740748180d4907540855406200a81c0d040e1078506850000c1c003d003450003030051b003030407044607000180550303040c04145194a29400300d400d000824108813515442c001650602c0010301030b0108001510940805407241004005600c501c1c02400040007001c0080102c01400c20b01d0a1840703500000480c0f2602c03c00443c17422524182c040c100c1902c000420042e01d0fa4a16a1004001c00042c1401c842d210b454200088280e40c40a5600c00181a0603007201d40d2141603140444c144000d4550310b04441402002003040340d1a4802102c1c0c2c0040540020380c40300d0010b040c1c02c0c041c0c1e0786c00150700d11548034441f0f404800d9035050f000b90300f0b140d014000034170040d1680008211402402d0141c2c100c0145c050000800ba660302400c00840042c1c18010b40b2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 927212023 1250 927210773 927210803
    0x40b04020f1003050402130204152f01050601080609070f052a06010303020d0306060c080d0e01150513050106080621070e010e0a06030302070b180d0507170d020703030c 74
    0x2c0b000300b040e640660100390f07998200300660610b440b0400425100f490218981804d19074042848224402e041c42044604501c0300c0d00001d090704096030340c038188040c241a030541ea400c0d55021b03090403200f4900150040c40840d1044c00c10403180d0f80207400b203441d4800502c141d000215519000880307640c0b50120340d07803211000c104121221000070003a10010344103c4d0705509010389002c8440301d49108161900808104c0e2036400b249101c0c40591002107a0394a207a90300021000c3e0007014803a61003035280c000300004402030310300c10300d00310390083c0c4a0078400c901c019001c04c1140e03c00d2040c0b4001c0340080d000102246001d22030145c050b140c110035000880c0756124010320b00041c54105103450085c01006016070812000559480f2580010901030f00c0d0442e50003d40b910304501c14078403403003004104c14640c20701c0104808200100600304002d00d080905046039202d0346442910009081c91a5060500c00003040166140c3d010b41c000300403403891a58210b03030715100da00007a10340000714441c039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 927213273 1250 927212023 927212029
    0x20708131508010e010e13060608010f140f0a020c071205010c080f1017010b031221100308030a021c060e090a0c091109060f03041e0b040b04020f 64
    0x240419854106440050600302a101502840101c8000c800e0040380c0c1d004000c2c3c3c40d600c040030750550b281d00e900d80e4026201c00c01055040c5008076002440340d410200082400001540000110060440103211080c03141c0c8004001d10419100700710b1002000000480c03550894008010480b400b104583c0459640da00c0410030014901f82100c059454120103d40319500c0382065030045903540740300002d420300700ca1040001c00f843c400c2041d1580e8030800e5520404080d40504030300d00002e02540d20803540f240340c080b002e60115042c4004511180414100ea19040b0a440e100ba250500800402c0307007103455003625900000d1000f5070840c1c0800050080004044d0544510303d5813100c0450118100030380100045001000100190f00ca1000d10012460b10310b03000044070b03813000740010512580001d070140e903c140c82d1f1442e00107100003030001000c6104001540b046000b6141c540f04c5040c01c2d0401a094a014040900746600c190003140c04603491201464110307200030151000e5940c10f00c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 927214523 1250 927213273 927213277
    0x1701060203030a150b0304020f03070f0b0304020a080304230418110f0609010f03020c010905030a050406180302010e1903021e0a080c060304030f0e0307150f170613020708 75
    0x2600140c01c040700344004084507000351260040740c000224440ca007840002c5200e03000c0180007a01c20408070340f42c08026201030140c3c0002e40000038601d1400e0343c8407515111564002e036000c03401070210740710001d40c450b80801524181e807007607610242050000318408a00c0c0a001840d00d40c03040c0c0d112440c05044802c1800582d85900c6400c0c100c02030ac0c140402c00802440f1002414042c032400c010403a071584c1d01030712000100c101402e0040e15410902d0425005251860005009110000c1ca03940c08a40200180084494580c1d540c001c91191911125401d940d9210007030104802c0d50851485142407119070340800c540c4607003200f180d5900d8000030fa01c84550040142c0542c1d40000e64481418000c40c0300001d8a82000200000c180f1000401c18038407000300007400b00070400c00e1400b6001e10401d088a15140000d00f180c410725180e1068019000181075a41c01040100024101c0240540d030303801c064204108403d40265290010703c85050f103800581d450a80d1308000380e0b0001022580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 927215773 1250 927214523 927214529
    0x9013905100f0b040b101b050703080a0810090c120507110d031a0a0e040f02030a150f050106230c071a03072309041d01090f020f04110306060304031701 67
    0x404290800790b041130004945a0400301400f5a6540390603900d45500041d0420f080440e10100d0341d41031245041c0715081c1241500020194440013540910050b8040c2c1d41c240544001501d6100d126510141d41080301c208002c04408984070203c0640d0100d00c03940616446103a5041c40f0300c0b44c0c8082d401c0e0f20708160841402c1e0b80401c1d594104514045403074105801c8000302640d000b07a4003421716468290b021710080c0010590121090342c0c904548007805440400e6038010b4600120741982209000a4403c0d50f04146075181303040000a40e641c882d0485c015014034002c1d4506084004c4a211515540020303090100780c0f00e0080c0006003110095400488044910101d9440b4100310b03200521800c5110211000806000003a0310030341d1f40707201181e03984d060450740000d50905082c000704070b48102130780a6405502e00100d40d42800300305000001914400c0700c200c1101d00068040008031001821208103a01c000c1c0000340d06402d00c2c00c000c0d50018002e00744074a8100c1031604142094509130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 927217023 1250 927215773 927215801
    0xc0503010513031e050d0c03020f0a1d090f0612010e0d020312090304051305060102122109060702101107020d080d0b0a05100e0a0902030c0901390510 66
    0x307151410f142d4044001c1c04064500f83c003000750b10394228002000303801189000d0a0031540c5854100b191402603040394a84a2051491611180280005000c0c003046000010141540c140b1018543c603001181910624a5010554441d12901c0922131001d4000160b074007199603801d214600010100080c00540103180d0041d5035071600c14190100c121006040d030040c1c0d0b8002d20003404190b82d4074004103c56080944001a682d441d140101d10309100e01e0601c2c0c2029000113510040c4054001d40001c1004582660a040c0e0320303040e070295a101e0085620708010780001180301058025600400100e040c24061070b4100400c0740c0001c0d02c0581514030481c0d501d040010700440c9501da038050145480001c881d000460340c9804040b6195546030080d070070070018442c9054034169560307500140035084c00750342192685807150031075105038005880e940c0400c1ca40e00c20100e004040c009034400e00c45983c41d40e480b41c101544080c148075400c1800c11501c0b40a20700c804c400241d01481243c031580000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 927218273 1250 927217023 927217051
    0x6150301120219030b06011404050405160f0903200a081207020114040537080d020111090a091d1507080921030703060f030804090e03031b070c05030105 67
    0x7a00c1040a586007483d030301800101c40000030404541d81d201e803241d01980a0824a1004000c00c1c1081598880c07034001c690721a20f014203115414203100031003404400140c80e400c0f800d07040707040191083d18140c88000c050003d0700c0140702000e01818021103001310040d040061aa0300d41303180d04e080015142107100f0002e8080b400800755030f8410340fa400e240c48840011440c00e070802d03003c03810320252006100152a030901c9945100c49420031a11400041c0b140322000c0941c0f02c0d0852a25098003124600c0150709020b0030108624240007240c0851700b000b8081400300e4600791154000d40480005503105c1d503013038007a006c4c0301041480801c071901e0f80400c0c401054903100c04027600081026210078250703170090081c600310b40054074990794000003420f5143e8403a503500f039044020b401d0329001288020400d600c000b08001d12203000c2c0c002d6615201040c80062440301d00340380c0c1c0c0c1c001144e200003d008400036007001d040f02c180040c8101d6001d4220100c40c02d0b11f80020a00b96602500c0d020790515134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 927219523 1250 927218273 927218309
    0x1002160311180403082a0a0917010c090e0601020c130603060c171503071721070309120c0909050d030f1b1809061e0f1a0306150301 58
    0x1c0300e0440742202403001010041c900345604c00a110004c01004a840080c0e10380410300c3d03c02800c216040ca00d40c06040080c0c1e50000242e00800c80c10b034610548206e000e01c62000c20380044180100c2d5800451645c800300a03601d002001174110f840a00b045040d4059011259588d450780c02e12018100c146482c0400d4030351a5183c80c0e8210b07000c0b002080c1c05c2241b64009070001c07141044509030022981040b0f180300c3c00c81880001d04260a580c005824580004403503c0e207103078085174031040342c0e008030040e041c152200e06080e00e5600c290a0000c000800d00241400340c110104998800c8501030f802c000c40b215102c1940b8003c031915010150340d01d6001035148203550760705000344404000c1c0200c0a0100b0719000d461814182c2180c90204140301001c1d00051500003648040303070042a031050140300e165074840c82e4035814400900803140b081001840400c00106070036402045603c40c00054104c40d0340c851707114440d80c10280c1090340c00b0707104426101004480e0070240d8044c2100c144100301c1e50603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 927220773 1250 927219523 927219529
    0x15080a062f181008180715270501020304061b02040f06090b0411030a23180f07080303012c0106032c10050402030a0b10090501090506030a021002160311 67
    0xa00d40c2c045845591156080000b02e50711804042d00803441d44560708080d41c002840342c2c00e048050700b003501c61a0340c0160250f00c0c25480000d4101003a048403442110f55490010b0141c1089540103c03400359004000c00c010340c6125581d202c0c084010320081581c0c0c03501c141d00250603110400041c0721129201c0d2000e111080c000c1c4036080e0f80c420b04890400c00c4e85a4030310302042600004100050b065618000e00c0d01c0c080b1011a0003400a14071001d8920724601f05011941004c54913403001001d1141003c110340445c1c1c0002c00c00c003680c211000030b608603843c205100b0001e028081622844001d004e04051005030b800c81302a0203410151004290b1295940340b202c03000000540300c040403803e041c0700d0203420902003460a40703200307a020003280560366400460f20708600014000d0000b0030407400c02ca014200741d5103480070703a00c842005105030707640c88240780c0c00c2e80c4080e100d460b8180c001410010040c47e042081d104070040314015640004826020b0700200902948242e42222440341110990b20b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 927222023 1250 927220773 927220807
    0xf05060a0b04080d1803050609011d06190f02070b0906010e070503040b04062705010e120403020a15260403080a05071e140f040503010b0a030b0f0406020d02030c070615080a062f 78
    0x82c6414020045480d10403032000c0d6043700d58290400c1283e0320240810000b501e50100ca0300360782c11925201890500c00c21450ba9000248aa010348030520000310340c40398460411280610b070061786180d8241c0b40c50311880000e01100182180c541841080c40d5804510b0318480d4101c580202d00026601c005043c006080904007085042d8400c0d00308404e00047e510062000240c0d90010403a0003481030824050310a00741940101046041241d01214103604010219125034840e98841c0c0d0780c1e448500340c1c082501d00a9980c480450b00754400c0040008101900c2c1c1d15031038040c07600503d0000d04040c102d0301907024074101c45058000050a00003800c09009040346250180c8204a0803890340d102d01501d013070081c2030354401064403400704040c131285406592401140a00c11940c03030410384e1040e40c49900c545402c84010f0b0400001a01e03000310002d00b9803c80301200094040d82c050781e60352100070001d500c442617003000149000c62001c486101e0f40c200307810800007050b0752411200c4a0410381 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 927223273 1250 927222023 927222071
    0x6020d0c020706020a140f0a0b1b120103060b030c0406120506010807031e060e070605031801090506060d08190e01020f031303020609060d0f05060a0b04080d180305060901 75
    0x903502c015410094540e0003d54003082c1c98100303902c540403282c15200300d41802c0c0080040d020a1141ca1060400c1c00030300020079001e14440c100e620504001042103584038060000c0e2400b0808900c40104081412038009601030900182a01c0c02c12603000000340446e803254210758030204010030388000b00b040402506002d0007083c0d000305142e91956071034010039a0b04e0202ca00c0e8040b000001e41080040581081803049047d6041e14040780d203a0100420700d0b0030031550454841407414065650a1040c07183d07454031a0003601512280d5200360522050b014501c800300d0301c6800411072404400403084489130058540e0346d688858280c050002490300300900368400304da801c2080f001c0980c85101070440c0032a42e0607501035440c1c000100c0042c0c994092002d200320018100900060076210039407000d4030401c2c08481d00300985844801c0785101d0701a03070040c0040c40c0d000f0064404041d003c0e0200d980d40c1d081208400c21801e80369614141480420380e070301d98240e912110400c440d0081900032403a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 927224523 1250 927223273 927223277
    0x2f100e030313020f18091c030209090402010e06120a0f141513060b0c06182103090f1c030c030507050a080a15080a05010e0102070215030601031806020d0c 68
    0x8608000e8412102c218070000002d110386415045113521340c880b07241c1031340d0f540c07400015140c1c68a00301e0035a580b10384186191000031041500b007109058040d109594a4981c00f8000ca0f4059945030300546502c2683c0306032550044052003907504060588031020300c80c000c80e40700810800030f010b4441c130030385040d85e03100046441001d003080a10301201002401d940301c02c680111201039074000000041c100ca400142e050600003030858021040043c68038020460300504417248800c0500c8161680d1b00084040543d4011071100f06d85c02400da0060b641189402c42507404105d14880f02134907284141d000301c40d0102c4210425100305405100390300c1c0032821030405201a16258a0040c5030b0300c503050901041c01034180c0800c070070780741c4c1d5840f068042500742640841d040d03da8411a0b910010304408450940c00c01d80c9103441480103000b0340c0e80c0158044e10056031403100c0f44400e905a000144000c1c1003581d03842c0382c4000341001003001001c4134040c076401a940c800000f003400a60f0044016901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 927225773 1250 927224523 927224527
    0x5070e06041107030305060607120c0b01090c02031206120a0516050402040608010506130f14090c1602010c14070605030a0f0603021e0f0a060521162f100e03 69
    0x161100000080f00d083c5541031400050079034078040082c046000e081000b800410811045402954001c04d5042e42c5e540109009011070fa80c034229601a94003850b80640141c00038042e02503035034002607205800c8a401842d072180180010422031914400400035a8a503108511074115031504500d43c0c00542003d446c158680707410030340e0103020010f041c0b042c0c0d40038540c00039203c50f03020b160b0910400a05401300c08407090b140c0d54178117140409091103181d8801d600c01c5001c9504106004203c074880a8000000007080d0072980054550310502c0078103540c1984054183c4560000030310103940a401c49440d40d03038680c1440043c04080300d200c4034003070360a00e207862400d00140c0c0c2d1342485843c2c003900032910300a400e040342c004941720b40c03280d1341d50b2504980c3e09d5001150941e04400601903c400c0c01d241320340b08400c49804c0c840e4820b4152504150f072008080040700f5244a5044e00c01400701c00005490340c41790183c429025821104960b40ba40d40107490320302b0310f03070031180500001d14080c540158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 927227023 1250 927225773 927225791
    0x3050f01080d14180d240e0703031404090e01021305010503070e1e0402160506131a10080f011e0c080c03060d05101413081b0c0d05070e0604 62
    0xe040c02c1005002031850b14030100c4c04080440c80600300f01c0c00351401800300c03070740c0d62010302d465510000900003c1e0214500090070f41c140119910400c6002003c2030020302506183d0b40b070944101980200c06600014200400300702a061409004402c80301c41c000140d45036000300c0c0703100b02c08a036900090b04000040003406a09640070034101c0c0742d200219503001c003080160002c0500348111000c2c480d0464000b10701c14000f5003017210182e110703c0c0500140e81c11540c40402c3c505800034540001005a409041510f14040c1d1ba07422b003a511800003800d41c400d03a9100c8481501d000400c02c50440d00340e45646840382c440202860303080350740d507a40c60203000c940000c02000e40005401030120a802d8000f0000840d2039499241d0200c0f003542000a44000340e024401c0c0102402809407403038021150318000c501503aa091900309650390f004000c0608082c148403401c00301801d04102ca00f124804d050b650f6810380d58810f20640348500c6007008007441da250040003240017900403d0785216034070701981d070307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 927228273 1250 927227023 927227027
    0xd0207031a07021c0e04060f0906120b040609020102030d0e0c0a0611030403020f040605040203070903060b0d080904150b0a0909050606041d0403050d1a18190e190303050f01080d 78
    0x313100d55401340c0003036000e4000c100b040fa00c2500c1c29258551140c100f02c400107281c820003021070f050300d00300081413014940f100240e141e0161584402402c0c006503400060100308598051694a072051040d28500010b4211001c10b55860000c000280c2c2c02030300c04000503150172600c0200822403400c02d01d44055229880e66128040c6101c00b90084d80c2ca07106800107603445a0101d07001d010300078803c540b03034106140c0080107410103010856113540780c40180350680c40c1c0032407550f1006900203100c4e40340c003030a4414440034000072244004400d50040002c5100d540f0500500110403a682e1286462480c0c0b0095106460b40500340718040d0008020501520341c2c1d80d090740c0c580c0d07460940e5a034096100c41c41d040380c00788075803016810107502e000400c003403101d03010f6000e28030510700311030700c17182c0d240203560070812458150341414a030301c0800c11100c503481041c6c0114540c94901020b07030381030b441507448840c1810031018084000940d168100028000d0f081c50140c0900680402092001444000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 927229523 1250 927228273 927228283
    0x1030c05100906231308011b02030408031b0f100e070e15060f0408030f040504050105180a0f022b050108030a0c03050313050a050c0901090218210d0207031a0702 71
    0x544040c684d1081e1041040c0c6114400b103410540100c00c040708403d558030505402000c110080e10408999003041c070004a00c000241c4081d122580701a62410f081003025800883c80d0b0820300704103000d9281c0600c1d84079410b01c444444444980004941c03c1417400c0136a0519409403c030350302090100051002c030400100c2026a814010758100d41d40e8003030b0000250302801550300042c120b10002030304560f101031300c41c0508202d9800361001e00460741c940081100ca464000d000505c0785400b01c0c000b4607030f0003080c4c1100f82500f0420400618043e101c1180c8030300d2000b03801c0d074102021120002c0040c880d400d889164010030804001e10b04040072294001d09a8000b000064100040403001c00c400301141b00e0302c20640c90b400022201c0b21100d03460140c0d110540c95040c544603a101000024441d0907600840d03400d000d41101d04001007008004204d02d56124003986c080c102c41080715402002d40c10054415450401e40040c2692480d44c540290011802154101840c502205210000d41c000070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 927230773 1250 927229523 927229547
    0x4020a05031b04050307060f03050f0c070312020405031204080d02030a05070f0201030b09010312030c111504110d0b0414030f04050f033c030a0905010804150501030c05100906 77
    0x26002c00c04030742d00c0c054151a0700480e0865507150144a0b0b0009265800c51a00340b280b42042d04c0610a0ba560000b801503140302c222841c1c18108400c004180c00030348101c02008140c0e00e1403100504041d00c036000300e440c00c1d80140221004030000182030000f24010002248020290b1000f10302d40075510304010b000d0302490000900804912020034216030103500701e001c41c1c0e000588021460360356800d042e0740000700342d4811800b10b864001c040180f144503402c00c120b680c100000802c00c03610010b20103000407c004000b521901001c40000600b40d5a40c018101c1b8a401f4800811090034203080210090001c1c000555a581c010480f2440307003c51041074408407001181d0707010f03e95041202007402c0400044c2c070072a0b01c840c520305a6004041c3c4101e000c01e0081504035510f04003c03c00040e5a40744110200c49010031800c00080115611810b00c4950007407103410405090541c00ea1403105840c000c0e0070480300640c5044007130240d030030010040c0e0b03070300021898000601c601d40b40c2c0150460702c10413 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 927232023 1250 927230773 927230791
    0x170a1b0c080d030504150605090c0d140403051201061b0b0408210a0b010507080d020a0210060902030114010c0c05120f15010e0702030c1005100506031306050604020a0503 75
    0x444501848a408001001404600d0940381140350b00c81006000f0001150101c4443e40110f900d0305025030b45208103000c1d0f81000c0c0001c480c40c2c031920580409900400c000790044e5841c1c0300320580c545901000c10340110700c00d496890b100c00186841c09084001600840c0c01c201e140f0a1012444032800c0c00200f01c1d80e0007c40181c003a45443c20401054410b049200141c1c413110f5814003c80c420100040d8440c09002d041003003805900b2004459612507050301030b140c100c0c00d00550084644950091070880b03090300442c2c030350411800a0f0307800c0c1c9070740d54003280031198040f00401c00003a4011104c240a0024a031509201210342e545090019250107028042c0135185c800010040c01040200d00f212081d00c100c0358400d14403907070380d20032403070034003800b042c1ca105080822030060001003130315107103510003000e882404142c00c100002800010407a406180c06864002016140c10000358040e00101c240c0c6d64400c102814181d09480e0050301c0349020b984108840d8030403a6104050700d0b0061008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 927233273 1250 927232023 927232067
    0x11403090a021512191a0303030408031e010e0405010c092904170a020f100c030e0a1206020306100e03030706020306061324030c0c0b060a0f0909170a 66
    0x10200808070b5000b400c1d0f404c0b040c0ba00c00341c10300c12a00c1c449441c02e5106001102c091110b0320b21003c006407410500744600760180d01c10b0020400081a20000d176900a0f403448102061104030760640c05041400c1c0c4c0300c0000d04000400340710a000c1d080c0160400e40f0506e0504282c0c441c90000160110702038042510140310300c003120602c0c445001d008650042c407004030030841444100f031006e51543c0741e10408900c1410b00160002d0300d4203200d98071020028035520b6036000102142c5040c1c803690710411900f80d200d640b00c0d0340454943d0001c480802c0072400f0b414016101e28107902803000c0a50054054018440718240c004e19071380d000000ca840b8a58001070160b180e885079000f08903207014140785040031134540c0e4800f02c1d84010301ca0380c440300340002000e40e85208200b003401b41d00300d50703d001c0880000364032034600e480410704d4261901d4006101800340441035944400344d01c0e60a1254110440e981e80340d08031a424400411171064011500854417407404490300005841d0000c40c0c1800800d40080f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 927234523 1250 927233273 927233299
    0x3061e05042f0a2c0109020406020609011103040807030903080313201003020a020c040f290a050d02120109200901150c021c030c1406060f120109061802011403090a02 73
    0x140142000104c81e11115030095503155600c00010b504103005100062054800140345120b0500440690040701d81d40e081c40c54983c6e460750202507000329000e400340208003600200040381e0000441c4180c107120465006034005d8540110a8041c0402500b01d070b804000d403000007551548211180c8094606005030348402c3c81409a0404c60003210807a401071400001324800c800075080b08d000207040244081c1c08100c07044808841c06d40f0310b80795682001710303808240140d06005c540308100324001441078422a06a000050a58101d01c1c4101c9840c80300482251519202d41d00d07405e0040c100b240e0726849581400100104069030740441d03001c1000b04c01000c400d41d00d8542e1164640c2c2c98002d2805412151810041c050f8012207900700d50341d0190f08824100b0324004a44140149001012065078100c01070421280070740d00703031541c2415540d81d0300060010314144a041c0420041c400c0d20f1050440f58000504141d04405421403806020070822010000c04141d1910140e81190f00f01d43e480c00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 927235773 1250 927234523 927234569
    0x1b0905090607080a142a0403081e041e05030106060c0816030e12070e010b04050906040f0609090f060b010201050f0121080a05031b0405010903061e05042f0a 69
    0x1d10002a503a03040702170901440c1c400c0308403509502d00440844909a0051444ca04406d204510014001203800e011410180c40d072222400c1c0302180c1c0300d40c0103041c96110360b11108030742d00b00f683c84e6603c084408420451800d00727000360300042401303080c407000024558440c0c420a205422a115a03000140c01080c10140900c200d214a000042d0001c05150a041402c2d60f460303100f405240c44403000c0800015048010b14200c4d0701b40c6030302801d01007a54541c0320034800540412486514100c0c0c071b51402103403800443c4585200340d4060f12401600001508110084803a079580507411a4145400c0080c0c068500210364116185071492606040034a000b5680e0519007400c0148506000114a0fa10307544c0000558001c0982e9015500460a00311203151984624031829020850740c402c200081020750f40604040701c0115010220000044c3e15101260380403903049400e03503041c80b00b40340301e40045040e515212000181350600041d40c0d0b00061321015151040080f503203485204100c0d514 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 927237023 1250 927235773 927235781
    0x6030307050d080103030206130305073005041d04050a1709060d0617010e0c01180b04030b010303110604050c120a0b073605010c080f071b0905090607080a 68
    0xd904101a541680c00050700100203c0c000e110683c0148518400708581d07402c101c0200640d540d050700c5091615540e980c898004c02c0581040c58005110740c84c0d500c042800950040502400940e5a02e6455060002424200341078901090444039884c1c20400055000980c01d11460b07000000200590290350b280a00d51140548240d0031000102d010400e0120304c0e08048143c2d5036000c410544c0c668a111503500300c82d401400ea03100fa500020303034504d00754010740501d1200c48194200100058407802601da00b50f02c07960046842c0980c8000400c103140d80004e00f1003080c91058081c200f1401c040e160f941e610065a134495114038041e071044070700c80c20100000484981c1c441c02c860f51358640500c018220382800c41c40d400e40c105500081031040c3c8050645041d001d5003459030603d0b4141040011a03510744001c50849135040d0400841d0b5000420384058043d50344150480c40e4075200d81d10001c503620b00e4a500c4014403500702020f014140d607022840e0b90f0300004a141c8101c490b5151070800300a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 927238273 1250 927237023 927237037
    0x5011d060604091a010f210b060c1209010905030d050f0313141b06070218060d0507120302011a220b04060801050a0513030804080c1203190510050a030b060303 70
    0x1585400003040e809400c50344c01c41c085041c2601d800d0784920929009883c50f411118001048a55068141005245580c80000301e600c0240000b8188600114001d103003440f60600171044210100b60744030150f900036072180180c1005d401905441c030144401a009010b542c4900200700790100004074800220324924525a8120140700f4130041a10003150316100301e40d149a01c41c0708511110501c50516804039400154040c000305030620901072003104c03500000c2c00c441d074062000361942340172510030424034000e440040c002100d0071a091a02900b1111042043c00215100e41d410403400d9651144c4a040312841440b60080c42100c0114140280956030f42c0551043c038020001c42c40c41da055001d14840c0d4204002045540ca41034409118078811500050014100038009800035011700064041e070440001100c9440c1c3d01100c0c080915001260740d85074140700c42505100799011401031035080201c06e6040090b82c1c0c02c00010440300304040c003014001165034004554542c404104807510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 927239523 1250 927238273 927238289
    0xd0c0206041413020f0904150803090603040f060207030810120c150c120e042a05181f02061821250b0109020307020604020d030314090303010f060305011d060604 71
    0x590210703000350103e980c0181c90054080d52500302381700101d04981555000b622202c400950030a03030004100325041d0710013001114040c844c65030400024100e4006408400e100e40c0310702010f07142220b66514004142d41c41840c0340e4180c190b402d000720340042c0b108816642c14245481d51088090000d030380d482d07118080180412041c4922088040d8469a0f07005207507000c032000d1040d582541c0c940003051a046515008001140700030110143c05030000301440320000c91107070341c0112801c0000b07601c98400c07803224000f80604d640c04102158188441c9501204925500b9420185101c402c1d660310190000b44200c0c22054020a06000645003610310710f0911070a1036660b4038090a5245180b03c510741c0c1125840c0d156000030038100e045000b40c03442540e2950091803556a207400304103498800309425400c4c0765407a890100b0300612412460320403501c04000303554035454502c80f4040411241d200c2010580750600612212049040c081d000c11030410b10049603407503500c00079805101d1580000b0f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 927240773 1250 927239523 927239527
    0x9020f091005030f031809040c03051006181a0f01110f0d030b09040302060f130b070f020f07121511190915080a1505040e0f0d0c020604141302 63
    0xc6842030003003400003642c005400341c1e0402a44106403507900e0140c00c000b109005080092a50b2a06290100507402405115081501c0da0740340c039440c4c142145451048074540d01d400b402d12904a6a540120a1f621100e10401843d4a285201a042d4035440d40040c411101a4070480d050ba124026520302d803003c1c60280d5464051304441e1640c4c0704440c128100c04070303013843d03001007951901c180d83c1c07803141e601a00a8040c42c1d5441c010350026440c0102240c5003032041d0803070b0034041042c019846220715039607110002056a041006840c0c00c581c0c0c00003150962004030140030105100344000303402984904001c05000c00001020701174060101d0701c0c3d1000101044100c10b02101800307440c009400c1c8e4032012240354903481c10200c0c41502c080e03060f01003280800403d41039800c55202c80c1311610b524071100c10781c3d03844200203001e84030080301e481c4817503100540b101d5040300e05210700304e40700a02d81014400503000703902040c6d080c082c40c071490001001100c41c0030141d031180b92002d40c10007840da40845d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 927242023 1250 927240773 927240781
    0x816060e1c081c2f0301090902040f11091509060708030a06030f050a0b09061014010e0603192703050304030e15070614040c1a2223010e0409020f09 65
    0x740050940d13410204035034160f03a007288682250b400880740c10860180c100781c41c6a090010390000f40800e90303001c84e003040c0d451380200d80391082d07845801a2115000d032103e036107450507000c0143c140c1c0d44080404a0354010440701c4140e0b0f4882c0210391003107a200a1141d01c039542e00d5a9080144403035440036003001103203032280c2c0810402090582880c0d1183c0030829440d110078000c140d8a1030212004401208082c00900130640d101508000c40e4005241480100e269400401c0d60b6070004c3d104008480d003204034551044241d0f0003002c42010364020410300d200080001040740d241c82140c0503050103000008130707061500c1184440508800504000c4e1048083c1a8030b14107039000c80b0381500d4243c94454600c80b100240811347c1c3c062600300c0b03120a0b90700c5c140043c0051080300c140b41154095020864565806d40415202881d00801c2071a06941c40c80c1c0500103650032050300c2030320b00c08410703802d4540c3c0c90303a08040241e802c081c003910000b91640705840490f09801107115403640c0711121200308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 927243273 1250 927242023 927242077
    0x609020d030e100c03210906060b25050a111507030215130213020f1b0c01020705060a050f0307030b18070f020a230c06040816060e1c08 60
    0x840c80c0c242c0780080c900c40d00200c2204c10030000040100051301408001106803517580202e02ca105999400103400d4409680b80011102164000020b068000c519003140d070f4080c150102940301c0c138159000358501d0075500c160302d1781c0900c403004140c19100c5541c1111034659203c0c94106141d0f148240c0c5c2e8072241e41c28083d5680d00311802c07140c0072080810024080050512456032090350180c0b82105001c5600303178950280d04180007680c0d500c0c0e01485002c103100e0007800c001c0d100c6411071024003411643d02c0002410720b480c68015501994017002491403840d40b14003120183c00c40a1a81922601e4544080700034001c3c0c42e99056004c042b40f01040c20403501c511542d402210980c4440301c08854075041030361101d8030884080c0031035114005045e007038002503100321040400d1000391100450188002401900a500401a26400000c2ca540100b52a1302c1c800302401d09070170144450562840099016070040c216001175050035003106013000785090a0740d50741340000c460700243e45822180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 927244523 1250 927243273 927243287
    0x92d0304081b0a1410080c090d15050f10032006040b03250e0609120a05030304060e0304050d020111070509150102100e031b0f031308060a0b09130609020d03 69
    0x5a620800b210070b00020913115103690590400b00103001d1049542c402c0d00c0035500044000c140c100580c3c800c0202443c1540c80f07452031000703c2e12440030754401c1c2596010481c120b81c0010100000d5500d00802c0c0500800100d4030b42c0c003140d62052041405807030745500c8540d2080035030403d64000320040341c04248034440c0000786119404007060041407a8074560407208010302d100001021400f40020301c50203052400c01080a04005001003105a40500c840d40c0303001c4140c8800d40e01030b0004010302c81002a2406410401aa003800a50a0a08050025030000407003407009050120000c01c40c0640e1209120400c0141401001c4295914080740000403503075180c1c90403801801000d04514a103101c1d485001c80c4460900001c42c100031035000124043d4680b62807520b01031003014902d09002404000900b50541c12031100300b605446e0090a070718001010b0001c0c14158101900d4040366128555116800103c80c00100c2d400b00c170343d0030700350000d212901010790802645c81c900c03418160400d42c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 927245773 1250 927244523 927244573
    0x151a0910320108040b19110d140709030b06010804031e020c0f041a10110f01020909090f0607050d0617011418030304080717030709050108092d030408 66
    0x200c03403025040c500115a02d401c11100180381c911102d011400842c0410400506c402c582c210000700850701d1418045550000040c0010154407030644010b14600322071070641180c01c43c00e250801c24115910b501000700010030035810441448001070034140318402542d1092065100d124203924402c00003500c58058040e03541c080e201e40a81c012103403c0c184287c20a00440310400b03218511800c3c204100c09800f10301d118200020030300701c03202080c000e10404500c80d0015000581d240088401c0c01030007640140980100c0e08011440c5075a1000400e100382c1c00051840e1041d40c0300007911045000f409541c01c10003032080c40c160981c0c001d040560040600951030400100e00e580e4000d28442038002690b03100c0b07103d0300300303001003400500500060103510344144041c4241c2070300405002141d81080707803450b00207007543e20700700840c0d6000705207590420140320280440c0785d6503810b000e00e140000d40c1004804455617490141c20b010a00c140c401400e41c0b24103581601101c0c4403140d40d0381e01080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 927247023 1250 927245773 927245849
    0x6150a091404032319051c0603020301060905060d03030b011b030203120112030c2006070f030908010506011b1401050c0a020106090b010f0507141207151a0910 70
    0x81c3d0f41315007000008110103108030212180500d07103804911900c0981002d0800f90051000600c40000c0a14403c0300c9507842905006000441c2865801098291440c3e50700605200e850001802400d4075411a1003602a40508002c10003810b5400103d4000001c40c00c4918400d40c908511810180e01000609000390043e0b8200640e0b6205c012a00f1003c29250008002c9007844e445007000800140201007080b0700d402400d0416404c0750042407596100c0b401c01c1302c2a501c4040356804240d007204101e00900a401c000700241e107800700020f002c070754121082800240754101600c04006c10020b04003e6200401e0090140381020401ca1140f078010345443c0d009542003d1010a0018040c401c0000e0400e0507516511200e1190005403015880300806959003100e20128070120602001203800d01c00c00e0f4070380c00b071752440305080100703003241442101407000d401c20b0703101c03450043ca800d800d40214030100c0b1041c01d95140d00300115550542c41c2c0c030003201102039850403034070b141500e41a1016001c01d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 927248273 1250 927247023 927247037
    0x1009050906130c0f18050604031214280906120209031f020a260a020d0e0a05060a0c0801030b0601110a0f0309060e18010b0d0605060c06060f060a0206150a09140403 72
    0x307402c07580d04102c0740200c1f40c10400c10712081003c00e8013a81450072404d09404d10a0101404600c000100e5104d00101c4a12071040b64202c841d034503480010340c0102c81c0600e4a01c00003418164002c150040c050740303941923613402180000131940c00340071420a0681080015201e0b980100c200d5000e900410345810100310360f02402c00029008001c001882a1190307400c1c003247c0e0f90b00c05800001c0d0401944190440c0d5129100b40c0385100401060b642c25000710000c10307091502e0000103007940c60103006001004554001000000e094500c06500000e090800c0395a071180702c0c0e203c03468900310400c090480740c85101030805254000b071102013a210556619040c001190052112440481c00c01101c0c0c1d542c00001044400c00c080040e21640501403004500927540310001103154029421444c216000705080c45110f1a05002c01d176080c49007501e00d107050080700130000e5100c000c02011100c0040c5810041002503a8581c9644064030640ca400c000148a02c0140d0826500895084002c1040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 927249523 1250 927248273 927248297
    0x3150901050d050a0f17070c0311030a020a120501092907030b06090f03120a020f1618020a0903060203040807051006081e0f06010e10051009050906130c0f 68
    0x1184100004168200c40101400411541e441c04d0f00c0003903610644841c5000f4290203200f1b03d88074010f155060044031181886419030405854800320715003814440c2c2d012036068401611112815812140d400d8500660032440d030518a014018080300146208103814080d035a40041a07038005c0f42e5903096045000c00d6030f4110069080342c0c6160300744e5600c104144203101e861b03d0152403450070f801c005029104100d48840d01c128407a080b5040c0100540c100300c1d107580080d08200404142144031081c03181146103480700e400d804032a40358000d82c4260300051000319040c001c2d0164401164489000c41d0b492030681400c0c54540c008036000c80b203501540f0340b100425011400b8240c1a00c0d40003026048400c2100940400404000307006010340c01088540650384005212a500030031100101210f6450603103428840e4103480c1d0045841100d821b1444480340d603101400806603842610840441d455000020301502d00301034040c00d40f54142140a981240e001c25240c440c1c030060b48403038441e041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 927250773 1250 927249523 927249529
    0x1e0a06023a0b04151e1a12091203040b0703020412030804061406151b06040b16021203060f01030b0d051f0b0f09180109110a090b030d030e010605060315090105 70
    0x1030008400c43c08882c40c070280260b0a248900340401045c00015507191541e035907114241140c2e0f840342c0790190501191080b000c0d0501510390f5800360310720019202801c5114095080e500001d000608a07212410002d050355000381e048501911420101c000f03a00058607008146400481e41142ea107410b084101001030808a10203015800040014040c4c091f10032468a084c0c00c460308810802106686020100380c1c203100c01b074050b0b800743d015100d0300c0c500019181400716100184004540c410044400d94032001025690041000c8802880c49400c4500480190080905060f07005000d903e5890402c4000980212048000d04030b4248401501d80e02e1003c48510703030b001c00d0f04998041010003061501400803580013041c59405070822000c8081142111641c0100f02e5001b08502211516850910501001440015000d000d5454904042900c1c0c150407201c41c000d140d1102c070f402c00059420340200c0082c0101a0000d5140c0c038203514101103407040304044ca4042e046030000490641 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 927252023 1250 927250773 927250781
    0x60106140a0e01080a0204210201110d0516020f060a0f030501060c020306131703131506120b0403030f1a040c03022a07030f060b01021e0a06023a0b04 66
    0x4603203841c2e68010004080055400020040c11070944941c01c00004c01c0c100107000703c103c003030003610361032018a8106100140008848012991841d030241c280900440c0d4028111854450404140404c001b0144041038050826a65499202002240c90102c0e01c4c1d004840344285603c0782d5082c001d50f60307030710b1094407401c1d05c1d0314010303401d0f13001000010940358a403020301000b40d2007103100c012441109045244641c02c107887e4801101c041e11442410300480c241904141603089400304000e52600c03140407e80008020700514070600c0d80c0025061602a030301100300c4081300d06051042c01c000030180300483c8003158a491145250002a065071032091094a0025000d1081e0806801c4010160150800b440f00040c2842c8111074011000400c40705d002000d50780f00d1280401c01c2c06050340003a0030070740300000d07194bc07003020703c11390a81d8950005424000160010001603031384515142200804a202c0c05a0030965600040d001540d500b0403900111241031103405c01518560000f00300170b071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 927253273 1250 927252023 927252037
    0x41b02061506130e0c13060216140609090406090c08070f08070b0a1b1b09140f1b120c09131521060f0605030c01110604110307080f06010614 62
    0x1858240f0000e100419284503200c0d000b1125040742e41c2071041090308003030500810b402400042c3c021050150401c0031640d2580c014048410040b15550b018030041800c5000e80101c0f5841011140041000d0001075407000c656244c0000a0482c8180c031011010b030740b00344912400c4812003006000240c075090200709201628120307241c440c50f1196450080b00c801d00c1110b05c841090704054440000180c3c040c0e60801020500c8885003113840c5004070301021a0740a80c0c5001800d4003000401c0301d02e007034003440c0c41c0d8880340303180404049214441c11004140a82090000034010020510201e18001005480b491104889103281216070142103070a0710160028104241011041800703045c0d8140301040402c0b03d9444120341c3c162542d00d44c2c0c801d803411081c031140d040d5905c010900203400c003070100c0c005291003801c0000c80a07900881441e1740f100020000b6044c03401c410140e24a0b9a41400020010b01d1104100c1d64001304000445072138188c2032203248040b8031651100d6440381c08405c15a07081c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 927254523 1250 927253273 927253297
    0x6021c09061d12180a0e01150f02030901090303080c0c030309060402030d1e0c031707121b080c0309070f030506100e1608041b03080904061a18041b02061506 69
    0x41c04400c00e00300340d000300b84d11a80c81e03000c00c00c400c002c40c0c00001c40707030b12600030070000c000303440042082c4a0292108411400c034100f150010407030104240d8000c2400d40480c4e42c1480c0800c2e03036039503061021026002c0c0101030041400700100340300c3c038804009000c2e401580214242c90f0300100100d07080c0c4e081082c540c1819210300f10301e03890600640c001c80f07c0132030550107410039008440310f1100d40c0300c03481001c41d50500032801e03140c2803040f0f1008074400c03038450384200b040c00f03035203060036450151514800900602c00c80d680000000c1112005100000081c01c0b000c90703000540303440f894030a80f107070b004407007121150800c0f0600040c40660760f811070b070244810280c02079410301040021a4041c9000304155985d14412081500712003081c0041c0c4011802216080e072501c10f000304200aa60031680120200111a0f0390030003289107400c2128802503445525080429258021234042d100d030244200c4002014003503890703966004101c0c207116a0f070026040c1841c412441c2000440d020704100511 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 927255773 1250 927254523 927254527
    0x9030406030510030b04110a050d06152c0703140403020a030905040c02030d020702030106030611030a0e01050103020a0504050403020c120f07290c1606050d0b1503070302090a1a04240c06021c09061d12 88
    0x42100937140509402040324500814000104440c0082c00181500c04a005921548011043c50760060b070000107400111000d01403485000030080d500d000302070302030030201d500090307603411580c0940c003540095610140500c001d480305540c50100f5001201c0041c080703820030640b40861070043c132401d810b03039a008013034880d882e0400050000034200200102c0951041c4500604c841e07840484401c010245400105100c0c124100c040342031443d5a0701c41640c100b88a500c04000c0d40000b00401500e5100c10845926400c0d4046c109250241c030341d543c44490074240d040807907040d078001d0040c4940b103601502805840f60110505c945912010640c2002c0302c03003403021030307ca603200781c00400b092000200f081c1b28094850001038201c0d054001e1020141c1000a801c01003010850b1744911103108a0320920102e81241502800c01c0301c1c0c45c0740c020602c55000581c40b460b04040071100301c1c0c00f160b890703081016400b5484d244000b400c0200c141000200b401000c0912070f0000120300303605224440e4814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 927257023 1250 927255773 927255839
    0x50622050d0e1005120a051905190b030c090f04080f1305041112040206130504060803030f06090702070612020c060a1d0c011e0306050909030406030510030b04110a050d0615 76
    0x20a805030908c008040300d6405020201450b0141c0750042606a0f4000000301c02103001500f183c1c0c1e4000303c28000e070801c0c100301e031082c0d850303070310580d0700c9801d010100c002d90707031945041c6125118824802c1d0181401244608103200d00d0f0402c0c10070b4030340039142000000f000002c0200c0394021044a040c84d0500400003400501b8108050303e03040b007120403000640c5445400003020fa0703c2c1c58100c52442d0b4004010025080c401001d0360750800740c00c2d0781e4030308a4207040c00002c0d01c608540c0540c0d028880d82000d2a99450040d83c126039810710340c0c0060300e18900340b04511201a180d080000001c4e02c11110300a202884089500d100140381611164800d80541e034940703c1410284034400d0070702d683e6007400580c179115041c205200b5614940650303030303840c2000c0c0302404652014003c40c0c0c0c03844001c0c0f400d01c000745a003260643c0240c0c00400007001c007884180002c201d001c042c1c11860b00700480b1800c04081001ea1303002044015010041e45c048a603d5004010401d5400d16040300a084003100306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 927258273 1250 927257023 927257041
    0x20c0f01060e131101030c051b060619050102030a0503042f040e030a0f120f02030f0108070806010b070b10080304060908011802010207030f051504080322050622050d0e100512 77
    0xf20907001d0103407e012782012007229880326a25403c04000080b034008000b0082145014029485a0b0b500a980c403036501c2d04100000750fa90180142c003600384600000070505004050300101054071a56030b0b5112324070350750801009045003500000d4062130410f0544003607880301005641c003100306541c1d000695444800f045603a4181340000c00c5405545041c400640c000c1400110301c100d0250030f440c0c103a9490400701510b03058503039111140c290030030030040c89001c80c440300b19201c1d01d4100340c0038003140e150303054981c4584600703501c06440780c400081c0c0094419000b4442108540300741c030081100e01511080911044403196000f40142c000c96000d000041038000d00143e00b600450440784110171280118002d18010365003035540b00000320030000c54580344010301c00402182c03ca030183e000c40701e989141e035458000d0a92170002d91029800001e841c003800700c1540d0f0a0f0000d08403801100d02020103002c40700000310380d40c0503980d000800e4040303601400440e10700740d817000e00c01c1d12107680f56442 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 927259523 1250 927258273 927258281
    0xc0901050312090a09052505040b070f140d120b0108060310021b011104030605010503010c092c0406090605010b13180f020c060a06050f090a0c03020c0f01060e13110103 74
    0xc070b980242c1e5260003190b100317014803515116114403540c031110810550649403404034100120310403c50100014043c1012800a80b1080d5500ca00300d5282c10813140b400c08184008a80b550701203215200700e422410364003100401da0107940e0301c420850b4244240045600520865250344c05074000914140442e10b542d00030095098500300c0e000b29110340390180d03400d480ea803034112805524042014814800e41d8440c80d40100320844c0204803466101c107001d0889005032055410510032000d0000c0040782103207400720040d0800c07501246625040ca8400e0041540d441c0594032246010b00102e6000696401c84d0a904503000c0d6900c54103140c6444d1041080c2110440710510b512a000700c6402201400641201807a010180080c1d1405071400001c03108690f00540c82580c0c0d00b030382d8040e03a4441d078030196080000b600d008903100106040039030182c03055034680c0c030300c0d07106500c108074100c081075004500f82e42403d402d042440d12002c05290748034a580401070600b0545c10f034115a0340d030080d88 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 927260773 1250 927259523 927259537
    0x1e09050a12021c050306090708072708010612120e01140c0111030421021f02030402061b1b01050f04090e070302060f04060905041103011503060e16020c0901050312 72
    0x304680914038003281402844600120f0040401d00202c1401074900d45030800741d82c880c0c01450064208d00d04543d006008034059001003100c420320050301c1d00780365010311010010b410207800034050300796141003a18a5004462040d00c660030b90360318600c22507109400640d1440d805035500c00140488250b0088140c1c854102c0c8840c0b0340d42e0b5000d60070340c00070341c80146100d103020395400c01d883d0043e90943c1680d00c52035440d40d02103401c00348003140503601c0040d25641410700d407100182c5079903882c404038000d44900c0303800300e8aa010403511140240d00c0003600c1c00b400e40580050004800b41c120064915014440d82040c2c440400d000a000c0c40089500103080005024212000c642d680c1d004603156501c0180d4107a1607407030005080c8010364100040d0001041700b038408220024002c010301941b0f00042c054202161403282c04034012501c00e81014019100543e0490700d107041005203202c422100502903400f60142c48110340082c9401203069049401c041c1c044c0400c0e52000d01e590f2041e9003d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 927262023 1250 927260773 927260777
    0xb04091703180a080c061609150905120a03140313021302070b0c0405040c0e0d030305070c050f0d08010e04020a06050d140a1512151805101e09050a12 66
    0x2a02c000c00e04808100b48090103000341c071603a80d21404202d8984c2002d20040c00000004406010f2450403070780a044103080790044000385000c003102c100200c40200ca10b5201c594000e040d940a118450b402040004e0344a1181e1a400030854040c1d0580704140421143c42800103102c00508015040003c41c00c000390080340340c0103240598503a00d042c20148240d44010319014045070500c017a007001e02c071710010300e80181441c888030f08420300060400c81220400504064a59000c9400c050107000c41000142d809402c5e00c80207040e8071822603560400403000f4000079482000040c0924504194500850300075001941450429000b03580076407001c00c48004103556500c1c0301d1202d0841300011405001c00c0c00000c214101e403501209080c58103500803000d5544000c03600000241d10803403400e00d04e441600041201ca010a0101d48800301400000d0401c0c00769109100c0340140c60b03070020115419030b05490034071240c000e40100443d10b00c410300030300030b50106540030003103051000d040107190514 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 927263273 1250 927262023 927262051
    0x1103070f03090306140603060c120a0b010e0a06050a0807030507052d210a05070807030e2d101a040b150a020307030f020c0a03230316060b04091703 65
    0x40d82e1001304844049070500e04c90b03150901400481d20f0180400b03a08103091074a0340d4100b962100111b524082c002d46082c503034560702c0107024010790054000b003044010081c0441415541c5070f5000d031440c1c3c072035014100000c00c0100003551444c000c1c41028069907a958685080c100300c103a84400c403080d43e02c500d00410f8a0100c91912282210b00286010340c45018040300e40f90b80a0403056034140003405903403000c1c0c1083c00f00a10542e01c01080c941c0302409140c0030403905808000750342080c814840305d000d0024441410189005003d400040b0030082c401182c0c1d00d40141c4c900d000466006625508000107545d10218451406400103078040c0001040001c107041000c88a551590082c3e0201002d40c002064086c00c0c107401c400074121410a0f400588088005000054014015800000d00b0325800061000d0a003005c200d99080d003030588411680c4c0c508140c00964000200d02da0111405410000b141070306e4101402080303a0140c6c055055848191001e182c256140c0005040c071001d8000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 927264523 1250 927263273 927263279
    0x11b0f0f090b0d150e06010e100e040504031d10022109031e0d090f05060a020109020405101505040b030c0a12050a05060a0b1227011b0f1103070f0309 66
    0x7000010040c524500c0c0c0e000441c000c4d684800000d40e1825070000c3c50040c0385004006450742c1040c0302041002c3c040f140c0c800074034042581540e038000e01044064006140608004c1010f0f0441d40068410703543e02d400b9491007285808002018188000d48401a0084006145028403403c01a6180908100c415040c42100360119151454407803540303860b801291801070b402c180038001e40c260484a40b42107800c2d20300344207091081d0032041c0f1410f80162800191130801303a01c00c1d800031a20710b9000348144201c3c28070b00c046685d003803c0c40c0113078154110000001d00009006070704a4080781c10804106007503903510300c040e0030f954001c00502c20a00094040382280714466100d0b552003151040b00000c0c042c1005402c2c0a8403090356081309181035400c00148210040d0824003d90000c5140354000c1102c44040c96100d13030322140111800d5640c03c2c00514421000384103c01c03003580019075952901d042d08028100da819a0b001c01082d940c0e0420010200441c00094800208a00900705214480c4d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 927265773 1250 927264523 927264539
    0x4020d0201030234030801050907050403020d060f0e0703060501050303130306090819020601090f0b0d3e1c022407120c03090e090c010c0c0b0703020a05011b0f0f09 72
    0x1000c0c4c010119510f071000209081542150785940940030640e40820326203001d030b5014240784210f0001170b224003910503c24041000541100319446050001800b400b0350492245980d8045408100d443c01d013072070004201400e0005c280d07150401c25041d050240d518646504005001640003600c05980c01c101a011000480708201018010743d4020500ba44c0340141c3c0c0c0045610014082032100d0400c0c1d12000c45076a0b64621903805900442100100024103510b020905080701c00c00212240e41030184c10700c0006e00403e20030a160a5502000400d01c00800500c083e01c21030b00294451011500c105002c8266030301220141a590540c03440c000d040d407a034458008450030490002032920141c1410194003070b10560003443d502030942c441e404e0001a86807540c0321380071041e0422100c1301880044c0b000f022110b0004254404c0a196514154240203440303081182c401e9806609200c0d00b00f0f41c404100040c01c11413611940c40c1c80d0710407203d80d4211420040c0310325407800c010354600c01080e100703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 927267023 1250 927265773 927265837
    0x52103131707080a08070f0f0804031b0204111e040324020c03030a0603031205070f050901031d0d080f0402030a031214010b040f0605040503070504150f0315050f04020d02010302 78
    0x51512176903c54034003800300900c1d5035200c984200801c404440d860788416048100d998000e44d042c24007070060b6088c202c61100a080c0c2c140040d40c09418400008007602c03102d03000b0f1940c0724200c1459402480c220b107400d002031146200050102c000050048181e661412280c1d8000c0712400f409440c000c10034903094559041544d00519181c0c0c0c5a10800800d034002203940035041d40ea480c24485440c080a0150070080b04034002c10034443c0000c1d01c0ac20980c400d07446000d4034070b071208540001c1c0c1c0c0306030007050750350b0200341c00d4101090f210000305220081c1d00d0b0940748190b40c010001c2c504c06d021640c0440d44d14110000094032261540d84060044000800d040d010700990143c1c4c54559203440e06100038086168001d10a00804110901c020340380443c2a8007a6034081d503001c502c00d52000c550001015403940074000300d07241e0798008401c00003107000191581507000014041c5885070501601e540d03100b80c40007940407030124500780040d4001c0c5c001d40366a10034810322501141500a82070159 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 927268273 1250 927267023 927267037
    0xc100e030d051e0103060f180b0411060c01020712022b05090109080f01090203100216110a0e0a020c070501030c020c2107121e0302060a050a060b040305210313170708 73
    0x140b61070340c1d02c42d4404880381c41000350800903514000380e01c0d01d6a444407540603270007a00281080c0780e0b0080030861078a60404860501c4103e200840d540c20042c2401c804a810b502035400042c01062000c403002c04040c0004007540484c015003540114410000355015400030b038603d4140b1420050010703407221b0a201f2002100ea11a001103003c0e07030107104050a140c05081851003030351041c86200d1801101150b15003c15070700400d421050075017440080c0e9241001d0f400070b082040003204011003482c1d1034000d0702000d150581190380c0c59854400543c191426402010010f0b407204030b84010070300c0c22100b4807080b0100e11001059111500801c90308003501038001c00c03038600c0040d0303210040107003000402565880c4500503610440c0607540003503ca030406807150341241c2d110800b1131a00284c503400741e0020800780c02c1d6540d46070394030300d410303a20303000000301c664280c0301c0501402c4506040c01003107034403503584e62450f4124562a50f072071144800c0c01c0181a40c078101d0501441000a0010000b001c0c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 927269523 1250 927268273 927268283
    0x180a0b04020f0703181211060705061614040b0f0313021e0a0503010509070b21152d1212030a0e060703060b09131b03020c100e030d051e0103 62
    0x2d0f40780c50b420064415195a0f46091350803c9420003000300200d0401c0c2490744c59403046c078203958510b60000041c681e00070382e00302404e035001e075a052204000710380c01101e00d6035440751140320844000e000603004a00541c4240d0f039159004000402c903200303002c0300460740000e0015141425078000d8001c90610300e105c1d0410504900102102d9605150015050006000c110000d200f0b519040e00d0303294440c1042c0c403c0000501000c01d01c1100c613406284050b600910381a0805000e1401001c4c10400300508514180030760550380c070410b00030401c802e5002c8030148501c82d12500e040204240305c2d14082000765080b41b8040d056041e680b002001d4001d5000f000142c070f02184c03a0419816203420524068995800d162038058200218100d40d81503e0b0350b0541118000b900440a02c804c5002e402c1041809a560380c9400c04e41507420f0301a4003070819981094104c41c0195040c9680100301da040c211602c000e0360043c00700c4c541c0c441054100551112400b030f018002c2d190f000044007500c0b002078108540c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 927270773 1250 927269523 927269527
    0x506100e2d041d030a21020c0d03050f070e150d020d09030201060e0411060904021c090c090b030316050c0907170a02070f0f080903031b0d02030405180a0b04020f 71
    0x454a881d008846a0507450802d40d083e60b5110460b4039507904c100d8502a060052810b000180790b0040101c0c10b032007950003401503507141c80200c041c81d00e030100151980d005c030346080c002c01d10407a600305415119100710380303c08041c00c190f04d0401203a10080ba1005214690810440031006440e00140903a81c00340800421402c3d03003450080d00317485c0240c004540c030126000030400403540e5050300b190446030945040360340740f0102e00172401038403d0b0000780034030a441c42c00c0f4030640f2440e0350202d01b055018084042c1c100d174035840c422003518000855594154400c6c0410340a0750941d81e900c150040c41f5504544010f0000400b146000b201111141d001c1071541846ea0012421640c0451348800c1c0890214501300301c1c1d59450381c950f0010740c0701130700ca14903002e545002c0084020449101102c001d0480ea120100c03090311841c16440429440c0050041e0000602200e00020079513050300c10081c041090030003c10502c00c2c0c603140003031901c0407503615552111101e4669200070040d081e581c9815903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 927272023 1250 927270773 927270859
    0x21903061d04030f0503090c22110f0a050c070521060f07080112020d06022205090c031303140a1d09040302070504021c05010e010302130506100e 64
    0x200e01002036a04210007007109010000003c0d445940c80320700d600c403814199101e807200e00c8003070714040c0400d0080d9000403510800c160000354441d90182803c0e40420180b04a02041200d2034450142c0d042c0c04910b01d0302403214003040341c05040a030901206000c2100e40c059079607800a039504003a25030320030b500c41000360384e0800c0d100144101e03a8440044041e00415042812008013103040507c02d6150ad0890b01041c941103507110345e54414015000310056442c0c3e8400d41c0701c1410002510000180c1c0542107100051504140498a01c1550052405400c0d0390341ca850786054006442000c80400c00025605c0c51289580c20140201080342c1d940c5a91505440141c00c4030000d0b2542902d10903c0344400b00800280d00042440c00d80780c00380c4025880e01810740c00029450001242100c40505140001c90b0309150080300604a9000301c404142c001025403541c01125402e5607400c1c8c2242c2c0c04007610240c180190103400c00361102504800304c111450715407400800303200d12541c1040480500031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 927273273 1250 927272023 927272039
    0x120204090618050106140a1106010e01060914100c051c0503150306060d03031a0402041716031109041104150302030d020c0102251203020601031b1d060402190306 71
    0x208254a441d90b90400055042c5040a0000d40c0410840c888802e400a00c1e65100740c4030340300022107900c001c070840381740303584900140710084001d0060300d0000d48000000509502c50140b6040e14600140288000c2c5043c0c5400320748400244006450b1449050f10400d5020220030b200341c0d1040141d52540d8881c2411401c00000fa51504a954481c3c0d006c02e0074460a071b628a0903040c3c100d41e05041c0050f00712280034078a40c9010070510b14a90091000c0b40001c2c2188009903419800001201074075002120381242d8441038284d400040d040764034000b0004001d0610748461500180108034081042d40c1c1580042c043ea48000c134001454203510400b002107080401c100705811240c0d0001d40944024003000035590007007018446e520952041070342c1d10903081c60540c50040d001c204000751185c4681c3c1406035030b1b460203100455a01521062a02542130503601311000d84049001d1403e014242031f001782d0038214007422035940207508100040050095000d003448041c01c40d180424203501d0100d80b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 927274523 1250 927273273 927273299
    0x18190b070f021c0305090409110d1110050a08040f08070804090e070f14091015080f1f06030e072309160c0b090a050303070905040b12100c1202040906 66
    0xc00c0c20840c0c11003d080000303801006490400c6820359000448001a060011740b90320041c8c19590400031050041003844075060014000050541d0a206216240c0500f2217280c85011400800036000032b000c640065403041c4c59813070a90051304070609081d5107807290308440c1c0c042c1d072220814654681400d01c003a1002d0000d000101009602081d20f24901980c070060440d00007005841050150001400700b990b80d44443e0140c0004a00e90801d0040c028000e44912000e8542907052080030002070241341030350140c4a5a001d140b0721680b1503e10302002680a0718019100d03040074080c4050200e00103211825010403101e8120000d001e110720002440003c9002030007526040b404110700210031b640001000c0000c542c0300d42e8072130850b03407001d004070700b010261607004015000001c14089603d511980c003006035502210100034802c021810071400b08121201030503ea00304d04c2000c1e2500710030364040d0b480c001c81800d20300b03035640721a00c407441240c0c401d80042745141d503210024031a20a43d140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 927275773 1250 927274523 927274549
    0xf0c0503181b01051b100209011d0a09021b0d02070f0605130308032a0301050411090114030601030e01091520120606070f030201091718190b070f02 65
    0xd0041504100c81407140400b180841d541404400100c0400a400d00070b00c11454440d0300701a941d140c403003900200040c2d84440180350025003580c40e410000d130b002d41d829a01c0c2c240020081403490f403501c400d60019400030640300c199683c1e0054000880034080c0503540c1050169405000031a003081c510103c005800c0e007214042000c10301031204002651108602036a812111b480c0d203070713514070400508481c240740c08015501c10728420310f012694940091810b036042150140321075503150000c58000c0c01441040380c0065010407465055109110056400c42418035001c9440c01d80900030070f003510380c8400b0443c1c814050f80e822490320707440e6101d1150800b0078510100038440a00c1c02030201da0046410f000701c801c1c0600042a400c5d5664012034038010750003100b01035806c14904019000b800d050805440e000c034011800680820030034202c4145007800100b8103210034095040c40900d4000003086070b660440c205010642c92141005480320b503214080404000c081032041c0064290505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 927277023 1250 927275773 927275821
    0x15020a0b0106030b03031c1b0513050409030f0f09050a081621080f070b090a060b1f030509070305150a0f0207110609130e070306110c0601060c060f0c0503 68
    0x1c0800c139015a0080708440320094030300202c206000c01d0345507400c010001d0440c140100d000b0a070030304a07005d41004c00341c42c4d00002c0483d1b414003135130b4500c240b1059890100008000a21214605100794000c01d99901212604d04e06682941d85407000300d0940304840d0404481a402803560214000c40001075402810800c155501510340e01d0301508104c1942c2c0e00000c2041c0030100e1104d80003500f0750180c5544640020030320b04503043c443d0405440f182d1f076040517510780342400078100990900c2d00c20511300014140b4612070050b00300100b1001800003802a001d180551500007012840c04c000b42d240d59240405400940e041240800d411242d080e0015004580184084c0002c120100b0341e1a410f44d00035a6803a030350340c0000c0001107010040c0c60f00f0230b07201450100c2c4003080e184005904410b49104801c10003100c032641282c0074082c00b80702034440d2142c0c4414014002e5a110b414a44001032003280b000c035169804900980507205444410000036001008001e4468108480c01c03450700826 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 927278273 1250 927277023 927277031
    0xf0f020c0106140a1a090303040b07021e220b041b0801140a18020903120c0c19140303070501180b01170c090c130b070b090610090c030615020a0b010603 67
    0x3c500480c1c1808204c1c4504030003040038a0a0481c00340002c4121122000c004080d130360f44a0302c0d480320f1062600039420603809114a0041f0a070808882603070100da000c4e0040030000300304641c0380850201c980c0110750724161a02e239a029003994a0f940240440f18503190724260418281c02c0c001030049105034440440d401d6100d003840003648404a181c000d4882283e04000b400502d810343c20040e10440b034903660548914038030f1440002004000d001c0341d841c0c02e01a5900c0302d051408108050107004540f526448600508200b030b254040708050a001c0050113490808110342ca5141c2100c10a90001110400102c02081040303010401c10f405041c0c40003104082d00303100e800c0389030390b00440303008030340603a400ca000b041d1100c1e003160a5030760304502400301d104004d80768034080200c0d8000c0756084403502c804001145e0010408101075205403900f203000304504e483c011034800540711046400003030554400700440e0030704110103004440301c856001001c04200350700e0040d1407090142d01c08c008152034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 927279523 1250 927278273 927278309
    0x50c0a080a091a041506080c01020309040b011b0507240206060108040c0b040b090a0909020303031b1e030603100501060c031101150e040c0e1506030a0f0f020c0106 72
    0x200c0c01058000d4071001c0001900c1c1c100f4640b1101e1605030310880c103010f01841c03040008118200d45811151030341e03a64180f1841341d0f40c440e495910140500068056002801580c82ca41016071143d005103c0514141c10300b400c400150302602c0c01000340641e025003006c1418052102103810010404140d042d0114080f070100c1c400039101c2c0c2d001b4089504100d01d0030301003000e02c40e450b210382001d17140d00351503d940e0315601e1405062641c03012240798050709104400007111602c910803000e08903005070146141d03584110442d00404c440040d48840c0a01c14040c030070260511850b15028060002c04140c1c4c0c90625200301454941902c0242d0a440e0505005001c2103500401c0c401280e54541080c408146030200011301404120080c01100300c17030003e0000d0311101d400b9038240035138090080000c155449040040b403640040b205c0a03003284001e00e89840e281415001554012070318080021141c08940c00310065440200041011580100b451000d500342032181d980103150034006190b901c81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 927280773 1250 927279523 927279527
    0x10506010912080307140a2a0302060711031905120f0903041413050a0605010f0801031109061f020102030703060806060a030609050a1e03170f04141005040b010504050c0a 75
    0x30b2884000345182408404101d0840c001e40d5500e010311107100e801a240e20f84960014203001e803001e100c401000c1e032400d000d032514a595074242c24042d01a405040981e4400605503081c00051166a20790b1104201d001c00d0103040822811840750a90394440c0d403000000703c000036003c4080c10b80841d124582c814440123000020445040302c0c0d0011603c0728189040001400301c4071204130b81d145140c2003604002e4807401c9584010140d8000744c03600040c1c0704041070203c403500700074040141502e00c3d450050300140f51070030000f50300120017842840071310750300071100803074a004c10031103c0542e40200c1804022130705070250f070300600010402032446142803070020340e0700c6507144405410187c0e40c02100040c4207042c087c0386029508100d20304690f680566001c95519403a03c3d05400059285401c540c107290360400c100c0c050b0030700164540d40340d00d540e21085050204034442040c9482a106400e80035007090013061300c43d0b40035440c81d941a42c03510041c0025100001c0600076940c604000b030fa19116 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 927282023 1250 927280773 927280799
    0x70e060c0c09070905130b040e151b090409030e10020309132427090506070e12012405030a24020403202407080f130b04080105060109 59
    0x1000455030410070f925010800d460002c125000b894102c05c00c82140d0486443c503801044e01e50005441c100300b404007050b042c5880700b60481740005c808403620081a8400d4201904004a10200c04064600382c8070000250480314140030440105d071a0000810305458080b00002000105002841c981506e503000100c0c281c0000c00d00010300e583d5200d600c003150905000040c0301e421840320301e1000703640350340c0000001036503000210340e244104a11aa00400b55010b0b9944070381d403000041c0403d03215080d069503108489040550080800c00b0100c108820900803007800100c0078441da49a0603002d5242d070116880d90f04010f0082d484062440000b070700c94404800c840e200200c008400c40e04411100f0080d1003290710150607c80c151901202c0310803a26030711504008101c5440b01c0090002031802480266040c900c0c201c1d0314107100c0800428040760044c424040707919080c0349401740c0051103503d880e2a68200c1d180074103010609101e040d20074415a600080c090074244580762800038041c00c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 927283273 1250 927282023 927282043
    0x10b0417070914010e0709050d06051504050109060e0c070503030106140c160501080604060302150a050d090503041503050f040f1505070e1e030a080c1e0105070e060c 73
    0xa405908208006840184107800141c25200c0040c0060650420030000c0c080e000e0140e40fa440d41d0342c2010511080c0640101d0302211000381c10100340184d0b5480701d000400009240800524090040355001c1e5154414207018100d42d010005682e402c0004144101d00c0040031800320103400c12a11001c5480041500d044500038a00303034050f2441030324007900307030b0054a400b48024455a0310f01c01c00f2030030142c2c420040c0d031b0b001c6c6d0340d0303804a54544080006a440340d00c00a50400c2c0d182d01c40d0281500c4d1a00102040416070820900c0c150180c031804040f54180c03402640c0c07641000c2070a1112540581c2c102000e141c4900c0c0074815420905c44155001c040900300034a840000c80b0283c04000340d0094502050364070403010001c524100d81b0182c001c034681c00c1050310031811600709180c80702d0f0300252903480d62809001442a160980c0d1140d043e0f501500046a0520540b0032900394403080d440701c140b0301440c0034004112420010005404545100704a900c200800c0c080c0c01062000080c4900c1d070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 927284523 1250 927283273 927283289
    0xf0d1a1828020613030305091003020a14030606070807060b03190c0b070f05060f0a0c020f10090204020f0307110c120a030c060b06270d0f0f0206190c030207050603010b04 75
    0x30014070707840000c003580306240c00040d8400208000005154005000d000401c0381912840394079180340300304400721321641d40304a0110b18800403000e0a01c13000006103511800103021a8600722007512847c1c19504034041c00c0380c2d219180c220001a0341001d0000c4004103041c60320000c84151a5691140a58000d00030560f02e06008a0510240407061441d03858490700300041c0c0e000d60903c0d440c64101c46004031100744480307050000c070342c114500c0054a000030603c00400740220300941d00c00800a02132042091b41d00507004d00181c000e41d04804010340c060f5415448443c81d0409810045040180142d022031080100c0c43d8200c4a840c0e01254407080140c0c10b242400f001180b920380500100305a408840d001000491004140404250211100540745820683c2400b0300001c0041300f60740580000e08581003104000700043c0c481c00304600c035600c010300035810b0002c108036400c1c224055a2815001a0118070080c040c1901480018040c143c06e86419245d903050201c0680244100e1080c460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 927285773 1250 927284523 927284593
    0x30a0609022701020109120804020a17071809020325090506092706090706030f0b0f120c1c0209060301060e132d030206070309030e0f0d1a18 62
    0x60684c400c1d03009120b40d540c010f06d80c0e1005102c00e44014130b4428215001c90007811007010224000b0b0070354042074a03401a070401880b10034105449040602d07950480000b4007a02e48100d41d00581c0e003800030f00c200d040700340354844000d9011568004603030741c01c0c0e104118681c40e01052180c1511400b24a0fa4032120007081041091210102502104070210340d17000d480c000c0009104816602040c520704440c5190b50500424001007040f008480f054100594801050004403042c2c1c00d044e1042401c4071080020707101105602404600c480e04500d41050448811074a5081145824114190054016130003006414241180490203103405058050450030085040e4100710b01c40d00060b044040035283c10700e00040e8018442c041d0154110224090302482c4005160703540310340329415070070780c140c1d85119802107080c007484944c0714504003a82d007041e001003c442c0495038004c2000441c2e914401004c2c3e103441c241550030540070b2220081d809a401c80d0b00b1640d00c4a18150a0320906030401072211 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 927287023 1250 927285773 927285847
    0x6020a022b0806190b04061103250203151303031b080a0e120c030304020108160c02010810080604030c031b1a07020c0d05060f011d15120703050102030a060902 70
    0x3d2100124084c880803080b8540c2001c203180410780702400c110b4982c0d4031003280b941c90082c80d1b40d0716801883c0b4409140c031034038514814010310301c40c500d2030428000380548003002103211456003c043c045549006d200c4200030010109076251090b001c180d03c00c80118041003210304401010810080c105001d51074403070038030a0309080f0900400c02a0348144032006d035100c003079400c51600c942044805901003403503900000c24000c40b40818a038000345036030352075050002c264015541c008024001d048c405440d80070200e4003050400640d03001d0382c001e807039660380001d180c0340c01044101d14042c0a401c1c2e82104002c400001c454601d1201d004481d036140c0c200f25580c4c550120710300060680a90f41c071040e21140da409000300859070b81d01032414200540c3d510303a01e81c0c2802000070803007021082c0d9200340000086031601c40c0d01114900e4136000b4640158610007114852804615400c1610142d5000040c091134054600c60407000701200c440941c10301d2442e01803540030180c07895010380d41201d81c0f10f050b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 927288273 1250 927287023 927287029
    0x1906110d09082e0903031a0a0302031011040e010b1209160605070f080a120f02211312030213050a03031b0c0e10080d1d120a080706020a022b0806 64
    0x4102000302d0f0b010040d03c01070782401006415404841c1c462201c6040c501010f41c20125000029070390060014509c10a00c0c03400c075401000c100440d10359070340c41800085040345046900b50300038130402403a151107488800c01a405c01501604440d11940943c00c1285881020b6180500700d840c142421915500749041c40750b0624051400140f22280000f1001941900b02d252110040c0c420720041000107420b000c000704a10034010504441142d03400402c1c0d140e101d010900d603000081640c80f50780688a9903034800020381c400c401c0c0c2c0110350081a50040900207503040801042d0071910f2a262504d5910040d01c0c00062071318802c000b52014000e402404450420f000080864804460b654600b600e03100030842068050002940222050560b110384501c81042e044408141510310b4550b5010402426290080180300c56020b030f4a40d04000c04d5404001d02035003802480c02590320700d06480020f00b0426810020300c00286010788202240c081c221607003040b0750203410000c1d0365441d06800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 927289523 1250 927288273 927288343
    0x9021909030c0b21090102040617010b04180e0a0308061002060f04021516051b0d150c0c06110a030b031507080a0227040b1206151906110d0908 63
    0x105a0400e84d16824441c03103181c1503008108403070729990b8110701ea4102d103554214071038080c402c94065440501c402c4c00b2003032801021541012450f100002c041ba484e6210605003400810b055020840d040e08024030390811203142c4020704010b101038016031516240a404918000d44064050801c120b100c0240320785443c115a15081d100001e06814019480c10a41c0d0f001110010901c404000381061014103084251400b25070b4031010a02121410320f88580040420380c103141d007007020588407400864082c2c80350f6901a17030509a001c6d900c8503c0b001c0075041c1d841170180d66000c2d41c010014070f508040c506081a800006514003c007032511072208130006401104070842c901e2140710b0041402c0c1d802d01052101601d01030b64240140121030f41001040c9600a02c4066180c00200008070f0507284122070350340c90000180174001140e1806444801c0c06455040380001c03a01881098603040fa080000400090492800d42c544c5130503d03442e00e4546101e41518a01400c030640c0060403002c01403d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 927290773 1250 927289523 927289567
    0x110c181e010e01030204140c09040e01021c020309010e06040305032e060210050a02040533030903040602010605030313060305091e010b13060e0402060307030f020409021909030c0b 79
    0x20000003961159901ea03010b00080c48100e20035880c2202c014410011020b41a20581041d0300701030818a03404113220240840c4001c0c0e4010395820000c092000f08400e191a40e44200c2850040e142d01d4200481421509984c44404444d4480d80401001a078850300712544158140b01400c1022869010300d0880a5130140c100e00404040d0702c0483d00c2a4002449003005064540501241c0c5270004100c0491196001e29500601100462183c1d9081490b90301101580d0b240400d42c0d103017155071034460700e4000740c50b02c500070b0704006402c002c4580d090051170080d01c3d00710702035440e000e01c40e5054091030400c0e100744028981c44900007541d1050034441400307030f884000341e410345400030002998024100b02c090305114203000200b9610503200f40c07090f00299410030102c002c00d07440310740800c14217400c020042000c050f12010b440d805264140040c000800d0303605405030303c1d50b04501c4800018400ea0f4400c4003000504113041001caa41e41000e0411101c0c0c803120f455a8103061011756240100d030b42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 927292023 1250 927290773 927290821
    0xd062111030c030303070507210809061509060d03050405030a080a14030606030604050601170a0c02070608010e0f0c0f120402010801050d05151302210c01020318130b0d030c03110c18 80
    0xd820004c0c0c02b9044070301103109024500945a141da242c5000c8031050f04082c5c9403641155044000a61034149070245d41d103200c0c02400c141c0c3c201692100044e00d0800c003242d04503a0100003140d50815660485040044251541c0b4190f086180403c0401c41a000003441980b01c0c07074644020505690081000548040500b44124240e15002444801400c4040001c40047c4610400003a100c1c1c403901c030344d82c161101d02d0754000c003d0f125024000280300c409040c0c0c0d13001800400c40c6508000c0c00c5001032404001840058500e0b1400b4000580558016031001d809441004800c5000407400b1544425031010543c0c0f2010355220380c42c40d0513010442000003074121a0580c0300d210a0f0b01c80000e4482200c0940342210904917094004907202e0050030301800d89580d1080d201e1440b4500410418460115000005048200341c8001440e00c1403882041e0003084120500b403003855448010143e286411400501d45408070078041548190307503d48039016082000c001c543e80d01d51082d0120858244a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 927293273 1250 927292023 927292073
    0x801060c121b0b0103020a090b010c140c030f100c0c020d150b12010509010c020f0a1124090415270b10170603010b150d062111030c030303070507 64
    0xe1402e400f402a003800141d01c2050b903101d0000c1c510015010300e015980040e51210080800f942d038840c0b4004446107603481c17602a18210b40800d4904024050356850702e82c0003040c1c01c42d2440c450400300c030400600c40040209403800744015031070b01484850102d46c400c0e42c44240f0b62207181840000d0600880c420740c400c09410307007140b89000540200d405181440001c000e46010310310281d03643c914220040e0460f40240303861902060040c5410000808054012118080c1030180c0020811003411300c80d00c5e40c2000302d1008400e08041c81410001910120800b10060405802820142c074403103450101250081d401c0c03071112915007180d0f6242c48098070724000d0603401070028003081c90078801c858409281000083d2180f40c1401046940e13280604207002c03a00e5111580201617100180c012125a2180d01c0001d06031a800d5020302c5040b9900d070000d081000624100c0d000045400403e4820fa02800d04155191b4010040703981200803420100d80e200410f10b40b00750103011142d0760721012884 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 927294523 1250 927293273 927293327
    0x2011809020313060605060310050904030c0f0b0717010315021c0204450209060c06010303021c02150a0e070f030516081609020c031201120506070801060c12 69
    0x80f881c0c07500c43e01caa881805401d465000740b085074042101d05820b94441c987c4208000c0c03c1201c1c80741d40041c0a0300c0d126611008586440c200d4002070303001218070b2000074041280d0207901030b803c41900300540540c00255455a100d00061101a20120000030b81c00100e120b0002148a1b0f4038200000c010030640d181c0340c7c2e84005540006201064a418001460849040c1071a03810f0446070861000d41c81000e44407200b81c070b0030080d0440400d16400480400c003d5010305010000d41f80218030070b03401041c0d039442c0c0c03960b85655000b882030810107550194290100c0041d404200c1603000403000e800140300301d0b1000d0502d1924015500c40141d81c541d812010003404000b080c00e10510b401c031800d1003502c1e951445030f141c3d03500d600c01c1030490500e0200f20074810440705800502c404200942164100104082c15004902080e0720410400607030003805000c02c07030248091039101d1a103003000c040ea903140c9200542941c2c0e9903c4020700c50305c030000c42c01c4034050240b802d0644401001c5012800364132 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 927295773 1250 927294523 927294541
    0x30b0108010603210504060c020103091e05010b0d021305040f0b090709110702030307020907030b04060f08100501061d190e0a0e0d0c06020c0708010504030c03031b0507020118090203 80
    0x40b1800306075031803a00c0c100000c40b4003d0907881c0c0006030b8415034030140341c00c0c64950101c3c2ca141640c50200e0405171a501d03120301252142c003100324042c0c6030038001c0301c04620900e0302c3c0e42140c00c0c82c1072031030040381c030ba07a10000580d0700d100b0110504001c003600030030155980e107030107195240c0c09500149840d45010900c5002000005ca4905031408520100030201d802030030324040d40901c0f98000d505500c1048500014105112001c1d0811a1400d0204246820000040503503030103812801401c244010200030083d81040455840c40b42110100055410004001d00032a01840c4585080b048050049030540311011000310000c1281c8990b00055150f0108880c407140c20b0f100ca00360b450502c0f804a0034210b01250703215258115880e03850035400f10769035a00117900001401002d5010383c000000e0060002c0c06001d00c143c3c880c3d6101010300d405072402800319108001c100402c40364920151241c40c2e000000c641c545902420900d20002010813441000169900100001c6001001740316100b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 927297023 1250 927295773 927295781
    0xf090f0305030108150c030a0f2702030709090809012109060501082505010c050c060c0105040b090c01050405040216020406180e0f031608070b1321080705090406030b010801 76
    0x2091801a071780303049515030300c0320b10391102500e8a0781c1e451401c102154500101c0c1d07205800c21480e00d90041030b030314128642184540c8030b0341203112440042c07540d424110b180a02103000607140b00c0204101119142c1c4a007503d600603561f005041c0130584040442c2604601411548001d4040c4140710b505c582d032034514007808080c81203070030912900440d105071b11903180d1000c3d00a22130124a4031007a1401004580340c00320400203603658000c0c080c0038034650f102c500007448440717011070010440d0308140c41c1c0350b103800800804091203034100c0d5800201eaa0b9000c0c040380c02703c4400300c81c0982c64040641003c000b20350b1a0314000d60062908200086e0801c1800f201c0c035039695102c00030014001441125516004224082441b0307400401a0301e4440486400d03001020780900d40450604501e50780f001407254068401d103c4240341200900c007088654411074884800030680343e84822003030040540301c4000540f240040c03020106442c507483c2c07a030b584400010754000f0398a02c03555a41b444000d00030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 927298273 1250 927297023 927297029
    0x6050406060608180a170d0e010203071803050d0804060b09070c020103050c0a08220c06020304030c05010f020a300c050c01020c130e0c0406080c240d0f090f03050301 73
    0x300f07074260b001031404416524a0b900c40d071300140151501c40c603e40d440d088001401c1085180c40407080c0304024882c045445070080065441000580d80c0c1820300000e003030f44010b002918202c065441050000400c0403815403803000260a09041035201d0346041d43c06044210b03d080e0300500e803074081004642e404803980501034000c0e01c00b0051504c81c4603031b1a1082c40b03800b000901107880307103011903000d070b800590300c000b041e85d402499500c5030103d40e66001a914140d0042e80142c1c800714042c81488984800d0380b005207402d00700700940840144000e0348609805402804400c80c080c101550070340e500312035407a01c0343c10080c06038503a5040d010181112504140c1511680f003841600400c650001500c2404242d000b00301001c0440d02d00c0c4d06030060100201c00c074144c2d0050140e40c091301e07191030265001a22100700640700030b480c0641400024045080701458074142d09034800b9840c00c035802202d00614038120080303070400c1612200001342500e24001011940000511800c3c154814080c6061b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 927299523 1250 927298273 927298277
    0x10f172a010305071103090607050f060f15181504110a03020a350702030c1c030e010b09150102031306050714010506061605010b09100f1a16030507060504060606 71
    0x305449503c012540305c0d001804c5440664020060190586400300141140070700c54011254281c4210010a051242c2540c01d141c4a10707082003403010b11151207000002c0e101c001d4600c242d0001103102150811382c0d014054150f800340b0051400a19110f54100344141110340c41a03e076207019440d0000c00940c80348404a0000e1002c070724652407050700c020f1036040a0700b000d6812004000309502551903a8000e0561810b6200070030100d08904424048038400012108100781c15600c21200175085d10003c2d103441010f64508911006140c1d00c52a00f107402010421901b1000420300c00182d1551041600c0c2c1a2480482d407400180340394440c00406215100715140403c2c548440a1603082c3c81c4180c400a5005105100d00c12901c11022100040300e8001c5001003800c0000b03501080d10303240c3c156444d041000066a090004c001032100c64001000c100d43d00d42d110720000b0344001000d00410140c402580340381403d107400e01d0311032003c0d604400d0f080b20041241d800c040c5049401483d40f0b2082c600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 927300773 1250 927299523 927299531
    0x90524010906050a0e060f0a031506030b060117070e190f030c060c05120d09120201050a0509070305030313030201060f080307050d0c031d01050c0a0308040c0e010f172a0103 76
    0x101e074101402c1c420126003900c40c4045c126115a000c0200214200062980002c416540080840d05d000301808070903ca45030300103202811810800c1c20264004c0c1010f05114441c0000300066168080351648030f030017458a00c4860140d54001120031003007106801c000c140c8440c01081c0c00c50f10002500071203119030209081c0560b50002650054840b8902801540011008194410b04000200401c80c060200040c0510300c541c0c962200c0c200102102005079954800c000c2482e40c0c074810b49070806510380041000a180d5a01e069880c03000130001c40004c0c0018206004042c000d41040c0d000d810843e11401d4803d484011380f5070350741c11610055480340b0825000c3d4851a00801d040f016243d01965903208185500445404c0c10105169103810050300300a00c13810100306001c43c10010340320381c0d00d00c0c0d42800d1a040030011071219401206a010b0000b004010000d140b080800856401c0d0361400c08200e82034020500f401043d0300103610000142031100c15099818098040181d02601e00304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 927302023 1250 927300773 927300779
    0xb03030d050f1b030c0c030d05070e010305010e15060c1e0d09060f0909020721090302030105250f0c17030f09070612090c030f0605011d040b0a090524010906 69
    0x100d1600303024110f100c07034010b00700049074902c070b44e42005102c1c1c4440407044070716001f0f0300c038218401c40d00200c40d9540041c44585a07c030b43e030b603418041d150051444400620f0799040c01d0143d0b070100200e0512051150b50300203440c1c00100402e0100201c20640b40a0400540038a0b410382c64440c50560024000241c140201283e49030156240c143c050b08181c0d1154001c07401d0130580300003581700800644030070a1000c01014401c18074160301d51610b40d19611590350314918810306087d0b0303c02420543c2d50301c0304071030b140804841508191801c0c3d50149024401c811466000f600d080e100e2003406030403245440c140c4070081c81800020750140e540060940016a281220b9a442d81007500510001900c520642a9012a04d402c0002c1ca0740c05403180c145030541d40d0b45c82690f0f804407244c0c112061380d220801000015014200c002031615411007100b0b1030300d05035032643c1c5000c100410f4070b1041139444a5600c24000d0400c00c01c07002c0d00240780d00002c0d03a0300405404480301d00910508036482d003022404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 927303273 1250 927302023 927302041
    0x12030d150f0f0819050c10050c010c0f0e0603040f08090d0609060c080a0b03060c18040516090b03040f0609080c010e01090c1710021b07092f03040f0203010b03030d050f 74
    0x4072009170040c0181840f40460000c01024481139420791003040340074800b9041f0040300384240c0030281090344840c03e0071030304088040c10007040080c02d00d02c2070000380100000b080c001c840860b412071703009030f0b426601d50310a0009003000c1e400841c0030388550710389142182004410341c041008412103442e86000ca40d500120001541d07041982c050f010307000300010603192001381014101e100000366203914500c0c00b60000c80c00301c802c1103d1407802000c18411680180e500500c4440c080c00e9912440751452919464100100901100080041c0e503143c2c0c150041c090b4010545400c2601c0400034445810301c0848607002e04402d00b415500126000c40008406000340c00c1d40c0704d08a0740d01e0180ca8900c07a610341d81002500041406681c2140300b00c5452120f0700b09000b40704c00b614011200207911008101024103920312000b8003014101d480d01c80d070702480d07801c40607a80c0c405d500810106400c400c0c3d2000c00e001d800b00c115020f41502c80480d1640020b240c03900210f2040c144542c802074250346020700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 927304523 1250 927303273 927303313
    0xc1224020711011121030610180b0a03090c030f1a0105010e0d1b0b0c190c03020904020a0b0301081e030901050316170406140612030d150f0f08 63
    0xc04902d1510340811540d40954840c0c41c81101032030984200d54500c06401c04020842c89086504803c00410400503187c04000082c2d5400e01c0d10348030300004010394a00b6040c100034068a5079244011509101c443e100e07400506941d540b2841d041b12030390340d900d0000100280305400700c52030094200345507103000c00f90100a0403200142d4804240c1c038070301000d1040d40f0214000548201c4140c2c6146106400c01c03064690081800703d400940e5020b00030300050a1150310464020109040d4191101140a0035089001d5980441e80c40c0d401d9125440003444a803043c2d484030f40e0790140403000260790075012403040040700e40241c1c45a10355110b40240c90316441400d0301036010407014800700c1d0310b20207811409100c81c403050034040c0007810300080c90514117500311400c445213900c0d12181d02d55111314407030321500084141c0c0c0c205400041d000385e094580c0183d001d240069503940316805600d44402d00c1020003402503000701400319403070703040c00400c030840e41c065005c41d071103044008060030a00da60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 927305773 1250 927304523 927304537
    0x705010f11030c090d0b07111c0e040e100912030b1c060e03160c15050702030d110c060c0c01171005040b040b031605010e01020109080f03040c122402 66
    0x1c0d41403071955076600381c0310680c00520682e500182041c3c0c200d00062805482940249032030703143c0d40e044c40c204415891401090002c1a09600c035403c482e0116903030032411103510042c00302c0f0040f0720b0300030840a00b440c0c40d030f43ca43c100210070b051419a405104460601e404000000c1d9000d0000500001c14024007000c1d5480c07030410581405020001305200e5841801c0a855140c10b0328a065068844019041d0f8010b000791006040103030b00b0405040900d200b0201036089061044c00c283c2c9a800194981d104011448140024803600002c02032013405a030169800051040d9152a171a078400b41e038450002994a0100b5420000f84844100d0181d14a10500410b5845d0b007034581801d00788009828000342407604952075803003458441e41c0078010341c1c0820304c0e198141c05d0441e103001d0004060b044d2518406065925090b00d20001c1101d80c0c0880700709001668110b0b0340d0b0780ba0707072500702d09550303082d0b2115010384480b100090401c01e00c0c01e04030185068000e003020b50b1804c400d43c031004a01c5482 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 927307023 1250 927305773 927305801
    0x140f09030a08060f060c0a0b010f0501141605070b070f06060b07050a0f0602250b01060509031911031606020706050418051801020d1e091a0a061a0705010f 68
    0x9800a41c3c68a031400c1d0103155680e001c0e04071401d00507141810303868400c06903400ca500c040058018818401040000f6004250910300f0441c140c1c1820104e2040340b0503281a1f0a00303270090005001400f808105820040c05181c0c83d07682d45000c0c50502440d203812100d030840d461410680c0c005440e41c0c00c9800da030222608500904228034131940c4109140c0b1a8030342c11505544c091000d01d0309100303010391011610701401c03644c4080f003180b4549400700020580240c8140003081c044031049490000b910700310740c0002030030403d46030038074100114600c1032142c005505119000b0b510802c18545014441140d50a40840c0d00c001c1e110f20f001d85a80c0101c2c051600c83c90300b092400502100f40360002904441422038280000140240c0340c1c2c2642d00113550042c00c952619481a07820860b8003400070740e03400b650300402c0f016856a45180170400c103810f1074003100303e41d8030100c1c18281c0d183e44880e005022204100d9035901080b03041441681208a0030f640725460014000c031030307aa0302d00415500c20800c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 927308273 1250 927307023 927307037
    0x8060108121b0a141603081c200c0616020d030c0c1407080c041e05071209030c020918060c0a051608040f08210d0f140f09030a 56
    0x4000030300096000304601c003000400c402020302400302e051000c082607074080c101c81c8612118054150785814000c503000d00a83c1d500903c10030100c0c0860060f244101e608410940c4510001400400a48040710790034800b540142c003400409050034005060b40d00090003581c03c1d40d501c5c180c0f40303a101e40b080c40640d400747e001000110350442c03207a03018079220441400d004485401a40359012842041c20665400c1d503c000c0042c484100d04100c07851034444111001e20080c0c0c404945084203100c154070601c503454407080880d0328180108500388800c0384030f50f010400700c004c03070400602d200d001c03040030380c012080c24000c505070034a11070001c40b6500320540201283d44869400c540c042d40100600c208001051200c200301d4108822848a8907004084480c0c441c1c1c1400042001d83c0300d61343c004113060340408280c007015071003150200c10b0a00e40d001c545e51140000d401d80c80107050800b454600180c43c0c14100354034944001c0c4503600a0599107100f0b03151360b50b010300c100d0780d901c40c1e403201602003191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 927309523 1250 927308273 927308293
    0x30515061c200d050610140609032107151e091a43020703020312030601050909010e1f05030a080702030a060c0503091c0801030b09070314011508060108 67
    0x7102808402c188040c0010700f0001c3c4030b844280c1483e2040c0c401c209009186101006261440180103005680443e003191400b291034000030b0783c03810141c64000e116140b614138141c94030b03149015520f81d1601306802400c0400740c03044407002850400e0b0000011009061062074170405849240c0700c5079400408a6642c07642e1203000c000341e000041031400c80d48042d440030540342228659000c81407a000605030744080081255410640c00034a030901158004801000940d50010f425520207201c88401d40d500d03200c080040794035100701005160854611000080d1105000002c02d208a00502031181340c1101d4100c184610092489402d505510584050001c114a440284170262005089842825007030b0b4410080d1075a0400c1c04001ca40d010042090702d00080c0000c12180e512030340e40d0000c0c0304c00c1200180c1072010600000e40054990000900901c0741044000040c0d6008002100c4034000b860003070740a82a081076620892810010000303155038005041c9059410a902420074444 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 927310773 1250 927309523 927309563
    0x50f0105061204150f090605010531020408010204060507030e04050408040501050f0c01060e0f01090e120904020d090b0a061a0d02070804030b010b0310080316060c0207030515061c 79
    0x14040c2050304d01ca501c106a074000f04245104100c0b200e00883c1c0c001c100c0b8019410041c00b207500c1613104500612990701c582c124280e00812440c003554854181d020b204048a400300c009002c1d5420820080d880098040756094020001e411881d02c2980ca6001d002c80300c038240310a485042c0c4008081001c00d010501466000d18080d001d0b210310407030420300385010003800030b007035441603802914070200300d8090142d540108080c01d8054001c0480a0182c6c0d10300c81e1a5955401e802d80e0261000c0c1000b00d5059000d903141d030110340060242440511003d030140c03e209004090544006035800c0c40e2902c001900c110341200b00e1a00ca0300205480d003000c0c45124420041d62043d40c003225900300070040800040c1151806074042c2203213506c400d80364a0143c601c21045841d6070050150355109011482414002030041175042d5400003010a00703036040c0109900c0c001441d04010258000d800b46072606500d0105400d100300d070202c3c0c0030040c0c1c49003180c0b00f110f43c401e43c7d9809041c1c01e50701d5201c580746507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 927312023 1250 927310773 927310807
    0x90619150905070309080f070b1605040501030b0a03060903030e0f01060803040302190315090201021b030607140d1d10050907031106161a06040507020709091103070f09050f010506 79
    0x701508010511702c17030f2035844842c0c903032004031f1010360100c1c0441d441050001050701c10b07074400110305125503140c0130204047d195001d10f1251b50b04040d190600304d102d540354071204030300460344004103210805540c0b60290151000c90f04c84825480b400400f0200c800d8140550000c68058902a40c5400d0464081c041c4480d4540c0030000c2c02601c40c01c2c0080081d42148034901c1102000c8400910304044c0c1c0f000900f8a44280b9a001c1c2414290540806683d004100035401c02c8403410400581500001d800145009454585051600c0c0045000801d514101916581d4480c0010b55845814050100044841c00c0d51103004a40c070440c014000608203450840d0010001480b1030300704550700344661240c0d014107804481441080c0c4101c0380f0790101b51042500294101c8040c0000d18203182c3c000d41d41c880034400c5a4565456490030418800e0307035040140440b05c0682070300e114a464440c6075036504c030303035129600291b03242c00000707551036a01c1071019068540081c01b6500d0984120424070840f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 927313273 1250 927312023 927312031
    0x1200403060509240703050a020f0412031e03200c0706080c22180506010f0c290601020d03111608090306040c090b0a1401111203090619150905 63
    0x2134410b030001d95040021a4107108802c0c00c1c1c50150500c18905a0401019540c0241064403070500500400ca001400b40f001c2e50152202150545041c0d40300c0d05048900c1008101948117001d0202c50b4900099455040b00060690301c620541651503035000007621441100e00116403904080010b00449100328550340d00020701801c1581060018034001b00c0700c04450302d0104035086100b004001c9108001140d942d10304030440200711a2400d030b030029005080c01407500c010406038010f1002000800100101c280342e1010700303030f10346809491110351610070580707000f400761141600000006210340100c414408450740e05904007100c41e40d1494074041c3c0040c0459241d0814011003010380c070200301c009d01c1a805101228203062401b1844012100341181860207000150340500440241d0522507040520078a4206403c0b080d5040c441d0810301628205480070f240041032051b08100020305901484986400d144d10001c42c4850208807100c0c0d4440c040d400034000c10810001c41c096000740d40c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 927314523 1250 927313273 927313291
    0x1e031302010e0a0f06020c040c0e0d120306030515041b060c1101171005130903080606031f06020f0c0d2f031015060905130b060d0e0a05012004030605 66
    0x3005071180c4c1e2003400fa405507000340005903c03083d48003c581c078250140e00781d4080e05003402c0c1c580522110210f28090000c0740c02074062400003050151440c400e40c000300007035401c10140c9081010308407035940c000070182d0742500d58441d42c01d9004c0e80d07d1b1004101c50308869a030344501404000a9a4590440030705a544505128a910700b100c0b02420301c130203040c45080c03050035450f8030a0400040142c0c0303040c10403010390034510f0700c0321800000360041c2080c0d03080201100e1070364a81d030f6042118800d5480c140b250200d01040000d0000c0c003960009100c0c200c06502074191480a5010800c1c012544003c0001511480c00c000303420721907241400404180c401c0500480b40d509500d1720119142141c60859403445070740e100c40840900b01c03203100107005011140382590b00ca92400d000543c0c0695011a8012080d0787c42000d1529543c03604101d41d565040381c030090101100d4244d145807101e40240098619500b0000207a110920503000002034207200d420550a2508503107464000b08001404081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 927315773 1250 927314523 927314539
    0x1050d03140d05040609020a0e0c090906030109020d03170105040c05030f071107060903021305070905060d09020d0803090d0e091518040b0115021204032a0b1e031302010e 75
    0x2d0a0006405120303c11806541e002c1140001ca03c14480202c41035805880380c41e0f600c000b13000442805404449510400f101c2c0c0c03880640360080000c1c01080680710081d07100f8170780c233000c1c020142c0000c0f60282d00003914166680710307a690b1007404145d40140c8500400500100000b03030b25221544494ac0d0010100d203041d01e031200d07400e102e50386410791940000010800e0030b02c2c00c00441c6005500c404001c1c680490a000b1418000005041f00d403190195510582c00840c4000b00082a07502c41c400058006010700d8050741281004c01e441d80c401d940c41500c0780900f5404891300c1c2c0c01180d4200c0c42c0c9101401e004c000d6a2406840c819141c2d0002440d0740c44021642c440d030050200004143c0610b008280070074055141424421500781c0412012055400081c0745910300703000f240581e01101e810050001c040d80306000c5064803d5030525050f400800691400b103403c2845030080c10610000c040c60304144481c10f44030702d5040c00101d0354000c0d2071524900540065201c1c044c03110a04101801e503003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 927317023 1250 927315773 927315787
    0x1216080c0601060504091118240a03020316021f0f0f020c10050115080115050f070c0801110702130f0e0327060901051209030c010204171501050d0314 66
    0x140c184070082e40f0501c0051400305040c00a51074907c5907400c8030b041c0401c154640702d02c4c5007800405008100e00d80f0b1040c585150781a10905c004d0009100411311210030654034401c4034000b070000e42040d00d960300c00c100a8450b06203040d0000420116030a0f00c501d4000100040d04c1300b8030040e2400d5040c8082981e00c03507100d032504035140d001405001c580d000152002540d20301600c03044034030582c04042024030707414511075802c0d00b008003a819203146440786940320040510589039442250b5000910030710010341c01c82440070a102d51400d48034400020b020998031061107041500681802a521903151400d890480155034040d8288140c860f4000c5012104842504c3c11500300c00d000f0902144a485151a40005caa88200214008a8509060441c406c0008180d03009054181000c448103a000c5607142000b001903620300c0c01700000035903440b5264284680c07850b48002c100c00f094441d08054080048020306003d058030b5000e0640042c03600320f91400c946510404101448492040282da = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 927318273 1250 927317023 927317047
    0x70609151e031d010506090a0b0904030513050904050c0406060f1407020d060c11010c03140a1d0304090c02070b0a0e06030a0b04051810050403020c310c08010602121608 74
    0xe448404100000068910b840c2e03040c0007e6000080c400102503180c4100310f0f2040c3c0e10101460b80050b09031901d103481e0004070040b00d41c07641e125003103035034000f001d4001c00040103000038180c4a9500c00380d80c18816141d607803c05480311003489242c903000c40e1510380070803208401d40c03014000e41d138001400428500c00d0750721050103c90701d40c0b21003030000326502d41d04940281c7c24011407101e01d0140c0390803c903c000b000c42080c2d0300040582101106a102c0300401e0382880c0c10782903e1207115589055a90f5150344041c2c1c08003c00500342018054060310400250744200c07941501c61809541e1504241c0c82040b40400483c1c0d40010440807078543c0d00d440c03003403060706c07940709480c0319400110541c41c201c00d4000d011882d0a101c2190381c2d00040c01e2404000c002039011503604030001055450800d012014500400c2000c481c080070310558107203140300c259081440d00a10140d51403511000c45503629840c0c12070310b4100c8856010700d1141e0422000020080c403108100600b40101340080c01c0251100d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 927319523 1250 927318273 927318311
    0x6010f15140a020606180f070c0204020c0706020f160b030105090712020c010b011e0e04020315030a0606140a0b0f0f090402192a02061b0a05070609151e03 68
    0x20b10300141c0c0507004100090500c1e4201c0a4002c034120411202c80c034041d0703865031200500520103010002451201303411501c803034056410b07001101c0143c525454031880001e54030b04072110788200d00c1c840c01ca0044c0080c00342c04214016103940510300340c42e5a0800301846070481002e031038042000380d031038603540b200c940c0c510261110808140003c9200c0440800042c0301882c070403402c001d0b0640c09400c044002e42c101c4d4500c4000360741075401588130fa440300921009070a03148a0305425000300c00d409810002203030300c28010303101907840f050784840c0008144801032040d40981c480c00001004007900f1001c3c000c0250115030800d101a9141c11a0203020405903040024100358011005915006142e044810489141081800c1c0301b08100020800c008280f030000010340503c04c0080c4000001071041307104188010340f88126801201c103072034044d60312060f0740710300c0d000900da40f08042048182d0141240c0c41000c00c5d910f4188240062000002801004012000703060b95900180090038207030701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 927320773 1250 927319523 927319537
    0x10903020a2d05010e0d0203070b120f010803070b0708150d0605271f060b130602011103060d120e28140102060c070f0f150b0306010f1514 61
    0x81c14450221034124420419600100b5182000c003000d420b0240e030740d01181040580078102d60b20040c1c4d04281c004207040180d13903000325120010015a0901c0c104040449500071070700481d2002440c2c2e40d90102301e0b100d02070400005c11040c070141c080f0704a2885008500d0708081c940034080294190381303000074407094452204440072b50b102c07000c020704008d140c921400300e800484107200c14020740d0721050345c4400c035502c409254052004032400a1888940c02000a450003180ca66540ca00b1864885440c802a1154400540c2001d1051025000c3c03403003580c1c0a0340f8060b085030b01e003502a07640c040c41c040c0f6803c801030412505400080043d9650102c0129018102c20741031081c078100322401080701d04940245100c4144510905000c2c8da002a0300d59001c1038a480c2c503501c42216140c0b241224010b0751001e441e4102d0040c5400c144014818940055a1804810000b82074078106058031034009104414200903000302c1003151110300d0201107240482e40c500300d44070700541080490540c00543d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 927322023 1250 927320773 927320789
    0x1f020c03120c0c2416020607030222060c050601060c02010813080c1005180309060a08100f0b0901120506090406050a0b060706090201111c18080f0c3c010903020a 71
    0x44d820804036100180d00c180c205a0130b200303148055403031010117903030703440084c0036001019030000740c05c9440568180310218808040ca400f1401d41d0340c40b207004040c030075102015a001d015410001513110301400b818626158180c5981d6460313618002c42e008075018054040d0342c8203c007085500404e0205100c11045441c1000000589040840030800b0100801103210103035801000185c0940d62480c003651f0f008042c0d8a8980c00555480032841034406d0355500c00c2491003040035004c40e1f204d0b80304000d40071404080e03030f076207440e541c1680020781a160140c80950700015110042008101071342c10503648660524070200b0180484004595a58400b46007607800ba56180341c00e808569014244841d1114000300604500c0210030740b00310404100302c0749009000c4501206c0d4480540170400400900c0d2541c10f5a044850035064a40c075000f1001400d8810100490b8407009080a040b05280355024502c0c80803c0818503070140038200c8031030003a0f5041c045040000401030760b0320f80300c20000e86000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 927323273 1250 927322023 927322063
    0x20d03021303121107080703020d02040905160f14060315280f031a07171320010206090f0a030c0812010303200a0f03080a1d1f020c03120c0c 62
    0x110b102509102e12078102071b0046e003210108202680c2e401d2400c1c980c03250110b400040030310842c60020704c1d0443d40d40f0041c10554224100041030b4420307040c4101151900c20300030b1540341c09281004103606c01203503926440301052403030800c141000010100c46000d1031400c214a1405000085640d03041079201c5500044299000d00030000c00703d0343c0751003a01c04803441c03640c141000100038240f0384004e1084c80c40a9101000a44150300718000d0f1485250481441c0800c0c00700c00e034449078440032405a0034054032400c0c0c040b441d800d400041c202c600f4291a006000000d0f2150703400c0740d05c2d640d0307480181c3e20f0341c009200c030b10400001c402c40c147c025446a101d8000c0061000c158081e2841138510123011038002c46510320105407904c200300d261540c945031404507603443c1903c1c4001004104040d9840202000300202034450000b000400c40321150610082102e140308403200740d01c15440301c01096001403041e400b69451021845401040745250b1906009403000300c10b10b8420144e003015203003055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 927324523 1250 927323273 927323297
    0xb04060b090a08030a05090d030c0f060b09060f0604061202040b0a030507020607110601030609020d0b072307050c10090b1303110f0d03120e0a11040c0f020d0302130312 74
    0x41202c0d8103008200300005507082c1400307544090658010100124040c040c102c600b0810103100b0300c5007868240d403091518051284bd81804401450f4041c0424010802500843da503841c210340800840700d401080146401d081c14802c0f507004100008d40c6c0030b015001c0c0008180ca181c1500500b0000034240d90014440c6000d45009190940c0500b440c1c00740142489038a5a242003c00d6060550781c100074081550a010320125406100b1128041c1140321014144075000d60710842c030407402c3d14220700700d00c1c0b0180d941d07180e007015105028009126a000d40c0d03520145052181e00071031402c0c0d544c1482c200d400e9650390b07100103a0307200c54049074506400200520800411072100300060f0320960303002d112034644001040c0c0040354150081d0610400c0a17001010b0016034108984695182d0151905e0641c9441c1680d803423548600e4452145040141c01d44c00b20303108098a141c0458554000d041010310310390207170004e40c000c41400414107011040400402c3e0f08103006d000956103a40e0304020820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 927325773 1250 927324523 927324529
    0x130315050a0b0a060e01050a05160c0f14060318030c03030106051e070201020a020d060f09030e040e0c0a06112a0a091104050906060d060806190908030c0309010b04060b09 75
    0x14180c00380c0d202d03065410b000c4c04034aa00481e4003591210031300b0200e64582017064182c0e6a8080c104600c81040300090f908420481c481c00b8040c220b900060141c00d115465040340d40728180c3c603080007a0004070601c002000950400080030403003028000341c0b442c2480b080314850079a4002d81190010560004800b19a0304c081d840e00156000061529400c0011070f0b40004c3d00c88000c1400a442160561565805c2c000d03180d110070425150014104024051403601804c440464107505214920f0082404500e1201140da444207000c0181420a4142020b0046d03e00303c0c1900b24012061043c442d0704040c84003440e0306008829800040650000800801c10040401640010103518104851101a01c22003010348094440407140004c00b5076460021941501400b034210703207ca41011000110b08902045030b07801421240e01c047c1c03001129011060551303a560b003006050304000c00c0090400045040590b410031108000030843c460202c1c00034080d0703401600801540f07600054099042e03d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 927327023 1250 927325773 927325781
    0x402150c0d170402130f06052d0409170a140706050103021c1e050114010605130b03070807080a020c071707061121070b0c09040506010c17130315050a 66
    0x50100c042c0a203514050f408a03400306040382884500548803010780c030420005400040c0601809018031014801100725103800d40c00749800e40c0150264101c4c40c12580c100343c000c4d012183c1e04402e5a60fa0424040b40d40b0b851f5611800c0b10700100a030034101d11070024450002440411301a040102e0302c2d5065004002d0810000b07500040d6641408803600300050342d44a22000305c807114440c000c0c540c8241c0c100b481c00740c54040268080c4103c500d002142654001c4003410046882060003034009482d000c80d61843e20003130324450049620074002440c060300c64031829030b010841800241c140500308100d180b4242160300802148048480c00048583d003c000d80c00061000740b400075240c07600b000b425a120203031346000d030101c040400355501e20000640101c0d40240d6010f01c146459145c000300d240790302c0d0050030a052080307007071101103041c42d0311813001c200715150440f24002e140c01c0302e20b0b00444142d1040c6c06900305104680c00c00004589500f040100e03202c40c08030046418074100000130101c0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 927328273 1250 927327023 927327047
    0x2040e040c052e09030f050d0e06040305060610090905040b0109050c180d060608031207180e06010c210c0b0109090f0b0a062d0609120b0402150c0d 65
    0x62003007102021038103010340f804a8000d04001c00145203100c40490884080d540c0b9000a07051458020024040040000d2680c1c0704000079038a20b9a101484801c02100741b18500c0302809603032040c00810f08918103011100c10882c060309200d0006561001010f0690302c08507070035600110302c20010000c1024034050194481c0f131011a0728681880100c461062480c0d0b841c203540507014010501e002c2218550040003d8810002142e0300c070000000301d0443c0c0002202d40030006182440d4141400540c17028250641b1074030744000b44640d1340e0000440b00003040c98401e50300c075221181c0c2190840946420120041d129981e100c003444010f00345a8603002040e0300c0001d526241c40031040104041141b0030046a41c03003035040300a0f44500c0f401c000a0300e234a8002e40001006240e044c0c00b0b014986c0c0b01d1511182c0106101450325955420a44041c2c42d10300c5000d52003401d083e082800110f01000b2180e00a01c0101501558480b601e2440e506030405418100180d0141c024200e9035504031080c40d5039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 927329523 1250 927328273 927328279
    0x1020c0c0916080a02070803010816080706090e06030111030a14060d03050403020603040809031e0610080303060f15040e330f030c1302182b03090902040e040c05 71
    0x703070b042280b07101d1641800200044100300d0404041160312100b038048414040d0082c0d43c403500c03543c492110944800010500d00d0105428510020746e40c1404100c0c941215040d80303070414a9868285058008000141324541c15581d07444010390702d043d2440594001e80d88003000190800080f018883c200c100075003080d05c50f410424900f00002d600404540c2582e9043e9144c50b225200ca150071403560191640c1d00c5e5060094456607500c4002e80230000c109100400103c65185d2155000d0090720304180c01420f0094000b00000360321790505850445425502400e84817070046d078642d400071640c2013070700f1095082040744188805001c40c00e40c40e1004440d0349103c4001408022124445152a41c101c01d0081c41804210803041d901400807070314102018054a04100110250500a5012260341e070054034007003e0340d04d401d04000c6031401e81c2c01c07010380b030742c010340941908180c200f0307642c2413070450810405080110303145000d400640003c3c1141d0514141d44d04061901040170b02c2c4907007020f80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 927330773 1250 927329523 927329539
    0x20d090503060106031d0a06050601031b08150316090902040c050f041e05060a1205150102070b07050f030d090201090b070209280914010b0627030a1401020c0c 70
    0xe40c1d00402d040341103412a00b40002e00e81c204000032014188510004032070780c01740e02107040a001d056082140b01e02026a0100401050460100c9840000130801c1001070103039000100d000c01c41150b06005100300808451034240000e10080c0458419000441880d0721189000214202400703a6003000807282841418604403424500e450700692042d4080c1040c40c403520314030140e81600304c6000d000090000e40d520240c00c2405404488051408079200b40b81c0700000e0440d4440c007419480881c0140e0142c030300c6901d0a00c510031150040d141c142c40038054001c01510703081042004214100c0d0300340300403c03c90b0046c0005002c02002d6404412710070010405040180d407202c60169200512920010000e8503c20080d00c3c7c10f0141010b40c4007891820212005101000d004100c0b03100704a00240010012001030007500d0094110701090003c04464458034140c40b00008185118050100c4a005070f040e207414241e01404025007001c0e9500280c403050529091104031090401510302079 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 927332023 1250 927330773 927330779
    0x3090b0f07050f3403110309061c0b0a0e0a0608030f030a020d0b04111201051c0201051621021c021b030705060705010e0d030b0a050d030c0605070f020d09 68
    0x291003407107204070b030214000c1d000540e92508a0400a40b50610f000f1345590000d045041030b00302801210380005a01084490801000171000041110103034403001e400d550030100d180c07940c0f41c1c039403411030800301c8425200d4100710131548410f803c2030000c2c050118151400c0c202002d4440448aa41d00840055001001001c000c000802c0450340c000100c01801aa1040c002080070700404680700029481810302d0480c0e40c8008800010b4043d80104040500e0301d80d80c1d80080010b40071903028484201d4010f025440090343c020406400007420760390030b07020500d40b250b5407402c00c00118230001c8040c1070140c0d072003180c40d98104000300e4480741c5080030078101d4803a40d01c080d5990059400540121114242500700d171303181405550020705c0090a00ca86a00329440c049010700442c440c01180740c8104440131002c54401d02600e0081d54010300501d2050382800107008124440500076420f201c2d07045500c8000510922403240319444590f40e0710660020b6850080c1401030707011002c0b0401500e42c41c14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 927333273 1250 927332023 927332027
    0xa061b1119050f060a270b0c0c03251416052205010b070203191707111e0f0a060914150f0c010c03092310090303090b0f07 54
    0x10411849920045041c80c0e206450800d1070190403604074105030149006010320400e0581224034803115006001100000a203908500c42450782d5001c0c0c004170021010800b007040440c0108100643c410540e807030703e0140044801e021a8183c180344a1303034040c18100c1705025014006414050402d8003030002c1078940c882c0c042c1c1e111414000e040c0304682131915044243d9500229040d080c2d5014002e01040d03030340d0000c0300800d4128404c01d9009000d00d1006000d41100508118505170f4030580e018031072030581080c2d0a2980101e481152601448403904145680d2082d5803000000c1e09229182d03c9503145003401007070002003012a0094084200c1401400d41003481c04003610741c5005008542d00400c8002000008000e8100040c20400103405840e05502e400522980b42120b000740300035022100304800700c1d0390042d800740c88071440c00c0c900c10680181e640807046e5444d94400325114075810010701400c6034448102140441d5594440d041000045482d00340e2001030f221410403a03203012040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 927334523 1250 927333273 927333283
    0x10305100b03033a0b030304150507020612040c0603020306030c011b0807150c021c030207150e010c08011e17030f07060b190605090103090807050a061b11 68
    0x1030103103580318074040c1055101002641d07107100b003d040c814940322100d003030111004418400c0b001c5000ca911418820ba411900500807203200140c0118a443c0c0307824070309440109400084001c0050422400026031b841c1005048103130313000c0c0b04401103401c0034034088510020070f6210038141401841040f03520703500410351401c8850282003601d024482c0701f500c491040081c02004120b000f0101c1d1080a021360400b4400001601d01c00401012010100c280d0b5542031120210100900303200310b14070080e1194002e0845a4403528090703d1340e003c01d45404040c0c4240c0e107031420b0107030740d5509400c00f000e134004192401040d804c070441da9990304010340402c8283c818000e1515500b507404151040f010100704640d1b245c1d40c20318025460704001d00c8c1ca400a4814100618030032a140d44d04680b000003c0318030710040704c51649596242c2100c2800640282400300402e0b41d03000420300244021403030901c490b400c854403811000402c85105a041c2c004005000501c034100030400c840c0120760100014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 927335773 1250 927334523 927334543
    0xc170105012102030405010c1805030c040c030e01050412170105090a020f040e0903030a050903210a090f0b06040606090f050103020906091f0e2b0816110103050f010305 74
    0x1a001c0484a0082c4440000c0b4003081240102c0c18070000420003880019800f880380e00400381d450010700483c3c05212410b18845001c2c044e07141e008520889010b10302039001803407010007800c2c00701345105480d5031030b402c44a080302c0c02d42d100000c0c0d80ba4112890380c028856001c00c10000c0724a04036504100200340380c03a000602c3d6603402c1d640041d81e04501041003050342d00510350f2881411292030203100c1c0c3c5480790401d6171103036070550601c008100ca6101c080152580d183c020703480c01205a01c251061200b4200c0038281d02c254503a1030300840b02050304882d18040d450b0195004692908110044c4012a06603034004001c0283d526800d015a25855203000700301c54003441c0158680803a100000c0103441240001c90f400081e640410310342034520a46400140d203981c4548007038881da00213108c0408124a18240005160b4030040610460b006c60010340a004000484c02c09a02403002c1c16503a40c6100c00f0b8800b040120030310b81d612340c1c1c10b010342d560110b01000d401440354551754a00c0e9881580b00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 927337023 1250 927335773 927335777
    0x4020111031812070b0708040317040b03041b05031002070b06010c05030d11090a03060b030c031603140a08040b12010501022407140301120b0c040501090e07030e1507030c17010501 79
    0xc0f0ba0312500480400200d005043e03840b100e6551110b0314030b003031102e0780d02070305c821254911440e082c0402428082c09850854500605503450343d6541e5850410920400c1c211003441d00c00200c010805460400c40da010f404941480140e0b51441810b2510f14028014041410001c03450302100000b1008004d56102d80e0840c0000304100328035111581c818051646019082400100004107000d540d801031407690344243d05450340d42d902c680a0686611441d10040140400d012041000502c030750722044032107031840c2c140e0b905500079944400e410b51281d03010041e000804680c8049045402c8030490041100340014995002120341529400c4040701202805407690303c0000c60140c012504024030036004403460f80d0369a11100300207020352184400b5075411110f9000039503a04221012201a580b05031240d5407010300d03054001035200300040c40d5104140d121071111540790010828580d110102c4030901d00c0c2c6240850000b01252074a20903101000040740d02c4000a010228115065940038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 927338129 1106 927337023 927337039
    0x30304060903110c1c0309030506130326011401051c0c090509040c0e04170706061503020304030f03200d060914010303020d030519090308040201110318 67
    0x1107070b01c2c15080050b2848031700e820f4a9418800044030b10030b1400c03540e895182e6560605107541a41c1c03507120668040c1e80c0c50209500000c503171081e40c0c00c0d00303000510890120081b0a034900e040c41000f03521000344210700d40a91080003110340044e21220003031345803036107400c88078010005112124001035410390045410301c2d0500d64280030f16040220703d90054144035107080072400141003142c007802601900710303010282101a02500d03008140020b6440c3c94004191034442c0f1440032074081500c10001c1000180c0c0162107a456941145070018040f00b410410141440010905100700c0201203800c0c4010110f60f040241502d000d01414050442c104070034542c104000e0000501603049540b0517050544079078801c1d43e20a080040c0c15000307008c42e65241003112144103060f000900c07158208810b55030420b18060701189454011483d00d020303020750212054200300c03841c0c40340c000 = true := by decide +kernel

theorem cover : BRFrame.Cov 927158273 927338129 := by
  have h0 := BRFrame.cov_init 927158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 927158273 ≤ n) (h2 : n < 927338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
