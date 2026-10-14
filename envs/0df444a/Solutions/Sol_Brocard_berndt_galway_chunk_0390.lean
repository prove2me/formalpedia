-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0390
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:34:08.331975+00:00
-- url     : https://prove2.me/submissions/372985e3-fc84-4b6c-ac02-ff9f240ac1ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 69964031 ≤ n < 70143887 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 69965281 1250 69964031 69964033
    0x60501021606170c0c0604060209030c09190e030403060e071503050906070509011205040507080f0f0c060a0c02060d0c0908011109040207020409120503011e0e1611150405 75
    0x1a01d0941c5a03180001c0340b40a8031001640d40000030525400500081d9009140501c4042c45c0a41c0300c500c10b070420500390390413250f054000440011500c0e0810142011000464030540c0c40e08110b01c9801030048803001a103042a1035442004004500380290750007160420740c01e01c038078660b1209041c1c0f50314a40c0a15105502c040303e5034018103200703200e800d00c204029130040a40b0348a9000a444540040c0c04140c1000300085020200d01814000da41c015481003004003a007504201c0712605184000e018400306138040740c590221000000303502200600d090742c06a41c0c401401c1821109100700340000303500f129000820701180015a44070090900540d80c959064640f901281ea00740c854504c3d07041030007102030111458601e0140e000300384d5148000e03c00604074000356107044d540d019000070503022400c00700040003070ba151002c2c0d01445c40d006440c120201c0d070510a1880c4c00440c09840141e038407400d102c88642c61401229040c00a0060004171580c04c0d101c980c8088244404544c120b0fa1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 69966531 1250 69965281 69965293
    0x6070906030209011d032118010206130609171b0d0f021b04090c0806190603030903151116030e060403050a080f070606060503040302010b010c02060a03020c0102130906050102 77
    0x2918468403d03241c18001c140d6a469841241000c011081034407400501e9050040706481c8858040516003c0c580d0040301c45000d48605161f00110101d031454800c103419500700e4001c210600c00713803645440e00d0702d40c8a940010304040c18206142100d10000325040840c00000781d554036000070740cbc03000011540003070485181c6005201c4c101c1d40d0500d41d0b900d580250303002d9443c0c8400c4121100d040c40c41c01c50f0160000403050001e40320700810405a600441c0a0b401103414003403452300c0003084600010101c0424001c085c0f0710b64000b801210030380b2001d425403002ca0f502002e10186500b010b003403222000155515001c8002a040c0c0848091604030081040d415440c851400e140058404698011002d00000380654039440c00f558444200d403e142e110400c080000600c0c0740c4607504c054a40ca54030140c880c0b60a15010707003100c21494125043c407103c001400e0043e5110011502d031824540390150303e071403100c10400e01a0041a6280c440f1108410003c214403103d54420802c48000341d0840300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 69967781 1250 69966531 69966539
    0x418060302040f05180c0306010603020a0e0301020a0c0210030501080604141504060501060905150a03020703050d0e07060e06090a03200d1b0e09071208042304050105032e06080f060709 81
    0x1590720000008071f5059040308004000690083e400340070665480e06141540c2480300c0c000a08a911015000c000305011007070110541c00c0c040c22005400d28142010040c2e54107100c146e950301ca40003080140712505001c0280288203040c441000380102c82000348196051518003c809840709014032000030310342420000d4a481c02c2041c50000110201d055490840d201c07400310065803000e40103801303000c0200450711501c8244e01c26001440314020103041c0c0181020b00003130500960380300781849a5028040910656604a03d00341166800071300c1d11039001490960600300d15810791a687d01c03055011140d07080c42002c403412800607001d003405001003511a1903401105105960034000c80c1d04c0081c1c10700600080c001109841400ad0840f00e00b0165902031804c090314060f921200100a080c4084140e41801d006946c0946070031005080709011044164441e6065104142412004506120007078141944500050f10410058503404114803000740e0343c5040a03100c800001c0c001d04030000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 69969031 1250 69967781 69967783
    0x60504050705092b0b07020601290306040c120e010e0c0a0303090e07120e03070215090607021c08280806010c0f1b1404050c040b0418060302040f0518 66
    0x1e400f0000007050302c941490306043d0a1800b802c1c40191081e41c01844490340041041c0307944051003681664001d00f040d6041122100c4100e43c40000c41a034005070008945802e0444000d0300c1d400b41094400042c00d03201e0682c100d603d20707204c01d00d52151514100d8500c48080041d04018640c0910310102da840c040e501c000e020354446c1e9444050000383d40d10601748a490000020a40c000d50a8a00002a00c1051410328101e4410306215006a44009212802c504041d4040014211b900e541242030250072000709419114002d0000d1081c14159080d201100943c0320907241c0942000c4020303190448a10a41e003841e045580c0a003130303684600b05000c4203601c036407002407041c00306a4036204180c05d035941d04610344086040403104000c51800d0300c0a05004024113400802c1f60005201c00c04a01c40c00380800c0f100d000e403600325621003c00003400b5281d01c01c001c81e03044500300b0410001101c3c0402a00e0010f018503080203501c41d041089803003c004403500100d0140c0e0b24070303000d001c20a100342042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 69970281 1250 69969031 69969037
    0x3d050108100807061412071d0102060f0a0b040905010c2f070b1b06041101110c0a05010f020a0b0106030204140f010c02091003080c010e06010e040302120304081c060504050705 77
    0x1a0007150301c00f042c180700d5540700b0300c0c4010000303081c1d00f00d850514610781c07030b555100f0030102c80d69400203d000600c10b030011a43d40f11740248050a002034011420320b002c01081d4410010480c41c4503e0300c80c015140c2e981c40300da00041d40340d601f00303008028205074540020198a1a101900b400e090790520144100418844601c13140341404010301604c0d2408088004580020224a140500002200c2400401030081511540c420140070342e01c0c0a13090000b600f10300c01040c01d0105a4402d401c04200f40c0c455210680c1541d209092207891141a006e0491900241c2e03032005201d03400c5200002242c0350560081c005599071069582d403162544000d0244030a0000c130111f00160a46174000e0240c2800e840d8990001e4204804d0301016032a900c490700141d200c4200d03e142c581d55004d01c0c01d40124180301c0300740906000c1c01d842d52141040d1705c3c02075544401c01106103100400001180c03c02c444181201e100c0e5424004081078003175280c020100800043c403420f80a181042d0000c1c2c8814494811 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 69971531 1250 69970281 69970289
    0xb0901020d090b160c090c030504060e030403051e030c0d051305010f0e0d0c08030c100f0903020709020d0b0909010c0206010605040b1b010603051203040507080c093d05010810 77
    0x740f03130911842c05403400e4189070f010303410f50340b6000300400407a00d0940c078080c81d1842507072502e01084504003841e1403822203003505d1440c1d185420034082400042c1d030214500d02c4c0340340d031407460b6842105030710a410304620031428248824400c07070071500d54103600a0050040c000700c03015003d007040e80d25001982c2d806044c448040001c0d0036541418150f03d0b003038601c008054050000902210f4446103960300c1d5a1000b02032902560042e511681d6802c7c00d4018201820f90105060045800700d030703030203540c0b0341c25400713074120240d00802c40704028005a4422906540700600150240c10100c2100d4028265400a0b01c018011032001055480c000e000315070880310640101c40c0f4040c2c19588010100107210311444080d500c0b00c1c40000480c4080000c5600030000801e6540e5904162030b00754607000a0342c1c4040403640010044185c0b43e521205519407001c00162445902d007082c0d0048110500301c02c60300d04081504c402e031040c44900101c3d00d101542c80c02e0701d4200c815140e60760801071503151441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 69972781 1250 69971531 69971549
    0x6010302120f13021003140c0705060705030406090606030c061e09060e0102010612030806100309020310020703020a050601080313050405011211030a0807050d0f18032009010b0901020d09 82
    0x201140d44800d4100b01141d0101003802e000c045040d080e400646400c115802d410006902c0348800d403003070160400d0329600034841c1c4260900e080e580b603440903150980208100c041c080040300141c1407103455007104c5642035025408020203512031426854102c010b000f41c80020315159405007168569180720310100780e9a03111064054603204081b21081c078003404450455407036120025428079055090b5005610a4941c4096071402030148200d040b110f1183e00d040508100100000d43c4000c51002d05800c10001c000d691440e450500740e1500c1c841040040c6248590380001030b9480003c406031014180714081e2441041d50348040000f551021700606560038400c03503800c0d00242d407601c1c440e54111006000d07a1400e09542d00d6201c8107400c442d10a8620380c000491041d0029406040090240301904181180f0402030040280c1c0c4151800300910000031803001c030548620300d5905803072084006003001000c0d030315104e402c07045810005a8034058450b900701802d000c5d00a110380300c02d440b0b00074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 69974031 1250 69972781 69972817
    0x2010e0718020c0601080d030c05040e0a090c08030d0b0a060c0c1214240708190902030102091003060e0c04080d0806040f0204060c0b2409060301180b01030b06010302 73
    0x5508100e40000e500300501e99080000b000700c0e803018000140240340c9071010740081102150058162100c41a003071007005030400050001c5c52002900580001c142070300010000941e203400c001c10203103500150440c0c0b00200340c0e10041a07507074000805c04239040d40c510300038640e6030000b035442c0c0304410001004400e00800910010507032030401a6036a004501319801e07040c0d540c4c02030f030810a034030303d000c034001c100300d0b41000710340c03100d40030300303500400d10386007038185482d128151804081010341027010260b00c4800341029503600b501078844d12070340100b410107075502800006d80201014450491200c807024005020342c024907096404a03070441025000c6014001e01c00c54185100400543c0d1280e17030b40c80350a02c130152034030140011303103400d407500e0b00302200c00d0500e140050b1006080000002446101c4e10030b2900d010060962028180c50003402526103000180c054072040c0040b0103411580c1500d07500f0320000003480c81c1200e00032010610962580c80044013139124420151150f40c03100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 69975281 1250 69974031 69974039
    0x403030c150c020f010e030901050d0f0f0f0204050a08030702060f0c1203040f0b090d050f0a050721090605030c0921060708100518040609140a03120b0102010e07 71
    0x6468504040d9214450400000c540c0d01940300440b08002408030042c1e00024241980b00c01c2449841c000c01020001941071000c3c58000818500c0b80c80451804a40ca9064048170300e002900070500301d2040700400c0c440d0800c18107001009400c10300c6034074030075401e42500107008400031045070b040c0f540182c4028505194081460a02c0c0c2c0404241b18261003551000265218650013442c001c500c15258003001d410a8140348001c030304054403000c51754002c5074840320304035041011504080d0004034480e48030704031580c05440038080c00740c001d011130910603203c001d40c10a078410f02d4500072007038942c42c1d0076944401003181c40c1c2c0411500903035248000c10141c1421b01e881c03c0b13407210312481500e42c00305040c0a400f046081007025900c81000c04c2a04081c040e200c3d070301d80d4200c80a00350a03201000340c003803032000302012000d02400151141d0307a1100b1100601c962126204200c0510070101c80001c1c43c20701d00140007441c030645050107039140004c503081c00c0d8818000e40b507015821070014042ba03410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 69976531 1250 69975281 69975287
    0x30c0233091204060509010e011803030f020708060406021905030106080606090a090e070503010b010e130c031b1e0e0306070e011206030c0e0a091709060f031f080303010803040303 79
    0x4040c0c80348100348503110070210080c41d10030040003e083c4958505e504e030704481c00003408244801020f070341400079100c1c1820b031030070f03c10789c0410803260140b906c03800c400c00001c0d0a03070802043d40c20030321160040900b040140f115a80041441204582c01201c0d1446c4000701210f040c003013070081000140018001c50001c0ca0400d019040300d000003402200269590007915003154200399030750b00ea9403c0034804004614003845078600d559000c1c2009000c209c1c80c4000180511440c0b52185840c41e07a0b1078800714081d1103580902280203140c0f00920410403140c1e0043e01c0341120f01c02c2e41d0f40b08007032680c08940e02d6200307292801c0302c003501074010115038607441c40503101d41c091001c5090402c0010035140d4000c00c8503000721801540224001d01c2c04908195081340f049900801d4640000d0508000b4030008158030b000141c641b40c140041610350001c1c40003d140c45c0301d40b949d0000304c00303008001c2c00103008018403e42d04061520715503130545039407105030b0303500c9000920070300c1c1c12608144410004240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 69977781 1250 69976531 69976633
    0x306071115180c010201060b07030507140d02030c0601080118110301112704020703050301030b07090801020706020301170109020a050f040204090f0b010807020c0f060d1506030c02 79
    0x40340306031100c00034850294092400100d80303040d081d000c8000904600b080c01e201c02a42c05000388000d01005080241c01d4800d4482d01000904022000514a0512450160081c2d14103883c509940803c007150384002c0d6290003d1b01e1000040c0642000010681814030a10391603030042156030120044586452000c1a608e813503c54255480b10445000c1041850041808207440f03604503811815114000c003030060b00140e103901940c410020340c4040b80d008806e0700d0440e60b009001c440c0700d40e0b90070421034000496a01c80c200c990f0011400d0020005d19401650681b213501840c103010741b19035071990782a10000c210194022071140b60070300c10b0b41443d030440c015411000d4009441d05585205030411075840b6045104540e60703d5080c545d9039a8048072250700000c261000b81305403852140001c0e20031003408985482620000742d14108007049400240103544400c86409a1603a04d0300060050040c081e91070700140a407190403081c0c0145806d100c60340c590003044080500d04c45400188580c0307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 69979031 1250 69977781 69977807
    0xf0f070f1218030201020d0e030301140f030709050a05070807020307020a0e07050403050f062d1314010e06070f0306210503070c2c0103050a060c0522030c0e06030607 73
    0x40d0b00d032032540c4030009410061091031403283c0d00042e9540402da42900445003400b6080c005900100300410040c280d090740d40d10005811180b00011880b44c0c40024506100741e40302c1200e03281003504200041d1003551040b88075502c9034417001056a204c11040f41c41c1e201d440002580110528024054040c1d413030b01d0315500083c6410454070300741c2c403038442620300780491100d480d007544000704101780c829043c09210a50107600e5a41c8402d52132010142500110003007004801d052807000c0f100a009128600d02411a040c000030803402404c0c242407a01c812040755914040f071840a10217100078481c0c8a00b0013150900245c400d0400ca0a01320721851000300d400a40d640e10040c810000411102c1c59080014041e201c0346014010002c91400e651030801802c0007161011200100302150010030072418259001400082040d0280c030183c071540144008035007600300520b54000442c5042c0382075400d690040d640c10020319596405501507620403101e464168101c00c005c610f407030340500c0b007044c010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 69980281 1250 69979031 69979067
    0xc11060f04030e060c0109060b0f010f05033102010306270506060c0d11011b09030809180709090b0609151606111c060308090f030705090a050f0f070f 66
    0xf55a6620000b9181c1d00704103144803050350350b10000d60401945100c0c6209030141540c1c4019880f119500107862020304922100500038000002400810a680825002d0014402c00140754954034114201180c0d060412070101c1e19110001c146000485240850251750f140c09c5026800c009454902920001d8049500301c1418041100301400a01203007840e031030180d030b807407040c1481420001e081d14801c0381146e041c41d2070304c4040118254010348034401d894021610b00d0b505c80d0400040fa0a8900d052541c03c1141050340a2207100c581c03010071482101d5101d607090112025a208003c03244c0702d0000c41c160701c04a0f07041c1480d503c0300a8400b82c03001c03001c211000024600302d0341340d00040e143c4900c2455010900003900041c080b255007031300380c00b02c40c4980c41000814150750701c5000a01c207800002d4421640b4030030240b2280e808101900150101521959203410a4018030f8007810040d20300b5400f142911001546449400f07480d01d00c26a52650750b1807401d4103118060f00c088200701080107075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 69981531 1250 69980281 69980297
    0x20702040b040c05070b1005090f060102240a110301080604140a1203090213020a120b06280818030414010912030903050127080c19060f0c11060f0403 66
    0x1640e590f0f104405081da03040e15850b507a0fa03054600400021b42c010322048203010780000c148210749030b4180c00c03070748a6816010308109032900d034010703494058071451110105a40031300012052450100c202d0150f81800014440c4400501d034120440c0824010749800754460320002d004540601e000301650314102c4180c80b11039610b0340f2403418052058101c0000320742c039607500d1021418641e05100e444202640e0841c00d1a110b5803004040101c2c0020181c6101d8031851441155900d40e411a04d1004140c554481007d100c41442030003041420806400304114400040103105003c440d81d00021055000e945094100014000802a4004414100101c4910224204001c5424080d1071030094130303507290b010b00d986001c600759410099074102c0c4183d54110000d0082c800f208485680360b01c14061070b26800d0154040349006601c100d280a10002220980f0900a080d400051249a84034091041c000c20300c2c41030364811691300c9030f28260360120000034144172403003211581052092400c048 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 69982781 1250 69981531 69981551
    0x40204020702120601030b01060e06190e0a03060e1908030f130605010305150709060e13090b010618050405012114121b07030803040f03090e0c0d18021302070204 71
    0x1203000c60301070301076103c0e600441c0140140b044d6600402d00400061400940c0c0b92036102c0403600b40c3c0540c0f4560509900d00c3c03c460b2912a0260050750405c1201a0802c25602d40d641000405044503021a40741405903510b428401c5008200a5860503040791903d0301d90703260241403c5071480b00500d5201900140a01c0d840094107078007546000314002d20040402031038041a4510381c60002c1c08035400d120b00c41908101c0700790010b40c044004c200481d10203014500802c258400b600144100900000640340003140490f0020000800f5079014544801d0b01a140d405201c12180c084c010200f9005a0300781c1c03640c046c040d144241c0c21f041d00c12000d40003548020200c461420302031701130120801801084d01c95580050075126035141e0111030007000d481c0d180d0f07110100984400b41000d08040111214070043c10b010b461000010907919121001c541741c584c2c8154140e8008840e900d521340c0c240042d10300d002c21000301010200340c0040802804191484040d0000e5000100c1240c100c2d4840b00d801e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 69984031 1250 69982781 69982789
    0x30d110304090c26040b15041b082508061c02151b0304030b1501200724120209031203010b0c0607020f03030403031508030309011e06050f09040204020702 68
    0x283c8151503480d2001c4110501e400f4a1500c5000307080d40d1181088542004049070030121600c0c2c02c040c1030f03586102c134401c0480c00318024244010780d5164000c508140810b290768010701e030708c0c1715038a42800210300d2030007100d410344041c1068183c040090b40c0600492910f25080c042224065a02c0c540b196200b00c40d0b602041d5201d04403503505408040120702440007a10281910b214001800040d40c6058216610300364400d101902d04446002e40002c48000c5134001d0790494200301c220401ca0302c000c3d407880e418654581d658000e0200a02c295048000f803c0281c81107043c031450356880b00b841d00601e810280009401048929030b040c410b0461052031500448015406000c2015005594810300121940341010142c1004219400000070040e01440030094035041681881c010923016024200c00030052003a800100d514000003061100c4900154000c0c044040d40140c5030250300200041081100c00900c26580c000c0b0080c95107036001c1c40d24904460780309200800050405405070049 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 69985281 1250 69984031 69984041
    0xc0605040501051008010608030708070c03020a08030403060c0504030201020a03080a060b0d06050f0303070c0b09030a060203010b07060c020c03030f1308060709030606080d0e040902010e0907050d050105060405030d11030409 98
    0x41e2400e941d40c50500a41e10b244140c100e014210765802800020301d4840855600d2103201806000c042002c00c0040030010488000307801507070010803142c100382d19401d941d9105c0d802444222101441c0a94041c00d850044058504034ad405030041c107045881914203035607a80006050300c540030744c0d0380c43c0811801208000380964902441c1d0000c0d9450030706040c80300850701d2211440c0311303074005d128200000ba400e01080c42600e8041a0064440c0b80c180c0110f07140a4444030000c0003180013100104940341c0501c0a8100a4052401400084a00e18041e0b8403500e404400304d415810801141582a4a12000302904a00502c2550b40582d640000a041141c151001c1c80050022076080007800f10314000c0d00040c03c171100c050b080ca000c0c1050043c3c80000c500074814000c0383c40c4d80038442960301422076800440801781c00440c103841c142000910a070300c000b401d103810706d20b04400442d040c20031a09581c1500c1c0003030002d142e100b100b1102a5920a60f9500e003c105100801012411200500403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 69986531 1250 69985281 69985283
    0x1140103061412011e0e07080115150908070b030f0610050405060c030712020c01080901151403160306050a0c050304050309091803040e1006020606030717010603020a0e070e032b0c060504 82
    0x151180c0b0980c0e41c58148007803179004002c541cac14581320180e803000781034407182204c45c450310010742e030f80001e042620300c01803650202d49280240180020700c0c07494030b0000c500c103c92454240123107596070410080202c00c50004240091400d0000744064203100008016204d2640c1c1101d0030303c05541c0c1e0760665200c03514403640c01070300005140c41465030418500c07a000b81e0003800901403a007910140d012031405c1407041c034017441052100302c1c455031070500401c4100103800700e82000050310307420000050502601c584041c9881e001190a416104805690185a01c40055858102040204400c058000d04a0380140302840400c0788482020070060005084100418246191280c0329421503100e40c0c0c090403e542009080211070380d00843c000b000d0b28ad01e00c0031440d8801d60812001d00400890704025004200da010101f04541170b0a50244142c0c0f0070b994a154064005007807685a10038807004601120400b07440c482d440c20080e40000c01c2030241d19254100038500d8440c10141c0708180d070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 69987781 1250 69986531 69986591
    0x1030b040603060e12271f2c09010b0903030c0604030e01080604060e0402040903031803020f010e0d05040308071e140607020729041208030114010306141201 69
    0xc01c145141c2420b00031100549074110610307081a050000881e403058000001c640910071342002801d00c7e0b80e44d0800e18040300304002c010b00c0c4c101c2d40f00d05c000d0281801c0c14884e09984031a8a1410301401c03108008000c226401b404c1071105903c1d00c12001c003d40c10124031079500d400700348a05e11041004105962040c2c1c00381e90f0350620104040c001401c60a4060401350040742441c400b4003901c0b080b1601c00f50810b0341500c0000e40500705043c00c42c024540b1082c4411904540000d89040c10350020f2516600c540050080109404214410380d55079202607515010a0042c442007010034241c1c4090482035005800100d802c2d103108804440460707294001b02d8210b5840d0210808284042106951040e85170005154140c2450700a501c41242180c21589030038620000010640c14034064070f0090000d4008001d00512900e0542c1039500300f401100368050312801588165271003401404100ca01c89101103030b00507007a0003804010403a002d91910341d5904c0d481405010300d500605011042c2040c0c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 69989031 1250 69987781 69987791
    0x408030f120c0304030c11030a02120705010809071a0c072c06010815040903030b090c0c0d02030315040507022104150806060409051803070507090b040e070b030601030b04060306 78
    0x40c40d0703152030141442d640020103004220000b40c00a60721200950440c4406000d0000140000d160072075880d0025009a04102011584600090310405641003601e0f81411076644000d45680c0c1c0d01c003031140351011910081400c01548640c8014810603c0800548040c40d8072910031140d0041da0715145041c440c60b1903440000d660224207540e4000b070091a040c030090030715040e00c1140000d81e040340351286548203800030801d4000d81c40f18900705005003202d0034524142c440100d19421a039100030241c002c400c08810094404003c90b0701c600d4098100c151031400c80400e00c0010700d401045c1c041035101e1007a003105160400c2152156102170010010b0f0740c0c43c100550f542c03881312018801c07014016024148141070341c900d026a41510302e64000000c242d510070601030001e40142c0e403040301a000019283c828840e000c0b80b83c4056078038956041c03000c41c004106200465000c58280d80203a0080d00082c40350000ca10f0003990002414900400c0a41c0c1c501e00080450340346a00841c1c06590322 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 69990281 1250 69989031 69989047
    0x30103020f010c03080c0318011b0e090135011503060f0c0503040b0c0405090c040602010510150e19090504050607030504020607110d0606270501060504060503040501020408030f 78
    0x501e0750398041e02843c008208601d196405030801c00068000142082d001c000150300b100001c800a6000d20418000c3c0200b5841e040300d500c00014080ca05000a281c40c0340c4201c2c1400d00a24003412551203028422504210615400c00b845407090801448800400000980391007402065244c800003894109030900d9071400708110381100d00000440e9081043c60401113130004140c0307a010b074204018130310301d566009542c4114800c3e0741020760b11028442c01e101002000001800507507089400070495a10740d104e1a0f8001000f610548020398400b00d07020049520030044c0c0051150007a207400400a00503444040d00c030302c1500698111503403002000280034040007402d8201c012414108414200740d000700d990b0b489980d030068030480d80c00c02402d529440b5200344c1d003400f07908114104051900d5102d00401000298002c0703800c03040d4000390310041105442010b040319019120940f403d4231f000f40c02c1e034050304024025546558244000a03038490140300030f04449102039403295a48900c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 69991531 1250 69990281 69990289
    0xc030509040603120e10030506060f0c0a060903210605060702040e150c0703031a0a03020622030c08100c050a0f0c020307030c0609080d0f1b12080a290d08040b0f03010302 75
    0x424003104041509160501403030382c40d95411100b12180903003d40e03540d003303400c00c1d00c1e00e0a200c070f480090855242902440c14554400945034488022050304c030421441c840000e03050300d0250242542c082020000d500043c5040d511900010096805031307142a0407045a8541c2141c08450056045000003005010180c2c5881414012110b8101410140810002151003c982800001d01410300021a6140b090091b401840b2041c0141909140a5140e241401e10060144109081c0d44103040c41c1b40480d40c1c81c2d000b00001081255101401c1010a490894114600f81c3d480700a018000e401c0e0300158906120040c01f42d40108180441c2d946401030040a407100343d40400d0290701301c11039103210b4070b0307108814a155041520302107900f0001100140a0342c8013001005019007014844c05580b580c01c5042544140504801005100a1010b180b014031600c158000e8800c0520400034500740b81188504850600485c103580c240380d00d80120b01420381c00b20104481c0c0400c040010401c500d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 69992781 1250 69991531 69991549
    0x90c12010e060c0c030409020403030c03030b0607110910080a080712092d0803130e01050a0f151710050906010306081c050f040b120108010c0c030509040603120e 71
    0x2006100030440c651001c00e9440d1a00310103420280e46010000e40d910b0980030030001e41e4050a0a03034400c641e156642c0c50060061064040100c01084c100b007641170451802d82d09844406070403040912011012104220050100a001040d00c8001540100351584100103c1240c90301c1440c010360b42e02c140341407505a020290075140c0402011300740070b000e107030041ca103903c8141009a2901c0d00c16650780c0e45501d004086170b000074410388408502c00c401600030500800898a24000d412358607625042031200c07509460058180301414140200030060480884800c601741e030b850007011400d260240030b40811001c0d81d11108001d4072010900c07a030b01e40714001075000300382400c041103524034245040380c4035103800c900c0b01c013440c2c04051075101281c000e504451144031000101d83ea1640c8400300c0d0300e020f400010b425078014941c10000300d8000070501c51040b02c0d85040d100c650455074a542c08031003551000b580d60b0b03042501c84600100060b07500752150a0003800b51224880e122000040c040c50314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 69994031 1250 69992781 69992809
    0xf1406090316020409020d0303090b0106030b0d0201050d02040f0f03110d0b040f030c0204020a051206040c0503040b04031202030c03012112050705070305070806090f063309090c 78
    0x504440144030503014004125040907619803030781031640200740000350092100e40d07006500310085155503002c05a1540c014265a4442c688030140c59885407412005c5071130f041c00264020528403502c8000d58003400140c0001030b00008013603d0b158841401141101c055030041012401039481801009034074581758030001001c0d640c0d0680000c0e9500e90b040134880c0948003031307c000c8154400c40c0c181407150400391100394016000f0b560310030031010010907640c0040e0400c0074007a11364012502034500390248005c010080da0354207041d80c81e2031316071101d05007029004a081c060440c08240c040600750021f14800c0840380b1049450398900f41b869080a103012640401c1d1001a010540000d0000c034440c203424402807a00d40d4580d401031414901c0d001c91500301070301c94401c800340000c8a4400003203540c40350120b40280c0340c2c0c1540c10101c0c0d5a561328195411003501650401c0c2d04103110344030383c0034010101e9088070380c3e0440604031b001c2100e81c0c2040e5400c4a9a8100c40c2c440ca001e07040a1151030010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 69995281 1250 69994031 69994033
    0x207080715151701230105040b01080f0a050c0706090b10090b0a0303030f0b030102040305160b0703090b09060d05090a02090903040f0b030903041509030201021e060a0b1207030f14 79
    0x346030b002c00d91250411a00a0741216000d074040c000c0c1d618403d50080359004e040d150358105840700b4801c5400140720074401c81d4451401c2080541107944659a030302d02480202c0c4280400303031540400700700601001003420034003807420301240700800c8081c040e1440b0030703024841100c10390800380804640000150001c4110b14180410001541c0310701b5990402c8980500d000900d5608408900010f001d203445981c1c1e256001003004400d00101090900701800d40040420302547e07111080f0344140103880010b0045200d000041101048100040041130bc000704010724218880800d1400c5038025224501d05a00c00405102141412182c2c2600803c0c49001142080e240c00c965003c4160b203070060354802c00300400496209481041a64003a1012444040c400b00010000806609179440142d0042c23280704400e5240414003940b51081d031101d01d000c0e20301c0303907034141c80d040c0076022010b40b00b50803104200c07610307180d90414800b030300185200703861403d84142c9da8240075080c0a94035060301d81c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 69996531 1250 69995281 69995291
    0x305010e01030201020c040c0e0d0818010f09171507080901050106050c0c0103110412051c03022712030c0f07050406050108070c0f0204020a03090b070c0b1305070503010207080715 79
    0xf60780c0001e808440194100c602041c480c00f442c40894130300e021584555002a54881002d04002120b8050010030708611b0080d02c0d03081c419401158580c80c2d241440d004904080428051180c864030351045000d07203a02150202c070007440e42101032510403904503001441e1a000e00c20fa01c45c0a000b0540180002d02e04503007030074010601207840d0884101c82a06056445981c1d134020703c0054241c030020100207002654190310350400380d8071000ba8142d00c00340300001101e003400080c040d100b5200c2c503080c000c000341d083d11095402c40001d4004041800d038818845400d4100c070002c01c00c010542c2e071040310007600d00d03683c20049591031f19440d600f01510460910000384121b1740e0002080b94004042d01c3c0031048405d15080c1180c40790b403030600c069085400000d0090b28181c0503080000c804e0f119004044003030742c680344112840200307982c00070803a58289010a5030700c0c0b0400008004540a0419508403a64410001c1e003282d010150444032030308080303031030b805210710048418040c00c2044010b00c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 69997781 1250 69996531 69996533
    0x702070f06110717010204060807090803040e25020d0e03011a010302090109030b090c0901080118080c0106080f06010504110a020c040c09091409060c0906070f020409020307060c030305010e0103 85
    0x6400e0006014000420035566001c8101800401840009200d124900c140304010325099502030351150041e036000c24070680108400c81c6c031034141d0b1022a940300e40030350304040c141617610b00b11a001030281e040300814070680342203100310a0309105108103560001c060030340100307030040c1c22080107007036462099160000c03a5030400345040714003120b00741c00d00c1c0c010b96550320040140d41c040c4480e0805044401c0940421140e08400141085514000c891100041e039807650118241d4138184480201803174000c46010008070103c00bd01040c0306480c0000c5400c40d107400c1c0081ca0f02000407030b18149030f0b00040c01013000e403c0a02c1100c0101030000c54942c40c1c65014100a0340d180300351203c45004036522054500074502c0ba00d0500003600840400744009000c20380c48610686058070b00007074501a5801044482d00d41504503503001c0d9014158038200885500c43c40310300c4049800998215072142014001642d05103c520040d145540b00c44021540c40d060060071240d05030440c4c00c2c14440480180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 69999031 1250 69997781 69997799
    0x90d020105090a1a041a01061205011a07060507030b190302040c020d140702010903150207020112060f05090402040b0307060512101d041a010b07051207020904150e030f03010608070207 81
    0x441382030020700b061500d40340d911700b80710780780c81140400308061001c0d0000f1031459030019501c42c252117100c9081c0226601c0b120b03600309400490f410050900390400842c00054019000140d0051450600040441e25400440e91003c0d03500340d1804448a609014001c500d0300e40b041c1180070781f60380300500c8003074800400540340d0905083e004000c0c3d440030070040304681c0f08103011310145521078061150044000c03025806900a0340b41240419501c8002d81d13906001c521401d022202d12507000ca10880c0390105100114002030002d80c0c02c251a01d01e52589900e04218175030081c0300690701c081c0c0d5980f142c40318100d80e81c0c01030603c02030701b01d88200411203060b2100341101d2400844000b1800c0d0344403480c140b200030010742c40c800c002400150000a5030035980c00940481401501650071000c5945800381c0c0b98424a440258040d40620118010545840d40321143c1410b4100009601000016003440e503089080c90643c0440e000005014a030b40c0b00700d1030364005005000a00b50242000909 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 70000281 1250 69999031 69999053
    0x40f1806080a081b100c080f040506060607030513080607110102040b030604050a0b1f11010b0306070509010504031a180309030a1101200303040c050303070807110612090d020105090a 80
    0x1c0e0001c0d101003040c1350307482c20b070030613156441490348100d8000c010500342100103805004002404902c1d540d000404400d2400f04c024170a661244c040e140719902d40d4100410b03030b0085002541000310a0115080b114403948880c406001d0a1008211518000000401520002040d6101e070790061104005c0070f40030b9800e90b60440f8046a000c01c0c9a41c480003d40c000b05185000103500020030a4082102082903542120294440d9107000b010002886068203a926510031503425038828000604023510403401340044000500d0010329150366520b901c81c680c501101114019070000c0f0034401d00c100c003400c015246c2c02c10a0091410036000e240002d4030380c0244000600082d1801c41005003aa12038a02c2c000042c20030b04442c1204202c181c2e0080c2d0341d4008032800c403169080d40c1000315003880c0c000190344146074084082c610741741155075070090aa51030841550452001d010741020a00030440142c42004100d0040079810031100307000f402d544010344408015041224010040350440b540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 70001531 1250 70000281 70000283
    0x6030a1e03050702180601030f0603030c12090e010611010b01030c0516050c13050a1817210103060e06100b09040209030a020402070b01141c060e010908040f1806080a 73
    0x30400040c510360805807010312440000a5102604600040039032a210566030b00510082c1d07020002d61003003141000855810740400390100710000051000517800d00e041c100440054980614070950342c1e03442ca1007682d400c1c0c00c82d04c0801c0f091641094261001d100c0e094450009180070302041601d064054410310401400d140b510b400030152106100c410803031680303884405410590b40300c107240c03c043d0040905031002c40c130b0306051140d1b6080301080802c1910110390484891a03951945000803201607100310b102c00540060045001186040704104c01d0095004002c080340001486440a04299005000340b02c10300d4144c0301440840448815204102e20541c3e00503511484030b4002854042c0c10f0300020341c428000030383c120030020b1107019541250128103031084485081400c10002c01003440004c140e0300c1016100348003040454002580c020050300c00011190034070744a004041e80035401c50407160652442c1002124203d0044000c000c103120801c000c0981403084c099240c0d402150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 70002781 1250 70001531 70001573
    0xc0f0f2401050420030c120105040603170c010905190302011407050307050706060e10030c06030e060403050d2c0d020105090c010f140301030b011706060102060105041d03180906030a 80
    0x1030f5111881200c5880b4040e480c103d8a05507031645840c803a4840144d107d001036003040c2d8030020000a044c02c1c0743c0201419680e01c034607020031070034080229074203a400010840c02e9964070b41100f4004504140103840d140690210046507801c0c4a007006800d4444135100d03d00d0b80d004807020480c035603903c20f05681c4c1261683ca4180d07a21102400e0000250900c1d802c40044124074030184501020080710000031280700300f44204030340d039a542041d000c031a42e26001d450f00e50070400c0000d000038401c0c0002c04d0140480d0f040040c00c25001100a00e090b10b4003e024605145500301642116004110f000d4410202d440284030a00d0000c11040e00c0300000b9600c14180045003800030340d44d5016003089941c002118403816201d42e520b084c20b00d40314034280b256080b0b01704c0070440306101100104000c0d1182d030068000700642d034a030000740002410302e0500251180480001001c4e2807006100900c0d100080d02005065044030104010b00c030345002d007030544a40c2c0000318441c00140950305030288090220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 70004031 1250 70002781 70002791
    0x10c0209010512030706050f01051f02030f07021c031205090106051807090b0a03021c060303200c15030402092a0d06050a0308030a05011e05150c0f0f24010504 70
    0x790a034594005d00700e0040c90786060034200034403008503103503d50484104582c080c250b403030548043c0903440280d480140040e0410043d030950303405603c0007480c2651014102075081c6511901400f062106a00101c00103001090800807082460180a0300500c190000b00200c2e8a010f0024031000c084030310080c7c680340600b002503101030048440d00f0040c0004807207903983c1c0d50980e80040081d0b020981001d0b0406001d85604103070300c4d0611035541580d602d600c3d1400082c104104140c005070f00381c81e10440e68490b0b12000d40a07525440340401d900c0340d00007211030326400c10b41304100241c8401050141c49100b0440c0c00160500c1400070003030040c0d56008916a99250481c000000c1d081c26082036402010031003000041020650086120f518071040c108001d0b62140181c85400c2481e860740c0f1840b02c800c01b418403180c07074098002e0740c141d0030400446241400b510700b10741c01d10f46080c01002030b640140c0006d50300c0c180244189045440100c0581d07200d40403402103520410703410f0140c580129916 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 70005281 1250 70004031 70004059
    0x40504050c0901061106010f0b0304030e0d0204110714010504111c050d0804150b0303040504020906070b0903130614030403030507020a0b010e01051201060b19091d01090506010c02090105 82
    0x144501c010022010304031a2140d0303181c1001070900035010507405513074440d10b40000b4007409045440c001350fa50b082030741c502d5030325151002c03a4008184030100364080c1000d00ca910040c2d82c0e0780320f003090002d400418140c0710012810409042949002d14202c00d90600041100082e81440c009149d4023007202d0380f21450145001e80b04c1106108040108144100d41403043c0e100e81050440c4d2059200782c0c40740400c0c0200310654010354881922640d019441400280800d10300707a0007500d480500078005905011141d00c2c0c0100b104001d0362450303040d07000003407042500e01880d80200081c008030f0400e424000310b401c10f008003e1000a101904040d5948046605584240076055076650007200d60f80142d43c40e4424200004001e100d518410170b07690b8441460800107020b80b20403900101e0140307003032001d108007a00907d031110710110100001c903000814080d07030740e6011000b4100200e4a2550942c10007007150120b500192a107814040c000c0c0c2c6080050307450030b407070505554054400c00340c03d0581d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 70006531 1250 70005281 70005283
    0x7151803050609030315030c0f01140c10091208010b0d0f090f0c05030705030706020a2d060614180a0c18030b0f0105010305010b0d110421060e0c030a0204050405 71
    0x1403504010000d0154009000c0148000000345000711546001c0100404100c170030107940740041030001e50050207540d0039540390340c002e40b0341c0070f80e003007501109600d040700088825051602c039842c0e18042640e10b5994506103c84009150400c071000e00f01454954109590751145001e060090740300a6161080900d40b548960802c103191544005820000002840d10110392412070007034600a1183c1c41c4009224070b0002120b0045564607006170a840c0c0d0fa640320700c00106d400b000d9041c02d554080880401c0f081c501034007250b2150286070001041410716408849800c0110602403040750b1000d085c2d030b070440b1243d0b44c07a84c2003003e590000401c0e0034890400e490680b040c1d0460f40109607175007000000c1c0b0103a0440c1034401c030310081424900f0380e2514015022107d081c0150540c4a909100109007100168012400c00003d00b01c080e0509955509c1c0c0c800ca041c101c5c49044000e1500b10540c41000024098152012034100c064a81410101c01203556941007900107440740d8ac80d400880c043c014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 70007781 1250 70006531 70006577
    0x1e0911031f050a060e1815040506030a0b011512020915090102120408150109020a020c0d03050d060b0901030f0b1302070c030c030f1e02100c0303020c101d0715 70
    0x70142007803884907601c1c0c5019040c403a4400c01720340500c0480030300040b088030381c1c2c10b05e512450700c12032483d81c0c15a540040c4001800002c2c85150141309003580d47c0c0c00300b030110f41c04500034129405c901d0358542c0035007001859542032000b0030035024014016004207580c4c0d2041041065500351030581c8902c0b150f00101c1c038200706801000200f06000901180c2001c000c81c951341c50498800c854070030750f41d80780c01c601d04910610395070f0801600010034070380c4540390810401c1d11007406468540c0c14600c801d0641e00c12101c1982c40b4100407140052051503a50300350190b104c4501c40110104882403421000c41d00c004c000f00c241444040e40000c110301001a0100c0400103103130401c1c0a00031998030b9140100081032403013419501e00b00440303046406d401400808000703169010b4580080d1341086c12040c2d5100e00ca03110202c5c2807580034041c1002c500300401203140485c04024001c680041007078000c01025500c0c0079800159003101c4c800780003e1000000381010303403625107888145400e0805490700814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 70009031 1250 70007781 70007789
    0x40602120108010b030d1b240e07061103070b0a02030a02160804211505060d020405040302010c0e01052a072111100f030c05131e0911031f 61
    0x40e90040010031142e00550146603540c03025012110150a413000644040d040300b515112141e9140321800c00181120b5080c52090080b8004800d03449070100503c410384180d0284403016500030081000241d601049010080c04c1000c05103150840c3d503198194001c4006200200c5645c0000220f0345049090b411145002000a0103210031003c5180c407080a07032091007400040b6001d01d003401c5501a89104c1110103692002014112000742010f52002d80350040901c0c2d4003104541c101005a01d031805201d10441c81b035800000c0800710040e026046048202c00302c0c1c10003a0902000030038298000030700202c1c0031220f22091810b224500c5040c0f604100390030058080c1c070700c00b8149000c01980409411558401c2c001462024840014070902c542044030050000d24801c0c01101000c0c0660300101300049207142ca246448151240f0788200841540301d908485485201405d1540e02401030701c0192485107000d10178031110110030100c9001c09000c1c0d40040940480d00b0407002c00a2083c94010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 70010281 1250 70009031 70009057
    0x50405070b040914010828050102040b0c160b090307050d0203030d09050607080601140703080403030b190501032403080a020102120f0403110c030607030b0402090405010b09120f07060503040602 85
    0x1181c03a0000400503051030b42c00b658102040134000f18860070b01180050100400300000f40704449600c14081c00f0104014042d51295401c00000c20130a903244014010051000018039070f0030101c4165824190890b0320051410400f80941b220039500031900c0c1c3c040740c200b103403c43c000c0001400080d04503c216110807d101c0e1070228490100000400c00a21030f01451316030002c1940d4100040d04c20f2401070041c852085410044940064080c00007180c0040c01703440d001448032109030100f44480c5032034010003220132440e1010440c03503034580205180481d10802070700203407000118900303034080207010041441d41c01044407001d680c400d6058404094941d2608907c6003401c049031851204203540650000b40c0700440700300b00c210700240c940110000500144040d80c0c444400300e000301010300d080c560154080010103500c0c4e446001d181e0203080a504142d6a035404601001800c4040044050181d040701441204080d404a10390b400c031095403e0941d502e40d11850328100a2040a5446640c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 70011531 1250 70010281 70010287
    0xf0801140112051501170405060106030203070203090d03110712080304170d020307032304051507030b040e0102220303080103081309050f09010f06080303060d050304031e0615060c06050405070b 85
    0x4d030564180b14064105001e88030301d03500403030324109507008140c210342c003610542c888001008082d209900031944080d640c03058906040f140302c00034100b0048000190001a800c00040003070300c00910068000304101d2042082007403443d947c00c030031400001c0000e840c1110607000107295107116411a031030090241ca0840d030304d203400f4401030001c0c180201f0405a403514604145500300300420610301842e0400e0051580e0429030340041c10324280188803104041d182c01c008030030350310b4601484131103500c00c0c4009030b1100b0581b42502465008080f445489032a441420004a9080795507141580c1e0410b003c2036454684e00366040070728455a11544685181004004a541c0e83c60321440c001d1128a000740400365010090600f615140d0003050150740040011480c2031410014081e2014860341c252824156642c4805451580c0e5061600070f1020101e018030412500f4410300104000780c401682c040713070404400815007100c0b2000204000e90703030341c00303d41884010003607c0024001015071550b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 70012781 1250 70011531 70011541
    0x1507051201090e1c020a1106040b0a0306140303090d030302160f03020309011215060825090825051c0c1502060906060306040f06060b07030e100f080114011205 70
    0x10041c43e010084002a005801407103d54145059080204810a0b4002d00c5420115122910343e048904035956006d0001c00c4000b40d01c5010368007521950b201034078009515442c00c00c00d06070320141403c1d964401d03041000021902e40d0740d80d81d000400ca40500c0c2c01a103903110280c4d080c1480e00201000f800f80724004d000d8404141c3d0010003012640d50071390b55142d0445900000c0401d441d4000d089444521600d84188044c0740708158565000e502949001210040305450158118503101800000f45215905104445081240c142d4110424250704081013105185115404280c01124444c00b01024000c505448040c010325201d07800491a10406641d41d2144854aa10f0381130140036000f140300041000001140d40c1340701e00070113009000203a44907622800002d8420f9411148150f4640010544a00071070103070617501c0c425194120705005420801c5080c0d00c200c2118010002820020617903d070f405003c0c181100e480f064a45130300c0320b02e00016581c20103000511441030380b0300710401c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 70014031 1250 70012781 70012799
    0x5010908040602010b0a050609120109020603010e01030b0c07031b030201020c100203100e06090708040203030c010e070f0e0610030b03070306150302090c12040305030417070308010f14031507051201 87
    0x100c11548035030000c20848902e01d060010310009445208c1d882003060040000f1418443c1c034007490f071040080001180b2441e0341c000f811b0354200707070081a58a0210801441082061403880750007240f81e16400c0e0412a156500030b0601804803000b0408e01e07900006031003058002d4040c0c0300c0c452500740070380700302587d0741c88440029001194040d00c8100504c81c00038030055490350141c0076070005001400c3c02d44d902c89c4140c0d0120701c040c1040743c0500c810014000010803c0c4105411008a4405811441d1a0502c6800c50a0458201d0170315561444103004050b500c2a080754001417075070401003150556200000d040124a40c40a03044900340f07806e007640707511424200030940344211202d0f596600c45500c08100c034011030490003408003a050205010a00943c06181d1103841800d60314140320300394040d10240d4012082c02c40c0800c02d850014001e0303520076180300015081c00c210040400131002c2c0002c6e0f0700c00194803011402e074144008a03070094403403001c42d0445440d821210549594400b409 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 70015281 1250 70014031 70014037
    0x27060c06070311040602100c140301060309020f010e0904030c020402040b0c0a0228090b041d03090a06030c05040605030a06080703080a0206060a030b0f0709031203020c15070203120c0705010908 85
    0x710001030318082c201c21184a50006032000d03a40164018003290441000b07200003000040110024000c0ca2039208045111410066028145968010401e640c403441400100110000a00e05100c5443c2801026032540d1088944c0540c0518041c0106d2a490022130000d10444e041810140e0740051b034a150004001221008ea900c2607500050340f0380414402c40784080c5c80300040245e404040e01c100f00da02581e0b000b11001540c0100001a840081c1c0481000000c142030038a615800110700b0044e9444e08003003400060120381010300801d20417000080031881076014070f00a20002101003043c01c540c6501000180000c44100d4412548030b0602c6c2c1c1c560342103084454014402c40000650314104040f4000483c0e5100c11182c0c01500e8407220280482070041c4610108249100c0c0000459040802484d1082458500680c1c031075a41001c0d0b81070a015611648542c1000350134401201d0340041164501400c0c10742d4103245407907640248501c0d21420101500d190308080303c05017448540c50003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 70016531 1250 70015281 70015291
    0xa0203062e09080a0b06091b0313020f0405010803090d0606090c0e030607050901091202030109120809010e0304050609040903140c1b04090302070303031802090a09020906060c0327060c06 82
    0x2e2041580d680e0107010795070461600014000c212100c0403820908020310601d4000445241d404c4061280804000c0240c204440e00d107082100c0078154000d500700b14180b80c0a0300000e540500c21581040ca41982d00d00c1000d0050740502102101c2d4018070005910840281816000501c40b00100c42c800910000032100b106200f03000e090301240595014000b11901e03030313606840e00d00003646454402c801d007007840d94041c4d806540b25148000000d407d103100d80b2120086860b0b01ca0917041c0540010300310b413440b1042c00c0807640104400d00c4130760307601d1040e120780380b03800c6401040480952904480c4500c0d401c5040c0203000c00411031417080300000c500031003503c3e03103012642000305201c400c00c000e80d004d403c5d005d000f681008005002082c803e400c042546142d0146d0b001140b003c590200e42009000c44020711000d54403c00300b01180741100e010b5410000869100c1e08080c0b6108500b501c074031034000c50b0b03003498a16200c2c400b00c441101c42030301c2a440005000315215400c0424248d2030746c2040350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 70017781 1250 70016531 70016537
    0x60c151803030a05150a03120c0305040b0a090602010b0a0302060706020318060108060403180308221e080d0c0c170109020d080c010c05041206051801020403030c0506060105120a0203062e 82
    0x1245d00007402e208100c07900b16138020800505113198940242c0e1200d080c00000d9082100402c404100245501c0c0241080340507903803001076861074094001c2c02c64490480151040981070406c00140c1c0c0e40c83c0a8170400f94010100695907101d6101450024110b40d02146150142400000b2140700c086034152084d400303a1030300240c03890303186018900300b4618040140170b000c0500500d06070104141c0c2c0d0303039043e40c2c24445628516445141d000100c0d403010440c04150b00c0c904205001020040c44000c00d464500d06082806c205c4554501802c20450301818140000e80ac81c0600003900035000728480d1600034041c403000c002103040210040d072000700e5501496003000c9000041a20481c03c0301c4c200c44642c0440b10070400141d84500203003502801410301030784c0c50395281c03015580a04c0100002c51003910b030324105400c1d80c03904500f042001440241444014001483c0c847c1503003100550108500000680d81c1da1803600003688000c03018819481d10809018070302e01e1070042113000c01815600e407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 70019031 1250 70017781 70017811
    0x40603150f0b18030a03120f090204050c04081c0e0111010f0212063a0302010e060106180b0f07080a120f020a1d0a030308060a1206021305060c151803030a05 69
    0x130700d81c2c1d071110114020002420714050182c0040f440d8091050425580000304960302c40b500003c003500e1060310240785144002500f0020380504001b003070801d04400700481608484018040c0215804c01005d505104d101c4208500f0f0100079404172074680e407e1801191545001c0c088103040340021100503000c1c4052014058034802407460b210b01e400520f0002c171000440b0407400c00c0c1d00100b559400c4080d507413078041c010196482402180e028000590701d440d880c06950216040c10380496120743c40340c440c2041200c4c510b60070241140e40250704580440d54401d0000d00c00c48404000d0403544200c81e241821030590350070b44d80c00602110540790303901d0840701b1b48862180842107203400c2c800e80c00001d0100c2000061300032a0043d80c0138070020030569040750b6402c01c6261588207208103c40d000c1c0d00040c00e98206030000303402d00182c0001e494480c1400030810315141e481c0e006180c8843d44100000c00901c01d09440c04180e12829000810340340c80e41403010300c03103003d4001a0740e1550852141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 70020281 1250 70019031 70019077
    0x1b010b040c0e13020d0e0f1005070f0207030204051915060e0316050907020309060706060602010c050304030c030806130c05090901091b05070807060204030f1103030f040603150f0b 79
    0x42c4203400300020300105610051010305407200000e51140001a04003a29030b150490980d0040c03003081050074000006c0e0a44071034684640f4100c510050104081c817000e801c1809115900040c01c505595040e6800115034a1307500200c5180105044003010150500d09404101010000713004121041c585035548084042001c1689034028444c110300080c603003000402a501d08480416042040350043d0380c500280c180204d001c1e1382c40080f0603a002901c0d44020030030706a0921031500c0790401450810f00314200f0b07940c0240920200400507040251085c08185d5075a92a8020ba402e0000010f04001c0416107060103881a000860b00c0380c031450024000080240040c0203000c4800c0e0b0710300c01e80010003a501401d403810380003900c0c1601d00314030034040000040d1081c8028000b444c003c0c0f040c0f1906444c9860880400031136101c2944c040c0d001400794140911090b4143e80c10340e00242004109075810b48810840d880079540074213040b0890380340009118090307100402803107607001c01d0400c5031009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 70021531 1250 70020281 70020287
    0x90b070e15091e0402090301050106110d020a02060a032a02070311120d0f12050c030103020906030a020a090c05070210170a06060c02090703020903011d010b03060906011502031b010b040c 82
    0x10b00703604a80c114800c0408082c443d07041401841d0305a81c000c0006040558110100f800c540d001d81041000c10b91104a54290b00c00030015420351020500c000c1900d0003070b5601281483c069240304000f410740f01c1101e0280c6590071010421201110241c5190816410310001e43d288158130068032000c042011b1890282001c128124030360100500078800030710054000c0725448117058812081101e05444103450070b0481c02854001c0c40140200c50f140d5040d401003040703001c000341034503106c2d80c08031040400603104d04da080d40c101c902901c03000851520400d0150360520602c80e0003544104d514030242c140c2d40d00000a942080074055004003d40d60345a150002c5408a001d220089044903c0c0e980061030954000c951013102e41c9005070800403240042400e40340140b0942050311044825150141024820701d181a60101e0040200c0e040c00417000d9240e0300b060181c1c83c505e42d501e01e20307840c01c1c1c1d0081003151010030038030303105541c0003900e4240c5c180284540501c0034403d908280e0b6100b181c1384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 70022781 1250 70021531 70021537
    0x51c02071202010f110f030406300b030a0209040b040302011b08150a090c02010516090e010302060d0b0303030a091a013804030803060405100e07050d090b070e15 71
    0xe094141c0785001c09150011368100201560540c00c005601c82c041050140501061198000020003142c0b81e5050060142801401080251610700b10004c110176182e009c90b81810303415028080055800148030209003414034084c00650010720790424881000340032426a031146000c1e50003046003200c003c40024070b0560007045c0f00c0002d045a40801c00984039400d68060110b4003d0540d41c0e001d0b40c0d9503d180542d03403845801005070b5520420801403022002503440300c80300601c0e04c50307007072401c00e00075018000d81800081e0040300080b03107000da00d40e000d40c04500b0000c1d00408886d140c0ca011040d400150a0100d0102d03000f9040d031003100075094581e2441410390341d2584045070950202e00500c00e0246c00d00e40810403110301d5105c0a908101c0030740c0180095070085020320b43d40d1920134140410f80f08003401d02241040c59a0040000c1030312040140e410101a2070001e07a540c1840c2111406044241d001a03e115485010300205c15089035a82000040c00e840d4542c0213840c6401e840041c0c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 70024031 1250 70022781 70022789
    0x507050406050312130e010303050a02010c09120803040203190b15041b0c030c0204020307030b030c030c0102030a0815090703050105040e1b01050d020f04060305040515150f1309051c0207 82
    0x340c407002a2201070342d0351202400085d00a0850030070111740e00d06003815003040a9009401041000645180e00c69080c001c1400a608608003c0805450700c43d00c42e0191190010140080c04040302041c115502070040c0361507001c4004140c4010300710b50034140101001500c042407101001e02004c03a4a003094002c00c0710100d184118205950080030702558000d540070300c00c4040100c564070381030040c0d44920145005d085c0303560700011103c10744000d00d4a0842843c061606c260310110f88400d00d0f070390000454049400360702e015441500c609011200c40f400119007190702c040c84104200d84513915500c4503040fa04115000e000d00418404401d0301c4003041061504041002c0c030004555500440c004d2005440c8840018901040488000742c507030007179004100041d03190000d11050003801c0181648100c140c040075519030514002906880d030312010f005002d12445003402d1150b40d207698094803030403243c0714140440000341c038040e6220703424040502e8814088100f0080c1c46480060000195 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 70025281 1250 70024031 70024033
    0x417070909111c020d080c01060509040c1e0b0d050a0b01030e0d03020a0c0206120702060601050a0233041b0803091302070507170f0d0503091f0b03150405070504060503 74
    0xb81c69044180440e01450307901070710800b500090f100e40180c42e400300c11041c03540100300c0640c4500e03000c0c0306103081d50703100c0d40710354461154501884081500d020b160000c44041d120140318151071800d00d8001480d01d1b500000d1200c0000c280000040410307003205100794855142000032201d20b90065040f00c0700c4411143d090340c010072800070b00391700035802001003807514184541391800303e41c001041a80080404080d01c4828418003d582c1c0d01006000d410540900f845800d010340300134025911080c40301c100309140000c05d0514400c80c4105002c034160315601e40c08503400e103828240440004103200740c081035808100d41c0000c6410012080c1c4003a580014660075400c8000d1040c20042d40000c2c0d4166014081c40a000134a816500315000540e8000409400d800000d891041d00342001d450410f01405810010003501100c0414a165500526141c00761483c50904140c0d00a040e089107a98045c4141480030000d24004100c0902c5684280704a900e07045e2030f5000d00090f40d19a10485401d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 70026531 1250 70025281 70025303
    0x3030909020a0f08090709061d01050301141b040302100201200a0507030c060209040504051c021b0108130501150f090c020303010b280c050606041406040c0203040801020417070909 79
    0x3c4900c5034400c25000300040046800707480c0c41d000002c007140d140d0303480700010184081002c0e0180030350091b202d0052804400030411600c902d4000500c0703c0004210f4144450001c0d15407801d0300078507007507401941c0c010780000120f10818001034000c00c140421250869034181d1140c000b011440111141c009281d07076140c0c1071001580d01541c1c46000040100c0b461a000c0c071995009072941d10603288242c2c0284000d2940e402c440302d00d88002c0358600e210004541000e1014510f1080d4159403815448084c43d00c2d018964422050409400000c840100903500f803038540c1d40343c11082c81001c000d03030b0069000355110983c0c8040d80f404980c00142c10002503041840104518000240503103a011985400440000304026003049405480495080400c4140740e04209000007000074940c85003080e07500308070740ca92810480d403580c08010000c0c0e100f03d837a418403010b0070344280107903401405c226009640b202e4a4404100c0c2c1d2102d00003000f1124071030a10300044400c0c4034054200060741143ca6211 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 70027781 1250 70026531 70026557
    0x103021e04020418060e1014010516060603140c0108010e010e09070b1c05060409030c2d0c030b0c1303120e0d031107060507050c040506040b0607060603030909020a 72
    0x210104652062550050782400300080b0800c03503a03c070841e540d22503000000c115091840d10046c1e240d0103081240c180c3c080d08005d200039030901515038411b50302403c3c115190100c2500a800491010000502e101c1c10820000f0030048070051001105540c2402e44606c15080b1004551020003441001e804940d038200401440c10642090b40d040500304d01668201501d40031000c1030b517803004c12802d06400e43c20078138118240403449055000842101d040c0940003a9850062884070035504c01f8003030f01d11b0460060900354500d4004880340c1144100c61a0045050600140ca07502c148015151003491740c00241a11010100300d4545902e264a04da54050031a180c1264141c001003070742c03041c0650a0030034005075031600600055144a0783d40d40315401400c10f0002c4c204082070340030310b061180500c45000007075000300b190001e0300c005403000035a5a66900004019120340c880082c4c20030303c001446010301410360008030541e030003a110011907551781e1402e10128469800a8800a010005825 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 70029031 1250 70027781 70027819
    0x10f020703020303160504050603040b090709060303021b0109091805010509070e130206070602030c03090c09011a03041a0708090c01080714030702010e010e0304140d0201090b0a050c1906050f010302 87
    0xc890300103241703446c50810380c5400200e0413540c41a42c5c255208c43d209010411114420840200905400301081c00980d165544c00b0b580c0d000380c03071100c483c400d0501c003903180349034031800b100c90007003000300c07420701c24203280000c0755400109041095500703500b0700700002c3d00c100300003034041c00301d030103c2d1646030441d03481001400544d54a0304040303a0081d81041520003040c00d900103036004500785041c103656400d2100110b45421250078026004620042c01009111880585070301034035800905190740713503280d00e44941c0311004054044030948549081c0b000e401e0f40110781c940309101400854000c0c069803801550324210881d19a00050310400c5d464480070001006150414814000810481409424942514a103007080d0140b41c0c00030900b00000074502084080c10503007550900e0203004c0d2900001c0424226000746400884000745003c0381600c50700c1140e4055607290140c4091108003000c062000c5000c1c081910710608260100c1c1e41c001003050700a040b070380d005047d6a0f010410b2221070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 70030281 1250 70029031 70029061
    0x124030803040f0206030f061c030f110f0102040b1b0615011b0501052805060607030c0f080d0603060b041a1201110c0102030709060813030c171605010f020703020303 73
    0x2c443e0038040941000050f110803003c3d41c007c0e0104480e045161030b01105009000c036a0010410460210320054008240c0004054000b04c00c00e10f00004040e860094203450300402d00d00e520a40c0d0301c0010000303100000e00c40500514105660b050303c603c0442982c2c140d64401c291503c00c0d135a0702d820301038003041d070264400104503084141084d80103031450702d07840c2c21200101e45548c1a001402005440501400c02d201241e8890000810160801c140440c03a50300800740c000303090101c00555003007130018808640c101c580e0300c100c2080d510b17031004034030401030002880120f865604080400078289442c1c01280c4800f00c00c105401c2014072180e04000c0180c004526003006550f85d601e4070104841000e0003440000b04d854005662800c1102e40144124510b0348442c04000c5900b09000101e2002000c03600030980502e841020480503092007071401440b480d1403000440c0018100c050038000c54500c89029024500130815060081d401c50140d124400b40103005030010400070b100c1320020280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 70031531 1250 70030281 70030283
    0x504020a03090218010602010506031501140111030a03090623040204150f060e03070e090303070507061b020c040507020105100b031e130c0b040303120c030e070b090102012403080304 80
    0x10219002c281ea401040c6103113420310041031040356240050011070b809010f91a00500b082d0024491710b00103404103130b10b0440c1030150280e031200c40e501381040d80e88a0543d16494140a2041d43e944015104024001b004070403000c0750910b08221000703920100c0003041540503c04405899050703a0b6a90810000f400403c20400c43c68982280104055078011050400780456031140900208010101072810030507a0180307000f80403c02c01c005c0c0900c1c0c04411b40e6008115402d03c01d40300c03071440c640034028104918030a036004291b624207064895001074201818a4181e908000d00c0c0c0711980c0c200c1c01e99504907070f1184140024a010850142004000c50340030210751031f20b00c07840f400d0301040601d2000079030b01e101c3c905100000b16801c5c0403e1040a800a010080005103403d185940250815005403100416150303200e29003e540c0707000703800c10030011508078195607a03251180e494526a4200103203981c010340c6815010580d0001d02d000d404403140b135400002290340d00d50740d00c1591503400180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 70032781 1250 70031531 70031537
    0x509060d0e0f07030b0a02131e03051203160e010206070c0c05030a0605040c08030909040b0a180501020a0e0603391603080c1804240905010504051e010504020a 70
    0x98a003900000074031403400c00341281c0c00948199413071410166140400500203011340c41c41000a4651800c0c10b8446070111083e100c140c250306540240070340e0310b1115a51015000d4019201d03804a0241d07000b0055108440c00206108045400c04044a001c0b42c1c0c012014050392011005c00d000c00c0c0104446903049100b03520300310083e504c0304007182c28800d00c8102110440e8485c1c041c8000c1000f98038003103024140000055050410040000c2c42c00c10003d1b00103001b1516000c0411701000103034001c43c10b401500c1c900d0306050b540380d1400900030b5010003041000103641d0880c003092890200c04030380c05410512906d01013044001c00c00c2d86004600c3c6a00e1041403030b0020b44020720f020324009403031a83c0b078a49024050010a04020b8141c00d4018101080d82d01c040155104564460800c200019030982d800110b800c1c000c20a0f0844205544400c1e2500742c5100001881d4681a040301d4182d42d070030fa80c1409030b900c42012030040042c000200040c0b80070a60014000c9080c43e07805840c820310189 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70034031 1250 70032781 70032791
    0x1020a03080c0f1306090e0f042d0510050619050405180703050a030905180a0e070503010e03032401020a15060f09090c1e0e0a0908040e040b0109050103030509060d 72
    0x8454000030350302140700400200b203200c0c01003000a4200d86800000d28130707d80000c100e480c080e8460000f40000400007010000c41c402c90303415546026961404824414041601e0800c0382d0800a6840e0800303201c06010b0303030030f2000090007400e11a031009518024181680c0b078003420942008054200206104103200010f616906994020082c100c019409240076141242e1a0305001301214495000316000e508000003080b55901c0b0b103640164401c010448c00503018420300109420720459610181d030642c00c054440d00f00c2c2101000842c00b80c5202042c81c070501c2d10181205841001d4403590f04d01582080003503002081000c15125a81c10040400055190300d03640e04041d050720b6504001d040e0f030360b034181110810603503c5198018084131520009454004a6010030224150046103601e860307000105030800b405410200c292544214015240c0e0340340d0b0100f01014008803003d40d61011400c00003d001030052144d2410399030181c0d211840d0030a0401844020340c0040c00301c45105540c0e0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 70035281 1250 70034031 70034047
    0x706021c06030803040605090712020d050f060c13120b07120b21060f0408040b0703090902030103080a0807030209130c05070507090f0f02210c120403052701020a03080c 74
    0x38850720001d1841003610030740340d003020f0500404131440142540e8065020540901c8580702c4c036a0007001680c4e040b03d88840b140e00d02c1c5030a03820300d1140f5813422894403541051150403a2601d01900420b0082580704580b41d60761001c031134000e2004a805030940001c0404605254840c1c0384161a500b88840082182c004d4500400c2138075942c8100b9060304c0002031880c400004090007156000358102042ca403003414191210035480c0f180c0c0c03054080d000c400113094410140101000343c0106515030003103482c1e43e52405d101013642d0050b801c040014070380c4000200f0b0305029100b920020341000d03210002810031000b4174070080041c02061000c0c03100074050080051010843c11016012014010480a103902d005100740c1c1d8075565160306950050200303121529030009525403014148a03000c1580d210f03041e04001520416217890885a0b00c0c030100f00070305803c0402040c112a1544000b411543c1c030031b10864484591004080c010f0700000d040e44c01081c03080da030260708040340b19204e524000b10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 70036531 1250 70035281 70035337
    0xd030810031202240402090703150906080703060b0a0e010308030406060302060c010b01201c0912050303060f0103020c031206042c0c040522150507081503070506070602 74
    0x1d4501080010b0384085016188007001c072804c10340350210340503d002e8904141d4001107001398020240000c050b900c0b0141a0149422081d02004020444041200c280c40702221601c640d102c0c0025500755060000200d072604000152004503070030450800d032a039007160745640d03080d031000e032054030190748426010000d65540c034002c142003020b00d800040d100c810300c0b00150503031501c07643c81d103000e400751000f810780302901140104070b607810112401c0040750745610070f480c1050283c1005050301c1e0003000c0001009000402140900c800702c13401e03108030201710300440130f07440380b00203a20041c3c0040c0102c0305010800151985c0007a002031010882050440e400440384498007074002e80d0aa90898503990b45100380301c3d540c0c1401099600f40070781d00c2c100825034418090301d5110211705400c01500e0042c441c0e03460000d088142010014081070a007000c000b001030300156401800c1d9461801190006d01e00080c007603080b00e40c0a06018180b903015103581c030080d08424206000814404140c00703080d42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 70037781 1250 70036531 70036553
    0xb0402040905040605010e090c01031d0a050f0106080c0a05060304020310020c03090f0306060105190507080409060905070201090302071a0c0706020303040b130f11032b020d020703020d03081003 85
    0x2201c4000082614040c00c0c08003d40f20180c0c00400f00c01d0a40081c460344980c04240d95019590a0070042001640104111083c1c0441110b0300c00038012600c06d80e0410101040c00f011402c900802031203003035216881c0e0f540b50b81800c601c1e0340d4031a9840c1e000304075a0600b04007840c0d0060000701550780314014140301d00244e03440105001125080001c0a1085240080c0c0c60280104258020109440d0000010341030740b0550051420307041c02c07021100403451045044400140e481840f82e0345480e80c0c2d4040d080540414042c0b486041e041400243e0344610500c51803104540680c000e0032483e19154101403225045042d803e8604800c002da00d02d4201d08000001c000c210319801103a0f03c2c906402c0074410302102a02c5580003500101d280404141503004142c0317400d0b001010301410030138002c00a0714100c011a100055000d5070346640c2001c414051612404c40042c0d000c0d41c03a0f160310068102c1e02c1d20654000250700c500d000b036065005c241f0442000d031380304040a82c0c182910b91603850b91100d180d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 70039031 1250 70037781 70037789
    0xc0a0302030a0201060e0c0d02160503070c0e07020606030714060403020a080a0b0106090806070e010e12060615070803130305090619090e0106080a0b0a050a08150903030903070f060b040204 83
    0x80c1c40007903440500b90382441264018080b864044080342454590080103109a60000310520780100303010b10800180303c8007842e01a4402d00b182ea40da6071503d044090440c82d846000f48444d40000025000c500104009105002c024040c140c01802c00d01c5c40e1210208030480d2681200d414040400140c40c1c804400c4040d0130504000c0404414914100d80001016046001004049802005603050000d40e090300200c2d10b09154004811500c0103c40d00f58400da6101da1003040310628000c0c000c80841e0300c0c8d010710002c6e074400c0c1e582c82105a44061074421ba01c001000b0040410004204031010018a1481d17807183c50700c98948090000005c4068011103400c4081261403580d181c0300c140c10480303607002040e22001e090703190341c07501e0006070021a000346024110741c1c131841c1d81c2046a40d141d25030009048001c1c61001c11944804480d42c1c1c40706024890061007480c040403a183e00000015070344103400390705c01185001d01542e200003020103480d20846800307071070340710b9040280e4660001e000030b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 70040281 1250 70039031 70039033
    0xc09010621110f0c0d02010b062508030a0506100f1215030c03050610060f081f05060c070518091c020106030b0a0905100902131503060903030b120c03071701020c0a0302 74
    0x11404d1001d11402c0031250301400c0c0a582c948a0f4024040d11902c05440e0081004401c1c60000d103a5681c1007524044917800003010284004100400c1c02511380c00300780184401d4400c50f550b800301030410340c1d14502d80c51121020032816091404081d80313641003207610282d19107501918a03947c1c2c3c0c1720f000074052900211a80d07003005003044040701c400301c0445d0080640d890b00700480001c40101405960000c1c0120b5908072220317586440c1000c054030040018a00039020558030b41d02c00c41ca182e2603401c42c3c01001d20414591103401640c41103007261030f00807803089010340004800d0b2110080301700400040700c0195504c07211300102140c04440d03903500c01c5040c180046052885440d100d410300b05020310b024082860120f103000541c4550751242c030410722802c2c000500c40300c4241400e8030a00154402010b941c140f259540405505070801c0c844041c040d981c0d0044800ca100c08a41c0f00d4031000c554030f406500c001020029861314045103050307051410001880d1140d80b02142e41402c040003415005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 70041531 1250 70040281 70040287
    0x50403020d141b030c120a17011409041a270a0302060105010503070e0603090102090406080a0f06051008150f0703021303020f0105040e1003050c09010621110f 70
    0x6040d010301111044900368a090103019198840ca03012038020991072903004202c40030030010703180081003121800e50a81089503000040c480000359241d11002886000a40c0402e01c0c0ea9a20b40c0c810316941600e035460740d15034050302c415041c0204040d0040c01500d200c00c51224890700e0515000000303001d4443c800d4050b1014800001c0301100135511605a58a41c0c840301408001c44e90114021b8190f40c42481c289640340c031009011600d801d030315209103030f00080000c14020904015802072500d102e080d87c06000c4180d40d203101a0f100c2050303c40260020800012510000312a03a00c2658080d40c880207450156403290031503442c00b61281ca5642c0906004014407140107401c2d12101e030300050760b10b410345c6401e024032040740a54109102c001d0003110800140813140e80078009440140140200001c011310f000d0703403105000c00701440140c840740100200740b8501c0c02c0605405050340d905031074900070348100d461362801c1d40101c00b44d03040e411a81d9032441d0040038035140003010141590202961 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 70042781 1250 70041531 70041533
    0x307031e0b0a0e0702030909090709060b0c060108010b060d090602130803070b0c27132a0302040b0a0c020d051f0605040b0901030b0714071203050a050c1605031902010504 75
    0x5070214807500040e903102030030303c10800c00381da00004071511004103a0b0009007503280c0500311440c00019400050646040c1070010616200391005480020103c1c0708079081640c0e2800d0302400c07540a00d1b1142d801020800c00b040324641140c110b044064401ca20041c035044078801d0f03400f0b19a030190400f4045400000d07401d800d2000d805007560308042c1500f4800e00e04154945d00402c48001020303908843e10070048108150b60b5006d200700c02c0c81d0baa580c8180081044c0540040c511404400d1004201745d01e031280d01d000c80d20074803d1b2001d554509401c0b81c0b0f4a4040501a1000c03680c0d130070126441200d180d24040023403000d2003508040380c00200c5001c00030941c05c0ea0305058800d260013403400b881c40c0200c42086565003614060440e600a0034a144507221080c048030305026501800514100008040c000c2280030701000c2c1d000a001e540c2041107031501042501034034002e98561940a07418004c244039080d01c000d4080781d07244102d00301d9152405400507008903002032a110300240c0d54a40401c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 70044031 1250 70042781 70042789
    0xe0103140c0409151a030d210518160609270c050414030c0310020703021005070905040507080709060302090109050901030602030603150702030304030c0606080f0d020d0c050c060307031e0b 83
    0xd007000ca5114043c3c4454114100440d50b9247c4160612080014165040f00001d080c0030802901016401d800d1140b4540200021032204800d0303401c0c03065110f244103107092407500c00b1005082c0c07640303503a89041c3d0614003d01450400700000648110f86048858138024800d144107200e03008855841d203a49561504440c00c0e402140c1c4100f0901036044201d60a199a0340840c560070008948000140c07126a6400c2c00c0745060395840512058601e054180842560071052803402c4030300072141130115a644410440306240140c4550b008a601007000307201c4070340640c000e8414240107241c02e17000ba540e030380001020000280d0007039490f00d5000083c007031241007d01003566402c80d801c00c44005414102e1f4001c5d6a448011700c050700b0001d000340114100000f0b5002900105a0802180c00c0c003520441090313181c1e06041c4150015228550030003412901804080e1036080d048400f0f4000d00900100f0300905500051900040550306d4840c059503041c5440840150300098a0010701003a4000c144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 70045281 1250 70044031 70044041
    0x50105030c1302030c0f07030c120512040311030c01020f0309011a0a09020c010204050a090f1a150304170301030305040303030e031303060b0102010b03031603020c09010e0103140c040915 82
    0x5180039400600110707071141c498909021804080c10001039a80d0b0312404022064007994030001c50801c80007032884245079201c1d1310181001e0081e0130f241c42c00c44404a069400b88940700480c41c1380c00b41500010080b0740500a83ea021416050a80c0e1810f4007505404d42240d000c011715018000740881072001c1e50b14240703d01401445803c02ea8054105003400060034000e25214041c206900007961f20390030f080030b4050b2030040c00e000d42a04506600d808101000d0001444000031852900030045414005120fa0440401010b4030b602070440e0034408001305940300800541d5175019441c0410003031110540114000c0d80a030340c50700d0b20745042d17103401400d0754980c0c061898141d00c144026100010040c0c1e031041240e62114001a0722100b000050340584000c010ba158140004148900e50001d03590661146511a5003507404500000302008a0500c082c0241c4030550701600050000420ba0800d558003121103004940410500c00000b4081d00c111001c01c640d9140d0f20301d000c5091229901030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 70046531 1250 70045281 70045289
    0x60905010501260708210903010c03050403120c051603021501080c0a09060501020c060912250902030408090f030a080a050417010506030c0112090b0a020405030708120301031b080f0c040501 83
    0x15056003843c1c49001a51404180f5681e010080054006000e41030100115070840347c01400a104c820311008001e001068200c42c158089100d00c6044622040181b00e01c20034056207443e00350600041591103420401d0f100f50480942c8a6504842d84804220194a00034040c02005058111010044c030011010650003480c5190800005002980e00450300110321101a02c80a80f907680b4000010400c1c4a101c00b8000d05009000c80160a04121008195420710510400e8030309641e404440080b440f0071180a0201c403030600c0b40741c40c10300d8415603210411000408981240055494044007640080c0030303607020441c0044d040101001c81401d00c403480420303100820152400c400426121104c005800781086012041c0b90204c00c6194000c0382881d4010000da00e031403900c40d180d140203511a0140340d21030b201d000030010310007100043c03030a02c0c0380ca0901420304507480c0da07072401c0031400c8400501c100d12120660214403000c0401120030001c13900c00041c001004280d060104540060308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 70047781 1250 70046531 70046533
    0x506040201140310030f03120c1e02030c120309070e0109050f010501090302010f0f0212070609111504031502091002030325050403201807021605150706090501050126 73
    0x104028450380301000c91030840b46c0250715800b9410251804481029000100054241c0b90802104000340e0150850101625a01d00074520074403141050380d49028220320304040340e010030080c1d51210a0080a503401205d094100d4013220f458140e00c0c9410301c400d8210760245030740c41c0e080090342174426880c14011b090a081100c0e58038119000240350000c01610076041c00444504200300d54400c00a0302007803000304005a44820f40ea01c2c1060113400c10031815100044030300703401092880c0c80742034047c40c1c10362141c80b18601450366940441c91140c24180e00c0165070300307001541658907111401b09421840703034055540c0746800d803003000c5400311a01000d145404981c00c014a042e802008485c290780c4c000e002d204501c960347e00f000050074208000703260401c8024100000078980000c83c1402000181c0a5030280385040303e0520210341d00e0300c541c1ea4481581040c3c42d510701d100784010034600d800785501181d0f8101e15141d89007503174070a84c8146c4040f9030060980d130401100c1c9850b1902d0240d004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 70049031 1250 70047781 70047787
    0x61b0f030402010c0f060501060203040e010e0709031203060510080405010c1d01031a06070804170303040c0b09040f1d070b03091b12060a05060f06090a180612050604020114 76
    0x5404994040188000c2c18001200b60b01c106121005081480003a0300120511040d03840d108000c0d1250031610520040f000418004603041050041d0240708206a9442100062460701d030020007421840b0080203040d6900703400711781c5032201d8501c1d01c950184c13900c441c09e09082a203003850071102c9070103500c400c02040003a69001c01d6440c0c0310b12260b981d001d10b004174a9100121800000960041c513403940b2500020301c1030304000035003001d84115451146400140c40052050640381d2008481c0242a10205034007484144801000780000c2d9101034070014030141d040412804441d8503101c880c0e204405209081384043d82001950084e21342407200c3d50643c00c0001841d6600d584407002d200408413040c20081141e186c640d4503400101c850300c100d400c64207040f240f0500400041d21814001d1601061611040c20103030f00300d8143c3c1c1c002500300d404030b41c609002200326482c1070000181c0c05890b084000348040c10341a1031110140a05c000d4241800c05100140407520781400c2002924018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 70050281 1250 70049031 70049047
    0x3020a1b0b0c03090111040e0708100e011a09040510150201020403020a0e0411060708030a050709030210080a0b06040b03060a060c02090c09030c040507030e0624040b03010603020909061b 82
    0x114a1054218882082e10ba403079840304150705000d8011103c61809503103003c6400112680c80100b0344d409001c3c55100e90b802d0f9269030107540320034500741c001d040011000c0c100411009801520740c58650082d000101c0c2040100400102510416504500c0d00c1030340400c1846480da0f041080000c80015000862070146168003082c6c002c4058841d5403060785000d40001c2c01e1043c0d43d0754040e4003490040c090ba0b0f075988246800081c81d0000d8820070001e0345801c0004100d18000c521401c00c1c6c1e50000e01e58011180100340840c0e40030001042143d103561615446500b0b511440060000340003070056841c0c403480d04006010150751241d10140130000d904c60800c003d0f8645581e13032500030300901103d81c2d41e03400e00c0020a140840311400e00740c000c0c0c5400e00b00070b51250305a00c80f4540300700d1803040d540662100030305110040050b02c0c80002042d001d1101030414036007680070b502008030103000030510942e41d4000a403010411500701815412041c1046219018048854414440600302074181099 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 70051531 1250 70050281 70050293
    0xa1b0b100e131401020906040b0748081204030302010f0c091e120b04050d031109040b0d050a0c0503070f030803060609010c0203060117190203060f1f0603020a1b 71
    0x2000302a02c03ca41400203110003440030b404031614100c0c007402d01035481d0740d81c00140d038195008900035103050718104e0701103100003001324400e0f40d80e40010b039100124651341050701455000074129225002e03445e10001440ca80d060191100f03c1c052100d90070703100c0d895410007a00b03481c400350101c0107991903c81100f0f005c0707800005820550b99121900814403081e510260150191504010310400c4944054400c00800c928542c0c8118402c00a44a051040f00700907020b03a1101a03a080358980c00340300c2200582006c0e07202c4070001c0030041c404940000141c0742d26040c072a4101054409033300000b400d12041c2410480080104608c1103e44015480d544500603640070180000d1300c102d000040d00d03a141ea101e4000010119002811f8402c0c44d603490485003401100b65000706154002d4200071217900710244008101e491700900500b002b03035641d984c0209031820061080c00c0c040d10300e40321444808500c880100180140f5200180d54204810f400ba041000076540048100b00304000a800146 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 70052781 1250 70051531 70051561
    0x607120c02010b0d14030c0a05010c030b031b10020709090507090e030c0304090f1d01050402030d1b0b04050a2a050907120906060b0f07021507020102120a1b0b100e 72
    0x7800c00b0844030b5001a4030f00309806c1d4411804140524411050034505208041d402490280f2441d00e040003003030b289a007416280c042d000c0c0c02a0340c114500ea10707001d050800190030000d0344c0091054591140d00d40036544e04580d82c4007015140c41e8030090042c0115600c500c20404504140c0d001181007070501c401440e92885107000305901d0644494401200d0182500b12486100141e10ba6031064051166010f00900c0c041310b090344a481525000d50500740a40c1c03d40700c40d10903148000c03110700300303d4882c20b80109010748215410320480e51903101048241c0c001da03e48142d40703482d41c0310144013080100c40420a64202600c210141c0f0140240d868001078141c55a0511110105421005041c048001d00c0345901403039040310006084190141100300a264092085889126407050041c0601c5207004880000303000d07070301100fa1070001140c00805480410700a240c0b003a0300f41640c28003c00d03254001c8904503494804801801a05040030000c04090030208010a0152400f100c000c20307040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 70054031 1250 70052781 70052783
    0x50108040b040311011e0c03050a02090612060d06060806040c05030102130e0709080f030d0e03040b0313080702060f0304060b0409230a0602120117010203240607050607120c02010b0d 80
    0x8500000426500130080d00078501c64089503d8007600304000c0382d4030001034466008500e0009140c0300000d51154002d02c00c5d5554198043d004908041031404131008000020f0911035000e220a1006c00010304103000b000f0241000f00302030416404e01e442c2040c2c000b00290801c503ca070b401442803240390079010000804950703d010342c0c4007854803004400e440486083c0c000003400d00035070b42c81c00120b80001000f416a00c4940f4020480c46003591b0107030707440f4041c034050540f850a04001050300d000c0d00c4110748403524000c1591918224960340029400c0c0d0040400c0c644808000c410401403081c04c1c46084c10000c001d407820301000025543d10b08410010852400000c101e0b150030001180e82080b029803055802081156120100c5900302c240c020240b01d00c419128100a001c2170860041c02a00d020300251543c2081e84007425484003100300f0b460440a07000340b803d111070000b1910070000c0d680603804c036840f00b41c114500306289a05071036152040c47d05680c14421411100c0d11201c501c1c08240d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 70055281 1250 70054031 70054037
    0x51306020601180207021206070305060307050316030809010219120e040509060601031a040614091003080412020d0b1003060614031506010216060e0102100b100e010201110a03060807050108040b0403 87
    0x5680703688001140c1c6c00d0103281707c0030140300313840c20490b200b5010b6200034000c500846c12903d01c079a07114105540c0702c001ea0603502c00c80410400070800501a603004d09a90388050054881c0c1580241001283c00c40b00e0000b50ba51554106000c074900750400501e034100b40080e0740901462400700382003035a43c03801034281030400d0342c0d840c200703945490381d510a00040c0c0c0c0c00503c2070000360754441032a4180c0c180781180c10302c01d0b044640415141141c0e40d482c501280c0c7d0007943c1d9400d141ca400031b000c0d400d2025040a0344c002c02e81144d840c2c0040c0300500440d00c070b1074128902c0c0d8449411400c240045030380342d0b000b01c200e40d0b440460035000b9a900150040341400402956a90381e62043c004078141101d100c2e01401702030301040c01049080e0481106104448280d0031100e00444080c828025260954012038100602c1c0e254400754520070228406004418000442d0015100c0a10010ad600c08041d40b40020381e1100103010f084028800c080c005e102c00d107010720039400e20f42c48005400c10050801414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 70056531 1250 70055281 70055287
    0x8150a05161e03230103050c03150a0b0d080d020307020f010b060403060207110909070303020c040203060108070509030a051b011e050f0c010f020406030203180d0e040c0207050d030513060206011802 87
    0x20052094100c000c81d2409180ca544c80e855104080120400c1e0130b000440c1e4a004804402950707040000f00341d080d040910340782440e542c69030b901c1c0c0d00042c00c17204141a0010b022132003600100e11441c000b00520600841e005030b1381d1400050090400d41d01a11007019641401d8070302489681300e40035202030b03070782000005070766403100d02c0c00d40e07150031b45658000c0e00300e04c030201003103410b850200b0b401084a00a8003030f1140340b0341e045c0400c8103e11040321054081502d1401050344144074030080c0c81d40b004090b048034824241c039110640341c11031180e1400c490104011100e981035922000b0b030030706180c90f000c82e078a03401c41a00c0040c099000e00c80503041000303400b044403100e010094002c6008100921011591607840d442c0c028040d520448600c404119098105544440e00280e1581401469920502c000070000100400382c2900e0700d0350000c61040305004111035a42c4c100c7c01c040d032403107901e882c1d0f6594080802100b50000070b074841015504560010080e107103051200c0380c0e03030740028240165 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 70057781 1250 70056531 70056587
    0x1b0503100c032910030e0706030903050c0609010c020f01150b03041502120f130f0204020306010507021f030e0d0e011803050a0f0c09021611010908150a0516 69
    0x50a0b5203800c5401c824216440d03242c12242c14450112103501070b04d06043c0c4403540a0180d068810854120000b0362200c0e004000c00c0e4429805841424800d14046142c500b4542c0d00c58a050700076a0001c2d60390755500c2c03540700615010480981c40004110003401503940f85108081c000d0f485100d14040070200000080c10400005500c0c080c4c80c0c0c9402d001c54a031290390740c0c40c01f4001421501c00402c03044000100c2d525644003500b10000941c845007100d0f82011590174000603400c05808181400000d000000c010307510005a090b00c0e480325041d503903681200680041c00c1c4e4055074149102c0d0340101d44400c121660050045018035020b0034a4000741032490313075800302e940d85039001800d54040da0400004100940c80d0415502e0302448030717007a401d91030b1801c00d0224802e07031481c010580c01841d6548002201d1080c43c005403e01410100070180d5640c9840d401c20030380b103200070358000c0100204201d006191007800e400500d01e40515640205280001c0c0c0302100e6541c0b00003c814085040d8a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 70059031 1250 70057781 70057787
    0x109080405040c0215040c061409130902060c07060201020d110406141608180f0109080c090414060124030b06040302090a0b1009060e03160e09030705191b0503100c 72
    0x400c07174a44205070f0f01c0149442d0a0207614104503005584c000344000d040b0000036902c080c1640c0d20084021301d62030000c021200d03004002c054040c401c0b60880c2c4244689480c2180c2403090b80300070b0038a5000135036600c414042c0c401c01c9035210b14030194500030a00041c010980d0104107088000056242507a5400c01100e00e00c000d01c80103000241140d00c0024180c0814030220000703400b0343d8050701c484c1c1805032f41100640d1a10703068003802c0da282d44642602e50300f614001c4816608103025032142800000a0f103602c60078617009802c600054241c5901100f003801c8030b80305401210400e842c081046141e0074000030014451403001a00c240100303030206056003216031000310035103001083c070f000800081c4406404040c0d2842030202044144000f42d070380d81030106140b02c184c00369648007684681040d415410035880546000002d200c140b0041001403410041c580c421242900442d51180d04c9207840c6800103000000400c800c846040104000e490002c2c0d00710390700343c0c564008610051091012 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 70060281 1250 70059031 70059043
    0xc0a05070510050423010608060a0c0c060c0c0c0b03010605090d0503120f010602120414060f070f081309021603120902030a0f0b0112051203060a0302061c0e0109080405040c02 77
    0x40702d614a04410310040240c03140440c141d5a010348141c28000a802c40c001d0308840e028895040145c00050020f000d4510030382c1300c80050400390808421001258640401721100d0b05d0405003c601d0b0708800405002c6100c01d0240104a5000c0c0581f071917040c0301c0f00521310b0007000030860181a07040c035903104210050081d00c0404400340c8041079549400d01040308201c60a1080e40f000d4011711101d0382500043d282124160740c0900358030300301c0e081d0754014080c0962120001e0008000c0600110000845420030352001d24041c0c040f85845406c0c000d9140e00c8a004c5910042040c1e1041040d0010019190a00b83c040c0e50142006110750304c031603440d9405080201802945400b942c00c0c00c41c20400c1d446030ba0007045004603010310142ea00c0c1c4d0381c0814100503a400141071139002c47c8070f40f080701c04898025580041d0107006804e04544d60340c04030b4003030340003071b0041b40304c0610798005030408110a03c0380c4010b2800d000021700660000340c8800401c0c0c8900d0241038007035619100c050402074020005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 70061531 1250 70060281 70060303
    0x3030f051b0a0501091203060f030b0705041703090310050106020a0f111201020d060e0705040b030a060e0a0b09090102040609031118040507080c10090e07030e070b0c0c090c0a050705 80
    0x58510b80696842d22a00801ca000022a801043c200601ca0342034801e203c1c0e68195004071010510079401c1d91074010801c1c134009c0041081240400c4041001740d401e001d82c030a030117840c00003941c5964a0104040c22720081100401003d40f400700100b01003907002070a42c1e011a00500882c074501c69174241801c81807002c200d429008240181006480481540108810195000100a000d485031031000a2900940d81100007030300920050280805000040d904261221400030f0703501d944103200e405030003007115800700c8640d94a54010003410032802180e840141c4074004c5280c181043d401520641c15030002401c0c80710114213a00c0030740c40d541240300004500f20a07001c25481c183ca8590354a802d58020a42a402038101e0b940701801c00ca0710111304483da54882c650a2400c00d0310a40249000420003010503485031003c081c980740c280200c001601c00004256500c4800ca840140b403c0c0c0104d0b0325034000d009160411010058071010f0354540c407014030380742c0d550300200d00b0901d283c0003030006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 70062781 1250 70061531 70061533
    0x10c080f040509090601030507062115051906080c0705030904060e10082a01030b0a030b070207080610060c2d02010e1017091912030605030703030f051b 67
    0x50050000e000c08018000312402259855616a2100103d98486100b84030081c1503034018a030521030203015420f01130403401d218100c6032850301d11588072020344000403d24003044514100c2880f003401e00300c00131446243c201d005075500c03501d010401004c02000501840000101155050130044244100c0e000c0b000000d0040c0881a03e6080d85450900255802c9e208402000000240b5181c00b0030000341286204003990414440450000c00b03100f0b46000d1141099a50030040300c0507941d8a14030009103004918103443e40c6881c0102a1a00c051500034420030f921910800101201c000206000d640651401840714402880c1c0884030144065802d4581091010107a210505104800c0c0025000340d95007003500c007041d4140021902c03944000c20004008c1a5002c1281001381e8020781c0101c4c40c8400c40350072040c1000407000c0e00c114031004a4031104544500700b00d040c2c2c140200009011700714054040070f0314541c0c01030510b001a43d01003042c090046005001c003c0a10380500041034544 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 70064031 1250 70062781 70062787
    0x5030a090503190e01090315020702040609020316091a0d02070c050307150201050f010311040e0327030105010b03060307090b1909020d05010e060a030602220e16050304120c02010c08 80
    0x602152101c10b1040f000b40022180e00c1515150b41c8502c840400703c03500041e1801140451540c42d4000e076211071820ba803c10345801d00014281c0407803008501c50003600d02191400c0003c4407005011885582c000c1c400c160030b56038012591030b1800c0c126201c07180070940060755040716160201c01e4840541c000f60749402441c000040c10140c0d034045492284d07099008100035034850b0055014002c0a00014100c003115414940c000d0400341c0c80b492060400004072401c000f00c1c2c041028a034000080880b51208100808465a0409014203800f41060840c01360a5107800004607aa1702003038441d074000e141d260800c018280c0c40c0c034450b4037030242c10f0b05a01d0b125582c860a03c7c030702070350000303550b82c5c05d00c4c3c90a000007130303404030054809000300c0c4010440650bc514544a0308040d420041000f000d4030000655180c2c2c0d07440300c006103801003501054005c03291900d8224844a084001d4801080c001c04008000014903039140c010928521410310266a8420b400101c0324540c1805000381000000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 70065281 1250 70064031 70064047
    0x7020f12030c0d02011a19090213080c0a0605030402060a09030b0f01081b100e03010209090406050915040c03030807120f0e0706020f0604060209011e0c020f010809060705030a090503 80
    0xc001804603140b1501103410281c80000124201c0340c94141c441c4900c0220102d140c10741c6020900040320785c1d1010880f516264032441070000303e9102540075100c032103a805040180000600c107103040580c0c2158130112403850301d0005002031100400c0244144000600500003a00510500d40a1900114020f04030310703151100d56a04c81084c020b00c920b6200d80d0250700d002100344500b1448542020703146aa85041000c01a51800e074107040c121b5040d5028003210031710352610303222680b10714047d03803012a0300d0505029650800400c004c84a02d03081c107200c2000003080d034440c07683c001ca81c0d2510f041b00e941d60703540c0d47c100c40c420811041c651195080045c03000d565030301a04000c22111441094407071540d03807004c0c26680c9404c001071800e0103401c1040000d0115031564050028840e06040c41c4440c030800b11480000090240800c40200d40603140613419814004201c0c0340006007800d0140c12400c14448149d03031103100400e0101000400800607480c900150058030030f507580308040305d4030f801003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 70066531 1250 70065281 70065283
    0x705180c1204050607030f09030e1005040801050408070210082406280e010c030804080306030102090a030804180603020609150c01020c0105041a0705030a020c031603030b042009040207020f12 84
    0x1900d40100003070a0038502c076482140d521400c1c50450b41526810ad414805909000203461400b0303217003003408003e00000842ca4401e00645100758880c0304080c2e550113007881001407124100040408100030002001841d6407094500c08204128040780c030024030300800000d40c1480351000c281c2c5400300e00381c1c00d94031840003851000c00d480181e4503040b00050b4444011603040d20744400c0a0001104007000c20302062283c802160081800380004d45050b004601156101080340e1042b150702400007000c104c0e000113a650060409601d00e010701220380f458000900501a520f49a0700ca01c4800e001c0d4542011a0301c100e84540791160000e40d1140b1700058254001c000480d41510100e009145007004031a400444a00c07034000e0703403611b504586900c05000000d400020010110344020440030111882c002d1b0065603051103668081030100000c0240002e4800c0031445040100c903070f400481e0f28800a8041c0e40c0c0c85081540e00503110030705400010b403a003010140300b40d003002d00c3c0c409402003030030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 70067781 1250 70066531 70066543
    0xb07030e0a0b03072c03070b0408010b100e010e0102010609150306140c0a0c08070503033c0a0b0109050d0602030610050310051012050a020c010e0705180c120405 71
    0x60300725441900da0341d03100820680c0c3c0c80100d0b455000204120910301e050b0a07101c0c0710b42e400c0010004050040641640480e02e481015002101c42c4600400d00300892a03090084901c00f000030f490060100e0004800509107441100c1d00d0380c140040c4e403d2190159200358014001405908d04c180b00394402200000c800030764a000c10303140d1038140013251528a1780400307118001d0010b10030741c0313103841c0c031340345040b2030300c1c8203410b4201c40c640303000c00600c030100d6402c00c050b501a107000a0320441e80300c9620241902c0510000340c9090030080711180b41d1001c40c040c04101e0b40101d04080c007003901c050340300040f1603d440a0700000d9100c40480c45840510500d94055032045406495408a0380c403120020303252404216074401826a42c49024022410804020f050b550000d0500c0d0050720422070040082d158120340d0b40c58100d40c041510310040c0402d0085408005540c009420981d06082c081082140c0850b0030303500c61240b0001003000d40c0400300450741c0769000c07050345401c04e00b010b14001d62141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 70069031 1250 70067781 70067807
    0x100e01020d020102030c030606090303070605040302030301050906030d090306150801060801090201080f010b090103090807060509060f011a0d020306031c05130e01060509010e130c0216090c05030406150b0703 91
    0x21003070441c10601207005200b124040c00303c01c02020700395903e031002c02c60740382c8c072400740c440e05400244544030008606001d4140135030311030307000755490b58148424071008200c01001a440790b48080414038103a81c00c840d15605036908644082a401c0c106d604200203d42d4641c010400746d031904a00180c400c5040d44a92030280c403d036038010b901e480e0b40c1c4504280e10030070f020b8000e04000402079501e596009501821126124405184c113041854642c00200d0300116120b590030b810020800c24142c0d212405107016002c2a41c1e040010b01010250421501400080c0d4103c0d9a000001c18540d0b0380070892201c20315400e0fa02c03940742060600004019420820704e80303600100c001808150088105a0103050b1000781d503c0908004410004440340c40300c1341c110700d4000c000a03c2c1540384440900544005405030340013000c440c10311f00010b14209120f6449402e60501e4140003003900c0b6401021260055044807020910b1500400c600d0f010740c926501c4020001000a068000c00d5002200784c0806 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 70070281 1250 70069031 70069033
    0x5131a06030105010f0c05070f03140c121b030709051603060602010b01320415081003031b030212180f040b06030703020c0304090612050d02070806061509100e0102 72
    0x242450105101a50000380500750210300c04000700c40426119400000c0741d20b001307004460034590b45543e851120740b203640003590100c840c29002e0080303110070000504106000c0d04c0c52303880d910541083c41d8850312109070700345001d0b04c20110460b031640e0400980020b00000001046641010468039000300a540c1d404000b007800c0c05000116940184a41507d450040c0c4a181c0040790015400d11001c1d001801342c5e06043c89502c0e46400c459054004e80060328804021484030018540f0192002a004003050701034214084103100082c1d201d160002ca13009008502a2201c00d00d15050382403108012001e00303001004544036240c15120306040403030b190180d130b07202515851042444103443e11044043d4110b0810000705010718403c2d401002100401c13070644e4103003030f1030b0f41a4405407811680100c0d14119888804c3c01401814002d147c1203a10340d0000700710303451901810301d4071140c1c0102094402c050f4840841c07075502c0c0301c0c2c040b80c6c402803004000da41389090810f406800b10322100820341c01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 70071531 1250 70070281 70070321
    0x11b14040609090c050c1204080c040501030210030c0c05061003020a05031b12010f050907090506060c070909020409060e0604050f0f030d0e070b0d0614041a04050a060513 75
    0x200194088406894095031a10480e600f890040800b804a10703100c041006020044801441018041d03410310441c00c1202d00e988600c1d05601600d020b190303540c0c07144102d00d000c00400041c2d40742400048007250a080c0454405800354050b90503003130b00c980181c400d014160420008400e10310961741520f10071a00c050000d0341355424540d403284500b9195000240544c40c9031403e00d40380d01600c07907210814001080f86644030100c241503450a8070b822581d41e01c405002e0104408034001c0640c400401e40300e69040200d0107941c0f950304c5440c2c0c41030f14000d90b5120f41030019529140c001001c1250001000d2140000303240c52240c1d1024111420340e40780c0a030341c50700d0760384500c003040e0501d19001080065007080e007089490001001020611000380c81602000186c0f030b0b5003403000e000d84010380c080c0042c04501d080c445020061351181c5241c826841c0808502450300d2400003096441c20603140041d49a0b03803000f0b01c50040ca9950845c0e58081c429421700c21a02d540c0707400124542d005c505035414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 70072781 1250 70071531 70071557
    0x306060e010e090d110f1b030c01031b03021617191b0803061912290f0a0b06030a1e06030f021302160c091505150a02010608011b 57
    0x141c1040d0664403e00c1d5500040340498401c4d2041c003001295528079810349070b01a048400107443e01c441d0000c0681d0020341040c80c14254501404000c880d01804e0a081c401c44410001001410303021031b2a82003890f60100310701e0f04501544484c05905503006054a84441100030000d08503003000407009241e40d200440311403e02e111b00c5500d80c030113200c07040801c048103040e99602d1441d08010922078000010000305103a81c588a12420000d2a14109a55688070b050030030700100c80754018a0f035416070f01c46007004882c04150591640c0304905501c0d403051520744100d03810203051000c0407680c0c0f140000c8103005146896510038104804c0709042c00d070a00d0036100c00f110540310a4400038002c6040e52020601508280c480001600c2c000000107242403100c0903a2900030040040548298443d5501130040561520510580c8086c20810030002c500c0c2c000003a41000322041c030b500e14a140880da030400309000350415000341051000900452141031441c126650700c54001c54000b48665542c0300d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 70074031 1250 70072781 70072799
    0x5040908031515030105010c05010e060103061506020616080601030207050d09050f2b0c1a0301030605070302131413050c0702040c08151017090601061202040f15030b06040306060e01 80
    0x40c03c03080c0100090440c0c0ca000c006440440c2100c000307840c607548514491100781400d203e85400380d031203a0b07000181800d20400010b00005150001420341d0f0212084c401102c2c907907000340780e15401c2460958902d0f6a50b00049001c0e02a12000500521505e04101d0b4404e070419501001d0b50f02c142d54820030700e804541000942403640d010136891403004086518038440c0d00d400d001046000d40707400345110350345008402940d410044500c504200100051080000f0303809507581100140c40d0950170001c1d00d1a80602d15111445400300070780d0b100321004415110f0a100302ca007152241d900300010300e80031404c11074981c00003804030700c503918245580400c0350140c3c0409001d0b015184491618007007503030030b2203091040310451a040c0129840721504409d0000402e500c103110032005001d065240050281c00400c0700ca0300b0000241c018442841400222940d00003119100d0184000b0710001c0c0e10158000c08034000090380020300050301109104094010200301c46020f42c1c041005c0e0b0b0b82d0700002c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 70075281 1250 70074031 70074049
    0x8010f060501090311010c1a0f0f0f28020406020a120201020307020d081b041d01060f05070204020d060b2a0d12021c1d0705180f10050409080315 64
    0x2540c00f103501a881400811070000b031405480806042003403002c8a2922585640d0144907120045074465108010355029400c01c655004014042c0520280c140100d0122201d040100308903128060a42c80b0141c0800c207512010b4050400c1800315a150744400c00207494010080d010340e2102146081c5000c0300b8414401c481c0b0a80c52a400b50050b45107414040324100d0b8090305065074504112114000036503040020130080c2a0020301d0400356170201d09049164030164010028414180d01203040c041d00481183c40065040710010b03035441070b9081c110001c0c061074008101d8460003003440420f02802d160b55001709800039581083c0d417001c0140980da0340003400300c5c6400084000c00d01d4401a6450b8000c0d000d02c4501e500400d9106e0301c0c424412040324108060f60203400743e02c8101c101010014030600c0e01510041d50700a51190105044a20b1040041d20108490b42c2c4540003690380451800c2070009060028801d0282000798100400541c1080c1c980003280d00358413103d00d8103460305003c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 70076531 1250 70075281 70075289
    0x6030203060f04170f0c030406050304140d050301050d020d0b070206040212032a010b0d03090f0b07021e1807020303150405070c1401060b0f0409110c060402090601110102120108010f06 81
    0x4110a141840d03882c0c44d915000b46481c00d0408205000c1d09003010380c24405003024021070b83d109034481c580341c01c0480401e900341c1841d10300350308040041034901c0d50050449040d07620503030b4050084100341c80881c5c100000034801802850204091140303613540426190300950086a011043d051711141071512031062100c1d1000c00e1190b04015074480400502c0070301503000d88000080ea00c10804041840e100300e000040300002c50f40401271014211a21034a8094282640d100c0d061a0741c590202e11100c04480c1e1040352000b0080099940e6034410760095082054410398100908215a01a660360030070354030311000d0003544850401c3c40c101445560702c80c10940d80c0c0c00d26090401d0307d401070b201520300b14456042d500c444000c00c50540300386c010b01c40070001c4400c0f25a51490702e80d080007159404551160716801c1005190000f11001600d07a80041d0101c41d54402a142d40c0f0059600141c00d15030060b055002284c04482000d03544036440c103c41c0850024400703040c01540f200d08484060103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 70077781 1250 70076531 70076543
    0x120a020a02010c06110c0109062304022b0302011b17070342060206062202040e0f0405010c1803080f040b0403080301030512070f0b06030c090a06030203060f04 70
    0x104501662142c1d00f040c02c054001c510015074041c07044c10000c000c1d40a041e0740c1c8174aa440722280740401c0018800d500f94031105845a00719010f40e4034800c8044070001d00013900c20407551a4541085142c1c50344050504030081490070004210b02d4041d020703100386000203211002c0703041514001c5010b410220318038100300a10031915552030750143e00501801800c00303950000403031103144601c800c039496045a1601000d14201900003074907064030000c40c0d00107404540001003807040719216110a40d03010078107056441e4040c03400042000003401164866401024130005000705842014a00d0b40198012002440840180c0000340c40a16800f400f07130800760a1110704001050642c030182c6403003082442c00624055441c000a50b0b15001500140d0700c42e0f00c004010002c2080c01c103c1a803040008140d62800e00c1e1854072a40e004a42d003c4010741146810b40000344656002d0000050408005054842900341040560018669400124000e10a034004200c1500f4220900703845240e202c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 70079031 1250 70077781 70077793
    0x8060a05060415051009051002070503071e030f030c060504060b0909010b06030a020a030b06030f091b06040506070303020d0e0c03010f05220314040b090114162004051008120a02 78
    0x2000e00ca804000882644200088041b01003041c2d1754003550700200b121650f004124980c242800c06091000b80d612500e150440250660074501a000c82c490031681c1011040c031041c2e10a040944d61170003075440c02080d85240400700003c12040798003c003402d100507074980c8050f59450503054200c8420b0508164000000d04c00070345698001d40040100d0300c0c0c1ca2601080c6100500c010880c0c0740c20603581e121000c00e40d4010846941d01c1000080060400d180c5000c00c2180d41c0d501207140743c4100c1c0256805050009510740170326000360110350381c00080c07007403c010017041304d50b070705403a000707800c156500c294200005190958401d02400d8010341c1c00c01c001e8181c0780620194044114650382c1e0072010300407500e4072042d0340f85002c0b000d00b004108203501c1c10354407a2030400040c00c03610402d07071000e0481c0382408810486100c41c050a0240c0d5448072941000080d14401c82001c051030b0300c8800e611504140421500000b001c88100403100b10500300c41100c54100c2400a580c01481d00d0100107901c44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 70080281 1250 70079031 70079039
    0x80105040e0c0301060b07032303010504050a0b030307030e010305060a030c0506030402120d0525350a020c03070506160605060103090605040303091a0108030d021c0608060a05060415 80
    0x540c49038a00307528240c111503020a0000100c0c0c05e69506601155400740f0200380c0c4814190851201440110304400c142c4020010301032051841c00103000381c0b4020750343d600000340c1c9a1300543c0b0043c07001b000141125241c201514000300b0101080d49000d000034103050100b0b68506014003120180c0b540f20503034955880c148410700c010358200038416a0703c01c000c000c0010921100b80311031324000d0f840c0ea9480b592030030f500c0844401e14401c00702c4084059070b000b0026021030403920000c98820b4201c1210308000704080c96218004041b0307462103901d148001901402c058000404060345103080e41036401032540c0750200003d5000340800e1500010902180200143c40c0d84e01c2540e00c00b0050600190001264480c842226021641140865a02c031000070038044c0c0290208044c80502c55003920544c10111000e440e8003c00300044800c54011550144254100118200d40d031590030b82040803030b03580d6450a83c3d0303174020380d0058071036440c01e40802c43c9400c0030b0080c15054040240d010300c550f07140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 70081531 1250 70080281 70080289
    0x313031101060302100512090705100f031407051312050d0c080412151b09060e060c0a1a2505031f030b06190305070506030c0f0307092103080105 64
    0x10303900050555032081d02200690320103944071000d007103030380e607440c0c545206294210030b001c0301400a0b007082e0300c025008c01c0266140030050300e03000a140f9020082049904040e401f0300601c4c00440f42c17111901d800c2200c0f46501c0800340c03402010020361094065603488040e88440014840509070350030504c0202c00140c0140502c044031403042034001d00e01a6100030721340c3c2411404500300d41c94100d9031140f01050085000300206040045040c0307201c48540e00014001102c0da10039901807128801c8019401d50ba024142c51071190041c003a200c440b092b81c40c105220131450b280742c14045015a000c10b010180701070440c0484500788180c0030b00700100c2401540d103070700010521442c0ca440e1500b0400c141d40180641402903200d2038011495082c500d00b04181202c50074110f40c00420840810800b02c4c0300083c6460454409807421a80c907140c14528600521441c41c00400c1214008240b05840b50b2081c0b6850071102c030403005080440702c2d8502e00c022403002d00805070005d41d0010042c8154a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 70082781 1250 70081531 70081547
    0xc0f02060a050c060a02070204050a140f0c120405060a0608030403030f08280504020f0117010506070602090a06020a030212072f0d08040314060f131115031902031303 73
    0xc650030710300d00f0000e641041d1454000102c607038200c5141c000c9401411410300d40102c03500b24000640901240000c81c0115000d07490007015064110f41410100b0b06507071061f0101c81380824050305282036841c290030035940c0e406041e924001903524042000404480c0441590144e83d816a11202000700d41c0408449111000d0800d5034500900c0c2e000c00383d06130304840c04a100303500219010403c0e1805c3d00403c41a0b48002c1d005a05011500c071b00d05000a0303113410b4850660700e0841d100c50302d03001d40382000c400034000d19031607581191003264003058140d000074001d07914a03c03d500f00d03a580344013485012010b001e101d0f00242141c242c20300d444406985100d10460000c030320704503c00c05481500010304480c4455800f030b501300c0c00000b028014070000c900106008040c69000303044a04041617a050340100c02007800071021003591003801000684240d03030f800060000c2001411103144101c8107050350060710200c6182e090808403c1504a140c02581d225648000240700c0209064600b030350458 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 70084031 1250 70082781 70082797
    0x509030d0c050c0d0609030e0604120b13080403080c0f0313090b0f10120605060c120f1303030504140102060106020613020d0b090307020118050901090209060c0d020d0f0c0f0206 78
    0x20040710340c500c9141e00c0d2041c0399900304e40030314400305da840c0355400c014182e035594560380d9000307400c200405d01594850500d0144481d50040300790b901503644c5a445c40c000011018010085140080d00105009190001e441c13071000103011f4904000d0700c41215652131088071a03103032500301c1c150400c1013466904da208800200000c1e14078614401c032000019401000300d140c1c0d00101d09803c00014038880248075940180c0340c25244c2e940b901c140f1850040e030314060300d82c40c05003c0100041803561080c00f0b5040d141c0c2c00440986074802203440c0e250162054001d03001c4c2c004415192031410b10950310000d40541240cae180c1c1c020300078507110604500324a40c2140c2040c0c0e0018a80000e074000600d43c090340520889000c0301a540f13400051000505603030402c00c81144007218240180b040d44d40e000c000354111140c46100503524098000414828006c42891030424024822042040b0350003240100050702140e4501011907400c400643d0244c51800000e0607084424100d40c0c01824014010700d080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 70085281 1250 70084031 70084033
    0x20309031006090b01080103051b1513062d0f0309080d06150c080d05100503031306030f140a02070f05060112050105070815010e010513030c03120509030d0c05 70
    0x4114804645065081d0300c102542503652102040902002d1140f01200c1ca000d00c2c020f01c455145480d0395a690072480e0411003020170501c03403800c8030342d01d03041c1c24100c05508000d1280c030342c0121140008028910f2254002081000745d56500e4045180c580a81048841450410600aa070400c81c2c90404841c0c0c1c90052555860a07100490403001c00340001070f0303030b4078404900681041b03510000d9000d108003c6d801d010710b101d00d6000003000707102500c001c506000c9000031599581c0309a028a65030315480075815000008074080414604d080310825903601c0d4406100103000d103124001161134903044100f4408403071010507584c038020313001841d505d4000c441c5460803020315100c0c1c0e8181482a401100181c988140c0581005800e02a4a03442151400c1481040c5403800742d0881625103200440d04100d4100c0181c21580c4c040e00a5807180040f100110940d9038903854403540d2a540c0307000c00c0d249644104420400248a00c081b1001c0031030140180c8109051000c042d920344c44051001c4804d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 70086531 1250 70085281 70085287
    0xa0b070201061a090a080f030409050c0d0903031401050604050f040203040606091409060903070c0608060a0308040602010e0f030304030c17070206030f04030f09080c01050c0309060301060207051002010203250203 93
    0x100080260242c005030500303d40302e030b90b2041018100300340384106038841c0e03003280c1202900300c3e83c500001c000e03102200d0b2503000115281d62920103200741d6204628904455502d0000d9400c185075140c2e0202611080c01c030070042840e45c07035004010f00d034090f81c41110343c001c0302c28110080600341500030350b401c0b502c0343c4d202044007500c0f40c03d910281c030f15200b410300200e0900010405601c80421032150850040e6004d18a00059034071200001340c0140078800500c25034402151087d2600283c850085030045501915661580c00003406420000301e0074200f48a4034880c1c60700154080200e80c000d56040d03d8607040f2031000e86d5074102c1c00d0079a2411801c00306083c061000581c440c07400071403080c400c6500328641860b1501c0c000e04074a520200c2101003048002e001d201480e80014540c18040017402c01039154034035000d00790f141d03100341800c581c1c2010001c000007401d2500020340c0e800b9a03000712040b1030300e01c0300880102d0807808125030003030020350044140c0c1c0b000c2c44c80300441c2d5052a00c610503240303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 70087781 1250 70086531 70086539
    0x50d050a12021204030206101406091f031b050309100b01021203010303030603020a0b160803101703030702070b03070e1504050d0c05030d02010c08040204020d140c0703080a0209030a0b07020106 85
    0x3040f6003044001d041801940c2c3c1c200010160b05001310303035004185078405400b01d030500e81c0382d80f43c1c2d18000442c0390207200c001034801100c1d43d071105804038201001d030700100019003205004000d441340440307001290740100828800035005038181c0e881680300200070248040400b00c44d00c044d141e0410b0b06411740c081e035901483c8140d1804000c60286000b0b80f030111b032562441c4107120703080d0304a50141043c03032401c1c4160b0b20400301d0b038811200d03280d8100301c003d40c90b0b889a9a8061610386a41c4c000c15000461030704428600b200480034500c40c0039282c0a45048a070389940f143d40b144001c60303500c3c001841d0401121100d18203824001410b004401e0b440e8102a12440414080401c0110540e0783e01d140d410704011900c0c040100b55000c1000c0c2c4000e001d80701ca500c502070702d540c2707020b80004c3c411500440c04540251b415400b050303071101404003c8105041c1442010700035070000700141d0015200b00001265002c80e402103620350200580100030400154407440c3c110320740546040119522110002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 70089031 1250 70087781 70087817
    0x408040f03140607030207030c02010e01120207150b0406030507171c02100b1c0f060e120d0515090106030515030102030106030b040b030111031306090f0f030f0804050d050a 76
    0x3001e18400d0300c2403284000000319841c9031807401454141010700404c407210001c1e42c018030001c6120350a08013403d54004540060740c22002c5400600b40440c80401d00f2014412000000b12000b0b801140030010400b04209000684085010140003a0722007401080001d038503e90112200090300305170b07215500d2082501d0b2044100305006c50040e400000c000070010076511884801440490b09944011500c1d41161003a07104a4400341c6400b00990130b200c18000941c1100d200204e07100241c40c400351286414105c2c640003404030324011454400000c204204000032182100b900504042190f864994214040c2000905601c08098418050a05a20240040c0d400b8128030b0f1030201d070084006080c401240c003640074091290b8180340004010b40080022240c100d695590202c1c0200e1190a011003d0710200400400c203000410749081031080e030b401c50b1016580300781e581c00c08000c003201c0c1c00c40c0ca02800742c0300507005402205080070410700410003820300e20a40c3c00c1190381c94001300444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 70090281 1250 70089031 70089059
    0x30c09130f0b041101022b0c06020c070e091209040b0609030a1103160b0706090302031201030303020912030a2a1e030305010b130510031103090a0201110c090f040804 73
    0x1165510030003030030701041003039511542413025001e00c01421054400181c00181d4000c8418404550210301082081e5510a0203107600c03280d0080029950f504001c060340740c0c2c4141e184500c001030b1850314041108118041111680c040c21200194100482541003000801c41c0401d040e5000d1010000c105540e1410b03c000503095000e8800400071414540505013000d0300740e407030107031003000c005801e1081009580035a10702a801c4540060b05c4502490140e05d5440344242c81c0c1a0344c10500000420550306400071301210300140c1703810948107000d4440507940e010340308080012410b41c8805208007000304038001c4a02600c1441d44045a81030f4454040101c8110381c1d5500b6125080c100105254060184600414084203003618010701d88000d91280150380c05068401c0c41c0e080118645584a074000000880a08540301d54038202004916940c8180c081c040780440d40426104004540100c0c10009841d006010710241d40d85210304041600d00040045a04040078000813856418501c8d807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 70091531 1250 70090281 70090283
    0x180f070e0d0614130203150402060418020304030e04090f0303150b0a02030c15010e0a0906141e010902090604050d140f030408070f1505090a03021309060f0209030c09130f 75
    0x200041c4800f10214905010364018001a25101c1e804a5000140c5001400082c0741c040c028503503807152618400103e0318072855201d035020040040e406519200715500440c000c034825207540401140c2078040c03106803944040e000c2c004440c0a94204007003400b80c0c01250b06c2c0a048110080d00c85d0312400c0681007500310444a4005030700110740610516030403c404010304900810504581d1726000904402c1900104402c000549890440c4200540e60f000f401d0302d01103010144415240400c040340c4c5001c0c10007040c00d110b04003000005460902032003112041c0030094840da242504102c01d00c2403150f45600e0450700307200c12030b9604c002580140258240d80380c00e203014654882c81d03d14400c0c909242a08061241000810108030090b4a000220b41800ca41e08120703458644100005107040002d46c070103500600d00c00101036030480c00c0c0c3d0240c1d0410307220741e030304000070f01100c0f040c20204c0c021245030300d805502803440000703589090582c00d58044500701e2862002502551124004680c2c0302c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 70092781 1250 70091531 70091543
    0x141e0d0902040e010912050a05090301050f04060f110306040c02070504020d05040b070207061e200303071d03030901080603070b0d0212070c0b0a0507090305030309070e06180f070e0d 80
    0x90a003140b03054002c214445040308020700c01402107403111070031660000c1d240b4042c0980024440c120038000c409403104404010020006481c0c5142c7d405040d0f10211000c8900c00e24010041c7d8445c0824441e140019980130701460840d6140c00510000f49010911301c000c0d40b16201e40050259243e000501d01c80e0350007440840c190034149845c018500c0b0150a41c005c3d9048000d0030300c03089500070303501200312a010507071040c940015441540d0190300c150281c1d403841c0c0c0005480300b41031400402940644840c2c0e441030010207001d441d00f02054550140c07642e054204000307040701d940c0300e1020160842d81c000d050b00c0d4105d40d59102c0d12420391081c05c1000e84150040740c50600483c0c4810b045502003814109990020420707903038030520300401130071a1110b40c2e031500030441061048a0a40155038008212607a0f403c103c0d0816a0342c001c640b03c1d81c00c0c002e2409000a030141000752600b60b09100e50600da22464490300700560040000601c2d9400304a500b10302641030384c0e0b4121007544020301500c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 70094031 1250 70092781 70092791
    0x30e060c0f030c1203040b06010e040f0c0f0806041503022b03020115050f1807030612060b03070f030203030d0203070e060415030501090e15090a020406031a0601020d141e0d 76
    0x54510382c00c4c040c095400d008900410300800001c075010205c04c55212500f4078110b01c51800311000500241460301c030103201d107450300395a601d0894001c4180c0b10b807a84079844151035540c1d400200000d4400b0344518201e442c050700380400050038907024651544009082d400e0b04600e02941d109900c1c2e618000c00d0b40141c3d15601482811100d0202040142030159a8481d1513034031000800c0442c031645900800d92101c11001402c054869400030307004d006034002d203026410960070010f000e042c4804030310b4464014a100020300488030001c01040b070b540038000d18181706080707003e04001c2d000140310005026083c1d01c002c080f80e5030704004001404201110710a0144040801001c58605800c9882c2481c03500101c0075100500040701c90040099500c1c21020f075803200843d070708004010318002e4010b0705081d008010829129018552920004201d503034039500c86004982c2c91100020314404560358001c58544882ca04004005000300600300341e0003450703035600b040031542c0711412038045103986ea = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 70095281 1250 70094031 70094047
    0xf010504080a0809010507090b0a0905030d090311030309010c1b080a0309080105070f1b03170109020306011103030609061c02090103060605010212070c050904031107032603070804030e060c0f03 85
    0x101c40101d130070546140081000e031a008802800c0350b5083d0107604017110012624096040c4501e1000340948000f4003542c0a07084e03121005052440140030840742c8104890504405080020a6401c2442c05035508482840161680006100c46202400c501d628091010540310402c100c010502c0c1d21a80c0e404408524042c00307542143d5000d0454000c1103440701489000030761061004064a2070800d1707d1402d01058502603400c1c800d00940e40708203000c6100001541017055029510400b420789030510503520b00e09102e904c0c0e1000302c4105034017800c00070200784681844d240c0d5441541c940003280e80e4500b00381d00040e071491426842224070f41c1d01e9010a002d10750381805944480e040e441e0900d03080c40008c0e61410640d21080c01994043e40000c000101414480c10403107180c0b544020070b5a54142c0c030707820018010310440c440340e00e0807820300031a10951800041100d12400040d0340750441d40d00e4a0381c00321808080001c1d0300d07a00c000e050042110301101481441c0c081410640110703035407404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 70096531 1250 70095281 70095287
    0x50f0a0b0309100c02061005130b13060f08060c0f030c0403060e07060207150c151d06041106090d110301020c0102040e0405150408041401050d09110a050603060a03080304050f010504080a 82
    0xe8041413011500050184902032400e1003e040c152441280c0c404060003c0b2180c81c00140a505a415400480c188071088541401c2c1d1200c001ea41200700e03004482a110384200d55551401e5840d04002c440c100951100d9070b40ca01e024507040780e542c2c91040d03e000c0c3e50f41c40d00b00c01d0300e0b510341c46072000740c000c8403003041040c2d01000094010700352020001d0040503500400b400e03040f20703400007501041c908418041c042141e54000400803c1c0240414104209424001d55413407045400b1524001002408103207450044140c4102030320040100030054403640d503015401064148482d010343d02800118515042030000e0006001d00b100c10813114985420840d140145004411540d50405d00622002c100900c0031502520800c4800400c13012240c00100d42c90300c40c44040e4460382d407404ca1500e00300b08800b20000b040400403260034001684540c00c0240c0f61005070b51165226400744400c2000450740000345a00500440584a0701010001281d095038002c84040391f00340c2e00000c043e90b0040d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 70097781 1250 70096531 70096541
    0x403120908390c010804020d14070e130809010c05010603021c020102010b0f0901050108130503030705040503060603010c1b02010905060f0405031002070b0402060309010e0f01060f0806060a050f0a0b030910 90
    0x782c003902074403951520080b696201c40d00c074800790b4100032100c030019040d5150100d07804421680701c8490b2400d48501d008c13440e00c3e4a924015242800350a40100f40c41210a00100b0002038028021034030f802a202e00642d12101c1c03211045842e55201c41c0004050394405417a9421242d1003002d14542031034500c002400c6400b2940d8440c4a035840c03010f80b15982e1a030b200f056040d030b0000c0c00c142c41d99848215104240400c03600380104a40720000402c0001c1ea030000c080e01c1280d0381170f8201e45560b103810f41054262007034003000c07100160300502c15503100d01d4406c61420000c2c1c010304281e0741207616030000c41d43d242d100c904064041c1c040010204940c5c1020044c0d1100d40b90102011410003681d0340d520051020040d0000e8480c51010000c500c45000030751240900c054940201c031148154112058007030400740c481c0d03030011405890000b40d4080302080003486900002d00302d01c4220304002c10800403000300e0503030f282c0244800c1804100760424800035401a58484014807500c09132201120980e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 70099031 1250 70097781 70097857
    0x109050402070807170d150302010305010602062401031e0501060f08040b0105040b0f04150302010906110309040c23030a1a010c030c02010509040c0e090f07080403120908 75
    0x30344100b1a000c0811100e0080da40c070750b60b10020340f101085204003440294010482a00183c034a0140c0710704100d84441c102c001124070030f0724248440e88c3d0701c44080e40c80e0b0604031a1508000c03401c0f070b0800d2622081c0c0403040b59140d4141400640b6511314000c0030000410000100c2d12565520300501200342c00c400c00f603400c02150b04c2d050310240340c141e42e808005041881124021503d403041e801150342c5d08107040444500186c400c0000201040211358052a40d1100741c0c0454495100480c40a10503402c511034012508011403600c0c150605110080c04221000c3e01040250054010010b00341007440c00c1000c2c19050440e2a8100108588210344503010403200c0c02130300310803100059030071001d80220341c0c0e05418010306041c2c0d28001030341c00388140c00b9255886490180d003401b4168101e9000c42034110190b8015245503160068031090550039145000800c94580000380041c1c0705000460002020000100d2104a03030f80e250300494015004c030310031200c0030942d0602c0c0100000c1941c0030350 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 70100281 1250 70099031 70099039
    0xc0f0906170303070203180d08070501050703060905060319021206070f02010b0a05090106180306060b0715020c0c060f130e01170105011404020906070506011223031204030e100905010905 82
    0x18100304e080030b03540f03100b030b003014054603440241d104010343e40e101010203409400620b000c2daa11003070310300765000b40022104a4003192906002107411006880f81b10320445002c1c005100c86034610b4075488000f201c07184204c0e03004c8035006402c6c0030050144000c0e4051480c1347c6aa031118400100040c1c29a1030100015003d08885101003002e0359546038410b0440320750b810b021071404103a0343d41e580c1f18251500b028080c4e60904c0070000c3c1c2d80301e40c030740100030b024020512040b4103000298a40280c1c482c6181c0700c40f040d400b240741d200303082ca00a802450040880c0009a02e0b0800c200766950320030340c00354841000416078a004204030b0325864141580d0b420540001c0201e581481ca03c0c040901030050b100b405107a0101c3c42136181e403036900c202c500030b41d000000c0300c15a683d83c18203100b240c090b51034110303015079200203080c00ca020003003d020313000010000954203020b001600617510303c4006105408002202c005125591542c20446191f0f214a0b62401d822904180c005400950240c1c0b005000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 70101531 1250 70100281 70100287
    0x180402010503180a0507030302060601090902160204020a1e0201050403080f1b09041404050109020f3a12090302120f0a081608031009050708091005040c0f09061703 72
    0x40c0c0e448411254401e00300e000d410625844080c05920385840c0d100010494456401c0120506800080942c45644242d807030240f01c0307854891440c240e0146028a1801000446941c4010301c7d01e83c016040c0c01c0120b2800b400c001f040341c00c00501550148103a0000b50b59603c0500060641c400e0807590b02c500150a030020a00389100c0701114200351820380b901040d80450385500747d03526500101400030101142c95514100ba007042402000c91000480c480c240d150550105130510003a161160211007030304000c4e02c5040412104011041c2c10044450180d007c03d11001543c4454041c2d10500290349a1455604510620092040f00c81070845194001c1044a0800e40c0000781408082d601c0581940c840c5140b28900313400422115005220a00210401040700d107800545c0d4226005141c0c1032218bc0c44541007034586030340c01d85681d00706402048001e204a0b186400c525080391162058420240d44c568905442c1e000301d400c20034101c0c1c1c4428082002401d01da040c0c0190141d56405546 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 70102781 1250 70101531 70101533
    0xc08061008180114010806010f080a08070c0f0306020d0b0301270f0506070f0f080f01030303180210030e06010f0605090d080d0207080406020d02060f0a0b032a1804 72
    0x202010345004020044848009408507414540c400c2812001d01c0c0280604407000706001001102406407520511401d000081c1220480d040e010880f0011b02c01b07410b400c074403619882466804230b503050700c0d2245289400504520312804003c01140107680068681030040360362801e075201800c03441c0c426810100c0342d02c0010000e00c89580c000c0460707a03a0300d058103164075004c105241c0400e006029130150404120301c6680060001000c680c90b41d55051b541c8010b08410b640841064807202c3c0744419000042c80064000e6008000381501e681c2c1034000700f00b0340d60000d00080c0e0b21102c5000000d48402900c20014010800e1074050711150181c8805030342818001407e030700034036801900c50514915081d00b0301400404480c80070009010a540d1100b041c00c140340c0d903500511030880144120103000c40300c01d02c0402c0c5070b400b034418040412040d0721401101009088407008403036040c06003d000c4500584103c0c00715484141c944542162151074004001c11003890031032a00507405040b04000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 70104031 1250 70102781 70102789
    0x423040f1515030e06090c0102070b03040c060e010201090f080a0306050604050d06021b0a050c01120e061f260715141308030d06090f090203100209061e0d0c0806 71
    0x20701566603510159949a450040840c090441d803450700b041070080c001880404d220108840080c4038080e003c40d405240e0380c280c2c001c10b0b84030494016241403580002800a90321880e00c03c21f480005100118141d1100e0b280c1026248200c81d04582c9024005103440c41c080c1c150040500a0504550060a00b850100170600301e52803854020310b45503000902d40403500d020a01c4031050f01000007203030401c03d80d51030103c3c1e46500d6044014040f0710025401601c803140c80c0038598002c0e900401034401c03610341500169010030314803592480b840041c200400c0403190340b00003079203041d000711051110340e16106d02141055a150818070301c00d140f4284540b180c2d0780050710790b03407501411a5440e036111340c031041030050740740d80303402054285c000010503500d40c10b110f421050948003800030400c00f5043c401010f400f10340c0d0000000b50160800d803240c3c00104802c2d8003400030307030308058800c51501e003009511302040266903143c2c0e44070500c049440b06040035203100b8088402060300f0030765060308010b0000303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 70105281 1250 70104031 70104071
    0x3030c0c0409170309010212060a030f02090a02041806030204060905070507170d06031a06040501080a060509031303030c030f020703031710260c0307030b010605030a020423040f 78
    0x501d00940c0c954035103004000e002507900044001e0302480644a0409000d4039000c1d50020500388000100e00c1c0220340302e0701c2e200040c02c045030350142078815041c00c03d50920401d81e80080c03016003a96801c0c800011515403621901004200c1c088001800318114410081100c1c0e180e00a0750140b80b0349010401c0450700802282c10a41d04014200d8848482000340c0507544241004100305900b85200001000128141c80c12600d0001c14503545680c0da41052004852092107400700c0303030303004a01031000308d00c5541c0810f4200490006407131810640291030003103102650301c22030001d02a00034410500d03a001158404c0c888840c8007424410380703140c800a11a114515003680200c0310030000c00e1101c111000c82800900424544070350003100299200801c0c0600102c4003480e00075a0440c6801e407901041c90b000360380c1d211310ba009070780c0d0901c14100e8680c0c00080418000941c00c10020562018511900c0b1580400b00301c0104502c071500240001d40e00c030700c503a95a44d203041c800340c40d41103c1c0100003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 70106531 1250 70105281 70105303
    0x31632010c0f0203030d1413030801060c020607060504030e1503060d020103020a03090b07051905030105030d0804050a050f0a1101020604020109050f04090c0b04030605011a07030315081f0b03030c 86
    0x2110407011801e040411116051080003503040c800050b0400c0140100d800000c5116070302030101085640b60041d4071480c8203410f23030080014505400500400340135030350302910940040d120b20300f492038960340c0328106c0e2030544095012800d142c2d02c0c03081e1071400c500d08100e042c82c2010124154104500460341c03c0c110302d08001e0500d038002c590018441e00c00d40c00746000580201032069030b4104040044c1c080e40c800081080e035041982d00c094070a5000314103c034100e510150050458080080b41150303c00c0001c3c0040303907039010b112249030118500b000b42c425102104070182824012034036110700c010b240e003156a03041d034000b0b80400005d80e81160f8542d0840c0c0382522030148840d48180044d0040200c558002c02510b440c00740402c10160780c4016106481c4214404c00075640c8a503401181e400030003845080101d800c008083c0020300c40d070840055080d0f0306c0c5240c50b07403079101c03010641010891010701e07218a9401e2455a808500c03801000301003001a030185140010b801e81a0341c0343c03400448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 70107781 1250 70106531 70106537
    0x1d1209032401030f080c0d090f090c091703041802030f01060306060806010c140106031a090703020604090911060c030a020c150a030e030c070609090501060527040b03163201 76
    0x16254103002d41701080700c0c04191b401040d26041841140050f0245085000d00c1c0c00110b00030002043c540d516201e16410310b0b0f03031a221825181e1905010702d698550440e24900240018403000950401c0d01c68a18003800c1c01c2e143c05a20303072070690002400540140d000c04100350401c1420041190051040c0c1e40050003841e12007600744290a02410420b11140210115841d0041c00414883d540e00c036004a1802441d58203a60b887d005102a0f071130000c0d0001a40c07008081100b0468480320b5401340100510810b400b140440c640c10014890350000d110090b8940c0001407941d1200354103005550203407001b00c0d18001400268642ca250a0040905500900d96210105d04010b10100203880341307400000c08a0700c0325912200d00404e21500d62140d50085800e060002c00c015004038292091410b80e11000d806030034580c5501241d03089084030b40340d0040e65403000d1020382d440520082030260745c1c2804001c250780c40d101151075000c664468070500000c0140201d0b0507440705c1410144805002d107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 70109031 1250 70107781 70107803
    0x516051801020c100c0303060b130b1605032a0d0f0509010c1203060e2d0c070209090318010804020907030e030f0a0807030f021602041d120903240103 66
    0x180180e1610f078001d01c459038081041c0302800002540135106101003803080c1d40070700c207460703a03400390390010301031180c03038610100c04510244229030075400a001d40450100b4101212036a5441721420341d4040000700b428118880000c0c0280907030310600c0c02c001149013004045104601c68024030790300e003507554a01040b50000d01d00581e80c1c420301c45d40c101c40e82c02c007018554580d4014005030080c91644900510000308070005001c8010f1462501d0120340c028040580010440c07420152401c002889050880340a1044d5000350b02d608070400e12503100140115541c00ea40d881c00c1d15030364101d5554504005840c010800140c44041450390842024140030424800e0400c0382803d41c0a542c1c802c110b000804110001029400440207000780b00e1fa071400c001061004041005912a500c55034001690841c200c070f005042582c03201d54141490240792035040301150586080a52000d51302000501c04a507103012031409205802e110120401d0300403040031051102e0601d10070500c009032070002c400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 70110281 1250 70109031 70109077
    0x60f0f08060112060e0109050a0509060f01050402071a1303081605070204050901090b16080601140316020309040e07031703060a091112070c1a090718090203070b0409051605 76
    0x10340c000001170849044a268650b844004400080c04101c0b52103e0f050704100114404401c0442e40d180101c01440b107032400c1c6d81c00e000900000e9407103c0c07070444044154101205041130303618000340c0540000c8a50005002d80307400e00405840c005018910382c806003040603002c2a40280485504d59419240840c0075503400c2410b5004209842000e002581c02e04100041d2507901801160009059202d000d4113845030001124144400b1094a0b0a1901000410f0f45000b0130201c1158254031441264641a07e0305d01040c01c0e68400d40e00d104060380501400c0c07081007400110041d01c000c100c06414118905000002ca00d0403142c45401c07503c583d103144d002c900c5017200049a04950030001d003040700703041480c0000e004020f5a107085d5209003445444070710f01c450100c1d4040c00750b092500282411400c1c0000c90b20702120101108440c00d6480303850f40b005072003c0c030045008256802c28aa103661a043c0350205840c002040051710f500b00707032144606203801c602035440e000c403070f801e0b00c800b88555 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 70111531 1250 70110281 70110317
    0x60115020a110d05070605220303080a0504020a0b040b04030c0504180f0809090f06010314150111100e0c0102061303091203210b0102010f020301050f060c10020c030301060f0f080601 80
    0x424034090110b0162017004a81e4503000030052240161102c41000e00b0080c074005001d01003010301000300098143c001183d900c4005c0c4c0c01a1740c2060000b04915000c550302c48041544d035000d9800b48000302c0380410200305010328102c0000080000385c80600000e6003401c14401c43d120300c540001d103001d107803001020a010381c1d842070300c02c40800507114856a060440c0018a500c04c1100c125001a0424a2011310660700b0b03c075903030140c3c68910203018601003100064640c5187d401410302c041c0b0a50001e44502c94240c09003541071645400078003820250440020b040510083c0401e462106d03042042c1c0c0001d60101000c8c040701d442c00c0542550f8404c0b443d0864056940d135414048800c4601901103040d52240e100c1001d40c21309800030070031340c0389150001c0c050740007d100e0701d98041811400d4181c01e00340000104440c03038080301a00c01f00750155401c4003ca0f0000320124000354000310041c01030940000c610612880346040ca402c40742e0001c00e0003010200010b00c864100180c1550718203941c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 70112781 1250 70111531 70111549
    0x604050d0c050304180914030715020901171e06010c0b0403030b1c03030e160509010306020a0302090604031212050f0a0b01110d120b060a02031206130504050a0302060115020a11 78
    0x18501d1210004c1c1410b02c1c003144c011b4081202d060310105c440030802d540e84a400411180c0c00c40c0d01401741e0b41401d20114928009410105103541800040702c41d102042480300d5045101d41e6601e41c600b1903048094560180d084001880c60703040c00240e0822001143d007409985602c580e2501d030101c0e03c071000001080d28a900901803150211929586604050300368002d8008a80d0040072a11107542c01d22040382c40c07543e1442050340268026006002040c2c45800070980341c200d6003401351a0103420030125406a00070703401900c90140a003511064940e00c01d0820007540c403422014825401c141d81d0002c0c0100e005814044000d9440b801c0d04266400f400c006468000c1e05000e0b83c100319215003002e0710880c81c1807942000c1c0392800400b400c9602d4490103542c11b0b00125802103042250103681b01d081060040c00041c0e0044850604140307400c1ca80c0147c51003903100314050036120819140c080d1601d601a04840c40303104c2405421601e65a00003082040c0c55040380711403407520048000308881c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 70114031 1250 70112781 70112789
    0x1505060f03100b04120510110706051302060301150e03030306131806051906050303040608040b07031e0603060c020105090d05090a0305010f0c0207151403040809120c120604050d0c050304 82
    0x800c0200b400202048009605c07000c0c540144160f0384203520440c0c5080440350650105c1070b080c602480810b0114885603c0343da40058403076000702283e4119000200143c02c02d9000162040c01507060491040d8814402c0c090070006030011411401c00743c000509140c401a11100410b9640240ca400a141008039082403034100d6000c0190381015054510695030200c1c0ea4002c050603d500084c043c2400011101244c84d5031b80d80c03142a07140c0b60307510381180202400c2c0100b05a02d0b0010328801c1e081000d004150013007603501c006031183c51840e000b02554501c10341c410a59140070108005000041182e022310041468003a6a450342440000d201d0103541e08090301a45c600300341d0305c0044500c1d6002c90000d40c0c090b000c855242d580d850354110729102d0bc4007a0300c0007800e01d2400362550f5103410050b507009440b603000c0605003041e00300802e241a00c0000313040803552043d02c1c01c559506003401c150700d540c200040a88020b02e42501d5180c0e8507080860b8480411600700b503d482482818016130703000d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 70115281 1250 70114031 70114049
    0x5030f2b090b0c011b0e030f0a05060406200a020a02011704120e13020d151e05010804030309080d060512010e060c0a11070806060a0609050108150a0f06080a1505060f0310 75
    0x71a001d642e001b0080b44200d2402400380c403030700c619032456500010302058000c2c0e012004224954035076581030003916210442074060410f4440702d041d00726440018162400c0d5030342c014124207501d070000400010824400c1141c51014100b400701044401060341481034141c1014580d9500d801c011070000b01c00032003102c111170700c0403034000e98082d4581c1000c454030b044480a0346400d500d440d2469480802410002d8050080e2801005194081e0945551040c024280050560300d9070320340c0007040e40800000110740396100c60510003803900b5850b149024003064020004100f0f540004da5880703002070300c04940242e000c15500303c118800c00e1089100c5131100b0030340c0e036690740e21070403e55103c40541e41580b00d21030542002c00c4840c86420f0102c22180141e442540e940c075220310604458017501c0d072454100d00d00040124040d150100000c00500099503400343c58506a1038840450782a4041d03800d440c00b180d40e08014960b5039a094441c69003070070600c0e60350303502c60006e0843c1802003a44985e049c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 70116531 1250 70115281 70115321
    0x2301080112060c0e1309050c011b060b18070305091c05090904020a080327180c030603010f110a0e0906010801030b0901020d09080705010f09030207120c05030f2b090b0c01 75
    0x240043e01d1b080503412510500403104c03819210001503e00b00e98445080a070001c000c00d40038041105604488a10040580f078012414030702840f04082100440d00e00010a80b21020b104081e081003040300c641d8481d5903201102c8800c501c4008001d44249222a8860010503001c5020f540e13844040800030091042266554170b01c518040c000c00b000e1701281850040c0003501840c41341003040c1c0d4400001d589103116001c564a130028000e01c0c0e000600041e070107641e902d11065424040d8821000510782c1c420202d512482c0d00e400041410810396030507802542403030b040c44070990b000282d8034192070340505109082d907224600c09009000300c0d98030100003420b21140e4800d04c00e004005066460042000f4046050600a03a00030703182d1032480200168000502001250004420000074510612004007183e5236100024075000d624510040b140e0003152029038106e000c8241c07580c0d807440064140d07034102e4a1710300c040c1c1030881c00e2150009a0500180c1440090f0081d80100b02d4240f003500b034280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 70117781 1250 70116531 70116559
    0x8010204060c0201120207020303030f0702010f051f09020c0c10020f071514070b0103080a021509060108060709080303070309110d0b060405010f030506060d05010b03072301080112060c0e 82
    0x603410b06000143d0100d4154990350b10f100085008491803540c002d00150300d180c4651010341d40d1500003c0210741113560321020000d100c005406502d01a200300c400040e5580600c9960400c0003a0b181d0240007104d204106a01c19040c0100302c142c00f01c0c80c1281c0030300400c00260016030500b000500358001c54043c1c900301091008a0841003030140d0000c0d40c900b11003030038056015889100d80b1401a01c2ca078005001000000c4080c0d0040c08001f5881c4140c5482c85109102c4c41a080390907075141156400000042c001d00000b0498258032254510701044803e29020489880c0d2001a18410401d0344805145041c80310840b000c011814000e071a000341030186060003102d0b04016030780648214200000058064054500c44c0c0036aa003240103411541c40344002c05c80c4411209404a40030b5403103c4150499035001c3c00103900624904010300080612064507544002c202010641449401001805008103c00f080003090341d001d0000107103405410300540700310a40d03d00c1280e114203891070385030f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 70119031 1250 70117781 70117787
    0x30501090b06040e040f0c12060203060f0d0209010608071715030f0c03030414030a02090906151e010302030405010e06090f060a05060108040219050301020304060203090f060903030109020f040801020406 89
    0x50488905034010450780e4003600c1000010b218038480c64009031107240104011611341a8202481c1e84607030301c92501c1e184d449221030402c041c141421b0354080e50200400450307003030032544007080e00022208032014401a0307000071300300302041c09044108a03900c800141950f005200d2900070342e01c040703403244e190329120300080000b1032290052030080c0514410066013132000601513500400050241d800c2c10300380ba80e0111032607684030845038584200b040d200d003d600c03007401c05401003001c00040d002034545903503480280e9540200c402e0244400010100705252800c6071156000e0003440d016a407078449051990240c15000c64600850058a0511584040002d4805000103442055802a0795094103680c01c454045500c58041100b0b000010018688081140711a070441542e1040c0d10751540d010a08a0b00221002c07111103074000244460414104201c0c0030305034403040102181d02c1c00e10340b0310342c0b01d000601c602c038145030300401c0d5028440c04040c103a8011305103950086480d295200002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 70120281 1250 70119031 70119041
    0xf270b0720100c110f120a030204030f123209011e0f03240504020702030f0607050403021518060a0e060705010f110a0e0d1104021303030201061512050c07021003 71
    0x9000420540f0030420844c540c00b08900300d21502050240864422150100300d09521030b039200c104040e400c10000c40001c00c1c00e0100c0c1e182600409050350030022003040680303408040c00c94584645100c031080c00700c928030643d920a6001ca8100c031680c90340c01610050780d000e0000112981203007000c08001110503800386600e1804903a996040c80001410340076920342051402c02a400110340d20014032003811b040c0c00410059102404481d0703048000030701f50341800c109640080c00150000303010001e42c60440d4081341040e40700c07440b0614003031690505480442107152401e00a22000c00c3d80d04811380589080403c613080540040e950b1462032606074002c0001504421080340343c0f00040144500e46c0e02a01c4065a094543c007030400800300070450200c243c0c680c00c0b1032107513a2809007545925640081c11001c0c25400c1c548241c14194a0082d01f91212500000074a030022000c200b00503620210b05081c1131f004034400680e54a42c1070065005e441a8500030350084103400320f004400303615500c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 70121531 1250 70120281 70120301
    0xe13030e1008061302040302090c0703050c03040e1005040e060601080a020f0c06041401090803070503090316050c0a060311041a041502060406060b090d0b0a0605040f270b072010 78
    0x51584d4015210510b00124041c030701010390070028003c00111142020402010064000c1c2440360070101c659081c14603642c010341000d41040302110a10080c488013007600e001800040f1028403007140b8003200e15603141002403040e41046140c90203d0094409a0304442c41c101c20026860340d15400203109a0f9540d009a03801c64000350000440e041182c0117106000615601c100514915190303902c0484113504068095000d44c0010407001c1c10784985002e60301281d521803c0503204110512041100d803241c41c0e408581498240b900700f0701740d031002400301c85c1694517068110400701600c20420f40c00e801181c1014118020041c901900a0340004c1c0180c8140e01c202c0781804070702d4607003140d641c4a00480c00742942001c0b0141c0c03140000b0300c007842070325400106039a00007a00c5680b90000340644141c40000c190310ba5840383e05140304400c4180c00fa606407040c4840314a0300b400c0f5980d450500500a0400d02081300d842c000c0c003410040029416100c0003010b0031240e60032980742500b40200a4400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 70122781 1250 70121531 70121539
    0x51b0f031804020a080c07030e0a0608041a010b1b0a020603100333020c1501090e0d0e060d0504030210020c0c090105010309020102060402010e06130f05040606090e13030e100806 78
    0x1001201464540203c44c4e5800c040d64465644e5112510f5207213040e0000101101030010103a200741640e124980c1d6903000b00181e43d030b001064106424002c00f098056180e4190b8240102d00512141441c0c0040b1045040f000880340c00c1d888180b03046a04119555200035800039001041c04007140c214056002a03d0086141c03c1d541c244003000d00404501c40400740e2180d0100255220407134001f90b0281181030071071020f07a00f14007080a840412030100b604101c600d50303555024900908010031007950ba0030410704000f403480c442c50700068400d025003040c401e6107079150000503080507c02c2c17007580180001c9030b80554440f04030148054640d81d540000c2c0d40544111030000030f080d8840e0184500300758040e009821503480301c4d001141c85400800d00960454010460a40e0100494020000400504e0030019001d41042c0070071041c0e410741d5100d0741c20800460b0061040f05090210150400542080c5aa8000c414a810b40c2c02c9040d020348541d0051820028000c0c01d9040200b040c8a100c00729 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 70124031 1250 70122781 70122817
    0x60201060602160303051e07060c23072904050706030b090c071401061e0f0f03020a1401140f0304053018030106031b05060a0807051b0f03 61
    0x50012aa0f031400b050840c41c042440e5001080030134011802403401d9519094004004d0b424410020080d50251a044580c2d541d01c150701401a507229110080102c4054102d96814029055540070f034068000c001e42580c045905512110030900f44400300c1c000c194000c8005460907041c0b160f141c082e140325620101e030030003910b2407944c5000c0b076605105410030801c081c240001d54075807041c00860a1848401996201404110503068000716102001c0048008294505041c0145a403081c190301c0620a11400f41040c00180d035410350103010b4584010303c1602802120b00120b80031f201550b140c0f002d50000090707018140701c400008501c48c600610403144002c104003d4212403c0c0f000b000e100b02408174888211080007440c0060100c19065045500710f10003440c0042c1c00c4540d03c0d40205e4080744229000c600160020b090100200021615241000349041000d41601402032240041140005a03200b81019040c6810305010f6038004179042c62101c3c5407059940c1d070241c501e5102c3d41c40c1d03003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 70125281 1250 70124031 70124039
    0x80c060108060f0115030e03030c13050301090f0209130b01030309060e010807050405060d020d0e1609020c0d0f110729090f040b0d1b0608150904020108060105070605090706020106 79
    0x2409401500c50341d01c0524180c0c0b07064030503c0c645c40c803240c100c0d04240d00d481d00c048800d581080554010b603800c80381540d60f040e1842601c0100d540d640c0c42140241d0502c90340d4400300d1200c0d440c41e05e465030140c1e9107072815904c55102c0180c03147c1042e0020304090b8110004024140e0010305e540c2660f445440f0919040c00640040d070307818504490b032400050013000140803074184003002d062100c050603005801e05103090560f03802c0c1c41903c08030180307a9006060a044405040d07505400070105c06800714989080c00050544a03100a007066003440040210040d6443c8140071040c0400034640681c0c0d144e6440e03e4607a0b1280c802d0480d07400002c1e0a0030b195010300c00f050b004031040d00000501201c00c1108143c2404060700c0050700c0a58042000e0040b040420003044c94032692804030280c0c5560603003002c1000c0c2603940b01408000c590001080c106040780c8910450a8001d50242003c07402c659507400101c600c0d01c60b0040007084c4906090500c29002c0c00050301005031101500240826a25 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 70126531 1250 70125281 70125283
    0x20d09080105130212030427050709030c0b070c080d03051b040506071103120a090e0a020405030303041401020c0a05011a040e031606021303030804170310031e0c03080c060108 77
    0x2643c10001c681c070a150182c00601e0a0744540190b000d000054a040540d5540112007840d002c5c03183c054a580b985032107002400f41481090b6010034a42401c2d81c40342d095072502e0a254940d4080c1200b400030018a44050001c050300d00c0c4014140001180c042001005c03000300a0b00d8103581184186050340050104001c0c0d030400e440036110007038031710350421900340c8032a05420400c40c10300b5014015030144a214a03c040000c1803c03041039240d00ca88649042ca1403061080000c1c0f03003081551040c00b00b4041c5540110481c0d40064000442c9440c1c0c030b040c0240c031402482113144558a0f8071400c0d03940010030006400c8036801404541c4880080c1141e40b0034002610700a03d450b8545402c00c0003001004812804045417460040500504000d23041c00a5850b145c3c0c00d4101740c000c115220300300420002c20042c0c045a5503035480307405003141000c4210040301c04660000030040000821b49403a0b03c50003000120311982c0000e442d41643d0b56030f003410340b40341d408810165a2405050008910158 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 70127781 1250 70126531 70126541
    0xa0e07090606050d05101220150f030910020d060807050922080f030709090f0905030d09030c0c15081311010e040f0c120e06130303090f060c020d090801 67
    0x9410f4444602d0500d10303524010040400600174103a01040d803030040740940e82d982c19030100520078104e283c040b807407001c1d12070601c02c21100c80b544110b0303840b94016040e800007401d5070a42818015516265119005124100408022081f0300746201140c1d00850b1060340d0003240c100c800d84400e540c0441c3d200d4080c8440110100c1d62034102c1c4400203081018a1030b0128101d002034000e900241c101211040064242d500079100000050b000c00028046003005109070721140c8000c600401100380c40c2c0c1c4e61103840340191400301c5025599601c050083c10300409017641c808d03600c100c851109a444615020032000c03200b082c01d001408038000640d54001d0a0404421036800005000c400603920700111012114045803e401907290030203c40031114074010f40041010300c0d12501351165910070250102d1329400d0b0060910b90003c801d229030385140e024000002a018980401e482c0308a061055202c2c0180d0710091403d440e205804c0d58195002c2034846617804165140168290f4420240d03090301d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 70129031 1250 70127781 70127789
    0xd0b090c030408030603120f1207050c070e0a060503070306150f081f0e0a0f02030c0114190201060509011d0c030603060f0a0b12030403060c032007020307030b0a0e070906 75
    0x640d04202207070219814a014542c030002c02400c69900803005181d13104560822442c8040f041d10104150101520100740740740c0c845442e24040c0d040000c2004c089030b44401c6841100c5900e800c21002c5034519040d07403c080060600541184c900503664070740600241803030a0401d204c0d00f4042404a400302e00c0d031a402d811682c01d00700514650740b030110422109080644411946640c50102030001441400309110f078900030308140c0003800f541d005060405e42c04660349070420603101c0000407415035843c02e403000e801c03001c24500c507004042d2000f039006023036541080c0e602c021000c00005030400007503001040383c00030b0f02200d001500d92081b040c00c14003040e2000c0b89c1c541c10000000700c106911950080c0c3c021444d80c4040b5442d0a440b02107610395100c080d4840d603542000805106100b99030040031001030461900b04215503d80000e1642c00804500020250600080a01c20b65804000c448080c2d900401c030740406007401d0b142000185407201d021783d01070054120020b4000040c0c81810215 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 70130281 1250 70129031 70129051
    0x21203070f050c010c0c06050c0c040f0203100b130905090309040908031504020703050703181802070201020f070303170406150b07020f030109020609060f0403080706140f0919030e04050703020d0b09 87
    0x11b604210341a2080d8003d0b043c1c0804d04d204140c0e80f501c0a645a010761b0305c6410b0f502ca001a81c078241107508030303409003064000c1144005d003001030008580c1186a50342c122100414005020348400b55042d04600c12056a86e40c0981000150801e000b8400021800303080b054200c0e4442e10706075001c0c4030a900500f040503000c0f510521144000c2400341120f041d8880306190901c52041c1c4400d910240703455100c0b4000704c119800b04082d011544c04100ca00380401d8520000c260092455600402c203c00f4510342c80c04240512001c5410405542c00c0502c0f407104402c5003050003529641440e02c20307004000141e1041d1914811300045003018440c40d40a1034019011340d00e006400c1044c40007551144400a188010801001001c200c20700007620b03a2a225003800301d1104000e01c0c01208040300031b410720520100140a01081c2080040c0e02140c130f0301d55603400711070301010b03080641d440c8008011a07a005030401d01000311295165000f09155052050b00308000164401841100e5204980b40c13000c2c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 70131531 1250 70130281 70130303
    0x10f020f1b0619091806080712050a050d08040b0109090506010e1503010905030a11060108060a1104120c030303050a02120a020f090612011805070c02010c021203070f050c010c 77
    0x70640e94450714501c07003401601c4540340c80866507003041000c590402c55000100700c0e0809100340c1e641c541c83c1d00724401c1c0f02002400403c0c180709800e03890b4100c500c18048000d000303018020411006008881d002d0380c1040035504842401d14001c2d00840d0304a8040303541c04021400880d03031190502c6052039407078000e07000300190f0703003040c4840e0b4066002030710150703401c3c1c0701c07512100d900ea80902400d000141b10720051a11004845800b4000241d14559191560003c00c0180315050002807050760083c80c1c000d010513103400f41c5134841e0140c032494002c00c3e01c81910ba02d5150a21403002c00c0300381142d00c6641c0410191361800a18008ca008803545c2800301c250100115600d1030b015000b9060469a1114140c03070220504002501507201600168601034008010440310201c2000c0d081d04240d03079281848907140940005100c1050000d0090603c54181486403e54540c02040f614480384e0108996540c1c0752828600c9800d4199141260a0b10896501074441d500c156003240b01c980d4810710030b102c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 70132781 1250 70131531 70131553
    0xa12060b090a231009060602070510030b0102120d0207020a080c1f020a030c02031606020a03030b030604020a030b040c0b180a05030d0516051c050d050a0b0906040b04090611030105010f020f 83
    0x582076405404030307021300b00314840450507034010b10494008080c1c5400600c2e0a0341340106000001e94510b1610091600e08000c3ea04944d8011440d03892820700000901c0d5941180a0800d00078001d011019402055602001c15806400640341d0050641100e51540d0042e0b81100315440c0601902d540e00141c00ca4490000042e004080701160244010107480841500c41402800368129500c0303940141e000b0703a00c1405040d0184242807a482003500500180e00c0e040c1c01107407041c0990f200003089250040c0000e002d1044035442d40001e40b03103104000d503980c43c0c07000c101086000c2070210540304200b00313080000c0d5483c1c0051000d01d101c03030b180c42c1d1380e04000712182c007003000c0d80083c1c406451a0040091600385403800c42010402a0710395140c103510758280004000840d80004c1c2504890303460488441030315a00c202d00d50f54040412a0086059031070613005c20013a00359401b00415490400c8458991403038500040c50607201c00f81e0780c008462071480c00403640c0ea443c541c06042550081082c81c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 70134031 1250 70132781 70132841
    0x30b1e0607031106090a0201080709060905010509060712030b040b0303070b01030609020d0606080304062705310e010c0804080304020105070606050603070206100501030603030203180a12060b090a 86
    0x41d2460090818100e524001000c650505004851512054200c40030120440d83c00064013508402d4500d00400356505042019100321594040c4074140031003c150090159503920480d94a1544602c900c8041c052080d030140141c02940b001c1481030341000c034610100d04000082d20001a00820f0203920b60b41f8541b10100101040c01c01a0b030000007501c0b80d000030070500e015801c010100030000310f1351603151070350040c420507400010800300c41c0c03d0022042d49980c044422400da450880305e403405001074191442c2046003509818509540c9001241420303522a07000003002e0440e50002c1c44400350841e41111420300443d001003440c00113201044c00355108402806441d482900d000806c0354440d4009091034104803480c2c8010f80c007140800c00000205101840208001e0a05100207425958041d46030301450300c1c0b034000d911114028484030350f10400440020400300811802070301a5050060141c030000c0500350081c0b1808012601c034010920a10300c108400307011802d45070381707150602 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 70135281 1250 70134031 70134037
    0x40c0305161502152e0b0405040b10020604120504090e0105090106090608030301090b0a05120102030601030605010e0607080304110409030c14061015020a020619030b0f0121200901030b1e06 83
    0xf940c0d0f40078200a1407a0303040d4400300b0b0f02c1c001e8901b410880d5111458101084142d1300c83c5103c250107540c950007043c0c0d00580000b61645c002e54849508920301240001c121501d0103654045d00c0c02600f4950302002060066000314080c00442000340000d548036507455042d00c560307228031020395000704010440022560302c101c040030700040184401030350703074000148185000d14011800365030000c02d008043d0f800d44580c00c0281000e00f422400c0d141d02c103001074414028080082d2400070004005410048450340300c90008a00a00421050b100703810018274a003000c940480d154840c0000e000d029200005220307204448210205110f103040451042010307205032000c2d030039032140312884030059035608050041010000e031070246102c01d29800500b5100c1062004d401030102c80291029030340d03c4450030351803c2c00071842c0c41740c6080b074860601c0100301640b6001c80405840140629141c00d43c4001c00134000266010310240c0e142c503003000808c1845004107040c40ca070040714004541064809 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 70136531 1250 70135281 70135321
    0x11b3e1f141605070f0617060a05010c03260115051218030702030d1806170c0c0f030307020133090519020f0c0d02060f0f040c030516150215 62
    0x5000000b08440d40d0b07007443c1c440b69411046003040440b1090250a5001041c00c0c203850740c60f0030800450a008011600004550040604016091042c3d20070b05000303c86125008220702c00c01c05124a04a06204082400380030310340c240c1e08e4001034850214807a00903036422500340002d02c050fa4076011040342c20240e080208801c140030030700040000da0360601041c0704540c09519a640c481c882c00c40044100c0c4402e401c050140700700c0d07010a03c804034030200959800343c4202503642d612032245c9071451402100600c03c5c07901d0b210010400810540c1900190003445116008034050030b005042c45c051010980080c2c440304500d17100401c80ca9190b40c1200760024448151003030405040e1030013400340e0b40440c2044005031000248260900010800b440c0d0048551001e40680d003055070015455000c05051401c210044030041380601c030801301c2e460011035000e021034050194070003141c5050103e6125100b08c03c050000d60845142c0007060360340d01030510205100c510361302c0d0040798001a540c492 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 70137781 1250 70136531 70136557
    0x12010602390424080c0301060b0702040f150902070605010f05010c12050910020304030209060d0b04110604051806040b0121110d0903080114011b3e1f14 67
    0x34071203091412010210704003003c3c1600158085007030980d0a40742020303420380c460180e898043c0c201b003c0100b010545040a504580101e42d440c2d0340010500505941d9040c4000407540b00c10000c0c004a26a0081c02620b11543c0248460b80e40c1d455000300a074000d1140601151202e031b449400100d02c00c1c1081401c50a5090440c05c00d6002c80104203e1020542d180d00540d20018044c42546480d00ca075560100b004c81c0c40c03070030401181c0da40380c0802ca0b016200602c074080f40c0940c0b183c1c55880e141030314098040030f4180b0a20001e07030445030b11034400c169205030150340307000004840d9504c94000740c440c581035080c459101003c12680c402c01002c40400701041502c06024441c9195414002c03c1c4038103029588030f08a950400e400016a00f1050400758148100b50000240704036070080c001f45040e070440d02c0789500c58403c0b169411529180850b480030510720114155003a00845d40c0020303d684180c4455080059590600840303841c1250740310040b41c481c85080000c5105070f0014448801c1c900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 70139031 1250 70137781 70137791
    0x8010e10030b010f0302030105010803031b0c0c0301091110020a051c030b0303040b0705060702010603020d020909150405061603020702061608070b070e0906010201020a170601030e03120106023904 86
    0x248415aa142e030070380020080b50550f50040040d0324090065901504020020350f00e1400c02080d28003500701800005800ca0002051990000009000314044428068024042080140b030140c01c07880c1c110700701610507040b507074203d00c20b0b502c00a40f40d02c60951200041040001c0d1a4010f401e0030280303004401016110308000002d51003e0005e04020844000220b441d070585140070790074050010041e100b10380c500801000580da8510241c201c994050f1004403841d00c514050030300301180d0350f0003292014181c0c01440100900000c1c001c2c801d00c00840a00301c4440c540c1400c030709074416020041d600800070300070604c8002500803503000d0180704a400a1408826036941c04a0072801c42c1c060380480c1007202034020317a0410500242c3d100200340300852802c844e4841c05403da140703080141500d01503090000d1082d0f4026440895a055028101c90300d4400c0b8140529910f0310034021540140140a42c050003007000c0c444a03502071001d0500c60720a084a004000140f103004418650320640711 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 70140281 1250 70139031 70139033
    0x5090102070f080a0801050d050c060a03022203020f04061d060a03020904140601050a05100e270a27080d110a020616020d1b08090603130303060e060108010e1003 71
    0x40d0304440b4054443c01200303844414000015121030416445540100c80021452001600205415a0402040b82d500b6200c0c800700200310024001d100002c012143c5107000c64040640d103000c0201201c0c4219044081219610140070660f4103c0c40f41d00101699501d0342e042403000b07249450b503c001302034205400c2540d60780025040c0c45c0d0a0380c0a40741e11000508142e04040c0911055015090586a4050b007902d0800480c1107002c2405020080050f81e8851052660b510403058114060f1205020b2560a103c94102d40030392050740c11040b12072801c007004246142460792048048212010902c03d8803060725a00d400d81c4c40458008000d42c0e0b1511468940b520b02c0f00640740c200c01c02d40c0109003901d1b240b40d003d50f084000c0d65101c0b003903510020000541c2c0d40e00000d9481c85031030400c40c0e40f0710302c1400d1030112400c2c080d41400c954050f030044108141e4481d480c040020fa94083d03a0203000d110395407141040306d20400e4486600156031500184a00c2d8281814144c2090f00d44000003015596 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 70141531 1250 70140281 70140293
    0x50a24050a051e0702280e0705070f17040b0d0509010501050d030f0905060d020301031e1e020f090702060708011208030708040f230c0109080c0906031606030504120e010806040509010207 82
    0x120100e241e10305090609200030f043e052000b0706d0050040010812040d08041d00050a41c3c02807a00080200000401d00c1c0100318901215071450049240b46989464541c603c4c15160742208820140e21131400e00000c000b0801405000d040798406440034491011a4808a40e2101003c640400b88440d030180082c95803640720003441d4100d01c110b40141c507941145400d603610307081d81400b402c07100701a240c400041501d4030040030030401c42c414586c1c29041e052020526805c041c15007581d0018290041000d01900810800d100d440a42d44030a941ea807150301d0545c124962507400f6210517010b100141c103d9000d50002074004e40240d008016900d1540e41d00c00481402e110101c8109564541d1400c0603c01040707441000c00003400c00c0c2a9990600b0b02c1940e49800c440f1090740f2401314100480c00c44d440501460500442c3c0204007a080e41c4c54030f07000740160500342d07003c640c00c03a400844030f0301c201c3c420180707410000303016526100562030304020400640340140822007030307540c01c00011000441c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 70142781 1250 70141531 70141549
    0x2100b090402060a0504080d180905041502030a0e15010509100602060714070501180605010501140324030d110c04020301031109090106050607030305040b0f0103020a090f0204050a24050a051e0702 86
    0x701035500c486945103640d40c482c1c007038109c0d580000d18281c00c0409000005440d20030f05440d40104900042e1290394284500c0f01038002484845405e0040005600f0340040207080ea81c143c1e0300035a82d5003615100c1d1001700710203000c54840c03000140c0010380460303203140c420304495059440c003200131820f080040d200d480c219913994440c10b056004030794030802001440d0088900400e03007400c011003d000914156400c5220041148417514000300d034031010004010a141c20703420000d404c498610f000303a00e0240600342401d0015a1070321540d04600524a064000c8030f0590b0b510841d014030314098001405400040500503036101e5490f8840821251903000203003403001d002c1d5501080340d0400e42000146d000c40034013002c0302110480018805a102c2c138540d9021104402c100240d40480351207050001c0c000d42d08070a5000030384a0000a21620141c462900c14000e041540660340010000f034600388200c0c2a024007080042c016048010303103041d44d0b960b0399500100d00364541120341e40000c411007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 70143887 1106 70142781 70142803
    0x507020f03070b070c03060f0c120b031203070f11010e06010315090c06030f0b0108010f05010c020307030c0f060212070218180105040503030702100b090402060a050408 74
    0x600d0800c40701c8003c10907040c146481d441503107050343c1410381600c400d030f500078103000781d00681c807104d441250207441094580070040c07005c5c5201e20f0041c00e03401c0004d5a040c003a0030105034a0644441c025881689203580c2c0c0d80c004803800e603025148414420382d010590b85440c10306802400000303010390550380c2000031a4a10b803460842c41025004622000704000d0088200184207a0580c100341461285648284490b02c010001161b601d0307000d1159815002240c0000c000950042000c0c2e0312050000c2c2c280c503c410749907143c41c021056a5400b80d581e01c184100200403140d41800300000d940c440c0c001e01480d01d02d40d50001071205941110486195100300d01040e0242c5420341c4480b0b0060b00040244654501402e000362242c208130347d0400076008020711410f03034480c00e1041140301240109000c602d07032076a40134841c1d5500078461800900c50208004900c00c0c9041250010711 = true := by decide +kernel

theorem cover : BRFrame.Cov 69964031 70143887 := by
  have h0 := BRFrame.cov_init 69964031
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69964031 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 69964031 ≤ n) (h2 : n < 70143887) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
