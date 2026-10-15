-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3852
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:28.709485+00:00
-- url     : https://prove2.me/submissions/b8af4d3c-48b4-4c74-9a43-3a4095c46490

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 692625899 ≤ n < 692805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 692627149 1250 692625899 692625907
    0x15030609020123030a0b010c12181502010f0b030106050105071401060e0103031808010506030307080706020c030c0f06130c050f0a090515120d020d1116060807080f010515 75
    0x584000f80044a00040007800200c00c00007038100ca8003660240042d4101003100b00a0200190b612420050015000c00b0b03080c40001c1800e8401d01904003c0011110b25601c5165104440d080c4081c1e41c10f0b20b000507135103900f00c280307a0401c10b101e140150b0200301e000b4050039144c02d002820341d200f10a806007901000041611078440250418001445010003101c00c540c0c2da0300300104906804601e548840740b000340005400d000501880e40a03540c001d02035840d0210f55502c0d401e0661000030300300d683c25002d000d940c000b0a0188090200d01c11280041d0200c0c1030000b0000d070501800402c0281c4100034042c00360081540f8541ca2410f44005440c009181050303980003c6a07903000d030b03010341001c2d42800100200481c010056800c5c0410544024803550a0000a00c0c0c60342d203000e1003040141d2000302500450341c400c2e00415031441ea01004c0d02c0c03500903103106d030100c4850640c01110101d0309040a01c420550700106003036200014015211040d4100400100040c0c80c0894440c00000b000c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 692628399 1250 692627149 692627153
    0x90c05060f16030909050603070503190606030210090312080907180b0307090f060602030c0c010c210201050f1302030a0303050702151314030703050d0c05040306090606050a060315030609 82
    0x360407a500b518032103224641d400ea0601d0020f01c680414000d5010880c10440411082c0c1070001c1c050084d218024040c000d04218030071454460b00d02d003802038540d551102800401b58541d6480301011185650b1414940303821810b03c007070010880c403101c400b041360001c10000d0700c440202e0a007013501c011102c00c410203800c0500d84800340c25100d4001c1e83c14003840100080520860b0b00c4180181d8000000b84000781d0340341c1e016610383c001c1120034542504640031002c1c17903600c030b01040a034203803040c50031000c460048440c810003000285d402c8c40150707548205002e604884214141d03440341c568089030061500f2640841d85844440034010281502d403004039500500a0004540707031107550481d0045868010301c41c1064044da07002c19518070203242e1070341150fa04084100d078000b54254640c0f40c50a454012020001c22124820000300036041c040400010594050000441c3c015140030034014144070400c40c1c10b140503440403061501d0020200709050080001d8030849802c41d000040d80c85080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 692629649 1250 692628399 692628427
    0x10306170705100f024803010b04020a0e090c121501090509060f130b19090509010605060f030c040e090105070905030619020c0304031202030a09090204030b1611010f1a04090c0506 79
    0x2406d400c410303000542c81c1e842c0c0a22126901c1c48000318001d00513014000144000c074420041107400040d100d401e07a003101d080caa0006a000361600140ea07161110a14100200c0e4a054138000c20784e1100c10f01c648450b42c1d108000030081e00003190b110440b803d000001400030640d14004a00901d010740c51858440b0069100d0701c0e410a001c0d02c0b13458048071008650042a0b4203000c0c52515918042c003040b4441c40c1482800107881c4090603003407405074207804601161f080140303182c03001882008003040c590107015078280119007546c0042928203019601801088231078100074000c0d841401000581403c280c1104500c00049400590314136440c00c0c03941c00e42c4a190005014201076503051044141c0c000700621840a695540410071b80c0c80c1c01c41c2c4810382c456032001030280010302c00415640003094001e614003101e035041c10100b11900c40580c9003990300280c01858103540d9005000301054401070320354040001120104030405942d640c801504295000c2c80c1d004401c0420101180054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 692630899 1250 692629649 692629723
    0x219080709080f03040501090b131208091c062016020d0f0b090d020c0a03060203060301140103080301080d1713050f0a06020913021306030209010306170705100f02 72
    0xb00409980d040e05060301041d90f20b501a110b0507000925120000402c04000020b0306c2c600d000004071898030038500011400716100c150b00aa4103c0d00400c800641940e43d90541941100b80c1c2082e04102125401c1c600c0403154980745403840f1101201c2075612102c00e00c01151542034801c0d0b20366500240900100707403403c070030b800e0041004a80c0700d801014400c0720300e91980b00c0c03000201116005403a9640490310707461700d841e03100d1700940601c005100042194010b1031b40310002030000035007801b00300341d0143c03a03410a900c1910a500000014004030806002c0101078100c41d0600604a200c0e40c03031007040c640e1004050821a2040b02d0a45007004002d00408854103410000c0356003508490900307900039400205071501c64805854045402c11440c000d49080c1094810360829403454448250060740c480100b840c10159140740104645061602c90050180b0721402003510900b050140200c1c00f9908010b24103000c80c0c803c040081d039a001500b4444006819020885001c80070f105803044a8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 692632149 1250 692630899 692630909
    0x30e012d141e0601021b0103050c0d021303051002040b0f0723070602210d0c030e0d0e150f07120e06040801150f0f090e0a0602040e04150219080709 65
    0x4440c0040c4402d0403600d001801d8100c03103018404150351180c4006a0742c03001110701d41e40c00c5c0c40c88800d80d54540e60295018544c44052041d0305450b2401c80d140c0e01c800c81e4020008200c078070048140a1040c094100324000002080f408114581400d110b56503005000d064203040c1407400005203081000300f00c0741c9101c51501c540c031100a200c20001e00d00e070b03250442805148014404c2078011203c4440300080740da41c0d00728100a051400060002d20300c0a41600c21200060545411007000202420011114000c1d01a40c0b07c0507030101c0001003007000f15884000786540f01e41801f20501c010180d40440310001d07407000718001c0030019018203590401a102000c3c1d48960b000c100002d44101c10b402441d88031450f140341e2021192950300c03202c01240ca500824007030b140c2c42c40090192407220352050310805180f608a5a00030281d40e5818180d038016000f1001701c00a090034001000754804810200490b0144194140352855000100c06a02c2c81f25080c100b1000b480401c0e415400340e00210044c2c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 692633399 1250 692632149 692632181
    0xf0c020f030f0a24050601080f1510120e0708031603030603021305060418030f0309030e090705041509121e05010924062412020316030e012d 62
    0x58050400800441d8180f04030180304030342e0001c1c044034810512400781b103614140c403110026210106400d00e202c07070060041d80740c10303c802110a0659511361040c0c115440b0743d9500344030301781d0700f00551069500240c0700b0880c42c1c0c0003000502ca00e62010007070f11f14034580107049030b9008400d42821805403009510194010448000c50b0f00410340c5c5800580c03280c5010b4400b44548000e05403030035152101d040340600000d10103944c003d9414440c7c1c220f111801d00070315182240c101d042d400a00018009d40e010000302c0c900141c20415003500b006540940c5425007810f00307a0510304030505120541c0d4903802001c014050b100a00b00e07019100c0c1c000c00aa40000082212007034929001d01c03211405e41101e0003450301000000d084100c03034010740003a20103540c581908910714184040c6020040b103000c000344803a104202c08400d00320310145100d045c420421007108252044080c0440b050a003d95209906000204002000c0139602c0680d483e203608a8406944594200b14010603404c00815200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 692634649 1250 692633399 692633413
    0x4050c10021f09020108060d020108061e041d0706020a0510050c041809050c0d0507090515120c150a170c13140f10080403031e050112120f0c020f030f 66
    0x1101c0c0341e40083d07080d034400c2e00e6a4599859035820000714240000b03000b800500c000d0001092400d010382550583c1d14109604d004002c0103c00040550307515001b1034070401d449000040300700310100003000041105001400f0b610b0643d132219602c500c0106c0921126503280e401151a280c0d0500448004080301940c0c1d00c0419980c411200103002d80d00700c00d075a54400c034a1642c20070700e03100c2103e94115074480010b2152519141003035010b000020803c0a48100d170710403800c1a0303103603100c10305481c1e20060054800144c01c00100508160070421102e01d04105000203003079030b5000440b1030b1031011041400ca406a45840d14000c1f02c0c880c8e40803650410554080004d030b54501c4040e1404980000c42c0c1c0c504075051501c040c0aa090004001c1400042105001c0f60200e8000d510007a82289828003200c0c60060030711019044d40e0307081e44815920060040b6920074480128595410b41c04189405412106507070703401445802c80000c0a8803890002101140690382004403035020b240c110f00383c90390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 692635899 1250 692634649 692634703
    0x60c1911091f0501081009051306091a070e0d0311340b09031504030302041508090c040b011d03071a13090b1c0816080a031404050c1002 60
    0x2400c0c1000102c200c1d401c9a140104056004154151203200d484280310032440c500030f04440500000b4100d140709106040b500703400300f05103000d0046064020745005c00d0701c2c50604604229001d00803c1d190802400e031a0588159951102041c0202d40528080c01c0d01a800c0907070609220030600c102e26103c008500900c0d1020a0450148078180c1084507201c10580e14100d44e0000d204034102c1c1685904442c080035824460645007503000b81c060b00d0010b0500341c0392a00b011140040c2c3c40d40201081d640700800001d41010008500369410a40c0e007400403401900001c3c0100341c0d04001c800501500281a850507241004411300038441c45540090010204240c103620381d204941703912881c940300b03170003013141d120601604020400182c075114801c0b00719689a0310764414160102d40301d200c20819070464215045108000600a60956a41d500c000c04060112103d20155400c4901c1301c10802000c580041408001c4040642e02031114041e00d0358200e0510a190f40105c21410303c165058030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 692637149 1250 692635899 692635921
    0x20d03110a2603040c060807050f0c010203160c02090411040f1a0a3201030b0d0b0123180a09050a0302070501020d0e03060601180801060306020d0b060c191109 70
    0x80000d8205500d042c2414910641c001d284812200a015040104010071241c0e01c6101070030f03406a031030311705542400643c80400000342d10044038280140e4003c0b0901c14400a5034240c031200c08111709112011020f541d000c00e8001c0d40050000c0d29140310700e2406c8032a03890319003000d41002920502013140c250782d040d5540ca07500b103051302c2902420f448c04012402c01a00001c0c10009803412418500307110111090700014491562080e0415454665106440d00c07602c2d04e80356003611030810302c003066041c4200c0c0a1010074440300b0a0440300f140b803208419440304c4040041c855141080329103140c0d21000510041d1280b5a0001c1a40c4548500c4205050707000c01c0345026141d09a090701c503c4078080f5011110081901515681600180d010600035070144d11035447c101064040300412a586030384103400c64000ba402603401d580c00060180c1c045555100d05140100222100b0707090542c181409a42d80c104407603c1c254408621a214007841100440c01341c0e5401c0041c00600c952400c800816 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 692638399 1250 692637149 692637173
    0x2704020d06080609150f15030a14100b0f011205040c031e03030f0504110603090a0b0a06030311060405030f031e0a020d0c02150a200415090e0c0403020d03110a 70
    0xc5940642000d400050140030101c038000e180d41144446c21b07403115003509000c43c0c00400f991b6454440d24a8410018860003020000e0026210281441d2045500b9a105440d10403808520989042940c0101c036070b0005c4185403140c100c030000003056651460416001d06290f000600703003185988103ca0a0b006514000360400c2c866601441390070546240001514402d584c01484405a10070840c0c2c01d06148010310360141021046603003800713072500e4650701180250707108103c154075281c2c140181600100000c0c09030a12600401302c2d4a010744681d42c880c051a50b400c1c0700c4100010201d103040d140384c1448000a079108580d00d0150520384007000080d480031610344030150420a60405850000ca14050081040f501c410720503a152030401c001840402c2d040e034111610301588954a00200000c1e0015007207245031007003103200761900501203032015840940182880d20400c0a200b403c034056408803681910002c0d808410b42c40c05070340303010090303111091034441c0d440b0f9442800300c000206 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 692639649 1250 692638399 692638411
    0xc0816020a0603020f07110102152412070e0c042301080c0304120e0d0609120201270f03211508010c020316020415031202010609022704020d060806 65
    0x80c48003a0b48400a0f826400b8100484031420403d0280c48082200c12a80700780c000c0c81441a54112030000d030515a507024160f6819182103c4000301c6500c0401d280c1e04001ca018003111041c40a0b80c02c5140166a0101c07401541410050701000c21401c0d0010010345003c2d20a01c40b580141400001c1c140072000040030000e40003d0700030012402c0700da403003800c4a02454010708c10070901c010315070007501d803092043c0ca26070b000603003100e5a0012030703514416884058416100c250402c41180402825a481080d003861010301850222141c2c045c25a1082d4074241c2c0004c1101c0d901d000c80c141036502102410904c1230110350a41018800e05080d4031911040100c0032076a16600e840c0c0303040500301c0306003103541005070f07004120020f4800c0d40c2504038201c4502c0140b0104a0004450f03480480394000d034030480d040217000b0b40c000c2c029502030045030080d041040046040c0004c110700c03032804240300b04001400c8a06807c6207103036520b490b01143d550a00c00b10042c000b1580d50b0714560b680c5c404c22200c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 692640899 1250 692639649 692639659
    0x11090904021011060c0a0f09050f040b010e0406060e13020307230f04091b02010501080307140f0d0c120212040e100b04080d0315060e0603100e180f0715050a0c081602 73
    0x8404e003414008e40100c0282d40001e0044401c500d10607050000500d21034510b28140415501c1105450b6074034041c041c0039100c1703907a4048604040c2da00f0700002c02c07011141c140015005004021605900c0140c09407031814004480350000700003e03c1d190148121106001134010000c0c010a00c4a2035802c14000021a07001c0b400e0081d1051030100d0884000b130203a03104640042145101040c96000085c607045400f0043c0c5035544800180d00c0c0c07900e6091a04d4401007080d11300e0703040030701c9586010100680000e00240c100e8030302c0003030701000520950103458081043ca4000c2004900d164124601811040c2215540c0d80d46404416a40d2611018000c1c0060704081610311006601c850030412903415807614490100c0040410801e50402010b01e4000f030070241f8000b44111801441901403d002101c02802030f020f0300300c40741803214089206c2c2c0035900c0780c003041280d80e6207a020140c8410341c500e0301c0d03503d4881c860b8049a060310781403005460749001061000c00741502c403c9010125100301c2e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 692642149 1250 692640899 692640917
    0x30311040e09100e07050d0501060f120308010b040e06090a150602210f0706090222140c030702101a0d0c061808030f16081207020111090904021011060c0a 68
    0x30f001e805655000c4a000516004080c1c10405410100141442c1600c1440089203c07a140c2011440780b4199500c8000c820040b01200c00515420904036405030090400942c50079080c44c00a80d494400a410180070307000000020703071300141c00c2d4004c908034170141040c1030711540c0c2c403c03000356512040307000880701101028050003030062140c100c400e4001018092414070882ea01c0e0807008000c1d00c103041e070304240e60002d0040241c0d100b0681c440070301401d00c3c00003506903051041c8150074000600b900e9242c0410010302040540008500c40140b00503003000c507281510460200050220344071598225031070400f5501040121011202514010b6031011600d460300e00340d4181140540c40744003a0b0b03410401c1000f1002d1040740081080510a1801c0c281f9034050741d0310038085503c40b00d0000c20302c0c0321640520120950a004440c0d00020140c0340711704007240140001c0b61910b0181000307100b2022502d41c0c90b202030080e03004c0c54061000724242c0350280340a01110303c2c036600140c002c1d400586800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 692643399 1250 692642149 692642173
    0x170c0f13090c02010e06150102030c1005011505040e04021e0a0b030f100501090e091c0c020306280902040609020c1e0303070503010b1e0c07051c080a0c030311040e09 73
    0x4420620764a02245c01030025032111a052000000d20181c40c4e811800100240c00c426001001924107020181c00e00165541c035100084412080890f8000304101d0100300030040c010280b010a41c00640440f000c0c2c810b50014603265401146000c0c42980004c4001d07030024009a0703100180d807203181c008a14051981e60381d540380d84007200310300940d80416442c000070b12448260400702640580014100c0d910102d10b1111500001c0c10701c090b0100151020106e0f80c01c5060a1042079040000002c41441c0c0000c0014609200741c000f00041e020681d03500040c506560316074004000a000c2c0f0f050456a68070f4018556890380d256003200305100304102440d040e440400030480b07108661a590349400d40e401c0ca00c2d030b40950740c4100d07588a0301d0000442e4207034031a00d1078001031060780e890500411100c1c3ca0310080c0714060b0060050300d01c120049500030b00201d13030b02d0412521030601764604481b240c091468147c0081a070303810a13440352280480c020451070703040381c07280c4d004050b110b045803c402814 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 692644649 1250 692643399 692643401
    0xc0902130512030406080702010f05040819080c250803042609100521010821130b0703180b0a0905030115090b0a1815050a06170c0f13090c0201 63
    0x4440300b04500d91080208001240c421421142c10000c244000701d04480c45180000540b101a28250b40301c440006070710302051400d02490101c801c990030200203916103004116070b24014040d807041ca0020044c18a40710302c00e0110b00498007a8403075011070b202d040504205002c1c400304c0d50411000d00e000310356444c840000b54184c600f070000060030f110004030000320031142030b00102071480c0743c0f034100701c0c0e264208050b5860f42400780400c08001e101211441d4031143ca0001c68240d0280c03440010000a002c45240156000a079007044907016039519092400b121f0300c2e0082e003c01120400c0401011a41404c03050003015540b100390340782e100b41c2c0d80321010142214400001c1c003060040307200f0100044205901321789108a4001c09101150341c3d50582e22503d880381c6089603203140d03500c0c40c003e2005520301c0098000381c4402e03202e1414040c24420050444111040101e0072a2030410010328401410b40440d5040c0d541510306540701c041c0c1d5646e04c0007402c018000c070429a0f00b4581010903903481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 692645899 1250 692644649 692644669
    0x1a07140c031218010e0d080a030507020d091805040c080703030203040e010608070c0210030f09060f15030c06140f070f0b01171b0316060215131109130c09021305 71
    0x40400c205809400710005591607003022517021340181701d07100c0039004150900043e201400c4681c802181e03502e00582d0003410070303201c511074405008400300306100c80308030291100e42d4071545400005151300d560030000c0d5120340c1075114940b00d210300c610203c10140e02001a104480701640444196602c410301541e50800c11610f03100002c00c140140d00c003603d00f00f400c2a80c100c0c00d42c1000601c040c03802d0900019940b0305141a03d250b42c44a80d0259448075030310541a50045030b18032241c9003400c43d130742c00d10110000d01c141740c1000081094035001803040001c42da0b1100701c7c1e01d5202d558120074901441d90492200e000e88605550b0780001802c004c3c6894030158140c0340300090718540547c14000040343c58500b40c62509407203040303030f111208d07002c1c14141d2005d803840b80c009011440c45260b180003940401000380425516000450000074102c0002c107929034400c65518425640d444000036540424000203404c40ca001040010720320709a90051008039a4038102d0002c8984900500c8441c00c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 692647149 1250 692645899 692645917
    0x2010203070e0418052a030c06070b090c03070e010303080a050c1e040f080601230a0306050c1204080c0709020906030406050601050d060b0d0c11071a07140c0312 71
    0x8000e82414400d28003030f070144407142100303003041010704c0154440b5032800c1002c00504550402d000c0c0c4181140d51030303045d00c0d016030008800801d0251840000b01303060780202d140040035245090041800a9418458402c1c07007400030301212042d940c1c0d408120400d40e420f01c01540840c0d2800301150340500d0a0003034501c941507a2603a185440d401c201458030322424000d4042e001e11041c400801c40c1d0802c0d06c1248000c0a10500400455040c84029042405a1a02e00c5150565000c0f0189591909488601140d0b08124006030558440803100306038481d65500d5920702c01d0b6803003004204a40003019000c1204500101d400c0c0984900450040f0300c900d0524a61040b024000140043c090303821442d84042d062510a0910940b10300c4903003566004d4210001c0c22001144140780042c0c1d900c10b0f81d0300340c00c04d49090743d004140c5604d001d448400d940a075041c1d038010341c10140304c1c4440480440b0303080c03a07101c030060281c1e00306514003540341c0d484d540000b482409030850400100ea1000c0555001e26 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 692648399 1250 692647149 692647157
    0x1020a020108100b160203011113050603070c0b09010e06010f0b1b0f030408100c031406010e1f080115080708070804030c14030319051009020315100203190201020307 73
    0x594603400540700e015005211800c66110403e0110b14a07035080c001d03001c0d15210b44400d40c04140a81b0416013034640c808402958980103200c07001d50141101d481c40c0c1121401d40b502a66a129003000310744041188802a1005a40a040c09000a4154850680c0e0070400c002d4441590300c4882607a80d1996621030309401075810b100012158690b07005842c0c0d02800c01c400c4a80c40b0712080001411500a940010180d1304186003040920035640142203038110315180401c1003043c58151450505805400941007013a41c040b400180e0310380d079252907119800105411400c0780900c4000b440340000340500410415005000300500d8024170680b8000d8040d515a10704658401c40102c0700d80c80d0041c02030f420001a081100041480c076402c2f0f02c4e2621420014651701c0c5000220214410064056005071034079140800c00c0355032143d0f070b180055502c00c41d0050381c0c94455640524410340c0050000f54484000c00380c40c0c11f0660008001c0455280c401c941302d24000c501f42e0207901301d01040314920041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 692649649 1250 692648399 692648413
    0x306050103080c060705040501020a060203060a03020d0c0e07210c0e1c170f0a0807090b1c150807050d14010204090501061e1403271b06040305030405010503090f060703050a0b0f0102 80
    0x940c05802075540700fc00a0000303d00b040d584d40000340e03600e024100545103c2c1c0811014850703109404803a0b0307844103641c1000240d03614146062101c40303001d0542c403030b085070ba140360851002d441400d17400e035625402012092145040c0141c0301c0d4102280304116010208041038072150100c640589aa80502c900942d08103404110140c1c0d4540004041a040102c181000300301c01c41c0b4900608110861410348964801c0a4170350602141c42e401c04118800010b50790400c81c8020004000083d66826030320f0b00f03102080f074074007101a280c00d84101202e9500108001c01c0c882a2580018103c1d10f460b0b551b03407001c0210300844a0155456440e9000013610710100300150014a002140c10840011001100c604103e040a81c820902d61002d4100c1e0040720745c15030041818400040169000c48030145054510380d00e05589106500c52181401000b00010703101003070a001e28110021a5000e40d200b84c641010010300030802111210380007490003410342900d06000c0d400008904040e0010000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 692650899 1250 692649649 692649653
    0x30b010804150209061207120b0f0a090f0608010e0f06180d0e061605060403090f0e0a0f061d0a1a01020c010e040b0301111b0606060403080d02040306050103080c060705040501020a 79
    0x103513010540d0260000820440d207025060301c038503a10310440305e0b562005d00584054103800d040c1c07001442541d100d0000003101c195980c0c4c402d20002e0444407441c01c00926029407500b140040d081645c07001800d940380800207002d18a000c0303041d500402cbc2c582c2c16510a641e50310700c4030401c0042d103c2c0800c601d910000110802034001c410703c880e00f4000501c2c0b1030030942c106100e808035446a048c22030312500180184420175400c00e20807000740c04c0e00d0001902c2141840305d4000001ca00800910a817911025050724552060380220007424000030740540c03200c40740307c001815080640703522a50f02e00d0921042d0942401a010401b01c0f80140c2c05040003c244200446010a02c00d228552055440c0100029130390709200700300c3c041740324904a94882a8a1902850082444000305c049070820700801800380c1c2d4940c11503081c1e0b980803074910f40b2900404c0004000b80111380005120f40c8c07030a000807003844804005421416505011104142d8031020708941134080c41c45081e0141c3e1105101c070700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 692652149 1250 692650899 692650901
    0x314060d08040909020f0409140d0503090d0c020d080a051806091305100e090106030213060e07050c0a0b0106090311010f051602130603080c06130507030206070303140703020a030b01080415 83
    0x55002e000411b2180d102d400800040d044401540381102c0303c100c520304103c0302600910807903078020254200701d030540c504484165283c8003008464010880340c071036001c1c00c41d41c0c6d1800181c0040d0300310500d191030392038503a80505180d0240d0030120500603075024082107458000200c0c6e02c5a440501110110100c001c0e0440c040c18010f4265080b00c1094ac0c40481c01219106840384280c0e00107002041642c618014031444c410700e1920511040d0810200388401d00f04203614940241c00352070b241c1c0c0d83ea080c01940c42e0520800c403c000b4811200724000080700e681c17140307050055030b0080c5400c82100d0510401507608401e040806004604140302d040380201c1c2d0030344d03c421b80d240041d0040a400000d5202d003c22aa0240c00031107201c0c10102c1c0900b0300d2541000041e90000c0c4100c5070442000160301d416036540e54520009100703003000a038200030036119421541c11407242014400843c140703008090040e40112203000d0029151428040e10303588940d5480f03006079004400c01d4804440400020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 692653399 1250 692652149 692652161
    0x50a0308061f05040f05040b0d030807021504110f030a050606010305090c09100603060509041a06041404052125060209090a0504050106050627041b0314060d080409 72
    0x1503000c458000d03504400c41c00c1d12002c0c0c1c50034a080da141560b690922170b003980c8941c460381025000354988000880141c482014481d091501b60400c541e0540d00c00000701d1400000c0310351080b0741900d060520080206165100e0080b0004490340507110440b40c041c55504d0540d0b08000e021540300401003205940243d1000d074000d48200192480303600b0f000081070303082a0944400700d105608601c108000c56240c0700b8040a800304951104044c249a00c5050803111441d01c030000052903800401c50958807540100414004110211481d141904100c0d444a0248140070300c0078105013103c505140d13040781100d29030642e48c1480d064143c403800f48002009410042100c66507400c01c074181c660b40c0c4408a2911510160401203206d2500745841c1c1d00b56402e0740d000b54044c1400344058080990b460469400700b1034010200150750303809500250242c2a8010004404022842c031100400d130f02d03800c0a5000350003160751540d80d480b03010501800820041c00500040421301040c00400d416170004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 692654649 1250 692653399 692653411
    0x90306070c1403040e0f1609150507060c03051e011a0c030708041205010b0d0209071d1c0b090c06030402121c0c1e20120616110307050a0308 62
    0x2050b05260403512091440c0c0c070640000070b8161260b03040114400c080d4a080b0b5018160305030a44402c02e4505000d410070080d809494014500c0c080d0200741e0324865419104495080b00f03007400340300d000c2c400140040a00ba600c02c2100310030744000245102e011081e9138100c03180f00ba08450301d69000301404000d41c01c8800c032410140410000d203008500c3c2d04c0d02400161485000c4440c402803646400c5003120f09c0e07119098040c4d014015401c2c0503990740c100702c0707a00c0384007810112441c03d050310740c0001481c0341243c410362000c080002001c4190533880b21042c440d101d60300c1d4200e940c4410610b9592481c010034030700d50101c82000000c00605040080c60848034144040b145400804c4122201840b202070000c8001081080c814040c0440041c1c80c40141e210080010034400d003c0d290440e40310350603101107030b580040007452000303600c503016104601172424040e10101c0c106964000300c6030f20038400e844005440349208980d1000e0100450311740b5035200d402021030034815581512504402054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 692655899 1250 692654649 692654663
    0x51e030c060a030b0102100c1d0d17270f0103150e040308060901090c0903061805071d070219060c1407030804050d030b0102073005030309070b090306070c 68
    0xd45545400000d00841c03400c0d910b01142c0030100da0b000902c1d0900183c0300440003403d144100e04042d030800700d210301200c80481000c15070a00d84012a01226080000034500406502250301524010b009445003845c4954a0039454035401e0701d83d0118620310700300307642c840558a80815558080e5101401881c507900750b40d030311a9940c01d541408108105e4081d00462100d8081200e5403600448240c050244081c0c00c003c0150300e50001402c80360b10b0f000c002c1810b030b603408040100450200401800741d03408401c540b042c9480700c400d060a58000250003040130a0074002c6a0068001700c0c51508500c102c4000400d41c0780035843e0480500302c1c2a031400140218155043c2001d105507001740304003402074035102424100307031070b1107844e007280080540c0406280039401d40182c4c0c0d01141e00c4007107a20301d44403070b0030000f003420389440c0c404510f070803504059402000883c00c01070048081e40c0f068400200743c0d0b1403940d660f44c6440d0107125280d861036041d0007140004481500580c41200028080c2c1c107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 692657149 1250 692655899 692655913
    0x8060904060e1501050411070b060114131e06020c01270b0304051b090c0406050c01020d0204060903050c190504051009050702071a040602120313050d0522051e03 71
    0x8076243c10100825059140500b0b4100140032a0405015001c4030b682055070321032038400a82c5500e2403c0340050030b0b040c100b0002402e04070054904070190b840244004010006141e41c40741065850b043c8482181c03214618004001101400405e12042d41c02c81030b15249420140c4551030300410410b89040d003842d0311001001b040a00038a8095445244070740014034501c001d550083c0040c1d003c984819209840902c00c20144076022026542180c800303041491311b41807070318030b001d0190044c0e905122801e4804240041c0e555801307110901203d004000342c841c040e605405000b071544403045004a00d1441640c104201d00b0315912050f44041100c20519806031902000300c2950025100600164006c91080c840804d02804808001c018004001e19040c540000651a01680101401003210100005014402c0b299003100c2490f440419203180c480e42030301c0070f455030300400b400c4185004000000440f03000000c01080c1540c0c40241040000402034002a07902440c00c3c0146825010f051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 692658399 1250 692657149 692657171
    0xc0a0c08070510020912010c021b0a0503011b080c0c0316150903030e15060f060a0c05030c0717061302040b130f060311030d050403030c020f061c0c020703030806090406 74
    0x2215082549584030f0000d6a9640350104000c1c0700c81810301305101d542d25140801d0503054000407246102e00d514403e4150520b8110000f8214200940c0a01c0d055402c0c8000070b50000754440307603075144400315101c1501e15151b07100c0d000410300079100024420380c41040005182c42c682c140c62003040d4894030503103988040c40c98003503043e190007540860200e0f40b1401040c1d810001030100b0b0710003007601c906c190054900383c800141c400540e03810007402000b0002d5107994540c4681d8407540238627005011a50383d00b4011087d1907a0f688540328451409000b80040408150080b905030b0282207452100384002c805a000c2200500c00d184000d079000c2101440e030060101140079001c0443c412140004040345181807000400040c0e401251103500215039902c00a5080000d0390140d9070940341c03004643e00103101281c0c403a00800c0607658083c6003c110011f6100006e4001d013001170314520240410314800e1700c140c1e910710543c0002004280c441d8000f510b03500713100703070b100d64824003941021540000300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 692659649 1250 692658399 692658403
    0x114010609030221150709050d0b010e270616030903050d05180d02010b030114072106120b0411030c010c030e0a0f150815060304030f210603051002030c0a0c080705 72
    0x40314817160b00c607102d242003020b556000185000208000e4030441020140359440305c14030304050040006c2000c144010803860714131105002000c1c5400c1d0301c01004a0180f1410940d2403000700e50032400821941c1c22200018881e00410b107660b0762589074103040507020300c0043d015200040c0300c110241ca0031440012099801c00042c20040703402d40001030110710078002d15096500702180b41c0d64940b901014016465803004611054150480400804a10f00c42c002005042103611074540807036001d140380c0910041030381041c040c520504943c807407a6150801d0649502c2020946804a01c040ca28a00400d000b6032403124030440041c035180c045515030600381e000c101c1642100c0c0040c02500340000c0b11540102d04241c0001e14043e0b220442da60b034400080040c40024402420444076000a01c8002e002d03141510110106006c1c5103000c5c034500c440240100001d00c010f07502c81c4a034086400d07a4121501c01c4900070108000d05074a864041101624840c004030001c417445007040040401040d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 692660899 1250 692659649 692659663
    0x300105010c06090c0605040608090606030d1809150815150d11031e060a02160314130801050a23070c020105130b1801020d120b04060503011d0114010609030221 70
    0x544803d81c1f5141010390080000d4002080b0710140c0d442101408250b580000b221140294280ba05a054448044541150010580c0650300c050309101302c00c2c903140d003051a00c40913689244100c8500c1e000e005400303e0000c105883c0040b80c0d0740e11013082545030910301e400104d460301031000c0b040c1d2140000082483c24614007a000c01c000410b0f0484081c9810620010f40c01118052040d418411801460030217850026030090501400406110200c4843c0301038401440e0441e003000d030410b58410180340648000c95542002920740b2205040f1040039210100c001c5900b0f07400d24607281d035501c02c192105060140c040e41840814406400899110b8400e44041d041038880307181c4400642c00303205a0107440810080c10b5400000c1041c101a6004441030781c101407540c0041080302c03071500802c0080049811458041d428072151843c40391710700500f0307180005480000c204240303100399080984c443c02c2c00341d13200142c12030004201502d426850f002d0341e103441a1009404000380c070002481c00395 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 692662149 1250 692660899 692660909
    0xf0909011e1a0109060f18051f090b0a0512070306080609010e0c0a1d060f06042301300f0912080108010c0f0309111203300105010c06090c 61
    0x5150404007840b88140101e4030016282070900d4440281400c2e406029282502490010400043c81c986148507d03400c4160003400d0250442c0719080b4060b000c140c0640c112941180030400000002a00040c039804a80440426540e9141064180b40d0403041082e0040d0180f000c241e203400000c180800240000c038041c24411f000003071809251580c087c203200c00c18094910540c411a0300304a094030070703400c071002c0851041e03015609a40c5d4a000030302028000c6110381d0010300109010442d40c3d81408020141c07112074550743c090000102c011145c049800c40341080c02e80b840310b0204505400d111074842e5143c1d040301c0100300d54056000701022a40c45410035500019061001c0d884507402440560242040310000c0c0140205104050f01c800e1380301043c80101a996981c0105010000d0640311051100034040c2104900c1c005030140c1d00d4000880704207419a11011000f500800c0003003072400c00074800f1a902c8a6880c01d801074a00081040d0309a50720703911800c03508002641e543c0300402510f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 692663399 1250 692662149 692662151
    0xf0708040f1805060a030b150103110c031c051302060f0d0908030402100c0c14030a0203010507022b0e0402071a010f18020945010617060f0909011e 65
    0x100302c040c00c441c15900c01502d0036020b940c2c070780018004a11030040440d8000034840006406980140c0100c004103088420000d50043c0420f00c0d076070305280070004048241c680545540c0082541070414100d0300300350b521001100600c030203400142071000c050700314440301c6203105003040f050880b884240c6901c10400c03150000c0000c1000304514180007405540c0d141c40c07a18428041882d9030b510f40c43c1d001405484104155860000300558040000300b04e26503000c1e000313020b58140010040d580d240005000e002d00c00c0352110601420325020620200b5a0300e80c3c0c0e032840f000e00203505020080d0f00c981c005582001864010b400000d01070750400d0700801a8500c0b51200520b007032807400c0c4040f1110701140009004214420440d51420580e1130841211801c01c10b404071910780d1038540d445c149031407081c04c0108100584c0545d01100c2254101c030f406846400c14540101d40c003004141c0704a42c2c040c0e1001d0315a07408280b03401c000364130641c400b00d030000000c0c05002410700200c80c00d10390300f2034403101d03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 692664649 1250 692663399 692663429
    0x60d0e1203150406060c030c080c0c040e010e0601060f091401030b030307030804110d051005070c020d06150b1c150f03060603020f091e0709031223030c0f0708040f 72
    0xf800d141c07088600401c41d81c50258109445582c004045a00842c0e002e0a480703408111800903180500000155501c02002044001e90841d88039010b0075034604080e1141c041c601c0000303402401481604400c00081da9510042410031840b8551240c01d9542141050b94a0340c40e10219242000188091030107a1a03030440d03031403e49020b119000c0c01100035801003004907490070001c0c500003120035a64811302c401050aa80d03542c011203002e59031400103035125511040c6041407221a901035002d4089040501d00840d0712044002021f214504d0454003421804040030b00048455020020b10700d0840e0f00c40441607510300780400700400b039403c140c5820360b070785204004529140482841490007500c0405082c175003800c8011928114012590290b80d51600050b1780358400d040b40c6000d1a880f00309030f403040010310401011645041a0402c9005601c1c6c0101c07002141c840c03e1fa40b003000d96035107040c9010a61101804030382c00c5058115401c45091102140b008032507031001003d00ba40c04a18041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 692665899 1250 692664649 692664691
    0x3070b1c1d0303040c0920210c0c101401060e0307050a0f0509090111030106120b040c0305160c0b0c070606150c03020d09140105181005090f030c060d0e1203 69
    0xa0440a500c039072851403520741e0031241000d447d800c4112174011218100e4230b488800760001400280e440401e008640301c0010498101204400b500480240c40122908400d40b40c3d810303001c480860000c05844481384e0010040507124914840c408440074040e036043c070350b07100c0100c0c402c0c5605800040d1020003c00c030038001d07414a1580c03184c2c4043c544000b8401141c041c9074140071484107000e10400c018082e29101040700150304001e400d184007510400030000d01c400004d004183c25200c00088641c01d0800800380d030f2103005207886c1e0326040090b042c402c0e255805400700325403102d48121001500e94000266103020004e80c50b004d01010345408150000e80e2400904000c842401c181c1817083c084400d10468002205d003121905080c281310303a03500e019144a01c0c0c080070221100d40d000180213940582030740d00038042e200310001038800d00d09a541280c20562108084000190007038428048a09044034941142c203484000b8402e548900b8800450f0011640c4202d0390300e219003070500300c4040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 692667149 1250 692665899 692665913
    0x4090e0f011119020a020a0306020c031606020403020a050111060703021b01090b0603060105101d010519020a0204050c0f030c0901090e0c190504121113090606080c03070b1c1d030304 80
    0x100b6200c1d00d04c041d248022560f030000e00c20309000e01010704400d82c00704541e00410810400c03103a0340078100740f01040501061600c90f000c0d40c8580012802400b03480e000156650140c00140505d8800768017030311180d543d28a0803402034001c81001c01d842030b030841c3d8403401c2060038400d05158600503841d1020520b09602450302d400302c10fa2001c0d0150001d02c02242640394490394041d17010200300071205244c010b180040ba581e02900750000e04007995104c40c10121500000c030400201c2c4281c9042c042907803042c4004500740520704041c0049201080042c50f0b88041000030800864141032242080b038644030007102e4002c00311a000440e180003e50024500320041e5424411407a500e0900d1400c1e08010b4010060304070034100801c80109036260140a94640001c2650040f030904100301c091501e0500380b024040078414442c49020390308000905043c046603e0040d5054102c4c1c80e40f8011080004800409845201402d6141e54542034a804038014a01e1039101d02c6101c01103440c1e09182c10142 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 692668399 1250 692667149 692667187
    0x100509150309010635030d020c010c0e12280b011203020609030301050f1c060c02010b1512060120030a0c03020d08011a07050102040f03260f04090e0f0111 68
    0x4140b20b031042200c00c0c1d08400345440a404582115a00c0170a00955171100c0d10f0b500642400c8001036002003546030940d08150300500c0050380d2a980c1a81000211081c03161600600d0400380654000c0046070802d030042010390294a451040c41d000900801c7d11501d0a4481c01c2e001800607052081240e41459810005076400c48807200140d441c652624001402c0840030702d02090242c8000d00100880341803061031102040d400813030070300401030f0382c04009008010b0410060b1003500d04490f41002d042d111000d071070700d61901480c3c00020303413609401550000100740b03452400b1030f0705100750b080f0500c050005e009107101030b8071041d40017942d500e0068108082c000c405020490b40c200100110100400c80f401c1041600d001c0d0f035510b22990900314060b10941d0031007144503141d0351000081100000034030700540034410820700c0304001c02c1400d000c548a1a02440300c1010140000d1005400680c081d41c00b00045108950510240303864003802d5800c10b526083c1d0f06c10000c034407a0410914a2865 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 692669649 1250 692668399 692668409
    0x302010f09050a09180b0103030f180e15060f0a0804061a0306010513150323121c090b3105030f090a03020a0e0114060403050c1005091503090106 64
    0xc0700000c0e040c0070115140040c140315014205403190068030001000300c100c40c10b069088440034403190b07105e00700030b4200062207904800260a0100380420640c0d10052403054982e02c4e210314400780c132813825410070203075501e41c141e0380000c0800c265054122020000c00c140505500c46005504d450b08140048850184140401c211400780c4411550b9003c14400c0c1034404c11110904211503404c40341d001095480c986414a1070420008000d00003c0302400402540d00080c45091400d500002500e8580e00c59680d202002c05001003072000c08005080c10080070548400144401e0701d4075070119040b41542d00d200d001e1101c13000301c2ca0001e056801d40580c81c92001c000038030005540d5070a0307035921400d52075403152400810030041390340c0e03020312002c02540c00500022910b5240d41d241da0200c90300b84a40d400444020341000c0c200c0c180310050350100c3c0d4110740503000210602c005d1000e03090034030080343d08024082020102076612059107035480c2800201c0b864680c5819444142120302c56002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 692670899 1250 692669649 692669657
    0x1171b2d0a06050708072a0f08100213030807170a050a0306060e0a0504090809090702060709080606060301060818100614030106300b150102060609240a030206040b040302010f 77
    0x100c07000c02d101e0b40895122a610121020b400c10311011242003880644080c7c0c015038564500003d02d21400f168003005503800722080d45d005280c0788412204030b00c500503040300b01c000c1d0301d002080429aa0790141c94054003646203820b1404880b045000b0030341c40541c8101c0031070004102c0300c1d8810340c1403003a030000d8520b6040024030904100700262112a441c425144034640300c4046104201d1200251222900003920040c0242040038019480784022101c0d8000a045841c002a1055001400b503026400c0601407030300e0369080c01d0040b646a00018025181010b50380070000d04600d042004001042c4000e0000501c141050341c0c0b00504041d95480b9842a070511000303000c84441c950307408400714100d1461140701c06090580103d00e40030414050103e51461080040e03010b1800303100348034660241c0c00c0d28116a100c8080100c0290103071010900081d00312520b04411410301c0f0806483d00c0000e04859400c2d0340e075400500345a0258002150900d40440c00b04115601701c4034052030b810840c10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 692672149 1250 692670899 692670907
    0x4020d1b02010e0601090c0504051206010303140708071514010f1e050603070f020f03030f160512060f1513091503051b0a12050d0801171b2d0a0605 65
    0x44884e41d10441802144512541c9442010300d04d07008000f1600240707000b030415800000007a9240c1d844800c01d21058000c01c84581c0d48018540c4000202c0d07590541c0051014202209038680703a081410600c01409080d6966165040d8011502e2049008003841c0720494049414411a000305840b40c50144040a021500078052580c410003501d07881802803404441500c10888205e141c849814034295040c040001401101690200100e03c01c8000c3e000440d0b51560050088410344a048007051004048001141051401203d440301e6990002c0814000c001d42083c00c00d001da100d010180452648248104180c82c450f000d0b42151801c01140c5141d80380c503684031310783c035403040103110b4200c00454003200c002c550382c9281c520081c4c6000d103100ca41d08036280c9070441d075600c140d80e0400f01144090740001032031001d05016118100940f40a03142009007200c041801810310480700764011b030012000304400340780001c203105558034880798441400c540001e11a03206c031143c00210800200700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 692673399 1250 692672149 692672171
    0x1b0f07050102192015030703020919030503030a11040815041407050a0303080718080318091e131406010e0108060f0414010b0604320f1c0204020d1b0201 67
    0x300d915803828810820300c541c450400c000742c5c41c100907141113071a0100110500001c140d15601400e42000c0a407141501145582c01041c09051140b2000f400f51348104002035055220313030032496000c080b0418103410320740c41c3c446907402c1c45801c46110100c101c22000700003d000070342d0038407110204480050308006d4200008206d003041240405418040d69030f010540b124801e0044072b2150003140354500c4031686806000c1d459500103c0c06c140072400302d400b0f0a03020300e8021245c0d03010344076440305000400d00d101c164000d403013001080d0100071050700c440c440124006442240d4845100303030140c02190305180d102050000180c2004006900003c2000f40c1d122012100b560041d1304020403c50076480481c1d8117002d07280441c0690b801c0440441e0000c0d00325801d500c2c09042906903684481607009440800101540005000e40c2c88070b00d41d5403901e92404c0280750350310382610f1246030980c89052078004c2003d91340b010f4032030019255140305561880e000d020b40020005400e20003448816006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 692674649 1250 692673399 692673413
    0x1110d110a022116030908060f0f06010f090801050c0433030509160801050709050f030c040b010c0b04121209021e01120f02030106020f0a0b010603021b0f0705010219 73
    0x143c0125207408000300f200160014640545401c84400c0031014800359481c0b0b0300500300180e070b10501e18503201c0d07140491504811101140c1c842c8860044e83c0c00a985c804004480c16442e07014240103224169a001c509d0702c41c280650791281c0300c0310b00310960390340c50440049410352140385001c01c848011206c21000749417000402ca044a150325011030306071107640901d41003040186110b8012140d0040005092a064000a10928080d161080303070b20b83d40e5043c020348080d40c03180140e06421040060b001362800360f20841010406240401020314180d0b0b52440b80c031003e843c10381e10801302a030200e0301650721a11074650310f00100ba0500281080354040344805000071206c8042c460700c01402c1003180d00c140c0203203249000c118424400d00d40c8000b05140290b100b0300030240140203a201c800e0300c18800240803811168020030035486030b86800d400318004d402038030940244001e070302182e9106003000c202281103102098040c180d031a29040000e4075041c0c072881d0302031000100c105844042882 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 692675899 1250 692674649 692674663
    0x30c0904050a0f0e0604120221030406111305040b010c0b1302060f160c060206040203121c06060518040501140108060f0402070c060905031c03090c0801110d110a02 72
    0xc0d2000701d10790b1181c81514002d012040c200791240d52800400850345200000c0c417501030384c020b4420500720200b88808907141c40c00005d100c4010002d480c1c0b1540b4040c810790013558003e000f6540040d444071040441d00007540140203030100d085d04442300740082e140510403010034020909040da0011555520504555000ae14811440c0b0581040c40e0a5454140885c1c0c11500016002a62081051601d684a050700c65054548100c0450f000c500c1c980006800d81c0141d8009000705005084410110800c1c0d0081e46020f5000082e514240b818410600030100074000316220b640d250f9030880c0005103801824013003e0720135810a001001200c20a80280300b14503400e1034048902e9540760041880482d5118030290010701c0007603a102445502049502941c40e03a40d26020070940d59400c00d641c030714014610031503a0945220814100e4001e50064103407074842e0504521141d0303a058010300311180b038080c1c2060070790001102d00c210a100d220707801041285813102ca0420041942c02551014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 692677149 1250 692675899 692675917
    0xc0206100f140d0507270b0609090f091507050705010506100f0f0306170109151103010501201f150f09050705040e070909110a0c12110f16060203030c 66
    0xc0110090f5051281c103101c3e10015141c0c05040403404180b16855019007881001240c00e001d15214080e942c0b440c00d88100e40740042c000301641e440342c641031468200d41002411500044c405c2d612000d41008416417440e20030385940c0c8682da280c40c1982402e500f55500200a01d00c00c05032001402e004680220702d160300b0f00c00e24503042c0c0c010340302c5407000d900901494004900008c00200201d00740c04c015001110603034450a400c4110040380e19060003030750780002c0c0d03000c0c0014081c0014045544900c460030708441401d2003450a504849440d01d084c10a84108a1440e01c0401501468403041d4029127560505564181c0351462070301004580da012140150240180c450000c2015544030b0b1081e10090400517186040300d080000e4041c264660320b200349074400c0e0608030110141040d85007501c1c070070451600d030f58001d00b00b20740d1b940340850741e0fa01500c0c042c0080203003881010303241000218048006500140f55000c1030390503103102684030354041700071940100200071a0385805010b880034a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 692678399 1250 692677149 692677159
    0x9080105040b07050f0f1305010215070912020d1a0708090307020604090b01050403051f0b0f10210606020f0705062b1103091605100c11060d0c0206100f14 68
    0x5c000c00a0601c5144202e0f80d0807004e481c004160072014608011045045540c03d8003152052210104881d41800040700c00344082054070700200204224800e12581e030314801024001c2c441510303074440c0e500700c10301344060ba49001040200260550029912508202400011400c2c042c0b16400100c8911441c012003078590784400071014245d0007a02620051a400f4056407080000d5101180d00b454403800134100c0c40d8100341a6034604d007020011825654809031034801c11000c0100c06685080340c1501600c2c85800010303051807060041d200e400060220383e40501498443c8186540c03134056035070003161184008104501720501e00020181307105141a043c820018445010321004026840d1560705502e000001c21032a1217000c24104640750341000841d5145423107205019070070032042da030301d070218500030f400101281364030a48400304500101007514101400c800941603940003009100564810804c0c0a40f891040c0c85190103041c052805140c41403031320900880d00761603021481c1c011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 692679649 1250 692678399 692678407
    0x2060706090803130c06030209011b020112050c0403020f0603060109050d11060a0509190e13020406080a0f02122b023405032a0307170c0109080105040b0705 69
    0x42910341085401c01d4210300364645928094030310b801403414600084130b03583c11280021038050300910a42d60400f20695940d8840c00801c03101d41c03180e8060020590600c07a800c8d50500d0501c816008485c420b402080c1c1c120388403855427052284605241882c18483e550134010498166800080c8000b01c87c001c440760b824040701da05100307614035004c040c000c0d00540006944101d90703030000c0040012030300035542071800140142900da4100c0f494082e210f040304210b40400c04000050004500384c500050000a0071581c5903407281c03901a82c2c0300c0449601003840a0a800d6142c4020101c8500c59814090410000340035000204079486070201c890340b403200b218000c6440d108000744500a0a1810b003940c0500c0060401d0080460101b5070741000c220304900484d0fa42408034945100c0c4400002810209250503195a64041c601d80c0705c541500c224500010040031044076a800005044013504e0580c9049c1c00041c008517094120702201e0303042c8418400000d00b004882940001113240460712 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 692680899 1250 692679649 692679653
    0x140402091b04031403070b0105011106070e0616050703110904050c010c0602190215060406081e1504062c0c0103050c04050a0305070806010f05030303130203010603020607080919050d020607 83
    0x141d4042c41c0c0020b0200c40b1407030500d01c0c0350320000005000490003040c0300280307a0384e500d0046030740140400300a0440c0d0411070210346624054082d42c900000d0041825040c44050854000c400340400000c3c1c405510490040051115115202d680b4100684902c1d0452809894490399042284c0041d410841c910301d0741e03001c0c8455603064a06605e2240c8002d9002507542c00025641c003140311001c2d0400da640d1010403101e00d33082c45614202e03038210015000e0030201180b4015510311401c41e2611501131041c6400355a8102e00c1280e10a500c102c4001440c041050b0384005a0702280914104200e45101c0c220002c50700000c0e00d007201d0b82c003480c0c085202c0e603030048072051038000c42c7d2040c0d030042c4001501008101d000300303942c801d5031040011100f1607030340c5200300360005005128440e099041000890b000303036103603107100b041d06001074008910719669078041000c9602008040d41e1400c2e01040501d9146001c0ba00c0702ca04915106140d681681400e0000b4030514035924000e10502c000502142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 692682149 1250 692680899 692680951
    0x101403010f0203090c04060801020c0d0815031e1006050a0308031b0c01140a140402061b100618060609050d05010e030c030a1701060f050a030e06070e0414040209 71
    0xa01d0010014040d9140d0904030b264666804000100d6480746041c0f100115010505100755845034100e04002c0040d00b0045800f80e0300c2100c00781c410001d8640014030403110f43c404000c200c035001107440ca0401a20541034103d410041c1505d0728509071802c1820820550340c59400e844e003565045403071543d0302e0320b810180d030003846200100b46514510200e8000700011041d80708c168000d203404850182552196191000c482034140d4001880c0b00d10300c04600982001c0015114009039642c003109925440d000141c076100c40c04682e160101d840c0d601c00d020301e4002c00d00b03016400c11001c20a01403d81800c501a211441601132540112041b0b003040040c0b00c030035001011901c587c9800d80765100014924181c40b5408140d04001064114002100c085ea0f00f5110a04840c4035581e20360541031013850844241d840000741408050b1507483e0510014000e01c00750380a49002e8480382840251002071100fa6140e880d08000c841c40303a082004050b0311140840380c0d108800b001c0ca0220265a006800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 692683399 1250 692682149 692682161
    0x203030d05060103020d0c21060308030c1c0e1b0405100b031f0b130509010605031308090306070c02091b070f061503060207061118042a05120f10140301 67
    0x1c881a003420b402e4400940c000d501e120359051f0380d107400108c04601d5829402a12054800184443d00c00c200044003101e641c0050940315400041a01c5202401c444200030f40b80401c9080380207810001c081c000d4180341e01c440207035140c4c042d40c0500842c074155466000480062003244405100000040c04100314400d281ea0943c400c07168000c500b6456007290307003e03500300d1b41d03420900c9a50b00c44089883c0c0b4012062504841e50f540e0340074038598440721000722881074107004581480f820300034030710241e0303042c40300922030181c42d80c49910918260040041c201c00c05084040410fa050050104465142c001c54940581220103100f06c0101880c00d07400400050b0f003180e266120250001c020049281c0007001c0a501030b41090090010b14080c0c0303138076442802d40c070306209455100d00b0392050500760001d000c00d07901c88203445040d01121465030000c0d00b080d00c01b20005580060030409046240c200310ba0018508003040307081d40750501c02c18084110310b000398005082548280c4142c2c0e0b400350808 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 692684649 1250 692683399 692683417
    0x21507120e03180616120c140a050c060406020d051b0105090a110303041d1b160b011203051c0f0614010f020c13020c100c26040203030d0506010302 65
    0x4110210990041903100e410120415055025038401e02035140707000401e40350005e5280460941e00303525940e0301d0b004804e41e980800305016504400002250040003a084030846210103421000f665203082c41c20004039402c07140c13141d0820300003480011b81c00219090308610904149640e040651101c0340c204030070300c0b8120311643c2000c0030040c03a0000070405e61040c51241d0004242601ca540070161280100d01411084040e890300000c680102c008100703412641d001e800c244180300744082c03185150f10a04080201940c2c0d40260740402c00460080d500402c103c46d00d90b0349144169400034510701c01d425011000200d550340304a0440d806034000c0d182c02c8146102003110654403541101c15024548009022428883d42c140f54140040740e0b1b200d030100024820000a49642d810100a410001710070400e44038884e81c6504c4c807440c0384141e094441e400e4484a40200324441d200300040713080790311280500c3c5a01d09100050320000b064804403400c06202050316640d01c80120002c0c041d503104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 692685899 1250 692684649 692684651
    0x1502030910020109050f01020301031a060111060f060120060a0504050f070f06030609050601020d03201c05061e2e0c14030f07060203070302040512010e07060c0302150712 75
    0x241006a501540301c2c02c4c685204809580c107030355000030079034200d0000340701c007501ca0310401b01c601c41a0400b5040e5030740e024005040200000b000201e0081c40e18000304ca440005103008414000d040d83c01003801040c05c95802d803014010a4400c500710784545014240700c000310344810128040001c14000d05c640f84201c0f100311500c4964500750000b40390031611401010034a050700106089000b03008180c0304980c10307002007036070700c42e440812801000c8074481214079050500c215441189518001d010581c072071042c00c0310355519800c10703c00f01c880190000307101d8008034082c1d07103038180c11002584004070704a0f040c00801c003030000c104900c40181948109400d42c12081e41d11220741000061a10600440c0401050742217500307001e540b441081c40140c840c21003409103070001982034008541c0981c183c9405820103a07244041281804442d41050503a519003904401c2c0349810030000c1c006061600d0440c596030015240691120328916500c800c0c2c40c50b1100083e240340c0607a80b0b442c604240040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 692687149 1250 692685899 692685919
    0xa1502070204090807111c23072d1415030910140703050f2e09060f03060b030d05030c1612020a03080108030406080c0a030b0613050405060409050715020309 69
    0x1d4141c1c0700c0d100c032000c014414104580c1c205003410f04500b07d480840e50003440880d0980360850341300070720030950792003160600c01d001020480d01c464110364103200102002060191603805400200c0f4081c90b0007096041c1200280081180d440e200030842c11107920032410b03940d444010b889403c1c4649080750b0000316003404140340300a0000880c0c18407d168540d030800440c0c03130303041000030f01c00000d40b2110700380341c1c0f501d0450144014040c81300211581d2440c0801c0140e40e00c0340200d0940300640d1101d0140f10300c191040060080c9409074203143c3c0400c602070076913104260030240c1240000741801c02c0c80800420b40841e00c1c199508449022608514030b1308118100b42402540c80c0e5040f8012070010741c0c00b000010360313074000000b580c055811940741c43c40503070344d502c3d002c04903a08894031010030946c89030050307560341d20b03140c0092490500f10001c035580c00f4181b01c244003e03200b014000c80e0086250050030404913001003041c105480341c444030280c0c0c088079540200d2a41c000e01c16120741c0000650 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 692688399 1250 692687149 692687153
    0x5070506070b04060e070f050f0102011b090302240415020a150204080c060414040c200106062c04050a0902060d0c0e19050f06040b0c0d110a1502070204090807 70
    0x584064420b074404e070820711405000da240541c07038100760310804602c2d5000082c240201d181a03143d0b8800e500041c400012a0029250701148403881c200da0007010520000081c130550401016400039010a807000441800316040402d41600c6688074580540c20a00e0700c154080c0e10900c210003001e50420118100c40d290250b20303100950292041300700500c83c2050480311070501400392802c543c032106101c1d110b1090306d01408043c044042000c0c040190b00c44000c0180401001820040540e22000059160800c0b0740038000c010202c2d07000405100034010042c040c000c20300320100c052410307140816241c444080550250100c0d41c40250320907000701d06180014115400007e407a2038581c0c41a005001c0603060203a80f0304030740c6103a0001e04032044203000600b088a8481032041014000341d1074660345038000400c9800002c05031003a9001800c4140311182d0003a203214002c1c0b272850180c818118260ba8801301210804610000e0a8000c20b84406641d170716482450b4030b54000d4211a9103600c28 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 692689649 1250 692688399 692688413
    0x120b07111501050f030708030702040b0d0803070c030909090b18102a050f040b07030e0603070c1115040e06030c1206070f0314130501091b03030e0402030c04050d0507050607 76
    0x901500f80205169125080301c1d14000035500c2c201d9491401945c6449c0c289d8090001900707200304029000b00f0182c02840010700400f005611906d01a91029442c0e9000c3c0741c020540501640221400c0741468568008038020024441c0c000350100c0c03030a500c51340c1300e02960341440e01200f00103800600d86008200c00081c4016030080ea00c0b0340c8001c05500504c8420142e0b441c0c003c5015800c61048140400e011092441d4010071280d4003034100014030b09040000078403a42d1044450100180180f03007203030b04100d00b0f0790408011180c11152030412041019104143d80076038861581103407810b201050080d10180041d060203070020300600342c0051001c1c0220f076149419912000041c01c0e0841c0003020a1081c8030b201d22084400a0903800390f140c55074a41841080c0d400b05580340c0d5070366400d8500184203c00c09042c03000690525002c81441d41c10b003c1e00800d2880c200d6030007240100200507101500d0001c590903228215102c0f00d20b1045420311a02e054019000750741c0044001480c0d0082c4484 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 692690899 1250 692689649 692689651
    0x210a020a061802120d020601032303030c0d0b100509130b0306010308040e01140a03080d0b180615120f070513090f0e0a0c0e1e0103080901110601120b071115 69
    0x91310719445111110004a0341c03004060003071001130f0043c90051000804807240c6030700344c0207510900b00b06402901a05402d507442514041c01c2c00100040349040302080d0300034142d0386401160400c1442125036402342152180d80159031250240d006001c0b1140c48540c4140c00301400034040300d65941e1203143c940302942c000d0245000c0c0b41444000019201600c41850b5a15007002e1702c041046440d5941d806450f402504c00000384507242c000c1c0c1c00264076840d813403101151202250468a00b0700c401404180521041b103016115002c0104001424482d1111a00101107940041031070381c98000c03ca40034000d084071102a100300180000d1800b900707400c54892611096020001020f10000a1341e80d844405001804d0b804003090420440b03100c006503581c804060030102c560420144890b80c0b05203400d03041150b605070007194841195038848296144448068000c04079035040200a04090102c0400140340d80010f900158000d4410148403c1c0c07024040d044074410350b03420907131188401c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 692692149 1250 692690899 692690903
    0x10503130f060b040e241009020706091202030702150c0a1a010801110a1205151002010906060906031e0f06090f1101020102030c1b070510050307030e210a020a0618 72
    0x42000348440b01008045165014003900701d80b0740f8261b0884c00d00000d40d1000c01040100c0704600f0101c000360784111070000740041071041100040c40d010318a04500c020b52000002030441d80b080c8500707001611000940c115440160791410707100c0e0302a2115034508048254024024a03480c01c40a081d004010b60b030fa4180d99946c0e000744800304840394080000d01550010400250700c007000d80140c281c04ea0300207500901d404400c030150700b4002c400f08d44085249240348005079501c0322810244030951240401801140c4814010300e8555262103000352490b048035003d45828450340407c102a036131000c01c110354808005e0104100b54140709694003206c0c035050342d500d2002c2102d040c1c198418400c4038070660109008a040283c0e5000031812052094030303c1c615882000c0d000308266582500400081e042e55075142d55a00c0c5c07c180003410f44e6000131a0401c164003611400399580d03a2101110785198026041c261205d43c6003070f0072468003501d20006000ca52516200762652801c0d48a44c00c1c00758 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 692693399 1250 692692149 692692151
    0x12162310091508060907080702010b1c0303060b070c0302010f020312010e091e07140109050301020309030306131803120209040e01020c0c060c0d080c1215040c02030702010c02010503130f060b04 85
    0x1c4200b603c0c2e10f10100c0e103c1d548214141c2c0060f548500840b0743c240c002a4520000840e25140804140100c0f88803403411480490800c142c410960306000304009080011891810454969540c11070110180402414403200800410103030340b080083e40e01d00c1c0351010307243d1410759503842041503850044d580340700300b130091516400000c0780314040c4101c403122900007407208626002c0700901c410070b01d0b6807660400c840190001030680d001d0000e54040d40100020b03540d07074100042085980114036501c0f1410b90304020918030110610000031801c1368040c140003c0140040300824024820b604011b03500500d0840b502d003848005501038102804a4404c031038484942030104921801640f004116a50160641c49280c901c54080307260080e40350030b01c9604003490403001c1c7c0603550049a503000c0005291560004504e000c1c010100100d125002452030802c554000a04c249540d40c2c000e4140304000000c00c2d03d0240c2034520409072030304160743e5a051002c51404c10040e010009110f403180d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 692694649 1250 692693399 692693429
    0x8190306180b0109090b0a0909230f060c0a0c06090501050108061b1902030c1506101e0c1b06020a061b0504090b1f0c021216231009 58
    0x80741d0310036a508440e05840d803c50040c502469a0068410000e85039003040026100080e1030000e8021001c03428070485200c59045103042c1191041c4010505616071980001140280507501045480d001404015441d5503910441010350304061140c40c0100304502e0403020b42d06104042d03100505882c480380950703025032590061403405000d800310280103d103042002100504090709a0000300b0300a0042c0c03414141c180c0c01c90b42c18624a000f1800c00a8240c4040018900d0081c0031031200754442e04207100c6071240c3c201c100b4480031300b0000b00300a01a20310605000d00c10040e12401581c1c1c0104003030110261102c4e00252200f15400c01110682d0500220f006880690740e00e0010b01c041d181e4641c4d0401e4500381c0c00202070000c29003038a80001640c1300401c03549582c40003125901c0c00d9a15513400c640c0081c4144081c6d0185003080020340c0e0451003591802040700b02c0746c030085840c4444040d1049661001403104622106040c1c0d2707108102411014100f0340000101007201e0a07280040e07a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 692695899 1250 692694649 692694689
    0x30c112107080607050a030515091609050301051005040b010e060307120b0a24030f020304030c02031506090612101b110102070302120f120106031d0705091308190306 73
    0x2588a064030a82c0100e170040c402d20303500c28401d07801603611604000400106207064404203505003010754140500c4e07500029004812500005550700500061b030003041180b0f071804812072800401e001b80c5100d0b40e16490032488980c8940b00e10000d0910081c00b0366540d041540e0003921508407416400d4806080081e040c401c1c1c45e10305901011503003585084510611102400c0801030072120545043c1907491090840c1c0052910140d44110301c251036105034003140340100f5151450031400c1c00050545082000516180d03095030303d0300064141e69280c000d401d0b0b03684031030501182080421410303141c0710208d019580c09107200c1482202c81d480d585100320101407403a0a0f44200c01000e405a80032001e008034020052000300b4080401141960411056002d0f005912800381c1c481030001e41c40b01d4404840c1c8485401c501880101d0030002c090a51604011510a00e0010803511112002486000500080b0b90480348601002c1002050304400e481000c0c0082c0200d00460140003404200e45032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 692697149 1250 692695899 692695903
    0xf060601180305030a03150b071b05120a02060c01091a06010f0801080c2716030f180210110f06010e070801050609040b0a2303010e010501060c030c11210708 69
    0x2680e0f0804003440c13420010980980107022170070b040d0181400c00b110001201050040a001c81911990548201d5028070403008141074040e00004d01c0343e01c450031214100c9a0002d4080580356040d984107440d650607281c001d0040031200000343c29098a05443d8110300c0914a80600c514000d0300c4a40e4000d122800841e040d00c0c00340514220369000e00f10611003880c2c108101c140f010f00640107180c0320700e00028009190b42c03040e02d001c001804400000074456070180695044049802ea0400200c90b94504801c3c8500100380080e0040d003101c05810304c518481c4003014200b100a0088400c95400c10586581d0390000748150112902a2070205801d14800c4c8486412104010241820f240c04071341004000c029151102d64000443c1c00c0014030510f000380011008803184240030a510242e01c245429540041280b04060745040e00501c01250030240c51501140c151030400414040c40c50809880400b220300d895121001900c0d200c82c054031241c1c81c0040b011440203407805a0390303400c485d036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 692698399 1250 692697149 692697197
    0x510020306100c0c09020403060c0801060201110d0506040e1e0c0a030317190f021324050714030d1e06050609120c060a02010e060c070b06041a030f060601 68
    0x580c03040d00600c901c8160703882080c840110600036131100103000e64540110040381d000d039200311070003912102c40c802d03500e40155a2500424180c00288203101c2180380c014907900c500210007041c20794070400700368180c41d00c0e4080a08481200115480c2020560040d864085004070722001d0b0f02c20b175804102c0d1341c2000301e00001140d070300d612070401940c2411741c8003160b00c1c4001c0240c101c0c10103030121551014518050030011406010700141d9407843d46081ca0b2040045400400c1000c1c03000100e16614441d4495440d42082c007032400d2629041c0341c1c5400064040300995001d802d22011a00c3c4603840e0081d0f01003031104c0f2442c1c0d40300c290011241e0f008410350700c16125099100304c05100d85075480c2002d820010000c12042c003a50712009410300041c4003170300035200810042c0c0d543c0d110745a242d10100300c1160401c3c0707241c40007420240d46a5410341420b200500c49801070b622007030b804a40c06220301e181c0000003070007410707940f91000b0301b0f500c15a9100300720b039028002055001b60901d80f020701d030140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 692699649 1250 692698399 692698411
    0x7111908030301090504051f05010824010e0c040f031208060d02030705100302090a0f0f0602030313060915140415090812091e010507200c10050d0e030705100203 71
    0x145046a113410080c00c01000b0042050324a0f005a00d2003a1001841000040c41070b800b83e00c0019055060064051400c08031020040464030080c00300d034040300d141c1544078111034082c2a4140a6920100f008806006992004042000f032a402200304100020004030501442d61404803940d182820803030100105200030f901600090700600c01400c0001048409485a06025150500e4400481e4032484c50391b1000d03a8003070400a061200d09440d1607400c000f0012407000b5411428040201112491001c00c020051580d0f1900803003003155103e1b0052140300035100c20172030b20403400940c2c14520b030101c404aa100c2580380007010540924031800e040755170401c003e070342444040031400c000079a026015408511681803015410058400120480e4100c140040307060306001c0c1c4064200354940d0480400e00605241d40403500000081d8400d10040840d00ca1201000c424800e45052142c0d442850714181052140310a80000100406040e4030602c100c0309100f5140500750120b0001f9118 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 692700899 1250 692699649 692699653
    0x9010c0f030605090a05070509060408030c0d02060403021216211403130803040507090203040812010602120702060a090e0a060303080603010c090512030d05040606140904020307060513050607111908 87
    0x810380341783c0d080d0300240e030246103070038020324007450070b800038015822541c49000d05500000301c3c00c0c0500d1040c008880c002903140001c012900b010f94000e0340b120781d03400a0b01d110704008030fa0b0312a00a08000143c010702d80102d4143d85007840c405501d90720313400300203103a800719143d4540d41d4036165210080f0ba01c10003495000401c400e81c2c42e99150042c1d07001a10542e5548219a8003040c01442813009501413842200a2603503010351644161303401d02c05170720030829500700031894501000502e00301c94005038101c8030302c0e80e61115520180c40140b215000b03802c800001030300b044607500d03141c0d005000ba030380680c0b80d820310382e03a5140405090710011240140020700c05101002641071007510802e0328002d05055a04009005055000312102117809803601504c44c81d040002d11914162600740010039220600b40e4645500403c0e601d955a110316810843e0028000c0b0700440c419400e44058000100807603911006810000d00d82140308030b00318400c9502032040c24545060f114884211514580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 692702149 1250 692700899 692700901
    0x1c020304090b01050c060907051203090907053603100b1e03190c0e060f01170a14130506070804050a0609242f03040210110609010c0f03060509 63
    0x1181000b0300000c1c842541404030501000884c3d44062103268480e141c0080280b090510b0003003000780c442e0f04e00f42c105038150010043c0c92020345400070510741c800e08070708000ba600c0d030b4a01118088041448400c0c10320200103240011541c03010500d01c1f840c1d04007282210b4890008000740c404841000700c0d481d80c05942001d00d4044440b24610758520104010180c0d20010b101c0001d041d0302c004030080840d240c40c0c50b140309000c034100784600f45401210135500390b00300700340450001e0011408164140342d01d02015001074100b0344103400150340340b206c0d1100700d076650400304d5250914224001c3c0c00c440b50b00079070340091140c510402c1050304c201d4100300100b1100e00715454800007000c081c070007038689040034000110504950580290b007001c1d2010001480c0d842c0b5082c2010606010440007030f03840c0450030302c0700e0140f00076040e642c08c01e804440007071243c0c403007506c00d4491154405525406000d040708000902c54198800c3e8048526078035081040c080e020300450480300640200303580902448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 692703399 1250 692702149 692702159
    0xd0302041409060a0b0309070816080307060902040219020f010b03150109150902030712060501080105060d051806070c050111090a0b0a3f050f0402010c110a0303030e1c020304 77
    0x40c2c40e040100542200052501c440c0510040d51040b10301081541c031210341000101d004111003503480c40c0b01e8180c032000d03d0800741c05985034401d010010700400d40341c40e110010740d07485904690490504241150500404c02c00294461041c004001225445c144da694068100861003544503840600000d44030780c2480090303802400301103c15009440c002074041200081031000350700a011b5510307000000f031880e12850043e11019080305042284010040216490314000d49000300d4541402091590790581400c0f00102c10440d2420103118403014443d040c0e0b00311940b02c144d030340110001d1105202461000390980700700d02d0543e801106c021000c021030b2840d1303800340c54001d410780b030061511400250400e6041c880c9150264841c0480c60300c42c6004049a80a1590b0701d0300d01d5800d0200385020001c0140542c0010030182c180400701d64440104241c0034400001c81000030030f00008107807641030050040c54800480791842c03050180c03106600309195454440503c1c250700440c0350178140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 692704649 1250 692703399 692703409
    0x6030705031e15090907060e0f0f0a1403070801050705190c0c0314100b0f010e01050409050f04030f020313170708030409150f12260a09080d03020414 66
    0x61101c145402e1542c00c02c003400c800780380c966000301c40240301e5200401007030040203201400904a44041d0b804080100850b60f008480340d40408030031039040c403a1b40444400b1489a140700c18200340c0c452808140030500d11031419450001c400242c044074001516161400c2c00c070360b025600c0402191050240f064070001c00b0b2900c4006503601d02d4020380c00100c640e2104555603a503041280c010454030351040380e582d810000040031402e144401e004403180703603002c07586c2d03803c081c0f111b241006808150741e0410790003542240d00805085c04100305510b0200000c4441c000140c40480024024214240360a803000042d01c000301d08650300f8103116454001c004083c2c00c000c080641d818010100009503084050000d800140b11581004c203100e5030704800c1c9071444034150046980c1c1401d001062002c40858000c44458550200c0700c2480c007002c04156a800181004282c80101000551800400e900000314400c4a032f0070001c581210088281c15001d0b0300603030140b8010307600e1040804660f4502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 692705899 1250 692704649 692704651
    0x1501050409080c0d0816090308030a110405030607020a05060a02030121050717030403140a0309171f150501031b0c06180b012c060105070501060b1909080106050603070503 75
    0x403031490b203850051040d60326402c0c1401c03d80c0400c0452140020807403003181608240328014100e141541c081429036840030058080a040704005654400400007a244820304440103000300408591f09881c001c50025034030666083c04407550f01405004c6181c19180b070081d42e059800b00c202240110341090f2080608031110842640c4a1240707441c0001e4504200718100004211140a1580c0e2400d5042c10103110402414280c031341e40c8030030194404a039000c0c00c0b61044d503100d15030524030000d02c480040d1510b40c401681400c0245008600207501019901020000800c121510000d5984100540c12143c014411495500000c01030003440d51048640c000c826119400002c3c0e02078280050130460044d4040884800f24120018400c0300c00c10585080000d010b0701091404c1000e2840c1c0c81c00071240644050305001000c580300c0200002900050040c0543c000b0681d1075400c040928000d030708030f005944001c00e0070f048020801003c10301844081d0307800500940d1845c2c0303500d0f0048449904c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 692707149 1250 692705899 692705903
    0xf01020a02060a05091915050a02010615050c01050610120b0d0b0a090506090307080910110d051801020102190804020a080703060501051c020a0506090102030d05090d0306081501050409 81
    0x5000300032401680d44501510500d0ba1580c0c455480300c0c41c0c0418450080249100c0d08540060301c034040100322080c11840e10f140500740350090b1910f8036510306a001d03000c0c0760802c801c98403d0003941d08500390f01034003500860400c3c80003030000351145000d0004441d04507005a000038402e14214240c044240c02803102144068404010050300361240c1300340e9081034400c0142170351101c0a41301840010800f0a402240c49406145458031b41d40e81c5035014403444200030700454541850544c0b036401018846075228844041d2100400c01c0000100180c0c0715508104140144150140e1554414400c6d00c0c0101c0c50b072140c45806400d1200b041d524400c1c0140100d07400b055a0501240640044c80b041c0c004600c910b501042d15414082086103100e0500300c180c00466104a01d17038056a1070405040c2210400c1e5100742d0b58400c10030040342075106540c4070800090805c400d100b6492400a000c1507114a5950100645512241403170b44610806d00325a17002d44040c401070160b407802c1e600100c1500c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 692708399 1250 692707149 692707153
    0x106030905120a0e0301060b0c06010b0a1706010c02030f1515010206040b06041e06060212030405030d0f0b18040203100c051c1d06100e06061b2e0c0201020a09050f0102 74
    0x213034200c00280c20f503001c941001070175103004074071984460801c025183c0034150f602d50860411018001c02000048001d0300414110744400c045011039004440d00040142c01900b529440d10000d00010342da403112200c0704071b0860b000000142d0611a89103208a0400141d0162a85031940e4640400041002d007640d5405a0f41e0710741d22180403520401443e041c1c000c40001300b0ba0750b1030000064103018880c0c500b0b00c9400020420480011404012038890a0100d207000490340c600620a80081004066280e0018413150120402d40b460051640c400c601c02c4040f50360040d451448401a180c0c03a0441901040f001e003c0021040200c001c0c028210f404481b0018240764600d800000c902021071088034150010800c3c040c03034001ca0b8000001909000404c10018104280481c09512810340c500079602c188032a013805452060103501903c80c2081ca44000241160703404240342d05a0204142d982c40c074100c0202e507442c1c010b0007500d00501c86604d4000d803961404051280050198803072074118 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 692709649 1250 692708399 692708417
    0x240504051806030c030321090c0d05070f05090411040e010b040218030606031b150c061512010e0613080909010b03010501080a090b060f010519020106050a090b030c040905030d230106030905120a 85
    0x42d80b182484ac94206001d100205140b0303252148086d00c1409a802071030142441208000101d44075410750a00300d007041c1c8002a40410540515006160008500794400d00000f040f000350355007102115504c0408406980d11610f40100301aa01c10664038907103007080121051020b03502e8806400395440081d002a280b82801110700d0030b00707042c000c90f09000741800c0b0303d031500c0003410001e131103195581410000708008000781003980e60f100d1000700504540058003a00000f00080441561240c401c0940f1a40302541c49003654070180e0024080c49000849540c00196103402e0350080514098100075507004580360039003030041c08000400400e0501c403041046040c500d000a08500c044012980001199070804003040444074469024806550402c044140f00d60b5001c10540107030307081100e000800c00240c1c642a0b055004540a221049144c0036083c1306622103505a030b803003941040680041d0303a807129002c1d811070303000000203855944030000c2d514031040c02800500744c076211810000b0f04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 692710899 1250 692709649 692709673
    0x9130e03041503060f0501020a150b0109170106030215040e07030b011106040c031115030a090c0506040608100e0c030a0902121204030c0f240504051806030c03032109 73
    0x8016000000140042c2d950a010041c11740801c20303001c05080c0034800b07441203200700d4441508461405680c80e005959402c007038081a030190079290300600300d010144401418081d5494000d159620050340140c24844c40b03035200c40b03100303021202a1303405900007103401d48514108038000c00c43c5040c450b0510180104092109808026107840b9a00c141d024180300f5084d071030803603c40d0901090b014002c40c903a06000d40c170051030100743c03980801b006500043c1100b143c10400b201c401c140d40402d40000c000100450f6841d840340b80b0074850710783e1911102d80c1640d2980c81d450440f004403076110b4010b0041c80802c00c021040d8000140941c0010084c90700c00c04040d0140703041c031003044000c3c20b540500040420801004251810081c10b003070b90440002454554180705a805c0c032261641580315041140700082e0107a01510083c0c5030207404035880407130350b60f800c0c250a03030150340c400e200c1d200340c2107403008602d40001250200b540c04c42103000240c2400a00c202c0d04c1501504010083c0100001011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 692712149 1250 692710899 692710919
    0x712030f05153604020d14060117070509070c15050c0c100507170406090519030e0f03120c1203090d0906020105070e062a1605040209130e0304 63
    0xb014000d0003a0011804140c4000c2000002e040c805900d01900c110081221001040580c2070440461001c8100169141e100007410602161030041004008147c0030107a07400001e6103a050b01c07003d00c3c0e1a002c1c112200501d40c0d0301c1c0e50501c40d043e80300304800006200c15218209400300c2500c94028025000483d85500068540031070345088198404640115162403c2141c0050303500e1070102008a4200080c0080a116451800c00e008143c407001180400a10ba40a02c40e07481d0044140e519091a18810030b4902d03440c0d42090b4001015088000d00a03d05400d4039400c60700020000c1254000d070400b11100384d00a034060404900600075006c90b8486004010f40c4140d8404010b01303110f061a0038083d00c4940d060300008211380c50442040042078200c091450140ea085408948030602750010b980161f20b055040e08410205032034209080c034000a20504031304146640038441c0f41c480d030600007240034860110b075000130000603211403805140e01000102c45070300141d901d801d4071440110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 692713399 1250 692712149 692712151
    0x3090d0311070f08060a090215040312080a0c091806050607120311030f06010309020d0614061f05160602070b0408030402091b0a0818070306020c0c0a0b0712030f05 72
    0xe008296032541e800c04010003885414007500769452501d60070790070886141d41e13404004050b031462a43d01d0400f40c0665881d1410391010801c01d182440d5525100d00c0d0800e9481c0202c02c0d08000300d4191404a007072030541c2d0151f060007030320640e80c582e0070a00e4010030010100143c0030302d0213541d0f40c5010104540c0c44010042c11280d0080c2154007104a0548004080f504076100080500030140184043c104410a541d900b001c424070700400d03041c00900001b4180346002a00505803450442c0d1600030556421543d44500e0040310aa0602c249018840c50030340c210f141c01c2c1000840412040101100d0003480d041300d17a0040c0700041c00d00b640c1d982c0d0b40d40c0307010040c3d4041e2001c0c0400b00c00c000441c500260a1944039810104000701e0344141003c20361280201107c2400f17000e005000078035890060140640346080040846034425500c1c24800025030040400e03102500038004046100e0500c001c000d400c480c403c2540600c2d2140e240c4075100704100e06c15a0008260b10b40b6084148041d03940149 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 692714649 1250 692713399 692713403
    0x15060905150604030309060507020f0405090f0c31020c2b03020f0a0e030f1002090103061505040e090c3a020f1224062b060e03090d 58
    0xd5141440015050301858a907070861086600300014000a13910040010486546081c07603a240d50b003030700c0010b00794003e1055003600146050104005c8000000c1d00900304507001c0300b40c1301d8036840682440340340c3d0b110320b01040f8102c1d290400f03000080803602095110700b42d140700041c14141c0a000c00390410417130b895041b102502d11600d8801002034500e0502221201c0d080440c5010418881101c1900551014006201c0070302c014100c01d480c1480802298294a02540c1102c918204101c000350070902c0951b000034501500460480d080c1000e642041140351284d90074145414070380707914100e00030040c40710741c080c02001040315140c03900034920034207183d8400240c02c140404940c8061440c404410083c22a01c0300c2440561100c0502101c03089081e1802ca1124141e2254070389051914a14500140b5100080482c0350000e0520355010780400c507000e4000045103541030b08003001d1140008054120b82814000144943e48840358070001e04064a0a000301d0070001250a10503080c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 692715899 1250 692714649 692714651
    0xb010b210403020715090e060904021201090336140d0b0f0a14061e0414150319031409010e03150a0b01020d021e01180c0f0b030f0a0504150609 63
    0x24085c2000b0850031004900032031902201292600039403200305c40c000380440c1e003c2d2a206000c00c0c01d545420015101c11040f40000b4007040110b450010103106201030700030300040403002e200400200007810030051200214041d0025414003404112000340f8404c010350000c4400c803c44001501682d84500c5030403c008821002e103000c0a429098401c101e41000c08640140100005c5030340ba84224882c034036050500791f401080120104009185401a000303500c07481c4410094403480d4584815103000d8160141c130006480c1c0940318541000110000b03021503020302c110b03000c40142001a0042d41782c149000c4059404500102e400e24282e9402c00d050041400c0c208142141c6c03601903280d09010030b200925403801042402034036009865084906955010a20402414250000301e9100c0e0f149c10300d144184010300d05060b2509071482101d00440551200007112070b046001d80c1d02c9038014410b0948160349a240c00001401c0041048820550144461400008520402d0090302101304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 692717149 1250 692715899 692715913
    0x20f0d0b04030e130902030a0f0303200d240603051b0f0304020102010510060509131119021507080f04230309180c041a0f0d14070c0b010b21040302 65
    0x602813450103040e40b0720140390400d1105001038400150280d805508158151007054061404a001e00b94035049050f5186d221161100400c00c40001020b0307a890980042045c0303800c110f404e6050201060300e0b41c1615030503410400c4224002d0300b006510000d060420040d40c0504918605560003400758243e00807004020003086580910443d60030944103840c1141b141e14040c0d0040003440b500f41540c2c015001c1500361100100c0316000707881100004044640c507001c01220b05a1843c0301c540381c1c0c200520031007030780311603160004158038013410095580c00c00fa5503c0d00181e4400c2e0704082c1040703a1101c0181c1019640741d00000e4545c81070812540556994803148040041226060150800d403071190414070080b80c80c040c0844084490032000381a00d81e55041400c546c0c0c2c0500e1003403103849a000a00c1c89a001c90076071000c400d04074a012400700e292210b60084400c0180725a000f0310800039900107201402040b405000d00d80800c3d42c88541e810b1455260090304602a81c04501581c880c036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 692718399 1250 692717149 692717177
    0x80613060f0506060f1803010e061009060b03150102160920041d090a0b040305071208060a05090907030c0b0901081b030a110417070503060703090c03020f0d0b0403 72
    0x10141c0180d19001d46814081d90414500180c031500ca124034032a005140046e01395a41c01000034110011000200200100d9100c2590207881d01001c40d22101c001001041c0407418581620890082e00e811811890950340d0710540c0d0f0124074040100a81540701d0304244402507052001d50300050a0b88c0c92011400c0311070324141160344000c20503000d10f43c14040c8000e110100c0c4021008065042c2c00300c1c9055113444694425042c10300e02c12000d0310902c0c1d201e003003206150b0000f005181d054424240c0405403030100c0360444054506503001a40601441d0040040d864040c4015030800500b100342d90f1183d90303940e2000e54401032030b07000c4900c00c1d0001c18490038640c2c00220840d800701800e01c0e03914420308484103035645444010300e802d07044c035691492006041c010300c007618060580d441018140031010010305944d1041032003014860311401c0300003002e0324403a019450f4416403020007200050704503820041130035125050940c1041d00d40702090089403403801075500460003603c071811600c3c401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 692719649 1250 692718399 692718401
    0x60910150c0201140915210a050405060604060b16030201060b0a0e03011a130905070315020306040c050a09030b060f0303040e100506030606070f02010c050601330f140408061306 78
    0x12001c41e00214010f1000701000e80b100120850540d8440c0f0000b40d80c0e1000f4002e442005c2c041f83d0b1a5100b841c01c000810900845540c001800b590149040361140e80d2004200b00c29031b4118000c0c142008001d01510b02d14030165032003403d99074800d00021a240351940700d1020260000d42d10800003482650082c0704905080c414104200509145402e20082d004042010024a410f00c8414160344420031418040c3c14040c05010719030142e810505550b02201c410040e400981c1c03407500c2149498801c2c00740030300510444650a00c0c1d500c0d40700140d451601c9501603d2002450150046003402c0c4014003030368180300802c05001c06070910710031818210b01061031160303c2d8101c5030081c0c0c070400901129640b580c0648282d242c0c401c034000c03461140ca20040301d40305000c40c00103117903208450012034032854103548030150122500c4148040b50701d090700c00401c071903842145800315000d200c51750100380c13090861010750310580b130141740f4265990160510380401120210880141804110100106 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 692720899 1250 692719649 692719667
    0x804210917030909221502090306060409031b06140703021b0f1c030207060603050f1203101a0415080a0b01020d0e01030c1205160f0c0b060910150c0201 67
    0x2518021400c10702c182c1c001c00e843c400094007a2107003a0700b03140b90100180b00b118000140031b900401108241d5840c003011006034011710b200c13a100b80203210018209007044d10030082c90319090340c2c44103000622100046a980c1f2155005d0320b1f4540c41c0d0010003495112101400d00591969900580e5014800c44050808007403460b03180c0950019079800d6102400002c4103054401c417030a6402c6449880c0400741c009100300ea2000300b8207800c000001040c4000428100c4400d0410015608003000e4007000d44428803088545501c031424040b03061015100c0d240000030440585500c0503d8282c560820211604505c0c21080000e1240350801c42c030f0304220b014007840d00c442030008010300d040040303000d44004202121181019500c3e00d4581845d441031801045500404a0030040390508051b4001c40c4440f03050500e0228003400480c04010703101d0800c140038240c000400e850952100e8040142040b4050322070750203142c030000c0c0420801e0340101d60040028140c7c0320441c00c00000d04c005840c1101c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 692722149 1250 692720899 692720939
    0x60603100f080c240a050d020c0f07080d02121204020301020403050a05060a0b01090501050a0f03270c0b070c0303080603101d101a130e010c05070b0a021908042109 72
    0x1e100139100d4240310785081541c1621045081c007a48801040210340001d01a4101d960b415100b03100350340001d00d9011540c1d80940e0841c03015551003c00340740c426a41c45000e41503072588080c04002004200d0400a00b0b01e811603c02000903140c6580c0c0c1d00e80526000c0c041e2000d03100c41c0c100201340301c0010f4451060341100303402807c0918a55141400107011030051034003050038450410044400c0380d00c030342d00c078524800340c00c07800211401a804c6042500c02403a10120349801c81014082030200141c0c068400282d4820308a0510a0071030b0390444003800050001d6400d803149442411b000c0455008080d00101003590150031015103081d4a03150800c003081d662044d0b0714113840803070543d5041c0460580441c0903624917000e00c0c81d0218240042403100c40314070b419441c0c441110081c65109000b40309890040151103204e80f106001d230310891040c0c8054440c9050f6803445404049d0082e044d0070390290144201005840b4800c0100051080c0482d070030002540380d182c01c1c00580c07004065000154 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 692723399 1250 692722149 692722189
    0x305031f03020d0605060a0f06051305310213170c010804120f110105010e1006050910030504020f09070302091201152d08030703090b030f060603100f080c 68
    0x181c9540c020520540c0724107400f809407500d41001a40c661035243c40c0f24000c00c02021414100340d55079034024115007080701c1200f000c030b0005000081a14081070040840c01d40011100307050b07841d41c00c3c01081901d8494911812503000e00c00310201074844425440181081c01c1c0c0d40354501c00701090359041004405035036040c010410284030218001a803104812242d9040c11584240c0c041c009030f880004502e1f80c190a50b090800101d240280003c569000f000101c0b2410003a41c5c41e030b50165480c1c002d800c880c940104480311031000480c482d402ca281c00234005408220614954004a00d140342d0840d07180c40481c1d00000c19542608022292080b0400392a0080000f06102e840041e140801c0d0300c41c1c0d001c00d61018071240850031103400c44000701500300304a042c54a40d01d0f12803070749076088244140d001c0341c034122000036890400001c0340c0c4100920410b518965550004100d40c0303800160a07882003049580d004514800300c0810f8801030300022004000115100c0708014140c40e80c080490084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 692724649 1250 692723399 692723461
    0xf0602191502040b07050a021c03270305010f0902030601052403060301021215010e0a140d0602130e041124090d0c1206060602031801050c1009030503 66
    0x148041000c518020380d0220000c0c0350498100c00c0c040c06402180c0008440e07040000314501007000000d04002402d01c2500e1101b00440701035404200450507040c040e0224070a0403026401c4c01c0000c008414450312401242850350b1261251402c40c2e0844000f0036080780d40785159010f501d82000514014001203414100408d100c4804042c0320001c0030340e00c810840c1c044049440c0c3e40d401e4040e141c0c3d0f88607074050754180b80713080c0c07001d4110120242c003040c0c0400e84040d02044181007000d941001e0711400410b251140c0c44079024005500e800501c10707140c1942c00e01c80c55090341403803000040200742900d103407010340c185400c14824242018100a1040d6403048d0407a0301600c400c9442410008230242607622074107606d01180500a0203140204600502c01010503044452034480102038000d28040100c540c5442090760b4038810008441048850400d21444540c420401408007180500a0b1007040e0798a0010b202a550399400440128001000300306e200100100841006100c00c0c0b110122 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 692725899 1250 692724649 692724673
    0x1e160803270f090c070c0b03040c05120f010510060810030b061504080712120306051e031203090304031a1909141e1908040b070507080d05040f0602 65
    0x942404244400545010800c0a9510380200701a00344028140c03001d40d00d00f040303139541142c1c86a04c04a81ca641083e42c081541d12010055910640d841580004610308203401c0006000000c0342000d001d01c03c072402d0114480c0e080c00745034002c01040c40754041150a03c0d81c00b40030224020300403c01c04050030030400c08984103100c003641100d400c0d50030264007040c14400041d01e2103141c026600f24030070440c000908412401031030820b28011140520202c0103400c01314140d07107030780c400c069001c260060b038081541700d806500000e0400040c210740030280c0280484070160412a564041e5800114003041403004648036903000d516440429001e5103800c10346600b850f441215000c0490780c0e200355440c200041e00c0c00107245090107004a8840e5050381040308003465116442241900607400007101c0c9000d50b2900c1c8004650041c42d1609041c28400c0140103600041402c0e2054401d800d0001482c581c14886003011000d15500c00d651a802e0403c1c1118148082e030006003103510214030221 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 692727149 1250 692725899 692725927
    0x10f02030f0d0b13090c052e1407150e060105060c0303071808030304120e030d0207031218060206160e131e020a120c050307050f07051e160803 63
    0x201c070341410400240034268200801e0800007254005066140741107071700c4e002c1c0110804007804640c0120381d801c2ca42a510300703240400440410854480c41c507084114504079003e1480e240c002030b0010013880c00e0405903103601100c0d1401074010100240e031681001c5402b8070034418203014140594006107499140c5059555a01c0010314901c100111207015403030456007120500300500907038088076102d042c0f134101404400400c4200b00c0c00308090044e800a5800c011840403e0180e040d000f51103141d146803105c0e580820a00508000c01500030f00c0c5058900599450b500506280e83c02010249000120400d04441c011700d040148035284071000d000e5543c500c07408105110154002c03c05041c3c2c0c14818900075800e449081a1b2400402da03254101d0784011040305080c50106c060015041c020800d86036480261441000604100008800c0098207802801d880f44039408540c105540c9400b0709841007001d40e00f42e0015041102d60310140c180301820b8901034810b20001c1c520304030080710485 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 692728399 1250 692727149 692727157
    0xd0b061201020f0316210f0e0d020a080f090901031406150a031b0f090917130b18150307030e0609071206110304060902030709060b040909061b050306010f02030f 71
    0x20703004400070740d00300700058450044600007500c042c60341c8694004200c406e0001e44003403070840d250903107010303802120381100050f00034840e072994010700703a0f501c00d58480008035070040c44c11211540301001913107469195490068001c5024060f0707042104200001c2d28145940034210210001c1c04003c00c00481c0e8448006000b240da104100700c1c417903101110148411819548005440c0b001c0f4140040d0f504460313001480958800c8101205c00200040880784901415a13035480c508940c040c140810344840c1c00500c2445a0b000749800c400742c0800000b6500142e030803a4940070380f4084180f06d04c45405010f05c0c44c0c1d0241440c0034107824942000955642e0404c1d01c5015241e03a0b20018100034064603074860900c01c82d00c10352541c1d49242604261001c3c0403540000c030300920904c4030001c0c000989205000603281c0d0311400900e085d28006210000d03040c080d106940d8540d0b10200d2158440340d042443c414050306844840e00e034904000090f02c02011192204190341041013020907980d440b804035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 692729649 1250 692728399 692728411
    0x605031501050c010b0306150f0d1a130c060509010909090302060f190e033004081b0307061506050c0613060615030f15050d0b150d0b061201020f03 65
    0xd0b60711020080f0b0128054007000d5030043d09030040c0070912224804584025503041c1c0183c400407540600d450070700c56102240038026107c640c582c0000454900e030000c1c981d4000029940481c0785030341580780c040244085901c10302c00300d00d001881d03016950704006800c00400f2280c00402040c45561030103511100300a1501f030309142c100000a1203880c00700700f5010080c0003100f042040300e008640444c0d03240c0c0582c03001303c100062952030350b003611090444000307006040c2d030b0401d00345c3d12150742d034440701c0c6c0118047d8491980c030100304c0020000108060801d890289801040d5408220002044d035030b0580c0164080041c00c0103503030002040041d038650050004804901d01c0060740c00c1100003040306801c03a03008464140040000c00f0340c143c00810316420030181c1001211082d010a2440c1000c0d8410f9903004002902c5820201c0c101d00b02d04c940c07241030300d030f201c0c0500100c26002a8070300304c0130740040b030300030b50400144402410320481a1100081400c001c610b060540741480e611804002d00c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 692730899 1250 692729649 692729657
    0x30c1b13022811070f1e0f0303141c0504060e010507020d1d0909030c0d0c11040c03140a230103020105040b0d02090402070803090607090e07050a03020c0a050f06010605031501 77
    0x2c0c00098800d649a840b0000d010003580c0e003032a25010181c26040140c42800301458403260380026241c3c807151920221104400d415500c00d14680d400c4d64010328440400a91250a001d0400d03042e20814080d0494811081d0014940c5000d1410104031409034504043c1a0325280401400b01d80004240e0000031460410740020807050185907c0540b990b41c0b20b6412010030401d0003004140040902006540b620641d0011030350230300b04540c0c11780100302c040c00740c8040800035201428035501c416140d440c3c0d0302e0013042c1100010102c401c0c43c0815640c0360810350f070b00c401000024144401c501508000d440603041c0079491a00000e00f540154040d501c4038900c0028413003c0040d80c0d504071801ca0038080c00940d210f00090810701ca40e9001216134000900a2600003645070f803107a07d0000955460002d550480d84a481c82111103170410100807040c540d080041d2104210204052551148620000d04600301002d02e554280081a80604c0500c030091040c05031007400d000001011440a1034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 692732149 1250 692730899 692730967
    0x120c08040618090e01091e0807080708091f090602030319020a170106080402040b01020c0108150102010e0312100b04030f0305130b0c0c04230612030c1b1302 69
    0x2c2ea00c1d009480e80c0b140ca000d034a803560060b0000410341040c0840d50140348921034004055141076404041d11400070b14505042209600260310b11020f0030300d0500900540c1e09000060020803041c811525400c11201d10f032030f0b02c1d0054154406020400b8040c28800380d8103508120488846900c40100f802840c2600850309100741032149582d4904540300c107940388882d5941d41d602600c1124282d609901a0f4100710075030b8510b500009802000e400c045c0d45405030740d5030798a824515041d810b04828115500d580c0a038058813010405441c640156005106140c05c004950707030440280d0b0ba11111502e40144808c2001c130702c81c810131058658150420503a101c0c1c2c8144403000b111140d070810b18451101141d80e82903a840050000a800826070301080806010101055203608215a24203034150100000d03c0e10708102550080141801c1c0c00c5904200300c070b05946003440008003d10600500494038041e00d40341026103403500b5000c19000b1854000e5071510030f01e405a00070024025281010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 692733399 1250 692732149 692732177
    0x20c06010e1b1b070e15010e030c0a08011e05010e010909081204030507060f0618020f0702040c08040302190819141306030501090608031e0f16120c080406 68
    0x3104005109010000541c2d24540d0f46007850b030301481810a0b450302d04c02c0c66004282e506407070244030300502400390301c0b40d1700c1d4600c80c00441d080e504e83d03020960503000300740d07010300c041c1c8400700c0c0b05000c0c040c0b8400115100c071070021042c420340003000040b40c00f181040c004105e410354014685040d0342854401243c00d015a06014185100d80540c036005010400f007080141640040600b89251180c0428090700000b0301c058000d4401038010f11031803904034014228200483c1c0d008204200401044c141001e007207070002012104400c0112001c5403102e4100803c250341400364484a00c0c0710484203402c41482e03242c1501d00e01500c0051000107101da50991038190048140ca0241c190710452947ea400340d5850040034180103220740030100c0e0614001042c0c4130502d00441c0240c1d07407410025800c00c035024400003180000184006030340e0304e007089000c101c200c0d0f10000b01050440d41c0c1d006003544820345419030000341940b0b131000c100038100144000281c0300700200e9085400a152103d2524055 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 692734649 1250 692733399 692733421
    0x2b0f030c0203120301030201080a060f14120a0b160f140304020f030a030504170703080f0313060204030b01060e101d1c060b010e0a030308040f0c0302060307021f020c06010e 76
    0xe5401a42c1441502400350010003800010343c10b0384d00c00ea86025168a8441301181a241c881c002c40350b003100644018020500b42c548410b201030002011220780c040e0300c810345420070166100668603140e60368200403210740403c205001c0c1207100c1c03402d0094000105001440d41e11540450b1420400c0040071409550310700c0420355014600806840c000030051078003800a81c040c0c07003000e03a040501d160700000b401c00440c5c3c2c042241e0700010041e1403d0b243d80240c051540c0000d1444070808014041100819143d102900c091489503241c005e865044c0100036040c1000c0d1342d0660320480f00c0ea05030a1130554020040350010242c2d4208880d08008040002c1000a10004200007001440c0c0c0c2001070040d942c02843c1030f02d2007071700c42e5031218041d070f02440350040460001501003692213021a002550b10445403804a000fa1000c02103992294001010381e0b1050780c5440059025aa10441c00c448020300400c2020f40400210300c0c180d0030401c025100c4405110b080d070645411400500c054802d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 692735899 1250 692734649 692734667
    0x424051503160e210a05010c0e0a1a1e04052b1103190302150105060306031b03010213120c1e090f0b04061502060703062301021c0e2b0f03 61
    0x25482c510852542000138550b9040d010906403269800c0126458030140205c0748400240c0d006021040c0f400d040c8130500300c3c0003800d281209a0008204407000004031001c1c100214401c0001000d5500d81c903010800540124902805500301040110f80483c4c003000300803564602e070b10146060325514158002400d05003081d402d240150003040000c003c15501060000d03400d05280000c080e02c0e40c90f05d0502015000840b85560561f1000010000c12810750301d0540c15188014005490000c480311800101e0280781e014003071401d40e03844020b040000031011f09020b480c0740165140c0c9052501d0100c10b10031881d01c108040160303240b030300012100003900701901000000d8010b002542c1da8031081c2010700c0341c0030007500060040801080d50648a0f015000407101e4000e4105004015099801c2da0100c01c984068154801c00d04240112400380c101d450f02c0b4910380d00e903004441d400d00306102d040f4803480580f40c81c20180765008122002c8040c14881e2841e0010740d52403151405160940756051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 692737149 1250 692735899 692735929
    0x206100f2702160215040605030c070f080a0906020d1103090d02010c1a040515152b030905190803040b030417030906150d030f0e0424051503160e 64
    0x40000764060030420325a01c040303c10f03442910840c2882c081c0c00c0003480b0074003443c00345000240b010004074000341c810201501403103004501488854160b5500d0034001d511401007040800c00d01001000615014402050720000c1070410204044c1450602500d9120307000a80c1d00c60301c00e44441d9000d592082040d501c00617072118041040c400000002901640700f02c400310340c640b044041c9652000910355005005680d0000410001d800b04010007440c44400d54038441055100740c00d80c421500d1000c4155505400f03915580070081c00c020070b00030b44102c0001d940740305851000c010414400f001088908070b41841003002e840792100e1034000c0600d10301100081a00340c0100510812890101d0700c1401202c200c00b501a500d170a6409100d51007000340409404111001340304c031b103058082e00e10f54000320380c0104001040340082410002c4100741442194900c1e000b10402d00c124244020490b041084009a881c21032400e00c2c44002c144010f49009803c10603510083e0689031500c03584001015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 692738399 1250 692737149 692737151
    0x5070b0a140d020d0605060a12020d0e010213030b0903130320060c06010609052e12060806040209090a0803070e040b060304060b1912080f0403061b0206100f27 70
    0x100d42c0e00c4000020f504032141c09a8000c0c41e0a50014580c074105045424604090700c80104000701000360000a4010003c0480704c41d45800c040322400710288000c203454801071002c400d94505506002c0117010700108030385440d910800071840d000c000744040740704580c0d2010002d0901039001d00e6450019001c0201103412900200e00b003042198081181c1c1e0503250107603a0079407820b9445041060b146900d012243c682410000316942e850a10b40203002c0400d51411320b400c00036100d0240c0d600b21451a4000c064513000003060004500e40b00d60750b1600500c1c41001407007514020348900349035110203882c110510800b561100c1d15a16550850882d410740203041d1901c0c0d182606001c1701034805604050710500b401000804594101000230b002d0741c4486017004040034803a9501d80d1036520007030480b00c90314024440080082c02034040c948900014820041003559059000707440e101d0094012041580b000c1c1080c440544001416002c03144100300e186201d000140881c510a41c600350f40000786 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 692739649 1250 692738399 692738407
    0x705011418120a1202030316050904060e190501050621070c170d290409080408010e01140a050915070c1203051503031c0b130911040e060405070b0a14 66
    0x4010640308500c41c00391913004111303000400201e171680700842d0701c0701c2072449072018520050300c0340003d080d6142c0302600019055403a6003d140d0000300403604580e0101c41048070300108130442c0211401404140c411600301024201040a000e030440d107980c4c41d1000b41030000354001d00c1003040000f2190003c4034240c0c6215000d007141d1955111209641109041610a40702a164145e800d96002303000b007122a04040260100809421080d0007941c0915050001140d030130028800ca00c0c5881c41400002400040000100e5070b0f1b91000b4490703210203142c03108100541e040030403003680010380010400304c55030714040107407916000114060070398440f501c215010507405600841c0503440c004010808a00340e0782c20541c0e00e12840070603d280700d4840f40130403410086908041d00003400113088401480034000d246040f50f800d40301c1543c50032072004a103c10780c00c2621400203403414140240603185095207500d0350347c1d082403080e607000810006500031200d1045172030700001c80c214002c40d5a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 692740899 1250 692739649 692739679
    0xb0c1605010212010816090e030c1b0f1e0d03211e0e1c030e0a05014701110a030e041a0907030c09030b010e0a06080705011418 56
    0xd403c80c0c08000c002601d0500041211080001c00100d030704e082a400d040e0303860411040034050210408842141c2c84184500c01100b50140003405541c3c4150b00680080c0301d00c0802c000d941c4243c030031414000e8030020020b0840700108091040c4006080d03030901c003580d9280c038088689040c0490b094142d4070b0106045000541241c200038003080b0300c05503640c2c0b407130006045031084032026501620143d121340700310900340307410b8411040b40007a5800c0010715002c0a003040741c101345222100303e4a5075569007480d03100002240f51034001103803030402c48950715452020f22411004034100b18450302001c03526542c19070700c01d00c10148104a000c094680c181c095190140c906c00240346c4083c4600e00b4580380b034050303103824800315240b030074010500c1a6030348070420160000e00740c01c103015040011555002c0301140c24101c100b4024100840350b4070180c40c01c0510181184c015402c04080c0c1d80001c0b07420043d5aa0190103404040d455141c6035035110034803615958072504510300b0a4000c4505100518 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 692742149 1250 692740899 692740901
    0x3180f0f0605010b21040219080d0f21090204090501060909060b0d030c03120207120804050d030507121104050a03230d02150c13150e030a08070b0c160501 68
    0x10050744101000d22050340c036801c0140b114011504414800d1400ca50078403000d01c82d50309071640003400900780768420302c916800c802e00314460741c01107840e95203d443e11440b610761018156030020241e20300b00d0000115030b1501241c0002c00804441800c1d2603018010079507444da8070207003d8070792080003000715035a6409000d02410a010080d101c0030b1030016424150709084282c0e03261164190349080b10082030380d0f01903443c1424000d4001049900f40f111000161141010111a45154603000f649140c03928000340b8207100316200390b00309410881803152013500400d418020300c20400b00400c1d0410004800300e1035010f240d008070b6100001040001c240011030401c190103c51103c0c18000d02122010080e83d6081501c60760001644801c0c1c518075102d4405510300d401c140c8281442e0301d00b04240f81c00344400c9805810007281701e1420b50700020400d070070800c901a54841078008d401c401e9825111680240640078010f4100030f2a800018482c60080007140d854004d000400880340380d99007800c0d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 692743399 1250 692742149 692742173
    0xd050a120c0206150409050604061e23070513180921091e03063209010f0e2104080a06060f050a05030d1206171c03051603180f 56
    0x8130070b004201011a400c1c20a80620840d203034218006103240c0d140d130ba9454004202440002280b001c0c80c0007200d0301910640104820701429120481070704004080300701319200e0103005007051003800c01085180c0c00b45946484100e4010280003000c420504500354098850700100811038245240340c56040c03110118168000c2403265600018141c45a4440d00020000e01114421003051241000015080d8101451240c0e401840010341070300d00c84070301082c103005c070310310034a0000c0c0c4800c014541009208403051031581000901c2070703100061049499807080d120b41c800c44080c0000d000c08a04009003104c0081030481c04540c5042d0403030800c0300040c02e060007280d07508a5070160001d25450405141001d070351000b00500070f11100c084042d00c0c0c2c1c911584594003803a444142c00510300c1c030320712051011a400300000d0204180c40392044642c008103100c0100074540341006210490800712030f402550f10f9079080015103000280c4943c3e10119401c00300524480c0004900c4003080100c8100c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 692744649 1250 692743399 692743411
    0x180504020406050c0601150206040b070504090f0516080106090308090604080303070206150a063501080c2b03050322030c1109010509060f0a03060218210d050a120c0206 74
    0x240d00383d662100031002c4003e00d487d5502e40140e102c400410007050440d0170880d005026410a2807034160b8485014040d508041e2049a407541d507007007000244503058039821885c00503803070440010340c10524080c0801c0c80500014001d00700124480c852529034400302c50251a40104880e164580304d00d009640342412a28078500d500080c0742c002c00d40c18000c04050a40e0002c1e20b40003440d44080114064106c4400a60341c400721141c00c940c41030090481d400b0327000e045d640025101042040341809400c07000243ca000e0314038125110f04070000309962880540c0303903041c0f40941c2e482d1076032050103d01c0928000c0c50111969100c0c204410190840f0344280d01c58030942d01c03555440d40e07800030040103610074803507260880407140010f000b031300d0403140c0700c00401d8006003441e554a44070340341c50040303030402c0300850f5019249107120045460044185240002640116503507145000030640e110915558802c09000c0c0220b50300002c58040c4120700e902ca091050100300880400c0002991144d082e588 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 692745899 1250 692744649 692744653
    0x1080705010906020307050d030f02162003120901030b010512010617010e06030606040b040e0303040f0b060901150f110f0601060e060703020a0b04110a03080901020c061207180504020406050c 84
    0x8000b49a134004402e132130a00d90400041d2214425424040d80038054062004440550811641d0106d4100c003018044060260451012400d9040b412049822980c0c1c680c0d0f1190344012098200145e00c00c003142d00c003400038a40071841c540f42900585040c01521802d40d000714500d00042103003039100504c1110000035102d420f030666654804c5100030b901c1914420740603004400010598140b9811010744044003a10006084451960507030442d04180d804403400941c840d011014848202e21550700f102c0201c950803150752411540107402041385800c031082c403c0151000f1708460007003204030700c014000c000380c400061509944c1a26083d00f40654004101408900b6007542041801d50396001c2d85900107042c01c00142d1664260400000d00032621345401c110011071589403a469000110320804100f03480e041008001380c203000710b0b0f9400d240211403c1c0249a0500c00c1652090740210140c20030500c01c5d852071482e002c801d0b00070f81100d508135000040000b8442d034001c008000300d240c2102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 692747149 1250 692745899 692745917
    0x3011e081b15090108060d32280f051009061d0105010510050f1b150109051504151e060e1206070f0c1b15030b090c09030c03060108070501 61
    0x14160b0a0380502e409907800950f0181c001a0f4608010080c1e2000e64001c01001000c5056044a0134000c001600300c08217461203402100c0001e10100b0500111100301280c28a210915600060300c2111941c8003400c0109128039000a2040a0240031410450708109000c01a42e0381460000380666850241c06083c004241201500e010302c01c2e00d050302d10060240c20354110800c01124540c04c0112204d0211004000d9400d4819001c00213440e452100000390202c446160b61319085603070140e00190801d41818100110a040071001025400701100c0000c1c60090511209503588801d030020050050719002d00340840000006240840e0035940c4c0310301c081ca10300303414021030070007080f500700e0203601003002300c2c15150088520301000300c107500d8001e8a400481e26421101d40c00c0001c204050000841c00b44403c0034a2103c074500b00e01c1900b010303c5080c01032001714011032801000501a5100803841c1744107a9414440d58000d848001d08a03029561182400c03902c8000031312800e400b10f08440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 692748399 1250 692747149 692747179
    0x9140301111b0114100f0605040513021c090c050f0102010b06030406181209030b060f010903150f1e06061b0308190c020d09170303011e081b 62
    0x40076030028514507050385820000c07010203011482a281001c44101e540303503080c1c50440140950161300c541c0c203400402c1501443c0000c071306503149180e0004010000704100510660b1120b44c03030040b02149126005945403104a401c1224041d0b40035034410b00e40c01d1503441c409001564800d181924812103007800495111703401a401c0316406000c454000c0c000344001000b05409034400750395010002c40014120003566100c0c03040e402c1101d0b40b1000b02c0c641040600521140c0700c1801d500c0342c401d44c0d004d00e11341588000038015080c0d902c4020080f039460030fa003400e0121540c0040340e410707030560b0f030500010038000c240c10021405540c0400c44903290600003d92244100d450300c20660120304242c0940c03445d51011a84200020102c1c2c0100712002e481c2030fa00c15151143c081c180c0b070268090441c1c1100c1140040c160081e55100c424244074001850b0716443c8080100e0381156500444016204114203610321180300c40e0b44844400e008400c18002c84643e00302c001d6010f51421201030215040b81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 692749649 1250 692748399 692748401
    0x3010e0c01120207110603040b220203031605070b130302040f050403091415030c07120e010f08270f1006030f0201030b0d20030f0a170f040f0609140301 67
    0x2440350300240d5416000350441489a0003810214052109824191001004200300e41e00607a4201ca910b050316082000d600070360fa141c1590380c8030704d00c403000882c407041d0002540e900810024890040c07178000d410341004820008600103180c98040b40391100c61903601e2440a407114401030b40541d00780f941c002107070100c4e446403900c240d9054540c1e0341c913a4184080c1c58403042c80d400c0f005070452504e03844d030030f481081840618421040507403102d42e600c01c9450124000c00c503a01758803083c03003c51515a8041e03030704201e11041400543c0740c101402c0ea640c0049020441070109240f800380303c0c2006800c50107001045200d8804ca030902281c41024108881c00f044031780a1001400060062045c500158402d802401703c80f5401005a2440030712500c8201400050041c05c6045c4024000012081e05051202c00140707021007010340503081c0607844400c0800d5040b501030300408030001d00041003030130034000d540244c0a180d006120103516035102400c0c10031540030b506440203448020f08a03130f02d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 692750899 1250 692749649 692749663
    0x602030a110c010c080f09030a08041805061f0c0209070c170304110409080936061e061c02040614090d12090506130303080c0c070e0403030e01050a0b03010e 69
    0x613524004070740440c1d101c0700d0b0b2a800c0704055070381c0c0c400100404080ba076410080c5468103800340303582a5850f4a82003801800c00805004546958107100c1007202d07940e181220055011380d001301c88280300803035403000c13204080c01c8c0d18000d51080da05070600800c50b5000319590b841900c5850080e4060f100d800211045000883c0e0003481c1d485026212000c50510f908000f8420b881110928144118400040e42200310b00e68200102020a0b01480740c090820024000c0d03038110801900d80c5061000200d02485000c0644c00103442c0c00c1d00056505456070740c01c07180300909440c54404c1300203400f08450041e5000b40f140400241c140505001d00c04a1041100c034002c01c001c0600c48800616611807400e0b600e20724407902840988200003400741c484e41c000713203552120700d407001400c10308502e0f01400706000501200f0340644103001030403050340d00043c66020389081c2c4894451581e65403600310040c000341c002011465003000103001100708550804401c1c1c0368210005e101c9481514400b03561182 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 692752149 1250 692750899 692750923
    0x41d010608042a0503241e0c07050c0d030309060c090605030403030e0f1203060307170307081c09050f0c04020a020c040509031315080a0c05071b03020a0602030a11 72
    0x650142592408008003100c809441d02c60240000181c3d6650002800e0001802401008245450398599a4207601e0821544005410700a4440745000c0d040c00710051f400424003e40803c000500302c0c281319082143c1312040b0300040102c019840c80749001405410002d10847e61982000e120100c00d6015004280c140c8500359180390641c0e4231071714114094211001030740d40c10300800b000d03c00d441c2403c1c000709003420702481c040340d230b40c0c10070800749450300710254000440c40e44910400325070b003480841114426600701c48507030f4903588010340644001d805261a8207019103804032078002c100c00401c0034141d00c030101d01516a0754506409003c00c3e40701d0340300c80900680080740f040c2e9251901da40010b4201d00032104a0f405d1070401043c1c040101001d802c4844504008050314400960001c0c3c4203500641b081000e11090f03050004c0074240d4091110020200c0e000c402403c181c100c0240d24400041da0002d03c0c1485071541e03a4000f0b5201c0d4031401c02d490008202d0700c15007031444400605400200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 692753399 1250 692752149 692752163
    0x3082a1c1d030f0a0b0603032b1503060c03140403020601210206031e010f3c0b0306030f0703260f040b0a031803080106050d02070602041d01060804 65
    0x9111448215030840722441c0045686541e44241046910200310740c011031262100140107010071410711240e00381000740380314801e45c4100040c4a680050659104019000c01d03141402d654a0441d0f4001a01d5440585100c3d0969440000700f03100c3e954000c010b405540d51410410750000c0302c00d00c900e0b07007001c07580079016074131542c010000c84001c104151034440030300a15086281060340081c0c450342c410781e00c4940782008001c000508001d8a400c06006142c8640c5c500000d030301d094041014041c0007401105d20013030180ca034003035400714055010099849176900040b1030352501085c0c0c0f4560401d407000350082c82084017011001000007904421381ea0800c1d00e005034880708402c625010140b0b8410bc080c0c1c01402d00c4200e4510040c02c01920282c84540d840503145c800e02540141215540301003440240390303c4050401081d041100c3e1811b50741189052503403103054856000292040c810000c082a100180018003502c1038585546440c84001c8042401e91f0f1302d500441c0c07520030640d0007038090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 692754649 1250 692753399 692753443
    0x602060f040b1e0c070b222d03180b07352d030f0a0b060903031c060b070314220b1903060f050d080403082a 48
    0xb080450508942c00b00000741c0407800c4524070946521082020f0781d103140d4401d00402e40300d081044064a0035806400b11011002c10300041800b050030000c440c6000e8815803424586100074a1481103c1ca0310742c2d9540d110711054080b0749001486102070080e48040c85596440104001051400b100d0201e41c02202d1504110b1605080d2003481c14140b02060303645011a4600000d58a0a03001e4581204400f03400d070507d10a4045e9001c52809045c40d5401c03650f0304104208041d010f9035110341c0c00c818210000902c804500740070550380d101c0c680c4c4040c0d1622001c074a5241d071040810910b191004012001d20a15a607000c550303e0300c0c0035505000300442c0702c5403078103810401c000002c0e042050703c2140c00c03514841c8124592100907180d8101144103840007031010750102280481381c514120a2604001c0d0364a0640041d11080d000e0040314480c51075044081305000900081d2009140c001c0f02d200c2d035840100c041410782100c1100352440045030513681c03070001c2c2000305006007907000c800c00800e06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 692755899 1250 692754649 692754653
    0x50103020f210907051009060309230f0c040b06030402012d0804051b09150102100204080a03170601080408030c071401050a2403080c1207030512010602060f04 70
    0x40e401070301058140700c0050200b41c0d08040d40d400189080d0020305a52a16414900e000700d0a0120603008603008125005122443c1540105880d048411038940046c0000c41c43c540502c1155400d8000003500c0c00d484c450301070b0003c005ca00341c800c4c910f04200329442680c10506000c142c58040b80015409801800000c0165005195440c256100c0b50440305280c0300e00c400c200c9014001176034007c0040c00582c2008100202001285195058002403100c0464078000007032120000910003035500c45210b0010b01d2507402044080320311890540255140c5440724002e9580e0300720900217400181c440000b20805000310307910705000b05010307502d03040c2c0303983c5580350388803d5403000d082007070b00b084100001d4022034038120150080192640011483e42030168a190a07252400c1c04142d008450101c581400483c50507881c08507a1312a001d15291504107409500380110381e18003100141001032020f041580c0079005000b0194402c0c2e0440583c0d8907410120f03550401100e807a10822160703004200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 692757149 1250 692755899 692755901
    0xc020306070e0126010504180209041709030a050c03060c0310060305042109051e010806120102040e15100305130f1502070602030609060619050c15040302060403180f050103 76
    0x2826041c18104020310005600d140f102d0300150300f441c4070040344e40c94018401c0f4541401307101c1c00c05089030364048038599160009101c0340000b83c002000720714020001808400d646060703664072030f002405d0f5110302200c0c1c10002e8030f48200d280c0540c824011000050f41d0003240c08107a038044c680b0070b001c460740703142000c1c810307001407001a000741c8180b00d41c40d641405d54248406801c06020311a84d078040c07414076010034090041c21410300090080740340402c4650320b90340203151030703480b135000c4582d06111000703070034524028861504041240c150a0040000140d030081c20301144000035901c80c10b5929081c0c000300c040752800d450604000c407aa241240102c0e10740c074026210640030b91805003004404060308001c0f07901c480e50449a030b80e004002c010107440c0c80a0b405500c43c00965110386000c1d103800d2025003c00ca081c1c50f100901a011540d0302c8444410410915074071000a00d81c001ca0078a0304020355a07500843d0b0440c002500d107416600551346800c030820490354002001060300e428040194 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 692758399 1250 692757149 692757167
    0x4090f0f0206040b0414010206070509060a080430140405010c020d030909050127020f03061c020307060c1b1511030c07090c080a110403020607020d060f0c030b010c02030607 76
    0x2a0b8000c905010200f8a41041c90007070005000d48050400319003044400642017600040c058400d0200502595540d900d48000f00c1e40c9290003890440d4180d81d4600d4220001c0c4003a020541c4909003013207040305808070085203020190310036260202c4d254280840d0801c0c61286000d0180064200044040142051070190f50350611a0404103622a11406401c0440d1000d03801898200090584400d0f07030403002255451080d02e00c403041d03182410003403030350f0031f14032020704014003c40000c880c440c566503103070a1000c20a03500409840030190b40300300051502c070110b44183e4014a07044407020201d5103c0c041c241c00c4407540904a03002c10b08042c403d89a40246200c100c280b40020040e8444541c000d004c00009400c034103800281280340d004000b40040002000e500400d85402165a4004202c0c000c1d0750889504460850759207003e880841c002d1285c1d014000d00722400d029048200c3d80140d0407002200c02a5a0704000e90440d0200443e03a03c0116603020350586c102c0004900c010344140060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 692759649 1250 692758399 692758403
    0x1116030210030515121b06030c09010513030f050102070204060b03160e06070b0103050f0d0f080a0f060b0a09080c0414061309231c1704020310110c06010504090f0f 72
    0x122601913454000316070b4aa40d089007000d00d07500644a10001c0c0d82e01e56100c00c41c0098181c51503401c0d80b504551803130880c030503500c0c010705108011480518414160307260601459010f10812411503140c0740c0f040c003030340140070200d1045080c2180840c1c2c3c2d0131068280e0703110701d00440805618540c1200290343e000051401c49403c182d003000b001000c6803503440e2043c000c5200e40d00a2050a807619080e41c00d040c1c2403410f00007042800c002000d00a50700100403600307e00b82c0000069401c14441c603070740042c147e5034000041000081013500f045604400700310204c0302c110003a50070000b00b0380e003044200c0c0d03502c800300c0122030200000f045290515058082c041098904005400c12040d20744c228403509052006081880070002c0703200e0f03410b0500003240241d100305491801007105c001c0190525401d280c0484020000f07000080a56030200480c82d90b22800807010002008045041d484643c41030b0060801880382e00c0000031281040d110725500303203420448248844080f03942c2c00300089216401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 692760899 1250 692759649 692759671
    0xb040c0f1d030708030316030b360708070906030e0d030f09060207051e12040e091c09170303070c081c14090c090103051b01090b04030311160302100305 67
    0x1d80c1046071400c01516004d000d001d80116120300e820800d201c03a0b40d0103000c0340f0040500302501380c0039584030603092042101c07180c407001c543c01041c00c07420a0351001c000381442e4191150014071040a40254825010301071960320140f19a44401c401d0701542c842e940255515403200e8105c80056105c1d50152900700c0700c240001c80c111500d51194420b03a000f01800341c0d200c2d001b6081c0c650890006251a80007a644100640f80d08203031580c1c0212580140d114415000300d800c5c0024a510f4424000e080117074407604110b0741038042403903008140503040d008101203454402034518010f080001528400c00c07031035840c0c4210481c1551048450380100c5004603c1007888442d010740c549090040202c0103504901e000030754a40401c00301e140183c0303103010900a4500d94018404943d01182800001c0110040d41a11040c0320004a52000d070f0390b48036034216540403801004041e40500d0802c00c02161004407506045050b0301c5181a8800b440002d60000d5450a40140c2c01e029820250f405046c80314 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 692762149 1250 692760899 692760947
    0x30d0f060503122a0307030e030a020a080f1e032a0a0809040f02210711060a020a0207081b130f0519050702030c0606151b0304090b040c0f 61
    0x202007458107100007100b00c90a00042000c134410806035800166012101e0004e0790a090f032688429103074800c80d1005001c01800154003042520200040e18001d0340c0608002d807400e507a00c3d241074035007880071101d1885000e014247e0740c40c40307541070840362f1070156100a14607016403a030200c00c040240117103034010540035072160210440c041c04510806401083c040c0d5843c40c0440400085072403400505d121144140101e003000d400003843d0014a5540c41030080c0140c9400d00d00b560003c4141081e820075201c1c8404000e402c10090300503100c4440c442e0202c0c4c201540719190251a103490281c803131860340d42740b04001100d00e4650000b10071403550300342c0020410030b06806042074400880e013441501c4a2003180c2d4120010034032406501c812a48080d500300644191400d44442021341603512810f86031909a9540d601076089038000300490030307440e01c45c05030386018646940103031003285060b41c6021410042c0c0d080ca8090310100e91103c1c0d0310650300000d0100700341c032569680c490035810b0702e21900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 692763399 1250 692762149 692762159
    0x12090102150f10050603160e061905070605010e0105090a09061d1b040606090308250b0702010c050301030c0b130302120705090105060c03030615120a061412030d0f06 73
    0x105190b402007940600c0a211440d0032a190924000284d01072030046030204200104152001c1c0c038000d8000c50341c0350443c1c071003810000041150159140d441084131070144101d0180382c02c00010540c1c1481800d050101e6030782c4a54650b402442440707655009141503001902880c202c0c2c0c4031401d40e03403140c2e00004001c840b950cc82480300404843c00c00441c0d105030340210ac2280f000c4400612648100d81c24407a8504200d0000c0400340d0500c00106080c0c00410414100700301210081642d000340e1070300158211150400768444507040c0d40c50b0001d546401c01c0d00c1c02c854440c030126030603242c1005002252a03e440e0301c4520a13444040c0407004000008008070050755980c44260703501007030030002c016a81c180b00401c1466001a03001c03a104007000c0205522028011090302e92001c0b0446440e0207a02500c4900310080c824190505a0400d0510030010480c44660050050b140c0b64480c420300c040c05403007404402c40059141075481c7d40280a184091502a0464400c000e071135000841c03100d40d50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 692764649 1250 692763399 692763433
    0x3041401140a0e071809050106051003020316030c05090108061f03020408070807120b060303040e0a1407020303130605060114190e0d03050a031802060d0c030c020102040812090102 79
    0x52401c40520684818000078107098090100b4092892025054080c0f13041000340d240355031411540100b07071701c1e2007504050100c01e40c88007000303100c0a046c031060035200e5100203000390b008450349681c40d018203c0c1908818400d20500001d0511034903260701d4180e40c00015646590004d0105500c040c0700b0410b00ca1020084981844806040d00e015850314281003490b41040d0181d00125087d600c0044104410010f40b1040e06d62690440c0109200e80c541a000c641984255004a030381100410180710388000d031030f448856448007940387d49525445441c0c0480e141d1209449808107448546692004110554415500460141003601200c0d6a01c6000c10b507541200c1c0751150b00310000440c00b03643c150080000080244100ca1821500c00b199a000c1c10134012002d001c020581c0d1552120304805480301201c40d1030350001c010b0741d1145001070021020344000b500700b9000a0800c0000c0c5001ca005009440070385440f000505480007181e00c5407a0301d5005403846504603c80c0503006007180c00c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 692765899 1250 692764649 692764661
    0x609090b06091e01090507050c0d02100b0607320f16060f0f0503090118060b18010b1c09080304030c0c06021506100201060506040f0f080a0503070803041401 69
    0x100d220640081d2801508001048900401c18030441299014141014001e81e0301e07107040d1010315800003002d4960f00b03002c444c2401540c0302c3e01c0b041c0c0704000407024120b80000c0c1e81003074a07034840e03c180711081d00741c030612500e4025124010216100700116002c210311807034240442c6101e941d0301c884e5007059100e150b464020391081d40d141a03084450304054440004454a001c0c040c0350400b00c0b100120400001e10105554517503404125000c0041407840b8002c0d0002907a50340074203519204941c103401c0401c010050340d19030520413803105440070100c50903508068101d55041118506240b010341b44000440d600c521100035182d0384000000011343e2000203140207500950712200750507864a050380410500350030110955102c12034500c401041164515032040080e56021620078600354140c1c05004c00d41c100c00d81c0b110020401080c0050019060000c0385c20410050310102d6488000c03640390f0b29001405415508204007141c0810046401590000e124049400e04480304001290854003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 692767149 1250 692765899 692765903
    0x71a0c0403020f1c081308160e090604110d03050919030c0806100303030e0f0708010c09050409150b1306080109021216050f0406170c0316060c020112060909 69
    0x1103414000c0d4100420100008102580d940031001401030402403c184003a100030071401001031110b060720740e200d040100030514a01141c100b42c240c209003500b0b942450191021480003440001c8844c480050664010341c0c000c0d041820b102ca5501c103205050400034030640900c00e04001d640321a456850200078071001002901180720f00b549040f070391880080d802502d59130301120502070812030025041007203950500780003c05415171966a420031841c0e9103040400d010754000094000381c11b40040001200507030f150600320f510b032000c1104372403502c0c6000d459030155002e020b61040035644001c2030100c00521220b01104105452411f8411507040030a00365100c032224011030030040340c00031a00c2800d2018000c008103441035040000142d01c500fa2190886001e07000303003500c60350b00034000b50045040c80b91240c1e0035015501d079030700102c50440c1c0c006d1043c1c08018440c5500440c01400b41d4010b681e070004008201d40046035982c1c92100070390b8006da41c80d60700243c81c3c407003486003100c3c040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 692768399 1250 692767149 692767171
    0x30b011d090702210a090506030c090613050409060b040506060c031b030c030a020d021006031208060103020d020c0609062d0403090f12140706270806040c03061b09050402071a 77
    0x81045403004144a202d0fa0287c3d0160100348280070003000310100740e070001007090b1803981d1035016468101c41c01c81103644c40309400c00e240450f0705050080e1a0049000c4201c1500c09009944401c030038486148604001003407260820720142440d0300b071081c01003681c04421003c4900b0aa0b00304146802c590001c038820000da404103696980310368040c440c0c00b0030b044011000f00103c62464940150544201200c40d080010344800138069a0113136055440844000c0f8045441d220000300e2a507681c1c00a0b2002c4d941c0c1c2c41560001408a004244405000440504240506a005000c80781c2000d400340040f01881406000424110035460841000700040c400c0c0082c508001e00b42004460304c2002c3e00740550f0461075040c00f080d034001c0290310b02140034400202da41e08500c10a1240e507000c0b600701118a0050a0521062100c4100e105090341c2c00b0312000c12554500c240001907a0303810a615602203500e000c410400e40c03411340c0c054020240203510b42e0142c1e049807009556845c4040b22120015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 692769649 1250 692768399 692768407
    0x90b0f2d0a0305010f0b04090203062b110415050d140102270a0b0316050c0f03041a0702010f0c062d0e010917070f080316030b011d09070221 62
    0x125414001d0a00503c05403640d511011b0904881d211540b0560003000091074002000c15841d41390904a803007907040c0d6035014401c01e588000c042d801409809816a041401c100c9001000c0c6898071440740e40010410003145098940400e01980c4244a4000e0707030a644640344a400d86502030004181c400350b030307965102c100705058955400244040c01032a0240304c2d80701c0e003031045015500c1101c0c0c0203042d00c01002200b01c40c1d01d0b000c40d028030500c0c1365a0101d0041c91b034031005a4100101034400e440c620701000140d900d401629a080d400f400c4c1c1c000e0300007201503032135079400c900546211190074081c90b00420040d04800c1d501c4044284e40300588180b10080f801d5a00002c9039109d94210300d10b07040000d0110f9000d58031000011034540103c01111a800201102040010502145075541c040105030b10fa10303104416a0300b250225002d20b02103801c000a041c1c6662041070f000496180f0f20b52510b0b180503552090000b21400184140154442e8000030254445000d40d80440008820390036a03035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 692770899 1250 692769649 692769667
    0x6030126031801030e0f062e0e0403230703051b19031b030909020c0c090705131212080403050d0e06091501060c03050f0409050c0316090b0f2d 63
    0x880c0e078055174488141d040144046c408040106096412100c001d900c100401e0b6003c800c150400d181d603000c0309060304201e0000030702400b902265480356000303407030f040007241201d40c2c3c20340480031041c81d2410000e400c0110000081c000c9000c2d05c0440c803482d0a926180d04102001c92a0600c1c410b80c4584d1008540303802c0f420168400e6006101c1507250601005000c22694060460720aa0203055441500450401c0c4581c004010a02c00301d540144203026900740b2050140082e81310310341c450030000d03c0740f801041c0510302e01442d01065900c010303450341d0390096034003c0b80c82d002c01420442c01c2280400210080d1405030080c1122003d02d403005d00348038101032010524000340c101d120083d260b000c0004010540d04106005a110f415042090b540c510040200505100d90f40008000ea03103402c00303002e00200880d0245118441c200940107e81d070210b00d00341c42e038034031500c9a0702c5410410000c0f810032416150140412084200b402010401c403560300d4241c0c16650030003c0d150180201e90700d40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 692772149 1250 692770899 692770901
    0x60c01020c0c10020c040e1203071106060105041802130806010b0d05091b211009060c0201060506180f0d081201060801051c030512011715060603012603180103 70
    0xe070503001120340f070101c440340c81806501d0b0201051712034403c96803040300d0401c07948144441010010051940b547c1c0345002c02020b0024004c010508285208074000240207500560444d825913071184440e0000c45501c024140107544601291080c1c555058400900c1c00820090300c1d01030455280b04a4130f6a810030b552200312100241814003e138414041c6015119032071100741c004003400c2d00c2090806040e06c40a0400c0c3c02442d80d0102d0600c50303040490942149903104500d21031044c0d500740502c46001004a09840b414095250310120030800c00c0401c3e041034040038040c05c030150a0304640740203c2c0004083e4040d0403800d4030f500c240021440c000b81c1080d52007a000d000035061000c0c1e15418980450401940380e0622075a800340c0e24920b04c141030040301604c8408008801c0c140d10b40da11032103084404441c003010002c1d44d1190f0b05090400c0f81311030345c0c014810340e00540f2140c00d5a10340109a50b6074814040d454201c1e8000626840801d0305c248028003d0f02c0c440d10120b1004507403800018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 692773399 1250 692772149 692772163
    0x3061309060618050613090f0803070c02310c02160915051503061516031e1409150403080d0203060307060c0803161803060905071203021c0905060c01020c 68
    0x2d8403444c41c12007001546d03035846814002104814400082100ca035152900c0a252101d901400c4000c000c010481c180f40d00c014100c01342403007a10701c01c0c10058010110704540710050441440384642004107480802168408883d0704024411203441c0d12002e405800c44040382c0d0404801749840d01c40707211118481400304002050259170194240d002c0240c402c00340c1c040034200c0b03445032032138002d1201400341000c150317002034482000b0724845801d140b8014204002d000410041121ba25101d1040d10f80189071401001c1c40780303441030303103040180c404219140504e20500c0c0640c510500000c40461140f10160900054000c0c0050345d90620604041ca0038001d5401070041001845c03015001078030b01d00540e41c12100d00c0351403501c07446a186040d40d80c80b494a252203101d0103030740000070500c000f6400c0003404602580a41d5052030700c6e112055150100000080d0160703100c2c004030521804c4c414030b00039a041d80c91a00048054484c400a00260b0110289a4107690003240d04800103070140803075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 692774649 1250 692773399 692773439
    0x240914010605010e01020616050403020612041401021614011103070810080309060901050d06050915190303230d0216060e0706120b01051c02030405060f040f08030613090606 76
    0x1820135603100300013560740b080203181d0f00040c41e4003d0455a00c900540507a0041d550003003141e6154040b116219112860444042d5440b100b5100703914550401031007212140d4400303c5c404100c0b20308540f21240d007088802011403866680c2c40084a0460380980a18001d500390b64072000141400d2442030880714490b00005107903081000f850101e6036440080310401942805d000340c641001c102c024000b045c00b50b21280e0000000d40070041d0f900480d415400b0342c09022609040b80f548030010618145880e404001c001c142c000c03014070650404003458031410040c0c40040c618142c80050b00b82e003a84c00c844024064040204248000c1256034003d20400003c41c2000341724261a01e80d005060240f000d08503104d0b00c3c0c0c0d6441004080e44154101e81d2070740311861300b83e11a0301c4004003d00007035000b00d030706032114011440400d5503d1010000725000b260801580001a105619180281d900113840e01c0e60090000340c0c10110340850340a0b0401d031500074030001401a180c41600780403082c0c90000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 692775899 1250 692774649 692774657
    0x150509060c04080712060b041104090e0a0c090213031e02040c030b0d1b080321010b03010e04151d07080105070e030a0b04020406030f05010203060a05180424091401060501 75
    0x30070703c404a800101c1074210303404000c0c50101840d103800c0c604020b00520001503002070500c3c440031441e64528005104580201c20b081000010a510068072048200402440c200840710304019440164014041d101d580c500c0441c0c4040e80c0703980c0d0803150080e80000307441c40600300d030b000e8055207010710440e4140440c0c2c3c241484030590307070800192034100d10800140ba0f10a028001c00c0b84480c4000c0750400360034040202d070764034201c00110b0303c4088004d4250211086035038002090310b8103a40282c82c101d603c420b01031354803600c131075803a940da4a000c90042c2d4415035a43e0240d000c0300304e40d035680411980368900681411401d0080780c5094407001400b01007440404800c0c120103840008038490540d41010b0f0080e055103840c40081e0182c60f071540058420300c255501c080500c48190300550103607108a5049142996803014022001410801d0011310060380000802043d240c02c2c01819102a10103120001005101f081040321840360081d030781c41e030300700101d070345641000d2203007802401c0d090030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 692777149 1250 692775899 692775907
    0x6030317040b070c140f01021902070b03012309011d0604060f0302061e0c07150e09060904020a0504050a02040503160b07150e010c050c0105130825150509060c 70
    0x12442c91880b000b405100820507000d054006005182e10702c40082d1301d610060f0307414081d0255880e8080e412440800134000d41c86004040c41c50300010b48801140d2400c1c102d03900b0344c0c4c80d00e000135a011a02c3da4011360a0070701c82da8481c0840da618081c15007c0c101c1807841020ba0030503010320300e650301c2006002c5400703686071600c14020500448107580480754103e60f6960746130003c0307040300c000c920f803c182c40203841d9000c1600744142002048040c00da0300054010781c281040ca50301251403003c0c107028141c1141614003c9000380c04d00d500c8c89035021b40090610612603985101040488908850003007401d0340c04107091045140520041c0841050281c82140745410210283c00c913100f041d00080c00402c41601024902c03825800500402c140350000f00111101c0c03400180c02d9612003084040c10b5468100001d4242004419151516401914503414040c590040c07104bd1184100340f0310504580d11100700005800d40066000308640303403400b0171309050001d440c40c5401c0340501400d19841c4180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692778399 1250 692777149 692777153
    0xc090c0804110301110f0f04050a03030c14010c080a020a030207120810060302030402031009030c0b010e180313150207170109021f080402011d030109030f0801080c09010302090a0e07090603031704 86
    0x1090340e442d080c1540f07803d591036102c5855487c540c441c0b544519000b5240b0140003080c50b41210700268a24000c1e400c960741c40d469160040c0c02c9403840318001c40459034420110f20541c13039650140134111a181070051415645881d1f40d0346c4403103c10302050004810300d040005002030441100018145420150f046091a80c002500c0300800d406c600001581c41107100207140c41fa40e1f1002d4070755002030600c1030a5850324140c2607201d80072110200d40c00010b481410b24041b0002c22500c00301c100c034141442c800d050021814425041489500451091803004103002c00c0c5484c401c50040404400020004940c1c0705000d00014000000200f0402840d85c401c040c5030480b00c01c6501941c24030f0201005500b02c031286441e040b4005032a5015841c0000c82010950403000304275680400c1c1d00c0e042041ea84c2c941000f59501a81100325802055810041006090002002d81c115080c44400315090400e41c040360725249150744140071003520b440e010014150008a898000a0358030200082840c1c40d0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 692779649 1250 692778399 692778431
    0x311070302030304260307030c0323040204050a0e16031205040303050d02130b0a0809060f091e0102090d0b0f0717190e0d09061106090d0c0c090c0804110301 69
    0x24005482565052080c5040c200061080b203070341c1c080c940ca020385074205010700138000c059028003a000700340f400c0100b485548201040009142f640301c0c60200c940d503a5070a20000d044050900d900c0d02d526080342c1344145209001100b108001c0551010f4014590300307010403038072890301c1c803403080c000b04000610100340c1c0841104d01041c005180541e59194414031502a19200c0d402200c002d1400300b2480f0090f03620940c890302070a040c00032907145484015605c150b4140a6800c0e0f00c40740c3c004444d481561442c1200303404001648400142040e214402141c40303041c6124044803a440c2200400c00d011605560080c0c120340d00385802c00404429045c081203900c005805450030380d11a20741e07140164041c3c0c000102120302c0c10243e4280080100c00544030b502c250058101154000000601100001070420b00c00c0e040350004201e2500041819a070a1205c51400c0d00c1d4000d0814001c0354000a501072084689002e64800480c1d00d800d080084070303101c090400f20f00c6641000400f2495041d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 692780899 1250 692779649 692779651
    0x191a0108010611070b130504051806070e0a150206040b0906011404091b0308030a0e031303120c1406061e01090522090506040204180b0f1902030f0703110703020303 72
    0x7183c244a110981d0200d070781e62414582d81c0c82045206000030741c80c0200c0c80c0003c408002c5070415034040c406500c803046000301b83e40010104040030307404100000d2000e4070690401d00001c2014103c00c440b1900c822141c1001080200b920015901500600c82041221142e0301e9010700c802e0098140395050040c0c0308004901075104910039a111000d8034140050304500c0108207400780e14444145070340e031400007071a8000712007600b0403d1801c010012007150110448070700203690b801c0a00e0043c2156a02c80301200ba10070030a080100034a00400043d82140d044081160807400604481c613101013005450030050b407252540d0500c015824071141d0b000445032043d620100c0d5002040a0464220400500900030441c002402d00556105000011a101f4000c3c1d000740d6003803100d10001c00301d500801c0f403140360045c00e0240880009040b00011042c154020011071042c8007244d940b05444000da0300b064543c000904d00030002e00121a030144100b00c1c2082d00e0b108041d0401010f918081d4503400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 692782149 1250 692780899 692780909
    0x507170703060c030b100e01030f150b0703020f0303100519060203120a0b0a0306090203010506010e0d0b040f0c140f04051b0903010e06013b04020f0f0306191a010801 73
    0x180301c030b100610f00c500035000000c29600140200c44221028040100780c089409162070100340341484810030712259028141d900c007c0a1b07000031046203088054000340d0b21040d02074045000b640c100c0c2c820300e60b044c001507004000100d4880c101a0400f8200100e04403801d1400000641030203081240d142c002c0300780d071140d2080d020b410380a40c4c1d41c0004500a0b080d805025540210380d601e0110400c0844e42c01038200c80d0080c1c0081100e651501c0c01902c3c03c017561201c1680c0003100d803101f41c2c00142d201d01c003181d02030310400003903600101c00d90398100c03000c1594008910308030321780c0c03114411400c050a0040150504031810712180c103004441d807601c0c24071081100581200099401d0320f5072800d4024016090012045801c0ba41e910a120300d0980600d071310100081c80a607000c080380d400d444d0802d04510040171805490f0b41c54130317801c00c074008031078060032601304000c0602a06196818001e0b240301d20100300103521411480242c0d04200c0d0100105400040b00d407801d803000c42e981c40762171541911 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 692783399 1250 692782149 692782151
    0x371107061d0d02240408070f06090b0a09090204030b090d03050402090a091707030f0216081c030b1503190e0604030c020a0308030c0702120609060c1c020d0207050717070306 76
    0x42c090003c1000750030040092000134140c3c2050741c003000243c4008001702d4a1100079540d03010745803000781d40d502d00b43c1c0c4101d0f0700140710000c003804106e4068005040700c4040341004c14807940c0e1000401b081c0d820030b0784181e480e41008020040060400e010000d01d208040c6006c00c528902540014031402c4040c10380500160342c0c0c100801084041d82022800a41480003035032035480c94900200011700001240740180110416a16000010112901034038055406410021482c090a0b00803240f1207810302c0c101030701c481604059444000c828542080542e0442ea928030301144410307081c441410040d02943e2030f012400003581408242c0303c0e003207070303062500c030302c2401e214000194010b441c0c0d007014188800000078450703140290001003c80c40c1c401c2e1441e1454403024107600703440d210101c501d61000d4014030001881400554024247c40e010401141000b0030050141022604111660001140c0c0002d40364280079041000800070034004e401262101c0c0040a91354641900d480300904103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 692784649 1250 692783399 692783419
    0xd1109210f01110403030306290901050706020711040506190b09060c07140f06180108101508220312180b1f06090b371107061d 56
    0x3011041c003215007500e20304402400100c01444003d038450b0b025110840100389000d00001d003110403c00040b160850386000092040107040c4400301036446400c0c00e5041040803c50500090000c1c8041d00065016140320000d480c00d00082c0406c44001a00c400c0c40341c400da40030b5605202c60020349005640485004988a429801c01305409018071031f41c4003002d0181a5002c070b807511101991500305003080301d1000c20004210240a0644034150f0f0b5a06005920300c0d80901c0c07035003e106a50307004004a440100030310313a1480d81c1105031b2400b4070307013400007040041402403041002e1000520640402000400f110f62643d005d0f212018901c849010544c48492a400c0e10004142551965030040d00d20003442c5040c0b1100341c2c07800041e50b0310044081b2804008101144205110f506547c0203491f51480c2005102510300c4103034105505c16010214a840602c1e1800c03101e08580358106107440750301c0c458171400505428640c040e000203040044240111101c8c140e680080c0c89092001d03901107042c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 692785899 1250 692784649 692784709
    0xd2406092c1227010e0901090b0a03050d21020f03010e0a0204030501060b09100e15090d0519020319020a05010804020607022d01020c060409050c04080708030d1109 72
    0x504003408500e0701c02d0701000c10744000301000301031003081129541169400059001006440c2d007803840382c0706a0001c4000006100c1071005601c81044210028025911690340c0d0784c40926000b200c2300c000780010010010303140381c890a40a070395445008000107504000302e0f218403801d03900052041030081041c07600443c1d448502581120003a50300701c0300038024140c0392250a4a641d2010008038040c05100701843c81c0940321320703640c215071030700140444442d01038003a0180054002c81e282ca5449000c02c0d1b0b000c000500108aa84042c00034410911714080d0640100740c248006030600264848001c1e40c0310005030740d0101d08505444007400d003007200e82c58a0000c108a03001d4807000940080320144550608041106003600100a5402c400130380d0012070012a21030840d504900e40210f0148000d102c011800d80003e84e1110a02142e24100703691114468a042c0031580880c011f5000021010310f01e01003030042e075001d18440302000303250a0002000c07540d4a80003a01315200441d456a039018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 692787149 1250 692785899 692785903
    0xe1e0c07120801030210050705070302090601020c060d0c0801082811040c031e020405030616050c12070204060b2802030903011a091302010215060d2406092c 69
    0x10646030041c0038952080740344100a0054542800300b6445150340c01101c2d040d20b8818011251540d138840040c21041e031560f420b002300f840b0b01030035481c154007820100b1101a110540681a441e002040110f01d801c8081c03000350119030180c100e680c4c15000f495240001c3d10700e039810075034803440b0706060343c20301c8419040c01c7d004d2908420045034094104114203005c183d140e0480404070003172031985c081d000d00c029138030301c01ca00c91845415010707040140020503a02055200c5a41da030024100940391440741c4c81110708010000401c031840c1c1d503000c9240800e43c01c0910806000d410740381007582c40d0000903058650b030000c05c1c0b007013108042e801c0480021154420300035241c02c1d09000e0028050a207401c40d1000607002d95444940c0103a12140001c0d003602001d8034541d071140d8040c0c000d801880b80c03059000b20382c040014440b60300065580c80441c00a6004505a40f04001e0f079600403046244940d002d5080d941c644e0300c00403055007000c04030180b40040c92284c480c03071080d680c4e5045c420480f04507054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 692788399 1250 692787149 692787157
    0x40e0f060102030a081f24020d14030a0e070e0124090b03090109150e010f0204030f0b09030c120a020f2e0f15030c0b120c0319050a020c070e1e0c 64
    0xc11008111040011141e03211044078400508508080e00c1820a0381c0d070499279002d83c0c0a9100024256841d091107280c000740040d604003000c60780c0410411040300c02c10b4602071035175011514072140342004000743e4420075410403864840070742c4801040c0c0001780080c200c0e00c07940241c060b018000400300d100754400358050f003a500d500c000909040c2101e044888020011416002960750034000c158600000340d00c210b0b41607030390142140d03544a03050740b110a20b00000920f640081d210400c041c50880a04000c0c00100c07803070401485998580c4008020700b04032400580080355404001c6070380d03500e000c400c02000c0c2e900408008002c0340b003102420030042c00c003580c0d00001c228a4085040c0f0f903258612540010740f03000300c41200d20300350382f241000f00758400c4a44000106188030701246d040750f52100190341003440d1031541416030041c1c49000e411907905440400340c5540c00a10700351100307810b11a81c4010034018460010324a0312000e40f110503c0d1807280901d032090b13035074002400c2c1e8400200395 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 692789649 1250 692788399 692788441
    0x10e06070f0b060a0501020a08180109030602030a0915140612030706090c03050708160501120212271f0c020703050a0b010603050609060d02010f140d02040e0f060102030a08 76
    0xe04150180742c108106102810745609009103801c010104095000207850300030a6800300f92103103808061044d43c80040e181100c02d504000c0e0226000000ca910390000e513000b0903074442c00250b01105494000c041c40c04018036100c5047c2015003072805032105925559208005440905400d140d00404604600c034100d0020807082c54070140c201488007142c6590166441201107960941c3c0344c10b515507039a00800e00d1030030440301c02203090145500c0b40c50101d00e030001c058000350a00d070348005c0b00d0a024408480303819241e05090043c41c00103595005241a011070003014051400c4030707100e8144050000c0b0318084c1c3d0346440b60514201c03175200300031150045800405030741701401c80e0715011204810a2180c0b00011f402c0c0004503d4518110000d540680001032129021942a600542c1d10001d403101c0070090100030701c0707a42d500d908041d0040a0313040c036072400141e48600741226500640800ba0084080d500e0000400890340d0f000011075101c1001800c10450a981c2d8852180c1500343d5a642 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 692790899 1250 692789649 692789663
    0x8041d100311040510260c011119020303120c0d0b0118060509060c0d1107081c11010f020c03070302060a050618040c08030a0903291f030609080309060703060305030306010e0607 78
    0x4140c0b022581b61040d440f101d22070a040d1481200e0041c01100c001d07000c01d02080045c0c0207200b0203004000c41540a22084c1c1c40a815039050071b1150b400009201e00864240c0034082002500c2800243d09100c0c803249440e09080603404030500b61b40810b1f85031014000c200601c1800202c0303040c1695120f040d25054036501040701c24218406200612010640c5408141072081c1c9101081021004c100c1c14503400443c0340007040c409005104030303003e202130001039906558603561481c52541e01e0006043c01c40600b80203655858840c580285040b40040150052910b05824050f690f41c5501781602c03c11403111060070380d516142400001d9041701d601c90407031880001804202d4641000c000301c1244d00812503002074407507094142008441c6842c003180302d0701034100040c040010b43d1400b00b46a03140610741c0181282c4030b542c0c00c1c08803507902c041a20009008804c024401070100140c980c02030143c81c06100040c5159600d50b56030001500c0c440c140b012180303041e0303040e40710441521074540d00404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 692792149 1250 692790899 692790929
    0xd0314011206021603051b010501080c04050c1210050312091c0219030b0a06051c08180a0308220b040308160209040605190c091202030a08041d100311040510 69
    0x34000c6d04035800040781000c0405001c2c015004e012041c45074034126210303c4080c0c10280a401d00704401450003c040b454681402c1c4030031140c866240c190244500c3c00c041342411614182400c0500e080c408500c142d007070070313010040030165882e50301103254240041c042006244419200140901c2e03404140390074200885003000041c000380b80c00c0c40e8003614005104200f610746510501074454684190928481d807400381ca540090400c02c01003101d010720840030212100f50500040050119a00c140c900c00c001003151680c11a0309d03410120040c903030262840c0ea1901e088040c030700500541c44085d0003940040f848080b8050314203500301210703500511181040c0303807a240c140006d20090710001c1c0c083d1101405070391035144500c10822036084076155010000e1410303482d14030884a0700170482c0c05014200300040002e0040028101400074500c111078481da034608203c3d150080202400c0020148a008002041d0080860708130300100f45c0303020455569412000e02000c01c903901001804000074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 692793399 1250 692792149 692792153
    0xc0e070203180d020303070b1503100911040501080703152a0305010803032221050d050c07021008090f100c030b0a15050c0c060a030e0d03140112060216 67
    0x1c801445820001e140803801c098150051280020b10440002d4041d40100025170100b45000b281940c41104a18150800318509012a05113506034400d003000d2034035140c0c03400400505000c61611043e0507070f170030051036140c00f207111b590305450310010b845940e0a804445c550034050b00910744e00d5400328101800f040c5022403914840e001d080484000a00c1c101c008144507501204580c000e0050400c01c59a03101102d0a0001e805034000e000c8601e000c5c440c00d92442490301c02813072041040b81e62500c0361071b5580c0d044400b080d168000c01d681c40100c0b0421072540161380300750800410b4681c3c3e00d03001600e99a0783c000e0510704401409008a28441d8031000d1350f6071100c9420400e182181c0781e80034000c8080701e07801e1040e07121480c0a40d65a0029008007010024411009450a660750400f1a04220301140200f000e41c0c0c0600440b80001c0d4072022240d500000c104020301c00e512040c41c003005051001030a00100c1d00040c00352000c80c0742c070100b0080030b0001070f40558900d101440780d0421001214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 692794649 1250 692793399 692793403
    0xf200910081e03042d0b0301030c0e0103150e0c1504092403030507080d0515010305070c050c0927030904050705040b0306060d020d18021504210c0e0702 67
    0x9803146888501c1041e00749038600070120311400d80603078800001c50406040c05000039003010900030302e80c40c03681403100c1c05c4600895075402500030701c04505000d68075419400c4c20f214402c8103400c01d060401285004000152030440e48020900c1c20401c00200e80300e07107085080c00d15014494041d40004c080c1443c0c1782983e1004014411240b00110400140504888141104440f5001840000001c020400c0424002ea0050501502c200981450014281a01e000b1180161820032222224152207030303041d60180302d2a9001004c60928074040c14055440b1303a510040e01a07501e00820000000c5400d02c014010101a10700800712400070507404002c415507207401400074544154100404180ca00e40114121016640d00fa142c245c0ba41d6244070610505a1101c0c0703424241035402c115044031060f803071107548070119469210285c901c485004205070a59592800455400c04101c2005050415519600201001c404078030f0401c00d1350074400d00c0200700d07920a4035036070342e59810401100d0380 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 692795899 1250 692794649 692794681
    0x21c0c030b010f05030a091109191a130c0905040207110307050108070804030806010c14010f05011a04050d15140414030a0503010e04020f041104050103050901090f2009 74
    0x1580da4200280e003481001103984455980000f004a9000c00c0402e80034a06074000030509401f0b01c07544212180900007041c2416400c44405131450402003400c0c80c0c00b841b0f070040800c10a101d14030308007009000400282d16031240e03031805066940e81c070390241034070740514401801068024000c41d01c464244c205001941c0c03481050b00d11900400c20040340941c081c801c0c10340104199910302a55641e569404d50320244050403081c18000c4030540c5000050411070051621200d21001150030903032844103605852060b088060340c281d0324002403044181000c01c0d2002c1314011a0910310440542c204800c500282c426888070307650410600c40071000010451500403441000c5e08181c3c03040440016460740a9000102d000070010001000a0a0b095007515080340c0000c00c0741c5000480680080c040f50000790480c589040049820011903815200d5694000082e000901c48401c1e40d948102c25100f150000621001d1290705444404e02120210010340d440075080c042c1d02c5c02e05134030040302d8602c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 692797149 1250 692795899 692795921
    0x6140c04051507030f0804050109050a0f150b060d0218150304020a060e0a060e01020c18480f03070207030b06181911030c0d0b15070303050a021c 64
    0x590039100540c101541001c43e400f943d0507940b403039990b249101080710f00d014094002d641941d25009404007092080c00f8203800360f8030440c0b8441559140d450030f40301071200c0d890a00101481c1441d051a80d13150041200c0c1070000382200141c0c7c0e03d000481d4558580e2010903d6a00400c9482040182070509030041d03000d03034000c50700d45d174100395645c00881d0703001412041e08d900050068010407145004074040303007031032805005680141e041c0801040b0011481100140006601028811844c15034500340008001620720b9060706208d40301c19400d0700c1841901c90001c4036106401280c1c0e0f4016101b62744029900340c003416134034106006c0c02940d0300c04034001078030100348240202d070300c1c1d00d0b001e00801c7c2c4c10000c9140f42c1096641e40d086081c007a1003e003860010068070b401400310300e00d142030001c5100d041000c002c00d40f16200302d0900da0441d034415011501488810103000e851104207401e550f4429403600d8007003a40d59451801002900030641100c51003400100c003521145030a030040e002082c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 692798399 1250 692797149 692797159
    0x702071a07030e032802060f0c070512160b16300914120f1917040b040b03060a0906030302010c14090609090a0605030715110c0a1206140c0405 63
    0x5900070304141d00d41e03030b5a907032071400004181203034850b5808005c1c00d1104140001e08190811070a41486402c503407010800d8070650300006003c4c40a032a0100d00310121421180080c00b80914248980e58124818042c0003051000403030303006200c07464044140c1c101a4400c018080421043d00980d41600c21504070b8441c5044000c0e8000c0120b1154002c801102c08240003480902464024000d0340075400c00303209000d000302c0351202d454000400c035000141c1e0080c40d100708540b2103410551103400c49070f08908e2030680100401c000c0401a402601c0580d009900c0103540c0703445200020701d0380002903200f0f442c4182024000400e054040d032008025140d1610b543d500d64100030b03400c5809208211090768003840a2102160600f88100c40a500c41c1c20844000b0b09242c07100300007860001c2e20782c00810501d0303150043c41c550035404510044148980c00090400740746071000188801c3d0b481c043c0f45820003e011805050226603000920740301004036042d8a00d051603080041e0942c040d020302d901407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 692799649 1250 692798399 692798417
    0xc030606050f0612070e1f02071421070302040911040c0903050706030b041503050d110f060105060a05070606060f030b0603011d100810020a0e0907080106080702071a0703 75
    0x703030610103044100208014407203031610564080140404002821004c1040f500440b03064442d100c0d0480340708244503c4d8240d6080380c0c4074680003850414940c010250b02c1c0b601001c2a0910b031916040c000c0c04103914110200c4103c920001189406800d80c00030754402d040401c101d090082c0e030840005000c41c16203052007102c0022109444140852100808a0344001c07800c2241c98800e078440000044000d001080d1004550101d0236101015003041c1d030f1036003264151160441d00300d81d000c01c601b181c42015140030348060300b03c83d4640350b05110300740c099000091080f103414490310495121071740c0400c041048913298040105088c80c0d801d11320f408a4603140342c08103249000e8050b40c0c100d90b040102d42c86145000010a03d110700060440c0e0200034030804003141804091000244003a8003000060b210041d410004040e118100b1070b4500500000c01031240c1d0079401013141e410340b07035942482c55054460703500480c50101075a010a9480b8042981c0c00101050301c1b000341180c50003035940440c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 692800899 1250 692799649 692799659
    0x101109010806102f1f0b0d050c04090f02030613020306240f0a2d050628050d0606120c03050c180307030f0303090b09281e0c030606 58
    0x84280030244008284561080305002002075a6600e13000950711059201118036001d4510f003056074080b0000283d290354203a61002402c1c4600074a410b401c60f18941010899280e494444002005c501c0c016515001800144610052070741170380c0350b02908840c024a015603040345003041c20042248203014080c0825200d41407a506401040140700510105144100170402805000040c1c650050340e10f14000800c2e0000c20f6882500000b0441070040244c0002441c1301a081d450300060312801041c8038149641400c42201080c0c00c00c5d04100740c2c40000e00c0340082c0e616028107018002414180140411041e90090348820b070780444070414000350300c81c20301c1030741515402c8032215100801400b02d42c0d800344000b2907400c0440d81c0a01920500341d140d4546907035a240720a000d0340420b8a83c400002000348000d4556880418a4050301c4801030b0009850100d0303e8203400112410760340100c89007880b148850003131000c01c0c10000e030300000030a8540000308902c20700c802d4400300e10301440050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 692802149 1250 692800899 692800909
    0x51c0605090303150108100302040507051b0a030804030806041401080a11060a021c110d0e10210e0f01020313020913030c140f0703080c010f0b1c05101109010806 71
    0x1300420340310310f180000301c4450b030045a0700840204410440c02d001140080541c903075100e1240103507010740d541540d8040c1d00080034030300460203c01855a80c001e01924004ca907105a840390481c0c1d040c60660901d407640000500a40318194007160914000c4000281c18203001640b00c0445100f1644400000012000c0044c2405807040d110007607003000c000c05405101140c0c81910000030307828009940791018850910b0540001960030101d03070440035000651502442c0c003142d00701c1034607000400c00000020480d1000c48802216921a1034242d00c85461000303010300d1020240d408021500c901c0d01003082500c699040400307900030304c40b480c0865403101560382003407400758258a4a14094460760385181801351407203038601d02801120307144000c0c484240f200c0c40095000d41c0e24507407245005460142103414046089004a1902d03100384803e0303c4102c56000f00d0300482c0c1814060100c541407507406d2200d03021505200034981001d0030141104000075024000d03080e61948040c2d950712007406 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 692803399 1250 692802149 692802151
    0x70f030b03070501050a140c01090b16120203061215060f06031b0307110a03082e090b0312130f0f080a11011818140105010f0c020a051c0605090303 65
    0x154140d0401481400954001e00c02000e0f100f00078680047d60a00000900003180c00200200d51965100c41c003440c28040ba07006c025800c21f040b80c0e00b00364074000f44200a000c1e800d04103603204007650080f001440a80e81e600c0406580b051100644954861140e01c4c8100c001048444070303c910106c0750b00c2d10741410403e0649100c0d48503c041e1102c0211940702642168100800f140c01b000002a1035030300046027031056540091007510743e980c03581480b9032602048180941c0700a14540c0490f80740407602d030240368010448100c00000603048011901090910b0440341820025100c0092380001d0001400e024004903201ca01903400e6560300c070b0400e005119858030800813564012070b1244003140022854100a07581410113550304d4200c103051091800719944003682440d000c0f40c200c60004007501500000030007100c0080515810038001070104c0c1d513800c160908003d660403100e0708544420902e80c015007401404144103841040312181c62a00c5414110381150500f4045003480c100003080d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 692804649 1250 692803399 692803421
    0x30306030609160608040606090e060405010e0d0212130906080708010b1e120a02030607110709090215030703020c0a230c06090402070203150c2109030706051815070f03 74
    0x440003c0c0c41c0590440e140480544282c5055585080004814420384220480750818501a20070791915003405401c690300c0c0c000e016841d801c216480b0700411703404540e12000316078040c0709649807407041c400400300202da50404501c0b02e01d0440d012078843d8000602074201c480c11030091200840140611900104020000c80314200507001c030309491814503031940b03180c0c9800007140d5446100d600003030702e4800280c48100c007052410203a48042202800703228050000140d085c40795070500d0b804504610340401075140e49400100201d07170214444d030100c800c01848a400c94050319401e080461129190800e100809291300c0c07800708000d0404205885d260b03000038446420a2000824440070b0341c8050b008903454011244401c2030031075031654a41c0610014a9840d4641c141c070341000e0482c5860880c00d072040c400c103108000d120308000084480d9958032036004143c5444c0c4000f107034010116039413140507038042e02c90440707032021924540520075629680c4800951400c500140e040f034802a080d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 692805755 1106 692804649 692804683
    0xb0411040611030c0601150c0533070e0121020d0b031608030304151d0115150c020d050a0b0a021c020313030f02120408030306030609 59
    0x14140021030b6030015807070030300118051030703580c40148118101c00c05070f10100d810242c4117001c00c2c03801036401021503090442c40403c442148c1d60b103091034402c840e080e1080103642c9444807140b038083c10f1142c4804c502030012100443d104002c7d201d0748042408080c15111032007520303100810550101a13070001c1c404891030704250404842040c1c030001d00c09003003003e22042c08044100c070781269120101002c01c600b1103c0b00300152026007a802070400005003004c1d084003064100c10281132100891119080d02c0d51441103001e10a11042c00c00a00fa0750300c10001800c01e00e11010a140c040c50803a081d910155131405030841c02200c1c60300e00c040e0041b07140d000c41c0000307072100c3c2c0903251554010740c15440d00620503441060f85078000740400c410f916881000f9402403040d01400a400100c2d107684503240d1840646da40d000743c070041e010b07204850014120f46000b01c0c840c010400c0c0548 = true := by decide +kernel

theorem cover : BRFrame.Cov 692625899 692805755 := by
  have h0 := BRFrame.cov_init 692625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 692625899 ≤ n) (h2 : n < 692805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
