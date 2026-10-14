-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3775
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:38:18.239712+00:00
-- url     : https://prove2.me/submissions/9d796085-55cb-4450-a2d8-965f2afb0a26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 678776978 ≤ n < 678956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 678778228 1250 678776978 678776981
    0x1f1802070c14040e060907030f05120408030a0807050a090311120607050c250b0a09030605160e030105040510150509040501050403090e061c03030e0d050d230411060409 74
    0x2020b003425040c1480c000030b02000200c800030f0310044020f400031400c01104840208913001925840000902180850b041c0541382c206c040101901501c00003401043d010381c00005005809240c2e513441d503203a655100c1c00c9500703001e0100e205001c40d803410810300c00116811403020340e040c070240c00816190491500d05103409002c0c1d03104400310701e00007003515100006100c4407401d010000d500e0302c80e4410040c000d001c415454424650740780f0020541c002c1007449080c00d84000d42d0842014843e034280020802c01c0d00c643c0d01c0ea0b01d80440e1881c21000514181801403902c90340d0800d019001c80701400d088034024000d03880000005102601021480f13940b9442c00d140900d018400020b020b00e41482c001d4625805500002a0002d040c01009203968509140d80326509403071940381f00340d8215103015030140a04034194103560041c2d00c011055503500601400c08081d5952081c00900311104420a07440c01c400c26808070341000400203404122548000840c0003009054640b5142d600c02c244c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 678779478 1250 678778228 678778253
    0x330a051c0605030c060f0307110a05012a02010c2a02090906040618050c0613050409030809010c090e043302040510030e0a03080601020c10020f01051f180207 69
    0x100c6107030744020500c0341d030504015030140c10405482040c60450301000340582404001e20ba002000301c0760007186d03000f88003445001d2415078401c0081c000d01c541d01c050721601611210621710038031404054016404d2050203508840411512a84020100781c1004000300300c0b000d0400901050001146005890b101400b0344142c002d50b029290302d0505142c1034041e0f03101d907614a02c600017074118242c04541c0105419a41030740c02c4505031303998010101140324119040d0320280c2e10038500000c86003410380010110388603c0500c4000c01501e6082e44007a5010501c902601c074450b0022000a8001000d50240b04d94918648040103c05800c1074040c900d0b65400c0d1103200141c2e078011400300704030b08024103040540c14031070400780201c1030900c07103080e41d0301038207540034040100c07140128070f40f80d000344480a6482400361011041056100000c0c0d075507034031030120342c1c1903620b4240010310310300d0400c0722400070042c1025492805490842e8a400d22520380c980180201c0c1d08109a9001600c03405450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 678780728 1250 678779478 678779527
    0x40c0905130e0d0203090105190903080d02030708060625150c02160527250f111b0603090712060b0310060b090613180b330a05 56
    0x12502c1c0650740041420314903103000000545d03205010701c84a0303a07001400d0314600710340d883c0400c40711700e034030072080307903802c16950010f0a0840d0004145100500d1a0000d40c429406501c2d500712503154001480b000d0321900c2d01c43e00018165110400c0d92a03940b82109030854000d05148070b000d400c5150f440c0c1151400c118050240e07010a81c03800a125000340e1038001041c08032160100901708414410700510700300d80308070030795202600007501070440d00b80c69074410030b06800315950308540242c00751106a000700013034049014554080301a400000360b0401c00681d4500351000d0741c4140701880041d40000d044640c0d2070103001404100d00808501001c2440c3c0260700208540f00c0d107170281b505207070450141d40c1c01c0c50305000781444403040c2d13142240d00c50701d030640d60305a81e035207513620501036500d003038001241c02185404803001402940d04022021001268504c80340c184150310306141c181c510b0110140d522240030401d45103a5040003034a0040e1141c01c249140011006d83c0e82d40300745402050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 678781978 1250 678780728 678780731
    0x1e030c0316050307090e1f021c02040f140a0e180a03021014090a173609070e060729013002040903030207023a11040c090513 55
    0x1003102c1c2c07604126100041c504d038030040010305c8200200d20380f04c0058405d80c50807214440070014900c00c0b16411100f41060b0055503895140d080c0034003101a5006224854100300b41d50b0011520341244031380c1c0614100020700240a00d0702c1c0030702d0940c41d86002005083c0c80e054030a04000b6000c414001e80551038400d5020f070004401034455441107410074176840100d0324180040200c40c030740015500314001c3e00f028041c20501c1071802010194400c00700c0400031840281c5600f8110b500d40642c8070011903910401c04aa550f0000900c080318204590380c01c0080c1080740c0786030160420400500b4030740e00642d8000400c1608032058181c551203084200d5400d41d5441c01000354403c0704292141c8100c0103a440000780920302011001e1450b41c0001030b00c1a640c803c4c94004050081e0304030303115158045c07c404041a010310901001c200440c0e0500007020f00a00c00c0e11441c8508a54600c116034007a900040c48048081400020300c545050102417040684011403180e554595070135040e90403510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 678783228 1250 678781978 678782023
    0x1c090b0403030915050c0a02090603010e030c1b090c030c090303040906060c060c0906020c0103020f0d09121e0507152a18030309152606030613021e030c03 68
    0x10390303000c0300b04011a404100700301441b00190f990004a5810042a011903130300300b1644070507002a005051003400018140700000d40c0c2c84901c0008103111222225010380b00a03000803031014080160021240c0358421141000080d4618140c80040c1044240140c202d904140e102c508100c100d9000307400040c00300d07801703000200801201d40101c182c544510310308142c48602c4c00b40061b603524003208045041c581c0104524200b8540d641c1941d550284440081c07103902e86030704011080444c04100140021007a018050b891080d06800b400460340c5640c441c4d1400c4600c0c0c0340c1d5000c2c1c0c40b410070f410948035104c2c5401540101100b00c42d2007283c83d900b2004079555088070000d004000300501001c41c01906850800200b600b02d415901250725155610000300548401121510f14007294010300082104080d4020700803505450300c1254250102d8040740c43c0c0310f40c03103180c035005540c0081d030212248240d0084c010b1004084000e00038045d007100c020100b548006414031000803204036041c001c400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 678784478 1250 678783228 678783239
    0x70f17030415090816050109060c051201060206060102030304030c0311160f050a0e04031107120c03110103020c10020c0a08190306050108070f031e02190807111c090b04030309 77
    0x104070364601608942c2080804055074031101039009950100c0594040810684103000d002e40100e2900b0742e01602c00c11084964000140058002080c052400c88000f400460715600000d50b050007060141c0003181159a9030360104c1c1c01440740c01040302040403460b000303405804200407811170171884491101286082001c5503203d40f20540c0002d20660483c0800c011610b000740c0001d81064151601c4c0c404039071003520741807500350300d9405000725941030040107003441011a049015644104900011060503000460a03030080d00301d403a420390042c042008820460f07a0060103aa04100c1c2920b00e031502d640c0304d001e09600981001d119901d21008205c8510394180310310320160000b4200400304d400c0c1128010030800c01101041c040c150340e03c0c10110040e00117500c0c400c1584501c2c42c155920100e00000c0d01138890f581c100500420700490119580c00e000d1510640b40e04e0500c0b0050104800d048503542c400c80c2070349500418403c10070300c00301d01c4002a1005002441c0262103d120492418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 678785728 1250 678784478 678784493
    0x31509050c0a0308040b0c120309010f051302010e040f0b060a030b030601060201090308040b041716172d0c01060b0a0212040518190e0c090c1905070f170304 69
    0x110a241d1085848a50610014101205550a6036403c4410541f03815248100360700d440700c00700406900c1003010040219520054014074110b80440f0300500c40c9445003d400e60b003001e200400240410442c000b030a41a0806500c00101f500b800301c0b0114504ca000c2002c1043e9611202c0002c00080e2500710b03603011800e040000c3c0e0b0040400c0c2c4001c100e100c016441c018600c01c005440103018101060204080c06180c11410071420b004041d221b0303444c5800b400f00c0c84141400d600840381c0c03589027440b0301c2c0a0b1111505440034810100c0c460300407005c07140c50780c01c0101d0084500100001f01808042c201d04000d1041d00007030800b01c42a10365548141070040e14140c014005c81b000380d14100018091758580400e1502105070300d2040009544410607590907198080880fa10f080e45050030741e200010300010003011101045c2c8904000f0748032078140d000d0500c1016030460b6504800724040482030311034001808042c3c0244000300b0400d80c5035a40f805207540203003d06001c40340100c2804180200d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 678786978 1250 678785728 678785743
    0x120309120c060509030f04050d0c0503060c04030b060909060a0c03110c031b21090d021201050109140f040308040309090c050a030e010b01020a15091401061410081f03150905 76
    0xa6400460504881d11b415800d58891401414003035511f05080c0700412096500c013101428000b01a9083c030700d041c01c00b00e4a203411520041c3c0d810710150011520320b0806e0003101d8040c0b020b1201410041e03655140403005040409007107000c241c0d940d112810005410000f034400c0040711760113103a83c0c401d070058071841c03409041c59041d055040703940c011a4400c0041030b22103058040722101030711a00e00d072000448a14111801a4206482503584110890194080c6050364499042040840d5028460303451003a400c44030340d06c04558803c041401301e03010341d400c40c0d1300c203200e8604130a410361030799541c06c15944091020000706802150351800103406000f0f5200300c0c0b8404000f008001034541c0000e41e00c3d00b0350000685903070100d80310701507040c0380c41c1c0010781515080401740c1e284406030300341203000f420548121461f210711104203100ca450052000303031110107943d0341c0c0103094a45941d500b206a005d0280d01c070b00c40400150000000d06049500840300d007140100040c403491500b03206041240c13 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 678788228 1250 678786978 678786991
    0xa05011806031e023c0a2a05010c11010b1c050703150917091305070306090e03030a051806042406030f0b0a02030c1e040e0123040c050403120309120c0605 68
    0x80e0350058580c818a21419508a19001e1515100c009000900c01c00381e01e0640713850042c1c1f90403024841d000c0c048150050b888100389a074888010300040a0103a007290904a1040d51002003e8081c110305074403040e8004600780500f040c3c2e1f5140313a4070754400b00c00f4062081407a8105032100c5e040f0b002c1c07040060880c0d4218400c0c8400900c0c0c401c04100141f0741ea8601f1802c010066500e1001c20000d501ca40e01c485c01400f400003040250103404203906036250400c0380d1903d10035051a00044102c42d035942003c201c6c000f590014070b840d8a5a07520030000c0c140141c4a20f003542172902401030480414051000154020000c0002540060421604c0100020000450540104188107100904400315565550031281c4040c001c0d80101c1081c0345403081e42c0c4131014005000001007501c2420120070254040c00c00601100b4040800078442a113540c1c03148a80412400d12040020980480c008900584140b40005003211240d0b101c22881d200c0406140c0040c2943c6511030030030105104840d080350 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 678789478 1250 678788228 678788317
    0x50f091002040e06010302131e32090a09080417010515010f0f0c050a060204151409010507021804050318090f01150908010513020a05011806031e02 65
    0x500f04030030002040703006000c0a0402d40d0004a4642d03501c03403501d014000d841070040d400440454890010f400e64160b0003548030710400d004600d80164910860300070401041120b18085070500c00400840a000421000e01c0d00d40350140c00700010302880080c4068440200201d04003103610f0031141c02c440004001403ea114610007083c02aa084608240011351519190050825040b030841d140c00b0000c00c000c0540c07103584507d01c108005c0d50040d00c20f98a279080c8034010030714051801c845200d40c0c8081e106580c0e42c10003503c051343d4481e500401d02c0030300242c11302c1a41807040c3e10a030080c102c12181a501c0340c00100340740f0014400f40c51040302401040b9524030507400c1041e20411a10410712070f10b8000c2d0800d01c0000903441c0907522410003800c862008221518215010340451484900c049102d0100d0030f1012070710b580107903800c00c3c1c00804040108605030030240160010b0491013011070398440801482500ca81a900082080d00649003400c0c904a4040c11203000d66040c1440c030b6111003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 678790728 1250 678789478 678789487
    0xf0408071a030615030705040e131103061603200d0504030f0c0c15030e030a0206010f0b030106050306090604110f130b120f04081303031e08070f1110050f091002 71
    0x260748503031030b138007140d203900c41160740d00c3c1c60740541902c181c41107901c82d6080c06681c1c001c1100420402c10080409801800c040703005252240826031920000c41d2080b15880c1c040b40c99507441d900c0b0781d011000b4007144035000300c40b658031884010410341140a440043e1900c0d07008000405500000c80581f03440c050070071801041c1030355131700115141540501d105010041e91034040c45482070700400780702d50813901501e54481c07070198025111802406024051203e00b200000c5803112081101d04840d000ea90307175800c0d40c42d80300030810004000b400c419441a15500c0c0c0040420a0b07100030003480c0000c01c001daa80c4c494040c0d0703d095841060384041d42c0d111007130240520120880441c0c5500c100016165001507888d071030030350024080c80101c1c4100e52501b0030080101031b003018a1010200300e100d690b01c0424440c81040f9800b60f0220b80359000540c0e0034840c500800c3c0500304181e10703030041e00150350400403003416603c100e86040b030301154100b4144040c000c0110062080800440840509600d807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 678791978 1250 678790728 678790741
    0x90b0406150b0f1c02040e090708010b060f071e02131415010203070318030803010603090302010e1b12070305030a0309021309050a0201050309101a0f03010b240f0408071a03 76
    0x66001e0180300100e0039813a44010400100f555048a0141c08000e2842c1220b0a0070345d0180c1e03554039140514141980703000e0708a19140f4000f001e45071002200c200051820a4a60f12000c46440c22000c4454200d40b0701d0903200180c2d5959185a1801d100f040001481d0303841109030f035540203024150306d50000807654108000d0740c0c0403040350b0000d80c260400440c540c0c1001550503119400e80e01c00341c210034000c40082840e5901d03030480610a80a58024040e641a0b460398907141d90b4550888030045500111000701801e24842c0002c0122004080c1d601182d03607a00c0d81f904603400007040c0e90010f0f54407106042103182c04041c0031070002000004228550040d030354143da540c00200041d0602074080009002c000080022012541003100240320800200311980720010059403c103210340002c811009650505100e0780d2002280100b58400d1182c40d501034061300d10510b05124201e541c00c0202c042c06c6603202c40144002e1000100811a0300c1c6010a10361041285519000c046001081800300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 678793228 1250 678791978 678792007
    0x2010b12030409181b030c091e05090a0c090501060f2115080d2111030408090f100807090603020307021f0605030a03120608060402090a0f090b0406150b 67
    0x6507040c9410004d000304004101d03900c6664042c0000340304c0e170b40b00030b05011500c55681c0c0304000c4912560810100035141c1501d082554804e038003004107050400b00c500000c22907a080540c100d0054402e507160003415480d0466031845d26040440d800c3e464500400082c0d90208014031441c07017614209424110000340402041c460b21501058280ca42082c6064403030f032004104000c1449404482c00c5042c101c101038007a070300c0c41240c00145408212901010422742c021381c0b600c2e80700c0c43c400d2407035580c5641d0b4a401a801c5041c01581082c0c1411440382d403600c0e041445d0200700a55107c0d03035602e14210038000c0112166030403100801d4014018407086a400246030154608800c41442c181c0d5020b1680b00014a1240d000c903616200c0e0100020505401080702080407103003a40c00c0c0050341d02d5052482d61140140d174000c0d0045100710000b28a400076600004002d003010001045070507140d00c40310080601503c00750742841da141108140340e959400588000d20b100300c1ca490404a5030340300b115 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 678794478 1250 678793228 678793237
    0x642120a1a0f150f1e01230904051909150c0302041202060a031b180f03050c01200607080603370c05060403030c1509080405210d030b0102010b1203 65
    0x514540d541c07034100c80700c0d035518940140306030750217051031001c080704200b10401c00014102150108000f0045142e40070700c070f60360461030300c00800407076894804000184002004d004040c44106213070008240c0017100f0030b01030207152074024009000101d590840b19011105084120410b140c4104000c211b01c3c00200300d01502070342c04561568452000f02007e501900c0200e43d60442c044003408550035081e00704201c01c6101440c501248202510781c0c2034110480c600c0d00029000e80d01c000100145076100b00c44060102c4012580c0d03403000c0b031a03800118a03045096032200046170200040181c41d040c2049031407442100e07851002c116030913820010702d102500c0340282c0716034802c064040e014080304100c100c0003054080c00c440c0e81c45a49003070090403902c201c0c008940300d0400c004009121019402031802d00340d080b01d0814075013481d100030081401103444c03824003a015283e00440c83c0c80e00c00d110026020400b5280031418507840b000080c2140c1d42c201c1414860b201c10b4054828410000042d40e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 678795728 1250 678794478 678794491
    0x3072c09070311130501081b0301090b0c030c210109110a0e0f0a080f070f081f0c0e04050a0e0c010f020c04050417070c06020642120a1a0f 61
    0x183d80001c4000201e42c001851001541007581450700000e00359500284030803085400c9290b40d01d55081c000c0800d400e0700c0e0040005410300840e4000702e40c0b841e440b0b00065030483c603a840c40916001800e04101c0c400115510110760304441000100415a03040c003800c41e1a98905201900d08150f01001501c8841090b070380c02e00903a04c0b505000c9198546034444405070400380c0440718940310b005095540c55415008a05e021480740c6000030700c01e02e000901c2c00384646481900340307485511046c024020851601210b0421000f418800e20707030b80f030310700c03500d805252110400b2400c10102028185455200252541040210f00c0241895503002c00c611a041e40101e0b400305440e29542012031409200a0f141042c0c0c0a0001e003000030810103101e40f1007210a070b40c00f0f94901ea503583c0c440b48411031030101d015075600715044c0c0c1350300c04030058094050950807080c45518104808004900c0380500404a200d055010700005010300282e28100488161401d041242624042d41159079066000e000d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 678796978 1250 678795728 678795743
    0x605070b060105040f0305010509010e0d1d04021b010902040b010e06040303030f0908030c071203050f1305120301080106090b041112150301020a030b040c0908032703072c090703 78
    0x101d03003103a20880484000700a0005030495080d04e034105680200350030796904070b83e58a802500408010003145100600500b5140c0402c9a40720f5001c1c14804c010429955a000da0b003003040041c51408209180c454a400800000f401c5100348148001c840d12607a1503814001018201c01300c542d14041143d050300d9243c5000b045191a611116015040d18940105913040110402c03095034180700140a0140c021701c4001100d1030344100590841d0720548200712201450380000751400301c4110300d50080d0348070360210b40140c0002e08000c89683c0003078016500594580d04104580f1010303004104680740e0460381040050072100201040f4420f4400151400b480310001442c8400c14410704904100050003d640c0c403131b00c0c110000e005002c60308000c1e00c16460400b8106120703205104002c1a0f800c0c80008500c1c2c181054480c80d603009801c4d02c42c41030b02c40010a0720b01c940d1024403554005003054520403090303074480118150075014200340c000700201c0f54002c108801c0c400087e50002c60b5005480d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 678798228 1250 678796978 678796981
    0xb01023009060403080a020c0112060e010e04050a020a1404110310090c050d0c031d0307050a0b180a050f06090f0a150f090f020306090109020108010905151008011505040605070b 78
    0x1c02c182d0b000d15403000d0084080803d80345000d64020075021074080c2c00744da80d10005501c9241840c1210024002d440c07011811740010f000c10307440c1030381a6810501407001c13524500742c207034000341910030309411100344a01c2c0101802918200341c058540c034407651910b11070445ca08a042074107801140c5c4a1444920b480e40780c007104640c020422592040303e084e100784003e014015018014040190b0801b010004941840c00d0703001c4040185c4010503446001382c98040c600d0748500c03c0007100500702496101c6103d04003100d5071300401c010790006110300041c00d420ba41103080b2071308211005051492642003905040018400810407620f00c55001d81e0440e51001ca020610004108003d1500103a62070071815800b44044141c8001d2454403c601300d45035a5070300030740b96080c1c405e8074000a0100f1a000b005005400e01a00101d91068030703410030701c02d000181e000040c8046044501000030403a400c0c0144081c910607090001c600782e040c24600d242c1403402c980242544510716014100112110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 678799478 1250 678798228 678798247
    0x3190b04110a0e010801020a020c0105041d0a020f0403061a0901060203040603022101241b1e0605040c090b031207060c020a12120609051501080702150a0b010230 71
    0x2c1404014100c01c4103200780960f111003a1038001c0d070280c0807030000b5100b05180841d2940c4240c085a0580b9104201170410440002d080c0581d0b42011384101c8200e03800380008580300700c05002600055005882c0442c0147c10800036912402c1900c0d2014082d21907500103000391a0000100d0f0200c5416240c01a83c07a113980950600740e6524051518002c41548000500c02c0c0304c94030511031b00c0e50741486200d4401b60307440c003e4440c000c0910410b880b0200380e10036071001c030b808284201805100c100702450b903400e480d5101c4044a40442d4100e820240c580028001c1404900c03400300d8581090300101403201034041900d141c0c0c0100d2400a040f80d4450080c0c00180f0310922086c68078a40c070002d00d480082040d080500403000c0740030b0000e000c034580b110010b803007010b5000b410302a42c141300c02d914211006200443e1100b030001c0001c4150b00c07401680003681e8101d102228891940050006554020352000904010f0074100156620399408420402800700031640d1000b5164000ea8992360803003071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 678800728 1250 678799478 678799489
    0xf03030f08180118031205010f090e031201121e020607060506031507020d121104350c0108071707030c0e0303030405070519080606010c1a100503190b0411 68
    0x2080b200501c0d5080050510894a1181d400058a44039486040b10754100300c00b1a4100c2d00244922030f60540c28100c100541109540848903801508007940d01d00f814150340720030b403100203074803001e92081d07140381c181d00f031004c003484c03603181395402d00e000240c0080d0540005100b03014552029203803554550100e00341b554100f1148442a0001e2400c124034541000e002e5100c100c0c041018022821203d1900101c119a224000c1038032003440792039007010b007000d42d410910107050200075803c90f880d0008500003091421000001c0310307420010101140044d000500b5106c01030400001d0194601001400d503504402d10750307201e103c80ca8000340d100725035071048805990318401280c1601000040c00f080c00000b0803c94140c03070094600b00c001e054030300c851b642c952a02d4401d00c02182c01210100f80315601c03500801c415075008180f0403120740f0003011601c58025003515801400c8420b04000c1000f03040611400e6000c0c84c5400514110455a4031008400880200000c18410702c40214014030f5542 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 678801978 1250 678800728 678800761
    0x306040f02160b2710020a050f0706060603060e01060804170f0a0c050c060a0507030e03030409020a0807030501061e0e2b0b0f0103110103021602030102030a0c08010f03030f08 77
    0x104090302c0d1003018240252981019500d608030703410400564030703600d2010b030314002c6500705802c02403440e400403d94440080d003240420008205080045e0b603d50914100580503141c011080001c0f02440c04002400311035003584030006801d1800010442d1a401070342d03469100c0d030000900e08558103d404214024803c6c90032000c41100c021034066007103580300188072900c070711803400c48400c0c1c00790204212050080c12c1060740012000c00650380084d1290f1442e119142d006400c590416868640c00020380c1c000941c0b40c0005030b540e4040103842076142c004d41b8010078850400c0010b41004200414140c0c0300d01020f5010700c402607055446644600c0450001c10b03d5100140303c40344044045400d00c4078008009540c80224080031400d42000700980e1810bc0383d016500707030396040d810030065029410000c00c0c0030342014076001c03201c05a2001c0c00154480d8140002c001140401ca28001c2c1a4040c1a0003059a040b142c1a0600c002900147c0c0030340c1110b01c90916103815a290400040918030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 678803228 1250 678801978 678801997
    0x5100b1b030414090c09060f0a0201150315150f05040b0a050d0506041406060f120a05060106022a0303030402010525050102030703050a090b060f0d08040b0c010c02030a02030306040f02 81
    0x10b40065040356001d00180000302c111030b41d81c800e840e81802c00c000d03801403066066004c281040100040403a0000400e4810081d00011807640b2040d0b080301c411190a034002d4030084e041502108003420f0342d200f82d1a440c0c55004580f11220f0070041c04900111035030040c5070040743e4411405200e070f601d03841c100d0002c0c0380007030001e17604186502d41252241c070180c1c0c0484a021030980324586010010910500c9114041c3c40e42d15062004e804201582c080812040680d020340003120000c1901031104501a14280d0010710064420300141e0001ca850107d1105140c0c504c0e14a0303c602e81d4003c02141e401a8091030020f8461090510b41001c0c281454000d50741801100440c0080180c190080c510030507540d1000c001d16a20614998180c8405420051080101d01c0000e0078501e09107601170300010015203803400c107d0b640d91b2140d02c04d50254201c4103099001044000c001c2d1400d0050101c2607403c0d101850820100213806596404003810451081e601d924100c10b44000550682d1801c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 678804478 1250 678803228 678803233
    0x1505181804020625110117010303080a110706020c0706020606060a0c0b0705130608070e010806130e190c050f030a050d05090112060e040318060f03090804050d0305120a05100b1b 78
    0x5804d80740100260150080d0300c0e000ca402d422103090ba0859000407641260741548802055640e04000d04000b460301d2409045040401d00c0b800000c60307024400781c6640c1350284010b00b4564100000a4580340b00100140d100b614100440403000381d100d613201c482160b0200041000f40c90b54841a9120b02841c0780e5540055102c81000a00c01d502c400d0340350180d030b010740340c2c0d800e103000f84401160401802c590064014a5250007607141a15540c04052480105010754204c2801801c050345610a0108165421440c420b4144000d00d0100d241da00c5000089004208801242e81c03115220306403500d80000380702001ca0408800e0740165610130400c00b92110070011103071030f09819500400c003600c003a000907910f2426044561114400e500548002e40c94100300072215200882c00f80c5001202118203440c20710000420352158080480c1c020b10a032900e90700c1c2c0b51100c10380d070f000c01e4008044408a83c20401406071000e01c9495078000d0f118030700ca41c140d60304402000d46251075207448a2001c85d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 678805728 1250 678804478 678804547
    0x60906010c1e08210f0c07030c051005130302070503030711120c060d0c020609010e12070305092e0201090b040b04260307090902040b0f1315051818040206 68
    0x700d13a1a00b07000c0180c601ca5282d04000e80721402626401c0f0403c8401c40702486040003800d02207400b400825410314811021107000d407250200d00f0301a5002500c4074503880d902d10454a04154050101101811b81a00103504060301520392184286103401050700232000e4400d200344000081c41904c404a03009000d80390b80f24031140d0303001c000745100c008030300050007003601040c01900c041c040c40000c0c0c10070200416906110455142031648440012020320604028035240c1d5241e03040001c02030f000582c41034100b45142000d403140c811010061800f164501310510300020304c104202500103410512030385003640c540c40c0000400008640a010400d04003102c50b46c2c0e10f40c01c0005603c00c079207555800380700565800c2c401c003d9001328081c4642200003445810b1901c01510080c03c0888200050000a0381e540c1004014107042540080700080c40081c245c08a0b015a180c6411820015612241000d014000c0561301e0500980001d00c1750b00c001030744207000310b11803490041c5a0401074070015032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 678806978 1250 678805728 678805747
    0x91121061509130c090e0106080111250b041101030b03011a15040e0109020a090b03100f150806220c05090307090e1903030f0906050a05060906010c1e08 67
    0x1200040007118031071001800000d0600001c0b00300c544007a42e00c0400500c100c1e0500c0d280c04081c10800c0500b211030f642e90040040c051009028224241182d00d038030350fa641150f031a92284c00c5101040e422465a0500080b000141c0110030319540590000d5840764161010130041300505100060145d040d1b0a100800b010750303c0502c9601c804031411035200e21f2080740700d0703007000242c0242d116280c08010701c2001044007030b449400600303450310789107405030466441d254a14039940090b5a0a0420902c9c94024000c1143c903000d510003500024402819078400010020190301000f80814021a442ea80b0008440172100074140c038480304080a000610080c10000c2044d0400d003115446031084000c000703801440d5200e061845d43c0040301412182d07100041a48103036000b50ac1c01c90403d95205a103200c000c0c0f8034400d850b06944030343ca000c5200d080200c09101505d2010300620300c90303810882403005503a0807007152452160b10002c05100030300d005c1021000320b00c07411f802a0103e0340c0090349401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 678808228 1250 678806978 678807001
    0x30906021c02120f060a1406390a0206040504020d0b0307080c010311040e07080403020a120915030e1027140708150c030c0d0f15050409112106 63
    0x1410003401e4640c1a0f40d41d02c81d07101d03040300c0400791754068000241c201c040c808003c581c1684011600c004d0705040c41d20305094440e1511101c04003040304400e61650244100080c5010100d1092480b100241400b00321a00090180e204034858035201c1d55001502180780d000b0394101c0110800c0003019182c21503550b04134191603074440161103002900e050790449800342c2c0c0800341c5040d18050701d03a4504c5c0e603540f102c06656050020b44143c080d4880c4100036800203640c50800483d5445560b901c0317004918249000b1085158809a10145401c20017000103020b000180c0405002c03c1580c00704810015400c1d10040c0480c3c00c00b034000c6498541014003e00400004e03e0049514003011100c4c056682c407401c940381c680300c602c1c0c074050799001404a030903203825030301450f00460660011403400210200c984105e441d08001618501c1d100d080242041c1004000f0310300401056505204005175545c80742e0664208441503441112040c6100c040003210b5202091140f83e07510843e441410012034002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 678809478 1250 678808228 678808237
    0xa140105100e040c050609031005131103010c1e09030501140f0108070b0d020306060919060f052a030405090109050a0f09081b0c0307120b01060306060906030906021c02 74
    0x200381e80509140012050100c0c0c41d000e10640c2c001d51446005402c02080040950207140c4081d810303c14508605075075a201c0c8615806214102d8150300d85c8e103920b140c845a6072031107802c0c0503c207901d404007403c60b19400c0281102583c04894002000c8800400d06491030f05684d000640a58a0700d4103a200000f500701d0b1050003038400300900325072a03a0f1402c0c3c09a86414501801c441d8400500200c501628141c02071038000d20020001810202c4081c0480d0001544081441040c4001c03a400c02501e50002d600c070400c1507061500d14a020301007000041c41c01e45026081c00d100304495000b50708641c2c02d100352400b0f8040202880c205503034444455010f402c094800ea54820300d02100c03110980c02074401e86450070b5000301550300301007088022048000155002001d94000c10142c2141c90380c040c4020002b4040503000c103c5000c0c41c9060481e41110140c00a03001d02d450400144401500400c3d408100c0b1520300d00807a00710700c20700d0500013a0003160754a10104010340c140d407050040380d40192 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 678810728 1250 678809478 678809491
    0x10204080c030a0210030507050702060703030504110609220e060910110702090c0d060b0301080313081209100908120c0f0c01140a2604020307060906050307110a140105 74
    0x84039401d00c203030100b6071580f104440096004075190441200719000c0e402041e403203402ca042283c10a051341d000304566500900e0200d000035641c60401c010454400f05201d04048140c0c2c80e642040d5220300442d401c0c14440b00c1c0a040b214170109014000b034184d4001c0e0326504000c4043d0785060829a5026039254104081c2c0c40c1040e081c940c15990301d5602c041590085d903001400e400541d101c001072040070380c1c00182130b840d409840d00c00c0802c1035222100214000c248000007590707034401403032044c000b04181c1d410441c0d0355000001401f40c0724442d08180d501c1e5a108440d0201c0000309032030151940c0d02c0a80c8a2010340c054104030756517021001000e03000011060081d1441c030046c407000180ca403c0e482007070601003407500d4004b130402000722019107000a0581400c0480005200c4ca6000b038954074081031015442d44410031086080c20b01400e0000e015a00740842e010f07040c01e101071300600008145804012020016188590b030070460444a40c0d0084ca0242e8001d00700e400c0300e0301904040303610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 678811978 1250 678810728 678810733
    0x20d0c0915080307030e1201150f0906080a0c1725170c1311130308041401050301061710050d0308010312052b0204180f0522060518010c0201020408 65
    0x7403a8078048204d0741c21980c5a42d60703110107808030040107a0030301c031440314020541d40c0d0654000c070400400c03501030140c850a83c0d2200c0440c580403204064400300d82225089402c81803c0c03100150b03201041c20166000e400515400e200541200e80c903040540142d119079010042000840603a80800c680c25200094150202e400c5002d1501c0d0360b07018000d61043d0001003503402c1c0e5082e0382c001da01089140480b5880b01c2e24001c04400710400c9002581c1042d5402c0341d00007010403100d01e084424280701c0c802820154115131404a01034044000d0608043c0002c00d0000020041342d010007102025000003007a101e0799454501340146409000d0000b21460b21505001d420300341e02850035034040f06414003011851807140d0b016181e4042c210798020840c15000c3c000829004400318001d10407030084080001d00341010034042054441c0900450340c50075650343d0b1300a003d030706c0c01d54883c14281c1111000c2110703290702083c03803021455070031648010f501c1c00410403e60740c4d06400410485220104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 678813228 1250 678811978 678812021
    0x621010b0304120e010c03141b0102041d0c03071b140109030839040e190f0506091303021c0e010212031e0a09080a0908011a030712020d0c09 62
    0x341980d50444d18481180031500305102e1400003445110a81d613100407070120103003015451030411f40c24840350f42594207a0b9401003011701026009401c415a500e510580500090405c0b119604081c40b000d82102c0400940c84940803141c5030388031100b2000c61b8080780b40039401041034002c0d80201038034482200045c1c01c8101051070301d00d44290270500300f00c0e00740300700543da2140c528284450219420240e0700c07880034000050745d4800c0ea4178061066800e10348801140801441143c1106c60071041c0141c418608403e200172900c40f07d188540c032146e000e0543c807080034141416880c0c03a01400ba4041200c0c03038101c8100c405580458494255032080c5c0850b01000000f1104c4216400220742c0004610848090700c0110202034440e203400c4000c0801c0052980c00f541c8988515511210741d010101d14480e0003000785000900c02d03080486883d102903000d1008440000b44c42d50391504c0742c40d004040302004101503540380510080000e40c00090ba005007641d0307200030b50140c100180450b078200312486 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 678814478 1250 678813228 678813263
    0x30818010209060426120f1b060412080709081906140103030921050c040b01180b0a080f07022505042a08130b0c09090f0a0b0f060301050621010b0304 66
    0x1407010080c00840c200941003d10030080071440d0b410a407140508123240010038103d019040c00f00d5806a401080100000c40360154003829440000d032542c810019030903c00c00c08000c0208043c0b40c080401e81d000220004030781001c4c0007601c0345400b104180c03c03018000104054004031207804541c8180c42d2241031180c16001e09544404421000d8016003006122411600c3c280d4010b0115030814100201100c6a1858100c2c1105282d0400c101868000456078202500030111039480741c2c400d8100146403514000082d21042214107200d80c032035100203003480e902c803d005140040c1070f010304200b180390018050b50540c09184c190200c0c2041503060a5011a8410156184920901000301d10420025a9285408500240322451a50080c0641c00c95070b964050900e0068010700c0b001002e9017444001c1d0400c0f02d0440100910580e100e02034120140c8441d0103890444408544003600d81e020340c00080c003a4072003110708140f811072020010a07650010340155004a0041f00491403070306040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 678815728 1250 678814478 678814483
    0x30e1f110c0303010306050406150e0601030f06060c032d05071205070b0121060203041b0b0910050c0304030f0506150604141c1203060819030818010209060426 70
    0x120511500c2e003082005001181c00d0340c02068000340301d6400010041c1c410301d01c14642040c207401980c0c2c5c2e1401c070001c0c407001d9a414001d0790f40141c0034a004000c0d07030f07150000180010084c001c0c010144064042034003000540c0d0582c3d902003c01251f40d101350100040001001548440390465070403c07000b0080305001e204034140c4030340c40c3c0c0c0400c0e5001982d081119507410340d5454051010ba40040171400e070000344540c0061405940702d0141d0003412900222800361841c2c468101c400b41907428082c6002c3c541e104024035030040c0d4039003000b580d586a108903a5065106640002e04000c10300d902000401c00700141043c4143c480d41c449000c20544c1104002c1c50b88100e2150b6641000003010300b001524140d5041041d00c80c0c7c0d030100421740e1713004e40d480c0c0905440b0801200d0210b80c1d942410442c500050046c050f04485458410030949410341d0094060310001d0640d1039414030903410141c1d01402581210b14052004103916151541d07488002c18003031003c0040700600110740c1c580705036840d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 678816978 1250 678815728 678815737
    0x30f07090f06200303010f06110a050a0804150c02100c1412130801020304150f0902040501080d11030705030a0804081b0102180613051309080c030403031403130b07030e1f11 76
    0x420031f8002d041d01e8404100c03a500104502d80c5520702840c2a0b280026404000d40002e0500c1070444a40311440c2054010700c550204c0746800910407c0e1080c82c0059a50560741003012002d410986c001140c241000100304400c40042d103a6481000410920000c41002910003500c04c030003aa5801e81c0c80d00d401ca400d1740016980144045080c095144211002e074006005003031300400c0000d14011103400003070540c0c00a034800742054000603041d1080c03960000340c10000030701c244000d40c5480d01c2d65965030703924480c5405400c08c2007080808207003004a5441100d414200c00407900812070f10120b251340c000c0d8402c035400c01c07510740d1046100320242400c2c3d0603103007441399901848008524040902c0002040c8061004c60540d40c2e03100310000401000150105500c006c2c02903845074107529018000c60420014204201414001c000d04a5041600013020f50b1b4003200c1000c1c1600c0c3e1480990240c82e511540000d18002c0d6450120003400c2c006c520f0940e2207032a4021b000e00c600903991820310b8840d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 678818228 1250 678816978 678816989
    0x703050a140606011b061e0203270c0a1503110c07050a0f0806071101020d02130f060905091302060d091113020a0504060c02120f15150105030f07090f0620030301 71
    0x40c9010041d0100d180c583c0210181142e80d005400003480c1041f100c0700b01c1e8811a080780300c184403104050300c3d42008043c9506c00643c0c0740001c001c440c00c00f10016a40552070301c140b80c1e00940d540001400d45110f40c01101e502082c01403910740700c440900901d5100c90300c031302600e400303840c0b40d410004d030122035840d400044403560000707050b8603103880c00f040f600c450302c051003040c0381c2d9005c100700c507440c21003840141034650740c1c5071408111038100300141502c0e24095018004000c5a12414081941c1d421412608107183c0c000001048441b84041303840380c0200c80c1840c02d03c602d40076914052000d21038058054410071500e00304109142c00c0100102c0c0503001d804e03000180184814801c0e44c4c00381c0d800104035800284540404004011018a4100b45800c41c640f00d401101c0305426504807406200e820100141f4200740030032445000806078040104030420241485000c59503c42c0280528801761500b01050080a500c0d21000703040142da09002401c0321140480b0341e801c00c1d80c0030007aa41a6403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 678819478 1250 678818228 678818267
    0x7140102161b1508130b16030b0324040f0b01170d030c051e0f040305010e1209130203130204060806011e030f0201140d020c07060906030e15090703050a14060601 71
    0x2070030150441d0813640060142d502100f82d8aa00808106c0c03082d98580f14200e040c100003070082480100034140c807401a1050300a91000c01649010030078442c60840d040d0705004008c01958440c2002800c0d58207c1c3c6000d80005072132000072402135080d07514041c901c00c10404403400b050304040c049080345d25002440b00001c40503c59101456190901c807800d840880400d181040058449014035a12683c002c44140c0c0d0b6942445080ba9410300445542111000303c0c1e07030030400403401040707071110000101c0ba0b0351680000002c1d200300113803600346010f5801602c1042540d48865180365581028010004038182400700d1040314007007060828141c9601c81204600e91446078015142c561000c00c9511904c3c1c014082840c1d080c01c94800340c0b240c6aa400001c0048500d41900985109402c0d0003450800d400d0441b5520300b4640002d4807084055004075001c1c150340e403000c503d8104069a04018013a001e1403065a05005070303101c08034641019002076034019103071900151190002170b0388904a50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 678820728 1250 678819478 678819509
    0x7020906180a0b040915230f07050310091a090117031c24051302030c090f062b0e010905060406090807300e0303070807140102161b 58
    0x1101650001c0903d1400500b0100d040c10751a560640403021002040da807059984450305e10801e16120794480d070050040c1c2d00d043c0d46c00c09420340403100c0d8005040d1414804004086080300105101b071400401c07034040208256032920580c2c1421800e03107010140700d042c0791000428400c03580d506414017003101030000c502c0c140056449280050188810507040c81e238a282050030440c402a810014034481c00001c558a41810200880b480e107510100c44014818820851704860785000c9581e101003c9403d00c00d98800c8800045581c030a001741040c0e101c084420501540742c0c2611800b074040903201d414000d0707113491080a4201c41d114032004d0410b80c41030000c02c002c00e15540c0801c01c458002e8441e9031620400ea15611024040991001900008030350000040d0903800e8a040e81c0c01d60b1840c241c0b4010390410000307540c038000c0c4c510141c4030b454009030303400400070090240043d0a2440d0025034940303004404607007090444800545045007451101490071203001c58140507540b442c441c0c0d8144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 678821978 1250 678820728 678820741
    0x507060201110702040b060409140708071b030c051f0b01021e150c04030503040b07030e030c01090b0a020102040806070801050a0603022704020c0601080616030e030a050309120705030702090618 85
    0x1034030306c82d80703c9a00300104020200300741e0894040d044504801201ca00e40e541071160b03008100100041000e000c100518001101c42803080c11038421345030305440c041600391940d00b000c074107088044010b80100c100c0d20703031101d542103220f4101ca001d00409800740d5103101c03201c01c8030b04001c1e580c107048002580c0000000c540450200e10417960860403c0c982241843d4990f0350f80d40c9103920540244841c07200100e9108100341e17103c42036409050b000d8001e81001c03200000080c05030140c50086603c10100030589014443c400d40c1542e0040800d501210201c1c10212405021103900b030040c540200cad580240402c0c001e0081c001c07540801c00480a8524400e13840300c504075a0110101d846038059002c0101c039200507000c1240ca0302034280b03a0b010300000e04296501301c0c2103c41e008444800d050030584292681c0c4000320903900824414117145d41d4954403000c40070305041781c030041e002203000d01203142c0040c404000b020340305241c803d4a5000c1607403900030801c5a0002120110010070b00d000001820 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 678823228 1250 678821978 678821981
    0xf140a0b09090d140f18280303030b0102030c030417060c030411060708190906110a030c1415010e07170f1303020c0402160b0c09060a1107120f050706020111070204 72
    0x3041380c9040c08905240d03401400580692212006804403403204080800074903000002c83c042180c0c40d103811301d81d44283c4000340e08006061101409143d6251680b1310564028070860740c0c243c0001e001c3c1d0303588a80350881850b01c0403034220700612520804000400e1000494101e1380601d030030500704420003001004101aa502c43c83c011110780c0010f01c100741d1440500700c030a2284003415200c2d040800c1c03e0000040c049181da0410b803546920140644020a400c04082030306a5048078050344400c0141c00300624042d039002c4e0b80101e0b48007000c00010349072041c0181c18050007891361800e0308800c0c1e0300c40c00c40005d50160703495a80020110b0200307c40d0b906420400040310f201c0d005484500d880e0500040072a040300352204412000380101008000d40601202d500c9121150144d0614041307001203810b9001d002d0b1520144018a2455075030503004004490050a038580b120308a21454503040c1c44400744040215040d1013900d0780412902d0040c041e007501150207196032070402e0460707000c110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 678824478 1250 678823228 678823247
    0xf010311031f0203061201060f180b100225302a0503010204060e152712150a0c030e010c020d020607080f04150f140a0b09090d 56
    0x80d814411011008038000c0340182c122a030300341150006840b80b4100043c0100d4645a446c03188150340341200910800d40801c50500946040c1c0031441840d5555064110060444108051380802c040320b10354003540c1d00084856180c08600098080000d030011842d0941445001d4114960682d8165914215020b03c610a0002c6030180b0b0030103100321507c41c0000707000082b40e1442140c0b001108080b1140c80502001c0041005a008604c0e1034988100240030305207040105200d44410300081c5441111801030b40e0100e912440e20420140d01a0080390301a0301c845038041c040c02d48078400c15801c61011880d01810942c8828070340c007660701c0c00710040003440f07080c49034418035965000701c03100d942c424804c510b408003241e0001c0c40b1141062078060700d041001418101006000810040305035070010040b50041e0344034100e003403d811054911000b9040c07110840010924004481001d4005d051900f4007903480050100a501805424071202050481e01e4020541c00126840e5640b0f22546102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 678825728 1250 678824478 678824513
    0x606070318060801060e06070b150111010e0601030201121404020609030709140a06081906112515060b07150b030709020403120e0f10121409070605030f0103 69
    0xaa03103811001c0500c01110400340c00031000107100400520699030401007140c4141800c0351001d00b0302c6030a944208007100c004004410f20216820000d000b40d00803001c0d502d0200c810002803004000011001382e4444091105900050940800240c081d43c24487d64201c00406074510b0720603174594080c0039840d80450441501846203040c00950081c0380d110300704e203020320401903c40032308040e00e0040540e011038003e03441d10340203483d940e08031841100d201790007190702000100c2d40c200d58034100f070414003a4002070b201c1c03e02c41d4000c0d84a4000030003030000d040342c855140e0030400e00b114001001224064002e40c41b1210b010000039010440039440144401100e0001050100650001c1b83c1001e00b546d11266030f1603004507050003003026180b48201c0180b118980280002e40103030001e1201d00c5c2604400e80039201c004006950a03206d000752004002c42407400703006000d1132248008801400705c44084c101d0084042c0407440b42d1103801128060003001c01c0c1c90b030542c0d095482d400000114403151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 678826978 1250 678825728 678825737
    0xc1002090d1113020d0506030d08010806045c0a0306090615030308040c1e0501030c02070504180309140a1719031d100801150507050106080f1b0906060703 68
    0x110400c50f034043c0010009000c112101140608100c0300b4507241c001400403800c240107030303400148010100068000d921a40040850b036000c0c82148803107500100c0402d80003020180951202a5440c2203031408420590001486640d422803104c1d540004c2e07507801c0b0301039000115200800204e11150070844c60305000c2c40c3d000a207109055008010030249a00032400f0680d40710030001404191000c140040201180340d480c4000301c800340c1a12041c10380102418190f07a0300642012038400c208204c003800b009081085054040079484204413a00780e0201c001400201000c2544a00300701540e1038690040d1000e540740313040811030141c103c0c2c943c40c00710507480f81858031b0300d41c8072404070b1070000c0500948500c580f00060010b90f00264206000300b6015880e507503801c11009030702240490444a8044d081621010180000c5803d441204005490366081450108080c0f001184650014003008200c80100d46420f5490251001d40781249600010480c006440f42c00d01c4001031a20701d220307180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 678828228 1250 678826978 678826999
    0xb0f240409080d0c020c01080c180904030201090c0b0912030c030409092108061302090f060c070f150306080a03020c04090609080c100b030f19020a0b0a050c1002090d11 74
    0x30f0705001c5404400c40719006a104d192201010350304034502d2604500110703102840c2282560080405400d80c900b41405044020005010706100f94854482d240d8000e045040c81d90f07450ba080202c640004210f03910030300c6203006408400c0c40020844400145020103142000c0c40c00070f4200040c8007501d01500c690140703020803c480c2105600d00404884240c0312038800d42810014002c1021900b0504d40400d44100040a065901c09c1c041e10002d113070031980c0c1a80d03504c1d901003041c1844182d603c140c03185400e8030008940c100e4003500d402c0014a965804105070f030ba4a0080658640d00742202801607000160103061504041d046000c84600442010a944007142c2d184d400c02d90121030f41e88001d8000b802040c4039510207001e80c410003001240140401941503550b5a11413240940f160740e038414100044046444141503070740200502d13690a51501d40480c80900750354002046507815001d800100d5011842074401d94150300d4000d04a417001c1146640e03849241c62442a100c1ea0000c5161b5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 678829478 1250 678828228 678828247
    0xe180a050f010204060e040203010b0d09080c01020403050a30501c090c05061315050a1205090f0d11070e01150807050f04030b0f24040908 61
    0xc0040001c29000000581e52458028024200c0209411592040703004000401c50f07000c0700c80a503104006001e000081002942c80c12041910074425114110350000c00d0010a2002c042480c502e1603000d44944503d00a00700010000782d110894a80400a50314031003d0705144180030141e00d082460400c0d28541d104041e8050205225168406c8031000351000c02c0f01c0315031981c070501c100403000f010080c14a0300c00c1d00924240c2c4212490801601e03519043c0704148a24140000005e08010300310b541da0b10102c0c1c3c9803903001c805501a00c5410f0100112002e83c0c0c42c8075000312070048415035642614414911241c4014100c0070345000528403600c041034020a07000d004820400404c0d4462244100d04100010704001c103580c0000c818159a20040050071601c0501c000c0901003860140f11a58802c01d09641902440c421400e240001040120810564140b42406240c07803101c441219910b081815030800b02420b200705101921000300c08640c18030350482407605106508107410280d034035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 678830728 1250 678829478 678829483
    0xa0c0602041a0a031505010806010c0c0302040903050304051605090f0a0b19060201060611031207180f0e0108030313060506030307170d24030f080f0703090306050903040e180a05 78
    0x39a110b400e80000503103003100325054070501481000d050740f400200d030301c2c01c40040c01c0783c00d00030061810712981c891100e040002c1080d4200180d40e00404c10885c81c1c0d064100202250400c840855031071107141004502d181400840743d0403501c00518815403543c580542417100d40014144020150300c0300c1d50348030035964540108403510030303040500706443d20300b220080c02e540040c0d00c95014005a51554110404048212103803201040782003021900c5161341118151500182045d00528181001c540300e00f81c0403162003200d0505840102c2e903600c4d08806612480161040c2d40708074201c01840c000580c00b90030030b680c04034009050fa81480400c4d11980f1010351041c0c414401075500241c0390343e000a00344284a6001c071240541103000564414026014800303000242c21540106145420003100d642141c0c0700c00884050148c80d03604a207005000d80440c0d0004480160900f030001d0000c9000006070703412201664400c0e8101c0c0c41e03035900719a000f918052010070074094107981c02c0c0450b004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 678831978 1250 678830728 678830759
    0x40828241a1f0801031b0f09060603060905060f0f03100e0105060a15020a0602090f040c020604050106050402031501120902060304050a12020a1a1005040f1e05010305030a0c060204 79
    0x1c400615011a2880800030910103101c0c0048440c02c06150418000d6448840c190559901c0741800340800341c201111904800380c0d610000405e41d030f9401c0072440b08410703002a0220b50b1039807400e001498907001d40e2400d0f610200c9610f900100b07003003159600761808088000e4241340c00750950780341007241e1214000380d83e144d000040c03d580d1200140301b514205980c400c1700400001b060510f1804507141c1c0252a5040e104d0040d0001e6004161645550f40d182a60303481107000178800c1011902c404806516002c003150180d4040d440c1440000b80c0e030815000700d910034107140b904444088500001919a191001d0007903440550700d406120060326000300460007140200c00412a6248038a4070004003403d03111007200315045200d0600004000c0440484024000b80c0082d203280e80da50004004406190b01c01c0d0382c8107052001003281c1890383d40c840e9a58448041d010214031030f4000441080e5002031000401c1680f0400102e81900d100d42079060b0250700c140005841d140e555180140740200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 678833228 1250 678831978 678832001
    0x60603020c37140709050403030509060421030207020a0b04031202010926190806011407020907050f040e090102030609070e1e0d1704082824 62
    0x90000d480314044508010311030302c1c01d2441c0d841101078900c203814121990180c50700441c000d004040745908002c404072040000c1c003801c5040360000b0703030342d84420303000380c00184d0303054010038503100201707002480c0440c2e8a072040341c004040303083d0b000d0910a420001c45000052104050703003071101d8001603031050005001000d040310307040d4640b4114100b8000c2680d1144224041d603240148540000e88074042c0003810400c00260140d80d180c000460490300e109202608082802c541110422160400c550500900f000e0b0b07580a440025a00322034940e1013140000781d40f11034141d001840c1c843c4148014480381c03044d010030034201551941400010b000a07103140740140d40100401c9903608000c00100e074041c1c047d181c42d912400c00d038004210360900584400c65140410012512251a1020000d1805600c2031070441120f49030b0b8060001c603040f5000302c508074010f640c811a42124158000100310041c02d0284007a40201d5642c02c2c145901c100300d03041041025040040da00c039003445900c00c84030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 678834478 1250 678833228 678833231
    0xf0203010821120a020a0c080c0d18061e03020408030f09091506030a0b150d06080c0415150219030804261204050a0609030f03060f14040b0112060603 66
    0x10403102d1000400200c0042015070080240b14540c54074011101d2140c00c000255001603540700108000c0701e9046c0221800740584200040030a4604000034460038008a580d03100b001188145800400e442c5a51041c48001100440c0d000820381403400d4903101486135041c0180781c603550b610300c541150404492043c0c48075000c0303117104442c104035642d684d00c10380781c019031100c201ba0310000030311070301000c1c02c9454810744e142c50410709174503002c8046440c0410034503659143c0803210517000c00740456015070300880c0260065070b5058103040c0149059092000314080c1c002e42405c48c42c8440050a030005404c510840d03c001141c0c09079921003200c480d0081d515080c10346441d0070300c072207402400703040c2c00f0182c0041840f034004c2c060000c0a542491120f010100d144d0f84803401c00c02d1400822900292504d40303000440c00c209900b05986100014694601340300d050303038400d680500703501d0900c26200340c445c1e124107820a03460154031110610105040031040b1030f8040c01c8460499031107401a4000c0ba = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 678835728 1250 678834478 678834493
    0x10209030a140f2b03061208030a0605040e33041b03170d15081f0e060a05061c0c03080a121508011404080a03110c2434030f02030108 59
    0x7070001300b1401100030388506061041602c0c1500580c0050041c0201412840000c404240004100c0e040300b001404014420300c20110303180c1076584c903407241080c803455100c0540d141e400045440e414103030041524101002559031aa221905040d60035000c480c00c0980c040c0d80480018403071500700e44000d490300c10440e1030381480c22188003204d0710016a080c0040e100007080218a81c00a0b030f0f034451080244285454814203a540380140c108201c105100c0d000314410001414410b0744514844c84044800c4000359010780e0600740c06158111010741880e0000c3c1052000c510354400504018495280c88122045012041c800f200c4000d40d03103400700c28a0103010071202400340907001ea07580c2e12010b01400781c00c0c40d82c1e5400c450f11403002d0403010705132250310034006503901a003984c1e81103803910103541e2410180102e20403d84000001c203100c4070420306c082070641f0740031041e40300e10480d04800d409000c00d06c0601c000750107140051103402c06848101d013090080c40c0c0d00145001707080000c0280042c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 678836978 1250 678835728 678835783
    0x20604121403070c031202030c120903011d10051311040203060d05011814070b0306131d03030f0c03010e04030e19080703021008090709091a0c030406060602010209030a140f 76
    0x1060806e40802194003e001c001c8102c040864080c044901e0700300c1d41a0351340100b00102c1d024003150714228201c8404075441c0c251003440810410050405070000300050340c0c0303209505034418032500f40030f8041a000c4a102256080c00d90065400c40f0303009108070224280f1760764080c00d440000c204985002000000c0c502080f460020300c6040103200009017172141c0c10a820f5442c0c5010050a80c0d110b9800d0107200f10210105034070180344610040b80208502e00d80900300c5580b40c0c4180d42100340541d2000c00a02c13852030800540e4141c0f00101e548441d03948030b03a10129465052075014a9000c512405484090381e032001c1c0020045c02600301400080b40f66004201000074084114814413440c0400c208c1002c002058074010740d0300000300041c000305c070750511240d4040c46542c1c1d01940b402c58014810b046044a000e1031003180326140900c403072911405c08030f003070b40200300b251a056270081401000003030302c1189510041e80302004075041d140d01c2c1d6584500d03203500ba100484490005c55203020a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 678838228 1250 678836978 678836993
    0xf2a08070c0b0a02150c040b03012405131401090521010e0609070512010e1204080d0207151d10201903270f080705010c020604121403070c03 62
    0xc041c2ca40b01141088001400a5110300c01c21540c0c0156904040c00242c1207400c0704103070f4001d00744800c162a241c2da1202450f40d103c1252354401e101000100401010403441a0121980c4a04480040da0304901e04612070440071080590b00341445042e05020680f512801200e0001c42d2070a210700c06002c0b0503280540c211242650321004a4205400300844401c0000d0b6020484c1e50640365141c402c5070300c4251500405044900b86c1c00340c010b42d509076180840d0a000780c410355456500352070046400303440507a0b80f45060703c01c40c40c0d03075000c0c0f0308065840e1780520309814500405110326002d80d0500d40c0007565a0142c0c0d0b15980c0800d24032210300c0c400c6816031018a2052042c0c00c018103e00c42c603810705442512007140b0007000c100900c2c0325001c02c0200124034030301d540f04e0002102402510f8050b030a114103450301641d480c0d4071502c2400a203a40c481e426401c000754020b03003d03c0c83c0038107144641d0f04843d0007407029108484101c44d10560707000100000c00c9000d011304500b140007400c5140088 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 678839478 1250 678838228 678838253
    0x101211130f240b3001150f021c050a050409050c0d05010e010b0d0506120f150709051509040b06030c07061104030b0604240b031801020a0f2a0807 64
    0x20040ba6503070000e0041c035204000700c035101c0c54840e80d80705000107220b00a1308900f804440d01188246258000101d035001c1c01007440c0d9110150721451030754040588101e83e1940c04030401009002000300b0f038140140500010310800d41107142080c50305442d80700c02030603a4415a6070300e590641c00905509122124814513003d80030081d11003034954904203e5156078010f1307980c071071744217652680402d64a540b1400c4030308140c0040ca0a484211840c050400e0300c83e8400500340080718014000103a25a102d5640941694001000e40f6071303800200c00441a15041008002d410907906d04400801d50b40d40c3c00030350f01c280c030101c0c05940d460f5058540902038414251a8030140c000611007800010440c107101d03a84900251000201e1070420b84a940400c04010341c03100d01c10a1400d80401c49408500c011441200d92a03004031520080a40341c070f00300e1150340b507482c0015401403100c20000c0c0c820203140c0c0341c500c2c80759004141e4000701d0f058003140c41d02c606400c43c0c1c06200003500d40200844084200f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 678840728 1250 678839478 678839531
    0x1507020a020102060f13021c0302010b030705100503091006080303180c101b060e1b030c0d020d050c0312070311060403050d090804030b13020306101211130f 69
    0x514215400c0e40c000f079a40c440c00740c03405a10102034030018000740018040c1c01c80090300100f4407042c070400c00010800d014900442070300154200b40113013045040c001600c1c01101e0000c1c0210201019442c403c0301c00b0b800c0a01700a9241c080d1284c070032071302d044900803000604104000f840d84e030b04081d494018a054458045185a000044c90451550714078803645034102d4941000703148000422625901501c141c1d20041460b850301220902140001a143c9900741c1e4212901c00b40d0a61402050b69424580c40a690b0010040c0d20003c0142040001000d2540c070071011640c8084031070b00007a017403070000441c00fa44160040b41e6801416888498007550348000000341c0b40380e0800f83c0703000b4514422000c2d2000b540b07440319a07031820043c01a04481c029500203e90010700d050003114000d803008603000aa1081c070030b500c0401c0c07460302001d41d0310741110f07110a070900c1c0100d00c1d99900b41c40100f0b01e000041c2c0c04400700c11001c4104896000c2c540080600e00400500701e000c00c003060803a01c10300c0100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 678841978 1250 678840728 678840733
    0x50111010501032402070c0303091706061c0311061302040c030507080c0f0c100515030f0303150f0603070801150318060f02040506130302150c0a12140705150702 71
    0x1040801e2102d601034100480d640000322682c00c001302144c01a11030004002c00900316441d0000606902a1a00043d28005d1400c04112841d0441041d640e510a48215510400056078200205070741140311100d00e1190070041c880d2441d41007003d082110480e541072003d00644100740440c40c19101d80c928001c0c0038141007005040c00a801070131400028918800184001004106421008142c1d085c5220800032500e11020220740c00c1e0180c00c00b900c00408515080380140b4103843c0124002c008000c000c0019030465072501d01072204000c3c51b8601d0364010304003010030003080c0c44400c003c610844403a11400b8055242100e096150400141a1820103107080314100000c00d000c0d44098030182c010401099007035008010304002e10803584a19409440002c100b8011484242000201d07402100c2002003074400e120920714512071101d11032459044104110b00103803d07445800e12401d02c2e80b602403002c0407500425840c550014205a6113984503180000c0f6907241d0504103a4009480d101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 678843228 1250 678841978 678841981
    0x20418020a081801020f0d0b0301061202060d150e01080a020f031c05071104020c0f1605010813111002030c12040501090315091e02030c040905030405370501110105 72
    0x1482c10501030800c01d11003080350b0329519003010940640320159001e044244d521a0740d80c21a40080002c81c0714503002e0350034541c00280d01021803207204682500940b140d841c00c407514040b900104a41001800420000f90011400c400c0c8040000c0c0608810720081071085050700412400c201c0da100c1142c801d9100f440c5081010703000383d00e07a62480d070203420700944a4816140c007418294503050029081440890100c030301200005004400b000d0407016108004000115180700002500032580400c4080000c0307026085c2090700480c010340148042c244034990480001d034560391041310000141c1c00815040a15013091003200c0c103010b0140a0320745040e1a000020b0100350b180d01c40a00712010368192000a904660002d03507031240d00c080607400d0041c4a115289140d00341d55401d900070300c100c030000c0c0e005041910500c202960400c00031810189850200040240a410780880314009091282c1580310300141141c0c00d078400201d83c482071401c3c40001480400100048a42a0b04000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 678844478 1250 678843228 678843247
    0x20706091a06150d0b0109030b040506010e090c0d02060c010b03250501091d04031107060201050f0108030a090306110f03010e1e041e020a05100306050109050301060b030f060d0b090102041802 84
    0x40710044100c2c00c4c0049501000e001c0140d0b4940543d60018084ea04801c0400c4100300010a0107416030300d200100c050035440f4400b03a9560b40d9180e0b8103062f0030910150b0960054900b26000d82882c9070440004111003e2032000300e030070f015030000120b0350714401f18050205003034000141d0025007030a10f441654945804140e00d0003002280300360091502d8400401c060605c15114550244100021070f10000d9503600001d0090000700c410b0000007010900108403485c004c000c4864902c0f49586405050f030860302c48100424203101003184035003040051040700580c0781c0196000b82a040c20030001854920200c001c805c641040c07202d84501d1140c00c0000040e05100b105810b80000340510311300d01c00d0751000c225080003e40019034064100005c0c0101d15905170072100c1503505c02c0c0c0e00d108201c1e070303144207150a07145103008003c4440700c103100250340351005404196001c10010000e0f512041d140c1c8903420601c105855500460b500000d05000352301d0b07100c060f000c00149032441140b030305417000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 678845728 1250 678844478 678844519
    0xc01050703080c090d0803040f062d05090c030a0309091503020d06020c070905090105180c0d1719022a101209021c02010210020f040506030a020706091a06 68
    0x100b03607014100d4081401344903515400c20450606510400c4296282094186040b410001d08400c58000d03052002c40124424600142448202c40380c07451081d0840015508001c0c1030010945c182a202b1003070027200c2581c0401c1080810b078080d460340411141040d02d1002a034100080c1d4030241c0e20803110810058803515659080345030460b40050701c40c0e51b00140c503400c000985e030080902c94104414403081020641c00580152518100c88008145601400e51142494002154403801c50002407000c0b0301100c2c129290080c00080140c03030507600400c0e44a60b01c03c06d18040c001684034030212202c521410440c103204a514008580c209102d6000044864425101d64002c10480480702c10054005800501c05c49a00411041004002100c641e8050700700d0744099006111721260368208200d40d108441040d8078143c503040c6498281014031800b03910150200840c0b990820882c0003142c2c580c4503200c0d0039445083c64240e006860400d100410001408551145511000101e03090814 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 678846978 1250 678845728 678845731
    0x170d0615090b1c0501030c05040b010908030306012f0313170705040c020a0b0c18090f010303081017061603020a08070806010908010615140301080604110a030812090c0105070308 78
    0x2103084107a0f692408181851205040100c40c000c03c1e410007002100f008804a8120103072a4196010080070310003000444552a442c0310340d40e840d070410804140c09510400c1200b10b014003082c101510301d28601c07050518101c2c01110380c1c0650b000400d05613640b01e44c20a0780c50090610380e00320450810006001c541b5070b0365512419101c2c43c1d5031210800994000d01522615542000305005a4505000b80501940c01505105604103c407100f031035452806425082c0240d5584004181a03802e580c2d00f030301c0010f805081c4001000e480440042c1b010140030b0750082c9681a580a0f140c607040c02c1e049140c42c1c0d000c0c1d200e40310030315006200c0080c4055200090070307400252407400903056114940143d0385442c05400001240d4204040420f14a04008a0041c4400306c1c2d6101400e400c0400056022804280950780291708948003180110f8109200074816400060280240990342d81e00d00344994464000b805040441a003000800401440402400d6101382000c0d4034040003590020441c000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 678848228 1250 678846978 678846989
    0x305060105210105090d02060a06060c0f020102030c030a0903021005030610030f02090307060302130b030c12072d08090f0d0809030927061e0108040f170d061509 71
    0x4464022904001da004521612010000b0026400c200055a4846e0140c1d00b0307007000b51080101080098440744103e00c102c0d1555903804000002942e00e0162180d08150241c0c1180300500103411202000d200400e0a400640c940000044c41d520501c04105120481d090a0007000d00c1049543d44440d0714018100c2614a000140302502c07030071110003070044124854140c850700c00702040c0e064040c1d005004110000384901c04c05951500c0c5039805100c2121105400c3c44148402c0c8446140039101c29042091401e15030040c0c046100359100d21903846007109000e6100e00014424113410188554010900d807003d01070b54400549002ea90303a001a80d42c3d01040115400109819000d100f80c54144400410028000d101070321507800b414070324035824501030b04440210310240b4112001d0382240d60f11290560000710076200550b40890018400e035000d801c01c491220016040900045514440b00c0c00207454031484140362003200c0e0250480303104960211001c020254105004004545 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 678849478 1250 678848228 678848239
    0xa0807020d1a0a051003030813020d12021e030306060f0d061d190506090105011404050a031a13031713050708060a0f0207320706030203220b010302040509072309100305060105 77
    0x410b076201181c07208081e420700cd030100c841b800c5800b1243d80e002c5080d80d5054011410944055603503181c0d6900c074070054498907071004003001005481c1d66558003504006101010014580340e036603031280c401031881c1e90070f0310b080500e5800b003011441c29040e5000000010742e1040000307141000c08992440c5040c0039840c144500c00c0210180f8255560480e0041c04015041140b600d80e04d06d8803440721100403419540c01c3c1c20702c01c005000702054824040107140c02d41e8543c0301d004031800d42900315a6010f82103610686601100a012aa0030000c00c001800c07014010852031400c11601c20860720b2070025140349078010407062003c100c500740000500c0c4441d441d5101c155050290203c02c10612048a00c0c40d409240b400080a40d0554055841360300040bd00c501040701d0210149940f41d0164070003081840c8006c01400942000c0c1c2c4110f9101c0300b1a4105c901194030f40200c85071072418034120110000044101d41c000f810040d0582d90086a145002c0c448681035581d9151102d40500505c3d000f00d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 678850728 1250 678849478 678849511
    0x90d091806051201051006050f04260a030f03150e0117010b0910030213020705211605031c050103020102100b0409020a17011d0a0807020d1a0a0510030308 68
    0x2085911010040000400794510b00c3c12890105010304021a4090f40c0c0c4024828001080350040040383e400740d0703400505602c0c2505068a100c0e110090725502d41840344a81840c0b044140c081056401c403a0080d1590801400c1c0c0d00c0004040c0e96030344c180c1c2200400480010005101d055490a0540d182d011140c1a100c06016441c0d004100c4040c00b01da01c01031010a000d001822410b05d0425a0700948106540d0200394054400b80d101c0d240c001803041c1d02c00b59004d503504099180028099a1102000b49000800103140054205d620005e6809810009044084000710795510303142d0080c07468240320079859500040d44810200f070320030307001303030384400c10903e485e5250391100c8410b690003041015116140d050625654100c0b0303981c0221503180000302c481500b00d040702409403c080354024418184645c1d1000025048418100e0b00310112801440019107085015011030114600c0c082151415052a5054510140c0f030f40a10b00317084502880030030b9009005d07640c0300c4d400328480140e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 678851978 1250 678850728 678850769
    0x115030308090a08030f01141804021c14011a03010608191403031003151a1005040e1810061203050309031c05180601050a0329130b090d09 61
    0x5103c9a6180200241e0000081180300003400e861a13040e50300c0c409054010f41440801c2c00721840c0600022a00314044200203401468140d07005c3d019000e502c103000b600340c0c03915540d602c43c10540c0f90000d20704c2c2e5141d034250000781141c41d001c4000100d04134001d1014501d410303140b46d280c0d015554850001496140d0240c188000341c1d049085810351401183c0d52894001c00b003030a01c480c140011607036006003400b074200ca041140546201440c01c009810200803c2034100500e0100321145102400014000040d503132405465007031160403020000403480c0000c81c810760404035403040b0160118602501440510582403005000a9041c1003d550700d0300d5540c815442e60140c81c01900001d2545100307000141d00a4025900581c0000400244004000541c2e6161031090041e107400044413001040426105010350880308000c24070f042014130141240d40c0420f40458540c5102801d41031043c0402c20400d00e25648102450081d15000d00710100041001e0014441e0029084100503044007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 678853228 1250 678851978 678851983
    0x1020304080a030201020d0c110c01051b0a0b0f0f010303080105090727030318030b060415030506010806040308160e0d050304210209010b070f06150b041206060602011503030809 78
    0x1a055079801c031060002d0030b240c000d01075803120914010060401c108004510b0003607504c9102650643e02074800040c104004440c41e401c5040d4074004a4144014000c1a010a01c04510000d00903060043c1c149048414a40c850720b02400002200c0c00c04001040403d030b01529007810759508a80c61040d03501e540c20211058820303c1d03c00001c0f082d420003603200c4030708104007076000c4034400d445148540682e000340058484207844050010a079010001d40c80e4030301035114003195040c2c600c05808140d101e464007441e00d003091308081d0859001e00240300a15030411996a80700303030301c000020440420220700520011b41d81d0740041c00742d01c1c0d4600d44010417500b401079030701504902c0c1b41c40101410b0300101c103003800b0a00b0810b90040390750303c00100340d44041d0000c4030381032904520300c1c041e119030326507562004102a10304504038440e80480030a40d00c488500a01c0141160900710301d41000074201070b01203c0c1164020401d45e03242080b0901190010300300c25046a0301400d0442381d603550b000d103131030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 678854478 1250 678853228 678853237
    0x15090501050d02101d1002100b04021309050a09170c15011d04260d0e010216020d0c15080601031a0a05131b0c0b0108150f07020f060406050603012018010203 69
    0x258401410751b14026250b50009410002110014040c800c0c07010700410300c8100c1c8140e400c03018061010210512807880582c10840e04001c1704000011511401d49811040c4d240c210107140ca8131000155003101d00e1802c00031714405600c904040c1010b549040720000741c0700d544554050039044040300103020700003286101c0341d42c0400c3d0026000d1140d100d81c1c07030301d485c1d502c2004000c0c145031405481c140c120300c05109035281c0c5070141b0048442140382e60200403182354400c20490707104031040000b0840103030b0000d98100051031501c900401742401d10025040d100c6501000071500310000006429940344121a01142d605584c584840c0e401c400422001c1e29280b900f03c03004500c40303c8001d40c01a400003650302c41500891385542d040c2d8032003402d9501c5004410071480c03840091400308403000d0b40366482940001c52070040702c2400ea5940303529410320038101c5041c1c0d503d80e50b0703008010403801c003801000c3c20418500040d202002d81000d008001c4e0040741180030152000c2d0b900c05403664000c000b00c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 678855728 1250 678854478 678854537
    0xa030311070c082404080d0506030a080f030105013b01031503081207092d05190504061403030d0b0d2f0105040302030c01030902030c0415090501050d0210 68
    0x1520501d807070b071444550300c000104c540300385262001603080c0d10001000e070042c020355009801d00d252407110750490700582009000e60781c0c540902c8503c00c002a440c1e8008002d2a141d403641c10341c4941c5000d0015119180ca50004008000944040070715411401506da0b0251a110500c0507060340c007500403001045650384428000300380480100600c800000034042c2d0f00c2c00313108070100710713070314404115143c1c1510300c20340e8029803960340078800d05080b00216050b1120351107460321416580300001040d10346209405401702c030800c032003403055040a000e0807010700b0500c044005002d2180c40441d41e0303032284110104005d66915884070850f07a60107801e0316115000440c1e68030320001003159100d071080010011050a0182a03070040c69401001503d040b281c004015090900c4000c005602800c1c0d00329049074103000b101c0b280c100b00e0fa43c41c82500a1908614041d1203101e0030030100e40c080700c006800061180e911902404010781d82c402c911070840c410f03440d0140c4c50340341510313071600a0260000b45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 678856978 1250 678855728 678855743
    0xf0c0b1801021305091015120908040b0306010f0e100c0501090609050d0906020c01080f071101060b07020a1d06130212130b0f01240c0c030515070503090a03031107 72
    0xb0088902d402c20381c1041074903070840b00e900c03442e11401039881e84c1b50b20314410204480c3d02e1040d1010201d0040342e440495107042c22002c5526843c0e50f854006580c85908040b5180c80702000f40b1007556400500606641842c0c10481005d240400002c0d20081c80c0000c14000c01c91030304440010082d013900490320780c036400030003030013181d80903e01107484100d00030100000448070000054090b20000f2000e00280c010f071103140c1076444600000c0c1034080c00805200900942101c03034914100c092140030000c00401207210344900c902d00c108032021005511000100d004410142001c1e00c03a100483c0d04620200c0d00c040040301d00a03070b050040e0003622004100c40c0780d6001005954190500c01c1c3c01d865100c2d00c0005c0d0550b0760402c50098040081c000d000c4a00404a070520103102c004505c400c814540d81880300a014960760303041c114217201e4004450700d4101146d541d4800c43c1080c0d201e600940c1c01d06140f030840ca0a002242d1340c0f11f8881c040502015215404030408091003000c803135245801c07111 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 678858228 1250 678856978 678856987
    0xe0303040602031e1b0a1107030b1b03011a160615050f030609100b010905130c140f160c0308070606050307050f03060114150703020d09060f0c0b180102 67
    0x10224003d400c100c80d100e5060710900516500c04160505542c42109104030356188411800342c1c0302d5040d00442040028014040003d01c48002c0801900d001988a490b0003556407611131960030094000341080c01c03910109000500003008003030392000c24107000c2403c49031140030b000c0819212400c1c444000d481c0601d069205808030702c0c450901d8054520659500d004c0621520606503500c0045a40c95040d420003d002281d40d012500078000d030b28014580f846690351100c002807000310301481e420104540d1960400e00458100a01c05182c000c60316071a41030034840b154000003449580c00f01c40c2c091a0310114071082240081801015541002517103445825501e4042c000300040d01500f442403003021400101850404a040031901c8060060042c9902c0c1c9084009160301c500a11540041d103880c10203e12000d0b6006051132034043e6005005000a40d00e000e0123442d00e49d00080300f0041c1d074804200445400c89425074501d5406540c0d44469542c1c9010308003003040101c1045519400084d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 678859478 1250 678858228 678858233
    0xb0420030f250e2d01080619062d0501090803040e0a060e0405100b03010203060d1e0b100303110c0a0b2a01060e011d04030503070c0804060f020c0102070803090f040e030304 76
    0x7400c4c81401c00b28080c1d286414243c035101d0340c061440074030886866901500025440d50903003081041c14084404002c21901e440340d59445a03020a01c02c040707501c4802811180b4400c42080070392005020a09001e8405400c01213040d032a0321803030050f6490641034402103038041c902a07002c00f00511600e20803030307260304061400d01d40700c9901500c0d080b041420f01164140515040c800c032402400000c103100c421400355901c9143e10103850804100181b600b020a0011072840c0070814440c24194200080c0703582186030181032000c60140c001d0b080d5120943c0070b8519202c1c140500242c503140c1c245241c4030540300781d802034244c10050060000890618102c2c00b56041504905c09850110032a035110742c0c2c9459185080521f900900b40380700e1950070114021900440055401042c070345405005030b40a500c4007400c0e54007582c0030400180c07011800400d807076814000f91407101d409101038101140380c801d0082e541d002f0600000d11422400917000d0181d9655400070301d80703009401c260f984070314160 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 678860728 1250 678859478 678859501
    0x1008061602101d16050603220510090515040812090a12091a0309070e0405160311041b020703061e0906150f0b0406030908070b0420030f250e 62
    0x84010b0301030b80f060070404104c015a40100e0802d48038064401c40c150f9484a03004d0f1109548250442ea00c0d1303a00f500014041070381401181c84001c1c0071840030843c4007044ca0020701d400010a5080c2c42c1e40941028840042c00380c004403400c81c083e00400c0051900e030101020300b06070781d001000b00701c8440140e00b20701e1a0780241c8a1000c80382d0903000781c0300e0900070410351341c0d1038882210f000d80d054016100920200340d1413941e898200b030154080366104034502c1611120b0b65801d070402d54a02c001d4803c0d00c400d0b4a000c1c0030700100441d49100c0c0841035010404003075501d1030180002001161280a03011f0f5075a495881609030402151041c003056086041070001054140e910042041016002050050070903d040c02100e0300309441901c1c00780782c80c50840080c40b05401c11186a90b080100501003000b5003285400f59000d160031800d06c800c1070a241e003140d00e048500a0194100402500c4048404103078000450f00c60804e6524080c1240d8040c101c500058102802004180c005d001d04041039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 678861978 1250 678860728 678860771
    0x2130221040c05030a03020a0b0912040602010204091a0906090c19080f01121a060607060f020904051f03060209030309041404030e01020a150f0f020a0e0405100806160210 75
    0x80c2c00030302440303807500c042c075807a0b2602600150140e48010706c5480040c0213a0300c01903109003500f06890503030304101d0021400e50300c0390703001e0401130f9000302e0706011003000c2d841a80b0f00a440d01d001c03200b4050840c0041441c404000f00740510a07100c20303001489019120044810050740d00f1b482c2c1c1200350003600040d0a058041c0c4103242a04034100c00800c0c0354400200f101e1030740750071050842c2945001c2c1d00c4006215001414180c00080134407554001540901481180742c0b0880005030703e400c030320020f01c412218002c112140c400c0469240311280d994458114041da078001030056601c40700100428a50b1050035100758005140c4044031310a6403901c21103d006a129540b0400020301e4000120b03a00c10420b04081d080113484081d8104d0088143c0c010b8007000c03203038240402c0f040700e100164000c98000e03045031000302c2c0440c0c41500c604c0c1307060310842d54404002408104c2d01801c1c4002d295840c00000c00302000c801c0a0545488110700070421902c0301d4908401c00e0142c004080280340d660f80a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 678863228 1250 678861978 678861983
    0x7270b0a0b130504060812030901060b0706050412020705010504061211030a090312050c04050d1103010f0e0c24070c09020301080a11040b092d2d0f040213022104 71
    0x40c80010400d45000e0081c0011101b180c2e0091070510310a1840400c00d62001d00104ea166603100390000b40014000040e24456008400c0014107141a041502d220010807913094115040890b09009507038008082c0c500b50394445c036000184015001d00740c030080204000205240030048100300c00d40b007080d000710507079500c0380ea101c800b103c04448441040c0c070000e449090403041c00b0720050100d4103000c003d80350b1841c0180d0b2071003103600c510300c08a42181c10b500a174980d01e644443c440e0700780f20b2081000138a00c039015200001d0b10040461350384020780044400401040300021b401050140500001024000052003199a565075030016551100001c0b003c0380c44c000485030400da00c0c80c080c41140f06090300602004155940e44c0c040c404001a403034400c80c2003a48441c46000300322683c6500c03a1051900320300d2030749059050242d28106c4100c585134100307000c0000d004c0109071085104c03092703042981034440a540254030001c1d40c4c00ba0050009841d1009080310f100000508460442d6000f01d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 678864478 1250 678863228 678863257
    0x150901031b05060f1e0d0906090c080c030318032d10020408030318120a27060906110715020102030a0e01050c090f2403010f0807270b0a0b 61
    0x40d40c0c0d00601800e4042d201d000700201006020350341c0b24511501601042c17001c0d040d01c0c01c1c500281042c0c582c08840450205461a980e40d0014000300403000ca2030703001030240340c0010700348000028002030740d07845008a9000c001d80c2c03401000c891034600308144141d4844102c0119030202c220700c1146400c3c1110b1070503840e00e1040c02d140046c141c0740d0f0310881c0d094441035805140795030346030004000c408004040126141c403500d008100800c2488000d400d085131143d4030100100c2c8a94070192010709000150320002403500030410000307030000c045000f10b481c113003000c0f03003008001c031400f5040c0840c507400101821100610710003500d13419801584940503030780082042c203a90b00d4040703080300c90844600c01c0340e14003040303212418034025070b4509811800a1100142140b0000705141824801105600355080800140040e184c0e255014016106110080403103a00d031608911458600e0344c0c0e61b0400000c00c1c541070b0504c0c91150401a00c444000c0c2690f00100c4c0c0c1c450f01e0700956440a0300040b000e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 678865728 1250 678864478 678864533
    0x1305030d1107270203040c05060301090c02060906060105040608070207090c0305072615120304030b0105090c030717270705010909060e07030e03070506010b0304020111010b01021515090103 83
    0x204041c0550140020060f60442105120640c0800003035201500540300e52110300f00c00907a983e40c00b00214007900161401080d92804114003914054028046640a0300075000304051641d00005541c100d4400b481c1000c1c207900c1d0b18506a0900300b803504085409070524074039001c0340790960051401515039994034800e00a22004400303c1c810b0002e40e5074400c0800c50045003507146a8140c01e0100311000b01500002d40d0124069850b5620561040304c06640c00d070010811803a058401e544e00c01e68840340b080c40c500d006000141400001221009007100420101d40c04058407424401c1401c00c0c11503880354a6079180c80300c0d0b59480d0364811075000171007060000c070707000049025840031034103184070000c41915403040c140d001c0d2803d480c84018521003400070102082c401c100141c02403407403108090b91b90500c0e00005000c529121015130441c0e041c0040e610712641d000500300d50181289040c09160744403000d00c0717070340502000885940107084d08004414401c015000c410458072546103c2c040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 678866978 1250 678865728 678865739
    0xb19020d0225050706110c03072309132009090a0b060303040602060a0c0201110f030a1505060a030e0c1011070f050d060b030a123f021305030d1107 65
    0x41c5040d200005103182c200c180704000d4140101ca194a0380a04101034847c0b541c81400824589221035000321840c80c51098042141001254268807a000c00d0f11403104a03e40819400240768110000410b0440081c00306054414075105070100100f0040194259007001c441c0e46035603803d560015078018805401058061400000711411100260080c2c8055580e80c2e411030300a240e8400d40c9000d5540304c400810310582200e0040411070801f511704c035100c0c00c040842c0340031500d69107032091180c2c504500500155480c6000d56203000018a401301d08103801c01030240c28002e0203408c0d55000a140c400c0d0054450700944480001d02450040350071141d030320840504404202e1007040d403c0030031040108003040c087c4d0085403088402034202c480049a0b6611080d0781d50600400b2000144148003161940d1402d4210041c0324040d80d080c0741403000d20b10f690183c0c1030b092600a96904e580050383ca81141a81000d401c001c000050694903a40412600035141000f0000400d505c0c0c011100080340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 678868228 1250 678866978 678867037
    0xa0c0305030a020c0907090e1b070c080601080d0e0f01030e0102031014040504030806090928021309020a060302070f0c0b09010206180c06030919051e06130b19020d02 73
    0x803034121561075071f0f0707071700d142015145420304083c4c100c400e521054070b14007400c0c09141c1c0080000720f215480c1d00030940d2500c01120b0914030181c105030394a403c20b4007c0302c4800e42c051461461200704580c6070b01c00c101c03840b00690051480300c150a4255001008200b007441c4250342c144222903603800c0304043c011104007003100300e41044a0040c04603803c50081030040c1480c04034180e0080c1c02c1c1c0104c88040c00201003c5000d00719421300302040200c2440d00d42d0442c103003404190300040c9000300910a00138a0360015000058600491041586c00300f081760500500c954507282d030680001031020b42d16103602d002c011b10791107140098058465280401c130710540c92200c0c800022340d000c0141413111075403400c100881c1e201030a01e15040c03080050741c141e0804011240c0c8021032140c0000d00030342d0080550f1289041c001c1d02080115007100d4108503c040c0d18181001810398026413008003a0382d2500d0f00c01d036410511000c0c1c44402e20215411448800c560b00900c1a403000c0801950301609400d00d084 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 678869478 1250 678868228 678868231
    0x21908010e010b090111060901060302011101020c0c0103021c0603060911090403020309060304020a090c08010503010e0c011e170c25110405041e0807120c1208090a0c0305030a020c09 80
    0x340c4180400010091208240044c00ca2400149403e42280d11101030291030901c066a600a072079548610030011036070400b903145440061742c402907041403210034015841e000c1550320541410307000110030702e080b1a400c0041074568040b8008011036612030500310001d0241d05000c640082150200b0b000c2450720790034070f5106a81c0369000758a454444428032002c0d80010303104903040309040c0c5012800c0c0500b4010b10098071002c0c0e03901072056260004240c09d680d258418411560009554200c0c0359901400342c803224600302c0603050220a400d42d0440d41c802c00c840c07591414032281d0f02800310b01c007400e00c0181012200c00703848203240340d0b00030880740c86032006038001001d20680005120b2a0f081a8102540c0580100e0450908003c21400004030400a5808036a80f420018103001080b48042401e0b03071a80c05442d05e2903404c01265204104c800406003a101848032550000300d01e03080030003148000da64046040d841e100e41d0b80c9401c95a1350000c2c1108400350080030b0f0504a20700b8032601e01c0707 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 678870728 1250 678869478 678869489
    0x709050409060519060f090c050708040306020c0c2b0c03050d0f030b0103020405010507110d0204021606180203070308130902040b1c11030109110f1b06070507020a03080c011b0302190801 82
    0x70041b985403840305001440030f5515081800070038030031100814406000b030701c0110b00aa20140e5102420b800d51400d09804026041c03244116803940748004402c0021100ca41c016403035000019280d80c01c006041043c1c40d40020000d00c542d01c0c0c6062050b5100728107a6010712503440038044a081007005506901460084038002002481440085807031000e0018140c07901400c0c007145101c0f50f4000c1400c7e40d00c42001500c030015001e43c0b400403c0359030711516180072801a00440c1c105c0036640040c0d100c3c4021b1001828041011407041020103004c031240c07005050300b900456640d580c1d0184812190041450540c070004030f0003d00e40452120301401040c0f40b2000082d9103140e0070080c1540080602668245075442c05100c42d4603601005402000d05585140d02c5420106904201c01d00e4000001e0402c0100a014090038005131210307603024003526840041ca0747c0303d81c4401d8101d8010085510040607074602e003105505060b8041c0c0c000d180710600350a10307640c4e000000400b42c501403000e00c02c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 678871978 1250 678870728 678870749
    0x90e1c02060a0504030509130c120501030206030703050c1b0709051f0614041e03120f1704020f10080a0f0207031704020102011514031b0f09070905040906051906 71
    0x50a4803880d603101035030140c171a00341503041c03070251000b2030318406080c0e582801899a407051040c0d650b42282c84617010392030001c801e1002d50304507070101d00380b03000142c00c8605040d292000f00b9404c02c10795081d075100d000e1100c01e2010402c40c0018541d96010244106540c003403900002c2810040c10001842a12189501c81401280703840002c68820103e010780c0300d103648040c000461800e10701c5074191184c10b000c4510811017815800c0655511705491029000c0c082120851211141c02c1108081440c00107041d40d480c65a82d8004a0ac12161400d00b65a004004070002034409800c5241c41d03000340501c0d0000c00100c0c105c81e4191040b17105201d070280114148841c1c115403016161100c80e81f1034818400440c44d002c0381171800100341c0c201e4105c046c024005102281581c1000c0064850380c1011202084422070301401180107112003401c60381c0580d20f008005034a45014200c40e0b001804003810400c178032240350034900000c15043ea4000701645044108011054040c01600155080000c0c3d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 678873228 1250 678871978 678871981
    0x1080a0204030f120201021e07111804030c020a03020603070305041a07050d020f0d05040f15111204030e130207060b03030702010906051b010f23040803060f04090c090e1c0206 77
    0x2030380404c8440c03900c40307101159001c102c1000201304088070143d080f1030781c0c0b5016407035901a1518089100d1140440340c041d0f00d05a04030282c0c000905001a080f50300f606100307201c0302941c0049400b0140d41c1d00065003014000051017003495160b4071491280b80500e440386031845425000350180c000035182c800c0001c4007407000c032070385040a5004001075a40044070300e00c0c104c106a00001510720445095074008080c0c0e00e240180aa4500f460704041c030307003100802c800c59a00c402d10041d4004c0107144400854010001403c241c0034000c0d0050f8080000c140b0382c204135a50f00c030b81d0080c0d40b141104a5440c0c1c00c2048180b0a0b0030300009840d0402e038161104521282800300803a21a0003000301e40d070016004010071800b01c4020300c1240b8411514040200301c4a02c1c219454042401c4030300340f088040d8410381008045003803042541d40085080310ba0841c07880c440d00009002e4a50130501504c1c152004100080c501d06550060000681110a88036280d11145490140800d04800c000260301b0a00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 678874478 1250 678873228 678873233
    0x810050a0b090123070c0b1c1e36110607031b08030103030806060306010c0b07030b06040f050f010f0c170408011407080c09061e1c090201080a0204030f 67
    0x100503121509061501c80e070681c60f82a81400d00740f115040110322010000f9030b007070600506d441810081c100301000d042c540064140c14050a02080305075100c055660085845025103944500114581400e401e000c13410301600031506024041c0c2946040900c0e0314001d010103102c14040750341140c1c0060303c03003906405280070310603141e020b0b510031000c02920150b542c240680702000000041d008001c0e040e225811490041c1c00500c001d4001441842c0a104012407030383c1c45180807085c1a8000011405610381038419400341034500350f0140c0c07001c07000c00d01040001d860724000c801c03a0002c035490000844840c0055031241c085601c5500002c0d810241d500200f4012014256585540410b42380781035519030300b8a0071540e1306009505160008003c0c007004a60240d416600035803c1d40ba05440c080f041d90014483d8402d084010140e00f0130f940292003800c1e2824140c2c0c2e0540400b0300c070b4004404000710784a00034082034a007240032814000c0400d0303508500b8030a68040d00e5104005060803a5030780c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 678875728 1250 678874478 678874499
    0x6080a093e2413060302090102070501110c01110715030b0906150706020f070204090f02120d0504061101020d021b06150a030822090902090609150105030705040302100f0810050a 78
    0x840300309004a00800801803c6001110200c0041c500e82d0b90060b21030140d00002400c2c4000d503804141004048811a0107403900400c000d90090000d081c0a42008a0301305e0860402da81544091018a403c45999418503010f4010048810048440c1140c1c0e03a42d490401c10095820b01051445070400d111040006105078000c1c0f4031024011962401e210141e40024280c80000d0004c4580180011074182103040480001c0707c000c41310006040009094040200790780220311030344040042d0354500010040e0294102c41d003058106c9070540d903408079a104140d0404100340c038501c41d4400c43c00090601040c410402904000c0141104901032540d140c00e80a13401089100718045d8100c145030002403000f41e01c00b00103003010500441c180340c150040050a00004142c1400340b2a00b404001540020013000034034640c090a005403251a101800c84240c010303500000d422000c0c07080c0001400b900400000100c0b52555120072155890032800d4907981224490795400c029104000c2c040d01006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 678876978 1250 678875728 678875779
    0xe03040302010c1e0606052416061e150b0a050f0a0e121b15030604090807050706030203010e060d02010926011d061e0106080a093e 58
    0x34241d120341d200b013100c020b011a0080705004445c81c0e80ea03240c041015040585072445642100c0f0300c2d060030741130a10300519852155540041840c01c0901001d010480b06038080c5016550b1724800d4000505030034080401030041b01e150200e80c6044c1c1d180010099000d0088401001072551601e041401d000c0603100c95400030b1118000784000748120401c1e68540302c035409501c250003c01014944841c51030325440c4810101c0d81030040c0e17024800f80c9c8000f90b0310021250000010745000814171100e04058090307028142d4014010f004000d000944254190081c5041c1c1d82d40701408a840d440d1401044070714103840c0d100034017154207042c0812609880711094101c191540c1049016520400801802c444100e41c103442c05a240d2030948488200400403540d00c41e441c1d444039040903440241d80740000d90148100c6042040c4980003410030310305d941000000907030002c40c8d0f04800d00036440c500da00c1d240380c10111800d040800d03260b0503040804da044000e03a54000d01198031600c0403444903c9411075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 678878228 1250 678876978 678876983
    0x10f030b1816050103150f1e0b0315030c121b0406090608030315060306090f190525030606170408040e1009050105090408030c0702041d0f060a0e03040302010c 70
    0x4074000e14105401041c881c4540801600507010304050900700090300302c0d10106254040740b005108184588540070143c1010344089003922412811060081c9421640c560442c10815a0100501c80d03040842da04587c5020803c406455404260600f4003802c1508100f0240b49640325070116001a2401c84080d075804101a0020aa6a407259400c4c1c0c1501c40c1c55200011a5100104110715105c0f20088a403030444104c500c4d5185080000015064020117008002d4214002000c1b03030307680c612030148990b4050ba4540502c01858603088c440013000c81c40c0482520944c8414485452a2003481001c061301c03441e450303101d4400140c00c04442501c00040c81102c1704030040201040c820710f50640e070303403084502c402030082c4c05003401160b1060382c0060b400b485c041e01c01042404000784048060381c0d407007010003060507180e030007900000300503019001124402200c0344180c0485643c0109016070070003ea0003c45180381c4403181581c1c01c548803000c442002d508244010310043d8462851940441d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 678879478 1250 678878228 678878251
    0xd0c1203090311030a02030409050a0b010e1003060324051803161b0f0512070501090506091f02060117071401140c01060602012a020601030602090409050106090b18010f030b 76
    0x2111000e0240c6507600c070b1700c03100340036074400704040040c3c1310240501580094825014040e58041c0340010304581610550340744640044840c402c038080c441d605c44401160072046036040b2600700041d022141844003a05081d00341480300180401c00c080c00310f00703803100c0300d00d008610300b01c608240403d058171103140407a148501800700c400720004011030324024100030081074181c90700d09010410103448a03408440960440741d81000243e8200b50b94034200e0348165196541d0b0100718001402000700070015282c0c0b10b02128000c41d82c582c0c00900305043e565295a03441d260031010104550310b4906111b000703124100202103c1403944680c0100e144c0340c28000d0121b0070200019074590a5410340d8004c0381c0180e640c1c0c0129500158940800304419101e213040c4507500105000c000e446103030500016008036000580360f50541c81d00d81c0200c1060340c10030b0007000001e0302c03039035590003400c0c441c1e480c140b2230034a070150803011340c1500c20414102e420b00014415660b16594600c240982c00902445008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 678880728 1250 678879478 678879497
    0x207030c080d0e010e0601090b0a06090e070c05010e0a060506010311040b1e030405010b0f1203031b04082d1203040f030302130605070311012007110607140d0c12030903 74
    0x1e82c007401420703510060000038110f80d41c10010701c08e0880f045515074610500041a04020441c0c0020451060303030282100c1018969a6110503a035542720042d00500039880d214038401c0c880c4001c100c45800b1441213005000d6522000011410f45880000d9003400c0314041108101e415801c200504c40e81c444400031046044901c41e40c829190400c8a0503100c1d80d45680c0140c0840c901140305006000d004c585d0f4900c03084d20035a1080d9280001418002a10545400c808020b00e41c1d100740c030010f000840031140403a05100040e011a0000740d2000355441900c02d16140901000c0741c1004074030f11030480c1c181585d8403916485940170000b40b007a02816420401d241400109042c090301800340c03919455912032a5190040c003c6c0702c40601d072145a4075000ba1884a8a6140900510800c00c02441520b502031400e11a0403580719100907a44200005004410030800300c411840982e01042035860807241010b05581400c000c4200920010760f117880c0380c0c070303850080d17005107070745406890201da20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 678881978 1250 678880728 678880751
    0x50a050d0609110309010b04050c070605180f030408010e0f0c0d0c0e040b0f0709050a0b0702130c080103020a172e0911030d0e030c0409080f04090204050406090207030c080d 76
    0x40f80d100e0382002220020000800007440001d00905500140541c0e04004626014040700ba46029901009001039140c1011030002e84505603064108210003098a01040094403115500e901500c55420302c3d50803e51002d01041c40828500c8045c401800606507411000c0104070744c81e05c120078104c8903a600c1d07800200c1c5204580700c80c203107e2441b68a842110b424402c0c1e90f44000c0800410140811030500810f200320f46420081001b19035150103026113404041c4005000c9100042d000d403c001d00d054000e01100394083d8029048134000d840c0a01c195031520241500c640c035000c0c075401c01d0b9101c1d600f500e070f03000001440c40c3c14003030003a01c2c110341050801683d5015540c104a05a5030754803820520b010506c0c007801110781c500c2c0107061084900200c1c001083d154040300d1a241d10842e500da407100d06001c01441291200070340c0d514019603c64403003903892300039001406001d0043c0d241c0354012861060354130032901500d40644490f108100d0668840d062a840244c1680149403110308241d003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 678883228 1250 678881978 678881981
    0x50907141e0a1503090b180705120c0306131103070303050f090f0d060b01080a09030c111c031e05030903180303040b0f0c2811180c0a020c0108010501050a050d0609 72
    0x1660b040e500800d182d645c41c2002810380d00040c0c00c80300840b005100c2840200c10000c0c08008684003641d601c20f0034202c01101c541082c5c4000c401e5034040c0640001c000d440096442c024441c0d500c2800c800b08031082002c140355484010307000c010082030302004100c980c114020b000c0c2c079003280010a0302c03114000200100b40301c41481034080303c24a0302d84e902000a507030407503c034650002c40d0181c204441c0b211510000e20002c044600645a640310341040c00e603e4481e41c2e10924000d01d00402c00c0f854601910740180581c030208890050b4040c0c80888409203407080040700e0084208000640c2025103000c100580c0310f400706c41c0d2950500c8100000036502603030202901e19514480481c0d6102c0200440c11070400f0300d025207040c020220215607910901101c11515805900800da803031020700c2c0d080200342c03448419203180c01000c40500400c440b0034070810007040144100d500356072410001e40700541c1d0700300003270080720301080c014001e62440a11840c060040042101000305103291384003042e20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 678884478 1250 678883228 678883259
    0x50903130b09010305011a0403020f0d020316150203190e04060312020f07080f06180307020307090b0117070906050c0c190602070e0609190b040f050907141e0a 70
    0x5007040c0c0c0401d52810540e00741c41500e006140b0044006203194446101e20b60a20460000138070808681c140241d013a21080c0c200d2031825400b40481c0c59840c03541c41c0a8071031021512030080042844d83d0010189071001c0141c8046285000071501c1030b00034200c1c107444900c491617445400503664940040840c101c10104500c2101c2d0350041e04088202c9209903042000d6500140c050354410016060120b01c0001c405512030401482c269820041800190031071140c280060360600c40c406010a00c3d88140c1d01610a01c00c0036228000070072003080107d600700c0000c960500104050b0310b02040a10b0180006066104940068901e03000141c0006078800765020200c0814001030780050101076010845c2d04084c0201b6121030b825072501c0400240a00f1000380801d111100005206140030b40a401002e84580020001e0056034a8520901c00500040302c0314401440740c000700140000c490b1700c00808122016024042c050b01703003800380d41d0810b0708024503504051284030000307442c0c40708210103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 678885728 1250 678884478 678884489
    0x151a090702101d070905010807060305190c0302090a0e0603100b030a020414010e1803040303200607031b0509010203070f03111005010810230406060b16060e0a0b0a05090313 76
    0x2408104000040f00745400134030342000c40d4541c5400c00500420500242e90380880f912441c0100301c6a1340c26840080b241040601c403c0614240301081036995016000b50080460503104822101d0391a02d0156122400b44c40031070309034000c0d103000d50030b2606503000301c402820050112242210b565000c101110b84000303000d07004408420040c0b06007501e1909103600300520800c040120038031f01e01180d45030b200750b03c001030038011407103145007030003204c000e0b0500a80300c002c06481c4d01c1c3c540340c0c0020340a05460449112040f225045001d45240940c050b5940c0d40b10690045003800d0003552a5000e03e112100c080d405e018909031240c08900c0300300301d03001c1c442d256000042101d500d4070128616214140794912081fa09000300a5800d0301008001094555800c3c8030042c103848a0a011006080030b4001d015040c40c00200014004001d00c040031501e0b201e00300030402c00b550009020b8880007030b10743c002c0c181c0c600ca601084030b500041e08400d0300940c00ca81503034036101421290884080e07081c1e114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 678886978 1250 678885728 678885761
    0xe010306051c150c090e0603070902370c03051602040204031506080c0d0803150a0602030901020f15131505070f02010506221107061503151a09070210 66
    0x42c204020045042040c4094041401d00c04007100030400f40040c4c0c1680584a441d981030400642a991708000390b400a00d100d050856441c10103110010704001000031340c14100150901d00028a0b50390050400050304607951403110782c206036400c4650340e1021054580725100740c12030f0000f43e60f03035100800046125141c0d0403106841038000006a8200d90f00500554002d46005215034840200c4503600f140d20603461643c99440380000e6201c240106101500500e01d1303100410820740000042c0710550098088680002000c050b1320b5940d5508589040c011100740042800d41c600300000018452048100c04409001c1000243c11200708580c00800140c003141504682e03078086c411103410035030544407010310300c0704001c15006405107588840caa540d41d941040142c20f00207004d0b80d010310340c098414840402e132002442200400c50105490b02e2151808206400310030344121145c03840304140881e0500c40120400c144110020a5901035000380c4004140f0402d01c1e01c0340c480c1c01700d8181c25 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 678888228 1250 678886978 678887029
    0x180e0105010e0118060617041401060f060315081c020a050d0801090606020c0306040b0703061205070306060b1602090606040b03331f051b06090c041404030e01030605 73
    0x11928414644900041000e614203170040c030900d40d014a4455400039003600b081442c0d20769181c0b207600d00c0103000921101754604000814071010700e1071903404a9445a5050005541c00e01440604550034451031059600184000c1800c00d21703080c19419a11050050b07131040b450340d895082c00c00044680000000b000780e030040c400042644282c00213461944000c04000d800880840d503100c40190000d80784441040c0002c11240c40390300818060500d0b05000e000d0141e203450a2503542240f40001c9484500345540450080200c2003030b01d072294006050b008010b281c1e07400780a280d4002030205c80c0c010300d007008040b131400c40c100c0045000b54402c0e08100a0001900c14090007107005401601d0242160b65038642269562050a003030011155000c07002c42802880980d070900c1b95481c00341041000d202d4401280c18042441480380005000b52442c560241007000210b42c014900d20300202c0343c1e4804980801e02c145003a545007001030600040c481c0d120400074035080020325a0002c0410000d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 678889478 1250 678888228 678888239
    0xc0b101d0a06060302121515041d061912030207170307110105030c120a020403170a02011803080c09150d02070c17031e160b15010207030c180e0105010e01 68
    0x40b03000000c0070325140441c2800c110000580031140701a003200030750803045880c0c010590303540400d65000070480403450707aa15070b9081028000121603030803c400c0b0110704001070b29400c01080c2290003540b01902d62002b0303420450320074415040058264214410810003165451200c000303c230f00914814000d5403100740c10710b81040300794031503a06d0f50704003d014024000100c1c180030940c0c20f400301c00011484503035107014000c0000d000e45e52000e00038006030b10790a80008030140c0240b218000c01e500130320501d115034009640441a040c0010300240c5810300003036184070040b02900d02c62100410780c12540d15094000c0340b0503044803200020751540019a803040100c00c0346800e0003043c003900c5003101600041941c80e1a0f005a201d910305000c201c4041d22011140d0341d080307940c8488550750500b003a450904010900c9903003141d8420540c419003c07070700e40d03660000035a10122070b03000c108842147d04010340208400d44491440550340d0319942c0c0c50a43d00002c4c01450b0182c02403510805480d85400d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 678890728 1250 678889478 678889481
    0xa0b1804050d140a030b06070f060912020613060c1e02030c0c09010503070506032206090218060d120207030501090b0703110a0203030109090c0305010906060501030f0209010c0b101d0a 81
    0x302401001d108542248801e4001e00c0c3c3d0039640202480c1c01c001802c0d210725400b003102481080700041c0306040c0c2e0414130041181660050031010b00400c1c1c0c01038803802c603032000e1769620030a8800410344126503a103807000131080d80008a16a540f032502d0b402840c07500d0680c40064407041c80081c0560408580b500700c2c0340c010440011003101c2121054221352412001c070762170300641c0c011940140c20010000fa142c804042c1d1090410300c40001e050000d1102e41402c0b80106410141203104010b60120607000394040c0841901424000b8410040c034001d60343c07100002c104002d0560b041d030103294000004120284120324040380221a202d041c1e240000e0000c04564801c017249945480900c800a44554000305507419200c900100045600c41030812400c0c1148940c4010065800c2030300c2401001601d030001c8007159400c1e24148002281c003401303403080c2e01810112a00042c03c5140c03140128004240060f001000e012041841d15118100151000b031580300003032004103103400b4030006183d647 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 678891978 1250 678890728 678890743
    0x70309030e01021501051e120a17120f0702071d10050111100c02101805014b1d15010e0c0306010905030d17060a0f06080a0b180405 58
    0x2d1000d0f01881200c0784000e1301d0440180540c501507000850ba0716070040c0002003418001c0002014103400e0300ea1104525510341c15020215040103013850002410141001922034403d00226020034907604c207800c90000640040c240d2085210700d1380000751800954110780c061300c400540743c00f128074241c1c1003085d82040c00e83c001e50401004806240c241c0c000401e600c1d5400d00380040105003526004c4040f8908486c0700308040c40c00e0300d400c02084801458044c4240301078030a400a200442448000040c035aa11108030002d6025a052003455500c4d47d00035500b41d00a0385042c509140c00c1800441d080710b0410101415070040a014008180003c02c209080460451400001d541c1800b207203604112001d0202501c442c0301101040c1140e0041404601504001d02100c0405681c12402040c0c04d003200880c03048408048082121410018034010560b00745031895074580c3c0ca0100e040302c1c2842c1c010301d4401100d955140246003960364408029100307404904500e0581058200359007000349 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 678893228 1250 678891978 678892007
    0x1d0a18050c16030507061e05010e090d120c0c0816021c1203110705010e061014030304060503060a0807030302210702010806090a150e16050c0a110607020907030903 72
    0x41c28040008051204426020032035454508507031112003514040018200c544480384104600c46103c01d0040c142e944800d04072889a00b610240d038031058051619241d410070442c0010f204031043c01460610303600043d00c41a124a0000c030642010b8580e0305480d0015a10144255000714248040d441d2125500e569245114160480e81a2541d9022150041400f44d6014183c80700c04801000042405a0b03021a8000700280242c40c107244200351a850115030304521440c0e107484c0401c0e1619046c6070584c09920140c01949002d0500209494540009000b03507400038402901241d085414001c400045200782c0040c02c0c80d1104403e4400301103407803128621841010720005d0f015030b034041c00443c0c1100080d0303807100d456143c0d0032182c80901030407616000080004000000c010001401803442142c80c40b021041150304000122901d11030640b0807105640201d104101150b5250b50745a94804014245883d04800e0750200b0700c0540c00700c0f6034038042641c9072075850525400607000403101c81c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 678894478 1250 678893228 678893251
    0x309150d0b010206070c0b0402060c060405010b0307080f0304141507060c141c0507030f020412020909060405070e0606090a0801050f0115090605030a091b150810061d0a1805 76
    0xa0440c0001b0505502d4075005810142c038500031400390740300e82d002c07105004050020768845241c24107060703020300321540245000c0d228104001404800c0440d20140c111590000f540c5003d00c1c202c1004c107031050050440e98402100b80c040084950110010950503104201c08a442410004003503c0e2040e1760096001c00c0d1000c006d200054000341000703840740304408070000f900762901003040703005112268101c28114400540403500d101c0042511010354401c0761310b565035942d40030045403101015240180f00368003084062200502240c416035210b100a40f03028101807105002968103806c60380a544165514820321811140c400d0f401c90141c414400a0031000004480c0103040d07140c80d110b0311081081c00310201d01d003800b903500705044854001184410560246016098503034041c880d03002d0004604038910500f90007450400d110340d04070310003d032301ca0340f074260152040301d818108180b0742511a010030225651300783ca0a0701904000700088070301c1c120308004030100c45002d1702c160f8400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 678895728 1250 678894478 678894481
    0xa12050306011b030c0b01120c240c05150c090f03120f1c05040602030f07110c060d0207060e100b0d020d032d082e15020309150d0b010206 61
    0x81e40c00243c0e012418054020000c000061400d04985030b000030356005204818a00c000200340b203d011030603811900403100445140d230303030322194850f0500348208001c980801d4640c00346c40c0d901640d050200035000304140c07075401d0a0303008001451402102c4c10030343d00c44c002c900e45d0010701b0915003982c0d10310740c194001c00040000c1c001d487c20f1801b800c52440d10300680018002046806480d1010b0f1514903c0700034003541c10300e80f801780083d400c11600100000d00c01c00c0007a41952052038030b07003a40f4000c10080d02c00d11030084280505588070311601409207400308120350015086200b1161760303041c1c04024142803050003d8080541d800c20390031038800c48008505201690f160000f0841048c1d0500f41940c2c903516104480201d20411544030147d48012845024025049140180315803614643c40b039100e00c02c030240032000c00d0301000041c0490600542481182440c030100c1c1c041000030700489052142510008204800404a4080200e004071707030403082c0031090040341e4030994240003501300c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 678896978 1250 678895728 678895741
    0xd020d051e010e060d021e090c1801030b06070b151906090e0702160801050609100605091302040812040302090c0408030717040e0103140609010e0c010818030a020a120503 75
    0x140010f0040901203015000450130780da41c0da080c0020407a501414620082c4d5849400c03504c41da025400c52400b440019002540d00030440c012900c039410a55892140081034800440042846230342a50700814204519030100d400352100394030580c92500c000c510400d00800340015022041c160400000101c041801103940040c80034098403182404c082d43e6944054049203030198070510b0001800c916140826540c00642006100d0882030340c0551b280c0d2545148000c0312402440346800084051012034142c1c80c103116080681e4110280150400307403136440040c10041d0507010745e1081080060108118100880d0459010460712610b90901d41b80440541d168451000c00800500a01a1728100341c00a0800c0d500680f250b10f011502c4c0e076840c0c1c03821007d800180014510184103140c009001d00e241400342c144416190b01c0038000643c01e2000541e1188406042188420103110b1007013403180382040030744600042da5008144810b01c500300301602403503801d0040c04100080040103072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 678898228 1250 678896978 678897031
    0x10e0c0f1003090c05150c06070f0507030513170703031707140310080d090513061404021b0321010618170c12160807031e050f030d020d05 61
    0x10140103506021030320a880d0b00c0c1681e410245600860360001401e500c4140c680c86c08805800c200c0c10420495000c0d80714280e040e02c5580020520200240d010403084001030300c0b50001c0c1040b0b00303281c89060740c500d843c6d6a00413940010105039400e0359125000270000d043c0d03c00c0c40c90194100d04e040b0000e107070403c664000c0c0b10200e00c25841004c03110005c040f5107503a80300c144600080141a040e40d01d001c5050200614106e282d1140324490000c080081d800d07200305201c0d0808503105c006600a0be50003000a001c040e4000c151030344481018481c51224000c002e00040403110030301340e00d95001c0c0d0038909041d0045213060300001304101488036030040c40340800c1503090a03600000040003089440300313034103803400106080032030700107407010b40c1003182d22000909448851410282c0c81045030302c0761100d513603030265440060f101c018241c2c00c040c1e25030104c13148059524098004d60301450f00d90320181e071846d44a22a00070b0520f900040e8048442540d2089581045002d070301c03028065104030080b035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 678899478 1250 678898228 678898249
    0x9130222140d031404120201080f070e0f010513030c03020a0f270f18020a0b0a051806070b040b04060507090311120708070612050601050a050d050402010203070b0405010e0c0f 77
    0x42c05800405000000e040c003501401242c4e920303602015589030f4807500180d072115603d8401720f020a401c03034080744d2200303c2c9119540c418086a5101c42081c40e0030f40c20804008141d0082c10305003c01040075240c0728111101e810003450094040310b64551552060000343c80d072503030000740b14004052003408001c0b000c6804008012100881c1e0f1b9103686199071000041280d000344910603803a02010203100800030301402c112900882e00c001d0102e41daa1081c50291041d03031072060005d01d04112501200385842c016541410010708800d08110389076a811180c108240c038240c854284440800003044010702031a98004890b103003507000c05203140e07a41605484040303c210703c01d02d240d0b5410004024200038100041015604503083e050f501e000240a46840d0f8040c4090281800000355103035004404468644800381c1d61240750a49516031306009000145c01241140010000c00011694403122540103a0007000005002a5010034052402400080341802200180b01d50441030381c070a076510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 678900728 1250 678899478 678899519
    0x519060e07141612030f0e12071a070c060c1d040509100c0309021207030c03021302040b040f080606010e0a1205010b0603040317070c02061e09130222 66
    0x41d40d020030740d9501c40030b841c040e06405180c16920028510203005110310410718421144e02c08209650a2600500c04d40b96031030744401c1c0035444801c60808100b0074100403d0018020f050003011190350306668440c6050640e11500003030a401c070703400140191442499598241750a1104c4c421010007a00b00c000d83c038185503d03214594032000102c0000c0144600d62521003011410481c081000101a009200d12102640038000fa501102c80032900015060306603a081070303501c6c051a18590800c99001ea506002940f0245c00340300000d40c03409480007030000b415081d22440e05c1d6605201e080c0745000c10080403c0c0c100165084010ac41d6110701400d80156a0208010300f40800c245c181039007d40220f51203550450800010002810b90000d1883d0600d48034215919545c2c560b641c040f14620721110000e54010010082d00c4002d071302007526400c0355804400754a0030320807200006614102070069083c2403580014038030400d4450701d041140400c18240706105000d09143e8209100078007034445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 678901978 1250 678900728 678900737
    0x21504031d062812090812190c120c020c0d030f03110d050103060c171f0302030307030c0b0901060b071b0f0b0910111903140703030519060e07 63
    0x1d0612a407290011280c0b9030108071102d081864040303a8000010710251241c800044110214002c642c0060040c00406500325121600303041e50317000707000c003078060280014400f003500c80c400140410030750284061030707265515264460000f0f00c40d01803c0d101a0b4407030408640010356003401c180e0b212280c03016043d0301172a000300c0f484500c1400754020140c14554090604d00482d400c0c5080c07d20303410031410b884c4a140309000d0304485031400c2c1c980e4070600f20f501c8141301c48103000030518440a040e04401c2c041040d80f0b00e04c065925004242540c1c0940c100350006030900308005c05119210210070380108240000b002041c2c070300304111883c2d000782c0c05d000b814203008458200d801c070b03516600c480140000a20001c1c08640e20110440207034000c10805018008820403420114004c01e90280c0f407081010250103884440c48180c0140000008100c080c400150a500080181c1c0000b40141e90720903100000c40d81000b0200000c003a002a60500b013083c20aa01401a0001168000d0700100281031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 678903228 1250 678901978 678902027
    0x315060102032116020607020304030803060a05181e0606040315020c010e07060f030527071a0403060b1c1b0504090b01050f19060507051e010c02150403 67
    0x102d0a5103d8200c0a00d004014040001c280d41d00c100f030040e004020040842203034903010b042c240d032500c5007110501d0142e0820b01c0104082500340d0029584008002c100c0b095558803200083d200c10001115481551401000c000030010300c116203008104499664019920b0031800150180c802c81c00018010716014002d4121084c03907405803401c0034140c034020f1000c0034050120b40d0781c4007809d100c0c07400054603050350a0035460080c49024090f01c81c04001c0041d005901e0741c0c0030811445485200e01c9407044034000110003195480c0f114803460103103100ca82d15459410310106039129903188520818148403000480d10500394889043d45d4400380b0a0604803504110010080495101c140c0040c10300001804000844190038145c44084680209418a201c03c0c8a0300203000c1281e8034015198030003c2c090f882c00360010300f500707620440032240040300100769405c3d030040342d0740b60344040c1c0e45603580e00ca00719405010b6840610b1140202500e10324161300d00403c010413401c20400c60400c400e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 678904478 1250 678903228 678903241
    0x9020d1a030a20040f060608040201080c0406080411030c0d140f0601230d0b012619020f030309041a0f120d180305150f06030f030702100c1203050f060d020315 70
    0x10082c00981c5d241035010410559550800303845140c00720340490004041c0700000d4642403d4105031402d560f40d80e915030115950759554840000c642d0380066915108602074000380d90341d9511040d010a21035400011070002002c41e152411402c0440c0620b1504440014808004070300804502802d120039504050400302c000304440245900300070b001300010700700100d9110101c2148501041d20842c80c880004081010710f42c684000490204a212039007803602c001d440d1203102100c0101000b01600c0c030b80002a00081d04a03411310040305640d01d10b124503039280b441d00b460742601003102a41c651a0344036100514540711180000004c050040c2607201d5050440340182403006107912001f195404241342c0440b003240c2804580e400c003449101c80010f4442d06000c00c8500540550b4801103040402940c00c0013000502181014108542d841804000c00d9083c4220340c0a08000c0c0c40c0041d0500f00b82e4601c001c4000002e00c81c034040c0e0280c800b5000180c0340014104c00b01c2c505100212825240c10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 678905728 1250 678904478 678904481
    0x1080a091407090c022a040e031611030c040203040c090c0903082a07052d0d1b0605030f0f041103010507032c030f0c0709020d1a030a2004 61
    0xa00c82105100702d11001c2040c00460b4040c549054541c0c00b207920020785200004114041b20340560280c0700700303946450280c207082e0800217400c103094003941e0a100e43c513149154a00002c40d4256a5403551250041c40b42c18140091503054106880035861850a600c13030581e164914420b811100b50740d00d0401010902c90346402c40a16444101c040d600d80c19a034030030b40c000031845c0703401034071003d01203100540c4c14000032405c049840180485c0e54402c207441003110211040004d1111130b10546060400640e940040400483d02c50426003110010b48010208880019004001801020010301c40840c03140007086501c82c0510f10150032641d0b913844d04038126040c00e1140c2fa015030030403003400102501070700035a000e1030f04040c0f002044a542c140081e1200c04000044039142c00810005d541085008001d05400d262941100c0740140e031040d0103030407031740409407515020303650352881ca000c9001d15040746003a075800c40041c001c14045e42c584900544003800403c2020388040240409074556 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 678906978 1250 678905728 678905753
    0x60603020d030801140f030c10020f060a0c12020702221503050319020309132f090f040c0906260f0108010b1c0b07030e0f0a2001080a09 60
    0x500146040c41c0107203406000100203024610b80c80c1d1840c121843c050514580d10002c1800050003082101c0781c040602418403000b1100c0c00440c02140102032200b0070400c81540266a0b850300040d9682c903250340105030000410000344818010020003015a03191740c0c0301004040c4515460118001e000e8220008000241e202c110011425030000300b030080100c041e18030f0340300443d150740072031444a00403030300e070320640301440d9002010180e00c0072110202d5009803815501201c244586480a140207100b9505418006501170000140801e007400d082803040c1e0f03031500560f014014286d085030044c1c10750a0380d0103542c0030408213844014121000307060302040b110040d00701031158103001410500544d000d0140100175030178800e0500907400c04209052440855404414402c6c107240c1d1105040c88001e40f11600301915800004061541408600214450b10000b0140c50003a881c040d00e00701c0300d000d1400c00035040172560481c00d98010400c1640a201e0b0400000c00c010b09240c044002c050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 678908228 1250 678906978 678906983
    0x150703120209030a0309050901050627060708030c220e0f151008161803141501060314070305010b04061112040605030709050f060d02032a0702091021060603 69
    0x104108134040c1034200c50324030b0582c0d04c10f4943c0c18043c2c0c0c940c010701080344242c2821044070001005840c0307031307100c0352000c105240d080189002e15041d400e803107094040c0c1055030020800e8900040b0314580b5035008049803211054443c043c2110351400c01c000102040080690342c0c041c0b07501001030740d640c021500d00340d0802c0c80204641c000d0780102030000c000c0c131001c40d1130f460703404030a5650001440c041c0c40c80300b5403e0350114441052505540da81180c19424101c80690307445009000d640c081d0180700c2450280000c0d41c0c0020340003509081c14084103001614100c2490324010040c0000001d103001c0390b080c0c80b11400e041211091141e252890407002c0130580d52242004200410b911754440000e50244080343da0751014507440e40204842ca040c071170350480c2d1003641046072141c0c54913660059036200d0341116899105940000c0380300c4c915021440500d034245400503254086180c4070001c682c000200025000887e13013000d41800b0400000b0454003d80320100080318100807207030700040055507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 678909478 1250 678908228 678908233
    0x210609011a0309010e06010b0409060f120f150f0e061605030604150e09150a0e1504061b030c030f02040e0f2805100b090a09051305240615070312020903 67
    0x44e525001a1000e8108ac010300c2806c6051280000b03000761485c0c82d1000f910880327011400350180755903c0c6803141e01150742c1100e140450004541c7c1e140d0b5a41b1a840d0325129011000ca0906101d1440a0810100804003100013840070314070181990300505596102d041030b940059040342c648200b22150195602c088200e800340c408110f000c003c0801c6040c146e00c4900c2d40325883d5142c844000d801e80742024200c05041e481005084000085007039004d4002c0d02071100010300c4200d59501800e24003203107400501080d140e90055915681c107118040803001c0810007141058103009030b54500010162001282070030102c04200599040b540c68060100c21401402500c000812244083c1c04c007191050307901a1002e07400030301245040c0440e000c04c10010700c610f01050030147d070640104405040782c601e03952500c21034000501e04000c01a40040c2e40040c04082c0d00c0803854098400000900711401803619150117504040700f2025900302a605040c000b00001c24122070000030300403200041d0380751 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 678910728 1250 678909478 678909481
    0x903091503090b100602060f010614090d0f0606030b1308040306050c09090906010f060302042103021f0b04050a02091507021318060609110d0905070308210609011a0309010e06 77
    0x21314000750050100c0b00c10f5000d41e40b80ea80c92007407090b03d15031b0911440e00462a04a242103d600c0d40383c009114144d0020861600d40d516512000310302c8130400001c64070320b81d5078001070081c41505260260300090902d503200008401d41c1d01e44807a4040c07440700510305529003000c01c4105101c50f082c0e406010019042492616020300650365680c000e10940004031714561000c1079041c8603008030b50548100b01d1a215502c02540c103400b40080107100c0c15011070060111003c8802c0112403502c1202181c100003061005501c410001140d07000350bc006c10340344c03042080e210700fa111192882d03030080c86c81088a0b114121070001c03d441d50254400d01d004146480e480d00c403031400301c40d0b04a140500610381042902d8854207036200322695181c494008090600807030a004020340c10a03009a03115009842d9481d6070b07036454039042d0b0001d80c0700508804081136420050404010420340c80f0604541c5100a9450104002500040d1014504150000000081ea0b100094101d00019000c0c80e040320300c903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 678911978 1250 678910728 678910741
    0x12051c0f0e03010b060f07060509010516110c09070306060306140f090c120708010806150f0607050f0d030203160f0f030b030a0b190b04050412180e07051b010903091503090b 76
    0x12070340808012110b0310309c1c11020481c00d002c1442840e114801940c01e00c0c9400700c0762002520b60b6200303146040440e1044a0aa0603e929141c00040c050185903d000c984035042100240c1030b5240f42c0c01c41d40d24001c0c403044040055a400c80c11011011003540d00c0c540d40e03220294400d090b4801c055810b4040003500c420b01c0803030340d0b00030903044c1280c0088095512640715005800c410500503241039078403d410303a007180102d15007503008007840c40c410411104007890000c0024145070040c03504c40042540841081880d001d20000c40006403a64604003a101c420400701421034140100503000301079840b0303215900d42e101080005c14403a0040101012440d00c421612085004038105000c0141404070140450038a800b800d030045130701440f16a00c001301711300d0407904e0320384040d00d80d0440d04141c980040c81c1d078203040b0300d41d00070f0701182e44e00c583e50645c0f0004c480e25484501c4201c4087c1c3e161461050200c0e03441040442a0b0b8021041d5158600310b590040b8054483d81601400c44020303d0b091003038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 678913228 1250 678911978 678912007
    0xc06010603020a050f070506040b2503020a05160501050631021c0f1d0304050f1207030b0906060306010b090306060d032a1103010501121202150112051c0f0e03010b06 73
    0x42741c1d1040711a00c2d5180c0d01c0b074226980381051002003410400b541c4104c00308085c01398024247d54143c5241c0304d070400503544c0c18003099a00d1101e056030184d42d0381051140c1c60510752580441ca00314445900e03108800c04500d265410080303001c0300c45440e0b02049101040048900c074490607001c1880c18020141048100e0005044c404c0d03091080f00c01c50b040840000101000740d0701110030003072501c5c0f82c4052100a21566206041c00c1901600401c41d020000a01165945000d4411030b401810249010710900d80741c0f442c107030000300b8503a42c1480202110f513130000300e580c1d120f50165250851a049440d00750781e4060308982604a10b1882c050303a640d0002e10112030f8040c40d00410b01240040800c000341400c90781c0138054a426044d10303241750404034804206c000c0455091b881103c0035403010b1801c51400031030a070401b4498155844144050100401c1506a2105900250b05e02d1003408c40c0c0c0034160851000e009014415004180500e43e035003940300c41c103005005003d0030743e20b0700e03110000c84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 678914478 1250 678913228 678913231
    0x3040b1015030e07140a0308030c1b03030108100b090720060a0207050c090108030406140c0109230d020c1009170c0a08010b09041e020d08090406050102030c06010603020a050f070506 80
    0xb145102d11880010040003483d2117190401000d0102102ea80c03c41d1280d403802e0380001c012101c42c1c101040320319201003202001c0700c00745100801454880d4100014203040030003008062440c24240003d942459841d91201504a0b50fa41030021400301000784603601d0341c500359040d02c52030044008000b07400d0b0f981e4000f0071007507100742c080c0d0340c042e003c40040202c00c00080c054080e25134014002442580d01441c00d5202d000746085413076080c91548c104071400e4400c085003c0b52002c40c820207851281d140400306c22410758402c0042e088460301524025138420004030302510405848420040c1940200d00d00c5015001030352381c002c803250407222503030703a43e04640c0561405010004000200401e0601c0355081160f0b0040c8900f400382c846840d003801c00a0381c900d40d42c1009070340c40c0e40540181e485051508026100355041c5880c0c0c90f0745c6041004540c100d620440c1590802c0243c81c81880022440b14192a001d0900503140c3c00046c804541c41d0164a180100485000074001d00303002000a419 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678915728 1250 678914478 678914501
    0x31503010e0d0f2003030105040c09081902010912150f0b0307080a29160e06030a0501031509080f160c060c170a0f030e030d2c0f0303040b101503 64
    0x10215a031255003400c041c4044e0544072005400900040c407061038290442c02d50242c00789000400561a44103060420008602d411103240480014038110750b08041c5080c0104900c024a084513201030710b451103c00301580701c003c01c1c0d0f55119214201046141e120400d002805022900c0c42e1b80c650781015958015084180c6208030301e5411f802130b03000c1005080c5510543d02c428150035031506400c0300b400541e102d00b408280041403010000703588030480a10300c101482307480803c0039403543c24841c07130003c010311300c01104600b002a0720022a503514100c415105440d050640c2d00d0f90100401c0010700c000d0500180312030500c80000944550019078800c0203401215400484140b0a001c81440c4c8541c03101280420103800484581500980c031039081006104192440c0c495041c40728401c0300d10301a2a1200c00264044224001012150401c04140c501000b805841c1d020503000b503603400014070041644000a00091060040100340001010484047c45405142a1002d4007910181804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 678916978 1250 678915728 678915737
    0xb01140a05180d0201140310090c020a200f0f0a09090f030f031406010c0606050a0b12010806040b280f091a01350708010e06011a031503010e0d0f 64
    0xc0700040c0c54012081d40c40e0f00d90584031107415580659441c105500020000040c01402101c0018481d825001d10340c10341c1c1042d805440d0400c0c40e40341610b151981c0034560580c0800b9400c03119440c2d02d9480305000340703001c101c1d5a982c40800b4440082d2018040d508044045c03400c01d20b500c4200880500318081b158400e807283d0a40e0340c0103520440c1192051904044c402c00036402181003035001d060382e0181e035801050003296280e15400030a06100c40396000203140c01d00040ca0440030414400e017103024200c0800a0121400c00c0d031a20360452034090101469030301111681c0701d003009a1203905011041071241030180c2040300851400800703040d9403d5030700c0d504002d0800711912110086074162440c0849101315080106058640e03d0f0280c2c0c407843c07480c0000c628440b400030b010852200200340000000c98208502c20525041000c1a404055005000c001c9003885a074079505590b800500d10500482e00c2d15200c0000b405006040e80f2840c403400f8041c610740002e82e010755119081c605a031074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 678918228 1250 678916978 678917017
    0x11100e010c32160b0c04050a060509060a03020c03040e0408070b010501020607080c0a14070b0a14090c01051e0d050105030d0507021807020f03041502060a0b060306040b01140a05 78
    0x514501d515a00c4400b1070024100005218080040c003800c000c03501000c410103a080700340d403941c0308200183e03a141d00a1070b000c0380810240c80c00b440c0340e101903c01440d03d1400e003105e110108800d4000e03245800107050700803610b030306040020800d460090554116072503082c1007504015000d6072140006440401748000003040c1540001001400360b012942c2d589119035940e81e080ca42a002034001030100007031451034164840e40d1102810302c00c0d0050207080880c0c1440c0740890301700d68064800c00d003070f140c1103402c000c00440c011450110450080c01e1069540c070040d41d0f0914001003644003d07152810120300381c8440c0710f01d54480d605a400a604403100f450410500340c41c14020b00310000e510050900420442c2011119200d400c100240101c481c00c0140f459110300f5904160803408402c4c0c80e422503032003e694100b10f85074000985c2c1c00200001c60340c4001003080c610004088174029070b00c07400140e0043e40f1400021540301041c1c0c04003034944050030300c000e1040d8010914441c03140c40b03410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 678919478 1250 678918228 678918257
    0xc0e0109050d0312060815060a14060d0903091211010f02010203150f151c0c05070218060310061404231602010e010c03051f0f050111100e010c 63
    0x440d00016614000c0c031554070545680d0b0300f211034003691500c0030100c1342c99a40024829108110105207203113010042d50039450000103009140d040c42e405900c5004240d04102503948032681140d83c00c08003001d010a104000d42002e0303901c1c040301d500c03d006034040d11001509000380100f00c91440d2200740d0340c000b00d0046110040703080c1c0c04140c4e083c514080013010802424038051440c0c50341050060f0207040319141c00c1e842c400054004440b10b1075280713042944010030744101c4c42610941c9005090071410942c042d000f1560824a0140f681d2001550b0340100d02c0640d010808a86907001c420000d000180e110003000010303035006460325014504080841500c40c2a0174a0000d085001031031448181e516102d03403000b16046040e0b41d000395540c1d81c240c0e121400003030003100034402840e1000b1482e410030020150710291804503a120300342c1c54460034000c00403110385000c00c680c001d10740200130314044050541001014421100c1062a1900ea40e261481c1900304504100540d102c488050140e007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 678920728 1250 678919478 678919487
    0x3070b0c010e01270f0512041a0f0a030203090f06040516080703021e01050d0203090105060a0e07202506140c0d0f050714060f0606070209010e090a080d0c0e01 70
    0x4607024204030382d20f00514001d00031000c4285045c011038120f00e80c5007564030344504146015404c41440c0100003018010015001c0810040140c0c08600c2450031001d003034203200c10b00521080f001015000808515441410071446216100380c0d01540c003a410940390203952001e4145040340c010901c101c00145000d80441c102c011650054540c0d20304c0d007118049803c030104482071080c1444410b00c11a8508006d5101a52280d00c070900001500c0c2055400c022400b18a9071080000d0110002042a2150300010f00403035483c9840140308030001c0c9410684c1800750841c1d013441c18404d00f058901c40d00801114540450b405601c41160004011031280403a11810040c040036620031890542004e10915003407011009a03c0c25608204544d9111f0756061440c0d4a0140194480e0044c05171903035901001c80d4010314200c850030f2030890f0b030341e012170300c3d4800501c03d076052054403000090100d14240028071140f58000d4440e82c0d54018408240b009002460032440095403002031240c3c0c55005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 678921978 1250 678920728 678920741
    0x3011b080103021203160503071110050711041e1401060c020915060409090812060438060a1107120b181e0106050411070222090203070b0c010e01 64
    0x265903524106070300319001d100205408000c0d00034070384001c1001080d100044240c003201948660081c60342c079211801c101c10113078210781c40390b449000e00130413035901c0a801208940801d9071003a02110040d14a030300050040600c401003030f1100b255a85c0c0380074414002d902450190003120188206030762590011202c05003044070081d040990380b00454200b50130004200f040710b10050110746080e485000070020750f000c48404403615a0041241081040624001544100c0c01d44080000b400502184910420b003030400a00e4186000e580b4105034070326051041c00084040d00c0300d0b6940d41101002810705081c001900d00e24051480040340314004002c14694036904149820420f40f074401c0284201241d0070064122841608900000c8030500380d40b4800c80c0420b9000003a01070314141c18881074405050b107a00e60004c0c10001800140d4401d04140100401401405a140e03100c3c48224001c0c4880f000c069410b2046a400044110b151802020083e440741300030b1080b0f83c5402d001764241c490 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 678923228 1250 678921978 678922031
    0x815040803040f0c030c06090305060f09030415030b091018110d180204050106081902090a06080417121b190509270106140418020d23060301 62
    0x30400115020540300800d5522043c0680007640420755a640e809140800d181d108101042d400201007003840350038000706611110a18020300c4a00d0492600758682c882d60041440038490300100094184c46a8401840410068200c24680c04d012600d000d0481071032103446003d43c01c0301c02241c0c40c0301a13030140d0500300d01240b2405061aa0403880e00c00541100704c492103171004144900c101581e2a8090745000340b00b2511342c04c0d51410900300041100c16031108080380036004202401140d228820402d007211201d184c800003940b00c030301e00b54034103201c4008080a01071010803040003242040c0101c0d801201c5462506190b40348540400143d4021030702d03102c04111500250501013030007440144442e1000800704070748410382c0d0380c4000031000c00e003400410a040800041c4085c1d904202d43c03200d100b90340c0b0251800c04d45062031100c44915440040c100b400d070041001d1040382444c4d00000f0040d2900341ca00c01044400b40301c0303015a220100c81c1c3d640300c0c0d820160106c2d24583d032400b800e0303034141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 678924478 1250 678923228 678923243
    0x14091b0906070c0504150614030a090203011d06060a03030c060f0912031a010905060307030914071211010203190f1701090b090a110d0e0c180901050106081017010605090709081504 79
    0x106000441902307030704000d108805c1513450b00d0310742c00142c0e400e2040b01ca0306071680480350382810703403141180d140004c01000540035601c101c0060000c01c4e0080d00a2034403640c0b0a00100300602907000c4036000d89a406001046c4024106c49a0f6220360160013158448200801c082001441e000c0119040c2e0b0f29841409d4000004001050806109070400d91516014040c40a2040705101d8801d151950030361000031410b003c002180200080786c02d83c0c01903100244000c5003003000295a000d0603418100001d0140701c910980140d216018001c0386800340a0310001505070741c0d44105400280619004091040c3c1700c1800241202d0514400e40100000c0341700c4103410000810b298a00034403100500380498400d20940601640e01c440318040081301d06800000c0c03a040c450a960b0941d001a04541c0c10721a8140c10490f09190600201c1c040741c1e4418400a1a0848803910500500c41500040d4100b0052420807100c43c1c1c01151031400c44821804550704401c1141d80403000401c1030b03d0040162 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 678925728 1250 678924478 678924497
    0xe0301051003020603040318140f1801150c020a09021801090303141312060c110f0604081b01050a060f0603150504050c0f0c150114091b0906070c05041506 68
    0x40c2003504c00b85511034828100b086d040030084285c1c1403129400d0b8003e82c1c18282144154105090a00070894922030581721084481d4030350300110841c40050182d1210742104040901c5032500c030308008a565900602151246030700e54044501a601100160b81a0701c2c03280714a60055100d4a10030781140d0701507403490040094440203e0060b401301e40038454141480002090070a015007002c840c03241300d8000040d050500420161030351801d400c03c40e15540041c2c1e401c000d0018080360184d8025448155544e8030f000300134845040c00d50200300c04030907620b0801044a0448542c7c0040301b40c40d5190710034840269100c0003201618411010108058640c01c410005810075130007640d003000c4d81e200c0d4103040009020b0388040d1078110102d0706403070394000e641caa0700c421402e100d40c90140001035025102201d0742c0300440c51028019020381c0c4104c0d08554481082070b10881610f950502c001c260351368840481c01d01008645440c052644114944551300410f001c0c61303c02d22003101c4290300e83c040b04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 678926978 1250 678925728 678925733
    0x160507080a021006050108161101020702210105010b0301120312020f0d0b01080c1e03070201060e040b10150c021302090418020a08030a0207030f020f0d0f050c01080601021e0a08030405030a0e0301051003 89
    0x780c41c1081c1c03a050ad45d028480305006031784000b0a20060904045840c1c9507400d1082620b00b5a0f0060b03010f02c0c580b0908000511002c440313892a80d0071190076040140f44600d945580c0c8000703110b01000781c240f070480404c0c0040c0d0894281c0000d11001c03002d036220300b1591100403240c040da100c2c21050b115807200341480208071100b1707100a59804075a60000140090340d41c2c2002d985c03c20100c508031040740c181010000544a102c10078400307031503011004444c810720000007410b600702000020784151140d002919070300c0c05580480700d00070320161092000c021554a41007003880401400ca203d82400706020406100000903030381e140c0c404d41d0051a010b0b03c3c64036002090041d000c402c1e608071211030318499140d280e40c50301f851004e1040e02207810517a03040c20a2030801829100c00c6040004090600019a0b400030b01404080381c0f10710306540810120000314940890090300801d00c100c04020801404004070141040ca01d0a4845c000286500c00405080b00d02c12a02e80b0b00c03940014809002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 678928228 1250 678926978 678926987
    0x5011d15010c200604081c03060e040b04060f0e010c02100203130f1511040303031404030905040e1903020f060a0e0303070302071a0c040609050406030b160507080a02100605010816 79
    0x20351202c002603940711142d44404075040f036202d074100358100e1f400008030040e8001c0120700e10300348032058074080103140e00380011801c40b040c0c050000b40c0709483c83d10110381805100c1d4400c092240344090108501c400703001c0154041c014860208001d80a6a02c0441c81102180200da1080504078258800840d190b42d98030408080c4160a60f54803c90464100d984951407103088105990607202710b4a562441c03a00070b050340c441d800244400240c0000303010001c1d40140385402a42d004a4002c9081c40748000290710700845074048600d10f20a10041c1410b040d0007080090444d541402944d01c0d80c0e544c5580c0d0070070b80349520510440e6600c200000340c0c1081c829070140c02e2452003840d140d01c200f413903103291805048055035800c503450000101004102e402024401c000d1109031014445603241d92a440c04142d0001c01c1009585014080c0b801e42e02d1041c01100d29959000c01c2d82c0d078079112141c0000750345a4050180b1004140703842030100c1ca40d03020700725491050042091039006a10801011903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 678929478 1250 678928228 678928253
    0x150103020c030d090c140415060f02030f070b100506030103030806060a092c070201140417070f0309091503050c04151703030f01050d08040b0c030d05011d15010c 71
    0x41c14001482069030700e40c002e000da82c254501881800c00c1c0b5600380168003801140c41c8070345611880c07502081510310130314042c0c1e0300d0440e4400c2c10858000300d00d090003039085200350f040700406a20000b90325010005078022040c0150f03c0c0c221100400e6454070103200140c8401e0101070049222400003c00314a41000180980703140c07841c1c45010999500401500a0044d001c103191103c910440c82d6030481c01e03150f24a0b40846a44000d10881c030442c03038880b11740000640054001007440c4241442051040f048a100c16070160164030b900d06641802020f0782150700504010700d0400004802c02029000c0c11000e480e0054081c10305021aa020070000304400c2d0500014074a070781030001140e981c1c00312803155800703412002e156246806040003440080580200f403081624103447c401044400c1d0a46041d0b0703114035600c607525513011304010701c1e600402904281d06400c00d000400c0e1620f00c4c49001d0b6a4004462500d20785490380060b01aa69070320486030360015860110380d0300418011004036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 678930728 1250 678929478 678929497
    0x33050d0809010309350421020a080313080106050f1003020304050f10020a030b040c17040c2303102d0609090309031709011d0319030305070e01050315010302 69
    0x54244441c2c0d48203030f801022403101203502e950048000c0d202210050f100b032890014805c3c01c40c909824100c500c0a2412000c200b0340d1500300000ca01c50854403801c01040c081c2c010b0364101c80d100e442440c0760106510103802841034a5081c00c0c00010f01e814200d107031807e8220000c061074041030b000d0000318001c2d00300600944107441640613101c1141400c1c090f901000201a1015a680502c042c02400303507815688464003480c9000403104a8540c48900c1420203000d03c4104100c60f1107074100804910007a0708a486d22000c2e2254014013007071710000c900365104003542950144071312913130b40000300c8100440900500043c1c80d8500700c1d440011443c16020040a400001c0080e1100000b40495031120402c5000c40c04001d018414443c07030703c00303a81080850b100c03180d14111007000001d101c0801c2621400c0042d04d420410016a81c00f801294103551005645c0707038090105040003030141c181500c603103010076100d0f442041154403640803a881540c141c0c98402c214070f82d50300118000e45c0b1101c0381 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 678931978 1250 678930728 678930731
    0x50d17190b1003060f0b03060307030303050c19080f0a0b0901030821010b0306090108030f09061b031918080c0d111507031715190933050d08090103 65
    0x80c0605542d034032400380069a01e690340018070b681000404480c844460b00b2a4580301414010410241c2e80016034801b0b5035814070300030840c0e13200d8160000c0a4011030030700100e400f00200341c0ca89201d50218429110b10724090345204682c070b902540328110740300140c0d034603042032103100140301064844004100d08100c0c0300d084c84003283d008007130460415080c1c01800034808000203109003031508443e10390160500c0805140b4002d090584401c50b80320f2005401e002c0e034004103900c180310030400300c5404400800c10980f551510411045c200600a101040010842e40b6016041a00c2d44140c0725054401d12070082492007070070300c100000d60140702d000302c814141d03084024405482d00a05569110301014020b81c89400524020304a12003100202c60901900810040c40f90b400101b16082c0e03102c191448040c102d1900264600c819841d00f25030015403c000c008041c045c0b00000c3c80f12005071080c41c1800301c1d44040c4030f4000840e000d10074103038403d41440b05400400c40c854010021403105050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 678933228 1250 678931978 678931991
    0x8070203130602010603140f1009080d1803030609050705041824090e030307050304120e1207060e030a030548101422060216050d1719 59
    0x4840c10007803140c2011005075101e0504108002d075280c40030030700a96050141c0030b2401c62422080d62800c0812241c01c41548031100481482110012140040e50041c4103014070064409544004112454220f0002e4030300031000912407c6845482c1c0140c900b542c07444c2c94580307007040f804200d80800c00700c0400103603070303480100000c8141d80801c03020042c400b800040341c0386004099070865144210b182000d4200304200081280c2c49800c890f401580079240d00780c545841182110000c102c85184c0f038003e5088021560444000248001122900d0342c40c0000303004084140350700d901d04044024045081480355145965404603081105444058045d200701d0403c07903025640ca8803044124030400e403049840c0c031124400d00c0102032a4510000901640b00086071903078018400610110344100b41452400240c50840c002d084520b07000001903444024542e0040121508004201d41d18850480c00b07041990045e84032031042402c0c000d29005aa1b41c3c0301c801101d068004604007140b175135841 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 678934478 1250 678933228 678933247
    0x10f120e0105041b0803030f060d030e0a17070803040506031302150f0706060902130b1606092111031801110a060b0301050601020307111005090a141503070c0308070203 74
    0x8503903071049004444c1c1010304100e44001c0244040ea940050b800b0341c004208000358080e1201d06203030030000035a065510a201c03400c01721092000800782d40d03804045100c0015070f40c480e1403103d04030442400251416507070341d050903583c3c80c4240e219203500403405200180001003150310501205001070004148120403900a40155018104400c081e28001ca189001e0010034411040604082c2204600c3d00c032030448000788480c00da2040c80b510030030000c1d41e603200c2449412410001607008a003070025240f01c0c0b406c682c0426140b80030410341218400d2101203d03210380d4017504180402c8020f181360512140305044c00710300050740f99052041c840300048007800c08100098129000c0c1d8400110419800205829100090101e034110f60040c031044011580034441c002c0194012503064024048020069502e8000e0344002d070f6009140d400c0c001102d402c51410045410011100a26440544803940040c1e00080c1c6004000800e0007a2000000e8050100740c2d4106015004507400d007a00c24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 678935728 1250 678934478 678934481
    0x2a0213110f071110080a0c02070f0303020a05151003060c05040b0a020607020609060105061206030c0a03050607030c05071a0402040f02030a0603052b0f0e0901141201050402010f120e01 81
    0x121040501107200003034050911082c10003854010700201c40c2c0b2446605024001800d6240141002c54460740d11907150f81401c4c0200f00c0100205100c05200704030740ea80e400c010b501c8070620801070380c4a000350411402c8020310041c0891103120311509815906085803a400000c1049540780703c11311130200004035101072260041e104042003035004100c5880d2400000f1f00303042026001c030590703038081030040c000c40da00c00003580d06011000982c001d280e03840500091400c010412440d4002c002c1002c01310070f00c030020404072b00c1112103480034401c45007424011989481800005010640f14142c21604541c1400420b034000740001d10116800503001181422a8000d0b02c0101d86190388541c10020030801f4080b500c1d0196401c0140610f4040a4178040c0698841d003200c10200700303204521182460141180c10300095015041c285191707190700598012207003a0644600c00e1002d0020080f06200500941d4404c2c0ea06941d914140030f020f03c8140c1e403800440c800c034015180c030781602c0c5c01c40007000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 678936978 1250 678935728 678935737
    0x90a020307210f060e420f09040c06020f060415020f0d0e030c01060801090804060f05130b181e011b05100203041b060e010c0f140d2a021311 62
    0x408400040a00340f507046031244001000440c0b81c506c403004080c0300d409a050303c595400600030300b40d003840c1881d1500020540040d00340000c1e0311102102c244400d20006408240690780e0940032130b4031f000c0446080550310325040324010501a440301654400300c260360040c1610a0f82800300314107140001c4d2040703050310940740ca0100035503c042400e12460200740229070041c80110001c000024040c5c0b905007080c45503001d80d13000e014445026905480c4940f04489a0040b96250043c2298a400c0c062403154011442070703980f500c40340c5902c0290f14200010300340f1b40000c03004101520ae4248015115080145a901c40c2740a41c1c4502102140080c070100d1442400103e00503644c0ca0145481c019003501c0b14035844501c004c1d0700f400e000b2582c01800300c0507040800d0800d00d01070503141c9080314018034081001807240d0000303601c080040c4400114040794802507200c1054025032403250515961001c40300b614425070312035050300541030046006640711140040441c00c45000303482d8560a910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 678938228 1250 678936978 678936989
    0x150912050d090605090f09040c0b12010f06080105060a23040b04090f06080a1401090204141605190806061912060e010e0c0c0705090114090a020307210f06 68
    0x1140d0922503074240d121a0000103880d890901c1e81c240070002e008101d03a42c1c0350310701c3c05004107241030202d0180031255110030010300b0913140c029940c150702c040081c01703031a00380b04030034141c1d2070b0701d0001ca0041c0c020b40c80203050310005401e003410080c22600807a00c42c0642c002945c0b5000c0310a040310100d01c5039000803c050844010800d684030b141c03a040d81e0440e480c1400a42603149408010f20500002140b001c0d84141c002d02c0e01e032031091030000791900410002600a502c40d1030800d00020101111140e24407030706410305002c0702c020a0040c02e80d43d40c030401000990303104151003060704803800740b0b03100394000d10060701c7c0d182061948c442e90107118040c0806031001c580041d00702001d034400c0c0c3c0240d2016001c640d402c0301e82549407412202d800c0d60041e010000900b000715072040102c004100c000000c180080401809582d940c0b0b02d08030192a4600081c020b40600e00090741080c49802280d0107a803030303640c5030042c1c0d0000303942d000d004403181c20300c880201ea15440d599407180b0950291001809 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 678939478 1250 678938228 678938233
    0xc09090a06031b060806030109170c330a3c14010e0c180906010e09151516030f1107150314060307030602090406030506090d020706021615091205 64
    0x203041031303000b403c2d40800501e000d01c01c2c5c0c10007d0640000d080c1b0800c841e01003150103246030315050100c244a040c05113206051007c6070303805111200e000c0580034103165808802895111948031801d8920548012440f012105000040c100109040c0c12610360540700c580d00d00c42c0c400c1c0908880500660f400b0411031000019200014440d441c800c030b646980148100344410310b03005913600c01c088250000002d16102d000708500281499024030250503110ba0028100c2c8402c0c81c020360f60310f03211301c600180c0c070b030048203580001c0f56140c0e0804200c400d458803020240380001d025590864082818003d08010000081a0f603078030701404015030000352403041a9a034100640c082e0080c111074508c1250041131000c2c1041c00003d4402003850344c203481e0400b80160396442c1e8035000c240908920780c4020f000344200f00402c5001d120100b21030914a80a5084c0c4411594420303003280c0d10b2134269011801140844000c0024841c0c00003500e042007000d0a00ca080d00c1c0d601d10815414858501050711241c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 678940728 1250 678939478 678939533
    0x307060608060705070b0106120207081308011805102313032c0114091914040903050d0b0d020a17061605040504110c060103080712080c09090a0603 65
    0x441c01808100c2d070007101ca280190618585494240c0164818440c000c24000c204030000d41c0c03008180c0444100c0e54001651540c0c07042692401502d001451241081551070005a482a8100d107040083c0e07060300900100320700350300514044000d2881082c880c8020148401008510210b03006e62032003910000058050001181009070000c54010200881024481598100401e461801d02c001140030728011400c080a01034580c03440c4100d009281c0d10020750382c14800703c4150000c0b6441a105026041080e030211041032200b6104250b100902040041c00134a403100100d80c003d200e03184000345100c2907800706401191044105410034001081949208260348404100c8c183d04840c1031ba203004001d920003074005116016030b015007840345032641078445030500c24074207803013503540c0f610152115940e492400a43d02e5100490440d400e007600c40d00041803900640d1018455000c6441c41d51030710300e01c00108052100001d0148400c540c0d2108080081603034511070103460080d480702014407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 678941978 1250 678940728 678940739
    0x3020d0f03030b010c150c020a0819122a05130308040e1003050c01110307050d03050910050402030601060813060f0f0b091b0a11030703020a031106060a210503070606 73
    0x98030b43ca600080e05000c221214072002800792051881e60100c100070000340c0010080e012420032010000240c82c07241c1c04202c0c0303810340f200c1c10100b40800c4500d45940e01100610081d0906541600130004c0254001420000d64034102c860300c039003001040c2c5803c611348550008400c0700c4210680060710103510115007406280c1c4202d80306604144003000d003c1d0102e2440c3d541503a50280030440504024290031040d0013070f40708000762880140e003d011380740500b04d100c8006008100440c1c001c0018031070702d040c152004101c2c0c0b160318003646d009009045131340c2c02c015050302c0010000d01514000300c2d5042032000824018818a90700141d030700d40204005100700d05820540d0700050100b40714050707050901c0402c041d4404c0003c29840c41c0d2480e80c0d02c4907100d4400343c0e2208800165101d0f64000052610308040c0d011030400340092107a15029200511a103000c1e940342411070340e04d6049070a11205211660309000b2290300c7c940e40034100e03140041c45a0390300d070940c1c00403202196580d407200d40a010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 678943228 1250 678941978 678941981
    0x80105100804020f04180f0506090616020c010e01120213032001020312060102031b0a050d0915031a0a0306050f0108030f031807030c03030239040b0a03020d0f0303 72
    0x34148000e241108540c102a0006600d0311001e001c1c0610541d607491413048901080405201c180e5003080c205148201942019508c400c0201c0e0841554003130712001030a071007103c2105501521050b4010007903050b981c4019108003040b6201103051021006070508421950300041c074038880000407010800d45107280006d25890321065100030410302502108071a60700000333a901c02800340111003050f0300c903140140c3c1035214041072200e1142020200c400460400559025281e22910403140040c010250803502e5a446001d000c0030b184c01c0f01e00ca0401c0394482d812001c0081d280280c1401015080e2002420401c615481240c0701c0b40c0f100200000008588240c0b030060158a01851505420b080d282c40240302c0104403036141c1402c0166584400800c01400000c0c50740610060802e0307031281406562145011120901c4034141c1424022804408845815440e98000c200701584984420040034201000d03456803c480f680e4000405a5901d00030511854060a62800b060405050040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 678944478 1250 678943228 678943249
    0x150603090d110f0d08360d0315120201030f0204090605010908060405120c07090c0e0906220c030b090720030403080702090702030702100810050102151501021c080105 73
    0x403a6044034040e1040f0310804070340070160100303626084656913a1120428402d1002d9800c00151000e88911207100300703480d000880404250208a42c480300b0b00810440545150b0007601c0c1c81c810305454100209100c2041000b08207205060104d035081d842d4500030100e800c0399120b8100581c84680811855070402034600107004860080e0105180c0303a00c55550313514040c4804443c04100241d0071101020034040c1c070300500101801401840d10000b8028140951511849d11031007446001c580980f91080101c103041140c4220a01c242c01620061001065a501c60405044d1178101d203000e56a2440d004512a001580306d4400c0c02c020300b95251030113010003542c80a076500412060000c00c0300c82040d1076000782c0c12100c1a40659444d04224114026031500071340284c07070100b0900d41540c11502d0144600c0540c1e1a821815544500490340c0d517034042809010703004200040b130000b0f492040304030300706401801120800c1c1240811300e030300c800d00b400303c00c40050f10f245c0041c0200c2c40e100c01d070758 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 678945728 1250 678944478 678944507
    0x60f060a0801050121080f0d0c120209090f0a0e1e01060803161b08010f09020906040c0804021e030d030504050601090c021005150607060e0d11030d05150603090d 71
    0x1c201c1581060100703002d480c0c2c4115a5a401a00045d1000030810814126a1600008201243c41d80c01c4002c280b07018003441111400440c8819004105882c120f1003501c0003500e0040281d81540ca075800540708071000505482480d903250307034032a450080104a54046c0c1072103010004049414902c100b0300315440c581203a1256001003085494403d1400c1030052880e80020f8030f1103000110006480c2e44012583c0801e40179420002484095541d90384041013260095584d8070703c40d0381b48000c00044600c0e4851703100c081240a808100035040010780d0f03084403d03026002280c002529400241f90104030540716000980701d85c100003c02c101407084500402d4890818464103034084006512554030104080260341e4420018400d402e02204528816402070700d29a503a201c58101103004d000a40c0086400d4410403800750f01c89032180441c0404220508081d609101030084003c0192030080d0400b0340503000003054910720b03903030702c0002e60290385084001c1c08003000c03148010b000c0000d80d03000e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 678946978 1250 678945728 678945731
    0xe0f060405070207210c0608180c2103040f1205302a030711180408030903090301020d29010203040b090418030305010e0117150603010e060f060a0801 66
    0x501104039000a040801d84115113040c3c050002040900645c0c1000004060303d0440d108100041080c1c02c0480940079100d4600556403510103003a03840da81d2034852034100d07007100042c410101d4488141403000c141c3c02c908401d8a2a0940d203458801040c0d050303400224100002d010081d017084410000c51040150b00c04801415104038440503d600f151000e58020304500010600c00048500002d0035125000c200101c00c0c911080074169920b411501c421070b01d0f862400c42c82e15291400000e803084410745c210b104821a0b540d070356003807042d400c0501a1615403000340480d4038140c0d02070000c0c00c1e030705109003800100d0b919000c41c00e0b49485548129140c00c54510103001003503136030202c02c40b0f007600da09001d0155210620340100e4001d010404a00002910090014040561580101e8101c03038003002e0360180b5036280c005c1c010440100d4203c00d51640e11035003480707100c09818090150b021400400006240b2001d58000c0e0400d0800c5030b40f5108000110f080115502d071504188000c3d0148000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 678948228 1250 678946978 678946981
    0x423013b01020c120d0906020303240a3305030f070e0d050303010e04060c081005090c2a12120402090c0c0d11330a02130e0f060405 58
    0x412816185680ca418140800a2604120310364020880009000f50241c01803c1c0b1a0720000324035200c255012442c800600b10460005141d031000090300d000d108582035907017507007160301c084143c80c1c041d14005a800070b02c4401c00190481d02a841107901400590042280d00207001032440b41220122006003802420b205200300d4041c1e4803030040d804a0030341002d44c02121160000f65a165001c403001302944070010021800e68a0180c0c00703805288034641c144135954035104203598044041f2407458000a41000402c4603140c0301d04001d42104503a0007492030510f041c060900c4004171390050310421030449030341c0807200b8010005507040200405445040c104608800242d840010b44080c1c0b15000c4000810505403901044481160304030003196245080c0f483c025201e10100c60b0340c2c5000b13000b000b110701480760f5240803100604007a84180e20003c01c07025015056841e02402a4481c0e41d800d00082d018412042003130700c00380214803501d440030b15103d1060344d030305540103185074002ca08020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 678949478 1250 678948228 678948287
    0x10915140d0b0126070e0a080a060b0f010f02030f0f04090929150409081207020a031b020d060f0b0406080a15060b0702011101150f0e06030a051e03042301 68
    0x20071085d08204107103014080e1100443c00903142c151580c02c5801c00780596401c0c2020003c4550013507080d044281c5103608508003c1c00152801d540c6c40000c42c001d60400c00c001d045c2c07005024000c100142005400750b04003500c54404504880022008a0b10501c0e681c218800c2e4401e50741242032101c41c0404101050b1070310646038020041a019100d0140c0c4e184c1081504002d03009082d82c5c07400411488801d400d1130301040017562000980010780205403802c0c00c145502140d4000340c05050f40180800042640f156228030042898680299003540d0301c400d50700140e5910300890000b0080e5100170701e0a01034909103d400062840302c103031380b11490448100800c240c4c64007560083c40c1c0901b000410f0703400311821079014100fa100b50b03210303400b02c40b400030482d0b8140c030391071a06480c81c15682c0780c000d50300e01081c503a841c030190704041d095500c00000c140e19808aa190011103900003c25641082e6a40502a15032031150900900741c600c00c41d101ca0803964031012051050b400d18000c0c000294090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 678950728 1250 678949478 678949547
    0x1803051c0b0f010e03010e10061d0112032a0c06020c19030b040f0803011e0503010e06011509030b0c091c0b040b040c0b0a0c1709010915140d0b01 64
    0xb000c1c06414000800f207410301a5031300394040c6c0c82c591015402d40300c00d05030142c41500101441e0044e1000c00c01c0040c02c004003055000107441c1600d807400082c00200b801514240d821703244401c10002440c001032908020a0591001420924412030300c82080e181001301c00303800e001e4030203051400758a03000561150a0b0080300703a0340c00c032500007100c1007245d00c403070600217400181c40300080d02e014400000026800040e58800300032400030300f1410001c035296800c050070388144100c000055448000180700744149844110800041410091003030780e034a940710340402c00201c9040072240c10100d0001428100024206503440c440d240750742c11401c1b9035464840410b00074002810b48159000001c08021448002001170105407038801c0d11641ca03044000e0140c40130b104100c62075100c4202300803200b4031140c103446c0c050178141c5803858401d007800503851420071a00f110b4410440d040110002c411450401081e00e10100e14010915811100001d821320f1090f4060503800f92031000d1909615062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 678951978 1250 678950728 678950749
    0x60d02030c040f11070510061a030402040e1e030904050601080112200a03060c02120913110d06060903122309010e100e0f0604150809011803051c0b 65
    0x1c40300090301146090703a00c0004d01d1400c400c0c40242c0c00000341e03142032101c0082c403902403a600d9801030040540f50320740c505c8031f1442d00c4204040b02c1c0041c40860018605070304501c3c00074815a040340d200c10700030046104070f0206008c103000550030010b00c105881c00e141c010799600040a01748580301c0d5240001c0403015401300e02018001002101c1481c0341c1201d0901c3d0341c2007002d80200b40c2500030380c80b400c0c1030000740048512000584118068801c0301c080a0058440c15803009101c0500520f8020071080070740101012060091400c103c00d00401005115003800746c5915640d01d0034042c150314100301d0031003c4805d400c0502017202c51900c03210407211b000180d00810f100e82d40d81c8481c0300c04010b81d800e0302c1c0840701583c00b00c1c241e07039a210b065500015043e607501085406500185400062019500c80c2e0300401d4007010b02e03140751414160045104a411144960002030000e202090860300303801100d4086001900c0080c01e0313491180d0a000c5210000d00841c420454030904d5030005000c3c414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 678953228 1250 678951978 678952003
    0xa111b030705040b06121b1b1b031b22140a050c0403110f040603060c020115030213090c0b03010b03180c0f01080603031308010b0a060519030b0a080d0c0308060d0203 73
    0x540000601901f03814040d0300006048500307a00c2e2034113554040e80f0740901c0d103c410307403419110341012030003c905484021081258040c001e001000100099072454041b1182580e40002c2007400070041d8880846a00038061258000000d1035110407408000c0c0100103050300340810704020034080400a000d007118102c82c3e008a000b82c000003e038000c41c0754041114641c0742c0c0715141000c00010300c00c444e042150307807041c0c40d4020070440946074000c0c1c8022406000280d0401d00340c1ca41c034009511140d00c8003c9003402099400501a030320083c0340d045a000741c000c4180d0b00004000d004a08000108144140266101a00c0c0c591516000b28803021481c4000710304004005000c80c25548060041f0340c1c0c08a45a800303a0075607a00e4498079406080c40c85a800d01030b04103400000b40881c490300994600000704d010144002c1080e4008402a00040004a6119003401c1c00050391200400402d1a00d21403611180010300160070054070101c4000c150b035000380d041240ca0790040c1e0b8042581d50060f507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 678954478 1250 678953228 678953257
    0x15180204080f0d030b5e11130b160c0605040305071d06210109050f060f0f070e0604150c02011409010e0910030501150e09010c080c0a111b030705040b06 67
    0x100b01c2d0031080994484c030810070407030185103140000c407004100403007014649104400e0150312065641040039104107108101c05071034000d01031105003222801080ac44000c040300300380700c0c0e407181c070b40000c0c41d81c0ba0b0380010049640000c1c100304104090041c00010907492403120b58940d00b09003844181c00c4000c00c03061040c0c44145001400d0310301d03000d03010384070607041c4000c01c000ea4561500399941c044500c0484440e106200019900526032100e452041641405542c4036441d0400240e607140b18841c01e15510040c140004100007031803070303006031401c0041c4e55001c001c013000303000140c80f00e2607808000e102c00c0d0080247c0707401c990300b01642c002c0c01d0805441001055441070707442e175040182500000e1080d420410f40140e0b50600b4602c0c0340950705074154910181e120203025500b05d90079010150081003070000041c403500040d0001d450200c42c075080140850388042102e81c14030240d0011035801c1842d00c2100140350600300701701c0c030103014255810424070600c600001c1e02d40c05505100d02045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 678955728 1250 678954478 678954559
    0x31107031b0f1e0308090303060303090d03051e09011101060b030112060f06090209030609060105010f0c020118090e0c04020711120a05011107020906030115180204080f0d030b 77
    0x1008030000103802c1500000d20380401c0e180e14040184507100d4402c10350010f81c5540103d14412004000c481c0210740041c0194074000311030040c0203c0703181750b80040d014000c0130f002c07144945408040000c42204c600210750340c3c44e800c090014100d21004070040f00281c1c5004428080c101c416003c40b41590b000c205001300310001840c008000c0c0c400d484c00c440d100c0e401d2080001e03017006241c001d0f2014807801c4080d250242d0340d800f8020380d2400241300b0180001d5500380300c0016280110030031400e0a0040c901114010030390380b6a032070b0031081580302900e107503078a8242d101400e00a03c0b4000c0d00590440307041d0315103003040c1c4400c2848004400c1c01d074424240c0100d900341c058420085d4906041c0d02a00901c9440e84018541c00e4079001170400f40c0c085c1d00c0703000000b4880d01d011300ca0340010040868014a01500b032000c0030b000c400e0300030001c05000e50f003044041201c0c070040020000e110803000041100e2034402c003004041d030352641c0e24203004503091050030104900301160f15003030503141000b51824 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 678956834 1106 678955728 678955733
    0xf0506160602030c0c15101a040b0c0c1206060405060d031707230c010e0c090c0c0a02100c050705010906050a120605030319031107031b 60
    0x104019aa1000036520b5000d1a0002c00c18403503d41001c01e001d61051518200810880ea0001c0f0300c02000340b501c440c1000c2c0b501420345414903a1542d00e09100b88030041c0518018400c80c14004601e4004c080410890221325480082aa011340540d48580035143c11055518a00440c20400003a84900b070200c074000741d0660658604c10205080020f4240303a14001d8600000c0003d910040520300d410121001240402e8001e0165035a24081e9070a0840f0400400c00c5440c2c0c22200304243c450399003024041d40401541541c540d01c1810744805401c01d4440c420095002c0e0319151400c9416500030b0340405510701c51400c407041c060300c400040d61401003510410000400400080d018580319920000002035481404500c25444074002400c50f04015122f000e01c0402e10300501d82190b040c080d00910f0560001d04c2454401180c8008200460060741c5195408013900100e08 = true := by decide +kernel

theorem cover : BRFrame.Cov 678776978 678956834 := by
  have h0 := BRFrame.cov_init 678776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 678776978 ≤ n) (h2 : n < 678956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
