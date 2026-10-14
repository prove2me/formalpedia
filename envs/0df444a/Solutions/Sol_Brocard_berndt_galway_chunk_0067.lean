-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:39:59.61507+00:00
-- url     : https://prove2.me/submissions/5fdaf304-3d6e-4ee8-8489-70d6f86301a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 11870510 ≤ n < 12050366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 11871760 1250 11870510 11870587
    0x30f0a030f03050106090f0302010e01170a141602060708090f03030c0703020f0106050f01030902030a0204020c0d0206070815060c100615020c01090f03080306060403120215130c0605 80
    0x3003007122480d1681d59041001c0d0b83c031024150789410030b9015040070f24001c103c042c0015402803001c030207100070504060b244441d00008d41006003004803090110703a80c59003034241444c2c006c0484c242e0030800c18070340c0031240680080000e50381c80c1c00410350303030070000300c80089980308409002c4c00409002c407101b5a80d0301d141542c030424051b4031280c2c1c00c500500c03034240e444001180c1841041c017501c000608030f22000241100440103409007483c1079925024030244980180d841e84010f22440e9416400b070000d0180c460000b909000c00100402c0c00e1142090030020044802c05403500064030496200b80c03503030308280c0c04910f410243c51010b03c1c02440c100700420952800c2490304c0d1500b507aa801c480f56446c541004540d0310b1900d00c102011491012070030b10010341c0307010103140d10000140c40d86080640d0781e12625806005d04070220056003064060b900241c2e24a02401d40c00b04982049452402e410741e240c1c1075411007842900104000411203010b40790741100c00300409a801107034006444090b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 11873010 1250 11871760 11871767
    0xb0a0c05190819052401120603050601050108090a0506070f0903141c020c011d040207150203010806180d030b03010e0d03022106011403070207030c0305160b27030f0a03 74
    0x42e910030310a54040420f4441e600c125000307580c404c0c01005042001c05002c04501c400d42d07503031482c0640c1404844401154000e10601c100b03030046000310300070545949480c00140003c00d01030034456943d0008100d410109100080c0a40c00904515000c0304401401781c1c1100d0515071600b000307100c480d51040300c5501e5200011140000003400010b02c1c03402c044400140da075500c501401b140410ba904640f000b0190804000444c0b108004e00054070b00516681c401c0c407884582d90344405004d03804401881540800c0101c158403000007410380c484074400b507902c65585d020340246070080540b03581341840d0503182034210380f500c00010011910034201c0d140e00a4041d4006881c88003a01c51805461625554500c601c3c034000ca1060710342d02c82c640d802492140041c0d0004140c4001c0d0f10a2004c0000000c2c43c0f0708840c00198010f00c0541002d0b510f802410803500c0403070b03102038107404052084400f0b4400c034151140000001c0041c1c1c504042c82a8040782c101a03628103518410300490b0070701410b0640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 11874260 1250 11873010 11873027
    0x30806040605060304050a0605090d0207050105091201020408070f0509010501120905010e060c070b0a05040308070f0912080a0f0305071e02010603061d2503060507030209150d180b0a0c0519 83
    0x108e42c900307000c1a5900640719a0f122001c002d0140140c0c0462420040365008000918501401402009910581040d81c40c00d83c4e0081d4000d9001da400303000108000780c06500000b002c3c0070100c56003d259490040000c03c900324140a55000d9681d6101800400100f5408125002c9001c41940e001d031902c000d8116160b007082a050342c1402d054000100c3c071210314410144210703459202c0701241e8507140c0040f81d90b00c081181c104203002d291000441d89080034044400b03154802d8000656451030300100074081c01c0b40341d2721101410301305014815907942100c03105a00624100001d40000c03801d83d000c901428060b0b02c080c00c0c803071411160b99501c900c4e058000048014070740845903c00d05040049408800c017604010350300383c0303041051000600c9a008544c0001d49843c006d410007241600180b021400c03400c2015010000080501a4101034043c0c150b44940c83c40c0c003400b010540c1c1d2506c03600d440d401862a4011955002c80b102402d0140b03043c0d0340140c542c101014800402c64502510078031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 11875510 1250 11874260 11874263
    0x702150103110a0504020702030a030503040c031b03030306170d14040e0a06050405010503070602100b0103110a030c020c04021809060301150902041404020708070201080711240601030e0703030806040605060304050a 94
    0x200d010114030785c1001d008403000641c0c00340051005003040d4a048507140c00180c000c0b1410280b002000002c074140344010350102c020f1003039140190349185006001c446296010410070f00035486c141c0d00c0700001054501c0c152005040c0076400c2005800c8600c00752249802081d0b40100c10030a100500c0510780c0b00d082541d1069404008a0341c0304c80825913a42d0300d61258000683c010403d9000811464002180c0200d041c140402c1c04404070301f41d05119008650080b0010750354107020060954100200c1a07038500a989c11494514004040014184050302043c0101e00041c0490f62546095020001c5070446403808881c0c00d4440031200069070182c82850300700306401e090103030701340390510854015551002409107041080c0d801503800407002440001813085841480001c0788060284036003505c12081201100c1c013070384e0f055003003105001d0100c5041529100c0c04992401001801c00d00383e03038160500801c10358910001034044e2000b0780090390400b07804010701c410001d00080d40408030303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 11876760 1250 11875510 11875519
    0x80f01050108240a090602130605030604050708070e060715020f040303030e01060f05040f0e010507030906060b0703050a1107120f02090a0b030606060c0109020a0f030c08070e0f070215010311 84
    0x34003001e4003800f880d0803101d0b2200c0c1c1c00c003802004900e1590781d0b540a81200c61007a14094101451001c95048040443c0d00c81c2000c00c0300003003004191b14043c41401d5200d0340c141420070036420808001494000e60410b010f000307080015407113061101c80034482c01204840c400c199501c0c1d41e15120943c1c10303089413204501003418040d131503116140600891042c1e5540d2851070940364980303001c204c05000d40c614540007195549400840044082c000d06204121f01d84002c1030242c514540300040307903e581c2c400030400b20309100800c00241d00c10102c403480212460a00b2655980040d0741d424030b5030550042005807006850f00703080004042e01089003a008440c4a03d080c0d4503007040005460b0b07801c44403030741034006500094603464084007900642580d0780c00090841695400f0440011640c1c00001c0d018201620400402070710500740006001c44a02600b00c462810744d8260204401a00005290750b11100103200d9620800603150803140344c9026641559490030512903100001c80300a005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 11878010 1250 11876760 11876773
    0x60c02030f03160f060902090f060a0609030b0604021e07051507180302100302040306020d0204050f190905060105070501051005030105010f0303081501090e010602030903010b1c11040204080f01050108 88
    0x100800300a03210b00f00f0000c915085440c1041e607505014030204d45044a1042c1c0c0c864084000d40c81d09940507114540070000c422003070402c0800c120711802144d220b501003180b1f2810a00000d860100c0543e0011030680340580c55202e00c03020240c5064500004e1400c0031b40118640080c0b100c00900a000d0401004038400036844034503040301c1d600d000103481003507000e00100400050401d4080481440942d24006084c04d46a5440c1801d030390060300d1460080e60041000c2c42145480040410f13601411038261141d2018040104100c05c0d0070712605c3d05441e910400a0696400b40d401c07180d907603038098001c011030310b8540095112038225010b920b019610308400030402c1148080c140301034a806854241042d6260072a5a40041c54900ca0383e04210001400041b40c0e07800f50708041c003030b000d80d07005540c0b80e1380c46d101450708481410103130900c1103058008a202415030081d00e40e08198120b100101001c441e034001c603019106940c080d101c284203c0401e00d801034010f600240c1a1040c135801c1d00d48 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 11879260 1250 11878010 11878033
    0xb0901080604030f020106050307080f0c010f08040609030212120901050709230303090a0602070e0c07020a030201230316080a06030803070c03020708030409020403030e0a0303081303020304080106060c0203 90
    0x10100003405004560781c0000c0c00715011074014641d1243d2421144000b01d01c16444202007400c0500a80c0002c0c559400002c103c107132a00240300c2d001d8464028a8a044542c1d81e1079001401c58a0140014000554821907001818420302c42201e4040c10b980c48281d48001c0d05c030044801c00f40499112010794685000b04803000c1c464500e038000c0711006c4001c2c002c066054810b1042c043c80c80034200b42d040c4800c2100c1250380d142c00d02d094008241e9900a45003040c600341e0074000c00314004040004c6042d041090000503540c0f1801d031010b407502803801d10700265003000305507801c0a0451000440e00004801c001c02400f1410b025001d8102643c0c910019850380c00d661070a541c91408010400e010034030002d10580c1c8110003440c2074500038411103114541d44c1d4401c034215445600a0548a0b400003818002d0603044940311044420544001110b1495070320700411341c0b01c0c098000c0404100b5448000141031081040d58050803200f0000c00106036a80350150030101c020b9000c80c040e01810300b0010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 11880510 1250 11879260 11879269
    0x40210020708030d02130807030b04150209011205130c03050c0102010c05090603070305040c0308070501060f080309010c02041d010501080a03020f0a030804020f12010c080406150503030d09050304080303040f060b 93
    0xb16454480250b05220a07000c1d004081d401a05600325050349074031000806600c03c02c00c0300000c600a0044e030311541031074181561000b80c003040101c0c00360700400c9030036842d90380f0080307090800d188464001896210f4a86044201d00545000f41c1508020312011051080202e0400081a42600208075810041f1000e41c1c45008a66425034040300500c006410280640c1242c1d900c503109601501c409512641c441310716170801c5000f512260340d1808144004004101342c203002d0080480258100394082c40001d22042c00201c003b8002d036180d480c00b17150362000410402c2d0144450000740001d40c0c440b00c81d66600c200c004019030042c8034115210000d0340020891180007501039071001c5950741e803a004d104c4c0600c01d071011140c001e50180020800400f0a224100d60090b0381d07650080541032504080080d5410519400c0500031264403c10030350760000f04a030900c2c80c2c985c001058402203070030954150300440c0d000000d41c1c000041000704001201c120385034210b00c12a0204a062400f00901 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 11881760 1250 11880510 11880523
    0x1030606050d0c0507290705120a0b0406090204060201020c01060b07050601090b1302070f12080702031e040b0708071703060a030f020a09061403010509061005060a0e0603070804021002 81
    0x40001c58000c001007501000d20b50007049860840b420120b241400c0d5903a01d01c0301401310300b41c0400c0050070321522902c4525803c98941c000b54146452401c01c66121400111080007802c9203130120303629404550b080d141c6130481d800400c0402c10440d2116031fa404041d010350b214649400c0103510340000442c507020703000d0540d074010b500315004045580c03c1c068108001c20350403000d9a17115881030407600c038241c090b000810045100702c20080c0910454900040c40b162200c02c40018010010200140c003a40042514a0280014482103001c6c007290807984c0c0c07a02c41c0d901300700e1f9401d000040b10400e001480001b000382d24483d44a0400c10f24120f0304000d41c40c0025101507a00001c080000c1010650392185103180c41e0000305104291030742c441d029001ca43e203542c08070140c484130203000e40884c54280316550344030340082c000e04014038101c203000101e0380050292610844000ca801b2840900c506103000b442c40010380403540d20300309544080c107070800450b0201c2c810841c1250400b204c40c80460311 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 11883010 1250 11881760 11881769
    0x603150a0806070203040e0109200f0403020603040f1a071e050702030303010f0f090e0d0e0609030a03030501081005160f020304080303010915080c010e0f0315390d0207060b040207050709050105010306 88
    0xac41180c001c4218102019030106900d00300340c5000340000300250340d4482c02107004d03620941d03a00d000641203241c0030354000c0135049120724041c5147c0420a8103a0441d07280e041420000507859204007007841e003924280101c45010707405102c0400089000042070440400380c408130300c0e619200c2903a40030040240d81009002c1011030300701541ca00d082034054000fa10054400500c0d56042c40004808a89030500408007503000030780724001040f0040052081d00d4150466150174025403818004080b044a0400400c1040103540400048402d01c01c0c000d69001d05a01c0c1d040c0c1e1b0742ea50f907604050014002c080c45480344243c09140004050100251010b1102c4c01a100c030301c0c038001820708000e01c103000e092400c0c0d0076003d41640f0780d40c0d4101605000303100b42c01203820440680400c082d081101d03690045a4880c0d24442080345580c4140d05090302c2c20781402c20005a503074491440d008014080c02903515400c5030011480d04200200420030b10281c2d40c07040030030000e5030787c1c510045050700c095214 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 11884260 1250 11883010 11883041
    0x12020f0d061205030f0a09150c030801050a0b0f090103090206030a050405070b071a040c05101805060301030302030d05370c03020f09061605030f0403060501060e0603150a0806070203040e0109 84
    0x20b000c0d01c000c905d80107013201031705508040d00401c3d030f01c1d22001010400310042400003000f05000004054000103180c0c003414055404201141c00c2020b005400e110300c1403040c01d028800300703802c03070705a01ca81c0100f80c0b0158050701c5162241080000d5101901080c4e13030845140c0107171034022804c417038030400f0344400c3e907001038414942454170f00310940e0051015005892200c4480f0740810f040e01c0d100d00c01c120400c016070b100d6240c2c00c04081084c052228036001144988801c20040001c00d90000640b401700c62151000501c90301c9200b013102c0d0450384a0000c04190001e9a07150394074a44203850713a40d04600d0361308103000101d64000101d00328456244c1c04000000c003481442140d0500304050500c80c0b11101035000f000c03207562030301807442e0415000310744204070005061041010030700a503801010182444400d8046c1c45000441c1400f000300081200c0740d0443c80700c3d0850343d52600110043c00d02800399001401d00240007522a80306d4014102d18604900001441008030311420071803580c840e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 11885510 1250 11884260 11884267
    0x4030503041b08030417010b0303070506010501050a170406050108010c020703050d050c1204090203090f010605061e120c1305030c0a03080307050c07080304030606060e09040b0712020f0d06120503 86
    0x5407140741c541c0c814040b001000038202d41c0401c4000f0104001c0018095481561601d06c00c100480d9007541c6203c02c0140c002e40041c400e01d80000c83c00a03440303054601c02d0801c030340c030361760001c2084031966105007140320100290014031052045a1340028141c92130440244004600d008043e6a1a801803100810940c48150948240340c4210003424190b000c1f60161002e8941802e000c03d0780e03402039004412103590000910209040402500140348403c1c0c0082c04614a40380003c0c03054002c0082d8201c180c45a04140c003100320b49581111039581c05d0503a00182403c0c5002c440446400c503800c142c0d504100200085501e16002074912a0303080700420013071030f040c01c1d07541d0301e680d603007000e0010341c00d104084c003001100c24814405440a005c0c1d248c0119243c07440c5040c104140c0710030754010001d0146240110017162212003141e07500a81100e40e040713240e1640703001122034a031007661400d9180c0c40880c05a10342c4441900030035103840c00d03200500c070f0981c44d04c0c170301d00341803800c4500144285c1c800c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 11886760 1250 11885510 11885513
    0xa0c23191406090402030f01050907020604120e010e030303070309060b06090303042102090f0403021b01051911030703111b0310090215030703020304061109030c04091502070b070e04050403050304 86
    0x10007040072496805030540b0304084062010a041e60000d480e00102d0b26608401401181019030320b05900c08894402018a801d00d03450b011a010725071280001000303440007003401030340d00550034200340c040c000d030441c0d94918040c1001802466064011250a810041404114503041c010780da00c4060003006580340ca890f20140d4600c248010841c440c4200e40310240d20301503540c09103078904c00c051074a400403040c5400c1c40c0090034810102d000e41c60209040b0b20710f00869900c00c0c19034102c21071950304d81c11200003030001030f00c3d80c2c000c00b00c40303c0140c40700003404420954081c0b800c08950740e0b1f40d4122a9a0300d07801ea410004080c0c210b10554260744a4045074122101c5a000f00408900103441c5003c1402d41e1203448805d548111000400300390000144010080c4a200d040c80340072495292505218000000039290b141d1020114441d6442e82294001d209441ca81e4841d0b50003007020455640c10103150102d0004011200d43c80452a86103100e0500c1c1418041c03544103d41c50f591303140c40e6540d103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 11888010 1250 11886760 11886779
    0x40510051b0f130807030506010e3102040609020a0309020f0d03020a0b040f0203010c03020910020601030215070503090901030f0201110a02090a090302030706050a0203060f1503040809030a0c2319 86
    0x46840600f040c2078034000a003201d428020381003c0e40c003c0025002c0356040c079029200c04c501c050015019121b0301e0f00c0781c00b01401003000d241e030440b61240401515001900024015001980096484510002d0701c000c1c42c0350980d000300c6000d4806d442840d151080d9008001c0c0300c942c039030009405030b00286103120000e43c444c00c0042d800b6200701100700015040c4d4020a084400c40310f8844082640042c03001d1305482c041d100000c025a1300d100400a560540e4007045034002000c0c1d17062510140881c071282040014001e440e14504d01410868032582d5900340340403114a03030481070f8041510001040d24201c400f03d01e11803140e40282c043c55180d21040c60550090038000016011030206001e5000000c00501890b4081e4200c9000540c80303041c90341c200b20320007079680e14040c4203d0400000c1c2060111350000c0e05c4c0c5c40707900051001d44440e040301c0031030306014001000034141e0140c06030200f04048051030381c03c541d0f003105e60840d96602d10f05003803002c00761000180041c0c1004031a41013006001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 11889260 1250 11888010 11888017
    0x703050601090c0c0f030305011d071409060d0e030301030c0b041514190806040b0d1104091106070b0103030210020a05120a060f0e060f01140301120201020a0209040510051b0f 77
    0x5a213090420340c6000e80340c2001c40d4001c46811000640c48400400181d00240c03011540310300a0301210364581080d03080a00401e048039118a501200802c0c9981155a1081070315401001c07110284800c080c2080959100e6000740021039550300c1020002c1100707003c030415207040ea1b003070003000d80c00065074010544602031605450026824108007a0202ea401c040c2604242115511010043e0a0010420040d11101410345004000c0f80b030301c200204001e0082a140d1001c04da80002c1c8000c00c500303000001c400b00e240d00e142c0150000a400c8200210124654100c030b009900f41c404410004d449502607100c0c174480480019001e1001d00300b0160f00211480d00710001100000342140c0d141407801c900307604d66000c80e40320001201002424106030b5248881e1140901e0500ca0441c480a023a0b6910f00042c000e140c69844011560030869000b0400c400c00c598005141402604d058513001d1350b145000e02072440454180004601440c8048081c1107035248000c481c581004150100040c4942 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 11890510 1250 11889260 11889281
    0x20310031502040906180b010503090a020f04020c0d050c0c0306010509060112060f090209010201060509060d0b040c050303120108011404080a031509110a090b040513020304050c03010e0106080f070305060109 91
    0x26420080050003130628450710005068810308070034564404000e046c00c0b1100405c6d503605002c001c0040195000d00890310f8101c581d8111800c8000c0110034021400901a840854a25114404803804c0140d080350283c030b80c1d42141421900310202c0c5000b41910f0300001c1c8103c9030040c0f5942d0104002d503020b546140004a00b40e84006a06596918424843d03c2941d01076080140c2c00038501205503820b000e0f80015050558049400307046c07840114038900c440b8500902100c500002103006c22441885c00d03002090020704903511420500f01e0902c05550a1086038855172a0004a0f080420004210b510480e0084c036110f0078000e01a000340c0c094101003640b03220100b00380c0030114032002248640c00121011b0040380741c0312a400000645082460b4101c8490400284005c0080e81d81d01030384440804003040c4003503243d8485140c802d03d003450507000c05500d5424808003182c0718505501003012510140c04442ca000030509001c1e417510046c2c00302404603004500140400f8000390081ca6485 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 11891760 1250 11890510 11890553
    0x6020d1803091508090307060e0a0f080d050f090c010807110a06020a0305180c0d0c05040e010509100903020c040507020309090921040605030708040602130308070b0a02031003 77
    0x20024110100000c00240040380441c408000a1010403442a2051007440035400c005082e4142188240c0e52400317a000c005026540314041403c1b103500c103001040019621002042981066181c400300c07580001d8004140300f440e0000044014046c050a02e000309000c102602c0d206119500450380300c140101694240103610b218504d51103001c1180c081d40601400b03006898204001004003074500150001064144850402a00311f0b0301050955221034225040107950b03180c1d1402c400d12955070760015030b1252801040004900303041d04030900c00d4a07040c040c0d40340058202014400c03183c3c121405030050380302c185442d80a007031950005410941e64011281030000780c10000d0a00d02c0201c0c0d0f4400c603a04800100d140c824042c0780c2141010300000006401c04e8100f00e00100300e404010402002c1180b0600030605004142d8101e50140d803200408000e000d0b101e051121280e0700070402190112503040000d1a46103551007540c0c01503603180c00c9a2030141c5992100100e144107244001c490 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 11893010 1250 11891760 11891771
    0xa1121060f0a060804110907020715021002030403030c080105031603080d18030f03151206020310030203010e010b1c05030301050d08090901030b060f030d090501200703082a06010306020d 82
    0xca40d0b610182100a20031982e4620b5545040e191030440141d04005c00303030246410b039050081303003500428480300340d8091070400c034010402400100c1c42c0455812010800920000611040c5549904032516241c4a40c958020070f0340c0e50000c1c1031b5a6503d40602001603600701e00c0038070001c0d52640c02002c034404101e10100b40b0380008030468400c1d5000b0722080f004075002c808004201c40d01400390003211150300c110001010303d80ba09070415a62110401488190f00100052201403207002c060051600680200410143d02e030303030303640240070404090f4400c480c040c45803204240c01820503101c0b690306c40041e50850340b81c403050002c424003412003103409550601c001e800301d40b105151240218002c144400c8070b4280a0280103403e40d981400760301a0300304513800480941c101120000f240d0080ca031011401402340b00954005031031400004a6000303228002040c00901006468544080001a03500c1000f69104840d07400d801c10207513110b5049640108040307090360b4007800f00710203000400301c0c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 11894260 1250 11893010 11893039
    0xe0d050a050c030f030a050f10150c0302011b0302040807050604050303071101020a150902010305010b0702090601080705070c1e06050a080c03060a0b2a010902090115090312080a112106 81
    0x400e0300301b02c0e4000030340d569030801c0140e03c1c080d03200107a411060b000d1400700d06500f01b881000710060300c81c1228061158400300d840c1054400d501002c201da94862406100b5017940c58010040e5100313118209403071045010100311071030244101c600301c4400800a514005c5d803540c0d00010500900800380c158022011660082a04030004180010a80000007207036421480090203e0340182c001d1142d1450038860303500143c036004001e41d00070809007401c250550b03584000305c8003841000e10003411078a0004c40000ca5541801d4070400b0200881000304445444107821103480c000c4619500004e80e0003000300d04000e4a4100850304004044c1641144a440d5040c2004603849103481461246100302442c19200a403203c5041c801c02070002444504896000202d6050043c0581400c1502e42400c10171685c3c0180051002564402e00c1c10391801103050000e40050300441780090320900740b841141e43c0100200459a4000c45029036400e0519035259044911900814198011551510011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 11895510 1250 11894260 11894287
    0xe03040305030a0f0305070c0b04060b0d030804020a050f06040b03071e17010f05030312060d020405040b090c030111042303030309011d0102030601020c01050f09041805010e0d050a050c03 82
    0x1035405500107540c0e9500c10300380182112400c000100c1050b107003400340500250b000002c40451600a110040c1d185c55604281c4010003405484907404041c0284d4001095040081c8900c118002c03550340b014113644405100e142c81d4540300712980080100020310004511002860700a4a149004105103010707040700014141025884d00101c0c0049004003c1014241d40041c00740603000f040300010f915000100f5564022100000b0110a02030001200c42d01d8185544015a070010802e1269003070505088054010a0320106800c3c01049256205400d050156004144514580c01d103820b2606804d88207a8480d0060700d40260303503640e058226a901000030718061104400001200c0b21105014080848440d1301c0c0345e860f0740180100001a078010903458404002802c01603521503040744052641d1007522602e503030241c40c0164842d21051411102d8211a201c0d000821030240d0749442150390369500e0484d980080c2080029002452003113003d414003d81e00c40031a400c000321141c2c02d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 11896760 1250 11895510 11895517
    0xd06060509040b04051905030406030902060f0708070302120a08060103050603031b010e07090b06030a02071b03030e010305060102160b0c0703140a02031c020c04090c0306020a020d0f0e030309040f0e03 88
    0x156410b84030802131100380700c000c1c4103081d00c841d0840003c003540c000c0b130351341c07252240102e21412050681e1b0b1910703407055441d0309085400f13107501100c80540e1116a880d2501840d040354105a0051250110f451450111101100c0d0904d01c00e403035914660f40d40d440110003600d402400a40c05d408107000c3d2054014802d00d4a240c1d0845510002c5140140307590801e10b44600b5900c2f01c0c828600b00701c0580707280c3d114a07040301e41010f8070f14005a51480d40d403c00551000f00e8881d0780c0f0038103410503c000b0501d90f01010b40340340b000003640c00b800396840e450012650790301035190a2503103401c1c100c001c2101d5203001d0001c0c18aa0b82c2070003510758050b071b20b48400c00200f082c0700c841081500024509003c41c5000c1c440b00d020f00d0484800305041c120314800003551001d20343c1c00240500c0e51788907018280020003002c08001d540c010010340d91521059002501e55001403c03c5c0e001c20f4813503540f050103500412418800b80000b60040d4105480a410070024248012542d14610303602c1203080340307403072050009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 11898010 1250 11896760 11896763
    0x8040801020c060412090e0a0e01060305030c060402010305070c0b07030e1c09030c050406030309090b0d02040207080a030b06040510030f02040509180d02030316031a060307030e0705030c0603060d0606050904 91
    0x14101500d0709017018501e01968040f514200000f080050002c0051001c031181c00103040c00c3d0014002c45030703860711401040c15800240141c8004110f400a02d5000203986100703500c01e9809120946400c64141d5681b400e5090040440b49640700044d09a8804e42c0452074061007a811151180c41211b6240c034903203011403c410000d00c0e02001403050205140032100144010354042018520310303203006026001c1d81c050798840070340b51900014907a83c0d104031600c0c003a4004008540d01c120614190342903038050188500401e04104038080903240c10f400b91400c54001030006a10385510103000c030010552066075040c121b500344030110340c1d91203030400d0510403841101c1800b00d21980039101031402032402e071004115803040007002440344007411410282c42007421b01181c00b000844c3d500c0004482a04429041003000c41000701e00340d81500815000a05002039426040d161414181c0f11040011403640000003080420182d04050301141c6245001d0740002443d036440b40002280c01c0700c140c0c1c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 11899260 1250 11898010 11898013
    0x5150a0605030f0f03120c120106080115030603052e020a020102030402130e07050d0609050d090513020708070206130f08011d0625030e0708010e07060203030f01090908040801020c 79
    0x40c8220b06041021141010640e4004c040091490000039941e1280e8005040c6070b0705e0440c04129050300c1042650011115071079014031381e6845040c002d149400910440c418400941c6205000038000c3c8a204240ca07003003005080d001e10300c894805000b4984a000748000700242e640d00c000c0400304c1c40542071820455001507a6401c05004101241c11b648070450310082c500a900e0801010000d403080031604191003c105031251400c1c010000c100841c00609140980c40641084503401031109e0195035003241c00041c444841040d41040b4000c0503401000500104454805440d0030005484010103060307990600a86441d5480b007a50810b41c8001c106a45640081c00241840d449203503900707010750300800051270408251691000100c90b402090180e4038440e04856100790000308518036000c0c21201c0459444880b28001d100c3d080c00300c2014000d49002059151011003106d0248501d0340b020000c513401c00718030f540100b000c00022140401c08000010780700c1c2082c0081c007004c801540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 11900510 1250 11899260 11899271
    0x80702060c0901090803070605010302010201200901210f0903120207150e0309150702010e09040f020103050601110a080909010801020a0f0e040204030204060b07060c080c07110d05120406030b0607020a0504050405150a 95
    0x1001a080d6809070780b9103134190c15841c8030048500c0546d015500d08280918041d4000368614280d003002c0c015000104102c1400c011080742d14003c03a0300005465807090717032480380d500ca10241410890140355002400340c0c94620b05030b00d0a01590f0407211011a221007524500300b01039000402446107101c1d9111851404144a415503810a10b04211040103440303211051816a443d110500c0b06010300905040c3e031803000c0741c02644a1810302c500c108008040b07624200c05400d095040350002c0240b64446e4031480c0c008a060070060083d6006c0c0c41c100c0d12020002d0604240586207490400ba50a400503402d00000001d40d54500891000741058041181d844500741400007d50300315170042d20902460000b0b0003041050402124003d98020040103808100710000824942115401800a2007401510b510340000e007001002100d0054408000c40727136042042c014107000f00710f00a0360102c0002400c004a0400f604001d41c01441001540c0a06e036140b499800043c1c41510030f8a03066a0300c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 11901760 1250 11900510 11900513
    0x50f0a060b0901050301090504030c06060f050306060a080a0b0718091b0914040209060d020a050307110106030515040305090d060c0908010213051210021c0606080702060c09010908030706050103 85
    0x510030240500000e40c034052604540200190640c4010f1051800c070a50315000a001d1521400c000c1e4107940e4403403014041150340e02c1009000e05518040c082c460701817240440d45901c0c0660030001110f64041c05009101c1c81c64441603000d4000600c4a0180288040411110180b1940a078040d04d503a850001d44461401c00800300c0c0c6001380011000d1100041c2e05000206150b0002e21101c2c004942c0565112180303800700320304e4090035002050850010810328022078203d4042d6100320f0840d41c6190307009400c821028240c820610025001d40c001e00101003104525801182d0300c00d000c0d0034268178001a142c0829503503809410260341540d40c80c150140034542c8525031900601c0c84000075401c000300050301c150160721610a2500c0307680c2d15010881c0b00308051041146482c9281d50840d11203c020024a008a20b81640402100d2a00d0f4000c540b00d0b02490003540510034603801055160782c0c0707024100383c0360301940c1c25a040c0030b180b09001a0000c402c0000b803000314442c000208055145 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 11903010 1250 11901760 11901781
    0x507060815030a15051902030a050103020411040303090b09180403020a05101a060a0c02030a0309081009050607030c0e03070305030c1903140702010c0204020301090b030c060c030427050f 82
    0x2103980c0d840c801c0d00f101d41c40e4008901d000c010815034006007032000405407200044409151050400f1540480c0084100301c980003140e0312040c1228000d98051106001c44100c1450603c100c3c08001d01241d00c10409020300000c4c2400b801401c00c0c003400c141ca607140c0300c400c40340c20241e0840b401c87c01648aa030b02101007001c28400405884111a01401802602244192152515200c00303003d0400403400083d07292007100e43c0b195854015007503401440d840c0c01c0041204541d0b000c2d4290038440e840d01a80410258465420201e400501405136501c408400700d028089000c000020840010a600340e269410302000005600c00c0e0000d640e549001c184407030619030302180131160f102c40151603a010a4101110301c2505c403030700704070070b5030f4140c0c47c030052714464500f01c0040d400510103c0041615510303a4000c0d0384c60710088044400600c490340c20001d9512405c0500a5a03410611003040141c0010078a02c00343c400f50160790038020070785002c510866030210781902c00310310366a003031000d0b180c107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 11904260 1250 11903010 11903041
    0x7020102010b0103020c0d05070606170a0c08190b090106030605010b0a09140303090603100b0406090627050f060c0102030a0b010809070303050f03071b0606060905040204140d020d05070608 83
    0x130b090560801840400154456407401044800e0200c0018200c00f0414154401e80c0130300941310948181034014034016941c1c444403907040318081e444802c0401e01d00700000d02e89020403a130300c0860040200c0b03590380301050750b00903084da81199200c1e04040002459401294040e00003101d0703141d100c620078034005000d2030f09a8001107410091514030309240e2404400c54912000c217440080c0e07662102c0c0d50300c4108035001d5001c0780a070200894086100b0b940700e030041c0110303502542d84000d050010f03000c0130031550481e40145406208580108a5170400400c51122003d00522050034250b074141e69909990040341c104c0507980c0c0d5480d19688560b00800744c0e40e00701440400a040c80c6086980180242c4165a50210150404800544240e00c02e895400d4401180c601042d0b84907101d10303141d405808030780210008140c48100100305801c051081d681180e1400c404920540000010b100c00c60503040c13400c3e0b0b0001e1148035024003061007000600020b0809940300e4070240303000380a41c01d1a41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 11905510 1250 11904260 11904281
    0xc030b0a060e010803190903050f070906080f0601060f020a02091008010c0203030c07030503040c030213050703051302010c29010b0307080a050f0a051005030a050105010e0106030603020a0603020f07020909030702010201 96
    0x81c4482d00510841000100b55000e00305050001a0300118100081e6103140385503000410700d20a03441c480c03007400b0010407041d0403984c5145080c03203915110041c60b9120100a40b0301701c020f03403140c001040744178072072034500008c3c500e54015699079923150b40100300c11600c1141c0c002c548450b030110400c1549024070408d0181003a40c0b014600b035040500c1445114464800003608010000c00800c0c02d210310f001c01d4400650b401040c0514a44517121321402420044810300d000c2490000068540301d030301241e1410035907050703450b0700403407901d5903c443e0a12150a40c403802610100c034804e04d400828441d42e0b020f00814150541c07640740140000740403038402000007401c5414401800528402d9158247d00024442c0e008140d1380d0f80d99038903445858480e030100303a140c03040c0c0034600203001040d80514141d8105000802d802c0e80c82d0030b8260141c5c1c10f2444001d4001d10012400c100c2075210b075010b040b00c4981c0e110387c40c0c40c00e50305800240920b10143c40340741003034000241407421503809124814811 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 11906760 1250 11905510 11905529
    0x20f040510080408040e040206041205100b01030506060a050f0f04030317070203070206030408030a0905011b08010e010b041503020d090602190e030c040b040b030312070f05040806010b090d0c030b0a06 88
    0xd02e41135861100c00d01851003030b040c404035906c0200d0210359480d0f007071f180640070014400307002c09280e041c204d581d5004903241c059186e250800041040d4881c1c0543e40c0f0540e0041c003140c3c900079907c40c00f2669a03001066000e43c0d00418403440c03507a8205000184011402540c40000441c41003140b01c10840e0050011000e641c002c0040c400140c88000659901503040b0903041d071039039520240d10014142d02d030303002016546062100200c0c2c5035821005c0045031810342d01c01000e603880d02d03500d52b08000c00b070203014186c02c5d061000300b10307104020300c844000c0111890b015041c641c0b800744a50030f9910041048440903004150460400b46151448e4682d44403403414400342011040401c3c1c031000900c0010303002c0c41c1c940c50402419103d0750041040c4100c00b1f011a41c0d6400c0114001030306120599042c4001207004030100c0c01d0511400a803015684148041c00c0c80d0f0f4642142082c1546c0003410598002d8641000580400c0c80100903c00850040d1104080c0d890064142002c0750701507000780460 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 11908010 1250 11906760 11906777
    0x18020312040f03060e010b150414090c070f05190c090506040207030e0f010e0a030c060801051e0103090c0503030c01140c120c070303090506010611010f06140907030f020f040510 78
    0x500304410500f26a00320070009071002950010340d0142820800c5c0c10b13000a1800141c001d490101002001200ea120743c2d803403402501c100c200501085c00b91001001010180319680115400c036110894580c842d070101c8030a080b946840a981500c0e104069400082015040050115034006c4c90352102048808501d0f01c001690040c1100c090349040a000720402407581205e07901800c19880044401000c0145885e03403440d106030f030300707060340502070000b800070000007a00c0c00d0071411130340482486015821a804c400c0700440041040c83c106864404044038001f92a440a100420300c08060400116030b1420800c080741030a4005441d0328050a010861504c1c0b80548001c200d81120400c0501c55803410542001c80240c4130240c00607100f801100700025043ea0050b100b8040c00040c1c01c0244084850b8854041c121002481801300c80d0303000950810183c9401102907a20003440d040015100c0340c0c41e0440c00498010402420543d5000942803046182c81c5200c06101c59603450031008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 11909260 1250 11908010 11908019
    0x15090501060215090f0304090209030708070303090b0a17090a1406060310110f0a021b04090209040809040e01061202090c0301061b0c09050a141501020c0f010c061802031204 76
    0x140c946440c0303201c0210241c11804140c0c13041c0d0038440c405040c000281141d8655840b9060a002584960215446840340d0b080004410350b0108038401101d4040c0c46400d4000d01c0c2629141150388401e9012013000406030341070300b40c00090310360540a40c5200c001030018101501e04440d01400b41d0f001440c00350701c030804124050344c2c0011010382c02010803e010440035000c01031040076000e00ca032003100c41e00000c10504190b59000070348100c0c031510b10441c2c0d4424000b05c400d001c100d44100c04069005040d0340000380100315580d00505220703002030400650200c6100c2441c2c03c454a54100004170032550801c8010752030b1018601d41c10443d8520f020b031440d40b40010240102d40c07454281d284607186424500c09002c103191200c4000c102500f011b00052a0442c2910010441c00c1c0e10362045403220000300c0c1d415681d032484500c0940043c1c00401009000d1010400c0c08411304884504110003221200b0008d81c0600500e21960f009030754150b08140584101405c041d8205160242e007441444200f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 11910510 1250 11909260 11909263
    0xa0608190b0f010509010c0f0501050f0703110406030e0a020405010305010c02010b0102190201030905160e0105100e010903020913060905010204060f0c12050d0f180c05010c0206030a05060301061701150905010602 93
    0xc00b00742c04d0a28541d507841da1001030703030314044c860302c080c1c18160341401500510106402c110b20520309100e007d0256036420030103508840c041180d15503d070b81e06102c1800b609001c0e0340200103041ca55011140c0c801c02c103500050030780b4800d800448507a5100c04003252015024002c6421001007400a043e2040d44005081d00c040ca903100041e0405845059003400d226040c00322803042d120400c0000605500d40c1041c00700e1010a101d00c1703004100000d00b04050034440c040b520000d482c140c5d6400a154615003c001189030058002d007410410071092000180307440c400c440405200b0b50016846510b0250003418030f82c00d000114041c1701180c11500c000820002c43c3c2d2201326040d0034280e44441d440320f0700304004d04003d403011120300d1828000c0d45418100301d0298021900c608442f0003c16211001110340f1410010020341003c01800860080d12045d0002e0303901001c0500005502550340e010800145800d6509183c00e9640310070300d04041c10340c2c1d06134034080d1140c54814031255242403c000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 11911760 1250 11910510 11910529
    0x40302010c020d08040e070e0a170307110102010f090507091a030304030b041e06140901021903020304050f030f04031401050408070b0403020c090907170d02070308070503090a0608190b 81
    0xe22078105882d80c00304000407603080c0d5006c0d00034000c42c26102d00c1e10703a202400107040600200e01c1050406030020300301d5482c60900ca074003880003000d5030a0081ca07a41d00d0500c1f140c0b2281150546d525820349441d080f91600c107084080b80184002c03c8201d10341064601214584070458001c0f0790611805035068038000100c03800c07264800008400c6541c1c40c00e003c0303100f075410018160b04880c0450710300e06118482e004190008640034440302c0b07640710055014200c1c481c03100050580900f0708000c0c29418020307030285a20074040c0c400d54401c3c80c01844042d04690001010440000c804101801802000c071100a215140c89008100c2400d0540750100980298440100500c140c00d001604161081c46249503001e8043c007640c4035070402002c0562a08818001e040c0418a507001c100c1d014000001e90054112a98014000ba0b60454594000c160f10030f1109544500c03042010054a44408107041c1c01000b00e0313030328405642031030f48a200a003900c00410300441e40c14011414815580e03000e0a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 11913010 1250 11911760 11911763
    0x2010c0305071703040605060414060907260412020712050a020906130e03030a0c081b070512030906040201090617060103150306050906040620030613020417070f080102040302010c 79
    0x22940302c10039441d2209660f4002100e06030b8103500882403004011641c1c10440c003a03d4121002d000c9250480310707006540000315802c990252498010840940c00b5a10a842002c22401340c0d08008105682c00c1c3c40141007500c046400e00303041c020030f00798a0380c1070025402510381da0000c400808026210303241d0702c0d992546c0180c40f9414960214010307a5600740300c1d2840000b480c00612200711000b0003030361682c000300d54240070310b03003440030650b0100d10401440d0310031034070140c01541c880c1d0300c1c00c1e401c070b002c0d013015070112190300ca03400e12030a12241a102561107141c03c4070003000e052401784001000c2c6146c030307807000052144841949801142c0c103000184c0c010303400c0c600028030b44600071000069a4981d4000350400b0f00e41310a1150100020a803684520301130202800741519803000031010350b802d03008140d03100c44140042552494413005102c42d4541c0709030007600f002e072500700980c224010283c81408940c0558410010300c0c0341103e0400040c5491002113082030b00e150000303004400010300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 11914260 1250 11913010 11913017
    0xc0307020706030c1b0303061e0b0301030f0203010b0316031b080d08090c040903050d050f0105010801060e040f0e06060a0603060501021b04060b0a110609010b0d03050a0306030510020409050a02030402010c03 91
    0x556424141c420b1540c454150241c42554a00c0d605c9030030090014030071809400c451300c21109000e503c0045449903402150a07403607a007031030b503846c40e200c1041c07600880340126410b540740c03120004070356001c010480c5001c103030903045054540756103403001380107141030030300301a40100e18030410540350042440440140030341000491942c40505181c01c109034180013a512030700d41101402410360141c00380100a140b0002000152507079a0980841c1000344074182c0015004070050180e18170031b09000c0601c0d01c001d030010821403200362844054424451440d0030300c1e846002004442d00d8203a2040c0010080c6046c1003155500b8400001d4455221140040c10304c110442c1c443d4540d1075503440407000b000050401c5842d1a40c00e03100510074000080c0405151180c10301051250f1018420444003408c000c01c100102017075543c0980c0e00b40c00c07005100c010300d80d4810001010803030512110010008039a00141d5032820003403850221040545179090507807052040100603600003e01c858113581508 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 11915510 1250 11914260 11914271
    0x1212030c020a0203010c0f0801120b010515090306071d0109140607080708030907080d02010509030a030504021804050c040f1103060d080f04032405100509070311031504050c030702070603 82
    0xc80a07403030000000b0000b501580b130501c08804183e07000016000903902036491008990340d03200c6a03044026183d101410580480c001080b15103421046041d0001e4074909035410010100c0000c1d00b022022208200840c080104d0701c0c0300c24054104005900701c003400e0111010b420980728207a19500105c00a0103070100183c4a002e110b409410b0ba40c41d0b070f078403072a986d13039902e00108040d444015070b00c00c0f210f0038802ca0082402c0c1d5401800303141e1117540141d0045041c142940d07c1100074040c0036000303a804c60a40410801200c050030f41c502d2140340a00024800006040d06100031628240028604e00d8a804805900b4030303e14401c0b260005000c480640c1d00c400c190810302441c0c41818581f48013000000380c00020001c00907001c5212110b8295480040c401e2012140d06031142150202a4090403030f40604c241d00c0c00e04034a070741000062800203001405054969510350058684030030707100c1141d2044003c2d1801b4040d496010031071692450840c00e0244001c0d690350920b00a54050680303d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 11916760 1250 11915510 11915531
    0xc060c030d0e070e010b030405060a0207030306080604060510080c0904110307081506040516120c030204080714040b060421030c0209070c030801050609060703080a090605040c0e01121203 82
    0x40003554200008101c0030000151000c2510741c0e212254891315a2141c031050000a0a246076000d480c0b00d0341c1c0000180c5140d5840100c0c0e0002503000343c004a00f031540d50040450000820040140b10364400c00e000101030410b4048800841c90340d501440c550303840800b0000d03864607012000c0360416400384100c00b00e50344400000e810010701b40c000000c10b01c10034034901c00c0a1a00c030312035030280d9810340e0108400c0c2c4407004001401c030300d000b1503e404203c00101c003541c0f00410303900c040b201007200e140050a040d144c1c2c00590601066500440e11901c2c51b4001d6a4103240c40d102c0c0f80c601c0d0717804462052a0074034200b140d5060700078150000d915540a424610305260092001c20304455008142c3c9583d1310b41000b000c0c02806100703500382c0025210800101d001d060940488003a07070302c014103103420b00c0c82c15581200c58480040c0414285070b01c9402c0c07000080c0f4940620760080b441402c241903030790309144d80d90071300d048140d0009070038203000011080802c1103078507080f8440c181c07482c0c041400d8161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 11918010 1250 11916760 11916763
    0x6092a09091d0a03020304061701050109050f01020f01020f090a0e0402090402060c030d020f030f0702010c0203040b0705160605090108070306030213020d09020d0305030105010f09030210030e07080d08040c0905090c060c 96
    0x2c00592031441e0207080703c0d02c000c0640c080002d00c00d455985c0c4820034403118940341802c412509014032030108041c0c070418052440c100152400c000414811a40b001d52801c4000e42640c2054040a04071a404100700085103000348000b80905006020a0032500d070640020b82e40b0440900302900492000449041c01c401c10700859428070703200103096603203104a80c411042603000319251140c03d14644042485640706000d8030f003041c412640110b040500b00006010300d07600c4001c1c02c070341e43e1180c440a5a40f87c0583c90410000746070640300d45840700301c580c0014001c00350081401e000c2602e00b07401880140c2c5d490b001e034005210803a20040e15028020340490041107907440103036009500900701010141c4c044000c5059840a80e00c0c1120180540303001ea5032807216000c005d60040c0401160914241300f42d100e015000c0960080369420360b619264541005000c48a62000840c800108028040706001c400014045c00c0c10070004c0b40b03030030704000c0c0d241d901c401140352003690300180c901d4249a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 11919260 1250 11918010 11918051
    0x19050c041d06120102090f010e0402070512070614070c060c030b0603040c050a0501020f060606030702070302060703020703120503010503100c050912010b10020105070512041506092a0909 82
    0xc0041248800c0340700340d41d10109608112501c9100358082001200310281c10700030340706003010141c800d07400002c400b001554601c10b20121103400580c2030116002144c0100f04035503082ca0888203e5580d0740d0305040110039a513a80d80c0450340c1218480c00c4c4000c150303100950400c1035800c0306000498129035801180906480c220140e0711841c0402800148641c03201984100c9008a582c0c900d999a07400040e42c4580c011004a000ca0304528001041403c0400c01941d102d4564415540c25a8590f4001100b0b50020041500140c3c0301b02070030f000700311038031600301c403031011505103241190300d01000280e4449100300b5540d4110f490300080384507580104241ca804000c0141080c0b054071038650400e00801e503481d02c0038031071a6103030542c112950040c468640114001da554924000d4881060186070030003800c02c40f11881444e048004d58451442481d015020341c10000c220303000000c080c41c1e000d802030b22041c100038120012140c1d642d42c00c4440c0400b101d40f512008030340d06010b85450404c112 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 11920510 1250 11919260 11919269
    0xb01020a0b0f0a06090c030b0315010605040302010806030a0209011e0f1511150106030e10050103080708071e030518100207140d060908041d01030c09050a0905070303081503010519050c04 82
    0x1401c000001486c16050b810030303222182c046d030448e0031112400800c00b804210a21420010401c1008140003551056005550100010781100d64107800355012501d054000da0001032003000c86041c02185041c01d11041e0001c0404041144140d4201408100c1c017070140d0004401b8454444425130000000344441c041d11099510440c50f40d42e941c1c9000f4000d010404000803e900070340d19141e031860b059109030740c10389420800b03c0b400c243c17841e591010190f01c040e100b52668404050306080b6141c807005654801880380d0b55994440e4180d021a00b581b98901748034500c2129804076100d20346500288810032039124144161040c2100c1c1c0208011524042d0090142c40c00c1c481071009219015009004403603548510340c0980c640d54401c40d8540c1000c0c00014040c03c814002001036101503000f8580002404900240b410119611a0300d8035425510441c080b8050501b0408d6002c0c000001c1380c5076810990080c4603600d8513100540c0c070100b84c18810b059460361907010038017280c510b10950f800b90 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 11921760 1250 11920510 11920529
    0x60a0c21080c1b06040c050307060504121403160309090c020f0a0b06040e070b03070e030610030206070314120601020601090c02030d050907120501020d110f03060f060d09060b03010b01020a0b0f0a06 87
    0x24201760404844601c0c3d907006407400b030300c50884006505841001194100c41e102c00100f03500d0a071590321070081052402072a1003d200902c0103031040304c4440950304555101751201800c20340740a070f03040282d61055800f101950000311720054a9007000c16205400c940c481c45029035540c0f6071000400901907441d1807441442402000318989201030001d41c01b80321183c4039110600b9004041550740c0400b00c2d442d00203655998006c20040c00e004000d000030611a084c048080441590800d01d145c00015000045540050a201c02560140304a034094000303d101800080740030180a9580d125801d015400740fa5602c000a04d490018480c6001a1a0f000b8490340c0d06125030074003d010b90001da00380040302e40b0b0b14000182c03140f965000c541d40d80418039042c0e415079942d41b007003095100a100391035030808010050203c00514a00c81c01c080184142d1000030b03816070700d0040c1800c550fa60312105d030555015081320070200721410941540400c0301044888650350765a4040d01514003640055200c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 11923010 1250 11921760 11921773
    0x11e03050c131412060c070609050309040504060903110102040b0906090307050301140405060106020a020109060e01090504020c010606031404051507030e240f010f090b03030405060a0c21080c1b 85
    0x254442d0079080885004104c40c802091419103450030f803188030646401d445802c04021207400191160000a450fa010341e06a909154044010600b07070b600840d02125002d94542080c020150814211015851064000c50429040510807461449071000c41c40c864040880c00715043e6904220750006008003030b00922951391600329036a03011000f91011a0315020b08000070506a100140c40140150160345208406141013400d503001082144400d0401c0940d040200e0292114001881000704203000050645e24010f401002c031556051040222413091041c4030100b0400160203d400702d01400b41d1080b80c88075030b0164014062400b8891081c010b0802119104500c8060b58400e6402440500e000341d41d44424a26081c2007406804101c542050041c004d8004d01d52042442000140449182a4441d00060241d030484425603002a0300c0c24008405c02c841c00504807010145c0c0640800a0394038407002074601d03c4000c24042070b1400105000346013407103080c01500071043d1041917410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 11924260 1250 11923010 11923019
    0x302070f0614091902010203090103020d201305010801051302030606040e0f0103120c0b011a0c060412021e0705010804060b0607050a0b07020c15070303060b03070302030a0b011e03050c13 82
    0x580d480072079a440b2903010700903601c4602c0c3d413070f410344050269050f4003462410316030100640007034005002e480000380c0d68002e5004440340c40c0201d842240e41c540344168a0f40c013052080303140d1a2894100b60b04100703840c001000b25407261a0316080701065540056207950741c10300455001d004503406a003003035600c00c090280d0724203c60030081c180c1e13000d10295901018142e90a5801d8080c0300d00090618aa40004001401c01e5221401d01c2d082458410351400e10010111850f1003c207a07410303100d040b14441003007a0150100040c0701c50f6200b10085502c803581c504003041e1607a00e07501c1a1410b10801c140098100300155000e104a07180c02401c1d035460303403005d0400c1a520110303a00d049410101400204901c1e40c0000380709014008001c25000c2d401111601358940b580000384120141502d030540032540400c41f501445c82208180d40068507407a10110680a40c0c24454076581032012031864590500c188003030b608805141418007050a4444115144c4d55124840c500c020745003076082e0104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 11925510 1250 11924260 11924291
    0xf0c0f03110601030f0b0c0a0c11060c100204050306060901120305030901020409090803100605040503070b07050a020907020604030909020310050d0201020c190501080f1618050307030807021e03030405010302070f06 94
    0x92110302680c9100c12680d80c071f18026806100e908040b00201781c2400407180090f0414000343c400b0315000d055241005100c624680c54181070004d82601c0a401040a103c1030070104000c642c804070840d64079660354500105040084420f402c017600300310300000050101c040c2501284e008280000c0700704891040c03410040400e400036509122500c050f41d0740000c0081c480d100380c40030b803200107015040c6a0b1821760285030741c0e4003041c811078043c000c0c0c0408030050303612414201e1003200c294010b07101c10320f040c1c54000d10620761604403440c0c4510600500c4004c0410014003130950340260364400100c411b500050f480e0401111a00ba40020300400c14540118013154800480c0c00a0300c0300000c9440d6000e00b0f200300f500803500b0907940f11086404404503481074807030308824045045c11084044d1554003207403c04201d41c000340d920000005001046080560310181d110502035008001300071403400094480c03007141310301c2d410150046284001d001a50040100700c3da4040010440301c22090300c9003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 11926760 1250 11925510 11925533
    0x20d06151203020c010804050c060a090906030503070c06081501030c0c0b090106090b01020a0f020d030504030804060207061407020306070e040e0303180d02070806010306180f030e030105070f0c0f0311060103 91
    0xb10018000d000c003104c2254018002d07240910f500c00042c01001c0c50010030302289402507a25141040314282d000185100c1030f115050146000b43c01031640c0d86100e00f01904540c0350f6071300074410080b00600300f0110b1408005c545c1c0c154507003441c2c089801804c3c03920882d24200700003c050b1624015109000307000c80b0540c010740c220f0744110310034490307150541c0041e41c59070407c42e40034281c0e11804540800525056002082c164400e0524604041d180c3d12000c800d1340250300318a015034040c03071040c031034140c200041c15507010708060301030314100071540881d86030303000070b44003005100401c81d0180ca541d6454008030b0b809000310301240e07180d2502d14209101c0107220680720030607010741105407030307201d20200d80d0707500380d49410b001408264039640d00c070002010160b80481186078050308100001c0d14244c18061002d000b940c915075211103110826085800152000040c003622030504030440d03802048851400b41c2140010441000750f04041d07a9960141e0103604a5028040c004400c00c40741401a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 11928010 1250 11926760 11926763
    0xf0607030c0203130306020c01090804060203040806010b070203100e190507030b0601030509030313020102010b06070302060f01050609010c0204021305030604050d031109090103020f03010b040507030e0c03010507050304020d061512 101
    0x1c0c0000d0721003440680e00c91080d844121000001c0103414004a40d45400604007400340c0000002d0b0528241c0701c0c01072030f4010b0703008000103810002d0100709107082045160b0140c05840180e914044e165400281e0380d0410240000450383c6460310054031540c18420f54812402884840c1e040d03041c50b01e2b001d9200c1e0094041182c2010200c0c005c0361031035200b0b114061050844500441c40d40d01c0c3c074490501c0e20313006c60504034119900c1c1d41c0d6280c52a21800013601300e152103038000b44441d00f04000c1030b201c1482d05030040c60003400c0c02e01400d242da03a403100a10300c803687c040c1c0d80186da99240706110725107401950040c641510604c800d000800078001134510401c01140e40400c04a90480c035803401900c541d00030a0703403096225005101515001d002c5034900b4000030700004240c401c880101c1c06070780d42213545001080c4d6844020301a400e052000e80001041100208820300e8210f0001d8550300020740041e00072010407443c0010015541d0004a40d07405840821416607901c001003182c1c3c001102c0c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 11929260 1250 11928010 11928017
    0x90f030609050c1e040e0105060108040b040503040503101a01030903050f07020f0604060503040203100203010302030706050a1715041a0901060e060f071101030f09030801030303020307020304230109120b060d030e030f0607 97
    0xc6c0c2c101c80040612400d4010312050f501d11074a5101c07529282072044000c0c206558900080000045c1d5a40c200617140f01c001010324081000307220030324100000c181403400e95041c11706041c00c20000a078413408580c04c072419070140381c0c0c46403901c2c00440d003890351815801d0307080200040c0101c1c80c260028080d522032807003141100c0c0c800b96030b51100400e0b40420320009404d40c0c0549014403d403030088000c0c04040305617180c1750344101d4405840849030780301524000f12000c0b40200307551b002d04042c001c4003501c010101204842400c10008030380c10705014401c403001c10268008084c03080c0d803440120b4002d92141e0008646441742410040342c0c400d10301c400c2c0c82c0824030345000c0343c1031000321b80965102c20390142c840740400e038a151420f0f4080d43c4001c1001c82140000c0102140b031490000c07070a051014610382c0914000a001d001402129aa0300210041015035411000203000400426807102c001d4072106591042c5140689040388171028a507814080c04108140c40c0c00d0000341e484c4240070998 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 11930510 1250 11929260 11929271
    0x203040605010b0705120f16030c15020a0e120f030310090612080318160b04030c0905060616020103110a03090507060e06070201110f0d0801060f090f030609050c1e04 73
    0x180c1d6800391003181c41c01410f17030304410305940b100c0714641d001e001f8804680148510b404040104100b102e035500100301c0101d001c85081d00305000e80c001c0c0b42e0003216021a0114909460180c02408105031402c2c090712882070a410615845014031265414451300c004483d12400c20398111503008aa60185100003854440c0004a042148880243e0140c20001080c61078445030050785812240c050b0b4041c40f80300c0c00161500745210800850003c00600340015140c600b03522380f44c2d2410315940c0c4244083c40c00d000500040d50786071000c840c401c1c681c10000d6008600d0a20058000d0105a10b02108284010501480c0d154058021040541c400c0090b103100713f407105001d44564420301c1c0c801c1e41106081c008240103501030760316480c11840c46000c940014600e01e40301e5180910754010788000908a800404c012074110134840b100740e50310b05000c1e1400307051000d40303030032102c0700d11003d0800f58940c082c44060000c00c1c444402480400740c41c0b608107801e00801e021280f410400901e006500c0e04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 11931760 1250 11930510 11930519
    0x302030301150c0305070b271e01020a09180f0c03020d0f0603050c1c050a14150411091f0609151b0206030402130e070603060b0304050a33020304060501 67
    0x32002e6200301075058443e1405c20015484245401c00d000700785017150011ba000c2d50223240c842440d945850207002c4010b01c0c0007a040028010460320311038038140580e0040c8103c820700c6801c081033105898000001c0d451210004010f800907082c228400c071299403a0500c2c0c040c40d640d168000700084000b52105100e0b9500781d15582048509601c40505150083c05608596140c0328001590b8220346500c4490b035203007103486403801e01c2c1519400729401c1807248045402c03174500b800140c00100040c0c00c016642d180c03588609000d9803c0c80b03036061140581400090305640e040148080200803800154081c5031510317009031100c000740c010f4103209611041e00310841403107480b103850100c590380169171150229a0030300120341c0010700200d9004150080c0000084180c0c0b107807a40d1100c03014000c0410702e00e0110003404a40780760b040b1001d600405c008100c04118001001886994032602881c134004800a102c0c00704141c071100c103d040d502c3c1d06001050b803600e030340255024500a017400c100503640e8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 11933010 1250 11931760 11931767
    0x501030309060203130b030907050a0803090a0515030a0f1803021e030f040909020409080d05010302040f020301080312060103150b040305010518071a070b040f0308010b1305090603030d09030203030115 88
    0x88003260b45038288100024080c00f11401b01440e00014440102d03881140c564000941000030b42c0c0010300c49600c08900ea003054944030160030300920058515800500c404401c145941c400141100503403500c0f41c0c4400d100000941c007210040100b4140121543c10a00e0000d4890396090284190304412070065501d10201008941d100c10703503c442107140900e085080b0f80600305000d4140d92207960b425140000c40e40316001022506069140001d0700e60440c4104802c80703e041d2008010244140011310400310008200d0341540007540c1121010f544900040b005440700708000401d00c428a140001c010104a000d0015284502d00a0016680302481c4c418103400d040b0b40e001c0d00f03900501080040d0103000d1840c0b11511410700075a403411206803035400c030381c0e03000340d400b11400c3d1154650f4206056002450134050103401010754589001c1502000c010241406000c0c403803c0d004022a5195500304212400d40d075070b9003000e12540300c6034100651a81c009124400d0003100b907240d1440c08621 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 11934260 1250 11933010 11933017
    0x103150f0c1b0204060f06020319050a0504031509060606020a0c08010c0f050703020106050402030709030308130b060f03030d05041a010e0705030c160c0b04060216030b070c05031207030501030309060203 89
    0x29942e203035004080b080380101c0788851107031026030304166900008200c0c800c0100d0400040d1204c0e4000f0b594403407001a1007514410ba08150703904100d000c0c80607140e020740c0602218102c0303800c8491180c00352030442c3c101001b00000100244058600f2000003107941e004260310403503e00500103a45420741d41c440c01c0307080c0e4249080307400c0003680f60344501d40964000c10140210038003a1000184180d1600045400ca910580f4240e02141c4680d008104040d807141c00a0344c001940d03109200c402e41d140d0380300121114054007003445000104030340b100c96181003003540e2400902d444e0900043c20541060b54100041310800b0f4118806400041052000c951a15010b021190707200ca00e150340300703202c0741000e420614003180c20031902c1c840d0101041d24401150050517810400d03941d00c2d850044060f1501001000f241d40140c034410041001c6550740d90000e501c0b1040d41007420b400c040c1468000d0440c405c06554100802c06d00341441822641980100d058074070070746a120b8030701d44592003641d0303902 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 11935510 1250 11934260 11934281
    0x3060606040909051606020c041b08010b0f090d2006070b040305160206030a050a051003050c060307050708030406060302180c03070c020109090903020c0906040612060b01050405090103150f 83
    0x342080104000b045991140140310301542c25615464001d04011004042ea503220b1401a0300c00c400e03d0701c60b80b40520440c441d8003251602c9070901034648602403d001d1051003801c0d07030040c0c046030308807052001c00300325035003a40c1c02031501c4c000300564500300c5005030b00314011008a05020340b00c80401c0c2806400c5030750068101d1010380e000e65503507808441a40c82040c910f000e00e0b8070429580016200c80020707500440200102045a00e415507003041282d900401090044008071402c101141000c21208110101030794803940c1c0e650303003407000d0f2a14440c1500003030100e40c000042000344007641d8030040c2134a01c21244501e408049803a200c03c3e54105840e101d400310310030004100200e0142d004000c080f4410b041c1203840c40e03500c0421500b100c14006094000d030304211a1242c1600c1c0c1451100c0e03014008990800000b401c00403800b25400200100030300c903a035510100da4850380105c0c181ca0050400520410103581c4034904010001c2c00e003c00c4080c2141801100c54900c54180200680e03038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 11936760 1250 11935510 11935519
    0xc05073203010204050d1709060d0203040501050702120409093003050703060f090209030705120a140f060c0313060609020901020d0806130f140103030807020706050307080a0b031507031a030606 85
    0x6c903d581c460304e41c0018100c07003460018204100d250426111840506104120842d0042e2240350034100142900e500600030380442d0410517844905070920b070305940585903890800103010f01c0c03d241c14001400801c6001c0b9410303003040c070b007540b50b4400355800070140c80e801d40c0c040c4415100d07072109400f5101240580310500320061802c1c402040d540c0d0250031111001012100c1580d0b0325400300d100f960b8000b110314041d81041c00490140f1403c0c03c01400c20407009001041001000e2407203540f54003010701038464100d0000042172101911840300c1500e01e0b0080010020b040d5030b0040c200c0250b000c0840c86000d80030342319680c1c500700d0180b03140612556011703005510010031a030140340148040715940e8040c503039a201c0100304580c0e040a4034007848c802d460325001c0341031044000e45008202e130b010a0400c101002009503080d030081c600b68018542050210f4008a4900000e0500603031001010202c201041000001a4103800003440000d1150000000400480626403148001c07581b0903080b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 11938010 1250 11936760 11936779
    0x30c0e0105030304120204020d050403120c0905030309060a0903050607031a1903110a030f0809010201110f0d050c09180601090501050703020c060f0c03030f0105040b040e0a030c0507320301020405 86
    0x117803002c00e0b0303501d005103200400044c43c0100c40c456280450b8802d4400340d000449030100303214040340714490611544464200200d44629000000345e0700d100300c0c00014000c41c00401c0c100c503618003640c002005550b1020550703c00d46000c0c40018000d110007a1204010503a030f4401e000141000d492984e190525000c0e02507603071341140c48801690340002c8540c1d40140c504031001012500c1065440e07502c500c110b80080c0e8030202030380024207441004104141100080040c540503040340ca04a074517040d0450008070ba0b503520950401900d0040c80440307078011111081c6c0c2c843e9850040515403055000742c0f81c5000d01521030b001183e03280200e28004000d0781c40b45030003503410310303100026181840850f0035451505c44840441811500161110b00708140b901d00140b061b41f9060258451055098074100300741055041d00c4c56035040004006800c0c031034070044030b5003440400d0180002410900348071003503942c0f51032581102d4070000160142c01e4014224852000e2806000b120121400103040160 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 11939260 1250 11938010 11938019
    0x1150c0f03050c0a0320010203010509010e060301020403060c020102030405070e131e06060605070506060913140a0b07020a020901080109050706110307060f0606080603010603170c0a020415030c0e0105030304 91
    0x44203290310000341e05002043c403205401c58020072860310384038030035528117641d4203a00b40060340b444d040000306034490f40144014001a100c0b600440d0442d2143c094910240d1100c50200b030081c8610f41000d444241440c1e2010602a01500110f0040e403081c412581a039035144080b002d12401030b9060101004240c0c5040041035903c2c806a030001e00c540300c10040030200317513120002c0714401e502140108a0105080c02800b03014405580c0c06802079440c0d8500d8986400754103141a4440b4005100301c0b4098000d54061200300541c0c1402035000f1a0001e10341080304c800f95450080b040100d205603602e10005c9001c2e4018005c0c2040940e03c81c00800540d42000c00a946641c1c45504402c3c2e03510007840b141001c40c6190041c4840031443c0400042c5440c103000000740010b100400103070090f03042c203808000040c030010b841552004660002502d07402401c1e1002e0800e07540710740c082d42c801d0600300c40007060390000d04044212845404160041c07591404d00c07190a1109206003541904203000410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 11940510 1250 11939260 11939273
    0x30d0f0c02010e061306020d0906020c040906020904050a0218060f0306040507021006061d061204080310030b040b07020c01080f01050f131d122505030f07080d0501150c 74
    0x342251050400c441e00c945202d012401617000050f1240e1650800607041003200d80500090188884603d818806941880c401030b503103410751010b50380181c0e07585002c401481070a0741035a5a07031000a0040c40681020030840001e03400c25000c641d03000c14241c40c24a02d5150202c11180f4580d48400c605080d81d442ca0100402020010100c1c4154061031038000c11000030b40c810840a8427a07515141d02e4101c1c00c2032285a11544c10054500400040000c4d00301c2a14000a0641c442d41c4910781558940e079014500120f000c0c0c0c0c0e0310040100701c8038400d01c41081141c0505a11446140c2c0c00c41b0f1340c2c110b841d0011210f007034090f0f0702041c8034100840140700301e0802c56921414140050036050516200030f502d0b00440300c0c01d214181040f40038854228a4590600407105851100f10344031381052074030045512119010850404140802c078419400c02c2000e00c207950030110200d0b40603860f01d00c1400d00c6003082c0d004580c50f070141e43c981400442c11800814510031120308a0703880f00b84031602655600d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 11941760 1250 11940510 11940527
    0x1120506010e090702012702010507060c0908070e0108160506030c09030a080408060601140301080c0910150807030608030a050a110f0601060207090e030c030702060a050d0501031a06030d0f 83
    0x1a04000700400b166032191a5483c0407405803c481d4000a4a01c8003080c1c0d0800848041e1208011206e0080410025030703807080981d600c864001c4000070b07140810305030030b031000e0f1500d40c40035081d8000da0500140e410181c01c020390403542000141e520000b440c44c0c0131817200300130f4040d0310303403004042c00820880300070301d00036100806001c0c0407100c50041c5c0b52a40c1f00e2a40042c2e00c42c2c120395000c80c1c00c00000b543d0141d04080d05c09014885103086505044800351602c05d5840c030340e8010f524010020b03d0988640700317568000e001e08030144006c1c64803c400188050422158800401c0c00d0100005034420700004544641800350707600780c00c04201c6842242e01292038101d502b010b01c10203000700401d4005100e02070003042990010840c03503140000c2041501e0701440c0098241e0014402c031f02904401000311242158102d500643ea0400c83c00c0507035403070240709544c80007149803030700100030425140000500d008120b00101c0d11035507884105540e80800c055120002180707444546e10060040901 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 11943010 1250 11941760 11941771
    0xb0301020f070b0403030b06040e0601030b0315160c0204050103050f25030210210e010b0109080c010809070f060305010303031407020a02060c030d14040606060906080f18061320011205 81
    0x11441c103200c0800100b0f149c1203034128058110300700d8140f101a45e0148980344030031000750054915076101c40b0790440c012000400410394160040542c0701e615200d62407044200703500420402155840f4201241d85003442c1800d003041c0c5c40740f2860201e100c400b00d0460050141d49840e5400c14a04650a100680804c1703003c80060003611700720401c101d11030804c0010803a944500003d401400c00203c41e0950b4515a552810b1000c00101408401d001045000c1c200100b0300701039040d80c460514581c5032040c2c075440034008101504010a06a40c141c1000c1c1c12240039540c1030110070003072a000b4200b02e0040e82c00e400540c0c008003500d001800c0c18805081c40340d4410003a2410b102c05032808400b0f0ba8524a10040c20300301c58030801003002814803031000078210903c0c000800b80d0800702c02a100407005001c501c00d45144c440025210b401c40c0c9426141940d9003002c2d20128286940c0a080a02a00c28200e4904084d007001d40b4001d90364440c0c000780907005030740e4500071180d1030718a0401020f001e4030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 11944260 1250 11943010 11943017
    0xb0a020a0c02040f090605010f050a05040b0d02030f010507020d030606050d050a06050301020d02040512060405030706020705010609060b0a0906030203091e0109080a08011502030306010807050a020a120c0302010b0301020f070b0403 101
    0x100401580c0c4504c10f1a84402c000c202c04105541c1c04d02d416001c0300c4058001c2038801003a4107042c001034454604682c04d641080c1d50008281028a00040c000750401e600203516100307403c0f801c0041ca00640281d40560840c0e000c44990200340c240a030291140c030701609001038418048044140d496400541d008400307158000b50083d158000710f400c0ea844100c401480c2600014204031a080003110100c0800031720b0003600f518281075079620388070312400d4406850f52341c001c210a07003484429840132006209100c1c04014041c0c1c3c4540d0210141c10441d29100030030708610001a4860003402224071824125000c0c0c0403c12500700c1025401b000d040d044682ea42d42c5101000c001003407940180180b100070703140d04e102507241002e4039444031403e1035100115001130080c0800c03039070450b1180750000c036181405a2141e0302d11100300e140c80000c007006840d400c4940e03003104445400c0311443c4059402031740240000000e0344113041c243d104180c070502504200f0001c0b83e002c6142c0007480d40d00a4840c2c40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 11945510 1250 11944260 11944277
    0x7030902091f030512090a09060b0f0d0e01060e010905150108130807050709021902010621050f060103030e03011802031c12020705011d060f0105060307090305060c0901030501060503040b0a020a 85
    0x3ca81610345403038400d80300b0240e0710010324046c283c0b03404400200101000c130814008070781040003068403402603000c250a01100841c1d13200fa40495600a01c5410003483c00030829142c0e81c15400e20722000a1069010036450200810008201d1140041500c1e1068546111030344800364003034003803120310100740c408000c24404d00c40060000c0c0f1030640100710b1064050b86600180343c8a55508155442c0310003568902070080010407580c1c1c241d00d440c40c4030341001685411982c1009400c0c070850600b210340760300520001004143d04003860f005c1701c2c203040d0001c005610072580c3e038030003400c0101c00c0a035040d408515181c0301e90b0001e112000558000c0d16008440c0200545010207031f030800001120540d4660388903610500c540303d501119411580d000341308604042d80c040444440602552780250400000504103034004d13950f0030000d6500c4030803039455152513260340115400007101e0b0782c000303420400002000c03440381090384e0046411084025081d00c2e5842840c001b07610404420701400b8484 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 11946760 1250 11945510 11945513
    0xc010e010203070209040609020118030507140103020c010203040308100519050402180306040c1805011412010b031005010f0509010303050d0507020c0a060f030b03010c051602030709020c0d020607030902091f03 92
    0xc1d017001d008a200d4100070074404400d2001500020b07070b0702044145101c0c130210070400300b840020004129aa4401c10032507104901c0d0040700a413040303000800407580004107001c1015404620300340b050504004a6041d1600c880800500c00348910b20410003d4450740300b030100e0f1900d075005207029294174450002d000068070100b810008226400c0c0c84000e4204c1c0e042101140c141803201116004000810141d0b041200035a03180f042d4011840c0201d40050307042440f0308d400d41c00007003118401001c81c0c1c03410440c811860082c160900a09a1040c200c800000d26401e109130154145c0b0340c181c03170700350600e182d01c400500144001071042d4114417441c40a0b08450302c41c0450300d4050b080b0303955034000c002c80541c2c0282c152400b08044a00a0307150400b2160420380c09004d841989012030190018100030340000380c9408a40e400c0203002c2c074400a003602000e1400500107074901d8542c2c0a0320050756422006030103c1d40c032420080c1d04107041c14001110840c017080314529041e04410404d030303401d459 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 11948010 1250 11946760 11946769
    0x201023a0e0604060f140f07120203010803071502030103020312160209010b0a08070e030613080f0a0309020909030304230a140309010215010f060e010903050f010501030309090e0c010e0102030702 86
    0x903141d00e6000d98001400340028041607021390104144000420320614190b4454140c0000009001d1030003203d402c008141210311640c05807010842514043d9102d5866a05850f103030352080310104c0e0714000480c00d622894406000782d034100c0782c0003400303010880f1300307200001041d81c030007610003443c9516405c0c58401030b038901c1c80303880c082d211809141c0d44503800081c015003401d6018284000f80925200301d452541c0e800100503a0045003004400c204c2540d030704e0807a166000d11640c02c0140d00300401c091405a034194800590103008031500301564271641b510035101c0c4414bd801034155490f40c80e00e84080c00329200000071410408044070140181c4d911034036428107480307400c901180c00002d240c51039507a04005503810724800040210195240459101420410f40300e524180700d03020442811682c0507040502c0215008030643e200c2c5c0210040041c0241403d0100310003081c1115000301c0d90300701c02c1c464181030240e80b000170014866403d005551a9140f00c0c01c03a8118407040142000588a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 11949260 1250 11948010 11948021
    0xc0409060602010501140301090c03080c01020d060b070203060f09063103030902040501050402040b070f031103040b0c0616051215040e01020705010f02030405030706090809040203250201023a 84
    0x1c040e03000203110350529841a105110b0f498100d0311070b1307040041100c041115220804100c980c0040c6203a622031a200310f0502a0003510012200d1614010300041d00c1070304a4001d0a40c180b0032419070341e042d9151500e802e40c00700c1c160b81d1412241d1107003000403040c840303030040c00040740841c41500580c0340700b0b03e2000406c5056444100c1c00039449101510460426004540c00360200700c070290b040a060078400e00c002e0181602c0078020039000040300042c140200520b0300d8040088040e00d913910345450207580d841c0d00c01c1c040c907042d070701c6110002a240603c0600300e484240103903452515040080c0c0d0300d1140c20360003070000c4030f0383c00403101415420750b5a4400d0b00410301c0280c002689581e000d0a00e942140c0300380350741e00015401003017008000743c404411940507a5020000092500d40d0f420490076a000300c04565800c02d10002c01d000d001015000c0b000c40d0701070450148002210031178004c03402c0c0e0080c0105007204002e4103040a21800c0d251090341c19243c1640d00c00f2160f14a4902154281c68 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 11950510 1250 11949260 11949269
    0x3231803010e030306010507020913020d030f080f0c04150201060503010513060501050904030e06070807050a0c091505090711010902040f050105030d030e030f03090f1c180807050402030c040906 85
    0x598458045880d040a0041c0c01c0b0098008010718114509100060a03c2c0305040000740314698010000350449171203441440748640250500c0b1680c901d40c40d01401501411216501181064001070740090200414500c29100314100c4d500742841d00f030300c0301e2513940402180c400755525194040340036102481030a2080d08207036031b1305800f002c031401c004c403c554042e00200c4c0140d0844c0b08100103e50030007220901640180d41d207981da502c01d410314000901800c070300200103000d00004d090030b0084e03890805054442c01c120030030214441c03200302c40031100c880c4034154101c1803403000074456600403909490240320020011808178540e500180807510807074401d40006a4410041c89141400c020034101040c0d241800c1281c40540415190740e40551504c0e0300130510008000b940c0413905009a240b0f003110710003228441c15030441038002c80f0341e558408400160012845840c070011942113002100c40c000040c2003140e003001d0520012317600c0108030301b07010170040000180111240c030401c1d0051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 11951760 1250 11950510 11950537
    0x20312030105010906020105012d030501110d06060206040201021e011503060204090b060c0a1b05060c0a0308090307081210030206030a060501030c0c080901180b040f0302090a0c0207030323 83
    0x2581082e002510b0449290001e504580c0b40c003005021035000ba0014000f1102000502c00c950040843c50845240503604001c0032942007400d000c401c044d000004c0c2850520050041c07040f5615030314200e94404e4101c0b4040d005a2040d4200042c00c04200ba0000159241400100d01d03600d8007090f4101150071a0310490307500e40e0000382000000c0c694407801d48043c8080310394510b018440c20303019983c1d26030820b001c4d1059030b1524004103c1c10300c00100c04002c100c094161070302e030b07e614030185880b01c0ca0f203c42503020031785984c0010601c51000c0111084207500016407400d081c40361a0b01070002c00e008110410b103065002002c009a61884041d603c103409038000801c00c80c1c105400101a24901c03403001c0c0a011400d008c4a00040681c030076180d05010030b190240703d10594442d44840341d5200c0d0b00c60a03a080d0006804211085d80103100740940e07000b903c40e00b01e80e07241e8100000841e030b10520750f800182c12501c1d040c00040c3c8078a01041c401003030403044146c0c910045a11a42c035512030410b10050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 11953010 1250 11951760 11951767
    0x90b040b06030f0d03020c100f020a02060604020a0c110301180b040309050108040209040b06010306051002070801060b0f0712030207020a090501080f0a03080c130801050403020a14070f03060c0507020312 89
    0x4211400c09096884a0150040c1881c020107688041c0d803104542c0a00b010f041e00400c0325000101d08101111084050b41e42c24000710b0b240700c142c0b40003548000010001030040078006085420b1500840e00720b924a0340d100743c0c50790b03030a451700c0d02c0c800152002654595203c0200708455096654402e040d03502035004241079085c035281c040d0001c41b541d80080c0c1402903140801c400750340c0c0c2003d21540710b900301c01101d0140d51003100403001010b10b50407856220701196041c0b6816a030002301d0f1800e55001c840200180740d100d2010702c103035000f90001c01d1200d880400c48000090404110f0300074400d072908001d81403083c20750000301e00860ba600850f000c1a680c1004021304042080207000121082000c1c00300000035490081021100070f00ba40c006020014480310540c0203118000c00400911000700a45c1c00c1c41d1400a485605a1609558404218646001d519000f00ba10822101c0c0950700b1249286559500c0d009130801c0645c51081c0b090520006004d0b0310148107644800c0c01d1200043d65 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 11954260 1250 11953010 11953013
    0xf1a0403060203040c051002061e130b040c08010e0303060d03030c120207080a1202031005010305091002030c0415090806010501030b0103090503030709051201060f03020d060207120914010507110103050415090b04 93
    0x1000c04010880038110340c42703c0140028819001032181c0c1071041c1240301e000ba42e4412003003278988440510f0007400c141e40101040244900900754200340c62135000240903c6caa1590156aa8001039030502d42c06203c400c80140042d002e5440107000d94240d0400f046210740d000e840004a0b0001801074501c0d02e00000c4007041241c1c40400e554004151420841c194108010000f819141c14000c4505040e039a40100d600b24a0400c08406556681c100c2503560b1328200580b803030141c06c9440303061003a50003541d0099036a07005e0000780302554000401421282c1ca8400110098851a600039051555520000c000b0440a10043d841514a074580400c018508001c3c440c5050106c0d82241c4c807a450803009001805009611400322038045406401817812804c1c410002d200c1c0000007491061401100401543c000d80079804507460001c0f080e800740c400400559192041140c014a2614144a10380d160760080e0f20158009000c0c1d42c150940700032243d580011940994000d807a8802e01008000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 11955510 1250 11954260 11954269
    0x5190e1303030b100e0907050c0109060f0b0619080705040314060609011a0a050f0c030301080d0f08010303051603020109020406080312010503010908030412020309030a11100206010f1a0403060203040c05 89
    0xe0883c041a20f07100202229560000c00030b03891501014403600405000c100102d1064003981c55a40844e802002113010500d00300d4020844039613294141410030b4400500c40c500103043c1c642c030048281841d9083c00622900700c9026074000e0156090080512010000c14502d58640c81003d2140300200740d20b040180c2081070303901d0144c0c008880c2110441c1c410084440c0b01301070303d44051440c01c1c2141c4030402d400d0040914060080c080f1403034400400001440b4000068102c03100751030303817207904024201d44000c0f60700000901015010030401c10400289290169042041707600a2000140c451001c3d40002d007611107a134020a050307440454845140d6070090105801004201c00810100d940341c1c0c0c0d10480c1703010003040506207052052075003030f48600034011070f00e4500c4000e0969034040c1051518121020356492180d01903910410306030b0b4240d00004000c2d041e10030380c0401d1005603240500301c880f0129a45407103855028244000000a11207001640c02144644a44040d280c200000d22 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 11956760 1250 11955510 11955521
    0x180b0d0203150907050d0207080d0513031704020f0f0d0f05030901030e0c13020307170109021c090203060c0a110708060405012003010905040204060302100807110703020a05190e130303 81
    0x581c0710383c0700881403141440e00601140d914582c106030260321040c090410300800d00034011603440c240d060008200144000134036840030103102ea102c0d14401920900100c882c4103084400035003241d0b4200d41030446d450071960b80102c1c82e600410000f0724400c284c2e1141039010040c03604440d55480411a0141c0e5a050300908440d51916001418a0603c100c006841c080c00001113a00307031a03001000c81c4a00d882402c1c0820140320140d00381145503540c2c014080250300c244044100e00104c2120010ba5161900690385001d03002001081e283c1c40c1d82c44a08459030001101e2804e11040618001c03030054240000801030005001400b12031410341419030179104c01c00c0b4042409502c407664840c00c6085001982d0540b031800303100107910750340c503c00306005007019003002c1d40c400d07c40404c4406039075001c801d46102e40d02617992440300d0b50760300b680d0303680e1042c450000030750141c8002d00c28401030909101d06050b010820300c492a89a55882d4480020070007500e20300351103c4c034074110750b041c19014040e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 11958010 1250 11956760 11956801
    0x60c020106060e0604030b0702030712020705030c040204050907080601021e01050402091303021005040201031401032402040b04050d020a050a0e0109060e070804060218040c090801140402060307180b0d0203 90
    0x1040f4000b180400150302803069000c0140042c8003440840d1080d8820400d542c07036650300c104411400c9801d6500655507031658803030140b00f0300c03c0d40f0b01340125052900a8508a541c090007030051629190416a00c034100200002d04520404058120700207445031266624400c0d40e0000805041500501182c444014040e404040c810844200040d5000460468403403104200082036100c0d0310048020b4880c1c440303103904540003000003000748040c0364094801c442d0402c440602c1c0c12602c10f0070304240e010318825824a00c000b48001c2000341040304480390010304c002d1071048480c1d01c41000070341003c0d1070f03081044d141c2800c9005005442c0940300714005043c40003e500298903201000610092006000800480d0049007624001100408400042100510600441d42c552200800060461103001c5040d80ac019144205007000c404043c002c070b4019250314a5551900740c00c0d1490070341d410501062003600303400081d80f60300560140105110310140541d8038105250f01c0b04c42102080d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 11959260 1250 11958010 11958017
    0x6040f1809050606010813020a03140105090a02130209010c0203030a0201020712020a021f1707080a110309030906070203030c01060803031005030105070c03030f0e06090703060509060c031f03050a060c02010606 92
    0x141c40d800706500180c0182d00090034038080c043c03591b0b0180c5a07108a600c020000f03400040c0d04c103010040240003c0c1c001c0d0040541e0008200641c3e5605038181d40740641840650002280c00f151004582e1580041c000782c00c06050900e58915903602280c90359000202c4440180d41c0441d44904100b40c84680d84d100171818401401b41a81540004403d01549400c2c7d0001c1080d180d1070184050003061441003100aa0b0340a0708107181025001d010084102c51590358035103012140301e00c110030002540d010b500c450005500700407400e0305101c01a400b25809aa05200500042c3c890780d4090191902403c1800040d60703c90816110000f5100700c01d4001781e1081c1d0504007003044841d40280c10b00c00b40e81d0103141c00304d0b030f0342200b20602c0001c0c21401010040d5000700c00030042c0c0f9034030001300c2d03000720703807048404020540d280d0184540310a0207403004118003000b007010075046040b58900320310f0015100c000f06e01c3e04d41d99a9803070345081c034011011280d498440c816100b80540a200b0702008043c1ca09 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 11960510 1250 11959260 11959271
    0x708030402090c1306030b130f060509010f0602060114060412050102070b0a0b0f1e0a0b0306090901020f040306200307031508060105150c010b0901081b0103060f060809010b06040f18 80
    0x14180c1c0c402c4d0300324055501015520030341c180d11581c410071080030329a00c0382c3c003c000202a0700c1030103000d48903c0c021240914030040001500e40c92000962088400701d60180100d6400c00803040440310403c3d0030281d1041c13003404041001010442c0540d4007500c1040016507604062602503070f8074800601f60b00c840c510b804259101c58a0b068010614100129040700030b01c1502101098841c1104c5d8000d030b084200d440021901048004c01140180000c4506200d1503582080c010300b40d2103070001d0514498014441000020803540000f00b055040c2d20071b009401c0c41d0358841c0b09090300200e40340380001313840308008144074541ea10341b07401400000e000303000390b90305100100b01e281d0003081d0111801c94001030f4081541070300303501011040c2801003001c4110b580d00c070f12541d80d4604443c07100c0000f000c442d000740c1c45036000e8480d0340d003124410924244120324101003581e40a8006003600e24070354a800141c6070740d40d5808020b0000c1c3c219110210180340c2000390485000c180c0b54030780d240551422 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 11961760 1250 11960510 11960527
    0xc0408010c1704060513060203071d0a031212020d02031303030c020c031b030a0212010507090905040b01030b04080903070b04090f06030206040902090102070803030406020304061b0f120e030708030402090c 90
    0x1242d2603940b058010744041042d440c0d901010584240400024200c40d07c08018803940c1a0b1010801c071a040c0705007028034070702c0035520410490b0341c443e1000078801046000ca24803c0c6014440c940c4003071950800040c1800352a010b02002ea07881100d2091241201181013030170590144903800e50a4502c5c40146514180361f404a80e0364940d041c58840032035103240901001d030342d0030010302e0611640640032202c0c00744103c41c0b0901070081921142c011402002000c66541075500c5070310700c210741110940a10342d1850b11040400d05018000355640b000070010954241c0741001020018040010840c2d0f44a10700100c0100b140c40c1208407004103814500b040002d0703681d0340c00790741c2074079120640142e80340c0010005038680303c095408604c0c280800300401c414086c29030b000d184224021600ae01903201d2403180d60f841900703400303213410101e150f000c541e000082c4945014000c0072070f14240052424500c043c41480c1d90080b4104482295000041000314245011000d8100c4541503103d4107041ca0f4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 11963010 1250 11961760 11961797
    0x60a0b03090d0305090a3c121206090c120507020102040b030c0f0c060109020403020a09090201050a0f0908070e0405010c0908030a0804020d0204060b130b030903220e0c0408010c 78
    0xb10500101050345490118001d0b1005125450125a000d220b04c1c0c400801e004c40300c8291881c0407601c005000c0070210b4510410300447c45144401d501107450b048484d0364580c10307035040c13980c1c180100c1c0b05030f0b4840d008034610700e00d0720401401d049540c03680d54440081424200c192070008000004590040c0b100b045500c2000c01035980229283c8000c07030b12060204d0500000340038599084000b0700c5400b00000301c0300d0325a402402901d000369821030041d42ca13140d5032000d90715222402070019008110203540d55101c4d0000c0c041c0c403040c4d4600a10501c1d40d0740a0585480901c0e0021a20072445400703000800009206000904005003003617003480b46020f60b155140e0040100390828403520340002400c5668405a40c078005500800810400f0703186c2c010070105400214400c1402996114003040b40200c3d03200b582c0c8034040c56402581b4041084000120311601c06a0450650102410110f42007442c0c080c5140704003909491541c4a514001e07085007510042800e400511102601d810300600c40d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 11964260 1250 11963010 11963023
    0x906050c04060e211501030606081f0f06030c060203090109050406030305120705091905010807020a0b01140f041a010f05090102150601050d0606020303010f0504060b030a0504030c05060a05060a0b0309 88
    0x30895040a616004004546550390320442260391405150340b080c41d001406030006047c2d0740500810442e10782c8480943d55034200c600c8110000c010701c1c4210b8942241203401c8800c3c1220444c3c0d021a419640f51798041061660350000c0c405a0004582050030f56071001042d8024034046405010541c50f58802404030710031052408140040c000000702082c0c0600c0481d189214040c000900361803d41008d107042c100d81d030103194000741820011405044c40042c04181d8150400502d411503403900e40c11001b0101d0480b2540d0704803010110850340c950b0f40d48130724240043d44c11850170a51692200041058062050f0350003409003c0c42906c0c45a6070003d00a425141c0d03949850a840e110940142c0300c2d2301403030441c40d00c158113007440401d80c00d81c080003031360481c0c08003085c1800154980c0d00708810349200c2e0040c1008218207000141c0107030302c80c0d000680c2084c0a0f04103075a03100301c1e5858140c00c0034070483d00d088815481704140b14903414803030303200001015a5900d00b820341c201000300175202c0c030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 11965510 1250 11964260 11964287
    0x9040209060105070c080f0a0c140108150409080f0d0b012102090111190507060504081002070309050603010e0609010504091110110102040303080118020f0a05030c09060c010906050c0406 82
    0x41500c00800c117280303c882c0007a040482c1103994032200b9010856480003006400c4500b001142400100c0141e251441a03031030034144c580440641e02d104010b598003450000e41c69006446510f05408110f1120007400750000e054640c580d10101919044141d42052000e181084942e1302c10418072640e0400040d401d440750300e00982d50302c03004001224680f07403003808000b260140943ca0300d1302101e1008444c80e003a11810030395500960b2040103881c18015486050255080000c2551800c3c0da25801410304034428104500b0311501d03540810500d410036002145190030030000d028041c54204500c078010842254184403c8855903038000140c408148071740e02410f811104403203054002c24200c00590300c40e1000715281c0c3e035071382001412140c081c410300701030441c4445100c50300d01c03440c003c6412031544070404514048406101f12003d40c4020f15402004500740030b600419950480280042d101030800800d504055041c0542107510291541c91120f10400c000c10145400992845940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 11966760 1250 11965510 11965517
    0x70509070c0203120409090203060f01080a0f17070c091a060403140f0f01090215040503071806120c0305160807090905010902100807120501080303160c020d080301060e090402090601 80
    0x24414404a80b400001039038099620f0307404a004200c81d03686a03c0502c100340200c1c03c881590702e8bc09540c08036041c081c01500419040141510041001e59003803c074110300c5801131810000400314102d5080d008200c085035500702609081104032580c0c058494000e924043c1a0340e84008074001030024802c511000301781c90029800b0a171048402c0c450b8040402c003102c01e036030041c110f11103514020880700390b040340300d000e40d43e9080d00003011000c203960a840b00078006100141c02c0041502c4494418600140c40d2508d540307002c16000340f0b0148421800e440346001001a43c11072404604203550b00600880e0910114001c11141d680011142d0807a80c1a40000480c00201d04003280900034411019400201d043c0700c0241d070b1a44a4030782d034860505540e40a03090540c4c041400140c0c0d101b88210001030b030051004c02c880c9001c006585040180c5130914000d1035044d54081588204480310582c0d039040302100402130140c00c100101d28411003110681810724140e400191102c00181105042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 11968010 1250 11966760 11966777
    0x706030c03020904110c010c020a0b04060b150705030a0e04090210030e1009050c0108010e040503090f010e04050405061801020903030d15050a0801020306010e01051614010f02040602030306030f07050907 89
    0xc18003a6044035100315014000f405007905101020301544d00000340c00c2e0300d96282442c0d003401d80f480441c988550725841108204a43c4650f114403000d000911811a444240c03000b19404a40c0e440008054035031090b00038540724076032400007400b180d80500345030b80110706044c6020016590f44514614030465820000340c06540350002516010f811141c500d0051701c4c22907000180f15000446c4030011800343c1c0c51a0b0140e0b201e6240d0200c1e1401a10002c20719801880b401915290100400500b150103140c295041c00200d0001015908280c07010b841e5a000f020600480e111030218080c558003c0f030001b50301d441000e0000c240c2d82e206290b0203c00c0d26503110803a58054444182e0070000b03200003003102421760b0311200c02e18000e500540d440c1d400702d001c464183c1807e500030820707100316036809005c04200b5940c60f00c520201800340898520103540e00d0144052070890391000d080030f888142d008513200e103001000d051920502c698010003da1107007400704642e54500c13510980c0704516140c9200c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 11969260 1250 11968010 11968031
    0xc0201020613050c0307030501060f060509010815060708030703050a05010512030a180302150301080606040615030207020111060a0c140c06011a0c0601150305340507021804021e0102070603 83
    0xd2402e01c008444c4c5c9402640000024004150460000c0e2000207016070030b01583c0f080b05503064440c9805803808261403000140c001c0b00550f25010358100082c10640c981000ba41d80c00072240d004075017007408641e860f002c1c030942c019140301385c4c0e024000640f50848180788040c486035403070141802036820008420307500000c0b0402480c2030002140e015120122411005603c140c294200b400307603944510070507000601d545024000c03807007202c03030348100069110010001100a907004003000da041c000d55406c01294214200021842045040d500280900c0045c0b00104003810f602d4000c0ca0201060040100784c07400492801e0445244d0504040076020030030b91000240143d2a0420041c003960340001200001c90000b000c402c0d82580d800c0103190b50354004034081d040c4a00c910f500384241e40300131080d590035040c0210301680403030a0041c14590140d0016000c10300600008540c2402c4405010450510341700009150310f080d41803081c071a00d0800000c1d6101d49522460082581760152500c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 11970510 1250 11969260 11969263
    0x1c0e1201090b091e0c010c0201052a101406061204020d080d05070f0c0b040308100b031602010c0206130b07090b0d0b010e01030207020a0b0309010612050607020d0c020102061305 78
    0x410590b025042410a10704281d54548403000b401d409000d0000304200c01e20000c0c400720b81803240c448161203031a121340e003940046400390844e242203480c00c00ca0881244002e002980c80501c002200001485052440701031601a41d82c1000f81d000c460810b0b000340000d5981e04000e0300c580301040400b12004c1d0303545000081081034a41c03005001a000007904552407413564004074032601468031005038902c845c41003291466000d61000c1c2404824401140c00248541c0300aa0443e000c0b082c40d03003640e034403205000701c0340d03005a81c651005010001120b50b042e8080c010f103882696a0300240400c0d06e0100741900d0082e249190003082e900642000442460007480aa0081c100c4100b000741c40d0022421448014001000b004c1e01150050980c8403c641c4a13008840140703030f000c0e0014510a103028501e200d141c201800709a40755490b035902240d00c1c0d42da40080d02c452401000144501d051000f4043d003000f070407294500400c5102d80146002d42d8002903050340010301034010000b03000b207608005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 11971760 1250 11970510 11970521
    0x20304030b0705030f0105010e010f140d020406090f0605040e01060c02060d02031e010905070504290f040311030a17030411030607050a120b090c1303020d080403051c0e1201 76
    0x1414080c081c8103100d40c041d44030300618070a4008814013071031642c070f92005617818002d10315440d0010341e03221006011648a40c0c030020016420440c80360a189010490b5426078000d60000b1000508001040041c01c8002c0c00c000c0003001c0c282040c070b103003034140f0281c5507035894140500780170300c101d0261400071912024122581c0801c0014215141d0400078494510343e003114418810309040301c0c00202d501c01840c4916801854952201443d040c9802d00310075580107180135150000342d80700b0804420542240c01000075030487e1600c41d2b500c500314940700e01801100c200c858003a038410388160000800111500d900891000315045d165034451a1403118151225010f07501409108248403140ea0810302500d100d81070b0b0303100c042d0140100c001d8041110a000103140d4081045008a943c100c03c2c0f0004000c18600c0318040140342d034594012503207824403240129090100041c0030014071405101c1d4040f4034a02c1059000d2000c010301d00142403812040900c2e100c0e8030342041c035008007042540311 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 11973010 1250 11971760 11971763
    0x110105070f0f0b06031b1f1b0803070908010e030d090212070b0a170906011a07080c030304030306140a03140a0605010305010e0105091f0f02160f060b04090c030204050702030403 78
    0x2806004160303d44540c21050684046000c0d100c0c41c001e6080060007514910303415203028110700501d00d104891a0003403455001004c06025003075905001250035100c0001ea858003c1c50721960b04e0801039801403a00c40540d01940f841e034906003240e08400404005c9038560b07030401c41c0114041043d400092080c041800781100140314012002070128081806046a207510340c8401c4070312001c0f09480b0510490440f0320103000d41100300103003c0080c0c1d141c8000014100c100d4924182000c642c1c80300340e2a072196000030300552002c020002056818040c075800790481c00c2100e4000e0715000c001c604020154007000b440003042910000000c031040013043c0f4800e03000103051045594a0810500901e000765012000394200000074110140c00591080300c002007044001d0b0328100f040c0c00e1802003e428000d0b211446d02046981040c5140000c2d1101c3c840c003e6410020150030f03860301e001200c0e16a98118000d90070500404007150324442c003607080300d80540c0e02007007995507000304a00b5481140c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 11974260 1250 11973010 11973023
    0x17060f100201090201080606041805070c080a0206010807050a08060a050402030c0409060b0406050f09040602070309050409110103050a0b0a05060706090605010b1201050a120204020a030b0a0603020a09050d110105070f 95
    0x42455a49905411020030700d13000780c0381c4403250f0f01c42d0014010300c0e102d00e014151a65221003096880403140da80060350040241c13814003002030645d500c808141d80f21220325001039000c100107000c80780d814840d910041c071040302e584240344c0c1307001c660310b4460000500c91030010396030300300040c15910305000e1941c1040c0c0042c420402122285001c2c0008c0410a00a40c0a01c0c6446c00120316820800c0211420380e4000b04098500d42e0b4981c2c40d8000f95102c00c0b4100c0421003400310000e034544950003554460742c032940d00750f4041034260000500f260001054090301e5814400c0e54811904c1b09030004040c1d440c00d07543c50764dc5003168100200a4003031440000c00381d074230700000018040b603c2d101030610118083c0080150b030b6a07a5081141c110038a0184001c1000caa205100040c0b0f410fa00400301d40c1c00f90b040c003207541c0da105800178054007019400304011a4000442013011648170005902a10044900d408800d12944a8101e92091101300a06000c40003850b00e05101403e101044503035800003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 11975510 1250 11974260 11974279
    0xe0705030304150e03010902010207050d06140a090b0f04020a12030203040b030a02091203030103110405090a02030106091d0703080703032a02030a09060807080c030705040512070806070504030317060f 88
    0x441030f01c0001851041800080c50440700207401d0716040c085c019125805a00030540c841c20802040304d4034410090481d0819a20343d802d07a2241c844032585441108104000504040c481c02e100000180c0140f103024400d454400300401a511604410203503410b040c0d680308074050924050f482c603c100c1d000001c480801104224007110380383c0040c140e001c025039140d4a840303e261540f076640d0000307000c02460a03140b0081401c841c1030651100303900480750707011680035440b503030042803c6418940007000d41c943c54202d012001d2180c0e9a001414800c020001c160750743c0313103449840340c03030140640040406403204420110030a0610082030410420340749113000442150000c0c0d40d0ba0f110800600104084020000d0b0b0b050048335010301c50200c6445005031030341c81e0369003407040e640000c0000b024401c0a00c00414982c980d10b00107090180e1040040000505240c0d1184c40c000d001001c440c104142004280f000a6008900048101000780c003210b45444210001d0044081b51002e41c0e08084085d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 11976760 1250 11975510 11975519
    0x10c020607060603050f0303010312122301030b13030c080901030204170303010e0a060501020303130507180504050f0d1b0515090d0f0201060f05090c0417070602070602160303030e0705030304 84
    0xf0351000c0c0840c0d120b02c084070f40384201007030010b40341d0100740f001902807101c414074070468038000c0c036a0301c8910300c030988005248034214081c040c078800c081540c42d15001d402401402000740d284084d130340180e080d01801e40c01c80700c80c2d50028500c48201000515503400030511401590103074042c0c82c0a440342501d40c0304031107194610203649030000d02c246002215407002143c0300d418107102d003400360358048c1c0c05546590f0743c961a5204d1024484c500301c6882c03081c0c28000803203007081c1160171000080a0008609801d05052081c5006c00a200d400e03074a400c4001c4000c021500010b96582d4160306050031441140d01e424154200800a117108803035108003010888a2500481c2440750840245c55084a0002e2444100e080b1030060203501c82c0944800800d000e90700d80741c034000b940306403610612460b01c0d855405112200d00c010700391088a60000900b40102c03a0140001c00c060b102d0f600c010181d190b990511450120424480a000e05135244a400d00c904010300c2842c000d407801a0031241e80f169034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 11978010 1250 11976760 11976773
    0x30b0103051c09060f0804020a0f06050403030e03030406051218010207060902130b22020c010c0e030d080c030c091c12020f030423030f1b01120203040b0a0506010c020607 75
    0x312500803403805030411100c070b4014000c5031010184d481e140e03207071048400807030f9041e1811003000d08140e03804803c0c000c5c0003030031042880031400070f403070b80e90b68840c0c03100d14500c0d001d0300c0c3c0c03035000400303d1284d0014001404800d134400d0958030740754640c1c000d400003a01c0303d001c000c800d6080d4141c00d036400c0d400090080c00388502908210001442542c104400700c07900040b0004407002c080d03440340d101b10300350109110500e007210101542002c010f0010300d08403812804508480164601e4008129181c401040c8e030f20301440b007034084a0f030b10305081065140071f6100310304520000b0500e8202d020041189190b50b00da85652024181304542c041814901504018000c40e00d044d4402c0010701c582c1800140399080171040d10102d808681c000465110100070341c00e81c0741c0d800d0b0714841e058800d0300902d50b46000100b0010003150f4030b49848041d200da100700010645201c03201e03044141d40c01002031100207080aa1410342c02011440c000a15407100c2c1300482d031300c903000c82c406980484007084c404180a103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 11979260 1250 11978010 11978023
    0x30504030c210303050c090a0e0702072313020c0d080a06290304031704030302030a05010b030103030e1002160807050405060f0d1103031902011b0201020f040603020f04030b010305 79
    0x5218035028a40e030b0389442280c2d4100e0315500300c5840c0c5100345107400090198000941002c07903883c00d82d040c00300d1039010039500d001c0d9600c665000015035040c840c19940500445d00644040c0e911146c121030040c107a01c01300000c0c96045406107441c4d00480c0807010140c1e05840245d0351440c10341c1c0c506012207100804c40d110a4441c00e504034940394000075000c5504a20000b1100a501000300b0001000c40103d0107401c010030a60500000c01401e00d0b1845031400d0741032103188252001601e80c2040001d90003241c0058001c000300075030800050011035040340c0c901a5103c000c98200d40e410810800882c00c10014045a284582c012240440c1d081c0006c0b41d0318050f280141d41c00c01481d03075644200640b010407c0c1465421131500045000418880d5040c00c00c3c10b02c025040324506a020311456407000c0c0c0100e51580141d560744035046e034580c0c45030320701c0c480d10000b80300a50402102a10844c4d0a2245106030018181d000540a07000301311070058170001d617082094041d05696a09041d0344401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 11980510 1250 11979260 11979263
    0x20307060e0c010c060209151603031407080c0c01060806010b040504110906030c030408040302090a02070212070302060f0c0a0206041e0608100302010c02031507030606020c0315161b03050403 84
    0x7070a08030903028440d00024003400e44503050355851100340c850b4840d17100039131100c24410f8110000460150304122201c0040141300d44c946514040210700d800c2c01004ca0341c4030450200c1d81440d078018808026408254036402490410740315503182b00c1c10003c2d80c014100b0307a1000d40c9500036080005280e445880246c0221031054a06006c120ba541c0390080d41845050307015540000d092000c1460901110301540e4040c0c880d2213820f1503c1c5c3c4a40004507425402c8a460402a40014101c801c505000640c43c9440500c1c200900c001821607000400c0b60045440040820501084040f4680c004101b0071420755000340000340d940341c6603070a4000148806200380c1080e12807610005402d441044401d1040d000c002c607101d162415a4011141211500000e076030600c100d44110780302d002c5e2803004900a194a403400140300f458542d001e8200444500014800d80010794040301c05101512000ea1001516102d00d2000403000b0003a04e18000340200f40c1d250b010528001010940c1110081040e603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 11981760 1250 11980510 11980523
    0x90b07020f0f0303150a080a084807030c030f03020606060a0c12030f02120f07020d0e090403020304080303150901090b010f030b060c01020723010603021c020102070f06020307 77
    0x207900165845a440900d0800d06150364800c00004200040c0402c8402e0140301c020103130040142d070340e014540342060045042c1c3d41c00d903000440051070700907801c0696480b43c0c00840a0300400c0d01e240c6603410f200b041d40c01d60803450507407540b8011030f86040c402c070b0000d5548014241010780e00c0b0f0424100c6010700031812030240c440c0202040042c134040b01070314802c2107580d891400b0454140d4500b81c480c0240402c000c02e064503031000306207008030390002d080311021600525910b4076000a00e00d40342c0c8009000d03181950060440c40002c030703030b00c59104400c02e00b09440030f400948680c5001c91075032080c0d5201c07a103240004406c0c09082410320076074003856941202d012216076200c440c91000c071080a00300c0c50104120f0740100c2c00380d901030341003025480802040c2c0390402c0694449542680d0111504860504407000c404010382290640060300711103a000810409003540d0108135021024041c0300403111140c6c90300011a032003080410702030a04007000518459441c1c034041d650350812030341102d20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 11983010 1250 11981760 11981773
    0xc060601030608030304060e010605040f02120f1e0907050904050703030807020d050304030807020c0a06050d0f0603020f01080c090604030605040201111b01030f0b04020708040e0f0606030105040c020c0301090b0702 94
    0x6600c00d010b40350a9425000181d890760b240d0303a50f224000e01c00c01c0720003c03665403600d200042c195a148a00011180303d40405a0303101700c400c00d200301e03801d002015104c0003640802440001140d8005c0e81466484448441869454146502d440c0208940c071140c2d20465403030030402006808284102100d11039218030441e80c403119026a143c4242840003000241c0600c0040c0c040707889030100d15003154850041d60305402083d000700d01200d4864020801040c00020512248002d0b8800c04148102d04d1074100009411640003420f44007207002842d040120500100e40a00710110031615a40310041015a6403562072070410050101260b0a901080c181200c44164140c0445c011400c200021403540c681c0c0c00d20300c01500180907110040082641d5101c0f01141900e4910003442801d009a030460344461406807079403401d0b080100541d82ca10707074007414840f543e12200141ca041d140101d0740858840c071582c104078a071048a44a00340d01d58200396030710081c04102c42c60203000b62400c1d4241d510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 11984260 1250 11983010 11983021
    0xa0504051008090a020d060b090117070906050303040b030402061c0b0a08010915051005030105090c03161802031506030a06030b0601030207030206010312020115060909060501030506010c02011404051002030c06 92
    0x8000104407103082c1d00c0d4104d40e403180c0051030a096441442c52180c200085c2e041d96140c00314201c3d000980184100c0356220b170700d06d40105d4080140c2c0f0001d04140301c2c01d201e01424000825264000d9100f0382c82c0c1920040041011552501d0584030191204d0300444004109803100c400500440d0b400c0d44e01405101c0c4000ca00e030306041c0212000150846109585d04412020060060000618280c81d4a041000108a5540c00e0290300c0c00b0f111904002c16001d500f600800d130038141c40218050261020304800c104040c01001c120200e01c058040040c0c8940d1034080c100007441045480d41e5103d0000410000c2d48400785c0d04c0301040d03e020754040c9003990340e0500150b00b01c1c860700d80081d0250b840840100009196041005800e86c4a0310002c6060020303014090900522508241c0c040356404800380100c50481c41441d00514003487c042c820b504000380041c0c24540c3c2000041e04100c0310b03011203112410441d04403402058050010140f003409900000d45a40144158100da80600c1e4081b50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 11985510 1250 11984260 11984267
    0x3080a170411042009090c0c0102070308040512030f010308090d02040e0d030506040e100203061807090305060604020f03010b090109031502070309080a050715120501030803041505090303010506070312020a05040510 94
    0x21072542c0d12a15941740105020030000d0444000748964040c0f00e0400c02100001c0c02030020340801440783c0c882c075041e810325203402c0f42800d4507050240144482031081080c2044900d584504407904038420359603951225010580f0030084640180d007241c20400c81026110380010381d0544400306580402158442070200310a40e50a245c0100140d8008100e1000e0181c0c103a008540040000700914a0764a0790b05180408441c01c035100c0021495803002081480340501c40d0b6a841803007150210b2810500d4080440036000600500e1f80c2030702c0102c0c140340c050340035070385e50806150454042d5007404501038502010750711404007200040d040420000d81050006860302200e035000010701041800e0545103c682070050985904001aa02c003a081c1c1c5003461050320f01950082000720364030711302401e04405c104401d1000c2950075241c14101b1490a40101c15203040d030b036089840d50b03501d004505040301d081003d100482d000710302c0003d550031a681c00c60020000c071003054440301c1260076040c40c140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 11986760 1250 11985510 11985551
    0x507060b090705090111010b04090819020115120f0501111c02090a0326030a14060102030a020604030e0d1703070311070305090105090604090504050a0302011d0703080a17041104 78
    0x42c00840c4082c4102d400560065140341801104c22000003001c8041a000030141c902c1e00f41d00f501c5813040001c00b0440c2d112074110b080d03a122460300003400000014054114000f009200c1c502e00a691342050008108c072613140d8443c895048002401002403410b400c0c0041d6100400088000c40c001010300a007403118001c0d00e4100c100101002e400610756110122140c041d01408007012030030125600e0820046400b45000b62040640000c0a0190716807811b088040500414107552003400710440c0d80b64002469644550302d8904507086101c46000701c0d44814080390003c00150106145000066825015602c14002c5642c103000c48090480034070700c2032242d160003030002802041998482c1d401034008000c04000944103920342503a6042503011139100b503c00700c544c1d4000620102c203161b4240174907406040d090b08a103400001c1184610b40c0c5460b00e01c40140340b20004280600194000c01651082820310312003001c5c586031a1512003141d020140c1910710403460032341800034541d00441d80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 11988010 1250 11986760 11986771
    0x50f0f07091802030702010e070602010e0d1b020d03020c1003050906060108010f2706080109110303030c1b0c040603030207090608010507050a030e0f030d0902090604090506131109070507060b09 85
    0x14528030091071411000a54001000717a402d564031001a44402c0d0000c100600041072258000109949000751050421400100400410604107140c0800c800039014841e80783d98126181c82e0040c80c185002e900b010007000050b580304a07540850303d101c54054001c00c1c4500300c0002566956654400107484106080c0680c00c03880303070380035403d0000082000f26160242c0b04016480c140c500d1740400d180a9441c1900f0014499468550880800c0105200700701004d0045014604610705003412040c0c070700400c2e42c0c01c4036450420b140341028034001e11484420a0b8046d0092000c2074881c00c000c2d40e100038030301c5584011490101c002503c0e4070180b0840b4050500d580d1824070b0a20b41e850100c010f0180d0b003c0e4001c081c0100d20a41e810701c401040182106000d0103808500c480340e5004200030b5017001000603018609011300c0c00002b90001c509036074030450020340d843d910005400c049004000d032004451b0803112010078410500c0e000000307407401c1441303401c2c00e02100301c0c0c1c2410b00100700342c165103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 11989260 1250 11988010 11988029
    0xc0601120f1e08040311040b040606080601031109030a0606060f0305010806040308061807080106120b03030307050f040e010303051801020c0310110d0908070311060c0d020f070204050f0f0709 84
    0xa4440002d4200507101c0414485654025400c80c0c95889040b400c0d840b5a000711141e420a070a00e401508081c062102d460408035801c200d503600e085005070a8801c0240010304142d60781d801c280b84440c41405841c4070b0f140103003c8802d100308602e07003000200030303e0190710041004070b915600070500c640282e80c10b86c0c030711001628080e11a69000e80701484054980c0758450040c59000340808244e0011030b20170900396903404059450248081c02c0141400341200c40c540c10a1280c1c811a100081200d0f000242031620742e5507130080140200c030394042e0350010f80b00d102c03c400000042c154440701825943c0c5a000701c464100f07622100580c1e640090041c0240c1540001129051904040d0f200c10080a0111060303803501e07100f241071100310f0381d04c0030044034850000702c1c02605055128250710041801d03203000b0855070a094981400c5406041d0141e0040c540018045641003065001e032200b299002c2c0041c010303814800c3c080701c2540e50443d4240c802d030a402c3d001910981c0b01e0110142115030189 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 11990510 1250 11989260 11989283
    0xa0807050d0807020402030f0f0603071d0a0b03030706050a0f0501080604020d05010e0706020304030b0c040b07170708030103060912030c0509061e16030206060409030504090e01060b040b0c060112 86
    0x201440903461141c802912072010070f0150801680f0349000641c03190182000713806043c5045040c41b00f0111380944818000c2e40418801d002d0309140440c068420500a0001c40641e910b40d0503103400f03031032603401064041c00040350010402500ea000680102e9062005214503003000b8102c4080701c20174400c1d043c29900ca140410094103100c10195240c40c01200041440c500020303c06140508035070003400140d00001c0c00f013060005200c0500d401c0303c2c008051910701407500b140001c0d039018440c0007601d0b502d07982c0c08602c01d03560356004071408a644110507945030740e56410110010181074005441c0c100c3d080d4124089644248201901c3c0d80d0b29803182410304081900b400801c0d00400014446040300342c40300580080061b003d4980314150f884508a1811180b900a0801c0000782400b4059400c050310400004c3e040801d580030f9502c1050300007102441c608070b15000d0b1030b00e98849400300c540094041841c1862a00420032010082e04450843c1d90762030b004850f44c03240b404007404d60004d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 11991760 1250 11990510 11990519
    0x30c01241d040f0204060f0f08060609091e03120a0204080d0f021e150103050303040c15080604050705190e03010605010804080301090504080705010c0507060506010e030a110613030503030105010e0a0807 89
    0xc840380d48040c1c001707000001d006840d142000400342043c1c000340340b4108000e03810000600d04004080d80454180c840004904090300c20503030b01c4060000c8420003090010944441400c1001a00c1f24060841c8845401c0d0401e084070700025071040c09641441e000d10010003800070300980e601c07481c40c1c00640c010641d8607140c4a0403103417005035000c5640103020383c0349907803000074501d4840c42c080d5026801469690800380703841c004d400d90075070001d09000c0c01041540c40f025000b6420310352204041c0c0c0d0103c0c160313490030011200f80c4180f40e41c02c000c06d0012603900c00320a9010010301c010902c280c000f0007125071144019075211400300c9006100c54001c00052101c0501c5400442d00640b1480300c0a0500e41c0c160359040c203694140d44403400003440841c0c2070007400201d000301900948203013000d162403010f9201003501c4440000c40605003150341108204261204800c846c0081e41e01402d4506140d260b160844d2294028460310740081c4591071071a5091074200440c03c1101c1c41c0e00e0007002c20a00c2d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 11993010 1250 11991760 11991773
    0x3030709170309030318040501120b0703091a040308010305070f0b0301050d0c18090215070506130c0515031806070c0b0606040b03150102010c14090111030c01241d04 73
    0xa5030210031440c00b00b401850a151400c002804400804e003051403c44800c2d02c043c4012504160700090300c4603901b00d55103010602050180b070b0064440d10340411010134900b00111800b0b03501048500190314030b030401c0145170788032246c541038900c140e007a84c4d00346a5072401446135203142c0c05520210001000100074514208040d03ea00502c039000441c0b0300c6a907248505003605059a20088541e00c60001c54210f2074100d001c18064108040b0160800140d81c4816a6800c4010440710b2107102c0d000d044e5052203003081a000080c180207008a00d4018000c0100880e0380003a100c190b41080f08408051600c680031585520510349030743c42e15082d29454586407005103010745995080942004045240c0c0340200081d48038010010640d00908180d41c00282125140c1006400700035a01088903c5100708504440c00d0701400d2038215003c5980340d000b0350961040007001d0030150b207403160021040850b15070356203013480c0d19403960320002d5556040c10000c0d4524540101d801030801c0004002400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 11994260 1250 11993010 11993039
    0x70e06130305060108100e010207080301060509030f0105070c1a0105011b15020712020c01090b04052101050901060509010e060303040315020c0d020606030c010507051c0210020a090509010803030709 87
    0x40c9054002695540307840d1a8109074003a002001a07400401d40d411541542c2e000d041002580700000310301c0d2490f2901d40e04081d0106005c1c42c000c2050010348c080b140d03034080004580683e4820300800080c2844003000d840a040030400b2a51040c1c60000c1620079090341d13134564100d0303c2c10b85400c41000c1b0500d03a8807658803101241201c1030304d8031040304170345950036201504d030f210302c44d200c00c0c01c4020304800061700d400c8143c3c410904008000714140101030f2044140c2c4c085440a8552000d83e800d00c3c401d20f106a0000c003400000c1d5864502004030140054000b40111030080d52200b4050340c81d00c2d003d41400e001143c04075050b80c800c100410000e843c1e00e00036041c02500c0031300141040382203040c0504095001100c1c40059010301c0501002e4030b01403081d00224502420081d25207510f565a981e00d40f6061304809403504001a12009041d0091106a05114880600310f580304491a0040d02d4400140076550281c4950702c0080381c3d200d000400c0340c0c02000c42ea220300e0030b0107161142d01300b40d019 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 11995510 1250 11994260 11994277
    0xa050c03040f0602030a120506010c0201110c09100e070f050913060b0d06080d0203092107030206041205070e19050714120108010b06040b0a080a090b0108030c0606010206070e06 78
    0xc401c00000845a01c040d40100291006138040d66517010f0f8000f000340f000c2c101c10302170b814261902c42030040070780c0c11020144c1e003250f0a0810f07000c082100316806081c4105a2200c0360441859410007140203403001810003a1010034000303a90b01e4680a00c101c520380c1c040e8045c000070600804c41600c4501d40f480c005007044940311320104156445410b40a4907030440b418009019403114002d121121040c0002c07008400d080c40250306101210000601042da4070150700f0780092520251074032002c052001c00c000d1500506030b6659a03035210b500038072100800100b501d083c022000080f403078a8403400e189016814624040e40743d01000c0c2c4282c07006050141001c01440703648041e2002280c144805007604423000c2c80440f00540c1740012950a48101101640c841c3d0400c11090013441103036826a807850489203800c0350142d442907007101c028070014401422201e845000024071400010040401d072003c503064483c0c42d2612001681c0c1c4000503945500419124000701406040c12009882c401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 11996760 1250 11995510 11995513
    0x2060f090307060609050402040f0b0105090409080903010c1d011b0602090f030d0306060306140105030c0307020a0203030409061806030b0a020f09090103050c01020607020706090501030f020d0f05060a17030a050c 93
    0x10b00e2039941404035803280e8843d942c81d54807503003044250f00c0c3c0303407242444d00605041d0034030880603402c2c002440d911030949940c1c8140c0d56100c041060041c068140c402410000c4c0007005035404a680280090500390703008131100c84004103c8100e5480b4903040780c805d815860b40c15041038a40d076584d034041e40121140a800c13a400e0740d101207090307404000b01d070044c4215032000900503080c100c1c01002c0e0f40ca0b0707802c41000e0000605c0e6001403039038418101c980c40b6010340f2106440341c4803c04101c0c2001480c1501035070510003c81c0224400c504c0394002c0085480000c0150032241c60030f4000e80907901c042c80090804002d00001445149045d00142074521000600c81e00d00422880080c6040c0e07420703082681c40380d1000c07054525650b01000210380100751400180701080ca06403000304807a1301e60088034105525607921205256450b0162012003c80140500c00000c100010400421040742d05a10800f0b40d40c0e030001d924410100c03400c0607524034002131440c0c80c101d81c40603241d44e071021141780300e02d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 11998010 1250 11996760 11996767
    0x1b0c0501090209070908070501020604080708030615121e060a0501050a02010603080c0102070515090703030e060712020c04060b040b07110a0b0a0e01120501051c03180608011a030702060f0903 84
    0x140c3d95900b009103d007110307407103901c1004d080503e10762400d0515004241598440c0c81400003180400054580d02580411402d662369103a0010500705100b00c0d0940c01c0002020540754040e408090900c0d104103c1c200c0710914a421146590850b40004d88100380c108060200621440d40310b44010842280c2900010071101c8c5da07603584030a5540490041140390358003042d404200b020600c40c601090140203c4420a4100324015684032a404e2000070309000558006a00a86826054406e8590440c000040c1c2500181c4043e44807002c0c000c43c0f5100c2c44c54a03101003000b50380c1030160740582d502c40700d0b100e082c0300c020399821110001c244011548014040b40005404074258004c005110803030381c40701403500d80f07403001500070380c000c2c110140881e081c40e0040c4400c1e01c413140d0b0a0031401c840b5100191807001d034103040d9240400103050107515442c0700d101282264100007810f040315000001104d00c0f406204100b0100c2c00705841d442d0040c0c01c010013007044000380c031821b070f50403040803c2640d29 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 11999260 1250 11998010 11998013
    0x20405040501110c1b01020106030c092a18060801080322080d02031305040501030803070804061407030606120608030307181805062103250506070206090d02011b0c050109 75
    0x107035000500344c0c603003c1c1c2c0a83c2c0f02d92403421070501c155102d00c4003030000f400501d095a440701e131004200d01816544556a1907414080781c07258000f582d120034185403558400d68007034001000f214591740006031046400e00300144142c8540c0340d403412910b140c07002e1420105070a00c4000d601c003602501c80f5030070019410100740c002d0706000b035000422141c1c000f960f40d00128400c50b0a03a180036400a403013585482c00400c04140314100f2254008000d00d04829280e58603c0c2070001461400f50146640d0324038810842d407140c0552110013a2041d60300c40801d81c0a680e81d4420981c1eaa0740900c0da01c50b0002d00c08543c0260061a02e081e1b41d80040300000c0003540c03101c45100e440002503d180302c00346e46820622440303042c0402d200c0d00c0030101d05103405070000c4100c000360341e0740728803940d900c41d84e944601d010b4140c10744a10005986644501030321018103041000a68801055804600c24010300c00e00c01c00300c500511648c03003100e00c1c00720b0000800c04003460548100c00f00340826911952218695070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 12000510 1250 11999260 11999291
    0x2040e0601120311010506010c030c2405010501020735030f030916060e011706010c0c0b070303110301060806010c020a08010c022d060a02070c0e090a1518020405040501 74
    0x80c0604061407071002e4505880c10000c004c0604424008540e0745020288001640d000b2a1030a12a0b0582401c640170001490154030b034a55882015039601142c00700c0c800b02c503015030025412140c0c26403c5401c00f0b92a00294420980101d400550302e40006004035000e05008070403040a00f80441668100311800018031040c7d442214404015040041c0c14a90b6403043c03003041014014030319190380780f803e00c400040c0c51152803031140c0c1515800540010400d07841031744070315091a4400044a01c4075034a07900001140c01c02c601c114040707030503c1d0f40340f002e9550400640b0b048403003543c0c0d0201c640d19035100544001030101c1050b030304062180c0c0702140055090150000a5026500030302240c2c41d22850116401c03d2281002c401c428150340100c2408000102107401081c074020059840700285050f0554030920303484042440d403c142080752075031000c070f6012000c0e4059610481c0505c1c160040500b118030051007008800341507002e48016007055030100341d10509c940c0001441031503024172034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 12001760 1250 12000510 12000523
    0x1090b06060a080a09020a12050a0507060f3009030203070606090902030d03050c0d06080d08010504051902090604030203070b03010603050c0307080a0b01090e1008010f05160c030509041802030609070503030a030902040e 96
    0x181c686a01c00c403641801c00204110f334400800441c5000102245800340080040e80c2180412124100e528180803081085d035200080e0200d03810000c10040350149006500c0340c0200070203880c0b8030f16208001492420b5805590b41c1198010040c200b1402c000760107070001d103000b034822000e500f414404000705400c0c6108001c0a4210b9500421542070001c00003000700324141c0207140100d05082c1484154650048240320008520401589070f0b8210300124000e07009590000e9898415003200044000810000f141030380c14070780c0e00f0320066544542c504414882607d036200024103400c005250000a50b0040c0c00082051420499036562102050148441940c04a180c0034400d0703410004e0381004d05c581808802102014421854901000f800118201c007424007440034400c012010584110704a5551100088c020030000342d1100303007100b0600001004a020b07202c0c440204440030000140001102c41c014000e620304012528220050850b44404a8116440300d405805141052058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 12003010 1250 12001760 12001763
    0x6091109060c1f02090f0102010908180d210801080d12020a030213030501061e030f11030f01020a05040f050415090f09020a030506071b0305091e0303030901090b06060a080a09020a12 80
    0xd40c55901e100e042281d89034000c900300e812341e03151015407000140280140c848040b210406c41c10b5002805010800311106048018041000741d199640d8400c0840405802c0013000d030703a4109940c0c1c03600c10641da10092550500c010520030042c1004144a640061101d20041e10300542020940608950003221a40040340c00b80d44400c0140260381c801c6507401032200039200151521481c540341c50504ca07045107006451141850808125a1030400104440c001994000c550750144618001d109400c00d000348000101c0c901000149440d25028030b903100844c2e4041e00d6102481c013203064000704100e03007011800355142c89084016035210403000c0000c5000318080c000c240303802d00c80200700c04e00d00b00d2038800041c2c030b414040011a03401400c1c0c03240703500c044c0d40390070300b9106001d20094010b2407980b10a60601c0300000b04107a07500103400c40090907100b90b0580d2500d480e91410890180a00c0d0070f1003001550610001b0011034903a0030444100d40040d200308903446c1c0355006213040c0220180e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 12004260 1250 12003010 12003073
    0x5030a061b03110304170c0312010305120a08190f061202042703030509010605040c0e03060f010501020d23030106051201050a03020618011404060306060306091109060c 74
    0x240300c40d9100ca4140c1d1011402145000c00900c15050601d40c400c1c000a417001c0c200c050501760f00c3c0301504c040803c071800a00e007001240d440e030034618200500c9e404240011581800784c91404401800d4050030f9071407030304080c0c075000001d9559050032000900c0c81a2030715a81500c40501c054950a544142000b0700316004030104840b81034018802690b030300c4d07148030482001d449040c0141c03605207281c040545a043c034000c01c107916064100c5014044c1034001c9a481403400c0b09903010242c0241c40802343e404103030107858140c7d445515204485109100d41c5016030010780c41c00342004e2242003221284514861418119021240e1b84021608260054004220000b070780c243e00500148280c1d0040c00b00729501c01c019401c642c00b00e16640100b8050355480d40c10210791304042ea006864844100024800703243d141d607a02c1500601410b801d200f0000400e00c2c5c080003140417010b42c080e0480c041d00c100790003071800b6030410a000741d590000b8984046801140b00c42c4411070741144400e2006404000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 12005510 1250 12004260 12004271
    0x6011e0302090a051c020616080307050403030e0d03080118020d151701020c0c040203040503120f061009080303011203050c0102031003060e030a1d0303040504050a0204080d050708030c0d0605030a06 87
    0x20207100c0f00303060540006105582059140d440340c07241d201d03542c180f40d82c1070380c0302c0d0b440389a1251034000c001ca224170010511700c404010003501540c00405041240d0180e90b512019044c603105205002200000c080d002400c10310043c07000214219005503d03180400005140c0340d13448070706100b02c40d0049804c03003680e14200401c0205030b45146000c1801420040214900700c102c00301c080d61545254800c034040c540100000b4140003090040d0f6154011210900c511450440c0b01080c0034481103071101d10801c030101000b4150761042c1304072015130b400c28000f14516420122400d07405001c10f00110300f00001045081400071080c006140511072a0300c02c411182d003540740840540307040095801c5503900030f12912002e26848440c910b2003094001075540700c0505140480d04510482d0445600305007083c05015403020541d005004030b03070079241a180c2145044008035500d110712000902149030038000314040f0640711004103000e4007500d100184041e03982c1c0c0440d0402c018035100360307941503861 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 12006760 1250 12005510 12005527
    0x20102060106020615040504020d02100215090106120f05010209190503100209030c040b03030c0304170c0f0108070305071b0302060405070e010b070602070606050603040b0709080c0906010806011e0302 88
    0x1045600e002d80071900250480746402d25450300c0170420324400602c1103403202d011a0a54440102c041c41a035006403100840310b2151070040c0d80c0c3d00c6050703480e500c403181e4040000c110b0941031080e10280c49060200040e082d106441d4264030781400c4005960f2950700304101510759075000342c032408400c0d180111850306407a1604050a18241c0308000e0b4460b80100880c02e203039030340814007442d10081218001414110310000ca8554060b1003614800c5100004d0003003094800f00064142c1c000c0110201d8003400301020a000524408040e030501103416140421401030180d00125400040c81c608103881a8040c80290400c00c54108143c0145c3c0080d0107000c2446414464840602603c201d41ca4441d454011070552030300c03400002a2140d5804140d03c0108159500504020700c00180003a0b10303414141018110007005071034040100d0341180001840c07000c0840c4c00d10720103a00a04503103c40d90781c03c3c019a402d01c0c000700b11504015000528030281400241e52541a64499034010b0b254040c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 12008010 1250 12006760 12006763
    0x2040909050d0e1e060a0c060c050c0f010209062703060114030c010804050705040e01020903010615020607090b070b220303020a030b060c06042619030f02070f030e0f1804020102 78
    0x900719800e0240c00b42e50110801e20006403001300403442d040d80d1080e5500c800d21000c45406000141c0103021a0030719484c4940c0551150141c00c000c44180255100c04035250a1300e4200c6c40f6541300f50360480028450444070181c50180100c003d104100382c06040c02d4500300080c148903090b000900a4000c0e404420002d060800500c00064402e0030910400d050030303111245d5072416441a075110303a880301d0b40104490400c2d01904c3c2102000390081c0201d03515600343c442d140c5582c1409000600c14100054242482042000c003182c0141c1d03d020b20f418002e031100841e01c0d400603d2030601c252056007442c40146c400082680d0140643d030700507202c903480b000040540d03040fa5a03607441040240310103c000380c00822219027255200411a2201441c0e031803008454a071000300900d84040030691a0101d160684000c0e0a201e05036402c0010a440141c00c07406c82c055417a018140142c011040b00000b1b000300c0c00c40d03003171901c000e02c282603542c03506001900003070380910000c080c42408024030085580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 12009260 1250 12008010 12008027
    0x10c0201050f0301300203070510090503070e0702010c0206101206060b07030809011109060d1508160303121a0d0302070506070501021206010201140a2d05100902040602030904050a02040909050d 85
    0x40d600e800e68582181b50006941c1b0310303c60040c28400c2d2403120450744264000c1401d17200500001d010703a070407640e5907008040c03200030403074200000d5400c141042c0e01c040c0c0701280e1181308650100d80d9020050070080b00580c034000340340c000ca07001e5a03546408a1342e035004201500140748203a0350320301946010103166080d21325001c2e0381c200500c000c0c060001c0da50344400c01c2d00e11864000f400055508412142c3e201e05c2e400c0d50b03000d0100c6000c1c0d40512060300e2038420340074043c1d80c02030b19510404521442e00004813008110300340c1184210300d01e41c011501d0200019400d4500074411211010b440f04005003140e48010170450fa90380d40046c00700d0b1007440c0025141e44c001c0007400200440d08204140d620644070003030812558580d1034a40088045900d0400c1c8038203010840d0303072141e40b81000144001404140c078020098284080b000410314010300840e02a14281c0e4090350a210000e0305100203480040c00c240742c43c68007404082525101d0f03110f614942c40c001e00052810809400002d4440d15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 12010510 1250 12009260 12009329
    0x9032109010605030102030c0403081804020a05130501021609150504060602010b120105010506040b0304080d050408070308100510030f0603050a0302030a200304030f050a0203010509010b0f0d0b0105010c0201050f0301 95
    0x9005208100f94079100c081650112b0b500110100d5448034030000300305071080c0617400c1d2a486071011400c0021903600c20003402010804030444482d00780c40d8001640d85000701080071003c040000014001400103420541c1e2031760809020b011341c00d460700005019030b407185d000400140e5681c40145800d103440320083c400b003403411000b0041541010f020482900c114060301d4060f40e0300001003070030400440304880d052083c5c00310800840c10700f89084001907011400580001d442040454002503125042c141150303001454a062030780c4a02d41a40680303002422072149a81e00e03500040455000d00070717a41d1141c4250f0141d6540c0b0700c0000064280d544c030000c001d10301d200121030301400200005c1104c0940b5040484030000d440305103403280c40d000c12310324001d402d5400c0c00107200c2d524205420800c0d03842403c440d6103602d044810140714000c072230b2100c00341009184400401141d4001c803412800180180361040c5003030029081c1e0417841d442070780007080c2030401c0c0c01e08203450b1606103048400f00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 12011760 1250 12010510 12010513
    0x906051204060b030709050a02030417160201030f0618090308071103040303080c07080705070303030b030a0302071505090a170607031b080604150603020405040b030c01020d080903210901060503 85
    0x103900a0240002900042004007050759070b801807041640e04012150082040300c4050249143c560031000107900240d40c01c50304d11002d040c2400b040e880302000d891302407100c03100c01c0d510340f542500110041c0044404880c43c0d16a1005c0228164060313101d198500c00e4400d0001c515282c00740380081100e40024051005c10440400803503d0036000301c12101225014503140301d0301d44403c3ca400b289c51080c40d00040c0005000500c00301086804141c00c011a4082d03142045140d40a1040c19158034034148010016007204c0c41c240300041407002d4454450669141160070a060540030415285041d001340720701c1250407440700d04440c001c02006a0002541c1380500500480707289000c03884508107640001d1103112800a017140d180e0fa80405182456003002c82812039a80c078002c0c0080d0301c140142070007a400d080700e0b02070b541000588100e1000d0f06a0041076482c02c080b50440e04940b01074a880501d00082000351501c40d54200314030140b81c901e901410340790030042255401c4940c1603014900a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 12013010 1250 12011760 12011767
    0x203061801030213020d0b060703030b04110421211107050604180c030e010204090603020321030105060315040504031e0c03050a030902040603050a080a11030408060606070f05010e0607090605 84
    0x1138a4200c1c00d41045031841e00c0c05a2940040503038040a0244184401c0c2c004001051203c18140d00d6040030074018410740301002901204103101c001c0e88154010085a0a00c1001c0b1404140d0064100d40c00c0324001d6241d44460f207e0303120846401e25a1500748400628a16809844424240f007524001e00c000c80e8400d00e07003403510703251041500d14110901da4443e40e07201c840060500039008a9605512000210354803034a83c0c10707030070040c06240801d9001e48181c15280c0079003900d50184050080c4034106203821a8078020410401e540014400158400940100c22154583e401828059803094881003007013030803290702b2040d900c100c880f00f004025101100c50b001c41d40040444000c0111483d010420101900105018012507400100184a0720208405104411000d801c82c08080d6440700044c2d214907260030b5485c0154000d15001e9000000400d1492606400a00e01540720318030318034014000d40c46207400c4808080c0215801d4101c0404c0041c3c5e180d0220b1701e44003505150070400e08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 12014260 1250 12013010 12013013
    0x30308010e010b09180603010e0604121b020a0b07030c0c090609050702030a1e05040302030a11120d080a0504020409020405070801090506060703080f0702010e0607020a05070f03020603062404030303020306180103 93
    0x52480f680b690317540f107205000e070110f590740c0c8080d0049a6040e0160045481c00d06103450030310081210490000c001a600d0202c4240820a4241c0040300f983c0082483c1d1015043c101c4020701e580c0702c2c1e0710032070a001400f0381100026440180b060006c02c101e10700000d81a20704482d40e0203070b0383c0041522046410400c60712600540050070700c100c211081a40d00609500240e0607aa10b10840d0000f07503140c85100e81150400805903004546510b05a4140f1404101070303000f10b54074404180c80074041040000010740041003584403942c8076000500c04529000c040d0082022a0b50130b0758500001120035005002c0641c01c0d000719504000c040e600c0f80d2030040907450003808a40080d2052580740d41c00c4c40800d090a100b5044070204c82041c00c10380f8018200303000c0c00303562200351300c0048545010300d600000d01c600780d80d941c0804990300500102e1540c0c1c5e40c4020400c45d9030920102c0148004019070104035564040d0140018604c29100140d681c1448010016000c0c41002d030b201c5034050f183c00500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 12015510 1250 12014260 12014269
    0x10b01080601030b0913020402090301021b071a03070305070c02060706020306010e15070204020d0e0601150e041407030902010c050304140108090a02010c0f030923010305090d0e0105091801030308010e010b09 91
    0x86e400003110005d411154110700c0068041c2c410300000759455800820391a8589030004952424240e0b40e10480e82d501c3d54662141d0f030b0400c02d600c042c0a2038034080c80010255801303600b0560f03001e030305450840c001e44403036800a42550040e9005840d03031075011040040550300450b103000303500f03021528425404038425510407148035230700c0b009010b40c0d0045400c01c0031a0564012035200c040303410a41e0f215685620500c941d00c514a44c8800000c1d98040740d07504642024410003064918540f0710301c0c00340d540c00f1010350240881ca10124100700034019150081002400035201816201034070412011182d00014944200501000110313041101e034000140c2c0c00810b18108594058401c4180f50b086040c269084610303540118128003107040100119441214440e2034560262410401038036007405d1240d030340174808880404a0190304449010303602940207001c82d0440200100305400840740e4044040341d00703900460106202200501c90100b005c6110f40c050000c0c0018207007003208103400907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 12016760 1250 12015510 12015529
    0x14040308010e0a060503031902030f0c0f06010b0a090603110d140106020d03020c030702011b0602030106030b0907050304050601050f060f0c010207120507050303060105161a040b060a0302010e04020a0905030f010b01080601030b 99
    0x24802144505000308c14500034000e0325610000c1e010003d455400200040c0d865a00004040702c1074082c01c1c1c0040781c100114410f6070740701358180c0e0b90302400c5820408240c00604114207200c6500303070300b800564051580c5000b040090301d000d207400300d10365140c05e1021303281103204420389052600602010340d5014001043d80c0360290246480c0105d0103020081300041085064090031103070002002003045074047d0081070001d0010390301000c15036a03e4800715840d0006031001010358000302d004001c0c918291a000a0300007006010314504002d01c46180800d0b403180c5102c84140c0d4010034000107204d07040f0180c1998540f1403c1041c90310307416944564503840003c2a081c1800404180c0c20303010b214000f410b00380742c2c1d0b004d100e1642098902c40180b483e100d080781c044035000b007008001145402e0082d99401141d40c1070716400700d400d0040c0704110103500a500c040c400c02a0401c0e0004003917804201d15030406281100018070108000001070210030002c202c1c1d0305050501402040f0f0746c0360820f92 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 12018010 1250 12016760 12016777
    0x3030c0605060a05031009030f0c02030a030e030c040e06060a050a060915030b150d0605120304030605040519080c0d030203060109090b030703061104090f090f021314040308010e0a06050303 83
    0x901c0b0381d200d0000409803c490b400480d05031049400007180008103902c5000c071140241c86000200e02158003c84d0b0300038040b00c00940541048482000080c0561281c0c0402c0e074004099449031030510000c2802c0390301002914001f94440001d00110381030107000100902010744001600c1ca0407c04080c1c440c1509100e5040781c0082e1909003003800d8030a0f032220202450040c0741d40301040702c10042c280725810003891039811610300040000c0502c0d00031003260980a680e8042d50802d450350322640020300c0010402e450305d0150040c06c000c0130000e10b07100d4851a00c145903144d2a00c115074811440c00311302c0b24518003410f02c1007081c0481d0740e8101d1081811248402d10100c0c030a1200004241804c15540c4001c007030500300509242180b00c0b000242c4240d130b0070004100700042400c030100c410740d12040d4014003420b1520000c580941000e805c0b50940260444000c40e04400c884030501111508807800c0d400500058010300c0605192450140c00c01500c0805104bc0c80c1480002030f102e10900c0c51 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 12019260 1250 12018010 12018023
    0xf01080903070209010b0306041a0108061e060a0c0b0c030f010e0408220501020f0a020d0602030405120408010207020406060201051612180c0509010e04080f030c09031c02011503030c 80
    0x355454a040040701d1031a9405003004c0d5031943e641c01000410303001520340d64444c0d414854070383c03a0202115021001444140d480744a030f5141c0304103004c40940c4002c600321808020003c900015220000140000d080d195030b9441c014089040a500a1002078410150b10781c082003808121210b03040d6640c195091584990303420749880c03404030564415040080c2d0040d03041e00d0104508501261400115203003a003e4401030391172003540f1615100c110300025803080b0032881050101d071a0b0b034083c0d07500620460480d5061903020b004a8501c2e086584440c116070340004410045080c140184002040c1c680020b001d10b0800d07960009201d03180080000800c914882c00000d00003507038001c10601a1007107542c000c8030029040c0015104501d0103500d00900015000003038219403848010320440e000030341c460a04400021850099102400a00e0740c480c0900040391503030b6052001140641102c404d40b00d10041107807010742075400343d200140d0030a114143c02c1000c40e4101b24207680c4140c1c003a6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 12020510 1250 12019260 12019277
    0x10302060901110d020105070e0301090b0f0619090506180c030612101d120a02030a05070203010b0411030402040605030c0d0204021e040b03010303090e010b0d09050a02090c070c0803090f01 83
    0x80100c074802c80c1e41640544a2180c00b8042514031780650001d4000c914070740c1c0700d402410f034900070b25098614000d4024005900080020760038041d0070702994100c3c400a0100e1484150f0070f0030041910710b40e030070803c001c603a02c00c24002245072038050781101c2818bd02240f02c25207003403070150300030340401450343c5d00500c2009586440c0400a10030018403a510303200420201c203010810b915030208464900520b440b40c0800c00c1240140602a144d049042c2d900075460110486000c0b6415004068120f81664803102c003641d980e9914000c10003800c040111240d101e24080c010002078a18503400503000b5040307c80700e00101d03103650100f040d9064042d540035030b4811510014050b418107039800e02c40b12007000300e80800c07c0192240114100c030702940c5c40c3c03020307a81c443c02010000306007031140b4035904008000d8403010005c25001000d0860003034003a90340580300c607004501d40a00c00c5480c42504600003598208124001c0c0f480409041510000c50401c0405804204140e40d000c503003606000c07041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 12021760 1250 12020510 12020527
    0x10614040612061809020102010f0612080d0618092312071506060e2404181e02040807060203031b07020604031a2e090509030904110403030206011205030301030206 72
    0x30b4103e08001c154075411882418100c0c03000800902911008030700650910200d02d404885031700400040d5080381d0741b401419061580c1c0c444c8070b944070845161405485032400280d14900390059100f00f05020000700e5010344a14110b1420440900e00300340c203070031030b8100c0e10a2600c00281c11840e24010703408036699075042d0800c5c6100d00202c10190481b941014401b00b060780c0e10005940702d000702070b00c5241000415064040205065400024982c60184010810b0a80c0c8980d0428941d88900d0000352a03031401c0960600700160000040600d07800050070003520344200200c500400c883d00c00b450444c24007070012460107400080024003d0303004240c00081d907407410200c03002150f01107840d4004480e6400104000c800c200c442c1c840010b040242120714a1504244030100c64607101e400348002e041108803002410f01400002052100f0311620885440e0303032042c1171080c04071841c4140c41c2c40c074524000b482c0038016007011030748000802681d40010000400c0e241500d0f4102d134525200e4512 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 12023010 1250 12021760 12021797
    0x111e040f090c0312090f03080a0e0402090316060f02010e06060d02030309090f0a0c030212040b07020705060703080405060c0c030403150b0a030f03020105150303040303080907030f0510050106140406 87
    0x1040e400ba042011002d0000204030306001c640c04001d61a0329500c0a581c1c1d10444080a0942c40c4806448041e041290343c4104e0b200c1c1000c00e207503440c02080141040c4055000c40e1034500300350868041707003008030b2003071008540125980040e529184004d10a9501424010303444003009040c207402801000154000c550f41030003603414241018003030070300b1440d02240c1c0c0a00a0415902011007614210081066074802e0080700c030a0101c0c00c00d05440c5850355a6000d00000d8010414800c6014840011840f41d462034018000d0a001707035a0b800f80c80c00c040c10118104840a4032445045504108010030050080256000c0741e41181c0300340c0d0100003105101e0042d184400031517510502e030060200c00c021203900c90f881254001d5000b004942d030340003084480c04030b00c2042641d141d03106000c2000000c0c810280c5075409a080d90030b031401690b032030352004004040d07000103e600350450031505181b1110743c41002c1c0144102e18100c800200f14502000080c8154010002002041d20030100d81019 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 12024260 1250 12023010 12023021
    0x117090c06030c19080103150207020a0302120a061112090a0203070e04030201020904060603020c0c0a0303091202040e010c0801051c030504060503150d0302030a0e060405090112021801090603111e040f 88
    0x40507412420000744e4410300920101d001d001c02c5030118101600c102d1290000e1081d00c40140e8007405805145066408010660b04004902e013054400e8048103400105071f0300a01011210310b556141d200c5442c0e12050b0504500240078490540c084c6000c100543d0700010b4041c101c0d031082d19800c840d600c03142000ca003e817048000c61500182172040c0083c040754194000d081d217010b00002d50340a00d42490410000b0802440043e00207000800240240060b2245a0780000e10042001807619001e494042c06d48494013181004030b081c00004000605005025000008100c54200041c102c90b44d400340c4980258014001040720100001d04482c07003102209ca0446c000a01545000e40c1c0c51500135601c1c0d0007221b900002400c00750a10409041c030401356025070300001c00b101610703170070310500d401400400e90382684e000c0b0755040200c403055a26104a40a064002c80103e901d60035420a070300784402e1110711078010003010000c00380b540711400c6500580ca0003203901081240501003c0302c050311 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 12025510 1250 12024260 12024277
    0x903031602010908060709030303050a020307020d1404120803040b01170a0609020109180608010e0a030e0d02030a0f06050108062d0702100608010605040f021314130513020117090c06030c 82
    0x3c45c50085c484085e8009908208492099030103201d05c1d41d4045007041039020541d08100542d009840c03080d4000d0040610b40c0d0850036025540d42407a5503400343e0141500300b0319045d9404640002400203001c0742a0a0301d01504200d8886074086e0395a4001d16070756030aa800c080c110a070f03620420021680300310b901c200106001500000d544101e1a880002000e2030310a002d60380d8a400c1d420b440010300071400d4041d554164079003a112900580170b008654090301c02c100e0f410b0290003020400510540340186041e402042c0000326507040800c202d14200c4041e185c4051101d03086210b00034014000c0d180400702110040482c002d0f1100e034416850301ca50720421718032850600c00301048003e815030042003118000c031418428101080302c0c00c012131089071002844c1602421040c068000d03101c052030381c2c01102405006c40110b121003600304507036040d9542c0e022500c1d030300841c106560b4042002d41840032058004d0340b003400c00003107081d6a40c146070329541c0284000700019401011074015541c022 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 12026760 1250 12025510 12025513
    0x90402090a060201050a0e121608090a0b0703120203040f150905030c030d0b062a0703020a060807030c0819090611030906091905101812020304060909020903031602010908 75
    0x1502e501c0b001c1d000c0c1c00100c0b4030300f00c0989071895681c29900002000c04041100c2a000b84c130741460203003100c440030100c0c14180d03082c2c00b080007081c0319600c400416100a05a1900c802e4880d10b16140c020550104415a0108240184180000300c0d45640707815046c0d6901407824078010300c1e603042c2680a00001c2074090014040411000c41e0ba901c00300040400091030355003041040d41c00380800815005061030f911356100070240c04c00041107034468201c032000a0310115403607181e6079070001c0d0001380180c200100244c030881c1807290320398242c007861000041c1c0c1d0800107580d2402042580e1120700d801000801035854a240f502881000e074401c804c0704412016581d541e20b4079000300d540d104001c0d617003d5450306c40c503403051003030344040c44010078440d074404013a00c0355482c0901c4a201502000825060b00d101d03003842e090001c2e40590030600c042c5080d8014607250b900d4000050b00340d40c01c81c1e101104460040041604540c0e010080b40c01112a00340000080051400100c4000d02c0caa000546036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 12028010 1250 12026760 12026779
    0x60103060f0b01050c06070309020315041a01050102010c0c020609010c0b010305060708010503060702060609040819091505070206032e0e01051906020a021002010e1e0d020109050304030809040209 86
    0x140140d0750044034100308103900910680b118900110303424803030210150010380040d03010601091180d001088200d00040480d00340c4212203100c2142d8160030b8400702c80c041c90120500d141013000d030311401d006102c00d000030440114130403005002c000407018024403440c40000c00300c410303030300601002d030020703801c0030034004690303120b162a9a0f0b0368070941d800300106401c0b90000842e4a000034009126003490f6014109903250340c42403011440025004850309002408032003111000ba0889903091019580c4441e0183d20f042800b0600280740081441001820090703500561501412a80c0124022409c4001c54800c0c0070f00001d402101100350400b15402140003a04900d480c1c2018184c501c01ca40310f006102c0007180c40d41d40e61b5120310496004d600441a0240503150840b0300c0c0e0390ba0006800041410b441181015052000512000244c40c4000e020b200300d5803000c22003a00f0310380b00390000b040000140d8851039960300580c070006001090004203c030858659030181c45041c200a4540307250f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 12029260 1250 12028010 12028013
    0xb0a0c080106080c070b1918020405010e0606070807030e0d0302010506120303070c0312021306090608010501030603020a14030c04020a110f06010305061303030f020d0605130507091a07021206071404080304120311060103 96
    0x1040d000c0c1c4d15089c0e12807403c010021071510310303042c040350007075070002c100600e0a0b205580390b00654220390313030640c1841a020031518003600c841c01080c8126209900008040c070b00702003004040354503e4000101c551082c8108440d00d5000050f100e0400d405050000348481d00c030740316101a2003100b1001080b102407600c00142e07540c01c43c80c4082075405548444a45c2c0c0e803142c0044003152214840a544500000001c000079607490006940313402002e01035480030b010f644c021400740d901040d4100700003098443c600240000521002c6c9410342004040c094651541c0c64403950740c00040d10000c082d00d8804000410503010350300110b00416684000d54551000301426402410f00703206881c020841c040460440c01c4c3c4500ca00c52007035800c0c0d112140d00c1ea04100c40ca90404c0040ca1b02c0301c100120820511000d0307560000c0ca01c0c6078481202c01004a8641294010308461111001c0b186090003800203100948010054038191a03181880040442050070f040f1070003a1281003160160155000100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 12030510 1250 12029260 12029291
    0x31718060403061d0105070207120303090f0b010503010c020a02030706180905010f05040506030d0f0e0103020405090f1605040f05010f05040902160309050604080a060906090b0a0c080106080c070b19 87
    0x300040010110404084d1002038090a89000f2a04200103070001001401848040c161401c0b0303040c0a4680024400d401e580c450000b1226003400f0754098110b880104103503c1d0900400143c003840344060603400c0c04960110340d542c856400b5500621203d91a00c180e2492103241000042c00a000c0a102c0c95940c3c984044446246000c4c440c0101d0801e0001355980c1000a1301a4840d2126905c10410049212088443ca02c03500420f904158003000300003040d50b02c9901560140c14204d51440705410107081000c00039030a601d0340414000d00340000c10088440c08828000ca481c28207100c1c81d4044080401c48091056405c164482c4d40f011a03c040d990007010340003401580701c1c1d29003107020707a2220204000c500036449400016802600c07941c002601680001d00441d110303840129000c4182ea407411000c040131a15851070555910301d480c1426840000d95004280ca800c104055040c409098045031041203400340a165402c3c0204020107144c10000c0915000c3c12020070514448035100c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 12031760 1250 12030510 12030521
    0xa051e18010804080a08090708100203090d0c02091b0f070f030906030204080309010e04150806040b100e0105120a0c1205060a0203060d140102040801020f0408010c0903171806040306 80
    0x10141400000004040355000e074000c18042d03900b100300c8904000101808940c0d401000f080030b90385000d07014000840403c10030541c030b00c04078080b0340503850703140440300d070f034900740e0f4100340801004008200d150240e01c95505680d00889a48548160760711f41003881d81c15442600c40e030034440741c4000740e0503051013604000012058401d984030320b035469542030210700b03038005d50050705615003003081410241e40c02140440e000d104050000718001480110314000c075907040d80180780680002e010001080030310141c003507024039400040720b130183c00c0690343c0c960810140103890040c3d00000301c2036110030080000740c0815a104a440140b40d8865008068400c1c081000f21800e204200c081001445903009036031203201d019044081014050700c41d0038518076940850000d65600300070201e24040d00b8001403003c01c0150b85d003590b4552401c08003900b110807030340e00c241c20400c0c121418000034019240101a050481c2c2d04d103904c80e01d52440281c44c401c03012800c2a44844001400410010b01d034008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 12033010 1250 12031760 12031777
    0x209010206090109050706180801060b130602010c090303050a200c042306280609180504030f0302031005030604050606030f1b060703170a090501060504090b0c0a051e 73
    0x240c4141c0d03100e00303030410300382c540e044001402d0303401200c01848064400d0b503800c0d846c0c0350361100080150b40e545802c03d08480361904041030b1358000141980a0001e0381c2500b00c028442403000704400d000014000b09000d11f9400001c040110002e4030342c103080e12803002a61000c2240c6680e15403607245000c0d4503502d00801e41d41070702490400d4003800e042240107020b0a0030304100041074030b842c6d0b569010040746140f01401a00d00300c032440d52801044081d018200b003e00515192014018104401c104508801518407060203007001c0c10000000e40c4500c00c040d00100a00340513803a40c030358140901d5450815000381e90980302e03500400007071040c0045c10314040d40d0140c00340c44224007814001c51f140c4041300c06e081e041c07247c1c1d031280d1200c03401d1039001004850301900c3c00142501c110244a044800282d86da0001940c0304c010350401d005082c0b08280040c102164100842070890780c0324020442c00070941e421040d4007240b9050640c0c02a030448440f0341182d10b019a5010484017000c1940d00400c06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 12034260 1250 12033010 12033013
    0x19020d0e07090204050a030210020109080711030613080d09020103110a02010203040c170d0f0512010b0d0c0504080d0c0c05090f0109060608040206090d05070b0c0a060506030304061e2102090102 85
    0x103030803441e601c03c0310117580b03016009018090441d02800b02c0010101002d00442d9601c12010011821540140810700d220b41d14a0a2004003d070401d40f501d10702400c0302d00d40d2050749000d400054046011600d480180080215600d00c2c0703400160010105d0102c0302036824070002da1848887d5040d4025480390b48100d041180854980c7d148070130351109200300602c0c60b4051864100140e010b00f0207144e50100d54580f5610b840c19514450f2a051401c1e404099132000c0400e940b08040c1042c041d0f442c0c40f4401d450918201450090072960310300803040c14505000170800c02030306200710080d0381e2000d44809013aa90440c01c1031508281803560034800d24100619000d00464207a10074030300103000da0740040046082c0b40d601d0080223648001000203c5142c403441100151842c1813101401c03181c031500340580920351480c00c00d40705641c0000c203154403d400420040c4111a04103c26441e1f0543c00c400801c04800c81e407205503290007008113400c020354215915204d10400f107400900c50a2030030390 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 12035510 1250 12034260 12034273
    0x803130906050108011a0c070609030b13031d010507050111040302190b0706050a090b04050105060109060e03060f09030f0c0106031202010506090a02030907030b040501050f0105010503010303090e19020d0e 90
    0x10304500031035016014041c00620f8070350040104c00048801c0450000d034046000345003c039031002d01860701c0d040340d120202040d07606000f0410310241090311540300c9003014010030307090b006503001085011a98811200440d003050168810392141c0140d03898268850001c001c0303c1c1c140300c03000c2072540241c0300c200e210754204040300c0d1545003038801000460314020801420520180e071a40301400d4010941b8000642e0b60754032502081c0307051170b079501550140000080ca8100b110004000842e91707000801441034000030745100d902d00092407a0b0141d40c045e82d143c00303621109001411481a000c0d408411500171a06a07207500065001c01c045030b100d46203183d4a2902c108050f8243e130f904442c116803144103440000d641803210b80040d64031180b214181d40c03509450750f40b4030f100000280d0b8140d400740c1d5175104000020114511707a6000d070009007040e5045615543d8010a401d40d18040e21401100c22030105250f200c029058003030f14a5021002d5440382c2280c001500101401c030965041d610511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 12036760 1250 12035510 12035519
    0x3090501021317120a08190203040b18010608060a11130602030c0d03110304060c0905030706080105040513050d0507030201090c090e0106090e070509060609090f0420010e0d02030a0c080313 83
    0x90382c183d00c0441018450405c504098152102d400c01040e58040542001d5181c41061991004600ca81c0c803c40141c4880e051882d1041c2c9070480a5480201c26890610184208100000c0d0760f40d012031a01004a0001e01d014540030103030040030484080344162400100c0e0f000e40200c00b030b060323010b0342800310744030f03041c400d00c048003541c10b50300c1c0350704541c0f038200049008900036400482c0d0303c0210303080c1070002e0360340e510120746814420b51050380018090310042c4102d02d000c0c022550008921040e1001500300c64035295202c0000440c10420301c200042c4140804d03000f90401c400c89500030f2740600c20383da079660042c0b0140c06002c407158420f520300007002c60303554403e11502d05a40010b0000341005400e1800703000e0103110243c1401e9010409101801d960780c0e80d50b0b5410320510364500c0249042c281450a244ca8804545e4a042180d070843c808585990f0300520b42e090841040381d00860046039400445e0400030040f0028202c81102000031590340f00000c01044020f0350703208258420b642c0c3d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 12038010 1250 12036760 12036763
    0x6070215070503070c12030e030f22030201090605030411091303030f0507121a120703030f090302092206090503040512030405060316020f07090b0907030504020f060a03090501021317 80
    0x121340090100301803034080310100d1100080451012550b0500050400c050a5028031b55003000d900d16a82c40c41c0025511200d18040060002c0000c0e6103100b40402400e513400681040068025441000004800541840605400720310703001390191000000e4280407201280200d2a16001c1d808a400e0021114132180c035849810b200b1402e0b81d94040c040007101030750402410001c00c0c405030b40c5540384002c2d1440d0751207450090502c45070400038480c2c140340d40b9000c0d005511440c80d02e414004c22100800142c0c03540c4994692082d006800d04003920181c40d4900050440b042d000b03400c0070301d8a0f402c007081050002c003e006680c42182c200103000040c21070b80d9034a2240b8003405800c1201030004c9100310420446101d201c80f001c1c0103541a0040c7c1000c49440c0000d04c1e072140c11090b44a0606401c11b04040d2240d43d003080244c40e060103180340c1a004141548104c0c55100c0c0100c500284000c41c49120350702017062507512030001d560b1030b9034041c2d11141c0d00d0340703501800c40107581c91490310511240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 12039260 1250 12038010 12038017
    0x3030b0303090a090e03071e031106011a07060204030f1b09110708090f100c030806010809030913060906090603020f0303070506010608100b03040b15030d09050f040b03060702150705 80
    0x4010203d800385814040c10340040c0000842085103440140007080015484040e2408090b03030344401101010b500c3d080080803100a18220302040d00014010700c4451a0110340f500302c1c06290104070383d100020b01c0d08800078440c0e6400030f4801195400564104156900c06c0495030040028400003161100c074540122210210056015007003040007000003440280501302c2420003c010100150f80d01001c00c03008500b0540e8080001c8010107000205074000e200182c01007020b00e442032842c50006406a545d100300000700b4400c502c600011044005e45401441c050b02244509100d0340707a03103c5a503000f80070280012480380c4051a03251815081c008203984001d030b08240200001d0746000c105032191030b0003034490f941c13100c440c0101080d0018180001c50203a0b02c100b603115114980600e1208000e0004d840f87c40c8603801400f041002c40358041880000d484080308d070f22259019600005c0c0080c42008801505070158800300107007036801213100014601c03000401c640d08c2e640c040e030450b268071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 12040510 1250 12039260 12039277
    0x1206110301061b15021603030606030b09010603050414010f0207020901080c060702060f07060516030c0905030714010201090203070603050610031e090305070501060f080c01020102040b12040203030d020a03060303030b0303 97
    0x10b4404030030044104440b2903902505008060071300e00c3c0402458802c050b603114101c14070724200305c0b014440425506208000081103145800c018205003540000d0100b4018071520301010345650105082c8290390903030070602915007000b08604004081d4050281d004181c060341b0400c0a00000240800302148107040c01c0d80081005107031503072031b030300300030315070b08201052107219009112210014000e031040c54000c20b611100c85c3d850020910008081e01e20720941c00c81045090041004180c0740000c6450650385600c039050020300d00000100d00604540501a506100d01c81c1c000640e181c1580c01507002f5042038914002d02400c602c015415190000005c5a5072079032064100000d01059000304461442071070090718151042c5c59003425140c080c0c10008c03428038503d40401c4601003c1000030b0040c5c0d0300b0300007942094505060844d550082200c3c0100d0141c465000030119581030007128032115065204540703c44884030010b005288a000407000301e0b14140c0d907540d031403800000b655540c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 12041760 1250 12040510 12040517
    0x20606030307080a020f0a080403060c050a02060c0309010b031f050c07110108100306020c150105040b01021b010903050307030e0f010518010f030e0109080d0b040204030506040b10090501120611030106 88
    0x61469070f4824081c0e1140341243d085006407404810400018411090000e00030070b401a280c40c21800c200044501190304142400400c0007080b150301e8020403120751019510801640765554418030a01400c0000219030b49800381091240c0c081031201800104c02c0000b00c01080f031952a4030b544d1600f440741500150003111040c090841c0d80d03201e00003081c0d01c00c4e03180084850745592542ca550036038114100c01070703840e00004000d44c00101e1400f401c5006220440d0240907014030080082e4684c0a00303031400500d41c0800700201241e90003130400300700071580181241d0703640415050050180032015245e520412071940744612641c414015141c05000005038145d8031300c02d86006442d4201c4658250061545840d102040e5542c203105030710280d0700584d11075543c1c00d07484c80e1900440b03202511f10352185105200507c0880c4c00015900e82c40782e0300425201842d220110524400612640142c1c821070405d4004180d5078001640c1640c0c0501c030b244144506210320440c108980000d02810001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 12043010 1250 12041760 12041767
    0x106020c01050d091a04080703141314040b090705030403020105011410030c03110d0b04060509010e0412020c04050709030506160e04020f0702090103050601031b1511010e15160206060303 82
    0x295440c503030207400780c548a05c600d60b810034403444840d060090100c90566151202003074804c1419000584241c501d0010300714030b440c01891015130344141c0d03298010303094448001d000c1b880d429103c1c0c5d4000c1615890041005d0194a091400106a42e008031001c40041d42007400004184035405c601448140c8014010602d5281e02142180141001c90265080540300c15007800302d041820014000303e04051404500040581c0501003a2078040d484a4000d000343d80041018141000000750801d5000007060030095125400300c0c0f034400d00076041c03a8050714003024492880e4011107048200c0c1e120700142c0b0590350b1180f5000d05900c01c0e240c01840450071103001500d441c0b42503401813100790001240349003421004e4010503c0b80a09130422101d981c00a40103105015641080625a076055220b9034a50360410a003040c040c1983e840a10901805c03d4050961400a400000300c0d803041030308854501c071048140025140b0213440d04c5940c08641d0303105582040c408140c46104c4ca4014005514 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 12044260 1250 12043010 12043027
    0x203070c0f02041401030c0603240302010e190e01090605270709030b04060c02060919020108070504050301020706060e0c090102060c0714060703150b1804090204020d11070b0106020c0105 82
    0x140080c1d000012a4001d41c0d44101002d14035507910418040c50107039405108540c01d00e040034084501c100420f02c82c0340600c0c55044011000503c0c1c0c4415a0350a1031f10b160840c2d0502c001c034103081000d5051010380e400f00c0d81c01003001110341d2002c40c100c41d2028000d0282c10b0740d841c1070060b0440030b52084100c0340c645146504000b07803500051034024101d442c0601c50140e8903105c050302031900740c130111016511442c0d200011641084095000040c14014024120007a601c00040012101009052080c3c03003000519a40c000c1d0240e500600c0058000d55644080c2d10b485002012603014442c030342000040400c0148907400140c07101c2c610184c000702841c2c2c0740e0380e0640035a0340009004807994003e001c4031000244c0c0510215003e02c4c440e88010405a8078080c0740650800369810143c5648000d0010101c150b520400c0e410360103e099400142561203800410040c1c81068255848942081410040c500c0c0c10f4004014150013039110709100c0e601c6207030498861403001c542500043c4c00748039101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 12045510 1250 12044260 12044273
    0x4060902040b220c1103070305091f020d140409020a020312070e03190602070f0b07090806040b07050307030b151b010603080f0310080a03080106021605060d0e010e0102030f06030d030203070c 84
    0x10803001c54200501040217025800340381d940121000c0b0b000403804921121941440c0c10145501081948074204000c0b030360400075038641c1100c1149041112040006130303400c201c81c1c11a8040e0014050542d9110094500a566a8046820103992a05080c001001380e03200350780c02c2088010080151941d10803031101228646044403054440715400c20103000090241031019420300c1c410940500e1524124501415444259203d00540c0e0400c508200006601c2514540d02c8012420200d0f01ca0f1201c00e0304030003c0140401c00760300090000404900b5805030b0000c3c0c042ea59501403110000010b60154a00742c88080c0300051800701c0030300082c070618080320051a4080030308010145240e40d62042e4500c1c000c4c1c0104140e01290004005000300d42d4180a41503c4c0e96442a03503050079854440850018407500790302120341c1d070780daa000c80004078080d00f0039034809900c0c6009644030b041c00c3d61403840c0320000365145842841110940b4200a00078003d80303115442a898071841c2001c2c0e0785642 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 12046760 1250 12045510 12045521
    0x110f031801020c06040905040b01080a0302030a0c21050301051c0c05090712020301090203060913200303070c1502010b01020f0d050f09040f090b06030a020a03080708040e04060902040b22 82
    0x641540210300f0400c0e015115000035000900c0d00403400b090a0616080000d44440c060300089001d401078064480865000011510741d9201440c02040310b40e000e0402c804080012860307021640c0c2c102601200203603206e00030b103069884c102c0710a0b00c0c00d1004682c003040c141180d0002031041200600c100158070345261010303030008007410400034040c044020002280e209810030500f07180d001c014490a401c041c0340044e03021310b0b50100f4070306024068035030305041b1750302040503402580300501c2d40715280c85c18000c2c0d981003079204003820540d5231101d1a20f112091a003a65030700544ca000e000c0a115031001405400340a9460060150780490102c1140d103640705107100465040204250203e070b0715248161500f01101a000044e01462485d05c1c501012019002c140300b9032010050002580c0c4e0820404100c030380c85200b560380c0d046580342c844034074002d542c0800c0d1480d8015040000b4842c0b01c0d08504e015510840d000c11102014904100c02a1030060320000c0000c908100301c41c01c0412035004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 12048010 1250 12046760 12046807
    0x103061803022a03150a050117060f04051009200a0605030703020702040902090109090b0105030c0109050103090f0b04030207060201060b040b0415020c060d020417030301051008040309080303040f03110f03 90
    0x80c8443c00d000710200b403811405404003420012100300300310040c1124810b09001d0668000765503940c40b1300c48030b030725911700c006132040d0000b00c0c14101203410082c040104009200b0108002d109000310340c01c02c0741c075600981c50902e103d20b0355003c07182c0c128a40300c0060410303036440751101d5003540c072100b80490003500729240413031300259100e02c040003595070324980d54005c10f40004042060102c1e480c10b200c0d40708040e4001c078002e0f48541107018040c0c0e0043d40039420380307600380b1340000c0c40031071420100c07203c206c40b44003c0e05240c0e200091009041d40070602c030040d540030703030001d01c2010740e00c4800d060301d07108501c00c01508c404240300034003140e84800304040b86a58036104a444111940c030005030036500c031622818201d035000a00704621503803d64000c0e00c1c400b241000e103045600d4180030604401da00082038003048101000181010b015a000c9030245c0041411640c40345060315201181854450054000c218006000b880c210000108030a507a0303080e0001d9824008440b00f600031030034400c0b01c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 12049260 1250 12048010 12048073
    0x1403040306060b03061201090c050f130e0606030d02070302010905010e12070b1e070203060103170c030d0b041a030a081c020d090204060501140403020d060204080d0206010306180302 80
    0x10000100d0307041e005840251071410521640c0707003001c1c0e0400c1501d030907012009003564100111803000c50a0b811120085a0302540d201d0ba0b5040010001441c80d00003c000d9540240f82410030b0800520001c0c0c42d61040c0ca050b021079603003144021003a80c0c0c80e0814031000380015200d5100f0f120315440340d0100582c0181c06000b205085a24421940c14605540c101c804041808a000c0518603448031000741d5402e0707070200c058036155254010035181c220501000c1d02d60649080d8071803003524030900301c0303421201d06001d60792601c159003105400b5240202c4014455401e02c1241c0d807400341d8072071401c0300b1008010000c000718140d50b07550890365000341d40ca49080f810522400c140704070081c0024007120100c1309001840c407090b84100011030312250040f504216025002d01864072140040782d042d26011501094403060619104c07000c0d1040c0c1c1c02031045c50280a02180085070002511030580e071003003034140407041002d01d001c4000e60b01c851010f001a07110162842341889000e140c3c142180605a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 12050366 1106 12049260 12049267
    0x70f0b01060f090b0c07030206030403030204180b030a02010e01020709090c030209070f020a030507020303160b0411031908090d0807030504090e0102040b070206031003060e0c13020a02030301031403 87
    0x900440b035200020340717a5440c2d404024100003075a0041110750350f864240f600a020f90424414540c0c1d0302c2c5481d5805110100d03a014400100202900030a0b0014040c2c00440700300218042c440c0c10b6004800c4041140203c60241c807a0380c50003481d0544049255105000e080e0800805c00c00401c0303030b15409240f89550101c0c10311811609860510745550403400001d055202d807440c2e0350040c0060702c070a08204030008030043d2140e40204058000a1080002d045d207840820103018280400600c9403c001020600546005e0102401d41c100c501e80990340d814007641700000580211b00040b0707040141d194140201c2c500084400000e6090515015219a0300d004038503000b0700c2a100030001030342c50009680840d0045420200c1403000306525425a900c411495410038000c2012181c0c5400c428903600850340783c40000d900031480d50b840c5803201c050391044440c003c00f40b40804c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 11870510 12050366 := by
  have h0 := BRFrame.cov_init 11870510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11870510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 11870510 ≤ n) (h2 : n < 12050366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
