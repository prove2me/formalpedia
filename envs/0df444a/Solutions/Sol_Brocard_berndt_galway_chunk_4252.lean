-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4252
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:58.540427+00:00
-- url     : https://prove2.me/submissions/2c5eab38-b42b-4e91-b14d-4688db30fb64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 764568345 ≤ n < 764748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 764569595 1250 764568345 764568359
    0xd05060a1401031101270f050306090111220b03040623060117090a02030d080f010f14010c0f0503040b1e1213050a0215070b0906060303090f04021b160b0a09 69
    0x420f0342c1c010070710310f000a540c000380c0550001b003442c81d40b100d1280c040b000024461840c00b80100c5420000c4c0e84002e06c803107205c1c042030500500c62a9071585104a00c21006410514130781e92841c02402d900101648a24103410204060001d50303071804100740840401c1940d10403a0a038031405841c0c1a515245c50004894111800c0c0e10082c000868034840e02207034100581e0100400c48500341155221401d134106040a450f45410603004800b50010304601071200c0010b24007807010000003485c04013603040480c00d0903000641c0d5910b0180040c0030020f000709000031001d00a090602e0300c0b01c804030201d10640807122143c002d1647c013001c0d0030003400c042214940842c00311002103005100740e80c0c0c01a1258001b45402c2d810505089013a080071526800340451400d60a5100b240308015020790318000c800640c0340d10626030003520440d50080c61040e20b40719641a01c00360f41e000400c2c01085507800704000c0c3c1c0d80d03c11101051640848060100e0800b40200c191401d90a00f500c1e050020703810004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 764570845 1250 764569595 764569607
    0x60112020f030a060905280305030c13090b0f030307080a0507140d03090c080a0b0106210f0b0411040b090607081c0b0307050a030305120606090d05060a1401031101 72
    0x44141da00c050841110501603030248480c40090b4410500080c0701815864114200305166503140c82d10904680988818811103080b5068181c0c0343c5021640d903910311405048500640d218880c080001d42c00c0841c81200c0e50340209252001181c0c601c1881c0300c04000c141c0c1e40d03c100380005180c039105020808115002d00003400145114036584240d507415011a50320740074a0310100e20002751074180c05001e0140020301200501080400350031407088a45402c40080390611030745081005c1c01e18200658003140c0e07081c0b02105500032003840503d01c1c51480740301900101903403502c11460010300c91000702c42c090031141100e4010100b10300782250341c020000c480d08050004d03150002c1c108244400f0f801042805258003484070f0002603100d2071801411718044064000328020100c56409102290f0003d0540f108906144244103582d5074640101d20309002d824a01340e08402508404010003602150152040008030410030400000000240c0010b50a1201030844403410301e0607407513948201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 764572095 1250 764570845 764570879
    0x7032d1715091603110a0f0804050c0d050a060c020304120305070206070602040905041401050c070f02030703080f030f0c180909150903070c1d242706040e0601 70
    0x100d4101c824103403501203510300200715086000ca24a20f04500e44498061107444545014079021500345442240c0162001c66803486050030f0022080010b02040307030070841030405038005803101c0006141e0380380003662684030010403518641440841200745100200f07036003c0341c1d142c2410000406450300c0c103941c654020401030380c00880c00c00c001c0c808940d003030009000404409500084034942802e0070340d002d06102d504544681d051905000e400da9690050310000d43c2c01181a2a01c058540b0000745003085550009101c1d12000c912050b65002c010080d52088640343c480b400c00c0e82d6840751524241c0300d000482e801003500c40400c02c285042c15802240e02000c1c01003150070ae500c0454000c032940f5000c65241e0b145500c00a01001009140f01045000380440030708444039110343d480c80c0003058001401811042c0500104640c0c80080d40c14245060300060042d60f5482c0440311403000018043c040c20303120f0060307207011907060304040c400c40743c2c5803011a0103001c8590031300d440609010210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 764573345 1250 764572095 764572111
    0x3020f04021e0715060b0901020d090821130b1201060c02031f152301020a0b04020f060d0c030207060b0d0f080306240301050306070c0825050307032d17 67
    0x4050212941094403417030f8003410070315070b656840d4641c50000905e4451001f444008101e68600d01300b004580024465298500c0151401c21051019001001d540a040c40e85540c2d101031803030000302c14a05c00300410303c1086440d450281ca03038843c08141e0b031903280b40c0002501075110152001d580c42c1911003282c80400702000205130402190306444614195421055403403000540c0e9a03d040314035204900c05074020700180c44008150713200c014107078400a002034010059405180c10907902c8034201e034100411860b04100d0001038141c014001d4000060403180c06240c104e915096207800f00500f18840c0d4840c8904600341e04a96451000d5000a4040da1300b12540900100e01141003007406d610a0207030f20106a10780d8034002c205032810b5000361040c000d015014900b03e0215244004581208904400701d130214a011002d241c01900d04240c044c3c0513020224120042590010202040300781290078503c828036000501c2c101a0a00040207003c102c0d050f9800c170394031a5641142c0d90040c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 764574595 1250 764573345 764573363
    0x623070605130605090d0206012709020604080303040c080c15070f0219170709090c060507020a05060c0d0806060a0207060e0d120807031a01080a150305100603020f04021e07 76
    0x159115419190103480002c0150401b01d081d200c0076604201d00c5e8010111a50718034055602d400e440321002035130920100350b407500c4d02417240c2503444003070440d4010650301040325500e00d454207000310369820720f028210040c000c0d00d00345892490803600c1c0100e8500220402481e2800c15604c2d10190b243c2143c00300d800800d558480320b4001841c040342402403180031034813550700801c2d008560903c001030708a0b0754200e140844050220301407200e03440941d481030501550798049400062402c4000e036020ba0303402200010611035180021130b90182c3c00c50396071642810f0f911641d0811100b4020003c105006034004041000414810070010b8144040540030004585558036240001c51a020000c40480c01c58014030503402e50521622b003080714092a83c1075400440800242120005000700c11900c3d1030f03140c0d8203009485810080c00035688042226100c0000007c1c0308054180c40c070050348035100c451110b1426081034000c6a80100c0e840000b258015001d00c8044002d800045003900c40c0e0340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 764575845 1250 764574595 764574631
    0xa030203010c1215120f0809090406020c0c01090b0d091406070503060a06090617071125050105040b0405120a12030519020705100e0c04090c0623070605 67
    0x5081c032500110a810380d503100d050f901c51100700d1041d01c08141c005085054070001c10000710038085210002c03982e00c9001000e085001d400c183ca580c1c069030140320391083e204402e00040060300e900034920314800304207440c10000c3c2400195203054082c4107810f66a0401c010b0041102c05c6507021413041845804070b41040390510007070301c0c5008406ca40b4107000c240d000080c41b80030720f030110082c00203040c00d2410040b814280300b4000d00c01c1d503c0200c8000c83c02c4614002c519458000c0300c41c06002c10f403410854400702010300c0c1024020450020100040e0540100400c0551050b800c071029124060b580350b2400d403900061116070b00b01040b9409131402000b800e14000b0b07044480b115040480c503a00800c0700e080c007581100300e6000b181840a1014810402d00b00041c801060746d4061030411480012070710b2018003a00c0c2491408021a0791083c50001e00e18104058228024183c030340581d15009000081d509150b01c0a00c140620040441c1c00d014020010f04c064205545c030800d04522009801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 764577095 1250 764575845 764575849
    0x60501080102120105041d01110904110c030d2c1506030703020f0607050102041a0406092106051009060e01181107080d090f0302031c0b010c030809120c0f1005071d0a0302 75
    0x8610055503d0402400212682c4512f002c0c083c0071b4580302d051680783e28000982d40984c0c0d0320700c80d47c0542e1601ca900c40d2403403101c4440ca03a000718040d3f445c0c59110b581c0d024202031103548584469643c2c200c0030407038030041f507a9402c0c0082d07840142c0c0c0d809030080013080141d40c02c20580d03402c9500308a8945d0340810001c1055801c40156000540b041030a030754503581841030140036444150421201103115103500402500000c900305403558000310b00107219240e0034295040081c00d504024181406c0800001d450b100f40c0301c3e014100c0d000d10701da200c201c01054410744252440d50291403003140091044501050040c0d0061262032070320000051040c001b07942d00c1c01c11140d170840c06d401680010400842c11006040c0743c400505010700108445140c42002a00c9100030341005420085001e0000701d66100030858080020004086a40c60703081066001e07649444080c460f41d081d00402c1c848144030f901601403580500400d89034640b40750302c94070b00d40c3d2200074280d622591040325988008056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 764578345 1250 764577095 764577101
    0x50c04020a0f090b130b0304020a0b0f0a030e030c1f0e07030b06010806010c150e03161b091a010e1804030e011404080a020d0218010b07060501080102120105041d01 72
    0xc403420742c4812031003840000c00500901071a80c4a001e081ca401c01441c003041d0740030210385040d940c02d03440c0c050f2641c5481c008500648e4064126096400c000070382d0303403402941040030b4291000303035560502861520180ea00d0301e80c043d07000001c0c1203030310002c00202c100310b1b29804c1c4180621010340c001014440300000f41d1416001d41d000303032000c01081c0148001541d005401607405203081c00c000550700c40a0b035035811400a005052443c07282d603820a4900c0b00000d00865040c0c48440c120070503800342e5814113041c40c501c8125180c00680c41840c0c0020064003c0c01071000c810b502036141c4203121000c0340155100710401705900d41c003072410f822010010b05103188141c00399010365110700e10440b0f100d0000d003030800e040300c904100b4a8240001c0001d4000020700c04021581603801028642d001d201040386081f01d11014504904071400200e001000040505101b40c0107850501031645d88000311401c034401c45149480e01020180180194101500505005042c484807440b414001010090071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 764579595 1250 764578345 764578357
    0xa0506030a051f0f1a010e0d0b0c130e100509070519080a06060518040c0e120d0311031621020f04050a1508181509060f01150f0c050c0402 61
    0x443c3c0085004259155071042c441001410078003042980920640058401c940311003440c108460a40505510781314031107140101540001c81c0d851604081c1d81d0302c54190040f0b010031795030013070031400011191180003949011794644154400c020303003840180032040d20010140700070301104101a03c400b1107514102c0c610102d00d5556038601c0d0030070400f030b8030560380b290340f00104205040c4841441d45882c80c5040c200a00c08890008103244680001c1e00c4451821072030b540d0111012219883d9000c01088070101032000c0d40d820040d00b0015040044d00740003da44a055155121200d80203407401044a07010320194114400021030940354403205a0340100b00410002c4004a01000710742450b01d401c0b0003605c000084854881d4003036600408400000f0a0702c00e00c11030302800501940010700400c26040e51b1100240454503040c400203a4901c030556004100d00a98400000c1075404180f48480c050100d07603504950303000d44d1f003045031103e02c2000183e03524051511440c0c52542c0c0c510061034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 764580845 1250 764579595 764579623
    0x30c1b12080f0f0a035901061707051c020603040f0b1005130504030f08040620040e06101d01031404030c022107030311030c011e0c0c0203060a0506030a05 68
    0x10381d090a80d6a2152122a00000c003100906e12203941c0d03420500d91089503c1c0950030458001d5603401006940080e042d4104506880c0d4a07012001c01c69030042da2030034903c1d550b074104541c18181c3d62400d02003131a191081510281c8000c10783c840040c5807007002503800134003654203001c0301000360702c4501101c24150351207204048041030030440c50400308070090141038542c004215038a03041e00c0c05440745002320303402000c00648400280c200219a40010141c080110201d00015000d00c00d000c1c841d40980138007000c42d4558400203100d8074266946000c40c08071a030f501060009419400311103543c0c04091281495210f800c410840c0b040c0d500e06034415402070707469140e40b00e400d0041c80008203c2203040f142c104907440c164082210700003000b5040b01d51503e4664801c8412603178060075801007202803c17155003850740400884186415180c9120401e41c801c00c20040081c00a540c868200040290941c00c4400020300044269001c0e95003c40c0103425520451565980c44d0300307109840400c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 764582095 1250 764580845 764580851
    0xf02040602101505010f1202070b060a090b100f0c0b0a090b0f010f03030f05071b06020c030d0207030609050106030b0a0903091202030a0209180a030c1b12080f0f0a03 73
    0x800c960402070504a11540c0c0d108101c521003080020380102c80a0003aa41800354503400014214898000100040004c060840d02e941440c50502400b090a8860f0751080b5528480070803c49610b110300c103140c02c4010b1008008ad0003805d001e6a040a86011560502c51000019404107a03a60900f80c0300e1980207400040c109101c0c40c011018a001810000e01c80c08075000500c628002e19000200307890305800d010f13000c054041800c442c10301c502c3d0070050000030700c80760311040800381000303a10a0742c4954003912826001001410742d5405203d49401c016807000d83d0400102d4480d031301810100c1d001e0310003c28441c0d16601d500c80004000da41d103001c0c4566458110080c190301c6008003001d8030084103900411000b030740000783d807a40110b101900c5144d13410081410400f070f544000d0412090001592120541401e001d800885401c50075155003400030461848003460020040c103482e90000100700b80c2030291a02c0510340c00a02d880070944908005803c0d1051184002e071500c44590b5a001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 764583345 1250 764582095 764582099
    0x1b1201020a09090609060e28140708010602030a050906161416080a0c051e0a2603030601020303130f050102040f081605013207060203160206070e100507060f0204 71
    0x43c808484003030780b2004d001072400c1401e0191604600e07844e5041109007130055040c0c1e00b40c1120502c03200505030303c180341924140703001c05860f18081c40e42e48203c4039510340340c0590783e8a800a070384903c50400700b0000103500b0480c03d01145003500191004880110600f4112201541e8450340940041d05e09811548a11801c2c40d10f8000e0340b03400000f400904002c2c010200c0d85541c0c2260700c6000780609840307040780d501420110140400e8120800300020078582d000c81c0d9440e6800d4203a00e8203240d035042920b4000340c4113440100042200d02540040e4001c40ca156104424420a00c0380c00c14101d8004483c0d91000000c12801d00142c006000307000074011466151500361494604080c110081c01100b0800030005a0b070030484950860312452030071100032a10348404420b441100211005041c008240d80c0103000156001d0361003a194040c0140d8004404041a0f0b910b0104030750000010741c1030344441c1003074101074104070b81c041e00707604020382446041e690340d40507150414840880f296001c01c003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 764584595 1250 764583345 764583359
    0xd021f0911181f060807080601120603122703140a2010030e0c0411160f030314010305191e060e01060501140403020f0a0305061006201b1201020a09 65
    0x80b00c0c0403d8104081100d070307a00d0a50094800b04004000c04144884880042c1c0b461b4003c5000c13005042052100304002d80d1203191000500c108190b00c0000a0710701808100311081c01100c1c100e00c059041c10484a0300d195a40300031141c02d00c50407242d601e0003410150303000100d8030000c030300452a40b03148214204100c42c0c2800100c6c40443c0b10002058105000714040c604089002d040344d03c000d5801080300100d0001039840383c450701c40c030b0491801c5c0c1c00c4500360511140d8110001030380e200f5074040c04202104910b41561481c00e001c0a480340d005507102a48107101c089c031400b2407510500400d4442904405404030000714203031305484550702d40e11410400724080c419003000d8942401c0c50b03004510101007d1066000740d000081c020200e03a484441a580c52680541c02154840112000c91400c450441d00c021020710861000c540fa4103203443c600c8207900400010048820020803004240d4028001d44c1c206456400e038000403110314083c2034001c20300051003450002d8607110745c0d003458490 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 764585845 1250 764584595 764584621
    0xc1c1d2e06061d030319020a1a0621010b210d03051003020103020d09080a12061d04060b0103090203030d1409030307021f0204050a03060e0d021f091118 67
    0x254042880d03141000901800760031207020781c14040030b00b190490040381c03000400d1461003000300342091a00310807201c0c1c0311941c2c0042d2000340c0500c100001070b600009c041ca03062800b0800c1d039060b41e01440c00000106500a2041103545041600001140e844102808210300c210b910b0341300140a9400e10540307140440810030001a80040c1c80c04101501d00741d10792480c1e415481c00b00074105900068074800c001080d0300300c5009144c000080d160f40740009907014252403025045129454108040003540d0f0a204102e02c20308606211000c07a60307079581c0c0d5103400902c0b80803601070605641d40f041d08050f850800180c282c0c0400b20000060441c0703001c400750704a000042604c60b0b564030800400091070b6001c5050009005500103844100780c00c2605003019015a402c865004907c0440000601045403ca00131a9443c0c600380e6841c1ca5072460301b280c56010301d0003d207805054000c1e905948581a40c4000b03000c030b0250f50085080250203000550300c2c440290b403c044200d080e000d1117000d1450b00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 764587095 1250 764585845 764585923
    0x1909060f0c1e0507080102180a0609060e091305060a0c120509122a01090b0a0902240405030303040f05010612030906050f0708130e0c1c1d 61
    0x401e0414100d07006554070705030300301064000d2040b410140402400c01404010304001781c00e0b03030002551a05910383d000d94030080c200c1d02e00f503c02c1a604500107412809640b1000540d1050744e120754640d00000705104081c040a000c1030002100101440702054051240d140a80590000468500140c2c08010020000c440d03585c0c001c54605000c2c00800c0400145449441c0b800c000640c1c1c48002400c150648040a0358450b201054052046448030324113501909a152286800b0784841d141c00c005074040b12502c0600030340003a0140c1080078080e09141892141402040c0e14514051b00c500129041d500706031021200095040044410410280500006000c0d000725810070814981c80090020a8074810031041c0708002400003041194241154449504401805d07920484041d6007845240940304402480e00404042003a142d5a0800c507140c0c0b080302c0c01140c11107040b0494901c000e0a0003054a141a02c0807500040104414409048019071145917014158403011003001c0c00c407246 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 764588345 1250 764587095 764587097
    0xd020d0c090f11071b1e081605030a030e040b0307030308010306050a020306221b0f0801080f0a1e0c03080309010f050c0307180b0f090114090f01141909060f 69
    0x1040081c1008409440013980c1054594101800804c10200100241d411a1059240f040199010241c0300c109000448a1900449130f6400c001c888144400c0704501400b64190010030780000828411a0843c082c2107008100264401e002000240341c940e89500840204075864010814031440e80300302030744642c9014080d460341c5001e000141c1407900d00c040c183d440912040400c0c2a591882d03001d814008040d00701e407078a4640a042c06071146940c10391450000b154000041100540801c08941744000f1500420000540750b03584491030203a440081c0701d860511100001017100145c0040003035024480e02e43d940d040400c501c9003565401c0440d01c40840c200320512646002100c1100e07480203170362405110014130312001c50000c8001d1352025508660115240c45580e070004020a8144000d032200503034503c2c039240c904149c0c020700b808242d0082010722030446a50207001c0c8001340420083d01c96280c003146009a140302a002c1012800064460340705000071500300c2ca0410040b459 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 764589595 1250 764588345 764588351
    0x10b071a160908060c07021207030209040b0613060b0d020715050a02070521091215090705040e070b12180a0c0303090e06090a11134703060d020d0c090f 67
    0x13070104c1c05c6951280c0340c070013405000304003002a6148028404007003d140c0c0100f90389118180b40c01c5c030401c00b5006503031a52040c0b403a08060721a107240384c0b00f1f5504440c031800d03101d1b0520481c1021103000390403c4da400d4442a85a540d45031595403248a500d210b02061000107840c1e40c0070b400d11030305e4000c030b100c082c4404000222144001e5203026003500c80c101421128400c0e41c0c20b08804041c01d01501c44400c02c0701005101c00c0c4a0003c0010820310180c440c203171001c10002440405059032180f440c070075200d800000300006540741c140d11a6040d44981000b03540d8003c99800c0e6209458050404401e42d500e1700b510805004040d8001140c4008002081c452011410709600150903c9005410342c038409680c0c20030385200c0704181068808141d4050102c183c099620340361030b14084d00024103c240200e0f42031071160b960000d401550100d2224000e03d6003440b48461803c940d81d4000b811065214a48001c00c000680d00c00c0b0300581210310a658050405141c05407190554401a041070b0784141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 764590845 1250 764589595 764589601
    0x405040608060f01170a080f04180605120c0916020a020d080705070902091c050c040e030301050405011203050a08060f0603070f0206010807180209150c1b18010b071a16090806 77
    0x150000d000303501160084000c0788e581e60030181d41c074480d215136401003600e60710111102e1050440d5034050f0044400a40d8501c9903003440040700d9840d03090311500b05520801034000304902090400580e05034a02c980100e40c405940d54000075400f640745002202d020000152031350400c08207008010042c480501c003981001420400202003043c883d2265600c0070f940c540c10002c0c05400c008044000e84090310411440b904c000d489a1281d00900401c0d00890070f100001600391610440525140e07056a600e40c01c00c150040100c1e0300310030180c1010350000900030328160960f900801180940c2860701c40c0c407030003200320001a0030424140d10044154005c27181c101311961007140b6500ca440200600141e9a44841c0001002501c0c2020341c295524004585081c213003000203001242462500c514149a14882c820840e2100b40c221260820810407001040160480006055018400c038070720b42c09d4058006006120030750448003561782402000c0900b83c000d0b08144440c002c3c011032406822645 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 764592095 1250 764590845 764590889
    0x30313110f0a0e3121050f0a050405040c0f0305090a0510020c0f0a0c061205060f010507030c06141b031005010516050d0207230307030204020f0405040608060f01 71
    0x105403482050030144181c1d00040702d02c00340080c1c07001001e180e00c04130141043e19443c910816150002c1c04c403400400b03c40c80b200d5841c0040e1030060391200139600e607850441c03604c0b80c41c28075810081c00c40c02440f209102c04101642c0b1401400e000c004280d9402c00b224140050040c162500a80105101d4000c0d003401c07070200f070010480300c40000848402583d50300700750010b58a0602c40c103018502c2802551f14000801c029010404200c03210395079a01d811423000c0301c0d1002118000c0d181240e210389841c00021f013550040002c1c00300381d802418540164801910385100b903a90140d0743d0700104454008100d40c400c030705c142001c0c000010208450961610581e0614850103600400c2c1c14002c0200e460751280441c04042c41c1980c0e0300c141a602e40310800280a55035a00034041c499148005446182e4444000886e0a00e03140d401401030620519507020b00001b50302c0a110401c441c082008041501c0c0c90742c2c003134440101a1032008000a00e040682c4450022041e002154980c0701038030302600c03803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 764593345 1250 764592095 764592109
    0x6030902100f2c030304080312010e07050d050606070807060b1f020c040e07030c15090501170604150b0c031c051612060e071e020706230705030313110f 67
    0x10242000d907503042105814250301c55504a10300084d4503200002d0041110140480034115100725142010034a9880e500300841160742201e228000800034011341f401d4100540041e0382180000c0c004600d030685546452031240c0c080e100035182e0503200d07245a400c509050030071007243d0101920305814080302e00c00003500c0c0d40c070300d1040d0751190340c9034030300b80010281c144601c900640d1301c00003c1c1c0c0e00999a0340c440c0079082c02c03000c4601c08180007040000f501c3d401100140703000c000d11829050555200c0c030401c0001e01000081ca140d01c00007000108a055104000b0400400b030040219141c402c805001001c002e101000918031608160a00c02c503c6452030141c0e80b29900d07414845111040d83c03c1c1d40000700880e13400b99400400c40d0b400d11141c20b8102450382c40c090700c0031500700ea2010413600306903925580b5105510014100090ba507101e0010781080b84040301011701e00b60700d490340d9502c4140c0355400650b05085a054480c1c0c44908108084080d006000e00680d004500d0f07107400c42c002041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 764594595 1250 764593345 764593367
    0x90a0b36150c0d090507090c020709060b040b0a0f140d06051309080901120b0307090905100606050a050903071d1029181503060a060305150402070206040b0406030902100f 75
    0x3c0151a15640c0381007100c1400f400000e0222a00c04114120340ca1100a41c1c070101d41c800c0d0300b162854010082001840d0204883c1507881d0602e02c4c074602122410111203065100c40100204100071040618a08443d001050940c6040030702280b00c604080800005440582400504601c0d0404030300c00504044182c401c0c07900c1c242410394042d02d8840f071042c003030000450450b80c5402001008601100964082d0307541c82d001e00c08580e0082107a070759400496115000c0c0002091051000c01c1c58144588020501c218020742503440780782d542c640c54515810360051a29840100c40c0c00c11901c076003d60442d200419242034244408041030383c04040d10042182c492098000006241051101028030401c4081c00503000d05200d00508aa1821941080d5292841003a0664000602c0307403207030107280c2c01001500d466406514400e0300300300095001a804a030480d005210000c1e450342a070b00504014412a140464462581e204012110703903c409801c0502520310340744d1507001d6020341c0c6550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 764595845 1250 764594595 764594617
    0x1d030303061f020a0b0406090b01120c030605061201060905090d0504060c06092d0203060c070308011401170c0c10090f06051f03080d0e06090a0b36150c 67
    0x8088450702c1c0d040b4100f51038294080d20f1700c801341c428001003280c0c90707001900301e80c020b4404106507600c52086002c0d4030840d01010313040c4901d004003800031850b20b51100740c00c60001041ca4000e0400f40401230709565565000080d01a034402c204031499005000f1400101107a280442c9010700303007980502031204040020b0301007079950303802c01d040180714081c119001100700381c2442e41d00c000340d640b10184043d02c00100d0003130107100e02090810050405035070489074103450702441603007000600004108500c00305810000c12074074400c08004880247c5001d2104030042030f80d5502d4040d5000d1030709418920201207a81342a40300401324040910144001c2d1740003070f000ca8551100c0e02c40c0340190041c06002c03000b03c800c1c1c040c0001040249401800a070250f50024015841c1031400300713844090448000460390001a026400241c070018100c0e4000100650315000013009042c40f007007511404001c2e40e450000c1402c110303c100e0100490000744c0d408000c0180030f490060242c0115010300c00c0e800c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 764597095 1250 764595845 764595889
    0x3903070905150a2903010513050c09060c0d0206240d03090803041d010812090105070305040e0f071106010b041a0405040903180b07050d08060d0c061d03030306 70
    0x20b20000c0700346012611403500420a5100e5078840610a01840380c80f00c20200800c40000e01c011130091100682c1c0c100d490007000d1810000030745001001501005200141107041004524072aa0340c0c1005010704440c8003009101c0c14a484801074a0180b0150014110858444101100079001580d0396900d8800b56060940200d040c82c0c140c5200c07840e50004201b500000c200401c02401c40d0f500c41d4068840c1c0b01c0311080726681c07145c00c640c44160003125540c40c1d803810424503041c1d50091000b00b140a1003450308901d42075640d420803811020581d45200130690840030720000d0356100300c40c0641d01c111200a80a2940350510104492149103d2142425410800c9507070322861501503400615004e40b050040e0015842d0007440090401128442100f01e03071800b0580e40f0b01c2c0800c0c1c82c8042d40c040c1c0108081d240402040d105000c0017009142e100f0a200e503914005050700e0300e070b0001494a91148101200d80140c810728072000c0c42ca256021754418410018195a1036640e0103040070507040704 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 764598345 1250 764597095 764597101
    0x40c090c02240a0c1403220b0408030a05180717031b0115082811030114090606010e0a0e0417040303090f0b04060c0b090f3903070905 59
    0x1e03420141082800c1d00c50b28600340c2c0081c01401e060742010301c1000044810840f61303689500550340b214149611081103842400003c2e00d41c0d8491160201440410b0781c840000c9070303e540d40a60389102102d0031a940071012050040020450103070a4010b001030444108000b00b0f2400c05960704c08500c90b11240320401c042c1c90000000c240111400f20303658001d2609000c103504c16248c007805040840c580d03611007050000130b6158000c42e6500040e20703042280c06542c03040411a10f00c8010210042d91301e550b00304180004c82d60b0034412104018210401072100e03207010701d403150a25400908043c184544a807100e50075a0798041e038101503480380c070039a0a4944946c24a410200c00c0f82c4055410b4040000700131003815089a446d07000c84400c00c103510420394440d01388100d14011845135401144c0340003070040002d94100da010745e02000300c50494070014810404c4518280a005580d009d0508010140040d100038214200316100b000b220b658029048401280d035843c07051041555039580c41002c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 764599595 1250 764598345 764598347
    0x3040b0403030219031a180f0601020712120e0906010905060f160b0406060602071410140a0e030705030304080c28030804060e0a18090f0602040b040501110105040c090c 74
    0x143c603594015000603440b9500c508074003600501c0000306d164144040d04204038000d10f004100028191410b071031468150310340542c1c01408803006490503042d070048040101d040d000e081c543e944500d02840c40001c100308945405000303a1704492941e4082c45144003082003a0b60044640d40494006a52255503054403d14070b81850180912001003003152141500510540840341806107004a20400200350f03503000603039a8408601c1045600101d00e00403841d907143c00324980b601e00380282032000310191601c0004402e540002e58580214180040d5100c0c00e04042002d003002d0101035004501d402d0400c00b400b0741da03a80381c1e2401407181003c0030090844190401c1c100115810038900300358810345a04d01414550881c0c05079100083c6801c01945841c034180c4903074070032246251440e501c07040c103115078440580030104003a601c07a80b01c0381103000058003620081005200011406881e24185400182186142c006c10038441e03050405100102e03c107031104208035180f00d407002032a01c0e01048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 764600845 1250 764599595 764599597
    0xe130b10020303040506370e070e07090503010b0f0d0f0807051c081e1b0309010f060503122d0c010903080c0f0304150b1003020c0613020603040b04030302 68
    0x482190420684100208101d8000002c0c41c0214810350580d9141da0303030400e142c0e090110490400c1807480c1c0e603207406100e00070355080281000041e00760225003080c548074590f02d0486e455114040d041c40c002c0410a88030741c49850440600f80440080c04035441540014000c1c410310103040344100c5640c03d04e4010020350300d03012000158410b44080c0c54808034107000352101080a4000070150401c20220451482030140921038030302170304c084d038004202d9901010b480400601e120701d0410039805100017812800b01851284000030000308890304101408016140e0560003503000341d00c103d074210403c42507482500c105e180c0c03280340c058600401070a0180e841c803241c01c1581640500151080700c166040d00200702041c040d40380c80e811602ea40b803401c1d5a0303124441a8520110041c400b150014004001d440305409801d00b000c116103400340c0c0050030600d10040398001080d40007807680300c2400d0a00c60f0036805180c151074044a21301c0368001c02d04e42e1200500041042c00c01c1800101010701a034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 764602095 1250 764600845 764600861
    0x180f010905030709140a020a05070308060a0909080c210313080712030504060501081c120e0d0507030e100c0b0402220b041d030a0804081c140a0c0e13 66
    0x40032500810782d55203074400101905400790303401d0769817800002c03030107105402140c417806416034501e4548213154904070703011103000d0a02c69002d00c801c00000780d100590f01900354924040d660a82d0f44200002441d0700d404003110341c94003d500e116100300011500402074a0784110000c0c0a80005001481c2580c280c3c0304071b4034010f00484100a010481c20740c10340c03199120b94456402007203903989400002c2e03a281040b1510a40c412001d4118520041c8030301c052940700070000002060049564103203034203140601c8100030000b00046148000d15a1041c140004080306854010480f202040020f10100e442070010345441402c81c0818115214040c14031030800b0042c01030289100c410311188040d003104500644107508005600303401600008400c09100d24010041d842c14140007815128070100402c15288000180101005100b80d0007500d0001d803500400080c40048000c2c00740382130742c00a820b80441d41d2030700228045a640214601c0320074801100c02c5039003c0c14040011026080300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 764603345 1250 764602095 764602099
    0x2304170a0801060f0e030c0616120e0907080903030a11130303020d030b0f090103020f0a0e0703020a1b0f0b2205030450030118031103180f010905 64
    0x105050400e900038401d5040c0d51413507803401d5000342005822103100d6200503d0b02d505421011040304646881e00c000c0998424141c911038610040e512101707071201b00060807101241c0c07210401c07212850f011107129030007125801c0100c81820a11107440c1d507400300500061401c0e5441c03140b00b6009008005449031200c42181500c41c0c0c680b81e1800079121000c524032035003c00d08040011060b4640007408108491000c0c212010301c0e880c503000c1001c0d5443e1070702e6045c2c01c60418074001c030714400e10401161240c549030301c015a40d01004000100070b01100e14031003410302d001d4484800043c0e84464042d200700d03041801c00c440c644400c0f1210617040c850140318074021117002200b6040010110147c01295404c2d42209454603032089a109990040804850790704101c010980c484174401c0c4094409031039042148008125080202c0c0c02c4800c48440130f01d1800300030621004044c0c0c400103858070400d464002c0d6050004a48003281042d4a03009140d02c0341400d084290301592040b1091300083c000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 764604595 1250 764603345 764603347
    0xf01050d1e060603060503030715061d040b100803030f040c12030c14070f0e07031d0c040c0e0d030c05030d06032109031502130302030d1110230417 65
    0x1051840034a160203001c0e0880e445800e180c0c000400d103001e03208160841d00302802461400d01190ba405080c04a00040306103815a1030501060700c1140c44509230146286a41c042840d050505000315943c80051040c1c003102d42080c0c051100400c044143c0e504035012603183c580320b0701c4030b19140c06c41a450303420400e50301d2680ca2170344042c140d003c040506d1050249800c10842d44051190b5615091580101c0030025070f42c038020850f07192152550355002085140010b14060204207032a030072404071103002c0c255841040451414a014483d0316154041420f00d0304241d52076502084129081c2c1202034103001e00d8101e100c00f4810140110380fa0043c41c80130030403030a9200d10f40440d0080076524204025520650b0030400d1900503520b61040d0b903004003c0182860001288002941c0550303c0c03040c00000083e000801610100808002004280c0b200032048000ca482c5510f800c03200c1d1500202d06003009103070408803201903030003c8a00c0c5040140312031075507076080c150039100d4052501c00030588 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 764605845 1250 764604595 764604611
    0xa0605031305011a190312120e1b040f06140415030b07050c0f0a0201050d18170408120906040512160801060e1602071712030a02210408090f01050d 65
    0x100c0305004101900741290705d104100185400d18a004000303000007400720002a4000803c203005540c14004032042100c041500f8080d00c034524100b4529011000704102c0b0051150200d00d0140909014502c00b440100542850007400b8141c8400004250303019554039010f00801007406c410000103903400c01034100d80c41c101200f00810310350103001c8840f0706000d00140320300c6034040451100003442e0140c3d1421b08148590300c044008003e4413094007224a070001078113000680c14442c5d2019801c84000c2c01d6101e501d03120b0160b041c000b4030b4001d820080d008100007246c03640d03410140c1c1e05546081c0c9402808a030711000d01454498501c45038005a01d10078000a405071054010600365020104040f9854848002c40e071403a00880e0103d40150300400414012203180e0b04e15040d034025144202c0701d0440c0303082010507840c0d1059071000413003600010030780d41c425034a64801042128185050f20245400e88a00503a4054001d138203200300001d43d40140c403684036005071003091401c12000c2012207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 764607095 1250 764605845 764605871
    0x10e150a0b1e1903050d0f020105090c03070b0f091f02010605120307060b061c06090b0d05061504020409050a0e010e0105090c06030406020d0612061103060a060503130501 75
    0x40000c503018030030035042641a25031400c0c002e4101c0144608071200c41c0c4070301c0c0d0000402c00340500500f80f000949180003c0000443d82c02c0000e94040714881d11002e02c460a05031000703094407401000c00781c96520140324880306440002e094000c8998000742e01d41c03103000a01c6031451a20900207000d42c0500a003417108810395018401d580750300141e4000f00229aa0f85003070100640c5d9006c12400c0070307003060140c0d0300400c030190030450303000c100240100e14141aa408010b92000158003950020703075658014061a040d610464001c0e00c4101c803041044002c699a10b60f0f00c1000070b04652358200400003030f0110f0b84032601910042c1800b1103085c003040c540ba1100d5002842c40211080b031940c01c001c0398020200061184070f00405240d0003815411042c5010b010746a400a0710403603426608001c43c1981c1016846024080e003544a0b500d240300c150390618406440050481d0380080c2806c0080c000c0690b9621441c40031035496003006507ca0351084030140301c50b044c18138058400c0d402c00910407600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 764608345 1250 764607095 764607133
    0xa060e1011040e0708040b010e07020c03010f021312171c020d0506040c0c0503030c0702060d050f01030c0f081c05091002031c02091804020d0f0507180b030d03020c010e 74
    0x1c1c40c800c3c4a03245041da1040c81c21114400705179000340c144a940d03c018080d4840030101c561748220f450040710003060310b000201c0c2c00c40d810320880c4103086901007183c0c4c0b00d5000d1018810001c0c1002030040c0c0681005849400c621010320b80100c10b000340c0000d601c5c503528a0449000c0303500c070300c600c011500c40c6000c140000150008880369441a803610040100260103480346500b855000343c011421a0340b00424a2107076400650181c2c0d000c601405920b03c9001c1c0d42c02580d128500c060000c05841d49140782103220001903802c840d07207001c1d4519040c4070070000041c0b0a100001114100a0450f080600c107803401c1c071400c1e0003241c10030040c00110031003903000402888a01c0320400301c03841000d01d00d016a02240038904ea1654448038a10030085040c2050340541d070480e00003001d282062401c0e80c0c42d03087d11000c04e8000c50b850303045124204400310700b14004500c041d200040034011840d1a0000a4039000030203200010301d540480c400004080941c00311141a43c158112024849000c0c07007140f503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 764609595 1250 764608345 764608349
    0x1903021027062d0e0103230a0617030f0702010e06040909060b03330606090a03111c02280b0408010506030c030114040b092b0215090a060e101104 64
    0x2100c0700c00100160b50080310040311000f84680c1d01e004592a900c07004502038002d92814407092210789048400981d0520002400307242c4140e00060820b2610b0358230668420005081c810582080c0900c00c080c01303140c400c58100350341c2447e00d06400c5154500081e1180200e800c8641c40345c0c50981003d080007925844901000d2003141255210340c10859440340c02c8480c001c91090404000d1074120090200c1c5c032800340c0020b00101014140010a004030303840000381e43c000d50340d5148100c10340440b0f05040101c0c44a5503501c28516482c00304503004141e01240032030312100c1401c4204400c0083c4035900f04184090140f00c0c00c003507070351981c070b040003406800305807a40c034803d025110140e041ca24051017502d0140602c0703080e0880c266685c0c0c07a0900b1480004110070084d010742e4208504400840340154910300204103030010390b80c00504000d01d44003110720200032100e6450306100488a00240186016502520108a8182150a81c1e0500d200701001e0300413542000d0000b1030000011000d002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 764610845 1250 764609595 764609627
    0x2030304031a0f060609030a140c150a120b060301330306060908151b0c0a080409050a050712020d090203060108071814040f030c0c0b09190302102706 66
    0x7079104c550070010144102d030700301a0b05030f0200321b079540001c0542070440c448440c5401510404100e640100d8005480c00e012115038850002d0704514203500b0440548102d03002410030170180c10b40d240403403003600c010300480c0d0a5404e4611413200500003440603884802007400f61b01c481684182001d0f015105500130400818a034540115140c5400201092100294840000280c60341c02d40094601c45507109038003400700130018601403403400c2090002c140d05c541d5540d6607940c540f04018044480207407040380a9818a000e202082e5400002c40380f10003002440161b41d9144080907400070b00031020000d400d4051075000050c07080700400d6040c1206d134281c0c0700c021600382c5c00f07110a041380e0203101107038100360128000c180400d081d18600702076a403003424569010001c540720401d2800095100702080b1400180020315070404031000300300050b0745140010064150ba000038044289003d070710b0100710804d0742801411812685a40400c203d5249010109032034541c0181025208000c2507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 764612095 1250 764610845 764610871
    0x10f0501030902030c040c0504090207210f0206060103050604020417030316020f0703030f0c061b0e0102030a090302191203050903070f05090f0403020709020406020a020a080607080408030402030304031a 89
    0x5640d4020300440304455402009428141140e1041000800840e0540e04c100141480301242100c0c240c4010000c0e14069070039100402c10036407615441c9102d1000007400c100301001019942c50f0005200c43c0c110400742070114031540c030840031500078080e5030b10213000150803100c18040084044000c5002e1950b604a003e91180d04500503a034640c00524020000c2c0d00c081001c00120b03109110340c0010080031324040070700c00320340e0b1146801d80d1945140241d0945510301c1e00010107401007400000c20000380051070501d6a8040c02911f000c1c4103200c043e001b904280810b0315003490102c0c40c00c02400451085140c01c01c0740c2c3c14000e24136080206074602134802d1a0020801c4442000c107401291801000d01003599107a540b88031905c14041d100302c085d446519404030740c0d0159800600042e00580e0b008204490741c0c0c5c0104402c01c45142d10003a81074000000b4042100e0b80503030410350040d08040c0c010b86c1c03900c6601c0444d18520507a400902210740c2c40c0303e140445d41c6a00251800340c19070f00015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764613345 1250 764612095 764612099
    0x4020f0403050615060412020303120a0e0f060709060c0228030309240f110708030c0111190c050a05061003060f0b0f041802090f04170406050708090d06060806010f 72
    0xa22480a060445241c5c050020310041203007802403d685072645201400f50b03402c08291080c881c600d44002e595010a01c0d0701c0d000c855040c2c0404208964251907088001d0035541842c0401410030760441c00745034104401d014104055444684100003003810060038151862044100341d00001c0c07003800200c0002e40500d40008140155151103d207504425010641d010072608095541411005c601802d000c0d54507444510802c0600c0784000621814000d9582c5d5010040f81a0031030310078400c4a02e40b401b040c040030000d404500081b000c4d50040e07003081021010750341480ba10301440844000d0007480340300200403070000364003400c400b107900c01c038401d0012100e8618940d043d150000c0b00300d604400110070607882e514090700440c0b0100c100c10440807038950305401003603494204590500200340c6280501040250b0252801660211000a01c0c2041d081c01401040b508c511b8002a0420401194104855072021220400c480e44000b080103001da55850b030a4885809101310203000140100c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 764614595 1250 764613345 764613361
    0xb0115020f0106060203030705180d060501090f09050613020111010608071d06010c02090a1d010c1107032105090616050d050f030a0c0309120c050705150304061a04020f04030506 78
    0x140c00f0949109402650a6580e840400c5403150400b9a81c8614540f03180040d01d0035407142c0c0c01c1d4035801d40c094076001c28107604000180302a03e0300448121000c628041100010030b101007201a00700400308604007800040d070004864558045100c468154a00360000500810004803c02181c5c0b0a88074286200000103414031080f8040f500c8034041101640c4040c0149030085040b42c0c040700500000492a04010a42e0400038030882c07845510ba540d000800010703500840034803481034411004150442c10f682c4d41000303807801001c480841050444070019058000d000703486440f00080c0005440f9113445d08030446400c0702d140305a80c280102044181164810000c40303000c0303044400703524a941c544c0320800000b0003811803202c2c101551000d5000005030441c0066005030032943e1104894101814424100443c41d03100b644501040c1c86200e040c031201c081940d07802034000c440050a82d82d20310240d4401d0301c000c4007080c1c0c0f00317100084181c0c0d25030703140000d0825a030081040b16001d03650005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 764615845 1250 764614595 764614601
    0x6020d1206150e010201061e230a060c0303060914100e090d050c010f1d011a0d03112113050409020a030b04030c020d0c081005150103180b0115020f01 66
    0x1d44820454102e03805498a4090703044000034800620001402d10f540b50200d0200350054a205112800c00d20780400151801c80c41070340000a5000a006003c4103c0e800a40d081e043c03032007a42c2c107010100c061407045c14041d078004c3d0300034441c1c41014041484000114008414201e5050071040e20341e03c00440c0d60744110020030702c102c07035001c0180311400e50a007080e02e85070407071030f40c0041c0341d901e81200c04200c5180380250640544000c2c420040c0d00c02c7c03d80c07501e0a44044402c2d11446861032100e07982140e80d03100704d403c41590181090498100d03030005141c2040b41485104010901e01d0600d0100b4580d150000c00300306607070300c40082c40c00e601c0f00100000c0d114001b8019500c2420000140042003041d011103410612074207011038a5040b90340840c01340c064214040d00d84000c0c8400c100190102480b07084406545607004005c240351680f840248400100051410141e0b248100d00d51410034406050843d500b02e80c3d6898550394601c200e0f00360f0100c007915040140200520300c0d0318094140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 764617095 1250 764615845 764615849
    0xb07060603030305240d081306090515130501030e0309030a1b0602150609071701060201020d0506040b1509040917030907080a1713091802040c140f0f07080406020d1206 74
    0x902000c01c00049001001305000c05030009840761001041444120008c4c0f0441c24001c002e90b803074403240580b4080c10018820755280004c0d8064004010880c00034a4200000c41941d00034240003843d10071802c501742c558003c10100c50b401d1711400315100d091001c1882520302050f19410001204d5071900307803c90701c0b010000007402040c800940400c9aa103405054a5848602480d08280550f0f9032400140054001e0388646e0151354000341c06841c0d03860340d00805034032000a8409200c0c00041d403000c11000f1540104600c04040b0101d003c4000380d41b190048501d158200001c2e102c500391a010084060f031045d50748442c64403596800040c0034030701080d042c2145070801134a100500084109080342e5010010301c044051030f181020481503403a100fa080c0500a03041071480200c050b1051104884048403000103002c400101038141c151507000b21116050144030003926050030403180e081030b0145020042001201060204005a0002c3c03204c0041c9482d0340d400c40c06035110740010084400038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 764618345 1250 764617095 764617141
    0x403090906092c0c09010e0118180210050d021305040c0f0807030c14030a020c060109020408250e1e01060c02060412020102070e070f021204050a0e100b07060603030305 74
    0x54071491504900c0307404070f220201000c256440c0700d00100008640c050241c00564450390950010721001195203081c00c00e0700e06110081042c05050300070207000340c01401009114028031041360700c07814072071026103030454000c041c02d540383c044103001c000e40304d13540d4000d15000b9450581c02740d0250380300e0202c41c911000d0300e440f04861078452039401c40190160400b10b0040c003419980483e07244482030300451181424101c01601c0714241b031141820140f0680c040311210f4014002808403010110341c2c481416040203065007401d484500e200b100d200f0540c009241000172008102400030300d50791044582c41001c095001907a01c410055400c80010740c00a5048001030005110348541e4031803495000d40140101c54040d6034071440c0e148620070403509000092040348c034407100c460301000807621066004400e01c2c2407c1c105800300c0e803040d515226071038035491041c01040304890302c4a102400fa000d5000c0e100c2d0794a98500303007007001c0d10441c841103001914020029100c144600d0380010b2134401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 764619595 1250 764618345 764618381
    0x30e030a080a050c010b06030403110c01030e0c101209050703020127050904020111160503070e040209280204090c080c1e09041425050f030c0f04030506040309090609 73
    0xb40c00b0440b000d03000780001040c10742d6070b95000411540c4400145102e580310b5942c42410b1180441c003103061690200b4954103041c00e00074000c040810204540e540715009035101c01c0401d4040508455881000d112000164903101c0c01c20240207003c166403081d00c1c001e0701c03a4400130391100c440c46189490b154001144c00701c040401d110307900e0a202c2003138000e40145040c50b41c01c4101407009040480d290354007070f88c501504204004904062011500404144440041c4ca20b05600407803203801c0700401507940c080110180e90707031902c00024000000074881c0011511a81c848600800031318080d14a200818180400964102e00ca02c049a41c244c441c42030115900480b100c045120390031201201e81d010385c64100d4442038000c2000315034481c8243d250344000903080040300940f4801c0d07848500d401c200c0b00b000000704c1c0200d55400c580e00f10340c0445006031f8401c0d03200a03074a1540200e41005115000300c005000c11f0580c03003010714041e640b020404024035507880307010380c048602400d41c02040c410307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 764620845 1250 764619595 764619607
    0x60904061e0f0e071409062208012714150415180f081c090c0501110615011707201605010e0406050301181106180f011107080a030e030a08 61
    0x4170400021801c1c0669079400da041c44035a100041040e001034190f0000603171a600c07400c2c1c95100b0b122921008081a5000308401d90003450b145009403000352001410200b031440c0c041c10002003c0c940f00890700c0b03040c242d81d0004200d01c0c4062180e8420b4a0907104922852131581d14601288610815580c03140901004400c075603565614000d00d403a01520305260034002085000507035070340f003400343d100d8a90008641d105440c001c0075511041d0040381c10422810307180c00d070700720001920980120504110b13080e8001c01340d00403101c0707000c0e001004c42c003118500c061004c0f9a820001c0300441000302403030405202080c00096035524007000715072aa0899242c0204083d50040500400291000e00027040450300c420119080d103224a5106030328500103404c3c80d0901445900d1140d003448211080c6d458403000039000c480c030102d84080310348036108205000d941d50b030013454030501e00640002599100c55540c0309050321021070240c2500424102e4140b030b1410304d008649220255070018a15007045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 764622095 1250 764620845 764620847
    0x60601050d0c1e0c0c08010203270a2f0111060c0c0c18070909021612120509061e0103320102070c0f0918020906060904061e0f0e07 58
    0x1c040102860107100001000c000080f000700700c07060302c1c1000d503120703044002100d14240d950641641e200c201030340d01c14410f105c14070b0200001c1c0411503807048026075500c004540c455080126054000b0020741590040c0302c6182d07e0204202c1d5108000040000341002d81030042d1240c024038659a00e154000b10005039001001001900c480c413021b500311494003007528045107510400c26090440316200e40308215540743d204c00c420b0050b0908110960400603050401000000140d8000b44400b03a14040015010310410032201320100754041407001d0b0030038582031511030b00c05a070b004024040c401c941d0f1040708000c00c0301d07a0490398000c002e601204c864915043c0c03400020840904220003041c403025007150f0900150440300d001d412103031215843c242d001000b001c080d5000955860800d01c119035980c82c0e60003450360060f015a166a039039541d000001741a8482c0e0328005503c10703e01100403134003544466004501050800e40c150780940c50b0105504400c2031445902114030300e40b40051591 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 764623345 1250 764622095 764622101
    0x110a0c02060c191a06100c02010c021503100302010305090c03070312110d080609060a1d06060c0d030f0b0a0f1707030b010e0a1d07061107150804030f02060601050d 72
    0x4102448282d0300c214210300f2850b200f2100602c0269420345a40828211101d070000d0107a81004044540c0200810040405072005c0c1504030003905008007481c451301907480d02c80c039001c00960036840607a80c0b880d002420b00c418012a00050780042e1070400000c8104600150401141e900203005044c0300d491a40e44641070701c0c00f055201d040001009001d2040740c800c000510b03410207562110710b44ca1801c0418460081e038010040351140d51031410030011041c0b20001c0081007107002e5140201c581d50f00d4017140c030500c501c3c3c039400d0043c030139140f4601c02182c0c1503201078400c42d000c03641480000301c4641000f0496205000c0c209a120b4030310001c124070708070760240301258200c0310b09a4001c41e60302c0d2600f8074142801d81c8058800c1c0c807030b042048484c0741c0c141300e601d1192035400703a07550550b10b200d0304c51035851005000300f60610007402c0302076007000000c102c01d06c024403a94840c131f000f50740310000c01004140242d8084000c00e1440c00340326009400803800a1040106035140c0b41041e149c0a020005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 764624595 1250 764623345 764623357
    0x30d0b0901261e0a03020105071e08060a15030f06120b01260a110910080c060912010204080d1812020d030e0d03090812041203051b0307060f110a0c0206 67
    0xd500c200510b100d5103d00c0f1a50641e0444401d070068482102903081c007a007500c000506070010020000c159075808851000d840100b800c01703151445280c1c0e0b4800110f243d803c102c0e0442d0610300744030402441400da1540050512550030102031141c0c90399031468444400c2c400c0d0005001c0450f4400500801928242c580d1080c42141d00d402d100d030700c41007020740c00c101408800340c0e0300703290f01c02c01e640d410304140000036088540c0480e09046a80340044040e12602c10000322441240300290701740c515552590483c1d58158520002c6590750307a50042255100380c0d204890000c244803044ca003800604060360701c4100da00c51141304096030925420490719055103074088080c092401c1c0200156104d00c00c042302440d200c4d80750607200a00f004012403824060a8201c8400b0b00d04000a210417807008181c4142140d042c2040c603201d01c00c0e801c021700d51314032100c5080301d40d200118a89051100079005400300c110391101c200081011484d04140e540710b41c2c50b40303130085800b044220700141455002041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 764625845 1250 764624595 764624669
    0x90f02042412050c070c0501050901080a11131e120b0f040c0905070807200a0f330612020d030e0609100206180a0b161e02030d0b0901 59
    0x10700311500b402c1c50403150300365010700140d40f001c10744800300f02e1641d020401514090900c0c40c103001507140001e040308001020720000c103403503031004803009e41c200c03080e20458901c130780f00c10400d19112101204040e8100f00d105442445036a80000c6060b4958a852255074000c110701103103540d4038241118454010f001100c100006a000007800c0c0814820207000d4200395550041c1800c188000030406401086101c1010034401c0a403c000d00000480b400f489a001c0d42d19544d0b501d150504d949100c40040f0054903412002e10181f10104030940b6085262115241c104903640d140c021791010381442240094102109a1040c8007017809240a450b03038100c0100414a02509a80840c0c1071407a0400a100541c0c0714500780082d070030749459030038038021f034082c010506522162180841c0e01d5020b03000c03202484049071200d07060b600c0348c0d0307424904158001c0c4880f030340080510000d40e00d80c0512140f09240d0701c1c20700003007810300c0c11400e00380c102c032510140b440340e160300703002d07424045a201c181c10340c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 764627095 1250 764625845 764625857
    0x31107030f0311060a02040f03110d0f0c0e0a0c0909050928021e061b0703050d0c0311010b03030a11010b0d0305091c17180a08010204090f020424 64
    0x10744041a020394a403180d43c8000410721048035440c07900b00d0252041003c540144002d00c4036800c82500941200d8000c010901c00c03100050109075803c14480029201c118400c0568040c443d005040104441c040d00c0c1441d00d541c0d070080c0700400c80b00d0342203420000a8880a040000481507006280c109503800c0684122218030564406004c08241c1112415602c0000c800c2c154500f420b10101e101800c0511240c0300c40c004000146c0b14890950302017000b45501074040d030712000400c0030310055a40001226129407058601512444143c1012000502c4e1202c44000c0080306020b002e4440310302400441c1810600036090758403c0381d000d0355200940d070b50060308007241d81e603525102a80303000c1d84405958a150200b4041807410112040d001d02d12502c112070300140c1090035000c0d9910151450359281c400c842c0ea0030901001c42c0c18040d42c0b100200b50f0116220b10107600510031a52510810070074041003071007406c1a40124400c00111200d0240c8040b4007070f003c8100700d5006071003403800c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 764628345 1250 764627095 764627099
    0x207050d030926093a0f17040902040b0403021f1706030a05070e01050411161b0b031e070e0109090213050d050d2a2607080c01140105010c031107 64
    0x1ca40448045101445d4806003285013403030b0018805842502903c0c66001c0b1040745145031a025181d01005100411803d00d2040c10151506039009903805021162007d540d00d42d520240f9402d160410300003a0700c20b0140707400801c1d44401047c0211150101d688800204950440c100302c0f4103040240f0240d0540601c10b6010005103040c4408409844c0c8003500304225410b00c01800100e5045002c0351034141420810400b081003000000107100e68046481c65181070030522484d000c1c0e105900c000040c0c04048140085241141450046144429080d000d15503075040f040314030f00c031500141c80c0420004d0200740807240c41d035001420300b5003071011049141d03a030b210701160300103c41c00e9068030940c0000e800f02640d80e60023a00c18a040383c2c1291040449551054410481d0425a00c002c00c00061030303c410300c100802402c415485141c5009883d121202c900f04000e255000040c5001039528001520300082003403d90581079603010382d107450800000350307419a440c50207845104d4441c861a500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 764629595 1250 764628345 764628349
    0x10203090a0e18030a1d03100c0305071d06070209150d03020f161512150f0e0f01030803160e2205060102061911070c090207050d03092609 61
    0x7801e00074111240001224504a0341d840071804a065240d600f40d003003000b44101c41640315035014900d5176800c051100c119180341c0001d02d4241d44421190119007411100ca02403905a0b200390312500e460b440d102650110390b29690000d803406600743e68400424015003006d41061800700382d111040c9200c0c1103181c500d10000807081d05110108400681c440c02d246d281042062141050b40801d000508001500309120a1a4000c400308006c0c1004009512a021207480390004d900501d203001c2441040c80d02c585410107003036107a000381044900400042030341c000c1280c04450403203401445a500315156110304209107680b4141000800001000c0190700b03030398a0042411071020b502e007071b580c0004101d4018042c0e8000401840c190f4004600b0004414042800c861800558400003e084c440c80f00c1201714a006501d8003510488100c2004140c10909038000c1452600500c219041d10150036001c906545241c44020018001e0107903400310300383c0c0224607064410701680300314280804540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 764630845 1250 764629595 764629609
    0x1107050106061407030c020d21090614130308090310050906040212060615130b040f05090c16060c0302040905040303150f06090b0f040302120303040c0b041d0601020309 74
    0x10195100d955460301000803c1d04096514030f2802009041c0d070078012540c0b00902481c10001e0081c2c01104094186420070580700d0f180c00c0195810f0715120810058440c00410018050095402080d85004420002d10700304044e0345000340d11004881200d800c40c0c0d5804030640043c21350541520800001241081d09030007183e101c1c003083d400070304252504d07004009817100e0210890a964100c003051055503180e6030300919500c1240c2c5d60380c3ea560700c149005105100415804a007098101090201d0070f8560a12924200c90017243e880640d900c40c030b10429444e104801502003180d591802c5000014419000380c044201d0508006091503607a020300c0056540032035040f00002e55a040032a28502d140720200054182100110001401e2490203030207521370380115081e41c5804141c0940c1c861500c01250041d550140c0240d41d046103000403955640c10580d003c69030364440c00d002003004140f080c00d56007245c0f149081c0d60001c0c501140c1002c4900b84c090400c0341180000c0280350700c130307403240c070703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 764632095 1250 764630845 764630857
    0x40b030601061205061e10051b070305010e060c0409091a130620270d05070303020c011409010305130602030c0d1b1719110405100f08010b0a0311 64
    0x52900c212003118910034604a904c000e20842c459031404402c1000744c9410a0100c520790400e0f584070703c0300e9a0800c0c0986141c081e20341e81e40c40c02000802104812003012401c0b20840384104001d00c0741c1600f104580c0d49030182191040c1e03081005102c10000f61103150024905a4001d500f055002c0709800501e5180145c02c036000483c006940c0e11036010403015100309a01c440c030f034028610880c11b011681e902c2da4401e540144048100c00b900340da8950480303900032503072100010300000c0c1456081c42e0050302c2e00503920080d070142c020500031400d2540503559035030410700190755580c9440b914000660051801a2008041f0030810182000140b158402036003ea1942000c558550240041003402e590400341d001815548003410464117607000294180007405480587c007455444030700d58610307000745545c010112030401c000300300c130010224010320a0b03800c103485841c0e0407400c2490a480881c6801d106c540080c000e04010000803403500d015110340c00c580d18012440b203000440d034a04540040e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 764633345 1250 764632095 764632097
    0x40308120610080405031602041104030528020901050d1a0405010f0e0a0c1a0f0a050405040b120d0503090106080106080c01030510081903030b0613030c080a0c1202040b03060106 78
    0x4481030007072a01c1c004031034040c0c1031164580101c3d01d14040c0d88007900d074014400c495441d2a0007001d50700441d0b81300c0e00b106840d0314400c11120b4403550359040c142c4e69030b007107a40d500c0c0c080d54911040d03c0c5c2c4081404041121150064100c0d4140d034686030500c071410101e50b2050f1000400d0340b0402e5080a025274555020f81d000b100045241c0003c0d0341c00d48101d0307114a403803c29540c00025400002410b240f0041c1c210b861100c0c64141d14102042c009026104519504203508800210410020741110143c0140c440a540c100a200754000c1400400d00d5003210b4649550310402c2e00000701c1d0f00c110001c640c070135070040000c115503035610038a50a4070b0703890700415500d41002e0381c4001c440d40e1512480390b00c5421505d41d4504249441c640c00d44404a16103002500c0b03065060040c10b1600a801100e21450007500c0141d0381c800c4108010240640b030300084450035041d200020750340e01c0c00910043c0a0b07800c4500584460b240442503c1d400b41c00340300803600203031a0351307642240f6503040c041c0301c2c002c09203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 764634595 1250 764633345 764633377
    0x5100c02030f0c01021009080c031c180b0a0b0109050d0303050a050703091a100e0114150306030d0c050a0c0b04080d02030414010f11011a0f030a26040308 68
    0x10384109400e1221001a5519680c8030307040f4084260703400a41107150803221a00000c4c20000c2c0d0600d40c1c202d110705464001c0705e10001542034a5066000c15004000c902040f040060030402d0310b08001c20448190080e2501011201140c40b20f4150391040380700845c1410b04000d0f640ea04c00200e4440c1c619000242c0200c0c0e503400402030302814500a65501c221189410462900341c0c2e5aa50500700d42820040d21080b1810f0000300c00c410080c14200181a0a015024040d03940300e15680c400b81c01081d1181c09860f0030100c1001014003003007668069940123010f054080c100c140c0864241400d050255030074841e81030020041440e04045001400f0718400c429074607030a10389450718151194448608561080100f040744402c11594101c00b160246403800a400d030110040345ca96040313034920761403940390000e4010700e001c0c1603683e42c2170760400b0361300c04408000c04001c041e110320b410070001e04014908900d004034601c41e00101c404c404d805004c10350a00751a070f1140d03501c1c0e0f0000b031102d50450356 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 764635845 1250 764634595 764634617
    0xf0603060608010f0b0f010915090f09020c190b0117010906020708130b030112030815040f02090301150b0d0b01180609050901051914150706140c03220c0510 69
    0x1d064085c000c0190000c0d41c0a601002000000815408841c450721060050703141451400a228064210046c216201e280800c2a110160840294058100803103d4480c184403c851140b0301c42a00040641140001409030f207481030f400c01040d100c0c01214015543c03840070340c0015900388003030403411303000700142d070785a080c90050400b603141c40742c01407600c0a80510042281011148418240315450701c0d05002c5526610000c80710301888520842d071013402c2c088030703001e8140b643e4064078450504400900480318a00c0b10402d014000c0d006400540d0420805229500450b4209000800c418500612102c1800402c0c0840c101103402510004540c1e000801c0340b03140030a80349016100440302c414845540407000104d4411601c12010405410403911041c0d079903140b040000c00c0310030000ea50347c54015113020b8009120000c0e0071517511800c08082002d103540078058920035524004c2d062440c50f040100c5690361480301604a0f1543c200c20000700b59030b2240c0c9a117840c01582d035110b40f03040354 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 764637095 1250 764635845 764635871
    0x614010f03050a02042a02061f080c060c0316050106090c0815090403020705130b091b0d050a0f09050318030f0d0804051606050d0c030615030f060306060801 69
    0x40010303440341150311104101031020600120b4015a0164100c40000f00c0c1200e2074003901140344000d103071314a182170317a210b00d9000da500464420f2040003001441c0f01610304020801c081c2c01940d01a001c0c2990100c4c400c8d41c0d030340c14810005d29100103d80101c90804002c6500c2074491026608103c8035651101800c00032007581780110314102e030490800310124946100300c600701c0d241c282011446071400c0808141854001c0c451b03500a0710000d440b8040c40380d2048001b070050482000f41c90300800c000710010340b52001076480b14502010211240d860300e41801084005070201412515685036105100c2c80350b00041c0c450700c152030348240c01641c1c0b03c000540c110360554000198542c0207802ca01070041c403040b4003240390220301c042410b00303d943e925941001c500d04001d5454890300210044004140d280c0c00034007030501c4c4e280540e4244803c041d018400c0b03099842034031825a590203101e1803a048540203410082c0341a610400000d2303015a01c0e1039040c1658125840036502d40d54801c00c10a00c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 764638345 1250 764637095 764637131
    0x1a0c06090604020d06020d11030a0213150207060f0e100c0201032901030f090606080a05060711030f031302151b300d0c2f0a080904090c0306 62
    0xc40446030250100e80740c00d0300421498582030720010910340c0c0c00500701c2000d20165205a0b44a190745883c10746030318101c003210b03000303500c8844078030400210b502000070340c000b5141122184070240c0e400b5004891030a0400d9030b8001450300c0a50600c01020b82d0681c09803500e003507003109807003103554000715180030b80005011900403801c510604940d400500136030742401c14035045480420729000584100d5200b1600060500c1c0100412540c1400360001c1c610324000380c00c03010f03d4001c40c141c070f4058a81c0c420030380d000c0403a1001e400700d076001403100f04100f000880107550b2003607403105071660804581e4002003407400928004040a58041028403401142110307110035021030400801c0050716500d03c42c8840405040701c140d01d001c0a919140b081c1d859030007070311400fa080d00c030140f00061705140041d00044005c024070409480580c80c06250b01e90a0007485210107901e00500b41c240100d8603214625804100c0b0f0743e4003c2d44400b10540041c00c49903108000790b01a0100298803e002100d100354 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 764639595 1250 764638345 764638351
    0x60501050306070e0f03150c0403060e16150909140106020607170402041824050c030126011d1f05010501081306110a0f030f0c090e101a0c06 62
    0xc0e51214040243e41c80d08014000402d00d02221200921000c22000915041004d03000111000054041c400301032015405403041d070307100b80c0050040d070b801e4451241d601c82c03004000011401000000f04070511080a40c200e0000c01403600180c00b68403050780909481d0020942e40c6601580801003103000e0703040c0300e90f0b078002d4a03d14200904412203036049003113100103030003e48034aa4034140240314464140440c07854550240c14000304002c0107411008200c07a00f00b00728032a07814040010b01c9001c90900b02c038181c0f410f0340e00c0e01400c602520080c0c0c61581d0841040c0511b9942d031240348102510880e29101d610340035600070016401c2140d0300782200c44690316058011801c0200600040c0c2c0c0108400f80d011206a0100c00e10065600700040034100c288144061300000064802c00c82e60302100c0000c07101000e840a00c010b0a0f0480c1d014101d440c01c01a0310005035096000b440340c580007500700c9800c1420003880442c140d844000481071100310071401450920000ba503180b88100501403230794 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 764640845 1250 764639595 764639599
    0x6030f100510050708160c0e19060302210f01020c07471306030b090f0f2d010b0c100b150d020712030e1905030a08090a0b0903030406050105 62
    0x11031642c0c0848068020b00a1010041c00c40d080890300000041040c02102c1096030480741003519140c1d100351300340a0700410f40f40c0510740c154650007120311280501884041340c0e030103407030b1012414064600c208111801483d85a40f4000ca4111100223030090000d002e40c03010410281c018940f6100400b450122507045444e40c5210200c5c0721030f43d985400d10010180708100c80d0004401d2041c500b10b40702407089480c0500c1c244000d4038041a41d0781d1513170004401c04000e4600c4009612500c0f00000000030807107035440d02c801c032240020070398007403d0b6400c0102000701c14034010000800c0305015410000343c10544440d80045035000d0502003c101580345c41c00b0320f10040041100c85400720f0041103400d082d141201c900010b0740d009148a9a0407102443d40081400042c5242d91100030068032100784114a0b51180030351020302074110800e400c91441d80038000318609119504181c52000009200702c1441c040c942e2404c000c40c00201c01d5520a180c01005507a40c0e142c1031802104030391042c0c0002d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 764642095 1250 764640845 764640859
    0x702010b0d020f042f1c0e0a080a0e0307091a010c05060f0403050c0105190f020a0c021219060b01020613030210090c0f06050d0c14070b090102070206030f1005 70
    0x303405030302c0b42c03c0100400c507810381c0c001c2070607888568440f502c0c200c05a095100c1d04a1002203041d81d0b240c070070213031035060450404c68004226a5008505030344920380028040d802280d150000203040c840140380f0261107040000b51513078810700090a000c99a80090070f259101c1c0380c185200c0e005400c8813101107000b42003c0361000240e03250169265401041e0341a0b50240c007001c20706150140040d01c540c1e1014900038490783c85c2c000110f80351190008100c840b07041c14410341c000c1d0b013016402a43c24510007030b85c50110b42d00e0076408128160f80c00d00360036869805140c1403482444400f100c0305500324011500441d0392042480028500100105003200114691810900181e40851003013120100900f001c01d0190450600b40c41101155028030701d10800341400050791a00500a0040075024860410242c81c80c00000c1d01e002d0350028139008642e104010540000303007522001c94000c1c40240c00141006040d5000c20312907481514a07070003031100701c07040141440d04100b0309009410103403180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 764643345 1250 764642095 764642119
    0x60a05060309060a0e0129031005161803051507090902090d080a03060825090b100c03091208071401060e0703020a020f0d05070507080705030319260702010b 69
    0x520f8940d40054045034000c0d0700c403000d90341e26403000d401002665040c0c002c08206415403104030001c1d40e80d640e040034001e0042510320100121a841006d02c10000c0140c080d410540400303007100c40024090039440508480000440405c404000d101015585031701482d07940e00740802c02600803280342d88070984c194010486c16429440e25a9050310b41036102d50030310b45034a00060240c0c003400e10740e08503100c0b5220f05400703d16140c1c13000e12080c0d40a4500c0c0f9682c01d584d910348080d00107440941f00c015402c480806144003119220b0305090803498041e1600d40d401c59207648421b00c0d200503808042d01c4208010604c0d00c1070009100303000380e00c0ca02c44002008041d07d07000d0b940c441088014154014580d000c01d100000354005d00c0054200c02ca100c09441482c00d82001c050001d80003104285d0b440d100c0c039030713022a00d141c0c0041c0700810340c6c40060040d4140714800500c64032a90189840c941004030303413101c502e0060000401491801440205e0b010140b8210400a085071501c0320300e00d03c44c180c10a42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 764644595 1250 764643345 764643361
    0x1e03020304170c0d0209130219051e091506040e0f040c0602060709050f06360109030309050618030604050d03051b03150102070e0a021e0408031801140a0206060a050603 74
    0x4104015030648661460750f0b07c030302100346206070784107019400030240940440e032420740407400029620704848080c0f0b005910708501c03440f804019403071a00a10100c0120b1703810000000345e089030340d000416040c9455103c8800b0101c540701074510117001e03c201404d0004100307500814030050281403000b0b1000c2c0c58800c0004001031407070310a00b130107084401d810700303000c0c0c44007800ca80750411610b0041c0410801d1158010310704501c1500300c0c40095080041502543c8110100c200f00c07a0169034074601103041030100300d85d40e402584442c1500080c603162000d2614203104962155014001400c054180a1030140603607c000300314032420b4a18020f0603150600b4003056a400c0240103695459081c210340041c0c2c50308040c0e40200c070382440080104044055250003d0a13544a4507140000001d5204180b140034003590003034600a410900c042c001c540034019503645810014940820721000c00e580280b001d81c0003445a2006810020402500c2d04014480c00005c14064038440d2442c58407101c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 764645845 1250 764644595 764644609
    0x90d030c170c031902190b0a06150f0302030c090a0e06010906320903030f0315100c0f05011e20070804360504021002060c090d1e03020304170c 63
    0x201090101403100041c0130b0030303132007008101649404200031151565142c24010641002125030504240c24500c1c0464180200512155581019141c13411411441c44056003c0e410040c040c42410380f060040b0b880903036890302c0100040580805500240c10301c074000400c0310300c003034001744103010030107450714102240e201da641c800b20071511410201d80c042c1c6280040b14440c004907075038188800300c2c140c0e80448003000214000c09002c14280403041c1804140f280421505a510010402d06c03000c0601050300d4000c041c4049210b50b0000480c0c1e5007906501040c1c0d04010362070034034079554039100d82681c003692a00b403441c5820001114208640da6807107422500c142e001d20083c2c1c24180c44038410164800710441503400c0c2c03600c3d02e04244ea03004800c101c0186412a4181d1140000040400b0381c01d00202e801d50003000e00c0d03d1506c2c502911003061086074102c00030129090540c640300304017810140601242400d03c25806103a841c1e00c0c0c2500d030a40304640450014103608444105810799075805 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 764647095 1250 764645845 764645857
    0x3060408090f040b03060c1605121308070503030f030406090501141503060105130c11070308070308011d150a031401140c0307080703152402210f0d02090d030c170c03 73
    0x2c0005580c0c6e06188440141e144402c0c14002c9c01c1c0e01c59070002c01003000c0c20401a144010b410444510714075901c3d0845542c564683c4221500358104200802a110351a801194000c1c020382d0080358000540e0344d59400c403504003801c11910201c9406000d01b9003190801801e5410f811001403056506200c0000d4040c0209141c0c0100ca5a9030740880d04007034000c100703100d40e8529100681e840030365a41808403055101c40021000548100008140c1c4800c89401070040d81e143c9107100c0c140d0741c5180a000b00c2641e40280700b40c0c005089480080003800034803c5200c220040f10000c501c200b8103228a401003c07005c1c4c41c00030290710900c200300b000c40d80480c100b5440343c0940350214044402c41e4055a119490b0740100212110041030920242513100101c41600001e6080312150a0b206404e81240e410700c03584820703c0301c0c00700441500327000341c14060b009584042c1001450030702800c00227844d0444001d4120302080c03240c0c01540922814640e0304c4201420031217a01c2ca001c03441c00085032a44511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 764648345 1250 764647095 764647111
    0x9110a08030d09051606050c06160503190b040c0512010b0405010c03180b1b0c0f0a0e040204020f0c0f010c0e01090905070c0203030a120e010c0905011d03060408090f040b0306 77
    0xe2800e01c0c0c24000d0400c4400c00c4a110030650178889516a04010595803105145070094411800810980d0030010304000011034203540f440d0660715408104603603000100e440e45d40c0a9150840340c01941da8500c41c9030300c041c1c0c044e114981c1c0e071980a0341c01c0b078842c00e0507031110640030024001004240d8010790032150b40e56040c5001c54003401004a041d2040f030035500050721085005c100480c005079061420745894000d1400c640c0c001440c0340070021f61511488820750070240e00381c0d08004000e064800260040c0c80108058201010020340d010399802020214000b58040142c0c090150000c1c071441050176403610303046400b8108200041c1688400380304590000b80e0342c400264009115442d41160140d006054999440000d000280744540d00004203400c58940b5100c8104054148030f8001c0c41d0f2025180c84140500d040010748200d00360349000344078001e84003140301140c0da041c880c2c035100300d21030701880340c0741d81480007441800b0300c620364020f008600c3e09072624000c0c6e800040440d441101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 764649595 1250 764648345 764648351
    0x1140d051c142b0608010606050d0b0916230c010617030906031305150c0415091d062b030801060e0307030818060705010c0206100f0509151309110a08030d 68
    0xf81c0e032001c008103200d9108280c15440c0240118200d90b1100003031208544a082c00e01800c425101000b80056040d0b0b018a59100100542e816142c02012210039034015000c0c03054640c00035105c6d1080940c004c040d174610995444030306010f201e10a00c0b8040c008940040114201482c00380400d0442c4070180462418602998000b01044010040c0c001c20607403c0705d218449013002c540b5140d00380c000e13016105031208105602d4812510803a0380300304031070380032880c910003c10b00503003404081c001501c156040015138070036010001c04807800d035546003120b0750018008000750500820807641071700040100300400380240c3c0315517000124541520381003402540c2d2641d062002b800c000345402c0d407075500035001142060a10406512110115056800b51100ca40c0da80140c8030b80300e14035001c0c040c103c640074281071100b4149199501e501c440c601a070406081c80c80030010703035041c0c05a114104076540345d000a204003d2084411124407400f0b45003481082e051658607a02c0380504001c400020755 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 764650845 1250 764649595 764649667
    0x801030f0c0810050f06010c11090a090b071101060e01030201020d0f05041e09060806041e0218090c0411090607020f040902100f0f1701140d051c14 65
    0x18656041c0005101500c100c564201d080b480d4440038040481d148a0004a01c1e000290254015a403170422240c0c0040d500d4407030300c401c03001c10030a20b4014100b2150503a80d615010005100c440ca41c2d402100c8544404580f81c0200b2045401e540c5150490070740004190010070050341c00150b0110000c140c0d00b0901d143d10341e94001201e80340507540c01003416102e44021240300740b49400d0701c00305a4650710014051251209102c40c1d6a510a940080000d03180408402c6103188002500203c948010300b400510b4101141d18030240b0300c02d03940b0650f07d030080680c01981d450b0034800d450301c09921030000c60901c802c02c1c0002c3d1090052800c040c0c02070203103070482000355803075074050240141d005001845003500250001e01340c0903448070f45004034812000003045140550107881c0245004d202410030340c5c0c205041d4075503008202c09207640010b078030844040041c2040c4030880c100441504d002480d48810f40c0010300e074507161090310710014030070080030241d11824039000c030401c2c80700040080180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 764652095 1250 764650845 764650853
    0xc06040b030a061520280501050f0103172b0b011106060102030a0e0310020d06060207170601150309050a0605090c0103060f171203091f021c0b01051605030d06060f0801030f 76
    0x206c5240d4019002c442c8450055a030b02c60429440140075000380020480380d519001d030080004001c2c00040e21200d5107003408090a03c484c40101540d503079180c0c45040031350b18103104403408458803088480050b21060310f130181c3d50b4022450b9240300d0403040145043e0a202001070340300c1c410b1004000801100307601c5403001c1d450405c410a8a000304240440d50f9170642103000d001010b150040500500a448000070010036070840c0d914040034460161040c1e13480c02e2043c0c1d41115a840415040c15200d00c40b0002151050040d54401406454003280501d418080b2a00304482200790741e060500e4901e0038400e071820784021605640c1071a201c001c007258600040ca00e400e100c0504030350001d50000410135491400b02d03c0124102c800b041400c141c085807028041179004124902400021503046034500f1400350304101c54165040c1092480c140e003508001d034002040c400140c91940c00024114285a031620400340202580c0c50071a1a541c09980f00404021040c800a4a5000807401501c140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 764653345 1250 764652095 764652103
    0x315090709030212060103030828050402210703230613020f0a0305070f090b01211112010e0c070f080901090b0315310e0c06040b030a061520 62
    0x550303002001c241300344144492031a91003109002c2140015404004100680c00b41c0c80d01c0002c6088682801e0a49480d5140d842e00812006105907440350700c06100060b800b1094040304440e041d00b1003e45041400c504101c00b001440010190034102100550002900e01148454110722601c600c080d11000f140002007815810b054415404110104004200301c00061030784200c4188580f42d50b0f416a44000500407280c64020490120315580c50300051010f40d598400301c0e000c2040c40000c0c0d0010f80703c64980103030300302c0c0031080064641031005020010381c40500d9984201149503031483c051309540c1c2c0b41e8540d600b03074500a041c01004607104601e680150390290260080b4111140c40340350202030a4403002510342800d005450030120902c8420600c032a2061021104d15080304d0402c1c0960007100a1920301c4503c8042e01800e100c420f43ea580d000020001807107841e03ca142c40c0d00b0540c03110802c960459001030310791150070700100310241c4c118400c400642c860800003004800c10020319410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 764654595 1250 764653345 764653349
    0x1419020d0902190906080307032f030406050702030c06040b0433080610030504051c0905031212010e0103030e060307110703230f03030a0207020a0f27020315090709 72
    0x3c000394200d003040f85540054009811909103090a20150b603940a0b03164907407195600c09400507034019919812012111843c480b00454440a1080d48100c4c8064070305642143c1c105000040002036440e096107010001007d41120403120945001d1070702104c00518400c6100d9400e0003031024046500c0040c0c1d01100503c5030b00d1110042a60100042b0000c1a152040300d0442c0300c0c2d400d00540c0c603415403082c4510b510a07540140140840805086a4815042c0a41c0d500e010000d0706440840d207920188000058141e020906588031903100e2a00c4115a405070010004482040010804079a02403644032040c042a10066036a440e000e404941ca0088041c454116116148002082086600d5012800381d121881d90303171105585200a502c1d50f440032003584141d4000c1c40400d90160350382c0e00601d0f80c5840144080d100640c5c2e0704000d00407204503884199600480101003081020a8001d042e03d86004d020451840c600034400964a0020782c078501e0191030b040e4001540c8030300a20304080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 764655845 1250 764654595 764654599
    0xa15110c15071205010f031502070b011a1c020d06082107030917060601120c1d041d03090f010504030302030a120f02300f040803070306091d011419020d0902 69
    0x130b960312034060b00c000d40745911040b10101038008681607803a1146c4281e8091561159424030725919001005146240904c0c1081242c1c0c02041140c400b00180445c441550407110805622590590801002c4650b55484a02c194001e09444801e61044503c05440034580c03814103a101c100a0804603003502c8190007600480d010995445845240003e085200e20800d9880c54070080d950441103099580b076400c420b021503101c401c90340780e08100341e01c40c7c22045806800002e40c0c0d20344005da07a4041d0010f50701602182c20001e01301c100e0341448502c07607001550a082035490726240d507038002c0d41c07441a90145010005a0061444201da42d900044d040b5041141c065499001c0c0000c0c1c3c01e004811001d8a00c104440d501104142c1c1001b0a11071b40310700340d4000c0324405903803036403a16806a0f000a0154041564400c008540a015031090503040501d00760090b0044414448070b90171100d1510a41081c58080b4040040103281d900d00c130008411000800b60300c41c00c3d95003d0130041c04403040029 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 764657095 1250 764655845 764655851
    0x315020f041d15062506090b1608010315090c030203030f090103050912040303122d0f050f241806090703021e030402120a15110c150712 60
    0x99124002a00b09151100c62100c0d0700321910350304040007030305a40c140c116800980034040d40c16120240e28018000329500c6407003a09180803652008115400401c0807210003822500b8882c4107461412048100446420582280e50541c1c8035987c4040740350103a81c0c1d6090b151603007242081003030100c10005641c06821030783c40e00e403813034030f00d0645410201c41036000a103030100142c112000058000700c401005c40d20780c0d141604640707080300c00c010317840d0701c1d291002e480c0d107045824904180e150780c022542e000052000d10320317440c0c44041030340c1290380610403241c1084244402c81c00c0d071203d00c5130031040f403c00c0b2054640702508004901080350309042e42c04280a820381c0f4200c44050301940c401e0340101d469402c0341d9540c0c1c005a00701e01440c2039031200d28030031084c0a28403044110045822500041c10040129003c2c054986048540c1d07400711a030118042e0b00002041d030070300034410303410715030392895017803000c1c4d0401e240c0d5649014000c1e401c14140c04011802043c010314a040e03440010040078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 764658345 1250 764657095 764657099
    0xf010e0612060f01090b061602011808071d0a090b060f010909050a020307090e1308030c0c0102030405100e0718050a020909130209060402180d1103011a0a1e0315020f04 74
    0x10a10410f400d00c54041d03420704207040d45610b031a1000848031550a50109502c0c40c08a0780c00441e14400b100080c43e40c94181410081101c3d20108450f1000341040c08800d5406c40302d501d01d170300b0103840c0640542ea5041c00d100c8200000b4810380e2a03d9030046083d24043d82e10000034004a0340d107006548030070003e0b4908010b201c4142603540081d4842d20481e110060150b50381c007241c007260744046450750003106c0300c00b180f0702c0041e8100004681101591070007a040c0005940303400c0c2207070300546049490750301c0700001c1000481c04d07004801c00312003400040c0070614034007855100094648240443c50720358030000541f1007100d6038142c401c50000900f14491515101010340d46040400c04164820300314a00080e20328902030085404840303101c00e0048000d20900705014007a88090021913005500210080c0c180e2004d2062098541c0d0030807607545c01c00900001e00c00b05000701e800c42041013101e10b001401100c440061501100e1b03002d800c3c0143c0d02105910030009000380c00a2081c0d1070340000b80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 764659595 1250 764658345 764658361
    0x9060c010e06060909120c0c060c0a0201171006120e0d0930240c0c0615320d03050a030c300f05040f0c06080f010e061206 54
    0x44209164110340c110b4925403038075020004149801c40740c0701c42030b034002d00c40d4084003030290b0041c1c002e20300200e00715040300c1d000c10f0000f03149420003086004c40394460b000000943da4002003802102d80d00900b6200141030007011041d1003142d0b80200c038240000e60641401c1c00e919036001800390701452050ba05268110480206050788070b125001e6102c1d03150081c9269810355040c41c4132003204400510340d141d4425624400d0400000c0070110360542c0240104044c0002c0f4000e0409040c3c40340e852007500c12840c80c044088404c00100c1c91500080480c0c1400a1001c0c00301c04002864000c002c0780d04415210b680c0900c008427554601e0b003056010010303000701500000905001c40141c1c409025a01a11030100d807508061210140c3c1c4400424015603500f403050340302609039042d45408180084070040100a9403002e480850341a0103060580c4103101000c241400900390310f1501e004c03d418280e0341d03204901c0e81070044007100042e510106032166149251038081002c181d00f44c400302d02c0c0003d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 764660845 1250 764659595 764659601
    0xc0206040e04032a030c060914030409060b0c060103170403060c1e03090f020603100902030405070906060807090308090a08060403090f15120507050408031b010b010915030c0509060c01 81
    0x40450210701c040038440054240f40c10394007182d10000203032500c1c1302d010380c0303003150741041040c1c040c0c544036559a40c10317011a10340e607545184600c0c0000119511881d1400d050101d49003a40702e5440c4040074004600501c0300071481504503038206040e41c103680304e4629180801c2c45076600042843c0d10b03200c0020308032600440d15601481545081d44c0032000c00c1007040d0281c980c1c0f100d004001028943d821001031034000701450f004080c00140c60720454aa000c003808a90007501c0986d0580e101d014100004c00140c000c0e00040c01d424a403580250406c40e070003074014182400001e00d0b0384000f1400403e69201c40c2020170040180388200e440030304003418003030f150105a01443d14420014080440d0f4520911800103816a90380c0c0c9800030710013041c4502c0d00511024045008000c402c200001e9100c1040018207101d244100412200e1000c01c0405401c517080c07501a1410701c070380c4034410020400c04c02044061031000d03003004100d00c1d000b0303c41100d80f0700c00e0949140c1d00610104024031180350542c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 764662095 1250 764660845 764660851
    0x120f0a060911181306060f06050c2b030f0b0a180e07060f0e120a050d12051306050406090204051f0519170c0a14032116030c0206040e 59
    0xc4460310821102400f0201e011108000c2140a602c40841c615281d080507030b042d140d01485002907610b49800c421029820194010400102c0c0890510110102882207000f1101c50b044500503186030750803102c1503080b00030300000c11f1603a540030002e1604945d8000054602c0020840407005d5114030ba100c15003103501c00b00307020b21854a00c06401004000681c002641c240e92100707200044072203c200c1c1c040544c20002a0050304c03004085c2c032405808c000001050b4400c0020744107264100d28000c2c4081e0a02c2e20a042040c106010b010407840031882880c5a0b9400450101e015592802d122001d0041d02c0b400941003841d00d001c00041480b400515044141d0001406c220603a503682048003070007900146065165600300104440382c2c1c06500740c08074803041002ea0b074024252000181e0303401d48550000c0040312404c003c20a4a2070140801940c03610a003c20f01d002142c01c801a0250f802811066000100c9a862100515002d44142000a98002e00b05551561141c0714858000415 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 764663345 1250 764662095 764662103
    0x17090f011515020105010602100b03070b030c0919060e2b0507050f0411030109090c0305010212010608070813060507020a050106090b03060c0c0d05180910080708010903050405120f0a0609 82
    0x340382c4100c05144180906070480d03007145d00a0510301d58509400c00103007001d0075141da240c17203124000280c0d49207000186100e83c10a1801a071994421418045080003821244000e0303c4203600074058141c21130301981c00385d8001d540305425036401c00d0061100c10351041e55089101840b002200400400042404c2690700aa800c28400003100c010b0000b518131901042130500350900040c44601100c0e4001c1200b5401000000701950341c9803100750880e80000b1940f50b010070200c0040c810640c0098646411802900d4003201e41d142400e1910342c840601880140301c02e8466001c100564802c22220720b005401c500200b102556840c440d0303005101c070180b481e02038021b4100288111240f01d0035201c01c04e407107002602c403080c2e071008115201c0d4433035030751a46c1c1d05520380804001604d50011061280c000302a0b1301d500306017480c445614082c6030783d11280c05a81030000700030000ba40001550100d034026141482c0150354a805941484075054000180b8400d48640c04103020702030b0031000742d080c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 764664595 1250 764663345 764663369
    0x7120204080f0a05010f0e10020901020120070606060e0d02280f15050a05121b36030307060b062b0b0a06171e09070e090303060117090f0115 62
    0x9621b40802c4c0c0b000c5290807849600004401c0048200c607800170021400f051000203680b40350003610440809141c01d00c428800d4000c911034080002610945e80a0011410f000111075214400298a0641e40000070301a456001d1080360010b840c2c00c20911181c0d00080701c1c1221511591030608045051061000c4200c400c042e040b0214014821034000c49016903d841c03034044c9401c80c0f400d1180000e00700880d242c01094205000d44014405441400c5041030311052401e0078000110108d880c920354140d0703241c42d01d2503591803a41c00004403204694000004a80c180750074000503058020001480451810148019668801d5261070500c2c100780340c10401040c1010814441810601c1c05890082110f0311258005550000344080d8040300412460302c0303a07c00b40d003121910140540340300290768091304046c40400c8500700d1752a801204000214214900800020031204001140710a10303200c010200c2e514100a01c120300c024004140203210b858408003105050120520a800b64010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 764665845 1250 764664595 764664611
    0xf06080d020714090105012006130302060603120409180b04031707140708030c090307140a0608090316050a050607020c0f06070b0f071211070c05090403020607120204080f0a0501 78
    0x140f0640c03425280007000d07020b6440742c0e00b494015200d042000d02a0301e58255408001d800019007005254030410723161070b80030084040707841d000c1d02e845000b602040c8641c1090910502c83d103400005d80d0215083c40c200815040d550410500c1d002750803136409044000c1d0b107010401855000030764a8440c80d4145640901c03540c500c082100c44d91540c250200c1c400c1700410501000c108400d000d5130304000c00d0b5200918000c41e080010b40b900e130196001d400002c1d040c145144803468007041107402040d6a00b4000c116140080c0c2d010f8072442102d003002d00d0b00983d4082c850078000e04011030080c15a0180854403582405100650b485a0745014a80704090341030003480740c1c1c1406015100c51903800b915401b129120995400c2039054010480400c10600c1c400c01c029101d51406008030020f19151400d5072681e070f07401e04401d6103000c1d410141c000c0944405100000380d0014201d03038421080d151464681c4140c030f01d00c20291049901c00c0b07010f440b4007500200c80110101d289070005200d840208440c1c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 764667095 1250 764665845 764665859
    0x8190506070807020a0b041a0f0a05010911160503040b0f12061f0c110402180a1a0307030c09030c060e010e120a08090315070507110910050d060f06080d0207 69
    0x940112580f00060300541d45100010701d9043c10203402034481d41d10a808102c0350001c00001900440700e40f00c0b03051080051001c4010188241130240c40c0c290401d0203501c840203240c1c3c45911071045094101c001e500411340602c08207000f65070103081056046039403201c01205c070194a801c001600c40080324000085400c81ca006041c03150040074100d2040e2044201c1e01d07060380d190035414010f64490b04550140102d0390341c1d603c0140f00c0818280000c0324591407200c184103003450142c206101401c01d0a5600280b0010389054a0307110071070740342c08903504142c80300c125642407055100070200760303ca52000c541a0342141c00d150b200e14080c1d0726400e81130407500821011000c1144c8180c00381d0406007501c008200c0140042885080c090111050944042c8174166000300899208000072004a680400c20620364401d1040310002c564800c86402c0200510015a140e48070342485410840e00c030404000554000c2034602c40c50a9003001302980d01c641c121b4681604610040c014021894081044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 764668345 1250 764667095 764667107
    0x61a07060b0a1802071109070c0303050c0301030b0c0d0204050301110301150801030c0923100602120307021519090804060e03060114010f051e07020406080c1e04060819050607 77
    0x114200d01c8a0f0341c0c041888002c203c025800300d6001d640d0b0382c060003490300711a1540120140100031541c0c0d021a51811410014210340e0044c291004401003000100049096030100a030000c108090a55a4201200d107040c001d12981d031103150103500700180d00340705800440c0030398100c8044081001110100c0d06085644000074000200901e040050038484480a9031000d07000e25404941030701038900030410001c1400084403184004841c1c40400c0c0315003076040c0039010600320074040050841c02c000201a4030741c8201d02c0c00320750301c200e00ca000a000d45050406560640c4038a4820054900e49040c1401590310030700510b4040740f0f104610230064140012800d0495107500b03503000500040c00011600c0c0310300c0b80c00920420100303008000510030270041c062151b81026190a03034030421403041c80250f803002d501a074001d4000032204803071901c0d11440d600403a0000301d07a0300741c1c10800310001002000b070354120720003600c100700503564203052800c1809507142c003a00c00c48100b580c0d4001c080b551 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 764669595 1250 764668345 764668349
    0x110d0c0807142706030c0406031101140f0406140f12060f0a0311090a0e0f100b01110c010c170f04090e030406021e07050d05010b0906120c090a061a07060b0a 69
    0x72240140d61400c11110010500981144e4000c0c140c80050281d031000500365a0141c0054414403154003500301c40d5130f082400545400c004484160408107102c0d17122105000e18495081070181e828a03004281d4032400c12501c80c044070b1000719880340d0114000350041d007811510385000da00340001c100304a260600740c1b501100c0d030080b42080c100a001080c08107500000d404200c0c40d6031945020302d5901000d21801f002c1840500007445080c00402004087d603002010840c103000e00801003011301d01c004501d010460400b030800c64081c081c2c80ca4104050039108091800180004ca44880d03080d5080d001401101c1c50043c0c00d1103200c005448540d183e104a106100140c0d0180420300c040395114241082c04100c8a01640e40303083e5242c020404031204000c0c02c07110750b50b45020b03444c282d1030303c1d514290b0045ca059880306401310030340c08055070724141c1100c0c0034401c804003400110406c0243e0050406070030640d19004403103e01500e1040f45070004441121007070306108154009040600ca0902 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 764670845 1250 764669595 764669629
    0xb03030c2808070318090b0f1e042d0c1b050f01060e0f0f01260c120708100b060a03020a050c07142407110d0c080714 52
    0x105103103062a18090000814030440e0300c40e503500904002c030702c9100207018050300075210200704120710f0940d0103411415400905444c0d150003030011864036449840d000505080d65180f114001c9040b0594810351280700050b032043c1014001c0c9102031101c5907070b014603884021a0a00d0203420b01c035540c142d5545000320000582030b004050f580701082598000390758083c00603961981349103c0c1301d070700f940e00d26046148104600e0040c8544015210b0a2640c031100f5502c4580803941001d40300c00e1000d0006101c0f03000801c1c101c11400e943c0d0800d1050088100d4010180801240c800d454217446400a105806450060315803041603180c03613008410b0b083c54020040c80c68881718070016002500030b10f01c0582000030038000311010000c10440300018124882c4591f581e0008076041080700e04036003c204070340d1107160100d001c41c00c10070829503210550001d805810000c000c80406e44002e0101c60141c40e04014500c0001d0101d070100c1c5a07010ba030a600200740e99000020300340304c24111955a041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 764672095 1250 764670845 764670853
    0xf181806080102121609170303011a0a020d0f05040807031406070219020d0804090f06031209030807020d020d050d08040c0603181b0503030d02040e1b0d090201021903020f010b03030c 80
    0x2601c44425401c1188850150f061180c0e002d92520641f01090070382c1d4035640481e03407000006105803003140f218412021b08842e145890170342195002511200d0107082001440300000d00609818050010356024001c8042101d40075079880c2400d680800c3c1880100d00b80d400b801d00802c1482c0d03c08503d8072141000c800c414101401d9030740c2403190398100d007841515003110910010034491002d018818030300c80c41020110300c0324254200701c82c403540e1001c0140f0a01903184400c00c0001c814805559046404a902e00d144240c1e50022401e0301c0180c00e00200107002d0948243c0300a80c0040070345001c4c900520040d480d0315207a60055007200d00401e00402d0b0301c818408500001a51100303100c0034030010600d240309641c1e9503c0442c0c034541103800781820751070300402d040c00f041d1206101281d10003001c081c08054005202c0012040e0300c200140113001c40d4031031600c00150390080003507900b084503241c41c01d0010b6a2500340252a410303600c1e94945194200046a50b0303610f800410781d806010200f004d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 764673345 1250 764672095 764672101
    0xa0c09060e0114010c0b0112020f1207050d02040f020307120e2e14090a140c0906060703050405090a3c020901020a0c06080115020703030f0f18180608010212 69
    0x420008150b030781c80c1810080c4411050380010906d1680c1c3d4001c0c0032075000512008070520410210b4a0444a07407402240c41c1003800402000001e0f040049030416a0b40342036049030740c00854007a00c4c0300e035950344c2c80038000404d103c2c007941d20004445554010210801c01d103180800044d4480d94031003038003201c41f0708060340c1982403c0c440780c40c44440c0c1d020340000142a03481d0b1000c0e11080f00c0443d0002c0568000c5c0102d8414403c0c40b94461200f400b408000d01501d156240006803d401c3c0504500d000700350102c1c621080600038422900980401030049413140781c0010040c2c0600302c0d51140c8621003904200c0d10740c0004d441c00200e422740109036564a6151100c40740940290400028981184105160301000c101650400720262401e0355510803203604100c80e850000c100003450104560101c00c08002080e4814195503180b001d5291a40d007640903060300316400c494000442400e040e6542000903d0b0121034000001148100d02c1031200301e41e15403e05081b4040c0000403a030490341c030000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 764674595 1250 764673345 764673359
    0x901090b070806010c050106090e010c02150c0304080f0301180b0f03060106050904020d051305012f0a030f02030711011104061e11030c0705150f1b010216050a0c09060e01 75
    0x45607030101e010316214030703241c145e5218a8252000d5500c984031896440742c0303068040030280a0840b2540aa000420112400b440007009100c40107000072406a0044045820001000116a0b690038403808868883d6140c0140c400c000d40e4460301e01020354a00040f01811742041c1c08080a109002405002203030b1130031800340c0f0954800300021386d01a0b401c00c02e8031441c1800e44106806261601030a15a900399450480d08580104082c10203104034000d0041107030b6074070b0268102c6489090640c6440c0c00350050142c2c0540300503072011003005d00110410071542e174040f032618111804030000380f03c40c03900402c0100451065000365000906040314152801d410381ca1100315081c40c42ca001c1c400d080b80000000c0c2503410800300049a030700310442c200458502004448855502c44881d6032410b10030f100d0210751341c824403004121a06a00440c00e8150380b00b0b6043d180c11500d18070f820300c400c040074540a80c8905112004940009c0000008229100345101d1402501d40d41518020301d40d0030701007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 764675845 1250 764674595 764674607
    0x150608041a09011806050415110403150906240b0c0c01030207170301030f050705100c060f110c0322060c0201050c121c0c020a020105180102071e0e0901090b07 70
    0x80b81821541d00c400a4841401d000718032a07113003a005000004150078540f90109070b12040c81000f003401401c0200c900000300414089904480c1e00204c04040000c001c004040036003181c40010305958074000400104010a0340e0107440b02c540d107900500142c0c1c45a01708072070340c06010980d4100380e00501c0d00c4600d07940680d004080d200d0041d1900c5070020f802d0804017600750300903041251090010900e80b01040000c0155602401040302e803c403c015001c4801041e00e414082c1c00392030542c4a5540d034200c1c040b20f40c844005150351910301c1d540c07000c0103151980c1e03a5003c3e00c4100c3d00030b01c640020300e031403040e42060b00301600c03120f545c0d041256403550011145a0421082511540140b090364140740700304c20010164141c41c3d40c100035605002c11002c0b0b044418a410f4402503420000c54040141e80c450100c8034806124043c10a0a10498004030701c2c000c004d410004040130f500d010046100401009001107540015004070a9a80d2000c028240d84100e83c0050030900710202003400c0c82c0c000c40b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 764677095 1250 764675845 764675851
    0x612021314061504030c0b070519050d140904060303021c031a2403070f09060302130302150705010f090c08120f09040f09030903020406060302040b1b0309100201150608041a 76
    0x100200742416100c0d2214030006c80107500011484c140011769004200c1e0500850482103598031801200490544034191604803054506042050342010780d408440048207440e2400c801410810103d61a454041e503a468040d04a43c1c248404800c00f07030069201e4018030080031000050020440403210a00200486000c03034401040d68148000c03817000b40c0d49000d140300e5a03469580b501064240c00010300013032100c0d00040105030041200503001480d000c038140499a050312100180b0300d58000082d014080c4002c020095401c200ca4401304152541140d400107001780014107102da03540b03564564850305110302c0c2e03a00060074000403075452254005028210005400400e00c9100340000302d04480c3e00a000314080307a03010f001403081d4282840740c18040d10703550404600d803502700305a03d030403406201d580341001c0508010a882c84001072098801041010b41002d00700030b05540040e000e00b00910030f452198507603070b000041592103250700c80d003e90f4000070100070407800107043c41820a001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 764678345 1250 764677095 764677129
    0x21060f17070e2a03130f06060f0906151b0803150a181406031e010605090408040e070e0a050906030c10020d081014060319061202131406 60
    0x20140002e201150340d400039100b00c1c0c0a86115420018050080c000c656808010f8001c841d000e0003045000e1010360043c2d07030b41c5038100e8844103104195103000406011541c05c084042c01c1004000203c205d015001402034560b14181002c01220b00380c021500d90142c003400c0d13144810602c845501045d126130095800a1040310b03000e061044d0392001c6080b100080d800304604ac0313900d55003601c100c5964072a8004c2072421403451075041c144803000980d0782140c1031721281c034403200d255038010750701003580f1200003010090015011882c05007400c0c1000d410900c030303003150716080d8000540c2c40361103008a03849042005040c4800c2601b05000e01402c0c0f00010007944c0c0501c10301805000c00c1d81c13103005140007850254010315201d0303800440106910320280070601c3c5500c070316800740441d007c4d150701b420003118240e80298890741c840c5032800c40103c8814290b1059450300300d001c20400804008500028004c0d100c1000100b465201041143c102444000e08440c07032102044003403400d014071152222038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 764679595 1250 764678345 764678353
    0x1b01080105150c0a14011d060601120b03062d013002120c04140405070e09070f08060105012604061d07080105060108010f030c05010f03091221060f17 66
    0x28114124540701001c1000c0d2804151703540c04a0915109001d4140013a10040100c0040000860125501c410182000e4140944511041001c04a41c0d008081c0032100408558180c10541c144c1100402460988500c070140c40c03107650310f20001d000f00309049440d04011403c2580c90742d0000882d40c5001c4643c50720000440c1c500e5000b50340c40c5142d150460404e0310140c002c0000000130070080b42c03820300c6808011400c1004000214401007845400c0f5032182440002a9403812400303420018a504510480c001100c00030500710800113119050341c0082c0c03145800d0481100303946060104442d04113815607a800300203000203045d40c206070441c0c0400d102400c06001002006424201550008061695a0420800c5542c3d115240038010906603501c144030798155142c80c44000500e0083c14140b081c3ca000c0d02001c184203074400c1c2e61044e00b002d10004480400e45000b4006082d001900312018000c20030b15030f8101c59842504103ca00b41144400d2407481e00c4032500618000403240016030003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 764680845 1250 764679595 764679607
    0xf01060c15020a0909180305030402040203090a120c06110c0309013e010c2a0c090606031a03010c020d1202040e040503072d080c0a0c060e031b0108010515 68
    0xa07080c00a04100002034441281ea1810700d285202259004031070010401c4180c4440c40100360401c040301c0d0056015100540d0721f59440c06550300d003078090200107154a918a0b8450603a507808010240d54520a01c2c0512286140c5464443d081c020071550a203160400c1004840d40c0d03010302510b030309400740000c09044c80310021400a14800440807000c85041604035002c21065007031080b168180c9071404d104884190a8884d1107030084800c1d40d48076145501401c8605001e1104000340040c880310703205120a03910b0318002005802c0b00c2e0220030002c0c2600d05405002e28060140c900365245980c0200b035034030b40001e000c44000089441c0c00d0142a800c010100c2c2000c2809011403150b4014001140c1d103113504d141c405007245030040007900c0d008107024986520114400a00d1036a42c00015107a140e4a07154415400e001c0b0703802c0300070302046020000140c001c0e080030790703607442c50720480c1610046028154880c1100c801d82141900069602c4014052440c181c00344041c40c103c0c011045007001d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 764682095 1250 764680845 764680883
    0x21003150509010f090e3702030303041202480a0f05030d110706120e07080c100c080901030504050a050a06020301170c13051e01030c031a0f01060c 65
    0x301082e0080c06142d08000b8081c411780720240200070071200340c20000c0292403107110a444d0800810141c0b040710b503507640003d02182070708030030640d01d082d001000e50b43d990502e407070a4401e04492180c5075016005884500040005600640300411445400c804110744841c05404030401442082401400d4480001c800344c1ca4214242021b440f003948620042c600340800c0528040c1c2d15105c0e10b040111417080b07003402c2000441c40104840450600c4411403280d03c4480d401b83c1202800e520b66446148030014070404001410384403041c5c151802880d00704081d04c116003c580b1400c018141050409c548034155109500c40d036407090080c0d041d039840c000c441c0d03903c030f05150b8920001d1700c0c000c0d000300c01408581b0342d0b10800701803202c0b24001090121151004030300c00642000704440f0b02c603a40c00010304402100000c1c00c045200440034100250b84a03c3c042c800613040740404e880c405070fa0300424510240c0d010406000740c2c484001280141e1900c201103e0411102e43c003110301454a40d8400d000b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 764683345 1250 764682095 764682109
    0x1103010306020c160f090c17040c1a161202120307121104051e010311070507150c020916030207240c05040510030e03041a07031101090210031505 64
    0x6144a00740c0980d648248911080c64461030041040c82050182c40030025000552045001c03030b40c08000c003003001c0c0c42e0f500003a60203560044070080d100c402c00c800c000c03c004003a500402a5140c8a03848072805040c6c49240000b030043d10340ca8030128040c030413480c011903103068250003150410700c1161000c1041c03154400c1203810a84403000071030031076003019540c070020740217202019183c00c0180381014074060000f40240480d00d009056000900d421030f1172a442508556000d0000f0b4040c0b5950b440f1a207400c56481500340300d034203000004043c000301c04500c46c4403e003c8042d0001c1c8076202680351943c0000c2c40345031400c49001459402c1002000040351609140d88004c071229071301e00c0c85403109078480240c6107000904410032404000a001d00c0d43e4091112008203003626001402240d988801403542c812604a140254082171400010910603001400410300c00d0741c0300607104060391002401c1c1c60740400300951068407500c0071581584242c1c031101c60211140200e207850f035505c102248103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 764684595 1250 764683345 764683349
    0x14130b0f090d0b1b034c05180c03040b071803121106071b030203040e0406020912010c020a0209061c030206161407060b06070c0e0f01140102150a110301 67
    0x6803c50a410400f0b0030f860154600c2000540c8a041d51031440c005240b110250410005480c0c0c18a21001b040ba000004803422540408858098000180000308003040f041e5588640e40c07190071403d105000000081c808140207802d960101c505544560b503c2c40945c010040c29074040100307140300080404a00982d150066020360f40c8501c2d103428060006141030503031012000d09034807007401c2c4420036600005a0700240c13406910401c40e481103140803400c5205940c4565840e5a9060500090204030f40c02040701180485402042460003100d417820b072034144600c240503800c0402030401500f03004c24400d038000001032507620f001c0444413500240c040704840580040c1d0114040219603c00c80081605484003070a044283d180c400c5540c40700c6100f241381c002c2c05540ca504132561662904001d41d12160b52000c080e03880c15480c0e1340d507484030200c01c84042d01c3d02500d4000000d80900080000410301806038040c1000c2d2030340c886058503043d000350005401035a240440f0dd1180304800142d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 764685845 1250 764684595 764684603
    0x1030b01050907050306030615030a02061207030b032e23040212030909012d0801020c120f0d090809030316150b0102030301062303070f14130b0f090d 66
    0x184550500040c00000c0100038450824490200203201041c2c2d00003d5003540411100b80031440d0071274410209081c001d4102000750412008205241c0038040040c405216036025a8100076500c00d05003015540d045101d0b801c00050f085000c20303401c00b6102542d000070034944450100da54200496201f8884020304060b030a06406032003400b00b1854000802030007500644000c42c10301d5242c08c001926400d0601c22944600c01003000540303a5206841400c0d03040c0200d0100e507402681c4c1e11151070107540000c545140a000300314005d212000d03110165140c07207035200140d40c18280715000a90080c011032900791480101803009820316501000100b80080c020036245149200754504505000a481280c21800b800d05824481c02e903400410360303044403010315103800c0e00040c5280341c40c0e40311020700500411890000400c00341d19004880d003244d440941e07461807860318460034800d2440c02458903912003400045420031210103860b01508882209020080c500030440000680a841a81c0116 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 764687095 1250 764685845 764685863
    0x1090303032a0f022b030513140a0b062205040c0801020f1309050105090c0307030b1e01120c0909021b0604030305060a080f060c07031b140705030f1203130b0103 71
    0x45981401041031501030040c030451000c800304105c041d8050000c124008140e1b480002501c002c99000c400e030a5150441200070b491090f01485a8481044032015030f01c9580d0307040403a80b242030980010302e00e0b4030007481c951003030185503c180001d07003c094415030b0764083c21040440e160b9403e01c0141284c1c1b1001510540d90310180c80000d1030100c0e40d601000d2407501d000010061501d5200c1c6d007503444000a0b0103541d50765190f000940080c02c015402d03a80119007000110819180071030280e1040c0c0003600d601e00c5041402d0003020949847c0001d0340c0c0022181001000112100d4001c1c03c0c070440000003c00d80500c49808031850b20301c040b2020b400090300d50003404414103010302e01e0b202a001403005040082030600c0b015a441001421508807410009224000e02d40318441c010364004086c40900401d00003402e02c86003440980e0b4071001c0ba4000e0200c00142454009a48003000b1045005400d2000c10101c1880454100a00003082a80c01c00000360000307602411460203588145495 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 764688345 1250 764687095 764687117
    0xe031e0a0207080f030d050601210603140303131509081614070b09060d090203010e0a021003090b0c0f25170304081204020a1505071b0501090303032a 66
    0x70300d0980940c3c00b8041c0354020110301103c0001c040f0866210207250800032a46455843c01250003a060b4640a40d80c60204c280141e0310f40c1181e04440c00f180d010b0701010000c26048694903450303110542d154201807180d95092000503041c001c01061156050500140b400000d8442c2d000c1c0740c0c022542002040b1010a0800030031421844042a810829000303090301414501801c0d030900c5989103581c410f220106410031501c045420129000307a01400070b0041107a10007a007955851585c00c12481032000c0041c0c1700029111b441a411000e40140c80a203494958040030b9000307500000c1c86980f010002c000c2591200458041d6031412410604100e25540e00ca041081c641058a0b002c12142032041080c040070690381d0f401d440b00411048260741c0580c4503440001d044000c9070f40020004035940f044406050b8002d800740c40a40d01400c610302c49400507412035120824940180740c0450b0390f001050020034420742c08480004e03a44001c203819070060702c281d001800400d080b03d80c0050360440d06 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 764689595 1250 764688345 764688347
    0x9030f150109020c25090e0a0c0b0f0d0221270c060d0f06080105070903050c041b0807020c0613091b02030a030c090b030103140609030c0c040e031e0a 66
    0xaa14010706402c1e00842c2004079407000d131502c8115003031039800d0446190540415403d12140100010642c5041c20010001d83d495029210004031106984a81c45101c002519480040c202d451804514690b10b1500c90307196000ca00035040080c1c0c08440e8100078031058511001030015502030402150307a04d00011240d00508102107c420007599280c02049110000c0d031a04000e40d0740c18150f90340d02007443c640302c40c00b80000b48003036804112558246402d2001054014202d041034034050303400d403200003010b031050005803a000700c00f0318183d445c000d40c111070180c8079042c5070350040b01038419a00f5816411000429030340000c0e00c2030030391f09206e0030308001a5885100d42d40d086c014403050884601340062000e5164018410a403090580f180701d0b1105843c0b06041030000703041003280407600c030b5840c0d0400140551603014801c0341031180c403011500074074000040e58508185800141401142241440040d000a05143c01c11b8841402821000e0740c8208900e0043c00d07400e203031641c840d00c40d040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 764690845 1250 764689595 764689633
    0xd090b0f09070609030209090a060c0504080d110a030311070605010603050a05061002102004030c08070803030c0711130e10050610050403111f0207060f03110a03050c09030f 76
    0x1011070a03600000e410050103400c8540d920072a0303011254044c10760341d91001103040c45100070004084602d00040e00e043ca5400001400c05e8600074400c03203c40040c07401042e03492000c0b01550001960000d5030050009100e900450040766413030120606040c0c050b5900004c1c2d0341c080c2c2043c0d0119440d08104040c02c6494441c0c04e903c518101c80800e0071132911a406506e411354034041e4086d050302c50310380700715405071020f6454404c0040c1100c142e86940d0303410f12800702100c81c0604c040c24041d6600000d1511700000a50b40104030002001d46010150380d90801e8003507801c0c60780ca820442d404007200501c00e8030b1240346030024020006c1e0014030104070011046840003081240324640060b0b03441840e0303500000741c0d0250f80d402100c154a030095000001c4d1002035100c03410078214181c81d401d28180750f000c01c0c5481100c00d151100c500b00311640303c0070303001c0d2045180e4140c0700e4031f4240101d011551007504802d4000010612907440d05c001c00b80030a040118502e003941716a030107400c81c0301c0c80d401e50034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 764692095 1250 764690845 764690851
    0x50402091303050a141e1207090810021c050f0402041b1d21070801061401050f0304021527041a1e0904030f020d0e03071a0d090b0f 58
    0x168181091440d41d541c00341c034138012900840d0400c004800154600e40c03100c41250784421407141d07019000207018560726003541c082601848940d600c1808140c004d4054103001c000e480441340a000d0f52025112218029040142d0010a175803000141c00b440d04010311441d4010440ca28026126241500600c01070310250796407804443c2d40300a0400010754000d00c0c0d0040c29144640c004d411580903030010302050034510010448940d4020310120110700010b482d001c80354a04001d110303440d540d0341146101000801018040743e002c01c45801b41340342c00d03001964014401000d05840f09100680403015030020380c0210340f0b0440b0f0310780e013a02c0d11010524800018204550620001d042042e05404d0380d071840b0030b1280101810001e907011607914230400300b01d1030400b03440e03084070b4505424010401d0490a81d0000540103020200b141c2600c0354044112a01c07014004129103858550041c0e0340e0301d0026543d00c1c51000c03c0c022a08050708038010381c44a00d002d8200042c0505200c80140c040070000303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 764693345 1250 764692095 764692111
    0x61103091504030504060302070c08030f0702090f161416060b240d0c02030d0c05030f36010209030313031109090604021e03010516260a0b010c0b0a05040209 69
    0xa10401001130340c0032080f141036502d10320300542c07649982e01d0201c1d66135220380c209008034000440c3da650729403000c1010b00103d900880340301031380c1d1311106c140c0741c1c14540a4818a4114541042400c0001c0c0034840d2a800426090300381c07450108100001406440700c1001111101e40b01c1c0241001480c2084959008a4011580303079805039225a687d5050300c201d41d80200c18685980700b10035814028000d507030110000401c240500d01c03091500400984c0304840d020000d084900104001800c0810203402d01211980c0715800030851410000400e00c04c1d4500011940d0200320420441d01c041c0042c05205041e540002d100c2030651030a03c0480301e102a18602aa001404001e10300e100002c1c8182c006405032034030710302c00020382122000c01d0b0620542640540c03e10040c403034041300303864111110050f0ba5a400315900307002900700c1844640c0e824440d40e49103d44002c03c6107408203a0000c200c1400504000160140640c1e645180314002c6505182151761401000150b0804000d426449854 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 764694595 1250 764693345 764693383
    0xd03080f090106050904060b03070b04030f1709060a1808070303051b0105160309030e04020c03030906010515090f060403022220040b030a0605120d0e06091c06060306110309 76
    0x14200400e8405800620141c00c9646808800c3c2294402b8080b54001c4c003d6590056611a2030b400c203001130241015007251030340007a42990307254082c89070944c0c42c8000020001881c0038a0348030121a0390300c4103c0d00c11040c4490082c0004c21500c10001500118842d0302d034183c45038031200c0450b00e0303907500d0080076120343d050900f081880710050180c514200640c0c20001413802660030122005101d40c820990054400109422070326400400f46100d80300540445846a80b14428043d0650342031401407040f6070248104007803403810008080103810f0151442d800c150780c0e13400142132a9418090981c2d4082d08460319030a0103c00d0081e070713405c4020000b11440440e40364100f0341181c403843c0320303900c0d0106010010a14004c400d03084903009040007004180b10284003a5000e481d0000401c0b8200410b82032500d00215045c4082070f41e03510342004060050200300079070b010114200c0702404840c00c0341c1d11100400041c0481c8110080004a040180e071240f904029691515140e2034184858403c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 764695845 1250 764694595 764694599
    0xf190605011a07120216090609050601180b09040b040216031407050d120f06090209040b09060904020d0222140606070c2105030403080306040b0a060e0409030e0d03080f090106 77
    0xa4104102e450655000da41188100f21a0100728242940c461a142c006c01581c040002d801e6a241c01010070317180d54640810060b00ca000064403401e241c100003245000c40389200300030041000010b441805d0300504007003200107014000800b00da01240390f0034410380c0100f8203641030580c05020107401c510b0050026292503680d07100c596031072114408140820000780182d139410440d541124100740d1201c0f01c01d00604d61600c01c104040d400c51075550340124501080f1008600d40008076600549025010002e03a448503001d02808170000340040c2d8103c4500c801880844a91140a9a501d420700d40001000f107102409400d4144000d029184104000c0c442c00008c00c040c40340341021940300c10041c6e40b01c01070b8000410b0700309914039405082808045400401c1c0310f00c2e180114842c0c881103d080020214072420495180c0f090b004a078000780b203108408042d0305103940104030850007400c0008140c40d084000880c0c401b070389082200000c14042c148204e09003040d071941c0c1c0110311007000b40120342c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 764697095 1250 764695845 764695889
    0xc06010e041518050f0f010c0c02010509040e160e0103020405132a08120904060518130c090c0f0201050702010b010f0e150c0a03020d0503130201110f19060501 70
    0x40c450301c9000060b03a59841d440030099032540c04290745030781e201d415143c2401d80711050380e0703c40d86a21800072481d400c1a170313840100ba201e0f0400c440e40c0e9505071a028200b100160034400104480c0324600060f00c602481034242040c0801c2480051000781000640c96042d441800b0940c2c80240544464006103585a0b0000f001402041b0b005405607600015880946c0c507007540f85800d0741c2c040310300c40c01002a07020080380d031a0b000f0048410140d40500400d5990310078070a410b0103405d900400b035100c96000c511140000d40c078003580c00740903903840a0290740720201c82c0d0031540900c0d0500d001c149040d421002c000e8080c0105544100c040c0003c2124190040000c0e1074201490f00386d40c01c00030300c004d0042403035498071a24415456038812107501d4203010b05000f03560344d890341401d50151144504a1400500c500c040f240709405441c0c07203400c15410341d40151207560001d43d140b1064042c1e80030b84049121b0800c0001080814028000d5600c02c50381088411140181c014601100c0ca1020b954544 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 764698345 1250 764697095 764697113
    0x60309030c08031005090c0406080f060307031502041a03010e0714093006010512070f05011209060915060b0702061207120615090617010303050a1803080c06010e04 72
    0x86402a81441c3d5a40e20300c1110080c3c41110782006a2084862017440f545400802c06041a91541c3c0c80329442c548444580203440001240c0e6168164841c05082c03000840310079092130075012103c0050f042c981c880000d604240c4c42e004803150b810202000412259582d4801c02c0c0c6c20880340e051005401100040183c5c0c28428581618040c403501801070600b006d6102900c0040c0314058200c40e0f042c03054280207a01c6110070300c50503124000c6500c0d0144280c10101e004806c840c0004610403d5514002c010342d90140d101c00030307001c8541e5403d80c000200d200c1d401803a010921640b525281003c03000d58403070840d03c441e00000c80540c8181b0140005032110000c0782d8208001d1140514030b6901d40004071011070040c0c0e440c01c562414107000250580340390741d216402000940b140c481c3c981d2a040c08a900c0101c0301d1350f401c0b0a9104000400100703008000609880c0400d107480c1d04030b980e940d2041503807500c0d55030003110310746400100c1d82d80d00ea000b03000e0035002d055401c108078994102034603032104d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 764699595 1250 764698345 764698367
    0x50903100c0207261221070e10020f1e070905040c0302030307060f0b01030513151d0c0f0105160b0903090a03050102090a0807120b0405101104080706030903 69
    0x149554590041c0c119008104410040040003132001c2d040000c260348040d6044c0141c00d020b000d200e5500b45442858000050b40c0e1100c120080c1d0042e003403445000c4002d420400780100080c451a202d5440c8151140a00c3d4010410107400801c90248070060b41c624000094000f09050502c0301500440d40c04082141d000b00c4440a4010400351a1410644000f003100e61000b589840005490010404540c1050490400d510410013210245200640a036242104c485048040d4001044d000514842038a0401c030541b10000403500c48201e002c1180302d041c14020301c01030740710140042507441c00911002c1c2003902864414103101119260003600c8034021002400c4400d0302c0d00080d0f405104205442e11070000900c160329043e03036402d025000358080d1007410b006142d0141c0c00b107030340c100002d040d5003100c900000d443e100113000e48502a00c4040a8000c903064000c0c14501c000801c010701920610600c031841c600e656529244045180507404d0340101c05040c04c1000050120b6000406014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 764700845 1250 764699595 764699623
    0x12070e01050427090317100506191107121509050607050c0a02060313060b030c0102030316030b1e0108071b1709040f1506030203011202042313030f050903 68
    0x40f190a0081000d81e04050518040c1030991403d450b9005140d4040740c841c800d07001c00740002031203468440c51054410326500038540c000d201004840308103810061200500c08852130304225031880700000c81e05252203503202c10084040001410140104400d500c0b5821404000c200f0400805030768154503514014840c400303000001c20721141c00b84043c0099124a9401050b042da40c0c944078103003c01c0c106c0c0c040000e8800340d1a01010b1141810006080e03005404140c004500f141e4030341c0540b80d030003644c4902032020551901e070074031004e842e081103060402c11465201040d103040640010400c2000810081c1000450000c0c20482d00500001044051300000b14002003110030441e01240d21529900e19081171814030070580c0000654400ea40b01700c40310030030394515a41c2d2441181a4002030250301180b00d1110381da003006280c00d50222030b4958402c12109825101d24017548002c02080b2001c80b16910640043c404140c1c3c0041c81140c5081c107418080e0078005c1100c04a40c0d620309102d0a0a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 764702095 1250 764700845 764700869
    0x90d030c14030a0f320f0c0f030405040c0504030c050f0402120f0703061703090405181c020c010813150b0d06020c060606030106170a0b0907020312070e010504 70
    0x303015030041d24080100002044079542c1ca40c140c00204081041103c02e00015417150000349000d400703441e5a03d80c02070914090f00e07820010440c44031194001031500070200390401c44013502c01001e002200c00c024410014589541c90441070000f5104030681100403c801004103200140c2040002010358030207075200d600e00040600810020311660940b080140803130000c2000000340d4000071131152100741d03000c5c40390076074845100440c40b00311490032160b50010b01010400c1d003802e0b4802c039440b4032840003403c0390340000e64001d410440108024400c1000c03c01c9808203064040249c00500c00c3d0030310f00307180c803440e01e60594880c8014a03c4000c0291003158207084416100340c11205a942e002442125002d507189400c2d402984922001c2441e40120400a1075618003041901e040b501180c50740080b40804001080c0c0514000748000075144e5240106041d40d181e1132030292140b03a00e60019982c8505500404814000050070141005030003011090940d900a054804480083c2400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 764703345 1250 764702095 764702117
    0xf0b0403051b032e0f1a030303100e040204180f0b22110a0f060c020109080f0705330408060f07021e011404080307080c04050d0f02010e0409050105070311090d03 71
    0x44e20228030303a44100c5660030b0514200762101c01d0582e01081c400c5028083c03025032a544282810b440740070490b1131b590214554542080440d482116003548139100520000d070380c481c0503041107403040c001402903401800b046221030800c5400d80c0b2154004402e2030083c06031009100c1c04030500510000000c3c00030401c1d007a01003840e03c4e45100d2401400d1150516001d154443c170001f0308003003442a003a40015004100007035108004142016110356410140080600301010700840c003a800301220001c1c0116141243e01d5400e040c0412071041503d1724440c0e032907143c00f03c2c2501e031080c00fa0550204442c650113124001d5000202c002405000995403015141c0403e2180d004080101400c1d40fa441500b0400c4208031242c00218810041030300c5031081519101600c4000f0b008078021240c00141840c8840041740c180c4542c020814414905000500000c10224080da0124034003103c03160344581c24000610703018011482202e04214601d4148038682c03000500e84414a0009814000e01c0011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 764704595 1250 764703345 764703403
    0x5060d0903050c0f0c01140304120c0c180c172e0317030601020d1e12020903030a0903060c02010218100306080624090702061503070f0b0403051b03 65
    0xc3d00c1044001c1003e81ea0302d4041000e55076210511125440e0000d2150400c081901c44100240e0b801140c000034560020600448103035030324169100c09452419428a00280c03941804034042c0307409d001c48101054800e0a4034014242035240c3c119116250850810081c080c821411240804000c0150b541131906e24050590901c0e80690006452281011288081d464203000218042c80d420703402c640c681800040203c2e0700429a800c00203030343c201032384041a00ba20502d0f9402c41044915001072034800c403580000e25550100030b0080210319041c404000344241e91103180c0042d840c600007503107001c50070b038032000c1c0303403198080440d12507030182da5030f10582407080d48080041d01032942210024286400796510408d54200d860b00380c4500188224903d04260384083c0c09003c1940041a89454645000039080d411580c92a0103100d07038500042c4010704540f40d54002d10411045d40d541e5421424814100410433004182c0c4650b5181e02a81c3e9440c0044c80da4014603824010a03103080020344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 764705845 1250 764704595 764704597
    0xf07030504150c0e0a0e0103030512191806110f0904020c0a0b190b060a080a021608040b1206030f0c061e1305030f0607050406200706030b10030605060d090305 70
    0x91101c181500d400710f21040c1d07942000e000f443c200400c81d801c01129a44102c0162401d4003400014002402413009034011f00804495035002510018111004a20003000c1c0c4111400891059002ea00f10754186081c06240d12418200f190b00b01045031074603845a0f071211042c410310b106035004540c0080e041540303000a01107404440d0b886400c00d610760034007801100c1032650910503121500c0c80c103802420039207001c0f0304030380d0030023a55204d00d43c15507204201c000007904042c55440c03012151180304070000b50404028000f801a0a59a940b04d00d101c5c14680015480141600c1c00307684980e10012071211b0005030703c020003000710b41c0d5035a40e58148002c040038402c4d01c1c041508005000c240c608440070712a41035010f4800a5003111018000744c40604e82e202c1d81540c0000116400300402d01050307114280321520b04240c01138a4916400d040000c070700d01504da502c2280002c1d030702d1092100740e10742031040515a0110345000d00032541000300007103280c80781840a02166540c0ca04940402d80580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 764707095 1250 764705845 764705873
    0x5061b01021b1002040e070c050102070609030f0908060408090402030c19020d0e0f010c0803060a211a0f0a05280b010e04060f030f11091602060106080f07030504 71
    0x255159448696142a106540400600103004100301d1090303240c1180300317440407103400403003141c02911030b03a0702907400d410400010f03500365400300101d1000c11410300a1150340f42c400d980b0441070b0b071442c05008040740544c1d0000201d0b0341144d018000414010401d4500140040390300503600d481d01c041040e01481002043d4030001ca15101c994901e0ba00814401d030300b45420388031449502028000c00001025204482d804503480500900100700e1002c003440d800480a8074090034643c80e00c139400e0050400540c0511420f18901034802006140c15040780610786425030f8044900307140580c01d01403030b0014066102035a44400048100300802c05891150422441c5158512214540719018050030f01159003c40d2500c0b08502c4942400d11490b401c0314950503982407158111303034808501c98001a816145c0310b007001103815542e500c04e0001805a20306801031424a64040d2020341081c00580c8600140201d2804100080c1c2c0301c52000b5510404c0386c540020743c0d035907030320700360345420403203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 764708345 1250 764707095 764707147
    0x100815130c0b0301030b0f0601124a07030b070809010908160605010506090a05090604020405090f0a0e0606010806010f1e020d0e03121c021204060f1a09010506 70
    0x1010000b4011034807100441c1078901580c0446107c0c1e55207001500b1071a41a00c2d400c1c0042c1c40040f0701c50425481303030b00c545845c41c00703e07c00040d80c0c009016003420000c081c55200115041070841c01c142030054040035409071420a01030000e0f103107113484946000b18002d001030f090007607050000d0180e64080d44682d030341d240d000f8401c5465025496404600e5601040102c0d04c4074603000003c21186480800e86120007802050038425038100700500c01d00c000040c24075074000350280000b03e00c50790f441064600c00c0000c03a01c048128a01400604165920107803580269000300045c468a80d032f100d040b850740000282020700b0120f454140403101103c0ba01da011250102c2a40c6410601d81c3c0880d044800d104140d840c2480ea001b440704050b101e43c010480610341e03e030100000c49c14803550640c110002140e020005082a5202010306000c04084401b1030300c0e03a03034565420032040318500c0780294071001d1403171040e60000b01034003040078010b060244611650000c40c0007404002480c0011580c0084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 764709595 1250 764708345 764708363
    0x1b060b04110703030c0e0f01140c0f01090203060a0c0e060a0516030e030d110a0311100e010f051302030a020906031f05010609080a03081603060b0705070e10081513 72
    0x1101c0d0403003602d4010010490000c0d080c0b52030780e15024842c00080100340e074000c10503040500b0010041d84c07552611500035241c004180242e40b50751805118401c0c041701d40b0400801d2000c5144105030801a0003400d811040d880c00d10580244c6a1040701203c00c4001030f40d0385a9a407140c09015a070b2400740c203410000421410380c030030080503840300601c200c07140b0942c1140c080c40040101940c9101c0810580115030f4805150740000c82d21519201d880040a9010f407440640c2d044004802c0e1051403181028980d160400031460394864841d89034001008121014a0020b90340000d07201c4000c000c01034450005640402c03901e41e805d205c8100e03100b00102210130081a001e401102a103401d21684002c5464140300246201021070310354201e99041c0c0d2000b84075a031740021050300154480c1c42d41d082540c0c69002086003460034004005080c0100700a000780d070315020780007038a80300c002d140400b030075076a01003002400c45c00600f0b038008284000312007101d03649000300044042e0340e422000e0020b080d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 764710845 1250 764709595 764709611
    0x80c010c06022b0c1d06090a030c060809070603061d0a0b13050a050108010e030d0c0e0904081201051002211204260304020a050603040201030920040f060302011b060b04 74
    0x107540e0104081c040c41d4601840f601007401d2045c1e603814641c0c3c0b030130740d41d29004501000d2149024001804115030080180c1d6405840e905c40c680005015003062005c41c040c041480b91001307040010400401051a081c0f200d9414548034200101480e0044032010032440c0c0800c140c0c0390140c1000e0206140942011405031034442100c024200668103040031501d0180003007001d80d0180102c074610300015004500d09a26204000010101c0d60070f294108219100c0a140300e913a203420050003140940740c11625912944a04150305c001a4040b6100300703103070b07a0a00132103500810308400302d883c3e441c0801c40e84c0c540300781100aa4810301038401b5034001c114003084108003112090364420311a5002a0081d5404c08070451741c02d01c4180c0380a03510600d00a020402d5152420065030301c50f2040c07402080140190742d80f4500510122042508030310389001e001c146092520800d007445419900a0042e946141c00283c46c03421590b030818071440b800400d6070b0502680d500200d00d06d010291080103010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 764712095 1250 764710845 764710897
    0x1509030e0631031a01032307080a060203040b0f1006050903030c030d140f0103050613020f0a03031e02071809020d0512090a0512070b0a02100515011404080c010c0602 73
    0x120060101311282022008202c048810700c04180d41640d034070100c4081c0030704005422a1640541303009105e00c0b84100403001c03480120910044041501c40e0340096140e0900349002e000b40380c0010b000b1118030a1090030054004280e9001c03404881d028100655101d00c0031001c0380c114481c00015071460701c4002840b40600d038059010300b0700e04a0103051b900300760b00c031052508403000b028813004d00180c1c801c001140009180b4440e00041d02c1c801882a0615030060340428940c0384240c0c0243d01090100003100e0348180305000c0c030f07500510a0303c05031101906103041100c071060050815081159a40c42140854540c855400329564004044400855460741c000c62940d000d40d03210390207a00c00480c00101414981d0040d0039110520028003240c40c10000d0004203178102d03200c00800c40c45110b00c03014201d44184110f5000700c03044207134003800d00005000074104a401400e90300c1c0480007044100460500400e1b074242e20002442c020b520301d5042d007000c4010f4000e003000c40b1189051868251180e0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 764713345 1250 764712095 764712187
    0x70b07060c050301030f12091e080715022a030a15112b020d0614180702150702071505190203030606120405030d06060203071509030e06 60
    0x344561014081240078950854890100b0320004010740e80c0d884401001620b00502a110940d50f480e20b14015940c54802c0400000c20315825500071740c2d0395000788201d003801c1c404080a0480c00d1140e491401910748000d5950340c1d85103024000381004540280540e030100180286100c3c002c003105c1e1030844c2c500303180245125103664659240d250420051959440e202910384003802d070b5142d4118200e10890402d80d0074403000100c0035896080201c0b00c1498103520460016040781408014080803c4050154030f40140d9208034014040004000e8080d0b400907132400700b003085c4c6111550644400000740c0c6800c1042e00142d01c0b0020211480b545030350300c50054101c200c00812002442e084000301a0780303921058445a4003d18100a01e41c4550b83d07203000c480d0883d21a00c2160719100402b404074044030f400c1c2d0058401600005036080a20103509404d010200100f24100b140040c20703034001d414154a00d6646004081c0441c0c09900c1880c1d0500780320b1401180c1c0c4844a00b005c0d440d00c40040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 764714595 1250 764713345 764713357
    0x6080102131719031b17090f1906230301060809060a06031e11120106030209090f030406120f05010f0609060908101503150510050103091112010e070b 66
    0x10b1000d203410109280c0050282081e07003200d50840d1100d40c1c0b50301c3c01c8910303800a01203030031141c0281411600040c44003030b61400b0002204c41c07042d11410503400300081040c8200c00700e80f00741002c802074070f0030f000d01248510442c0c12a0411503c0c00c1000301a07503021150030710340c40d034404801000000d20141c101520078498890141a52210342c2c03200c2c614001c507030071030001500300f60420b007001c0203d000760241d03052181d00894440c140c06c01a00f0004d0b0074146088003403051651641d50400071400d15a410300d4000e00400d002e44420380b4103101841d601c0c0110700c81e40c000c0020051224202c03441940c400c80c95101864820b10480d81c4840d9448400000d9118200010300350104c009110343c810324603074040c0c40e03445c00a06403008500184002a100300403d40c0c0705803d00000000c001400c002100169941201010419160805480f1000002c5500480c1814205260500026180d9000151540701107451001c079026040d456801400c0141c08080c040c4036002000c00d25000000c0030300702d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 764715845 1250 764714595 764714609
    0x3180c06081f0e04210c0b060d060e0c010809070e041b050306040c21030206010510050c030408060a060f050306040b10050315160306030f0602032a091302030606120a0608010213 78
    0x145c2c01d440b540604201c1d0011190000c0010800b0030808002400a5130250b004080100321044880e103507281c140850307070b034505078100682c8403c000c41565600700d440303207500c0040d0b10003030080185800c140e02c80710100100000d19004503160300044a040c4c1090440107004064111001c40c40c062801c10076040b60b5000300b1030050810980c0b814070001c2c003080d4514540d03040d40908002d074a080c040c4101d42c540d0042a80c240042070080e0804104100082d1004003000d10041000d0708004d1000d40464082e0b40082c42c1122074510244000d0f20002a0103801590000342c5d840203643d5040c000c1c211607405d400c8903a00d4002d2420503800e088000c0400c074040d9040c2e01c070b1040c03a40341040041c0d0898540f4800240000c003480c202d28003158083d40035662240e0012800340c00c0c10b420000740710722810000400212074002041c100204d041c0500c4e001400c05408208501d0b40c206003001032400d02491851454100c0c039140040e9110305036401110040009200954640d2541c0c00840903400c2c881c01850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 764717095 1250 764715845 764715863
    0xf1308061e1012081612140325030f110d14060d0f030c020a060503010810060e010b0904150905010e070219060c1e0f03180c06081f0e04 60
    0x3141c1e5041d40710796004103422490703420014a4007200100540c40c0e0706056902c2102880003015103c520100e450a041c8104900355140540d0340b0003400e000040b03c1030901640d0140200580d03962100d5904410f0710301d800003641054105c3d01e04a010f460b082803034210300742c00d0440c01c4202c690071001411400e810701c0700500000701c0840300710100c00d07012070f441d0750310110602c203d502180f960a0011001d0b4061300d00b03c0350600c115004a404500e00780d00610010390000010444440113002c007802c00308980d4414001b061515000811801d0180a03c01240303000140840182e5500da020444112f030890001c480650790b440301c07000901c1c00740315040c181e400d550009242107202040b02c84090103c6500f004894000341c0301e00000b8611403400509220018007210402c099850806000c40d200c1d6a814140b1904400004d0503141c120241d20b141841003010f507400241c00d4400c901c15a001881c5c06a07070350381c500b082c0c036188a0043c3c060919a40040c4000f081d00002c0e500207520480c0655002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 764718345 1250 764717095 764717131
    0x1005060d02030106030620090604060503040c081204030204050a0e0d0e0102070e090c0f100903110406210501060602010b010818150408090108010f0311220e0c030105012103050f130806 81
    0x8031f8094401c41050a62000c0100002e101d0306001d84007454202d0301485483c0c1c211034444c1031942c40c0507580d1000211407040414100301314541400760561240729400244016a4400c15044e651142e102000081c030190101840507a403007040040010003030860300e28100d04000114a03106d0540d4083c00d4041c1c6204008107119041aa028140c801d000b0303560b100c503d5142d5240c081c1004040c00c40f5950194480c1c0c0c0016410701054010036080c0410b06070700b00144440e260281c04c40e1300c0d56002400b0740e41081c40b00d40c1140c2e0800441030340200700b08230341d0a0411010829905000035200300d00140c941400c14031044c40a41809400d550340d080e20366230030310703600e900240d4000c5096200092107104424910000c1d42000b281c44200e031340d0080240c0d501d002d40340710100c00392901c0040e11403050303000c450f561045107400d00940d801401402c2c1840c1c602c400e8101d40c20401c1c81c510f907020301840800034105140c100c0a40807900382d0f540024018800b82d807180d55003a101c6600b6030707412032030003a04000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 764719595 1250 764718345 764718401
    0x40b0a0f0e0d060501080c0d05070909020612160806030c0a060e030a0501050115180b070807020409120c1a06090c1605030a05190306141002011d030306150c1005060d020301060306 79
    0x41c0d2320300f040d0014010400c180c600030b4484c001e42280102243c1001c814402a44045918024240245042c00001900000e4404000d10b03a03a001806184a030b80b140c000c454403622408640c0d011398a00740762170400c0c10011000b20785030010b1244001c00641ca41000010015000340541d02044201d564061010003084408903003605075014861401000300100d000041c10704000300401361000c3e20101da003910b15216500b2001030303184514085201080fa820401c82d9034004460a951050300c0c95a0300d0601902042c0c0080c070040c201c224101d400904001c01303212810b018a1002c1d4400100d90b600c03252058003c1042d0408441d0000860040310281002406400354605913840c40842281140c0158204030300342d510107910505555030795424040c4001c030041c242d15115040340007107690f03080031014080b203003e514207010406401804002010032000c0f0301a0341d1020071600c040341c20b455a0001500488200c000254150b06c0d1060002c1003000c41d400a41c040703140c03001003803940038400107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 764720845 1250 764719595 764719609
    0x140105010e161709160617010509090f0303010603091103010b0d030f0311030901090203070f0e0a0209040219020607180323010216030305040605010b040b0a0f0e0d060501080c 77
    0x160304401c44400001645002514002c221500852034681c107400c00401620740c0071a02a15030150540081040301c003503061211a40d00200340718a004c4a0300300481215420a4806000d40c45c400c11200000c511964800c109040a44021070305480d07aa581d1074801070f0090144003021204100507114401d103d00e01031080325000c51000d44040d2401c0e50702d541c112050903030031034030800341507551b0042044461b105020350f05c41e054900002030b1340d030039500405141c0a016400300700e11284802c02400040c005400c91030b04038403151340142c0c45032200c20016002e40600b0590204101d4042091040369500103621070180d000794941c220005091403518070a0102c0d400003808140121244115801d000c5040c44a4200800b00040c2031240c00d80c0030852015071001c5c00d500007525079003800203001d0248201d41c0106488043d562506142400c2031040b402a0411001480700d230407031200c107031402100980b00f0758900801a0300500f0540ca00b00004044c207015040c0184181545c0b2942810660 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 764722095 1250 764720845 764720849
    0xc15150b07050a06110c15010326270607030e120102040b0702060c0a05060103120e01020d21060906180e010c08011e0302061201060f170a1503051914010501 69
    0x70010341070702d0070984c071050b018000c401031040c1d100800b04010400a2020700c60034001c0d6404410101141d4034604101504240c42c0c507911000c090704560100969007640c08507064100017600d03240005120f50f003205c0c595003003005d08e5904240c00142100425901103841c40704120211040a04d00032252003d600701c1c0610b00602d54495000c1040d1005481c1840c0a0046000f410080b181c0780c00d019940c00d402d1060a0740122500c00a0110301014150030500c4040d2180c0300384010a1750f501d1400c0001e09940944b200301c9103525508039041c40200030f9400c031201400d600002448242d60710680c0ca03801c1005118101070b024648030000c0000e41043c001c031101c5040035503070007440b64200f400000c4655101003c0451070107880340004010f86401c005011b440c8808500c00c2c9581d0325100000d001001c48010103807c00001e0321121130405011403426401469140340000c0042c50084d003102450482d8001a1503489a210b081c5032000c10052100041445140c1c0b500541311a5100c140c01e0307a07000c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 764723345 1250 764722095 764722103
    0x21303140f1b1f03090201020f0f0c0108092b0e010903080306060318010504112107030b0709080106030503030615160b0402010e0405070e120a051b010c15150b07 71
    0x1c8080704009403192a0a00c4079081c2c01020301001c5a008120340c0900e030340c0300d20400007180c0c48644400a5680501c10020481c40c6180600074500715042025202d99001100a043c40805030100c1c164103000c200c904100c8540190303078000c0100304800828802007145014001035211541003500d0752081000c502200c0d44020100d0543c0c5a410030401e19070002040c0d0000c9a003111805040c86e5024010700313000b580a241c84180c01d8554100340429401c403084a0005c0a00c05900c502d1650000544481280c0d00002041c401e500c4401d0104c508a019500c0003405c2c0d07080900120611101000442c002c800840f4442180280011210311038041d010075010008806140d84012444800b056544240b0501d030145034205040d002908807130007510f0020000300c6110f80d20f0418100f054404625800042c0245445d0300155190380c0e82d05001c8804000c02a0350000d00013003640108200d01d121075116a40200441c00c08d05100010301d103841d256051395202074800214040d05008a941c82908 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 764724595 1250 764723345 764723353
    0xf140f011715181501091b0e0d030309020a050303131d0712020a140f030601020d141e09030a141c0c110d050706091a040e1803070501021303140f 64
    0x24414852407000f8000f0b444101c9070140142c4854440c60000c81c40740a0024841c00043e06103041c0d00003c40c01034150008000c1c0030025040c4805981d8030501c003104198140340c0460151403600c0440c105492036849242c1603c00410140f215225401d10101a500380c00c8a20781001c000c803802c80105070080e01d202000c00c0c0310301c50141c00c00b9060780040c605044241406407800711140c3c9000c0c4240d100303034421428440048140180c540e41880088c6140391a460011b4034060300448496140c81121490003030003049440f250a0660550301340d40d0540f0000f07003900e96030140781c10140c0b51030346004001e100d14040d0070b404800d228074000c20f0441c921401e5079440d000e009207550300e99600c8005510158806140060100000d408000d008040c1c186035440300300c4c0c3d038649242425416403030050305440030b6007070000303200e12034070903a807254802c0858402e01c07044110342040d28211320520401a04039400090350780ba244c1240a8410102c0c1e12901400340c8d0700805602041d00d812490f5440311290b04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 764725845 1250 764724595 764724601
    0x3060901091106031005031009050f010c0813060f090b012c07141308030a0201060501030504020d0303270506040c09020a020d030f0b1c0605010e0f04060f140f011715 73
    0xa00c240503540c80b0145e82c031040c0c0c2840d2a280000c0c07034000712401202d4043e484140a0b0100041400260707c40d01d000802402030030003462000d054800300901c0469100345800d41001407000d15006108078200c012410400780074103081507403445100340a0f00d0b10092842c0032000880b03104008010a41c0f02d460141802611580e00881d01d00f9015050040340960501541c20f043c40a1000d1000404d408001960b41d41c030960800307401e6856036072106041c145810100405600d8001e00e50000070351501d00001c10405050101d00100285803510b50888426251001041000207500c1d01035400350313002c03104095446030808241e1044059a400581000ca05203c0d07070741c000c2c3c1000185000418002c03c0c596410700224111030040080c0c64024242e0210030070034883d040c814075000d0310200c0c0803031409141c2080100c030002c074040c10081245903641c00100b5442000d610485141c003540c0c1403c6a9410a110102c100d00028021480140e5a086000800100000320412461b1404112000542d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 764727095 1250 764725845 764725849
    0x31e07090305030a08010f050607050717071a070b0f06010e040e0712030207170a05120a030204030b0c0c0c091e2a1e040302010801050402070c0f14030609010911 71
    0x500150010052042450000c400200c2c140f01801444c80ca542d500345003076240420b807564a000d80e601c40d90141d50100916404500041003200c1030381c04084401d02100040060541740c244694014429130078005500001081804001c000d401d0140e4010081c43e03d80020408001d80c06460081c08669080c080e80030a0400341c02507400401c480c0700396003130980d5504c11221020b941d103004500580103c40b090194000d01c1c02c1103000584090010030410445585442d40e03010101c5003003502e200d007ca58003401c80e10a07011a80a9588000200c000341010660349401d50864001500d0754047e86d40d0030140c50420401940c862221100c007000036039044c084406011030050401c1e400f1241c1501000c415008020303440d9101c1c5401d00b04695a084030000c444c43c101280c00d10109110020802003000d03070fa012007000e05403801120010fa882560b407515021510f500e50080d15543c01d003460009184c5078001c00101c214105030181e6029681e1080e03e10308949441c50010203009420402d06000c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 764728345 1250 764727095 764727151
    0x103021009031202010b190503030307080a090c03030908010506040e0712020609100e100201020c0c01120207050109060f0b062505190f2f1509060301090e1203 70
    0x300e030460074900c000c1901c1e500d420a12104a440000150b9100c1e1440c608608017503100c04034002c5403070740302c01c41c4030b040100084e00c83c4000f8140c542040054800b00303440e9100c0764080380180e50b01c09064204280d03645005003d140c8a441260015480c1a000900c142014080e900c00301079800054250705040c011061882010420b0903a0480d201344104180e5440d0524050f200303e1136619072041d084400010880c8008821000200b164010f00840c8035141c00020341a00c1084242006d04c2020f0b2440b005070700038016214041d04035130901c0c4048051041c280d00441006100d03004c2440080c80c030409102c818460151150b003a07504041a64a200c0b103c1e918540501e8480c806071100c00803000c001004801c40e429040d07031000088120182000340d02d04c6c0480d98583c88400c8000718944046410203a001c003a02024003504220303400304029012181102c17400341c001401140c8039612050f80c10b0052200c480c5d10f501c5440f81100350f4414114050a8034400e8a072612019071081c40340b5000000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 764729595 1250 764728345 764728369
    0xe0718051012060f05100507112101050f0609060301020a08010905060d21020c120c1302040f270b060a0c02040b0406080c0f09060109031728110114010302 68
    0x1040001e002c460b8455074580160b0004101d404030109a07a4104030400c225125201203840c10301c0b10402c15600020011420807103001000c4420500c22401041d0400c01003e50211030341c015440c040070818031200e4810981d0007000c098131241c038147c2e540000e00d400c074840e160f05a000b0072429801000b4180d130f0f40e0000c6600940241076140f000d6000d581da40648803c240010014400c052074036507205504000403140104200e441c5a0b0707810a404e441922400d0f40c03c002e0340074000000c2050803101503030701254000d10900311045207050b0380d5007020a150300a400c18021800c408207240745800c12502640a40071401070415242080b132000031340b00c21031000000c0303803ca03031260142d0005075203a210300d10003400c00b50080c040341100740741004001c0280c40f44480c803844004060010590b80030b103035403013641e62000d0409134074031080944004a0081400c01c4c02c4070a921144019002204c42e01140d00000310349441d80104080030311582603816444640100c0a15a0300400c0580382240c15050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 764730845 1250 764729595 764729597
    0x3080610170a1808072f0d02450403091e050d060204030b0915070302130f060c0b100b0702010509060d0c05190305060d03030c1106100e07180510 64
    0x50f1024002402ea607500020f007825210b44101003580402d000c1c0075401141c05138950403c924442c40043c880c032600b9540b003418a070051418101003411502c0301a00d107034041c96400c1c04804130354201d080d04c0e05a44108503203c0318000000064032a04c030204084e050040d98181c907428000c4e4145040d407002d030100c410352000352010610000480ea101c600269512a00901026030b030340303086042041c0130080c0944116440d503c9180740300521900b0007205900101b0030300e070250f6141402807401c00e40348080d400042c4001c0454000284040d00076005c00c2425214515a01040c1e84d8849140007000035442000c4c121582006500d0040d0f00c580014604100020405800d100c20301c1090004c0300e211005040200e400010489203409140702c44181c1c0d03003c0c510b000e21040c5040d9001c50000c1400c01401410b16131510030205205006021203801b07c103c40c03040390b140b4540303504944a840d0b92803140c0368514003d40081400140b041000014001c48043c2c1c5546013460030f014000e1050031031311520 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 764732095 1250 764730845 764730851
    0x1032a11120406090e070c03082202150301210f02190306020c0708010b030102041a0705010e0f06040b06101e05190306140609150a020c0d080703080610170a 69
    0x30101d40c020201a00190089070313200c805280c2807008050202c5006080d8009004080c600c00c40026070004c86c5950240341c0903142075004c072059410f411550b20034903009500c0401c6442d03000100511002460407200c10319154100c1c01c450f442001180700303403024090220304110244001505083e83d8403014035940c02a135030704e0182e4035201d803800c9801c00d40d51200701e81c10402003008040c000340540303020884114002c504d002d04e0502071900861110724074001381c10010840c1c1080c002c0039402142c00c44003041c15125580c0003800403d442d49401c89040701c40d520701e10007203100b5040c02040b004d00c00391517445400848480c80c0c0210200300e00e0f15205020003030704001c03d000108c04070420b0b040840041c3c601261450801c3d41118030800207940c0c441c00b80105204080c81c9030b4a050078a680c8255100c180f0395183c44070113040b42070840d858603a54024042d0b02c2c0240c104030751107005040141c0295217503071035511120300b04040340011160000c0000c101e5100d003850b07404900c81d01500300344500700c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 764733345 1250 764732095 764732113
    0xf040912030e0c090405010e0d03060b0a030b03030f030c03010e10030b1807085506150b0403120201050103080f0a0c050706110625080403031e020901032a11 69
    0x4c803046400c40381103449035150300715000d940e1010002c404e100c141d80d00301881550308202c50303141c050144e100f01608264030f50000e8040ca0f01d00740104c88482101e10b0b00981d0342d20300700310340040591080c40781a1841f0785000004402d4038012015800f6a6840001005140c032507100060b415807000080200070301030804001000601013044e03088010441c00e5042d207080060145c624050550145120903c04452250100400803803c87c000d0725103007941c0c414080510f0400c100144202c18501c41e44c00406840481c8003650000540102c0b07102d002113200104510b48124241c407820302c00202004824469a80328501c884017412400039140740c20560741066484880c90410b03941e0004005c142c00111042c12a807003446255440100212a03000110f15510311110001d100c9002034100407811010034101440f0b07400c421821240c0402030710f2429414041900254844d4600501092070904e10202000710a108100c0402c13030300c01101240b41000c0815204c000030b507030203150b031401500e140e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 764734595 1250 764733345 764733349
    0x706021309061a040e010b0a020319120e01150314031303200d030c030513121101080912040b03040609140708010501171c110703050c0f040912030e0c 66
    0xc0c100007854480c9011484a181ca60401d140300c08880c1480b0014038100003d1001d40507005e1076504503295510281e940e40441e003422411030180700001c0200f020b020300b00004540d4054290617484882c10f000708a07000c84003c10170b089030b0403130618071010354010604001140040400d8485124481d007900d1820010007110819050f00341c00485a218400714092444040c200d6a6802000203071440702d08902d807520007902440c52010010300300100000d10f488a5072104c2400c50003049034203441702201010b86001c0c6541c5001a41807400100180e0000c2e1601d94005079040b070003407032803002070701e05801c1200410311980010419036040b51034075100b0001604507081d44801c954650b014018142c14480c2807401e40b0f1060f0300c100503510036514005110107012a60401c901c071601000c040380d007110041524012520003a00095000b00f142c000305004000c51070122500c000c03a0200740411030034042004540c041140507106012004034480420300070b0f80800d6841c04400700320f0b00160301b0000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 764735845 1250 764734595 764734627
    0x20f10050109050903070305040317040e0f09120a1d030708120409060806060f0d030c0b01060c050f030c0a030f020c091801201e0d020316090f0b0f070602 68
    0x6218826545800411101c0218856607800c42d2030100074526120761910001c04500a0380009000c44040313802c40052101c80310f0440f4020685001040341c40c1c60114034940c0c05503021144510203005004681c01800c0c218402c031407030a2015229003814a900340ba03002d610302d003005d0903142c240c8564500400c0c0e401c020001444016000380c8442d40c1c9505000400c02a14042e51224003903a0148081c0034181d07460413403242d401c80068614210030b01e05400c0c02c840000102c60702600d5018004000305106522400300380180340a1011100c540303e000c08800d0352803150100702c0025400404a020000f031150407031500e00c46140c812110407010303000005510117001d0b160350030010b9041701c146425800078080c0d102200b05800c0800340c40001692180498818000c1ca00d00d03d282410344160321350f0b0a041a00c0040282c684110740f24a00420035400005e84800c803c0b0200364914070005085403100c10502c00c0d103911042c031070300f4a00f4012500d48150070101d02140c54940078049000343c522025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 764737095 1250 764735845 764735863
    0xb030a020a0f09030203100b0310060801270b0106031d0607020309130203060d02060d110c060703050c0f041a09060a030903030c0c080f030903070813141e09040201020f 74
    0xa400169a000740d6207000d40410b10521690003400070324035003080517070380c0419074403000540700b2000b0500002d84000a07044c0748981003400707601071074880082001032055000505580c0002d80700d80b840340c8401824603a0587c580390040016406c00b0061144038030a41100c010a64010410307801e0400c1801540d003040741c01c88420b001031b8000b0540d0030f40d5280080c0c4110494568141c2146503040100228025501074000031b401a20b0005442c824082c05900081e165006400903e44504e604940039488000c10782c1c5480c0000d08040118000c600b09034210340b0310011002d919442c0c90324005042e0602c000324941c6c003110800c03d000411250300c8050043c12892042d0398005103e00c0140b40250480d04800705a900b041448010302c07000541c0c0c2800c0710070014400c2d400984030f6907003d118903d1441142401006480c001c01c0980741407584a600000b500c040358141e02c012441d02c0140060640007565252014040c51501d00b905c0c1405008950028018415030b90030740c0700c2011851a0210304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 764738345 1250 764737095 764737111
    0x2b1b03050d050703170106022e06030c0302190501080a0c0e0a0603020c07090b0f0415050d0503030405100207030903030807230a14040e0c25120f090302150f040b03 72
    0x58800f040561200c0c489440d01440700c800c04443d4181200207549029000070b01540d101c400c1071000000c0c40d111103940307003040c107641d0900c4207075120320300440401c03401e220490003a03003400030030a482104006140e042e00c0b01a5180402aaa0280c1358800790000e0341d0b0480602071400c04050546d25117201e5003002e0482a2030143e43e600040413443d1500c4410341c08075050500d020803489155450640c000098501110081200022550341c4c000381c03403440d03010a0703010300c030010100104800400036521550140040d80c181d0341081c21030106078481c800008000503550481440000c1c011000117400c0511880c041c3c100041c04201c1e02001c401142924000c40000304141311210740c0000d0002c0d500701d4500d00c103400c081c5080c80d040010034000c0d001e24280f035400304810001c50b0a98010000c42c01c01c00101d03c50194860500c20a9464211b03200e400080040300d4803a051801580c0784400c0302e502401108207005003084400f5250002241c045010408000000302d01d2200c40240d0300500174 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 764739595 1250 764738345 764738347
    0x20301030b160908060c0a0201060b070f170301300204050c0309011d0303010918050d03090215030603070603020901050f1b0c010206100909060b0d05010b2b1b03050d05 74
    0x1103142126040c40b00c081c095420000c030344805001a07a07001c6862030700102092030894030740d0110394080c0d0140880d038004440c28140483d1640c1032007440030381280c0141c024440c020030102100c1720340d41ca030b204c00d01a00c0c201c50310300540e00f1180110344011814540c6620303003030503655400398001001d5450075101140195408418004400c07400e2080c800b0f650403000c424507200c4180092981ca90005108004001ba40c84100844400c0d0007009044140d60040030380756030150b92030001e40142806101030740034440780f0400b4082d0420b248122400b64030020010501c0030310b0080c013103010354081071002d4108042440306102c104c030f014014007400480240c6110810900c80705d00d6240c0132807940b415046611401c02e00100390311410104c1d0940d441e05402041d4014035007090b6010784884805103401c256140000c000740981940220b0004608a43f070450015403408990400d407004201c0148815041010380300254410307006800b40510f149a41a4aa50300e0700c0b01401c1040703901801000c104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 764740845 1250 764739595 764739601
    0x300f140c0a0302090f06011407060c0f0c0203030904090302071206051e1e0714210106020714091504020a050a0e04060e01030b0a0608010513150b060a081306020301030b 74
    0x20040c0084494120181c500081440c40e54001030000400034000c124126020030114816074482c1d00c0e40341c055a0220b803055560141703031418400400c1c0281d850780004a80f840c1c808426807003840111001a001002581000300110800000340400c075012019441424030024455140005065040d8000c5100051070724041c00c140c0d0004c00040040240d1800c5c901c00c004620900f9100c40d66011850584480a903858050995440001300070400c0c400c403011178001140400c10b0007144040e07407608080811070340d80b5002130382d6840082c000c4d0100d004040c44140701909100f03900545c40020b2041e04e1001c0801d0703c010a00300d071b1009c0074141c001f41e0002003445800340c1202c0b10540e000303402d49042017000c1c0342c809407201109041c04002c04410114000c1080c80465802c01d001411a0754020020303400c081c054180600c103100c00840d2071042003400c002c64850140f2503880d03500805002d0034a02800341c20200d03012034004264508103120100014042804c903c043c43c00703944242c02c0089241 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 764742095 1250 764740845 764740883
    0x30201030b040b281a09010318080a0f0315300c030605060d05011b02160e0a020c030d0c0302090a05060325090e090c1207300f 56
    0xa00780c0303180d442c0240d04010320304503191212240392007401c81a458001030f602c0442d10501e42c1d18501d5100b40506a00e04400400c0c0903441c0b402488610400d8808005c00750b114005e51511b002040005400703080f041c040e120041e4082c0b1006a500f0455280002d01c00e030116032412980c0c0c00d1600060910111070180107080254010a85180c0824284403005100180e80d145001c440c5c50000074903450702c800c041a45038540800d20b480255010000740649040901e2905151a810021500501c600c0d10340102c4448008480c005a800000104400360390b2100004060b60049009401a100c108a00810480b1520030312010401c13030381c0c1c0541e45e500da02081000408407500510f00c0342d4030400c10b00003a0580114040040080c07890003a91aa921003001d0302c440050758820f0660307042d43c10400611176004260034001d90003c0b0b900715081000d440d9529a500306500680d24003c03110310080352980060a009246401a0b4014000700d10580c0e840e04141e04418400300d881e07080e25100324002c0c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 764743345 1250 764742095 764742101
    0x15020901030b090c070606170d210e0625051b0c06070b0a110913150f080f0d05070f320303100611071e0902031305060717070f2703020103 61
    0x81040e05e80702510100d0008c0ea2a0701c681d2000304400910200d040000c0340075500284601c0083c1103a60208407002e01c8100181d10740d84200c4000c03041c0703101d0705110b5039020381c1d848000105106035900d1904207282e01e00c0d607112186260100302c1440c0b00780201001c041c1d44400c01004440c1c4941a040c0c41418503514980c1924040c41414080031014010b103a0291242005550600405074000c95911522045c0303240340441074100b0400d4102207180071685481c0040e400d649550040d08440700080810411075007406000f41c02880f80742040c0000010803024010006801b00039108100c6081e0055580d001355145001050000d030808420030201c5035426452000524240c1851003502880c0c02c0c1f2152120b0040c01441303441c95070021110b400305002d200b0307a4060244034030300715901c4c14001c0d0041807a803a1303504121802d1065500103080c0c140315007000043e04e88903209030340561701c1e00c40007554244614030300c01041100000b4000307540b02c80c010240100741c40074054400c3c2c0a003180001000c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 764744595 1250 764743345 764743349
    0x403091d0412230a03060e0c09031f1b090302180403050a050d02040302091513110301030f0303090b180d020105010807051908010c081e0415020901030b090c070606 72
    0x2001980038204008a2009681c0107403240e000c1c5406415440701580d19840070141900361480964040b0313441901d10b03010b5000205640800d144ca1b00560f941c905038450507ca001c450542640140001d1249440d0f1403c450241e86004170001c0343c80b0120311341d84030301c4c0e00d0105203a00000d9494503040040d170421054054501030103480e441c00c1d5240c5914003512511801d144401004030000b6060440741095050303d020b1a4010007501460030419060345684040300f55662003100c51900840115a09200364502082d2440080c1d0940e8a1600e80c14050280e01206a003410340303c1d114800002c0e64180c10034410340140204a03254550780c03035410314048201000740191782c9004018007004c0000a21841180c0084440c940e28180648040301020501d0740f2103c415030038120b01a00250300b141c0314134443e0720390100102d05980085c00743c1c2c8605905440140c103500d046004101e0700348458004061941e07047c1804500c900d0098081000f18100302c8108807040b03004101c040402c030f818090300c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 764745845 1250 764744595 764744639
    0xb0405010b0901020a1e0209041109130309091112040629150a110d0507111c111903050105041103070620161412010c09032405040309 59
    0x30600a82c2c0780040d5640c482e50390060309900c0d03c4084c04800c0f0244480031904140c0c040c0160035682445e01e4406040307418240d160b480741d048000045e500c042e244252100b81c40c2c141c0c0e500380c009032805580b18000c254029021918490422008001521030148640541d00c0ba50000681d015405401e004001e50704003180300c89100c1c05902c400313540da03031201c0001c440450a4000c0e61615011000c0e15010b00c440340d42880c41c040c0304603032800d56400c440581591405402d82240c5075110f0810081781128400c00034103035401c040e14600c00704100140100c840c0c0d0b005032012074900b51030301c451203080b80705500803243d50f03455004210802482c0d55100417091001d43c0107003103031403c010001c2d181608040206103607408000300e4148140c800c000b180015080725410340c940c152a086140800c030b00714010f050150754041c00035560a54140302c0c0000c68045c940d43c0110341c90850780c030010040700803800340c881c0345204440d140c4414603610506000743e02c2926085c1390f407031500002100031462920440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 764747095 1250 764745845 764745847
    0xc01150b1c02090a0323061f0510080109050717091608030901020c121011030a0e0c01120b0105040302030d090e0c0c0d0e0d0f03080106021b030705061e0d0b0405010b 73
    0x72074807040d11803000e8941c05540b0300114603440c445640c00700a1074090000c240b0840007404003016a0416088401e08c800080b00002500e0b034090195882e1040d0200c00007034203a50040000c06615070084e07030072040718a0700001e400302404405000364816030b8580400d0300444284014100d1b040c0c0554010b0840d02c0146d418402d4100000c1d440d41640920700d8051100c21b800d0209403401400024403218104030100130580d0250070300581c1c0e400848544e0340b05445d06443c201a044005040088110140d5941c089030306036811940113041e1080490341444420712020006079000d00210790408016a00c20405520344510382844d84e901900c2003103190350030000c9020150002ca8245c01c1c0318864101410040c4c40740d00814901c81440c800942507038481d0701c8006c105035000104a04941c240d508403401c00803401521804020040b190b181c0c0342d800484100203e00300034000d481c43d82001c1d01c003400e60700481540468541d000d00e003c1c2d041681c0c0d84201a0316072401344a1030307001d00000384860b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 764748201 1106 764747095 764747107
    0x1a0a0c2301022104050606190306020d02090a06050705030414120303090c10030c0905040f0b1e090c0405010e0d11040f060905070503060a0303050c01150b1c02 70
    0x40b10f5810702901d4860542c0314a078607410300031038028000d01055129502003103001d0501522052030700310010310002c081180e500c050040f00041c0c80e03026070344803407403010002a00202e42044090000174010340e8081000001034400380d031807060085881e4041480050301e02d5030311540c09500c0d40300001c2045101c0c2c4000c02c4251004001b920352140c0614440c1c8107500345c5030407042107000500c030b801c000c007d18905904022660724154500144045002000c80d21180d401060308020030007009210089041928005a0003105140744909103410320000a007601d0703c80c0003052180c003c05082100388400d200301c0004400c00100100000e181e85802100600001e00c02c0002842c0f400c1c0000381140d000b201240e00c1004000d0103064982d00315075043d121600072081c1c40703060b0340da2401c01d903203004c400705810310180100c04001a1180003052a00c40500302500501d60800d00501c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 764568345 764748201 := by
  have h0 := BRFrame.cov_init 764568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 764568345 ≤ n) (h2 : n < 764748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
