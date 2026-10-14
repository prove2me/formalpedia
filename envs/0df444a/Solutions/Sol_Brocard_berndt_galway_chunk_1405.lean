-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1405
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:49:17.694094+00:00
-- url     : https://prove2.me/submissions/29007c00-c276-4ba6-96d0-5211c16f00fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 252517985 ≤ n < 252697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 252519235 1250 252517985 252518003
    0x11d0616150c233009070614090f030a0b0f010312030b0d060c022a0a06141917150306060102010e03040509040c0302060403030f020c0405070c240203070504081204050d 74
    0x50140c01c120202c0e010902e0401d80c64a9010200751310546422261284000c0000e4075806a210f82045034400c4200d4101d14a03580180b04d102d0f281c4c6008050820302c1e00c0e0040c2214501ca07020b03074400c000c82a0482d17141c204004414010030900c0b11204a054205111f0b26003000604542000611000170450020708240c0e525120540d105008010111845100c44d003421040e200301ca14100c801d90300890640d00552070700740001007041c00341a8905402c501031416500300303076aa0400e0025a07050301e02200401682c40054080609940700d02800341c0c02440d200c80381030a4001c1454500354002d40b05504680c544007443c0600880031094800780e82e030032141c040d8907403107508180c4118403464001941c015030000d0f000040540154140000c0101c0b6002c0c2d6401404000c1000101c4d4000c071021004036100342010300020700b6035880e0103890744585552140d5021620b20380c3c001c981003101c008002c0b907000581842101400c222081020301300321402490320b030030030004c0341c07030071400030b40081503da1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 252520485 1250 252519235 252519247
    0x50105060d0f0b090108010207020a0b0301030c0e0702190303050906070e06030123040f09020108010f08061513050405241b0a17040f0b0c0306011d0616150c23 70
    0x16410143d520791006107004032a5031076031003580c002d50007040d040388581200140010030800e02d0741030300d04898002000c00112440e1900032080340a006200d0300440c0100303c1d02488550f060a041c003048ac0c02540c0024191600356046450000050000e0050200724160101e00d9612241140d0548001c400e03900c0b8400524043d60101089900803180d0042c24007907181c00c1c03000207500041c40203000342d9400e0500e9907079003000f44008001d8010500203800840001d43c0041d524a02800300c0070014100c80004404140c10008881c001d44040f111034008414070402c481d001e02003507021000345603034945a0300b0312001c0355102c5c10700b0201030700f9030340c10100702501d00718001c03e0100d0310803c451180249500e018944603e40c1c040c0310604840851080d03001c94401104401581d10901040c2c4130341d500c8000241c1818204206901001d6001c0f10412000c21a580d000c1d0a1421f81c030721810317000d40301c44040d11400c010b6030040090f40c020071500b80300381c203200c940c10071890610000080c0034641d101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 252521735 1250 252520485 252520511
    0x170d0315080a121403040c1202180a050402090114010c020d0f051507090b190c080d1107050607021606080405010f060611070807060c0308090118120e0301050105060d 73
    0x260321580064480d000c0c9602c4102441100c0e080c0d00000066640d82c0c5481565180e00044a8001924007500b03040e40781d80d0030b0011007014102420868001000c0b500c0070680302c2c41d8a03495280803141d203030009864400740000c5040c00b0340004e016001030078169144041030400240740e117810300c801034820500310181d5802d01119517251840d650300a0140d4a0b0444402448400100156100c0b00042d6031b4400c0040d120a4078801d45040507030300c00003d600044030703007000c840a010340d1905841c504000c010007072400d6000d00c0380000b030a80c1c044000780c41d20300d14200942040c50007007d02041d5080501c3c0401b034198030301c8504045e0360311070501c1c15058071a400e1203401450496243c000f10307890820041403090300250901c0d20103110804440500780c840d60240d890b811580324001c0801c413054100000280606406a80480ba4000001c3e5882c1e202e03160b0f018129254405070380480740881c02007121a8800c51080305010141d000b40510751500010071040d108001e044c035200785e92000011500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 252522985 1250 252521735 252521771
    0x1b03160807060902061927060f090918030905040608071205030c03030f010510090b03060d0305070807030f09080c0307060309050c0907090f09050c0a050901020a060c18170d03 77
    0x601d4024020795100c445460503041c80345500c0e10500d0114848542e070940021141801d055844c045c5101d07d05c256150000988280b135184901400340176040030041b4400318180f080400841c0001c070000465040b81c100940740c0321264000a001c1d1b030a1603001c2c01315400020b40c07030040ba060100000040610703400d0140c214050000c960803d4000082400358003945042030700c1c140c0d00c3c11a8806d000000c000380540e0210401d229072900c040c07040c400964103140101d0892800c50107130900380c0c41c004990f43c07180300c2544118001c4022451240100001551101510f80540042c00080c60500b801000003640c546081c031400080603142d84440c0708005042c80980c082c014080e001c024142003411000d000d0001c140110100503c4c05403000032941240e01500707014161031000a803804038000002c0b1015030144401a05506c1500c0011002446034401c51000840c0c1e690744d2800e030440c41c0110b4400510540c00031203400c11450380c4d508048000718085858828a007400140821004809015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 252524235 1250 252522985 252523001
    0x5060307090b031e01060206090a1209090f020c07050a270207060218030d03091a0421020f070e3303070603091b030302070b0d020d020705031b0316080706 68
    0x2c42000482805a40081140864800c90415803050742c4c907038a40e403080f81c0c2c0d403208882500899104100741400b28074100808882d5aa4038605203071500d1b110f624001c00c2d18450740444013081e50005558206501c00e1080102501044610300d101341c1c03805d103841c8100c0000140000c40c44650751040240108141d048601060340a0b81c29519807a12802d010074052041c507076a4000d000b20040e041e100c5100348100c10300345074460f400c0030440c030105031000a0303240c000744219101c40e1610100032200310310042d00e405400760781d03005060015250b0100c1d801c2000c2030307001c0c0c01c1c503074141d4040c011903074006404030360740d0280c581d06503a540141b0140ca03c0611409100b141d0540036001002c0b841944c55004558043e0045080012007401c00c503520381d0500b030500c0041c0050b0800038051014501ca50010300c0c495819403409800c02400c004200204c1c0e003e4401119190310002d0780350036407251102241d05d0200e030030700510b0410500c3c0e18015180030500700010b001b0b01000440c2001c01091780d1103101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 252525485 1250 252524235 252524249
    0x3050d061d06041406060703030b04140103140c0315060103180606260601050f0603090705150c160806060103110412060b09181b030c19090b0a0506040506030709 71
    0x32038000c0340611000340500303440e21030040b41480c1601510b481c07894441800717160080d0020b85011869182107004003850039410381c0c019100c0c0c2c04e400a003203c0b0041b180c041c50140c40e001005128050000d80b0b402e00e41012a40650032410404008501103015a58061028240170481c5010000164520341e40b0074401403506140120100394810040200b5040c442c0c0d80b0001603040c130780d199456076180030034801e90740d1210480b4031000a50a0410145410500200864041940f658000f0342c000c01c4000038000c01f01c00204041c00c03010400c1007080300300700d40c54032095070f043d04100c44192181c0e0020404c1e0705041c1c946042015420101007210010134420701d0f14074021843d0f15040010b44180500b140c030840c09040444d002c00d00145c81040c0b5811004000e2450b20030b0303040f110981481c1c00511907418011000c00d24036580341c104e070890550f0100010f00ca91141820000421288081003084c050b5102c0c103802d02407510303031404460a949040390856180d03a502e00007110410441d0308404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 252526735 1250 252525485 252525509
    0x150e0d03050307180b070807020a0e01031a06040902150a02070308040801020409060608090a06090606050301020a0807020118020904080c0c0a030521031312031b0c110d0f03050d06 79
    0x240616034000003840c014985030b0b07110f8601c002402e035038000b42500c070f004600d40720700208254000079540f68000d20303245201822800301c160752a280586143d00990095490307401c040c0707030440c4550304404020342c04a070441d01084015115004110a10091605003100d0700c40014000300690080002c203000310350003086256500c1d00c60181d28081d40084c45094500c908001000c181c41e4010b826480c8216940c20081c081074100d512903802404c80e6840945040741e03520004100ca48081c002000218400c5c0c0750382c0180e0034020402801c45a80020001e880741a840f4540700607518400081c2c1c0040c2c128500f1510750310f4081c0001c1c101184001156802000648004100040412866074112014000b01c6100b5841c618540d120300c000c41e441042d5078090820800000c1c0600c000c010700320180d150008503400890a145140040f24403140041b4511401c00c204015039100d41c03a6410100362030b800603402a07540d800d1742c0300700c210b0b4000f410b210002c101d0810815580e0b210100604604c1444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 252527985 1250 252526735 252526759
    0x603260d0204090b090112050d050d06090501080d1101060b160c0503010c0809010f05070903060e01090c060905130c0e060c010b0310090311060108030f13030206121905060a150e 78
    0x1007004080704c04903240144500000001d451f4085085050759079088006405808002901102c0781e511031030718101d50503074030b00c0c01290010703440c81402d000e030555200a100c1099001c0001e44241650084010203038100380c0148003d21901055a03074500324108895908007551402806010040d000180c2561130140011110755000b20030601a41010001300050084994031005a842c111000e2000c501e025004000065040c0e110050061310000005034086060356603030450542507100100060005006100e2450300c000c00704c0f000c07c10400c080080707902140300503100b0424810300910404001c200d070b002c4110203401c02e01074074070b00038196044400034001c0f04004100290096002405003040d25040c41400138280f4140c64840b0011414000701040d0840c10764841c40302003907211205070700000140c8544014046207145808000c0d914502a046102002454000c3c0400c40382850305201042c2c480024000035141c2d0065090f000443d80c1c44259094807080240d142c001c00140f41e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 252529235 1250 252527985 252527999
    0x60305100b12030901091202133611090c040819030905030606090123040e100b0d03172d040605010b0c06010b031302130b130603260d0204 61
    0x9641070030021078990b480c901c50a01003a581c2d001c0d00c01c4050100da50301c0010b0100e000c0900c800840309100408103c0010a000d0304a01036841c0b5190300761050808903840c10581c24423885032001d00244002503100d00c00c00b6160540901090b0407100c0c0078042060101d482018801c3c1128081c080c00000c50b15002c50920540c002510700c0036040d03001999500b4080351901c0d0202d06180610002006007616074244503c03403000c10f0a40d4010702c14418203180780c50280d01e9500400910840180140c001c21465007405001d803003810030060300c610306d40c00001d40001d400400307110743c0995000031034182e95195241008003000030a07500c0c100005103001d541c2e5409408102511803480f9050a0045e40d0f65100306000c54003038180052001c1d04644014004054010084c40d400381503d185200e280d061600821002180071135804505a2503030283c00d06404d2602500340240d01c0380000f0003a551660b2200d80700c924801d22800b807101c868441482c1e00c412440d069401d0605928011503a4a5803110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 252530485 1250 252529235 252529241
    0x80706030b0a05031f0e0d0e090f0603060403030b061c050402040e0102160305070f0210050408061b070f020127090b0411030403140c010c030e010e0c03030d0c0306030510 75
    0x2148000107810807030300510300c1c200030003040225035001d00142400700020003141c1c070307070310b0004040203006945908140c804403040001209481030381e1100c0c1c150b00300c02e03401d0044d086d030010040000c40c96250240001501c0000d0b8050b401501440c001441c528a070002880c030340308070015091418030480020680980a522090045108450401c0070181c04041c1c6130a03406821410305200800202810100c1d020303000411203144241100207910100b6400120011180300c94a000114081014004038104200c09904030700d080f16096070b40c6440030150f9420348500030004042212140c041c104690144240d103039000b0900480c0c4c0c01c0c884030b070300c2c080c40076284621406128a0800e51800238504203441562100b05400c0403140c511743c2c0d41d84040d0f414000c441c0c0104c1c401d210800102c5d0b03440d82d007031150070039a151998011600a4080c0080c609503016494524581d400400c080c80541ea03001048515000d124071011070542c28003107082d001012641d0014069001c0d00803249108a0254 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 252531735 1250 252530485 252530489
    0x22104090b030a0c050f130203010602030714010902060702010f020f06070e010e04051e070203190801032a0312030207080706060503070b030903070b0402040b0d060c020c100206130c0308040807 85
    0x410401c144440801010f682e0100b00c80003a1200c0c801100600c810b09107100304082064010301a2610b4030030210702c01c82280d0003684440300580020410b4420081c0c0e8801e802414000e1000a00c2030445030340000b0300c5440b42c4100203050109400355080c0490090200380314210420060b035580c0c0c60b040750007420081e41d070b0300c00138006000c260a060081c0361501c03580e4011800301c90100c0315095000800075481e2400790a520551000f0300c00c200051850407082c501c50301c00c0769100d040d59459440c2518014002681c50707014400e425410400b0700c0d0f100064070702202d802c01050084003a1b1008260028031405202070400000003e02d0000e100aa40107042110000d8040b1140a5511100b01e403075804295500c540d00d4000b00b11f65004034041d40d4500340c006000070070010b542076020000074030b607800d401003c440180d04d5480c0501c0071a010701c0000d00700076050751908801e0744240740c000d407a09801000314165010414030b50007801840414a0003856024929030368454503035151603075420b030364 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 252532985 1250 252531735 252531749
    0x5040f0203010c02072301020708060420060c03030402010804020f0310091403030106120e010b090109051b090d032a050318030c1c03180b0903060f09060c0a022104 72
    0x4807043e400c184009241c01c00c80340c2d070180c0480031040c0307a04c0c0f11030102d41c6910721a045100d18200401d2480c410b11640c1c0c0124880c1c11010b00c800591144090b12007007100700340e481400c0c2070190840c83c00c00401100d901071741c2440c090245581c1c0b44002103581042c1d0060681510408101d0400c002d2240d005215090180c00b0108461220504070355880c0300900511001500480c1000164481900114000500c4000114a0102a0000c5000d04909a100c41c4c51607072643d09200703180d010b456000b0089403800e94068a00913030900403482030040f28030001d04000d54800005101c41c0c54160344008110b1001d410420941c180c241695290440c1120001e0612404400790701403030002550340c1c5880c009002c051184d40b0203103654660728a284810ba042c0503c1d010b5040da10154003106030003403c40841060f440d1010403040c585013100042200000c072114906010a0f1640003501030b07404440300d100350342c0d103030060742c0100c1c20040c0d81e21200722a21000107415901049480140080d2500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 252534235 1250 252532985 252532991
    0xd060f08010b01030f0b01020c09151c060e0106030201051909051f080112020d06240b04140d020d11010c0b072d080a05060307030212010504110604030519060f05040f020301 76
    0x403800c64408441b84c500350f003405684088e2140c58103090946035680d01104210401510450303142c0805c0000745c1c8103582c04140c072485190310042103018455a0112a1248000c0080500316400030707203548190400d24105215182d220020140b00701285005005c010f0800d500d0f000d590207128605403c0c0356400c401040d000000401c00d25200c5030050503460300200000b8200308291601c030001e114540f50b07110500b500c1c2c05084145c200101c454001852098210790703445250407074104c68415420011446001e181d008100981d9955542643c040c0d0000c08100340c0101420040c0c48400d4007031001055920030504111609800c08102c0c1481da00640340701c15140800f100e218041c101e0b800840000c5102400421000d030560f070300c00360740810090100c9403034a890b60001070076035480f5100404142c0d16081003008008030b64003452040780080e40d485040070704540c0c0d030365151030507402e020780d03040021181c2c4428411607800c40100c0a44000c000c101c40c0c01c01e070502d1640b003883d10303030240d0103903003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 252535485 1250 252534235 252534251
    0x306040507020307082205100804170c0a171606020c0d0e030d200a1b0f060522181b0f0207030206160b16030c0c020609060d060f08010b0103 62
    0x2002001300d840c07070303988013206501e011045c20400184404282e003803a240704d211040420f01c0c2c6c54010400352600f419484588407464280f410307801c0d840b450198603007502414000e012000c807000454400042d80007000d440b40745021050900e40340540308541c1d03494003415001c8800d1101d10742c0200f8030490b28000341c4080754840d0340c00345d8000e070070644081c3d050340c41304848034080c6129142c0c0380e2418014a441d2103142008100140c80d205d807404086d116148000c01d40c4403903004c0c00101da0010311440003000c401a20340400a8003d0007410400400103514100c04034806e810740011402508881d1003001880041c0500c440050000224441c184089440348020407405000e260300d800130154010042c5a055a00780503445d00b240306049078000c4400c4884000500c1c40722801c1c89170650004000c07442d42040801001d41e01000e0984043c808010303400310140e00d5200031188880c070103860903913480c0c090308141e038020440c07603204c0d0081c0c142d4101d02060a10040d003003004041001d80c1c1c1801651 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 252536735 1250 252535485 252535487
    0x4030b0f06060f09030c060a03020d0b0a080601170f070f0303081b030c1605030a030509060f0103050c1002030d06060306050a0e061e030a060c09061e081504020412080306040507 78
    0x2000c1e642141d02071018804620740191003c0100b00c420b002600341c490320004c1001054064001c0866000826008550102404490320900c030703218008840300e180c0d86141c2615152220f07418062031400d02100080350003101c2d410081104101c10300012206865961b04450701d0b44141030108900042d0b0720404283c801414145520012512642440c03864030b80ca022130009512540000d412146070142d91703c0070171b0f03090002d0008070089490104161410400c41c501300030004080c9004402e1040042c804541d0005200c0340c1c010040e41c3e08210710022180070b901d103004940301220150b0030490045010f60307041d00078070308851081d41c10050361621211030408403102210388542180c1e8412407a11407203030340100d403d0b01c00000f40c00d0324021040e503156441524420804400415541001000280d49c010003c024014410074003501441c0814402400c03014007402524071540a201055491380c0d59504682c024102c007003941d0545a16450009056002140c05522980c80c1400151090f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 252537985 1250 252536735 252536761
    0x31b0c061d010f08060109050d08070c0b030408270d050709110903060c0a090e010b040602100606021506040213081f090221240a0c0e0a0303110c09040804030b 70
    0x1840c0c05849100341071410f240200c0701032100800c07160421203020000111a10746088409113213015014035a601d072110b003000710b180c0ca502da0003a582507408104102c00700d4415410b81da04076905414a00500da1041a10722107030380d0081e0b115a018040144240c04c11400180e442c00311020240244240200a035210503d401030388880d5800da0031040002e160f600f48080241103442c100d0030300003541a160403101c01503001c00d0f0484020b50f100041c0038801c940e0100480c000c4220b60600c1800160b0411000075121540ca01c2954204518200418a15901d0341c0548000c0c4040c040000701c0c080c3d945006681c0c0ea115800c860300f2200c11420503c0c50002180a5215040d0b0054600308000350b4401c2543c00c5122a6245240140100201094150100c280c250620540d11740c4107002c41c10940000e00890f4a0701900b4018030003401c1c54080d05440380c41103030701141d4041c100380048c0044480001d080c1110340703120b01d074002c4442e8100700c20440d400c2e002c0c10a480c082c0d10449100d45d40c00e0440014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 252539235 1250 252537985 252538037
    0x7170a0f290f060409020f0c01021215090112060b1816180605091c0b0c09210d030c0c050601060206100603140a0f09020310050a140103150504031b0c06 67
    0x18410130081c041c4c5e0540e03070000c0c4001d80c0718020807403030140c0d00308240d400ca03000b40403850705844040c07003400700755080744001400a400c1210805503a5140c20003083c194801004010896600c3e0046101e469480c440721745071034030350300d40f10f1002460044000d621040034000681c0100e07280e4026034445250140c40311060394000e881c2e1a00d0080c0c031008100d29a01c4020f01c421140499950040c0000d0003104ca0900130000d2102060b01e600c0310904000e9420354064084104405150481d910138000003081c12000031030b03050000e80720005400c221004d00c54118003603c01d02c28240005045a800555588164148000c0e1003083d6103a460407003e4031040b40c5402c19028a041c04601da281d6650b00a0780f4810010f000011408101da0109040c000d04600301041550340e0001c1000b54606801800020206c15142c240c9540c11559140246a1000741c81c07a00a40d84400080405018404010280308416854418040149040d1540007421b01403180000ca07101c22203203071000782010300c600b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 252540485 1250 252539235 252539239
    0x406080d140309060106110a060c050a03060503011404032003071203050907080d0f110d020d0e03010e10020717030a020a02011b0c35130e07170a0f290f 67
    0xb201c0e46071003402c44a842d080f00700791f8a14000c0c014444000740c180e11920400240b90385642c0c1d1945503500700541218500e50005003c0d1f41020754981070314983e0f140c4294000c0d41405c141300e1041070a04d1043d18a500101c50403051706c4000340c814140703e481c41040c1480c414a40c0c003030000365140c0d0320079600d60280e4440c508140c0d00c070b8026946014011802e07646102c000d40350808110880c0d0035030500d40411004480c0158202280310084654003903a0518000070540090228000e40003081d6034800c2d11108924006501003029000c12180144a20807102d103850141e03164201452994001e50200c032601b805076180c803030301d03441c80f0031810070040d820406600d0301009103a40c0d40f03400c01001850382c90401000c2200c1c4003460158a40c424600000541d0308910391603400180011480d40903580185041000003410484096800040c015542c1040c0d02c40040944a42001001034000800200708807400e00c5c040c40106417040e1404140301c1107440d50810039096100922005180080581e0707 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 252541735 1250 252540485 252540493
    0x2040b120303070c0201031401091d0303090c0d020d02060408060f0f010f09020a09031709120304050306010b070c05041107021309170a0c02060301030b100605030129090406080d140309 81
    0xc0c0c0f07940c1c00780c0c60500f4194010b04000c0b501d0341c8a1510001e07480d409030000140a96941003c4100c41240c080075002602000001c503c0d40c18031144032599a0711100f0003600c20610560590115260003e100c40082d601800351074849850317043d0140c03110000c07a0303d48050b060003400034030030900d4404418122010740755000c2100741807603036250107540301c10110340070b03c0074041e00000011000e08200780d11142841c0d804c0d842e00003840412045880e03d62020640e80c0c003e02050169030340c007054460446054980f283c6e5210518500610b1040c40e661260703510138642800d904e00e400b040c500404005100300e4401d1387d0031115801030070441c0c50800003d044002482c0b041c501110030000108843e4000d4100414500b105078001501a842600102d500d6401c04050180c081c03000081c8801a01032402e00320305543c148130001c40c0c40642d940260007515100c0495480d0b40c18603100b04c8416a001500a0080760b854245c0c60340d903005103071071940c0011080046c03042c5100307840d41503a00420108011b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 252542985 1250 252541735 252541741
    0x504030f06020306061b060105040f0b0f010c020a0b0d0504060b0108190e0a0b010b07060c080415050c041e050a080a03080103080d0204180504050d081e0c0f0703090302040b120303 79
    0xa1002900300a21445d04010108030310003079120b400300b0101510068000a001640c1010144000d44003244515013005091003007401c419a188581400208000e10300701c0d801c031500e0700004a81d515507510100101000203200503c503000381c3c000311300c1280640014000c04208100440d000601120484502403880e0341e00c800420041d0010141c4524007030441d0102651a2220302c002d401c2a0307c901f05400000407020708021083c00303811204a0135050120a81c40d00340c64012000c03100c0c82201d00c0440d510350008c0c0b4000004400e41d4080d14800102c040c1c0c05070481c8925523840c80900446201d0900824005400140050030b20900c0da0b05540341e010356440e56559410540006082c00a540c4d024480840c00c0000703103600303040407102d4070030104480c1440d041850410a5000b017080402844030100040c00420400784030719078000560b00750850350350004d4104180550a03168440c100002124824146c1c00705241c0c00340c038001c490420115540908000009640030340135a00c5410074800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 252544235 1250 252542985 252542993
    0x11010c0b13032304091410030b1017061009050108030a050906040b030c071205120403050c010905070f080105060402191202040b071208061905120f010906020c0d0504030f 75
    0x1507525154480d0400681d0708010103000001a1a9411a14800e40300414100402443d500a410000412108207a92828140e100644120881c0400360049081c0d8000c10700018600c00090001c01c401c813800061600205440d54076540c080c0c0314204603041103413001c01c40411610966040302c0c03580000394a03104085600b0f40301500207061040e84204248000201c403036070400114031403400300175074a507074900304d29001030f0407803459001d41c0400c403090015206080c210865075800a415061550300c0d1b0040703600301c0713025044e00c0c10028002c0c000c054000800c403000122620540b0f0f40f201c002e1103d0760f00c000034041240035001c1206124410701d8900c0070001e00402d8031406a0740512405440c00d0344414018807903501400342140d00c20740004040d007003154420200c030340103002100c00c1c80f40d2a400e0303d1a0f0300a802103000d414403500071020080000002005180c04955000c0d009100400300e40c14600d00a41003a03005a045000701a00861101c1c440c2d8100c40590f54401540e20b480601a16 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 252545485 1250 252544235 252544261
    0x7060c0c03051005041b0501050405010507080d0e010e1b03030306060307110601080309010f080417030c1c020703020f06160305100302063405060604090215031311010c0b 75
    0x503110340c40148408400b042091000186050200d6404216401c04c1d26041c200500110000c02440d00c080798244116a8001d048504451091a00c0b030b888030101e007041c4140b0b11400300348003e894a4a0940c10740528103401880480241d901518500060344d0600b0f5038001c166820503030f16401c200002105440e0110241d50841e9040c9410108640c160780d11038684002a04404055440402c1c40078080da44684091201049442c0010090400d5139940c00d2407600f10100344084040400001e80b65440d48040d1518a0582d4008030400142d94520200940c0f001c5000e400500030041d80c1d004031000005c03d54060b40340e42d09024915990700c0c104400500000d491b01000c580030020000250707072068040e203003251085c0c2d40101d140030400c0401c0c4840134604001c50303800d9810701480001c03440c0030a4040d4020307000d90340400c2c050964400150701401d1000d0207144840040144528610150708121009100b15100e50184180e0001940e00c1c401c01d40b80144580c0e800e030001442000c0d121 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 252546735 1250 252545485 252545507
    0xb0319140c09040b0a050c1824040e091005071418060403120e10090302120a0209010b030403030e0a02090a1503020a1806050a050f101704030c0b0601020f0706 70
    0x4191220303010000d0010302c000e4001d48050340d04441d20401d000740384409103d1240c100d048614a5807504003203028030201c00e404aa5041c1c0705400c1d81590848400401000002e044054500307695075903100d03002c2c6c402d0128152444045445890b0402582c45601d1084500443c07039a19403181c41c1d28500590112640300303007103440711400403101c650281d0325914050009107100d601c00c003c2d80940d00c040204902d105910f41481aa180c1e41096103080c0c10188000a40340c069580c220081c074641841480c003201441c00a42107541c0d0000001c2a031100c401460246229982c1402181620020141d4814244102952000c404800b0941c801015809050710100201029850071740c0c0b90002003000000703a0201c0e0f20703a03200318010026001c1a01c40c00e00a03000c11141880e900c1d0030000070908805503454100c0c0030b01ca8000b500c00c0c0d441d0056090300e58540600094010910781807600920051703a90008580b02c006070700100344690700200301c0d840da0341700d031000070442580780074030840b1440300071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 252547985 1250 252546735 252546773
    0x906030405150a0b09060d0803060103111306090602371103101d0f030406050a11030403061e0513060209040902030f010e150c0d0915050a050a0b0319 66
    0x440d448001c00403045400070300c59980710070f001980314600303400d000f01214018101da10a05e0b0200703103400000c1c1c8582c1902d800c03100030310340000c1c4010021181101c52003140b104803402c21400400040342e42c9e102010201b070b524503a00766200e84d1854a105c43d80061003100700a001e0b01c0203501b01e6200b1120b1440c200d9014000c00d06007601180b0040800e08001040c0d0f10060b40300d46810b4130035500b0050b49000c0100140102c0140a56450130b0030842d1a1300560040e0020400005040c6002610400390420a166440d064950b5940c0d01d1810b8401485080c0c40b070304015003c0e40e031045054200d03210301d40c81303005030b02c0c10ba21110b5030540e2400004e5111040c050390140d520084800540c0701004421080d8108800008030000c00d000320610700b0313411141e401c030030388411400c109420032842e0968000704049440819011001c0c501101442d0584106001107880c0c1400c028082030542c120702d008d4413001034204142d1030f605040c5174860790040a554003541100c0282d1000424547c510a07540380700c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 252549235 1250 252547985 252547993
    0x62114090d2c0d06090f0b070c0305030a020c01150803070506070c0201050a0c020135010b130e060a0b07030e0a05011b02090a0b040603051e1506010c050a0519060f0905030906030405 80
    0x205070794000417144050420b41e1480c01400f903000030844c0207090207400036564240300c00004400d07a001005448014840c014098000c5008031041600b500840c6840100e40001502140c86014243d902c0c1c000180545051081d00c011400d542c2c060307200c8604858040c5d40711480d11000040582d4131000c0300c00201c0c1004600d091444041c0308004108101922034401c031007480d419030300020050103060700000b42c0c0020411050110a883c25401411201c0040c9038000541d40c140c00100408003ea1004c0c440040006250081540c06012a82828000c59003800515101c5c801110b58020840c80b00001c4c14105003203c0251070300c1c8000d5540044188008684104120041001d0f9421648102c2e290342c41181c0d03410b800306202c0c0f01001c0d101c0a80d00140f01c0d040b0041107560380d030000a80358a05010528907201d040c0103043c0010040303250007904a0f1500d0811a020b005ca910301014180c81c0e0900c0c0400c42d1454441c107010310f0f041641c20030000c0d410f2178808403c000250744090b00446071441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 252550485 1250 252549235 252549259
    0x605010e091303021204140a08012a030b180702150103030909020c0c03120a0206010e160f05090d0b010501110a2613030506180105070207062114090d2c 67
    0x17043c000810250180c003103a600c0a0341000188508002181c0214500b03034101600820094201d009210224420064925100d0340f41ca60640080c1043d6160940285480c0d6070f4007048038a515055001d401103a08842d041c0760400d2101c0148e031820302004001400c100400c200008864014100070b1074102d0980b84001d50940010749081003200004c0e02150012800140c00350b0140040e03801403181d101048568a0841c3d40d411034094460024000e00090f08112907044d0301c41d009555900f04041c04d00c210269003820200605642403040358005490311240d00209140480d080e41d2040e40300303600301d1b041c0c0800300c80c204c203016511401003402642030100c0b000d00b281c40b1030084025802607000e0051420039440d1a8030b203083c8d454081c81f071681480144400c0aa0020b0780c04110354a81c50000e5084942d61485640d804100204181c0c81b806c01b100901c010703a03070114050241030002c0895800c10009202034451320601001385e0213082d04020642e12100503490b405076540d000034007258070b681c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 252551735 1250 252550485 252550513
    0x10b030103140a0215301f0605120705040306020c06010302040e0a021e01020a0812191404020405100503100f0b030c1828020a02010c02010501270b0603090a03030605010e09130302 79
    0x4020111040d8000007010501c1f10000b0b0700f41c0135110b840303a24080c2010035801c00350b019043c0d11030f00382c2c918811410800000d80320b038810300640700550350106043d5550200c44078402e5640200b80000d0b0311891502c0303459526003200013508087d41750b014150b12185201a16030201014034810f00c0c5055018031400e40c80080c00c0c10005000f100c1c28082141e00c541400b171409217000e40e600300140c0141c3e00e0240c480180c600d2580049510607411903002c50700ea500c0032699158050150321903505032055104000741e800040c1c10805c07080b0a004010040100383c0ca0800d50b642c4105014142c220300c40c920045a0886040e405551000c09902d0000c4004030302e50400e2006100c20094207001580425603c41e05642030203642101d03103d40c4001d124075418041520340354007100084088017203210b00f18410207030042d00114180d490082c4000d403a071401c0040682c03160010602180081d140400120f410340c001c440b59504034602401c1c00381541c0c0e903841d242e030344207203a0302c6c064041d07104410b9420203103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 252552985 1250 252551735 252551797
    0x17091507080405010b032406011e02030a020613020d0311161424030114010e090a02130b0f12041e03050901090b03010e041209080105010b030103140a0215 68
    0x40c80d09503542086450241400c0d401c65552940840c480d41203212060051101c0090500740400e14600c0040152038840043e40d00c45108400f0300c0c109100c0d108644210b0340c012004d001c501d441038099403010380c1c8000314011101c6817180001c2d8000381c880f00c50000f1912900c04451801c4d007500407640c03070341c4441200c0e00c00402180d10400c0c0060400c0800e030b800c0e081841081040000d03140000c840400000140307045400140070324810b40d00040354580c2c05030701c0f07503002d01480c0f1000b624201c01810300d14001c001035480030310b008070510000200000c0d07813540d100c202c900400140c4001810858108240d0b003020001030810741d0180e501e01d4203400d050341c00080e441049846500e030030b0380c1e40c46400f0015000c2c510960203100c50300307810720040001c0001e1155040e400359100f406441544100740082d58048074a8200c003009600e00400071070a880c0b250006e40c180d03805814581c0c0c4078100100c0f00c2c0e9458110860084d00302208401d003001403004000984000744200000c801d908207548d07200884 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 252554235 1250 252552985 252552991
    0x102030f0c060703110702181b030103080a0306080703120e060405041406090c0c0604020d022805030c04022128151a03010b0307210b040e01020a170915 67
    0x1880d00400b05000e0469018071503500407a20844429052400540001e065401245144c848800c4200001400000b0000b43e07100c01109040b600780c1c0b01d5849041000f051340040c007003040800d14000c03002c1140d5000298250441e40d10160b904a442c0785440110b480c0d164840d03629400284c2440046900e41d124081c0800c0c107903400d14001c0c0c4526008081040060000d40412401780b01001284a840300109502d54030070303010741e44400500791074800302d04001201d0903c11394002e281c44044801e03044500c58041145c5044040355400704400381000102d01c1207070184140c4405c1880100c08013030241600691143c194407000200718001c030b1440e6038071012080340c0000da0784d56000d440908101c3e030700c000c00a00b041c102e0318040400c000201c0e51241c80b047c06404440c11003c03000840041c46101c0203001a0317203060500c0100445a01c3c190081c0c107141011501c61400c061540b55071060520998100d41003c0e980c0346a600740042004294ae4000b902d06207240c060580b1142da2a1480a65180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 252555485 1250 252554235 252554257
    0xa030602161203020306210c0306090a03081006050307080702070801061818050307080f070501060b0a030e0c03061501021908041a160303020c15010612060f0f0308090102030f 77
    0xc1003149803406120510102c11500141881072084c48a25124902e03285507525441c00d021650a004e8601c0c0c0f49031210b20758010b45c0c14850102040428140481c000b000315101e9206ca01302d9456030550112102c005005031000540240b000901e071381d02c15964188c02c2029401074540c00703070701c82e02c0301403d4694582140c7c07500802d44000210b2583c040c425510300c42c40240c01c1c1c10780b80b803456407038540b680305e1114068401c01d40801d8008080d03480104407410580e00c100200200340e80c6424010583e0891000307607012a190610000c40340001082c117481035070000700a880d907965981e80c0000d203004000c0009046205111070703110408040200710003034500401855031030701d18049002c101c1522412948a030400140841c0c00d2044192590556032035047c00c0250302d691003120304a103400810000801b010301d5500c00026115040918202401e444803000d01c00a80c6a030401403220b506e0307100c2d181d6615030740301c01007012503514409869032802c140306592903d034a03038002e41c41c1d5402c10340141d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 252556735 1250 252555485 252555517
    0x2040501090506030f01140a0b0a090c090303030b0301020c07051203070501112206050708030a0e03210601110703060509160803090405010f030317070e0d050a1101021504110a030602 80
    0x406882c0c104044450030011900030300107001f051059220f440c101a1500b031a060325540750020310340c0c510900c80090100300d0010007403030f0070240008010011b148019800309140c00035041c1d0300d0a06000300c1e03039003d4111000b4100f043c81c050510031404200c4000c0c190900040c495180020020f00981004805200c803240e125070f40080204640210000304020011007203030200705d0983c0180c241d1f0111504001c007980c40b0340c4d8001d2040b010b440404408121804002006d64560304036071054006030500b000890b00743c0d510ba2005450043c441030100245d6800041c08200203076054210b65841580307034044d61030025913541607024450560f00b10700c140c2c1e040440c4c160044d06051003480c3c0140444411514002d01e1a240901030b8208001034042140740203002075206405184000103181004d00040800b4455041c941d858070305040044807003031140000094175620014410080582018088000d5100c40e07443d03180076180d0362009038010702c000c0700c0080412000c0c4003400e502c50004a0700c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 252557985 1250 252556735 252556741
    0x50306060303040810020a09031509030e040c0903060b03150103081903050c0d090c0f09020403050f06060306220f0b18120f0d06050a080a140105070509090c07020405010905 76
    0x505164005100900a03031080c002000b40340b40004a4048490140318010781d02d1600d110203ea03111b01d250000b0703010010b61090402034840c258001d00ca02d074060790b508003589800004010030303914000f1000b0b00051070070b041070010590035030010702c4409008040390100e5110040d200b5003d0800d03801540c40c12008a8440500302c6100d4074504107c8103442d0400c00b514040040342114003400c8409001c5a80e00c040c0300d401c0110619011001c1c2006543c00d00c00b8031b13074449281000c0c5d842400121114003420358580200d400000d13005009440c000c000d00b0541c0d0b504460800e01e60401104044031840c2d10355044081542c80c080c0400c4940140261101450544a422481d0a0803050911254080d000086c81d108102c81600c96400758440415900c50b4518000340244c03c0307541000f607204501d120001628400000c00061040c41144040c11820180741501d00701d6004171442804a5000c00c00c00ca00c41c41c0030028280d2021032280b2440c285003283d004034045560036001150718595a20038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 252559235 1250 252557985 252557989
    0x50d1b060e0c031209091306090606090509011d03040b07080417030a111504140705040f090201090e0c0f090409051c020c03070609090f200d0f050105030a020d02151305 74
    0xc401000000602c0c428039090405d80840e82180005200246601170208040304004454100030f82950f00020244040c0381c44421074170003803005980906196190074030341e82c90400828543d440001c1d42c0c4008c0e50503d8584400c030000c0b1f50289000301d60b406820032000c101d580c1c104071000381e880440c100854039455080c4001d0991840c80b010034030160300403505500034004055840c1e61080c2d11004000b069404890f03000e1401c100340d0880d5074480d09040c0403404881d6194041c80719103000f640c485144035690a1740401c0d800b825641c54045070b80412060520030301c0030300204051640640006000c2145031680c6023482445204044030340c511015203040b41741e04000704840002c04034003910340c0601d032500152140c000741c1b1540c100d0544174a110607808113240c1c00312450851210144240c9001c0300404510f5034001c0f60b20300f24503450309101c8042c44001d886035078141d600140007040c0800300341c1c082210810ac0010102da100c0480c00b0760f0301040c070300c0c10082c0c0104c0703120003141c101d07480c18401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 252560485 1250 252559235 252559243
    0x315060f0e090607030b030f011a15090603010308070f08280e0d060f0e0607050417010501031515030618110612070807021504150507020109050d1b060e0c03 69
    0x404a41c440c901502800810440403650640101150400281c2000600080b0b8204080819202119403074144504000158414102d207101e40c11208400f60506080c45a070b003a00400c1d4441d608610180018070000713019900410005000d11050260b400690362560007030ba1100b440c142d440c0902007002001c000341c003817000881505c2c604040b070310b509940c0f020443e0884418809030210fa141c00304030001100507070140c1d140d61007030130580c0c1c030030305d000075025205034020301c40e09191103200400449201d6040c401c080c140d9a20810324001d2100316503401002e0800f205183c0d240e10303d601030020004e0030b80e02c40d2100b031044038942080034003e2800c4c859480070641c0d03080c1e4000c080400000440340d5007669160b50009043c1000c0b00d450300d03010300880c50b1002c00f091080340892818188428808140000c0490100820f000e2005d96940c5000301d00760b80b44000020300f1a0b00486075104200c0c022005104281c500000c001c00d210003541750700c42504c0d042400014680c010200c00ca420b800d0501c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 252561735 1250 252560485 252560489
    0xc070212010506130b04060b03070e0907080708010b03071803110a080109080d090309180b0a0b0903100c020f10090606050d0c030605071101090b10120b1504060315060f 74
    0x280080240f464040041100408600000c8050300c2e90342c0c1d0030f81030030b565542c032440180007080d240c1901da1400314000341058604c0c0300c038144103004000c0000d03100d6101d80502c52286582d0395030009142d103010f40200b207a4001034000414000700031098802c809580d04c94200030341c0280c104d0710221b42003000703000620b600e03600550485d034104109000818801012600c0140c1141d1001a4032151420200c0384000c0981050541c05e0071034443c00b42020f802e03001030080302c400311030040d80700790382d09c2c1211403e10034103001d41d800d60002e149258024030715030300005211741c2600640b40b041d080302600505006081010440c1e00341d460f4020424400d840c030035200600801c6c2e0b10a0740b0300969031034030024041035100080040362101e0020700050710401c50580c102c4680c80081c00041d156281000190001b1078050340a07090000300040e9190300400040799241d00001c2c0801c258499014140136640d48010307181d00f00380c40da0343c0000091211040314031a0707a02141c000035014248a5820044600b50f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 252562985 1250 252561735 252561769
    0x61d07031a060f0c12070605040c090506010c02191502030301090b012307081308030a02120f1806090d05070e070c021021180b090105071b05030d050c0702 68
    0x8040e01c008580c55020032114000f5580102d10381301d034254a45a880c040f1740070030218031008041040c03800c00c5001c2d00000d005901c60203154941c2c42d240c0300c0390001c5800c00c4035210b0026440d5071074040076081600000c10411008448182400d464902c1210343c4150030072080016400007004015040132403041c003144800918000300000c03106d114405031480c2d540180f0101010007e80c2c10304200303458049030000c2400500403006c2c1c96851015540303036008400b5410141c05007142c80c4000951410407910007203c40c1c02d00b0307070030802040a6060303c8610910303441c1e000034040120128039600c12940181d01c0e4807480003060f6650810f0308129000101a010304240000c00d030070880143c0d0b44070441c010b0051a80340442c981c0d2a0401081c200d400d400fa0b04600e103901d01900d0800345031000300910395141c0100c2401c944d9440b00c035000d908a6031700304c5c1c0c00000288204451402c13078040092031407825000f201241e091040c3c020303440c003c482c800d0360303190b80c030b1840020320108504118415130000d201d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 252564235 1250 252562985 252563021
    0x9210d051f0e150a09020901080f0103080415200a1a0106051b1c08150105040b04050906031f05060906100e040203060303040e0906041a0103080418061d0703 69
    0x5480e5008072560365501440c110a08114006400344141000419003900000c010041565444c000000207601446031240050342a4000a08109424031024100d85d4410906440c0600d0600ca841d40c040310291102c0c00c0100c402d01400705140250500d60301460000043d002e44035107131424a030a485d40904591940d01081e00400c1102c1d004400e60703007949424103440030410034002c0c0c0241841c0242810507c500c43c400c0544400d140e004189900c100c1112001501c0c4414050042d00e0f103018510680200480c20031081c851420545625500f00402a04480303020040c1c5502204540d003000103044c0035982d65081054602d080580c0702d030800d10989851103083d1081c030005101c241c0d01001a80076a4001011032082e48080003100d0040045501540c00c40c10300400ea142c498109481c10344c0d00241c101545c0c00c0d4000b0b00400307203040382d600541c2c01d46814500300b40c100042d0000135014440039a1410300188600c14580355903480f00b81201180300c00e1a082c0c4001e001c60b08181449006011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 252565485 1250 252564235 252564271
    0xc0706020a0503033c0405070602010b150c010b1f020714010f0f09050d0b060306150612040606090c030504050f0d02190602190507031d09070809210d05 67
    0x50b02104607504140d912520800c3d03031006826907402803036220b01d1030302e00004040410200c160f09030031541c0180d1299040d655141c1d518041282070740c20282d030741a8854400c002d4201500852402403103404500300001c00d00c020001e000509102e59044094074613600d0622100c0f13a80e60501c40c000142c04c02080107130225000400080c5180741d0480b120051107555050242907500651408004002c002c0411807140c4451521116808090f10801e0080c8540d00c040341e0303000c5440200c080c604a0180c421418030b241540511000007010f002510700c0c0b0780d504408100b01183e40141100d44007640c402085500309840c00f40e15092203d0001c01ca0f50b005040d5620300f06134086005101a003101c0c6040661500c075080801c020310984180b078105291071800d4410070303a00b000242106500940303c500c044e154100c11800f510010345442d680c025424000190000c4c09810306607086880d810444d0b0301402d100390310303001640d28003003010310311071010501c0404071300303140076455000d6400d80c11060300c0780c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 252566735 1250 252565485 252565493
    0x120a120f1205060f04020c1015060c080d06090615120e03031611010f0c110109050d0809010b0904110a080102070f080304020613030c050a090c02120a0e13020c0706020a 74
    0x1a1410052007601e8650b80800c0d040c1d03440c00001c440720300008008654603030600c0005683c2d1400100070068081c1003400c103440445460781e60b082160340540710510246040c4e40c036048168025602c03007141e1540c800740800e440c01c1d10b121350405001c5680c1c0d00d51448403061405000c00e0b0a80d80c41c5100341d4213152007440d41e0000803040d01e4008030004066000500303e18000d42e10056544226070700c940c40c1014400c41400c0c01e0700300050404042c0c5803c2c0c14880205649400e0362941c10300580b20340d0001c0740e400c034050722612106078004602400002c104040e540010781c140d4003170f00c058801212100c0000c0e210b2400d00500401440c080008616020380c90381d0748901800c10b442c0c080c1c0408070200c001002d54a0703090441d600c0751226601320200d1512071401c40703070f94081d40c00380c1c60003000318100100300480740d0711031584600017a070001c20b0103043c81d4111104690242c0c0c810402c002d5002513013891031f103d032521213203201d10095000d81c0b0b400600c6891441e240d0513a100c2c03811035010b144050b002c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 252567985 1250 252566735 252566747
    0xf030c10060e04150c050702180402090f0c16020f100207141c120e0909030304060c05090f1521061201090201090b030603030f0a05210106020d0507060b120a120f 71
    0x84101c0341008501780016240503103040c0501c04029410100004000440d0064860140e104501c221498070703040d00d881c07404800c5078600302c84840444200b0030a10040c08007d110000300c040c40100b003922801000808143d031f02002c4000f250169100450921912602c01d0441c41d0341901500c500c210f00f01c402000c42400362000d14080c1410003843d840410445c0f00e030094807440c04000e89440414203000281c181d4a5000b101c0075200d4500c0d040080910ba403013801200d504940c028046a039003041e2800300708154003120b643d46280141004019880c0302c1541c0b5540c074a030814407001e041c0f45001d8003407110b110000d42e5a400685d1606405400503038001400358262800700e01003d44030f6891001181c6507100313003c05d02115080106126a0b00b0358020300404130103900140705030400b15455000040e9260078080d10001d40c2000c50303c0c1c0d1a10344248090022240159808209801c0d1500444c540c10960301da01d08554000a1400b81440042550b81c000150340c1d14107843c40306d40c9100d0003004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 252569235 1250 252567985 252568013
    0x60319110c163203010608070b04090b01090b0a031802090702011a0910150c0213061806080d050c0118031e080903030402010f030902040606051e0304080702040507020f030c10060e04 80
    0x10324500f00a904200e440941c05003000d009002d0840e02c50603100c40d41440680c216100300283c80f814103004820729441003c0d11421680e841000341c0c10620401d50681c040c021040520034030b04054426040940d5844013854083d05c69900002420181c1070000c45400c00100e200350301860186090110300c034590a040804c507154080c40035070035072103104201c1d04808140d4010303501206906000c0206511a172000e41196404d55490000403520031a5005a8200c0c3c0b141d07501c540c112007000010503000d84000c15840300c0f503a0002070f198103000345100c1103100c42d00055000a030404120700d240c2c0c00602000344086103a0030125424509000200d0740ea1200800080c10040204042c0b42894000c0e00002c440075030003401400000e4896000500b0b981000302040c07454001414900c500c5140701c0212070180d904000c8180c81c0054903000c1c84003070300c4007828000461140400c0d04420010a0001d000da2242d080040c0c58001c2442649600781c0d0f50300c0e0840000810034000748000500388c01420f0360 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 252570485 1250 252569235 252569309
    0x106030c02030d060303020601090b0f030c0906010903021f030c082203030f02030a0b030c10170402060403120323190e010608071d0f06060319110c16 66
    0x20344034240250880c11402480801e9482a0800001104043d0045689410f84031400300400c4481c88540c104080c44504040194140e045a0002c86207810880c1c1c040f54850f20606007a170300b242c1d99034082120419203943c1748192060040c050702880380d00d80034070b880d842c44515021140d42132441c410b420700054426a9003001840030040810140217402143e070000851404640740d02d41040500040c0403034000451190150560a8100d480c03c0080318409403415600c0550000848210700a50500a00701f40e03844030091000100203100f21040200d034100e030b0307a808948800640745050044440c0011400b1241103101080240328081c43d40d8500075410342ca0200340007000401c0c82d0300528041c1c200160f980601840422265600281c0007a211000f2918203903d03a10b400f011020000c00340c8040d035100000304041070400c500185c43c1641106080c2000030701c0c00b051640c0c481a58401c05a0350704903003084004220300701c50402d10200900d025801c00c600340c405040ca420304006900380c002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 252571735 1250 252570485 252570491
    0xe01140319110607032610060e0f100c14010203070e09060a030507081e070614131e17070308030c0705010b06072406050105180310092001030b09010603 67
    0x40902c82c500c4090314107048060f00c02c540e03030421410000c00e54007440e11140e40340c03c501151490780405003504a889445000d0050100c61304090040720301d500e074650007590003800094a5140ca690301a5049603a058544036004500f1503448e000140c2d03074411300d55100c4c9034410700c10094441d80094201900c4442101e06112a68030440040c07190f84040c1c00c040d001d4411848045030904000411403d02c0892641810300303034007202009560340a03e800f444000035000d91220070040d0481c00500166a90744001000c000c1e1264429440c403507100c0032801c60807100c0c40d810404003e28181052000c01140b024045990650300c40b46414400507002002c0540e0010340d4000b400000e5200402c2800000d01c00c981d180e03410701380000441142c0480308003914110001100c0e42001703201e103908441040c0c5030030342003032041e1000600e050200e100040c0c01d401303070b250a031444201030f00c42e14000c58130030b81800e5011031a0745260081e03803071000000d5062626000030072100e55900010b150440e80d480c5004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 252572985 1250 252571735 252571783
    0x3140a03090609061d06040c15110f030315030609070614040b03090a050601080715030c031103070f03051e0c0f04150306060806091905060a0f0f0e011403 68
    0x100c00500d4102405481d040c81d2030a03083c100701d1a40c110b90080e07042409107a01070040f20f00481d0300c40c0800d45000340401d95541d420858910b17100001d00844041e400c05038901003450200ba42004012103031085a50000010440c0c560140011540003000940061450340b80180341d0130743d103100d01c1c026941800462520f0030300c0d90441a00712005403000030b01c0c1c1900d9007010f002047d030b07583d82d81c04120340720701601001240d0001c1c0003412008888401024000e140c0d15504150010001000008109a02c1d9000f80b49401c410700c0080d4094041550707214075100c0400e000404880029114141510f00e03103005048140c81c40000036000480d00c043e0503501c1041400c0691710f4420361340001c00c804170042c1004c061390b806600c900f00321f5000341c0341d00c2c807103a56050030081c144508403040d1703030588480d0026201b19965648010f51203040500f20400403901d4800da10020b0001382c1c0002214540103c0505c524032003541010b004003804c50301c080c212100c1c4000640c550807080d604c050595005000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 252574235 1250 252572985 252572987
    0x72301020c010c0302041706130807020f04060b030f16020d031d01140f0f0403080c18060d090c0801050402010203090d060b18010305010e0d0503011a0702060408031209010903140a 79
    0x4a8200702001c10080141c125411400b4019403c01d10896441120020440d4060000460001d105610702420344400f56119641c0c01010f41140106a802988228a0141c00d03101ca10802010349010039500e600d074074041000741e10120001304411400a8045640141c0e19000101130b05101c40c00d050204d03920313503c0f231004400240c104012585541c2803050100250883c5002c07140141c4010740101074a9981c2e40301800011011796000300012144400034400e42071000281105240c403400d03490f0300e440c25000049007504005690580700380e607100d41c07400304000315007082c008001d100c000380441c0c0340503000031b52240143c06849006240c1c4011f4038040182c00d034002c03541c1c02d000810542d8070036100b4121400012090004480b19840d1003965605000d0002e040403800819545076807842c0e081c00c81480031804884629140c40e001400b1200050351482c01a002038690900150780b82c201e280144124000040c0c554045a458284040e0200394094695001e11004ea1070140e500c039503140c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 252575485 1250 252574235 252574237
    0xb1306090c0b0403020a06030b180a021207120e0708060a02031e040501200325030608030c0a05010b0603130305090109081605040c030e0a0b0a150303020a05060106030207230102 78
    0x1030005941ca0808501c580103000a0000e8074025900d481005440d850203400316110680607a0f0300080940c1c0004014200944490f84011800d90241c10300140300369500003a0340c151541804980051184100c0a002c2d01c5403102c1d01c4400c0f0700610040e482c058501d030321104081c0c20030300030940000c0010a41212040c18400006044038404480d28140c14060f00030041d186c05520b40c60003c21304000e50070313440030689004210140201d2103010541c64a09280b8130200c26040a0540360680019801014400340401d50100380140c85a491241351550850f140c15201510a035010310a10031040c0b880350900c06403d6047c10244d40e14041e280040e04c00f851194413000d190b100d0601501444400406460200c60b0162410b101000d0004002d40a0b21140a03003880703150320441da0400419074401d81c40c0d42041300454006427000d00f030038021000020b01d800a03409644061228010441d04100b02c0f1b00620070340c81c045052240d04d540e035008440801a90704900340c07003000200c51131107081d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 252576735 1250 252575485 252575501
    0x70308160e1c050d0e010206150f1306090506040905030304030c0201022b1706011b0c1d01080d020114060103150915240c120e09070c020906010c0b1306 67
    0x7032041e030b00d01031004009540ca60800c001110280512010075070b1041c01091126000f800503000b4041e1a590440032011382c1e003500c1c01c40741d841241c2980301105a03c0c1c0030001424491120340100d01c0500341001d800a582010b00014012440d20004d60045640031094030782056262800c0d2484040c0c9000407440c00d5000216036902c0c07409409040141c56031070701102e40a907a40d484400100400020303038182060105e0340c0d42e0208500c501c01800e5241c0c10303502200c18a10800004003180d85072540d44480714105100000c281ca58040184600107040003980e0360300c101440207102c08252513101a0048901400c0d0506043d141e4075200010080299580050019800c00308107201d0304100882003040148511400350220b02c1450704186020503094030f44420356150200001a0780d91401a400c5401d4100420000200840081955400015070240e41d2a980d810008900790040018001c005070026044c0440f202c00e081c000381c038098940ba0701ca441c1204000981d455401c02e14003900640d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 252577985 1250 252576735 252576739
    0x30a05150c1306080403080604110a111603030509031c12090201021c02030904180528080d060515070b011710020c16120c0506030c070605090d0311070308160e 70
    0x4070b90046000e55124660520aa0103a500c91126440d00c4d410701040340c00c04a10300f818031004010560240380101c0c00c0300fa858159000319411070400ca1014801407400b60030843c0042c10000f015006032404010040b004140000c440c404e60307070412006081d00030803d46024003d82c40300001c505580c02441810710846c041603100d40c984075015070003912a401903208510585c0340041c0c44d0180741c2c0d8036504010055104004040150f1014200e4125031502c90b400000c12851110010028090002400b030b07080d0804070104500781401c081041540c1d11000900b00d00034280482030110b10b040c01001d0444194801803100004510b06281c18403c0320490404040d00005a01841440025000c03c3e00d031401d00404005644070000074014110500025000f10250303081448240f404d04000c540200348500807074034018041d03440341e0a85e5011240e042070742d000840045141c40d050b0161444001d450540140341c103180e50780180c402c04014041e81105c004886c0420680c0b401211960514040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 252579235 1250 252577985 252578017
    0x1e0e0712150b060d0b030d030c020303061c020d03050d1802010c0201111009080c1e060411030a060e0c09151e12030f0c24010b03060a0f091a030a05150c 67
    0x4c002d0114043d080c00030b2064042e10492813a5106070b8801d200700c42c080380c115806186143c40341001c001001c81581400e01c11220701c03440580050707889071039000c80300e840798946680f07403160400711f1022208002120700b80701c1e20745601d560041c0c0e0301140300c0710f0b02035090030442118140c9a28252a003c40c858040c03041c80e01d8410b424040c40f031008042c0c407203204050b0460303007000fa100b10782108908200c01da85030720358004c0c00441e000954018801d401550054201d44403048141c507084d0554106001d15802ea03001000f412260b070030000c1003940e202400a24814010041001180060740200408455100750a4070704007140c0c1c500442103541c2040340e0450f51200040c004159441c0c0c0000140f103440d200300c0c0442c01c0d006180e44400303249144c02c0401c14a0680ca00a41e880040d0700050100390b01101c06103011400c0d0351010350783c0713014103d00440094048420340820114510b80800c0b68402da1115450000080e800952419071898030ba42c00030442c0c0780e81400030f005004401800501d285 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 252580485 1250 252579235 252579247
    0x41d030c0102040f091109130908070f0201081506030c0a020304030212061609030b01060f12060906080c040603080313020d06090602030717090703020f030705041e0e0712150b06 78
    0x80150003400544e80801c00900d005580d0300a064200e900500d2841c00303401c0103100c1c1c400345103402c000641e030318019041c01041490450392160410350152004403003010b1012140c2040d5644075403042e500c007003080709616026480b0340001c1c486020081440d00180300c00900242a503100780151001180e0103000000c04115081e13803140c4400c0f00300c40c90104000907005018006100b070098500703c9400040400a590905404980312a0810f10310340502158039520720070303d01d09115640003000e4540e00040c180d03003403003501401e241a208409219074100708040c0080340c84a011290010b1200340041944036561021175010b4440c10f6015000714034120056003440311171b400030341c031a040d140c0d079400c203c0b030700d80f00100040d035001e6410007544e6000034418070050034403858036407240c03100038100c0d51607030f40c1c1b01d0010301510400e114041c00c050683c140c5044007a40c0b406500c0d02e160204000d030445070704168102090329950310000d4029a80000c0c030070031614640c0c3c86000c2c4c0041c09002240d4580f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 252581735 1250 252580485 252580507
    0x5101a10020a290405010c031b0903020402070206090d06060510050a0512060a080a03090527070f03020c01090602040905061002190317091606030b0a0e0406150e15040c050405041d03 80
    0x510203154401207800d00304270101e8507050340c1150083c1041d0385c41d180421829070b02408002d4001e504100e820134020482d002c000e560341e0031342c81c9103184216808030b21181440140075002c240a158042400402d00c00031007040e07000015180142002403074002e0b180c0d60364000803c11070f15580030081d680205040386051652050307030b400544000742d440f420fa8090340606c142c074031101104068004550317000441d08036482880a640004001c0ca0098282088a5089821070380145021942da59001904115100450052540c05002110711002c00341184030042d4035403541c11044035074450110142e5003014060050710070080c500c000a60702c580352401c00240d64015240522b222100300500004255100c1d0103401500c40010300401f245624024104280900281c012a103003900d074010402292045114800103210f010800e803400d052103015600d0038004156054001c2e8204a40107945c25004000c803011500191b400040348541030108603404410004480d101d400b0000c2c0c090010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 252582985 1250 252581735 252581741
    0x302040e0a050f060c030a0e07150c02031e060105061b01090627050309010f1b03050702010912020312030603010e12041a1c02070f05101a10020a29040501 68
    0x4684141e040760203c0d400c19032465a81c43d401c0b40c0c1302c1521401040024180100e03078100352a100404001c40788038544800c650341000380707503500f03070800504460104015840d0030055104004008000803921003c0741c40c0c00c6481d110140205030107004000360a640840c200000c11030010744240081154541300e01e01080034082e0b005d402080c031505904140f40c8080091910b0650650110055140101100055032942c4410011800740600400903074817132450454000244d1b03100b51740d032981d586241d100240040c00d094002e902c02d801d0105035080180c6000074000c1015906840c840d0700c903924000045d01524031040614031502801e8203200c14612010050001d96411a04801c007010300d41905059900071480003100c1511124891450f0ba00c00b540140810340c014107450008026944400b4900800310300404002c070342d0745103055210382d20307002010240602104d450000b000e041000960341d9400d045c1c013400c0031a90281494031501d01090031036003011202c583c0340245c82c103070800a000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 252584235 1250 252582985 252583003
    0x90307020f01030203060a0e100806010801060501140705070b132402010b010e09040809010207030b13110924030f0d030e01060e04021f020106090504061a041806050405070302040e 79
    0x35221011001c0703010340c082d0080e02d01c2858060701d00c0d00340341c0c9030a4850101c40d001070125401079042800c0401d42074014003007940602414400406d409182000041201110300002d451001061081c04d001070004110a8101c400c198003032070300c5048101d05074070385540d194070205402000e102401d00600348507903200202c9100b0f4000b0000040b030341f0015605044044641c44c0e110004400040001d01203001810300d10006104075481c540c0c980c1d8034010081015103d541c121510342e20068100420b620009801101c150bd002c0e030742c0d0402c06180d035400b40c41d100b4001c42d49031500c8160611901d040081d2400780c09488103c41840340b2090018004108550819200c0d50134900e0100f01010b07843d0a09024650142c103008084611002981810007840d080c5021552202c2002904102d54014580034a0040100080d68145201e4070562031102e040401d000c0c0d402c2c1200fa540902e0000090b40701035401c4038000c00c06a80390701d807440c1403000e2604000c0d4020b240a0050300b200200003042b540e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 252585485 1250 252584235 252584239
    0x30c020405010b16030804110414191104120213230105030703081e07051e0d021b0607020102070911040503120301080c0f420c0307020904150509030702 67
    0x190f621102020250b01c5040e00403c0715206164107180060710881400340e2090045007a82c448106401c00141900d8410514000d01018601400000b000e42030075044105d4086004200c40c0080003080c640c90300680c401c3c0102445030300300a205548600e00020310010000c00108130350040d01120040040180c0b5031101c0c00c0b00d508002143c00c0c100003404506498110348120f042819030100040c086003440c10b81c51303092106002d070f80005401000200141c210302c0c058525082900e000d49442d200480d413049007158400c3d00d0002c611100400e411401040c01d6a10a51b205a42e00060b441c203030141d84808041d038a8020014412210701d4041c0042c0c500480903150280380c40d00c0b080d6881e0100380241000c54100c070400400c0c0741b5040002102908010f01104036445d50400498411845400407640c036150328801a002c80480e000b14000e0034544034685410500c1100d6459600d01a6460081c0140d03c5800450203105484803900803070760f0403003410b0289141c110115900c982000714124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 252586735 1250 252585485 252585491
    0x60c010509100c110a0803100b0a02030409320c130f05010224060607020d0f060b0f010309051e01110f040e010605091f1101090f1e0c0603020a02010216030c0204 71
    0x400f0240700b8441d54020307443c030308001c00503620952100e42603a48068003018100c0381141000a81c1483d440141c420000e03a81c01854895180c01495000d507080e130340c6d20340c4501d017100d0350b1240c80703510380031003080911070400200384150b44130075000e4414415100c031131183ca01d2403140000c0106a030082c800a5900c01c0c3e00745c03243c102e19882000c11904103014911806000980020600c3c01d001c405402c500d80000c105000403501c1c1c0d00d07a8451502880002da03030341d50300c5070310722119400c000340001c20700349080c13804020f41125070300da0300c2d12108004074000041d04018004000c0721002d4006c04e10f50101c01680d140d0f80c000c2c0c03007403010b290b40c0140b089401d8100c1050000640340c2c0a4410f9030000385000c1d0210340d03510b002015208031810144a03030418045040700c500c26214091081244492140240301420b0b1a1401c001c080c01e1010b030a0020b0019865540f0f01c0001c018074000e900320780c6981400b50f21178080b04c10980c060b01074000050b490f01030000e80c803018035a114442000c024002e403410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 252587985 1250 252586735 252586751
    0x30f0e1e101107060806150c0a11030c01050f030406150803040906080105070f050d0e19060501050a06020c0108070c021801090b01021c0507020d08040803030702120309060114060c01050910 83
    0x41c0c0e0940b4201d00c03061400c0e000300200b000294040c0c50300d01d40c850001040b402c10440c0c82c05d805810368000002104140d40489021070400c21103030307200548054100c0003460069400d02c0001c00511031396143e606205d4000c008501000504d400c0306481541200c02c0d07410382511604103e07501e812502c1000c04090820400042000044c410580610f1540d5079040c205400160166001e42c001d10002c0e075001c2c1d0340c0d42c0c640034108040c4002103160900744d500b101c2d4444a0300b4410306848068201501c030f82e0010304100044d50300010402e407030780300078246200030396108402a1041e290700d06000e50007441d0941d807c48652081c12086059501844041202940d09801282e4a02421250304c40b1040c854006408860080002d172001c144000e10344200381005558004180d0016801903d00e03502c08824404800c0d0140020016180c141c40c81f84c1c00c2d80381c04507480360b4404040c0b00d00d6514013842c100020003511148100d0310302c040101c0090180c1d0800c00d120544e1000039130036802c103ea10300422 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 252589235 1250 252587985 252587987
    0x305060402011215030b090a052a01021c180e0403050306100c02090a1a0d05030a1103120103020415030807031107050a05010507140f0d050d05010611030304030f0e1e10 74
    0x28030141407100d42e0344803c4c050b04599420f0821100035118035100e216143c1c0040000e0010001c000301c0a4845003031205852045034800f5802c0840750420f4150341041501400c18242164641400380c060715020200c198034601c1c8800311350181d003002e1a81c0e04610100018036801c18010360040b481a6032100c0841410102115918002e001c025401040d0307070080307545000300341c020340c46507610950421145140d910008800f02d50060084a0b141c002103414101e075a000b0034180d142402210165140c42c1504262030001401404001d200d50364030201612041481052040a580d10034500c43d9941010305001c0c003da0080300d04a4541c4c41303042030204145c10504490402c44006031500d6092069560718581040c1008101e914180b040044514a400c02000346140300e00050b12040c2c4c3d04c55925651030180c8805800c1203082c80600000703034030040300020849510581514051006880c003041c01c0350741251402d0110362001003079410316590044580305150f04031040b2462400c25050040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252590485 1250 252589235 252589241
    0xc0d0e0609160e010617040303061203020c040f05012d09020d0b040b0a210f0203031b0f0d0f0c0c0323100507052a0d032903071202010e04050103050604020112 70
    0x540300c00109010720708400b2001b09199190402d00c01c0c20701044481d00c0350000700d05da2100510517070050380020400c10320750525120300021100000d5060190f0340c1000d00004030181d005501c02060300d00f051146104811000400014000c825029940e6640b0b0140c1e01c00601901e4521078855031420401d41d01924018500717104581c8642d4a41c808441d0103605403222100c50b201c10b40d102540d6040c00700059034180010850b001794990301d061105001d5802c1d13803400302d002c0703000407803580042c08080b142500003100d54600c894a207040c0324200180e140020010700d640e403000741a50038800000c0d150039062402d041041d0614030483d54017400c4071044209440040c0c90a0f008940200301c0098440404071051400b541a00410300c0c80e0b610400a00e4640445001c03e500040d640c0e96201d1a04000a0500141030070714141d11407202140800203a1200094412688583e0181d4010303800c69008942c050780404d4001c0003000340f90f94070306080b1380741d02c0300b01c40490000703601040384100110148 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 252591735 1250 252590485 252590489
    0x1103090d0905010f0c051501060215010807030c0b1803070803180319020415081912020309010f03150801060f03050c0919200c010c0e030f03030c0d0e0609160e01 71
    0x60344607010910801000e880516181409130780a001e04c41914047e990340b02640e5000f01095401400c2a20400c00400d40740541038020700829001035031704101040c00550654207591710002c1d8250740b1440c04500b05180c002c0b1480c3d0359098054010b0001b80c01c03c002c4050034900385040701400c44269541c0406488442c409000081d8196040805000d410b0a03404802c3e41c030007820203901081d4641904901e40708121422100264045901c10b0401002290b0201c103042c0c9400118140080304001800e40134180b00d54804065035164814020b4008031044402403507620020481c842c0c440c10300904030125404251a00c0c030805c2c1d039400150414040880c03203020500281101c075180003660101030000c100c034030007c0c1c0800004200c42d24140400620980d0780e180000500d4100038480588000d9040e140700b40700e07400600f5818960040030007100d91180b40d6885140c1d6803c0380c445114001d020081d101001489900100000b40300300142101600780034170450f00c00e642d41d4000c00e9032495024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 252592985 1250 252591735 252591737
    0x180b0915010902090d0519020a0e1311010311040b0c120a0c0305160c08030a02010c050f0d11160b0f060d11040510080d051804090b060108090708011103090d090501 72
    0x9004001c501c180b40d004d0124074800600e17000e100119503d9080c039114070401503551080004034581d0031454800051801019a0348400c015864088400b030000000c3d85405001d081410021020740c1c0c0c2b180d8843d03c0103910340018581c540344c448003103485680000e60300072070a1003440d0090f811010702500f0b40d600003100f9035070f60b400c8400d265070444040e00704c030452400e8480004100c01c00503080d21082000b0300101c0c4029902c488074220000d09656100f072180003401801c004109980d00210110790100d6450440030907581880050000c65214102d0200314003141283c0d402c080161203100c03140900e464104068054595800f00040c000c1a00d00c014040a204e030701d0920241081d4000359172207400341c403010200300e5440a1403810038135a034212000090300080c605108a4a0707804249000d90306079001c00004a042c0c0d2005980385000d4840c0b814000c1c00703400117616a100f0045030f130103040418000e100800350200902c030a900141c4010140e40142007142080601c5174000100315001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 252594235 1250 252592985 252593023
    0x30c281d04060b181806090c130b0a110d08041e0305071b030203210315030a0213061e0b040b2203050105040c050108100603050a020c0312010512030f0904021c180b09 73
    0x703501e52314666521103c0d658089050f4240009103160009025085d241e0075502c03008418240d07442240c0c140a0b621040c18240003591043c80041003d100c007070402c1c9202840c609480c01c60034141510940035428004002c2e4041003c06a029107400c01404102e030b10a600b01c03000703074184d41d0a640c112004240f0007001da000c2407000a610408a42c0c81180104002d0255250403c02da000304110700803200c8481c0703030113840e500208032100c2c2c584040040ca2018078401d001c658206100c25802c1d20841c8945011a8008603888001c0807420109400c10b00350122291140e81d0340707240840c0a0a0122800d942550301c908002410394001c000c414810031482c40c946504a040c03003400c0d4010000541009401d950a020000385110200000c2451200031036200300250302d0300341001414000d002c2e800003030307800911009020341c903d001030f00c0486004035005600d50381c01401000310001c1505030b81c000141405039101841400700300140c070f002d011b2001101d660f55100700e8955151100c007001005410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 252595485 1250 252594235 252594241
    0x20a03141003140d08070c060902060c0f0c12070302040c05040b07060501150c080714070510031a0a080703150207020405151003060609052202030c281d04060b18180609 74
    0x1114900d0b02d00c7c1640b240e440010048055008103680350000c48018200d0381c0101e9049a02c1d07001006082001401210340c056100301c1450500d84a42c1b0900c0001e01450b2034101007040136010f002030b03402400e40150420745030101410080301901c0284501c0100c49002d4006440d100d100ea1607501e00c4540010f001381c60701c8175503950421359101500411103503000c2c41c0c9010416540c0c0402c44066400e0320f07900031a06001d0790031300340038030100c01c507026115000000c0108641c40300441c0b1784049980120803410340c80200b0008201034494242e0003944945017400b08086c40c1484100c24496407000d42d0314101c1218a280181c0485038107000e00400300320302200802c030b03500d08107030300e45803c0102d0002c588440103e1075109040c2d81040d9804068000085520241d000a100003201c11101e0b0700380c54603201002003c00351079010301781c004103040c03510010410f2158940381c121000805d2000841075075480b02514003100300f1078034400c80d44035403c100c901092001c0b180b1103440c0100001409000070343c0f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 252596735 1250 252595485 252595487
    0x702071a0304140609010e07050a0303090b0d090c09020c10050402062a01150302011103130b0c0a12030c170f180a1b06120c0210020a03141003140d0807 67
    0xc1c10050044910050103820018141024003905001e09032400001c10001c0e45508600d00b000c41c0740c0c10140c050341d49160f080012036840030402088448600c51035039544858402e22028080700c3d8409802c010b589100060142c1d0140d00911000ca0b41d1000e0301e0402e8103002c00034044e03420548020350f0241e8240050810988400100300550202500b088000f42c07140b98203500b074a107488102601111010f40800555030800100480128140b001d50710300010950000080f00544c024613210070804900000b0321002008000102c0303811010b0040d42842040d00100a00078006002c07000665400480d00222282180036000c3d40b005040340241d41d84080c00d2101c811003210020303420b4445d07004002e0101d0506006652881003200c000c0c0030203401e215000e071280e190040103071b402501d4140c0c408402940800d00d4014851802809640c54042000c100c3c05010f18001c3c22402c090b8200901141e00038075400d00c0c086070b129003821a0740c481110070541e29901450020004100340c0301c0055241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 252597985 1250 252596735 252596737
    0x3060d0320061012210909060f030b070c0503040306090c0915090b0609010203090d02060910032c0a0312110406050d060611060f060a0e280c050a140405030d050706050702071a 77
    0x1103142132500180301c540e14047c00b015102c1c150f000c3c2000c880700307410a00a11070401c1080d980702d0000d0074030000420160f03071425942c3c03090384805010150f480100c4070801c609010240c009110340241071210031170000b44110b101c21184101a1040d18008512565052803002d44d00009416000340d41000c08840511040c0c0d00100000c0b03900c90000c21182a1030340e1403080c501168107407964005001c1c00101c002911403200b01120405403007000740c016a00480c00521a8085035052415800317010180007000054a00c5d2104035004080119000c551035600c40080c2900d044440f00038070292740d6591303083d19030080000e03c9a503603130044400141c08030006840d081d080038000d024019550750310400041d88000a440b90551840040d003011001c0000ba582400c94214002003040040e504180103482441520452401d101141860303080b920b02d03440507a0010074020307003a40c48111a0b400010041e60080c181220058900004622494400100841980e6402910b101e60000c031032440300113 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 252599235 1250 252597985 252598043
    0x14010b040e0c010c24060f030b0708010f060c020409050d11060115020309010c03050c01050103080d0f0b0f010e030106050d03050a02060a1e180507030804050a0b090603060d0320061012 81
    0x188400030300d00144a86051b02c6800010002c0ca044c00400c90709500e8409031501c2c001d4512000c0254010040c8021040310070301c54126155810120303c420061320201e00a00790102c0f016129002e42d004619050741c000d90030404c030303e07100c8040d80d26036a2200844640c1031011296400183c0c014072401030f06501074000c000c0060b0090502504020ba04140d1a0030b54000744c0080b100e450002c01c91112448080c09120040d8203040000d2103401ca010010450f070311042001c440c1003000240e00d40c100c50310b0a40c8072501401d405407000c40d41c0700303441c10040d010307910450181005201d800c0010b101014144a00d038042461200c40b4001c07549040100400f900c031510f0401c00ca91340d450030b02230000b9020444000210300c203007402902d8a282c0820028600c845901180d101c820030444116180d072042f0441e50b02c031074100c40001403414203003403c884031100da8401c004020101c020302000e030500003940601c9113043d087c910000b03c0c3c4803000580700001c0c200c0002c0c40350346050200d00003c2c010480380e400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 252600485 1250 252599235 252599273
    0xf3c10080c06120615040312050d06061b030305060f1203071103030c07122405040201111203060913020a09020910030c080402040e1009150f02070c0b070501060314010b040e0c010c 79
    0x20070203499807076003000d00d1523400c01c043c085100000c00952640250040200904407410800c402e0081550f10304154a4090402020155220700050346a90b40c910140d01802029100407051501030303244a075240c0c010b0b14140c0f02c0c025050040c80c82c0e8a400422554805050400740940500e02410100c1340310000f00e08461481e041c1262500e0a4110b50003042000820000440c0c9400c06000140100780c042e102c01d031441e0031031441c9140854452007129005141034074254001c1d0344500d00c134440b1121b1190025030004c4018000200c0001d60b4010741003140d41150101100c40622000f030302101c0b50034141201081e0610001005441c0c01c0e4054100358102c00103859000011180b0781040740c1a111044034514030881d220000302d1528491400e005a0036902140f500756152110250004903108000402d0340c00101d000c1002429040b00d4021540300c08407000300e50350300c01218041c100c40a0f189000394540105040010000501c0580d103200684881e200014a0f465041100900d204050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 252601735 1250 252600485 252600487
    0x20c0d080c0d0207050a0c051e01050f09090f010f0b1201030318090c0504030b100b07240203040f05101e0b03150106020d02060f3c10080c06120615 65
    0x4400b20300ea000410100348140050306007280d00d403a0014040c00c0903003006010304080801803101640b02c6504003550341003400d0494480b40c010b15100d0b0144211303448240c100308003000340130302013807881a078134140d6260446800d2b1103510303010351003654024001c188600707007401001040481c0c090300c0740307007013480c64101e000603d1601d4803440001e50b02080000302c00250000b40030410300400e4280c3c2d0360480c0e814080c8481c1d0a141000d013001d00e010f0080003400708a00c0c84202441c08100300d208110035440c1c200d0030354880c60035003000c1a40310705840c4240c0d0705005079103006c2d006090b20301c10030700501600600600340c449842d40e40c1004040d085e0056070140701c0d12480b00491010000004e00910469009151810b10600020300788500900104420000c01052094002d20480038100d00e11124880c0c00170f100322500c0d90302ea0301a09200c8119030b42c07100005e00030190312047d150710076690b4100860b480d6074000018010380784107040816a141820b000070803a14078250751480d0450000942803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 252602985 1250 252601735 252601747
    0x30207060212090708011104050904030e01020a0b0108010626070303030f0b030109050a02040b100e010513090e0d090b0702060711041d060919030210110d020d05060310020c0d080c 79
    0x12030881c40243c40a42960344002400c100b405000d0081300c96841c2020764080c102864880030410303003940580000e05000d103420198001da4402c226995840da0800f03030542003565240003003402060240038420030b0810b009280e1a0f0420078281a00901712a00010030207a0315503241200205521018031b41d040d5240c0403240c9441c5c0d402d01907a41c0e007602940c081c040801891040008481c0f03004035036400307a555403007007035405908001c0b4111001002e08005a0341c8400713400b640b07a100d1072508000380b500c1c80d0451201080c070340094a000510401d4580d2074030701d038852141c240c4078050030000940c084810081400002c000c16116081c1c45800b40c00031a5030400c80a0b06011000e4004615020303520900403c104003808000c0d450140c0e407104214800c14085490013500c511081d000384c10303016200c169581c54030102e1030131160f04180c5008110f44648502c3d071080041c4c80203942140c0700b4440c103140307610801468821102862401e6008181c03a203c030840580704a8401840c400d1380380c00030f000c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 252604235 1250 252602985 252603007
    0x6061a0418270615080a0201120507020106052806050309030409020705010f061e23010804110a090213080303010f0e15040204030b06030f06040c17071d220b06010302070602 76
    0x2c2403040c0d03204250104854051001e08090b40740103610100c00c941c010b16403070000d42d0b040603140584403c1888003003546e90721020141e01400b465400079400c8481a01411452440ca00340003080c562020112204180e4810742121113000541d050720071908100030800c4210b07800d50041c0b0010b80300b2030020038840241e03a5520201c0d500741c0c1c40070006890403c4100007440c450f01181010302040100000860081070758100101183c03020503060044401c017017010302045028404821000801e03100400da1074030b9248c0069008a000000490524040411904808000e5038141c52045260103041480c5c0400c0c0c6103031030000790003140001c0c0c0d28400802503031500e0004001450145603820702c1c0c2e0a0510505240c8118080c00403038a4112009000001b0142c00d030a030203c41080d13001c84040020720900600b46821a03000c41801c2c200c1c1c419400300500c102e0321846c0f2400d510303941801a08114409001c9203188008000c0940d200c00c400184158007940c060201d06000d1100141401c0071260 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 252605485 1250 252604235 252604301
    0x90308150f13061a04060219080901050d0207021f02071d130c0b030103050a021003021e0a051c05040308010501050a0c03140c1605090703090503030a0f0e0a06061a0418 74
    0x4c4038010503400003001c0c012039030100400d502c600326003400c02c035602c8110384441249015408455040150002e418481c2d2034190301943d54a5400510744080001c460510303030120030032002044054006c2c044000303000b0b2081042040b1041080201c0c0d8407603a20b4089500b40c030003030100304448407101000c3c00300d01a00624040c40c0038620540013030510f20010b004001e0003000c0c1102c80d030700300350042020104a00350441400302c049002030b01c40e61150442d540958041c018030f207900307030b004050002643d03640340184c02c6940a81e000f0713107440000380d0721040111880e100790140000843c440d41c1684d0002441164803084074035032416072508080c0d84195650402c1e9180c2040306040c03074000b00a00241c0350562000c1d41003107950404200d0300300660760b62600c03404010410101c0e0b90b550390740004201450307000b90340912020002d0b50051442e514103500100a45d01410808060007030303c07881d038007003074504440964400d43c0c000c0d402d0395060a01200605814144e000f940100840c1c00340704108560 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 252606735 1250 252605485 252605519
    0xe0a0506040f02011e02030d0b030132151005090a0e1e090d0c0803040203030f0c06150f0109090506010e0307180e0109030c0803040c030c0603090308150f1306 70
    0x2d42007250003400c900005010030000310300c0e000000540e801005010340c0005c1100d5504210010101c1c003c001103000a005040900843d4911449020003c00306100702c0203412408400c15560b0042e9182c08600c454880c1b1a940065004401310302c0d095041030203107019003400440145080441c80d2554545800c01800384c41525810303400c0d100700c500c00ca000c0c40302103500000c2c4200404028683c0d0500606803408005c01034007410780000464155242402180c0e49a010300004580c0d81d401901c007141c0d103441c2103c0c0291050740070041b040491030b24601450400c0c1059642c0240c10781022510001004060942410300280d1b100401607914284070001c0100b000c800480c241070020340f105015507094074002c0700c140c3d240071a050000394125443c00101c030703080000b1949965651a11102041c00307500007401050100b440010801e605805c40415035120703a55000700f5850b00d8624141c003480d843c80603036000742c0d1044142c6190070321200c51440f00304554001b19900756a0820717850403007488 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 252607985 1250 252606735 252606743
    0x910051507050d03140712060e0114030607080705120a14040303020415260702030c1b041103100302060309010f050a05061507030909110c0d0215060a06050702040e0a050604 76
    0x700d030803018820140081d00034003034141030034400b03812003844458007004001c03d003c0601050f80c42210360a8103d42c080e901602c40150422110351b11054800c05081e10400700c581300e4030400c4001100d82c0d20840d1254000d44a0b42c0701c050406c00070608901e0a044000c104100c1c0c0d641c1c4000880482c01c00b180014003860081c0c400683e90b038148240028070003c605c10710020701c4501b0460b1500440d1011215000d01d1026615010716103400200700d040d4030803021021082d02c6000c0010700c0003401d000c0f041a180350211002c1041c800b8007045140300703010403203010a04a201034002c00140c00c0c400002c560007403521000065062001c40078800302d80003500d10800303807940c5004021480c1440d560160241f40c44005041c00e00b40c01c0c0da0002d000c11818045c10951a0b110320080c4070821056043d20749400a40007a9074042030710380f4000b540c0c0e00856401c58140c809032001714005041103894842a110f240d610189400d8a076003e01014048240c541c5d4110301c949240301c1c004c64424089240103600c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 252609235 1250 252607985 252607987
    0x71209081c1104060c0209070c0b0109020408011a0f010305071b0f05060606070807032106090b0a1a04060302130b0a11060a0507090e0a110c03041701150509100515 72
    0x10502240c08035080000074903156001000306124041e0851345c1d00584030780c115003820b80c0741d80b070707003c00c032003082c05c00760001c005a120301c1c000b1a83c00c1d125005001504c0702d100082000861044d198140c6505003e40709410a4960407103a03410351103500143c0d4007041d54148803040020441e12111711240d81d030300c1030f42d05c03500f00f09094007040780c00c0c020320380c002c14220750160801e24592103003e2a4411400010f0034001002d900c802103089040300c04022040c03040781001143c2c2d0361031101e400303082c800c40f0031840351010340c1c00407030641c80909000080144001041741443e007030034000d41c029804481b442220302344200c00000c01125000040500450f20b0b81d400a10880060b0002c0c81e2010141c220a10b031400c0008100015038000701030001c0711a02120700229458100c100401028149092034160000082c04111524000000c02c00ca9a03038000c0705d0070b0300c0e80803800c6500b01d40c0c520441603041411300c00c1c100aa460440c0403207400900300802a501c0b0355031840042c15504c0069854145040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 252610485 1250 252609235 252609277
    0x13060504060504270f23160303050d0b0a0b0f090109061b06050a0f050406050603160315021309020c1006141005130503150a200307120908 61
    0x34503008400c0240340c140d5060200000d41130040301c2c1c00c0c4120320a0340c0c6030744a000c440c809105000424030303100ca4014901e07800b0324240140c030030005080080061650712850280002c02400381d09120110380d0107503550350800a5180811018100d114000b55000c100c054003c11a1001c400007000c0e140d0b400703076415954100d544005021550f0680c0170070188071403000ea024192250040c216640c6a200b0000038580e41c1d00c50900d002040d140c5c58002c0603034a80300402c420001c4c0e56100740e00071441281151a5401140010400d030600344c00010004040c01041c60100e04081d0017608110300310181c0702c807813543c07280c0da41000c82c0c110001810305a41705407000c403074001d01c910440c005040001c0301580c8132211400890108881140380070308001c1c0000d08e0404010100c00d407140503140007415504614001102845181002c3c0c4007926580e02e48510701901235503d41c0500c8404400713000310346c21a51000c1c070079190070f00038074105000b04c0d455810000004010340d009049401051654007a14a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 252611735 1250 252610485 252610489
    0x60f0103030818030d02090d0b0901064106070b09010614013605060a080103110105040305070b030702010219030903020f06011a090303070b07120b0306010b0a0503090c130605 77
    0x30009008840c601031030324407114403d100402210859606008003598442440e0701180c00c41c1d604070030103801c0720041c4060207071171601034006400721100100c4084c00c04a1810341b08200c00d18030320004c020601150309600045c81d00002d40e10410300000c2189042c09a943c882c082a014111740c007036856552181c045c080c0340301c80760410100ea0f00038030f4603400d42d628640c2405800320a84c0b000c840145a425503204600414100040142c00041e00c05074550000103c060410b030400c0c00122066200003420706c0507944100b060b90212500640207040381c038506101c0b03540c540d0014040d0000c5540130480541ca011041d1428407800131196400540410181030084c104000040744021940050300100b24585400d11880180b20400510660700c140400000b45144070b4004020202140b000c00c0180058002020318420501d240d0300380050341c684010103031229400d002d14803003400180455030403d407058028507800321228003220f5000310782c0c800044a500c98402a84015a00c4510901283c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 252612985 1250 252611735 252611747
    0x12030a0509030703270503010f0c03050a14060d081920070e0a0e0304080616081005010507060e0a050a0b0a0f0513061107080418050c070203060a05100305060f010303 73
    0x1040740700146050501580e40182104001e140010501c03c5101c50b02c203082d09038440031001804c00800811104501c555818050f007110314180020a10301000a54008842e0180c649021003040c205001644c41d1020003034a040d03015016121500c090201d0600840f40d80110b92a1683e00e460f0315001480d499040e043e8800a092040c03041c1c3c001c142d040042c502d0000c03059800019000006c5a441c041a003000c0c650700480d842400d8520420060282b520a08002d40038114150780d5102030079582e1601b00c6062029610425000500030040c40380494100e40c800301807074180c441558040c0c1c88d00d84406240002031403013036400c0c030a11820301220400c2c6c0d1003000d40c20300071240c046c8254030301441c0440840021274406441143c449640c81d580098031821108000e40c458440d50312291110302002d066030004030b000c0541d82c03404001c00e8440480b64141d58001d94010000c080b41c0d50b4500405003c0c0c040900038514600c1d1021000c070002d5001e02c14030303204036070745e0f4411242507165040080c21 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 252614235 1250 252612985 252612991
    0x1704141215041205091f03060605070c060309020612040c0e0601180b09060f03072102040b3c09180c0301030b101203210612020409080c12030a05 64
    0x40d4003046441040c0181075100642c041c0e04102d10030f083c1e106840d0180c816224512200e03600c440304c01140380080b0a5210207168140c40c03694108801a03e4680c169064460b0714400307400c0802c403a100b0814184030313412480b046480030740300703030b08010019900810f4420255411203007040303948810f04c9070510790042070707511840c00d2a040100c0d5041c0a50800ba156003806010b5a0071800280c5e004583c4814088403411240f030351156a03645002d54004202007850401c2c082d074010005001c00d6108514000d441c162403441154520b81001e0550f6929002c0c05a0301300c0320741f0b4403040004450705a54004c0c00c008990204c820b01d82d24100c0d13100300010700541c80189d51003030a00e003080c0704031150903a082c1d905403640100101140e4507a403440030103444495109160512040450008040d0302c4040350b581d84c844120035554a0450708040c0060301c1e81d5014004110034000c4001015281503008200458040c9071407902e00b1a0350491241040e040030031702100e040d400014481c140740180301d030301c0e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 252615485 1250 252614235 252614269
    0x30d150504110c06241e0d0c08060601020718050603100204061d0418080a020307051e011406060a05070c0e0708010f06050a050901032d23041a04170414 67
    0x24810f81040c0c80703170324540f84100e000c1c0100300c0140034804400d007402c1320003284d25000300398086048045c0b4003070743c43d403041d0b004200980c000c440100d0380d00d500000328101a1159a40e40c080c110070138451020007400c001389240d5151042c1c40b03402c0e104a403070b4030040010b00031940e50100b8040720303240880f561400a82c505401075140c410030241c42d000d001e41d01300c4111b600c0701c4c01c5a034400b105d6804914602401801a000b80503204516950708401c00c004541c03203001a0081c4040300d0991044101c51004842c00c5411110402c17aa42c00b070f40c411401050030601c0b030003050807126100c10000040020407503c41011a8013800103000c0364a03180c000c0002444140362003480d200c00040028550701070701000505050b2144d40408070024800721040351014004550320804484145040140640c4071080c200c0004c10101211200d4100c40200c4c401c1e0303040550b209010922040940107810020401d8035034000300e5114480e42010b0400030b00003824540f1507a004020380c0002c1000320703025244400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 252616735 1250 252615485 252615511
    0x50405060306010e0d05010212070813050706230f07020312070f0f020d020315060a06090807120c08031801020c040501050f0d020402040914010e0609060102030d150504110c06 77
    0x21aa1944200da070301032000e1800070740358440c40002c80c129415484008100f5400400e4802041ca48645054840c1c80c03507a803115031030307103515070301003004107074108081e1691b00002c07018002240a0415915000e612404030107004000207c03144442c1c010803c0503003c4400001e681e015460204100483c880d03a410000d45000710030b13601d290608804400c004d10850200e40c0210070b41d83c46050006a07943c019064030000c0a4404980a55030030440f486445222503070008105184102410000e8401c0031005001b0242404892680d025103040221003da4032007030086100e00b000d00181c1411240c000c60040500000800039041c090701920a034010392402c00108420f94503151510705080d41500c08800455690010401034821030700300141071402c10500705500700c200b2001604881180020301c18a0720790500300016110f0903204180164010300c440100341c02640d212036400c6803000740d119085556080800c05441162103d01d49801020400c843d44110910800c0c2c1e01080d841010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 252617985 1250 252616735 252616739
    0x311090117100e1603080703030e01061d061201060608041a0f060d110301051306050c180105031e010b0304031803020102120901090f09020c10090203030405040b1807110c010504 78
    0x101c0d55800224829408552164481c1e04071900a125501d13500c0c0c0008101e03140c4580701d0a204505501060044000a1074403180c2604c149040c0701d00d0b4203940020464905680c115210851501c0b806007800c2d6000c20b00704041032541000f44111402001542c80d508410701d40744c00c0103140440070a001c01100c511000420000328401c0030510707030002c811120000004c8540c00c0c40030280314071448154140d841c1105124040307901c544226502132090000b44a1540c0f14502c40b00180620020007a0401039055910411743c0124003940c1e0204441e03401e443c050072000c4198460100c2a40000104900001480145680440160030210009081c08409861035000075910600142c1d20031004074045401071681e840303004004018810540b40380d154503180c07070901c0029404121603500501c0340e4800300c151110540904580c60390010701039420185003100340b002510003110303c0c40c2d0010019500030390381d6141c402040d006e100290388540c0d24070f00b016082854814440c4003281885014402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 252619235 1250 252617985 252618029
    0x705090a0b031515131701020c01050a051b13090b0d1e03030b120a060c27060e240304020d0203100e0c01050705071e0305032101050a051c020102031303110901 70
    0xa060111070300c00b80c0c3c0751041ba5a400c001ca0090140c00c500410359402d1009102071030079541c000078000e00100182084110079003000c814144a44181c111801504d514100150052903005010341c81e4090007560b541c41803030b940c0b4460411201840300d90010350103008814164140708050b204a429282420840c6100e0342d040d5840044050040c0f01548442490002d03911402d0f403c00c020000d504101e250100184d07550718041128060304001a0890f05001002d250007074a05000d142c107614000300e80d451044800b0643d50004100780e030441001604040140c0f410403054011190641c800566443c03c030f07442034100040c110409042200c2880140085100030030007108031007000b00c42c11107168034070710744c0602c0004d280d101921038040816100c205c84800070100c00c28850742000500d69a0b2241d0411000c10780303a004c0c0f5508640404100c902031000e0700d80b61600c240c014012a4100040000e490880301850381041b03030f620321410300e1907123182000e4030704a01400d002080480207104a0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 252620485 1250 252619235 252619267
    0x50403210c1103032a0d0e0a03030c02150a0e130c0f0810050303030f0403020f1204031e060203090705030c030a021c030c020607080c0c010c03080705090a0b031515 72
    0x100501940c81c1c0307841641c02c0e550704208462031082e00b56400f00b030b01c0803001041442e00070300035100d6004d8001e142040c29494030403168080c1280700280409541402c503107049401107003d400c100e8114181030103001c12082d80002900e80e80130150384d00c105400270a421300583c0d00e081400125114200000e1036404c50300300100300d0442d01030b0b14150a55907202c040403103d11019500c441e0f0940000070600c07240412503c200361060b40681c08403a0021080059240c2d214100c3d59802c2075100d06000900c005400124401803039207036811150a0741d61140c44100c1240e0095031402082d034000042041141818040349460000440c0070300280030458005c99144402503445903035a501201a807020117000b0a04602d4072500070f0881c2d41c0320b11140c946945554000001c488081c03140c041045115807089007041d400640c1551100e106848040c1c0070745442d040441c01540c005200040814440f0448014500ca41004151101c003a45900c041c085c05502c0751031440c403242030400001100d0000c1ca4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 252621735 1250 252620485 252620507
    0x10506010f0e031c080601021b030d030c020309030105070207051318170d0f091a0702070303030209030f100b09071107140f09041b060f08010b090402070507030305040321 75
    0x3003801d0070040b2085000900384a110003101c00000354048080070303465401080e4921a00c02a021100c034068001c04061207141c18003a240d45c95071140140c00b0074540309401807001c0b4842c1307004490622840e28000b0b801d40f1011600000182d0001404000601c2d1000c4240f100d204180301c1004002c11406000d060b82ca8089005070840441104920f510303d0240304403091071000b44010442ca81c00002000c018140358801078070f00a40012000c0503407d052c1c410203005540707680040c0701d040d00d50703903065010303400000c20300343e00d4040d260300300c01540c0060040d064030b41451030b00003d039266804208030480c038020b0021810481c1014500005004c0003070314400f41d0340040d600d0200740e000c0b203000a500041c4480100c3d000070100007400100179018a01c0030031120154100c00d003058980b20101c8101021f03422240000d82620010080b420700c00008106400c00504054601041502c07010720b00200780d40300b140020b00c001003c0082c00160144454160081100141140c080490050111a9403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 252622985 1250 252621735 252621737
    0x708090d03020c1b06040308031905220201030b0f03070806010f0602070b0706090501060b0f0306010905011b0308060310230a021e181012050a090f080a031113030311010506010f 78
    0x2c100c0003204e9176034041134030011503020020303e991f4604030907155008440004003051407810034011503690550140e608554003242d002e0340c1802400c03a001100500089140d490b013001e10320100c5607094406000f00c4d80038040d5000200b0865160900404641010358403881c04c5402c141c800703010088002e011580c1c4250001d0002c81c0425060420a0040c5200d900c6110801d900080003654840c20300091480b0b04001d80303541d2202f41d074960055807041012292001601d100c030101c100060b0140c000c4540044010307040329405250440204101c4400100e81c40e200d6483d00c4d1217180b480040c100c40d0368031044841c000d41c200300740b0090300542040c110610100d001c00124102c0c00d50380401206402071500245000404516550701410103200b10003d501550b007000c1c0051040c0d0100d00414617410707404078009404903520346408516800c04200f00c2c0c10103440d2501c1c000b0880d16017016090040a5440142209103903180103020601c0b01d0030f160140382d0402c003c1182a80c2c014041c0480d10b101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 252624235 1250 252622985 252623023
    0xa0201020f0d021c020f03040306060302010e04060f0902210406060812040b040e070201090203010c09083007030c060507080708010801050907140a030606030b0a060b03041104020a0306030204050708090d03020c 92
    0x10480c1d0036410b0022002c46c01c00c051202003000020b203c00c54002c4804c0724000c1e2a128070210400043c0720584070300d40200c192594460302c0404c90071705994010308076580d0b581042061502e401980c0100d404081d0b405039405501d80c04180110320085c071207038500d034a500455a140c145820150440c50007207114020f0101820b00011703200c2e034000c4d000f10020b56030080080010009848010b00080d0042c0a0441c0743d10034001e080c00e415005a16060342182076801c487e0f10310f84d512110700003942c0a8441101080500c480940018100d406a00d0080b401a1580f601d81d14104c0c0000340702c040142e010b00c000341e0409050003c01b0030042142000c1d500388035500b0000c2d00304540821904410f42c0e200400151a020001040c041c9101f1203d0003200308040038005680d450788010864002a20081c0082c680c1004405e000c0c074056008010040840c1000b050544d50782e000201203600445190000c1443c0314100310302d0307880501150481c070109040850505c42c080c4003c2e43c3d501c000c2c0000a01641c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 252625485 1250 252624235 252624283
    0x40b1311030607110f2103060103060515190512060d05030c07030624062a14010c080901060f05010c050a0c060f2a0b04020d060e0a0201020f0d02 64
    0xc20194040e22032001a00700c8407141000080204150a441040e01590240a544840b0502c0205040c0012041e01c8590380004183c040c6180d141c1c0d0000d40b0b02414583d1342d00f000180c58440c81e45020411898500346600d424145d00d00c210940159001e0300700b08242040050041c00c1e01c4100b29402942c01c0e103800011603407500e889891441000c0c00d4641511804100104000a541008107c41d02c6042c503004416030001211181040d03900544010404801001d208426081030280300280c1c400302600003c48070b9201d204030090380100e541d00316511550344410301c507081900180c010b0001d10003000708501d496982460002140503032410001050301a0052002c00c00102048a410040c55070b14903644100c01703001104410500c801080f00c2d0399044c62140c003e0b1a20780e40850041100d07902002465540d0803101030004c00c1241c0c402941c010340c402041c203c3c441d40640c1110b40c0000c00c2d810740c1c2400017915101640c1c0641506500c00c00e0700710802036002c150b0722802200704c00e0ba050109 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 252626735 1250 252625485 252625493
    0x30601210621050c030601050d15092913050c0f03030c06090a030f030c0203120402120f0d3c0516030e040e0f061b0c10060e0906040b13 60
    0x82030650140c02240755208140e42c40c8030044040c606443c0c4501c040307440b1603001800749a2114004d100b855444449400c81402240c05c9149000c00c1c590b2007040040d03400c20690700c40c901c94070700300250194001c0009007403144214281c241078000350050012106406541d50f801c1e42e0b02000602c1c0350040325840c0351309000d61420400e48404030086003d40f1810b1426416a641da40140c0710160b000514044030075060764000d1180b040000d80641c081c615040c2d401c88024040c040c05001260414050115010f035001d05100b0010620441c40181004805100c0002c0020526010144004010746858080e01c60240b40180d900d0564141c2c1083c583c6140b0001e41d404e000f80c901c047c20851550620104142d8050035541803034404544c01c01084025940960396103810308901d08682d0301541c04500f102f00000521032070480d24510084c81c0c103121081403410092400b4081400d203440d80760621801268104441d030080511008008510f0a03880d00089800c2c06010f01d28440d0140c1c86181c140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 252627985 1250 252626735 252626741
    0x31103130303121d06040c2301030b12060a06080738040b0f0403050d050a080601120f020c1608031e0d09060914010506031209060d1503140d0503060121 67
    0x305400c04044921034014119502c1d1041200c0460708030910000204030381c41d0239503c0c0c0e2a80f040d00440c0f84500121b04006400034803200900356070151030b44045008032402040510b100b241940c0e404124549401c0d543c602d080c44603000199039515480c0703031281d07500810714201100704059040c840420600da50f9440c65100d00d41000061840008000f0107480e01c203c014403c4a22030742c12140d0311000b540c03048034140180d00f1007800180000c008a01d1541c81401845040e22003081e0000b450b803a400103202c01c0343d01000d0490903680041d0705515400d8508a84ea0340149502d4002d5440e102e4141c60200d0546514810012000300209410109030710940c4448075140e030003e02000398030480d0900c0790010411041e141c1081d070034900012020300f0003003144450000e202c21090700f40a1f8080400c11203810034110304070001c3d900c01c032a508002290400900540c0030340c040321003080c91450b00c681401c11446255081c018100107000c03440e40d07c034403126800b84c01251801e106040d0302c00d0302805 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 252629235 1250 252627985 252628001
    0xd1a0a0303090807090b090c030604140a0b01020c15090d0311060c07110f0108010603230705030402090c0f030402060706090c1412010501031509021c0b0403110313030312 75
    0x10010854000c401c00d6088030020b802e9403c110700b26501076a4542c8407100f515800c0d80445d03001903c1901041410005d40301442e0041c0c17000f00701161807222000045c03040b01c41101d050b004030341c8070400b80311156010f000e101d007070440a0f50301c5141885030302d00e00210303407040c40383c42401252884008414180310704813a2081040440c2554081d0920480d205400d41104800fa10110600a00e04500745040c000c40c0c005d60806841d40300040c0e01e00742042c1d00402c00346c0841144440462240c403641c1e610418071510580c0a41c48454603410f01e801400400079000b811b940d0080010002d107002d15002000b034030750003030b411590b07681d49030142c3c0380c08406818510001003d000d5500b00120302010412040034805030240c4a81925203000d40509090f501c081c400540000d5005880f564a070a0a41141c0812400a002001c064200c2c47e840c102e06e00c80d10005654cc42d2005050008060303002640302101c0704040000c42c00c010359001745c0403030305085c8d2100034184641784e040e403400c04085800a0703203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 252630485 1250 252629235 252629239
    0xc18120105070504090c180614300709080a020603060d05100b040b0315011406070c06030207060507030504080d15210c1d01180b0d260f0d1a 62
    0x7141c0c0c18440009061900309000e2502c2550030903000400c8648140038400031032048041074105a0b141140654110260041007290b1190030070550300804020000c03800d0b424502d184110650031074284045a251014180004000001c5420000b4407000030b01904015011540c0543d039413901000540c1c013003d4000010514041c078941030080920682c04a213542506640038040c42200c9070406446415040b8000c0e2501d03400300051008600900e001d01c0686405401d40c0d1500c10180c41d0b40e85505008c1e400040080d40014604040180c24015030b03801c1001800c0920082c20a5955001075001e26004418810b548000f12400700084100f00380007429000804000317a005944000d58509401038280c0d40381c0f900480000e450b003103054070000c1009503a4213a01059080408060460380c2c4210501c14860b280c248000f8aa070712402e0400c600c0d0b2149801640074078050700d0600c80110180d004910703411050001d545150009411220412208080018041c51481400d0100c40d01c0c003645507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 252631735 1250 252630485 252630491
    0x1e13020a0e07020c0102010c02150408040b0f131208030106110a1403090a1403030901140c072c06011e020109080403050f070b040b04060f0c170307030b01080c181201 73
    0x60544a0302034101e018405036402e1340e00081d444801a800d95803080c82c0c510040c0d00c110400003000c802501100d4008d0b1160b681c841c83c01d03039100c0000300550410303d01c100340084005502ea5400d01a104810002c00003c03c1075843da40d520b8030f481c1c28a010501c14041800340c0040d64070348403241400004840d079440600d40d18044c0000c1406903694002481301c1d4003541004401050201c4518400f1034502c4009009500e8400c025004441640c22050601540307013041c0491000c1e448107010300c20103020940708000710783c451170301c100030b694a00f450702002200c020010702c401d0341d80c01600b2007008280c6a03184042869891000c9005000b10000a04088400319010003009008560007840c0700f02c1d2003c03120120f40794004020284654454034541c404200402c0100318018143c040300c62070760341000232a2110035191030f0306c1b2541585495141c0c20000003080510343e0540b0035825944404c0c6040e101520340801144624824143e1080d5000051803100e4542d60711080c5101d07406085400034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 252632985 1250 252631735 252631739
    0x5010803040501020f010e0601151707020a030e0907120e030c06040809100807051e0903030307030603170702090a0e030c030a08040605010b0703051b07051009030c050103051e13020a 80
    0x2a948a03000307400341500500031103010b00e1034144140510401400c80d80003402c02c2e64038042040c01ca80070510460014402d0030321400307034030b414011035080c070941d002c0e0041d000c569007500e030082481c00c82c1c00c80d543c4202910014800b25907804640088064104240040d00c0d1502036469444c601990000d48001d02c0f4090030481088055006020131100694500a080c28804004e40b8403034412602d0743e000030b5007408a52928943c11401c0ea1004100300740007841c0c0f002c80c00209045a10840303180c8003081c0c03590010010404000410015040280c84907803c0040b1513000500401c4003134240581c0e84d03141c1e04255803017141842280d0350311100c00f00300d039554003140b040070306819003c460030348106141100004071140b0060071140d40c2079040c1c0c1c0302031030003148005690004021000048152081280c045540e48644421103039500c1a0b0700c0e1041024510316140c00242a1070300700f1810542480b0a000710150b140c41d080c0c01042a18503200c1a595a4020000b0781e0000240b02960101c5441742c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 252634235 1250 252632985 252632999
    0x70b180106080102070f0b090105130b060a050a03030e150c0c0613050a1d0115050a1803140115080a0f151e09060c0c11010309140f0106050a060207050f0d02010e040501 74
    0x95040341c6c034031450445145650303a0004a00300c0314100d5110359208000300b894800101140b0351180e01c103d0041064403002d485e04e000c202ca0140682045012900c1040e1401591814001880006400c0190306182c20348681100341c5500a01010354040c1e5800325600d448040d503095400041d1401034a4884031980c1d03442840e0100d00f6180301e01c502001c00d0390000c100c20300c1d03450884203903000b80d489242c54641c10134011113008401c00407408030320391107520200c0001e4031011850000860f4400100c0c2c40283d410084071840c1c3c150741b05140301d0380700c1d02e0120009107400c507025503100d4200760030700070030313403d440702c1c14080c0c0101b00021b0070303e0406c1340e41030135000010340c025424140100b43c20002001050001d0301c404002c80400b0381003900300c15006006601c240c015003982c0d44999204401080141e01c0e00d40f6001101445813020717515000148a00c2c1451903003000202781c144020085a031a1401103403528000d000c40314022160b00031b12505590107041d11204000001d03104201d0b940c1c0d00e400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 252635485 1250 252634235 252634253
    0x7080c0303060109060c17160501093c0303051b03070306030311010b010804110a09020d1b02150f070e120601030c0614040b0c0109151b05070b18010608010207 70
    0x800d203000c1035181d14003142451051040440040e4011604035400f5002000482e040d08501e0140940c0c8d034010042c280050001e00030b0050b25889000340070b050b030040e6a84903c2e44984204c0b40141e0854041d652100e151503003038034034103003901410009036075220628136035402014600c01c850600c2000081c09907040e416400042240d0080d42c0f80103941d85600b00450907101026001400100114007040109030740d03450044110f0f40080c03961801039a9045a241aa000303040c0101629a0302c0e0b06030045400504000013011007148044c0c429004564001e1042800c058482068803400d00300040000d1b01078108400407000051a14400d1000784c4029540c038103090200320340d401021900090214060310204041c8181124000e00b400e0030081e0343d04141d002031440018540d218554100401d11143d0f03d0203400200000c007040c002d401c074291440d03400e8a0648841041000c002560109980848040d00030301e40c4103084240002071403025014001e96040713082194400600c03d0101703c0d100c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 252636735 1250 252635485 252635491
    0x50f180414150c0d0f0b030115030b0601020f030f1e0403060c09091a130207020402030f040605010b09100c051c0306050f031c05160507061d03011a010f030207080c0303 74
    0x5045a04040b0882e009505800b000d40d4040c800341024046404901103075001030030706000080e40003981c0002c9900190035034981008030101c00c400b0380b000f8030501a170710505540c845002e0008125100440103c03d68034801d5030814406401c0126001c2e040000310f041010000c040c0703a00d83d5458540b2820160018904003c494021880800001401c0750060041543c0c03e141801d070422092400e8041c820200705101001304c405078200251401a0782d00e1001e903019415079060200ca9140c9850107a0032100180c014083c41c4a007805181125541c04420680500c4580743c01c0000d01c400d490130070325104074500e80c1c25202c000c641e8403030100c550560100c01150f1044680c840d002091030185900c40300110400008440c0000010b0340031350144004000100030716001c0a10110309484490400a441c1c002e107001900c40d01c040140310f0380d4010ba5510350314040307000b00711000103c0711000785d80321102c0142e0706002d400300c03c0030019802507040d61720703690300401a40d0380c442148050985a41c070031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 252637985 1250 252636735 252636773
    0x8071401110f0306280b0c010e010f0902010f0201050c0403061109031f06120b01151101060308131d160e062206050301060e130f0f06031709030601050f1804 69
    0x41c1812420311402c40d0440c0725031710501119001101e08015490380070382e01c01c45041402e59207411081400c0d0200744101500001c0c04180000d0101c1c4510005003080340300d10f03124046a060006100c0c0381402d00c0c080364101d0390700100c0010544691540d039403060181d5481c046d8140a400107440c0e81d103546070700e40310550754210020001103845003e46544465041009800c0700c1c2404014020401c1c03040114003025001c0c02c1166541d002c82a800f03003982d0f9503401c22907041d170022a0510500d6000003004001e425840007031090018400400700750840001c00c400c0346e50701e0b1041ca6072541405150341c06104440600a2a6034180501003090080078a038017101c20901450300000e029442102568140c41480d903440d900d58400300b04010a4040e503002101f14203503684101d611002e070510443d428400980f00c08940c451450500e84295000c0c124110f40b480801c000c41800c07907801103011030560300c04440d0b102a02560304080b80d03011802103407600c0f030240903005001c00d000e200072143c3d03031080303071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 252639235 1250 252637985 252637999
    0xc06090816060f020f09100309020d0507090b010306060c110105090a09020c120307120902030c0a0e0a0b10020a0b1b0a0c1209030314071b0f030215030408071401110f0306 75
    0x41580c1c03c02203100307000040302e071035200344210a494900121210304c0e460b03481c600400d458a860b0000b50500d035045408890a50000b84100100c1e902d41c05a842d08000900b000c02c100c52428501610300a101d0300028405158480c45c4015a070207103041d41c058000c050205d080c2581ca8039541402980220380c020580c0c0300b00144043d0100c0b20740300b180d10a903080d0b554460b02e141605100d5001c1d0107403010403a8540502481d0010b0341e264000e20b50010161030440b81c08606211260404031160001c2c5503003d2035040341c40010141d0001060040345912402c1e00e01641d446012700000144046440e044461002070004000341d485094151014040c84500e10304844080e4159446811440003d000c00c0c0a0702d61150390700310701700140080c01d01440001840d41c00b00c941d9400b945034903811402d2554442102407042d803c1412100e0303d01c444100541c0d242d400c05440d11300b03981c040c01c2c03070007400f407105200c80301080c20b004c2d0032040003020080b0300180c4429a0f0308200c046500100c48050013210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 252640485 1250 252639235 252639251
    0x10f05100e0a0501050d021302191706010206010302032802131b0813080d0b090f07090e04150b0303070c0b030609060d1a07090e090a05060903040609060c0609081606 73
    0x800d11a0344d040b034900900c02d4103903c100e030703091100040e07000601490340790f400c2c4114013521603a5a600c41c3c1103a080c0e6284000c864141099600722500641035904540c060f000500042c2c40c0094007400f40c0749005402e0782d15071815144440c00c400007d00007034011082c06a80c0d580710f0b1840e0030a0503948405207816104100b00c00782254150401c6404540d12901c0f4030084002c03440c128000c046007140f460002c142010107002148101c1d41c242c070808200300020040011140e44450158082e02d00062541c2403400c0540301c50003108504040d43e001c0680c2c82c8042c0c4503a41d010000c0f1000c55500a40f010a01c2d070380c880c1a0302d41508200e40b4107006e80f54400000d40c091510744403030b291341c5510604440b1518520b54844404503801008039003407000080001c101d000060b188540300320040307001003400d0341652a007107013040c8003d04080c40a910034403007070000581201202007941d02c0b501e40840e04440ca81001c0000d0900190050001c2d040022003500281032020b264030200d0041d6002c0c45112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 252641735 1250 252640485 252640501
    0x503072322090c031a07080c0901023d0c080c0f0d05150604080109060e01060303020622061404060605010905030c0d0212120a0f0c0f060e010f05100e 66
    0x1601c1c08003901a000d90794204001c002219034854400765000d240601d0500d03840e9075400c14004a030301220502121841c08101c1c442d13901401003580107201c281071900703082e203c80020703550f401440110041a0144002c20b01c00c01004100c506407802c100980c034100403650503640d80101b60300c001d10400600b0500000b032a18100608490b041000400715620702142102010000c0502520701c00300982c3c000040d041b00c3d40c2c0d10001d000601504d0000040603a107600c0d01c00e0484901c095407003034903414107108001017500425010750180140780300401e5542100c4c04190541c1007014000c240070b00c0c02200ca19111065500c9130f109074400c0710100a02604c40d001540d02005038840c00b0342c0740d0f0109062400c9410625001034080d88090070048006054800107400d0100150f940c0c26449004100150f035140d21590038907204009007040720030602c0d03984074060701d002c6080001c0d000b02d40b40c510780114800300b580808440f03568540c2c2040f503800d068080e070307014200314801d204602c0d90038004144c0034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 252642985 1250 252641735 252641749
    0xc030b070e090a020d090203010c030e011a0f01051606020d050105030c04110a050c24061f050306040e160b0d0c140318030f0708210402030a11040605030723 69
    0x10400800e07000305070b9184103c0001170751007a140c2d42c4401d92a040c2900058409004a9001c1c11880c0c801040d4224494991401c40758104208201242180c072440c00c19291b000000252803000e00c0c00301e6517401c2a8101c0001c054085200810380c920004c0c50a24801e041d030300050580307004600f42d4982440250070001543d03035004079805100c400b00001d10009000b0320090000702500b60079100a500340b01e030404410b442c560f1503505107840b060200407851500f80000742009400c1c1c400404440500350b0b0040080c000101a2405660345404204288100304500c0344801c6498104e03045154075010320030415007001c0b548003450303418030019964480c05080d000741c4046800e20346074210380da503c0411030011150840c907650303804208404003040040e4001444114043c0c2c0c5603076a5840089884601c070036010050201e8200123505001c01654003140c0241000e030080e22400a0394801c030002001030401cbd0b840039505200f041c0001070090302407400c0400c54400780d442c041d49a1100014441c1c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 252644235 1250 252642985 252643007
    0x80705010f02011a0f0f06031911160204051e07020c03011505031f0212010602010902030d0e0603071218050f0c0102150103030f020309150903070501090b0403081b01090c030b07 78
    0x3c122100c4400b01e118105000c508605032001012403201c6d113a0700011900036481512000d01b449400402c503140d622042c01440207950b0301036010340c6448919806034441510040780244a10744407008641c6845080c0e51080c60407041e41301000c4182460280a07568005120825001e5400c4c03412500e40f8003200c10001e4212032000e406004001605441d01e0903e145144003000116424040e150505880d007600e40c5c0a040c26400000e24861315004051922409480c41c60402c4049200c400d80e40d1260f80540e41c00240d14148513468a00007060640034083c2404600c6604410312001d406011000a4040c90492030758152080c421001004a0302d504070404055142e2142000400c0000e00c988514841e83c00c4910560707003045140c000140c10084010214486808041280803161a080c0000c00040c5024284403183e0340c5010704400450103030344000350440744080b4880307040d9001c0c0c004c4c412858000c14003c10000c482d0f446e00e07460350441d44c00150384605590340000c03c1ca41c010030344100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 252645485 1250 252644235 252644261
    0x1c030506012703030e040f06030c032a0b0304020f040f0f050f0606070b070e0307181b0210090201050d0f050919031e030912020f12071a130804080705010f0201 70
    0x30a036003540c40588218245c050140d03005a03a0b01058014110703544030724400b9600c1030040c859454074504040d4421192044aa0041c08125858040c00082404a501120f12030108140c07a5650760000075915a450001d154015051103040002c1764025403015803007100003001000180c6a611140d00341c1c4070101c0d1120b80060703080007900041031000348aa03521401500d0104224206100400e0070680543d102e2480300001d02d442c10341c02006030050080a501000c411040d049564038000e50ba07141e0691003664075641c5080000943e481101111281d24031444148071940306c8680120052900b00ca800c4035a000701e60803074014a02448a9540c0b40d074040d030722583c46160104c4001162541a030744682403603500d642030030005010280c008204903581d000b80030201490303080e013820b00002c0b001e02480072104110100000c0c5040d072041750040e040410525299607680e455841882c81450003822204001c240014815000240b01056032400ea070340c0100c6ca203001205070b080c2c07610030324516 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 252646735 1250 252645485 252645557
    0x8011703160305031008030f270a060e150c160509280e010c120f060f09021308120c010b06030103030c0609062003090d090b040b03091c03050601 64
    0x40032074802c00113142c000d600740180c101d04a648411131807841e840800074803600c03040455060002c50402c0c0300800c0381c0010401400410100304005a5100d00340d000f048140664402004256221030210084c00e0880061030383ea148220085181c0c0c80b003280a10901011203c0c2d800302d61414411402400713078032115150040c0d81205010950000030300f45242118903561481d8000c0070b0402d00442d80034001540750123000c2c984c4041e02000b9a0407000c150304501d41019010040ba6950383c0f04a41140c1c2d41200042c1c4070602d5a210941310321456210004030b2280070405102d481c086401000c001021900070050b244030641400600d0009100203070110b0110180a00801c01e190003400b8254456a40024541840d1640540e1034901d2181c203510044040104000510200143c00980d15241132200f4042e150044c07540f0a449980101514010301001289020404102c466000443d1100140c0381c0407014030000c0c010981150743d580015141c24050b000052243d05000b900c00070380c207000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 252647985 1250 252646735 252646777
    0x10b0705030a050a1407110f0f0d0f0609050f070e01090507051801020709020a11010e030712051e030a0218040608030a140714010b0315090307020d1a040308011703 72
    0x26600768014000324818883c017042100380b4910404020070006215490a102a568400a020590f1410039006004098807000c04815944404080b00c0e03c950001c01407840801e140340800191200031401010b51160360740c0200f42d00790104030310f020b54460014554290380da41038404d064440550320603011881c00c00c2800b00d504a820f8803482c04407410b00486a116513540902c20032139000101450000f50080d40d0300c113002c60300307000703c1c041c10200c44000c43c102200c2d41c44000c5a5110204180c0600100066940100070a290000c900103a41501240c80303180c00d041c904060360100b100a4a0800101500c1e425032929200304800d4452010003035043c407072041400d0740c8508170210003240c0e400b0300b4441340c0c0000d09105500b60340c1d0380071803002091903031403103090515150b680000c040014204d00b042101c40309000007a070f0502601111200c92400da5800c10040071801c10003a0300c80c2e190305100b0002855000b8810504944c1400c0d0101907985540c01302c10317240c0c000e0031a080b01458a81d008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 252649235 1250 252647985 252647987
    0xd02090a24150305100e10030804080102030f06240f0d050a020903010e2b0e031b0a060203040b03190e0f07050102010f0b0f010809011503030215010b0705030a 70
    0x452540030012000c00100315a054000700540c1002041180c41032291a8050118100d50072214034404050304044c0a14140003c20450042d0140184202c2d0781c0c00c04001400d104a0b802ca5100542d000054242e0f2643c40d2604207001c2e40c41128001c214401d040301181050403c2d8200f201d0307a41c2c104500603a22409004400706950000704096050141403151100080e510301c039142c02000094401607035003600106160a40e03c202e003000e411500302300071128820803050f0071a030f138081818000c1090041c7e20003054a210620300305841d010302c10300121002944020000b4200d107a41240c91400d40b5603242c4040341da0348520700440080c0b400600c041814161604580c008031541400c0110744a108080c60703a00d0056060000101948071200420542d40c0a05c1381d920809215201808122031960220300e001c1800d41d00103040080880020b0f0100c08298800c51902d1031005420b8042d540e2410300030740d01c03803180504001c10215403000040c408108011100c03010360040181d03052455100d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 252650485 1250 252649235 252649249
    0x30314090319052410060905150d060e0c09030f06090c04051b07230705150a020c1c050f0a0b01030b070210090b0a0b0d0503090607080405040c0c03020d020c0d02 71
    0xc0468044c45040c2e0801d405401d08a07a1010b264a02c05007041a4904501c1d00002240141e1000f4148400341006015079150900700d418000101181c0f10390324624031201c9801001030350b110101c8548a101406904501c5000500c8803038411012a84185442e50f14140c41da031040d1505101c070fa00c038641102660800c1d800a50340b00001d0100e01022400174034450800342e102070812110000c0ca1a00e0064891101140140d558810340081c0310440c1800085400e000d4000b8454544100125111882d6071003048182c00000c800351060680c032400c1110100f4600c4071003030485041c016108001000300000822100030760304106209070780e0f442d640300d8410140d07014002c0400c502030100c000c074541035540074045c0c90510641c0307021842c1c9032107900003084030301e10300c4d1051140644003480004101e00000340d03640010201c81c0f40c1c1c0e03910013600c0c3c0301803148125400560000e041526002d070480c0c1000c9191440d038080d07000c0e01c150681d135030780898448001024559000495800d18009414506 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 252651735 1250 252650485 252650533
    0x1008190e0102040312020a03180302010c0807080d0e100c0c0f08070224070b0906060a06030b010c05010e012003010f1a0f0309011a010f021207050c090702070303140903 74
    0x3000040c5403545907181e00c4460802010700c0070140c4e00c0a26070000709584040341d00440404150084d02440c2160b0009000b0084030102030106640802c0074018040b030030045450700c0071030b69030030003458011030031064494605801e00e4480c5490200c284103d130740110ba190400c43d5128a0380c0b00101401e50b40c096072030300031f180c059800c900240743c07110441d0007164003101400c8030200e180741c07207130610b261100c0b0380000108044460b802c0307242484000d450f06181c90f800e44282d0708020503141603000042303820110b840d201414960911550a050042c19802071801503510003075000a444140c5100ea0f45100c01e03ca5454038100e002c0c0100284100c3c20000005036100d40d00c500c4c030340140c140b00b0380c005070029208030a140e50749440c1c0040440680c82e0111007203500f0b080220003002c0081c0e001c0e40f01d081107150342915580020b4280d042000500c01c41b2800140148000454289040029a00d401c9070104402040242000042201c0020142c0b52180001030046c10200060f0f00701006002c440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 252652985 1250 252651735 252651761
    0x2010809031318090812010806060609010503060103051807030f0b013204020d0617060a05061e0f060712030501300201120f20130b0f13060806100819 66
    0x1d0040d400018a43d0380041c103001b020490f061106504200b402801d002e07024061902c500020404800142d0b04042980e903c5036090800051565403242209203414001d104084e0601601d000801006082490200110300900c100c0200307a0b241c50240544038a0a503904176a40000c83d483d1142d03080704100b0410720318010304098144001a216941910ba4503007240b880c108103201100041c002c20005141c0c004e00c031500601c403606083d808220200f400a08031340288400e1039601403951941601004611400340c03015644011500300554222003640b20341001a00b032078000a4804800e150805951034040d0441c41180306079040700e1040041d0013070482c1401061440031707510103a0b522810090f00200740c00864511410000030240414401e4070308002c03901408002800d030024a400010b81d190303100e0b89607a6220300311030601d42d8003c0c03114060f204400d110300030030050b038403669041c0948416941d158944071154800c2d900000100c401d0f0201414443c0a0340c0c1d080160380000500400ca = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 252654235 1250 252652985 252652991
    0xf13050f0a0e1f031103150609010510030615030c08160f030c021014100e0108100b180403030c0924050a050c01020711011e0c020405040201090e090a02010809031318 73
    0x100300f5500584039041c2c1c01510b003800319245074211400c00340008107042038401076021a519100c0c0008400d00018011107014030940d2000c0340c8058040d0703100d400948003207035400c44d0101075208001d02038000d0486180001e00741d6404035200c0c1c030003000001d220700051340340c50340c221000035421001401d80c1500d200c1140720702d04004002c03007007034810b80d00e900103c3c500c120070300d191005074003943d0b240c2c0340d02c50201e01e0b00c0600100b0525030089a000c800c5803102d04007085810310100080c1c503a584943d0002030440d5602c05104c10075403d6400208400c605c0d85410800580d118010a80c14605004550100403aa44500c1c5080e00c02c0004210071b011304c0c20180d080440980f0b00900f26004104100c03100d60083d04207803419030700106c01040004002805c00070740c0c0d0444038010200c03100c0c0413009000703548650202d02168020754800018042c203085900b43e500e40f0444440e40c82c441c650341a07001c01c58030401728030030031400703c01c84000305040a049640741785804602c0c0a9866070384003444075665 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 252655485 1250 252654235 252654271
    0x3030507060b0d0f0f120203130506030c040308041205061b19050c0a0b18030403030519030f050a0504060b37031731032004020f13050f0a0e 62
    0x13032000d1410b4000fa0042d84241c038480d0051621081d0703446414110030565105205800b810800e0b4844401a80c500752417458481e12009190440390007980c000600000021402240011111512100c06800380c001c1780c2e04c507140d21104080000f0b895000d00140103080104650900c0400d041304010b101a20b400c40c9080e203200f500d14180102e01c0300454611031503000384043c0b130060004021040b510f03500a540b03003d1650b540585103201e502d41908370003c28685510015010f64000c2c0700070b5070905410321482c0340000c4030400520302160101d65003442c1820740c45041c10b0018010654034080c19966440910030106580d114203020600102c2c02c0e1018804000240e200d000009200340541d200c544503102c0e0a4100030601072500446010501d01a6007040c43d1940817104013200e82100017540c130142c2d1145241007003108640c03020382060000503034191800b10403000701070841070280407003281c9450304108942190084002c43c2d10101c8900180702408038192003640103075542c096800701c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 252656735 1250 252655485 252655493
    0x8090904150e0309040e0309101202070206070f1b030203060c0d0f150f06110712030c0609080d060e060f01050f0c0a38041b030203070e040507060903030507060b0d 72
    0xc0c2d07902520b0300160008034003150340381000d001c4c1e1150701920901540c100b40f200300110b10358504218200042018200403000c0c2c640d02c642c112100e1035000340c50182c4d81d440a041c13100c080c481d084c0044401010b4402000c642c030711a03034050001e81e0b90050103400c3c6503e4011030a5141c0d001240b42a00c40c96070780c1c0e030220f2400c4c018070030702c040491b440072610103042c80c0c1415140c049429600440c1484154a40300900d4100400c1c00b1094840c03c0f5000c250741c021034142116440d107400303001071801345820000400c1c80100800b0700316094402c107007444456180c100b60031503c002920010340002102d1030404c525070041c0080e03d1019180104642004011034040e480c200010320700780d07001004800f04412003000c43c4403602d0b021180d42850012544800441440740100810141038450210074016110140e84c46100081d40c0050031191100e03101c0d810b0500e00380003928100e80e1480b44080c0010b12900030407414040340d03015100c443c180f01258413404040e05502c000b00c0c1d4030540e42c402e941c00007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 252657985 1250 252656735 252656741
    0x90a050a032910090c0509061b1902060d0b0105070819031104240909060f091d060c090f0a030302010b130b131a030f030d050a02070809090415 63
    0x110302500204020341c12030140b010941c00840340142c0c01410302000c0001c50380e95030400343c003121594100081c0c18604010708032180c0c01a14505540604000f80b81a080068031850b140301080300010765101c411600311804a41615001c000c0d0040030900c011a441c028590011100260604005190691365510a0354651040a86445540c003401d85000d07403513458030590010369490701002307190a0030080113200c0084101180200d11143c0c0d2039007440c0c42d01c1140140000d0001d04414040551207054000b507050346800360062192604481c148100c420400340c03600c1e17288a202828180d2141480d01c89a43d0005040d140c10410f801040c0c44580c48101d9003900560107030b400000c0f090b4000080100810b56242820704007802c7c2900c5114540d150b480c244000b220105000400c103400400303016071003041c0c044103a45401380c5455800d0303105011004000d4410313000d60822003075982004460483c0140400175065400903c13559078541440d1403807a4020340580650012202c16403010016 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 252659235 1250 252657985 252657989
    0x14131b150203190801030c05040f0e0303070e1807090e0a020f03040b0a1404081b010e072402030a0e0616060c05130605040506030a0926190206061302090a050a 70
    0x580c070004403a460520382c445503e040c0c0c08286040034655140d07864444102a85001e00781c400c95443c014081c40010304c0c1d100003c010400700689459141002011340400041030340d09005500c034410b032101c3e8440aa140030b01c648079580b01e03031000307a080950710340e000400103125070b414036400c010f0f0303101c4d000c3c40d0001386205070700c20002090301c0d10b00000000141d45640f00100700504000e003e0100103802e40c4103a42052100001515511110b40c120502404052200082a01600d1404114039840801c007164070140040c2d140f004081c100b000700d80c0ca10901d00c102c070002d00c8200c1c0441c000e16000005042084a21030240d0782c01019031900d104454151400c1004504002086408001100c15030801400a400c2c09070901c0d14020104800c1d1000030941c001582d5030b1000d500c1080074071a0070841d008020380c8541041c90383e00310601c45c01d41c88040c815143c620344540031421140700040742407255502424459000c48003e0424019401c0205003a17404074040c10041140d4449950001c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 252660485 1250 252659235 252659237
    0x7030602070b181b01051c051e0603060f01140607060213150309171308030f0702010210090809041104051003090b0a09080304140a12050d14131b15 65
    0x4810b0070100d10040790004060f1031050fa0350800e6954203210008150108150b50082c00c050f9a214840c0881c08042890060008151440c15040c01600850321500b084c00182010300d00800c0d032140703001c05a40e400c04882c1812500014401481a0350344d4840c0302d909040041d00d001d0038561030343d850909a800c1080041d92403035050004004c500002000700d00c502040d0b007000c010829068403030035076804580c0d9642000d1080024900251411003143c0d030010f01040d019603480d5140101e14001d268800c0405a00500c5810381c882c01c0e58420b40b254026031341d0300442d9075241210030414400909080955480340314020f020003d003d803140104141030428940e00010243c00030720340354008010107000c0000306841c0c10300c1d8400258000044031740290300120346a00804070104907501e41190480d0007410000c604407101c1001d0b0300074020784010a04800284540114403080e0606420210356650406100c041a080403c07001544410a4040010f46c16407458454034040c00c40881c00e84920 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 252661735 1250 252660485 252660503
    0x60e0d0f120e010809030d1e0908041d0112110103140106090503150f0415020408010c05120a05040305180f060301030503121510050306240a0908030f030a0902030703060207 76
    0x14000c1d0381c0407410500c04442400c00b80058288038048565078000d213080f0b10803007542e514404d0341c02e234010342c1c0d080801c0b0540101803009034483c1c5420500740c3c11901c1208801c2d007503950610a01240036001c241a07071101c14001c41500704503142d80f907000714005241c906141e07035003142000c1404541c2e4403a010f403000ea240d90341841d2400081c189804c00c42041c05070700e41421760a000f01081c84c1c0c0503a9070000c0d08070260480d81208200940000d01c200c0d402060305629000c0c0b1b40301080d4006000c1c1241292040c2b080d1031556400400109565040710003c0000e5402c101c00040c1c00480d0800c000e090034040c202c02e0b0102c00c420007107000c0758421b0300300340d800e6480070601d01281403010b6861540541c101001280c100319160114803c085000204001e2280200c009010343c0c03140300d001844000301070301e1400643c0b19011a00c81d5a48941503400000b0706210020a450a0000c2285c00ba000342055192035942e481290200030500380e8001c903814083c2d0500040401c406002a01350380e402071a440c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 252662985 1250 252661735 252661763
    0xc02040f06170a0c030311070806070c060c05090901031e02040f0504140706050307051e0313030207090209060906210c13050a061d01030204090e0115060e0a060e0d0f 73
    0x182c1021264064003900350384001a040c00003a246005202100e0741424200c0c050a81c05041070704255840d00404440e10612040002c06907211955030015802500d00b08801e00c1403030b0b0112810f00c604484141c000d40c90100402c000340001b40303908030021004145a5500002e940080c050b1071600f141c0041305a01c0d801400184400e00c031348140c8031481040100f82841ca0204040c1c2a40001405031041c00008200e1a00c0341800b01c81164050207408074540d52480d140f05034190000303031400709400510803c2c0e008035555000344210798036048002c00395400c0103400c00c03c002076507000c0001d49908505c4c1446180e1980e281203011801031040c041d0154840030b1030303c0310520507016648400d02c10302c1d421000701300c0240c00c0881c903003040c21100c0198100f0241d00005070041d10959000c0c1d44000c0c50300401c0c101507101940500a0070100104030302e0100e558520071600044854580c951000510104024603405028909001080908500f4800ca059102e928450b5000082691000310b04041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 252664235 1250 252662985 252662999
    0x19020f1806090d0b0705070f051c050c03091507020918010c02060f06010e2103040e0610141c14010311100509100516062918070c02040f06 61
    0x4003900310359003650514104441c200c0003d9680c15041405400500d0301d030040f07248503100300100c0c0d5451303070003c188203112805407405555030b107109106420f00c0302076200c4800240307110300308913010b203c1554021821703c143c0e00304020848400500040d03c41d04104030f15030058840a82c074620812000140d464500c5011000509685001460340c0454000604021800380307481190f40d0865000c0c6001da04003044000801c21250700d001c2c1410050540e00c0f160440c101000004005660112039540c5460711880c040c4141c03034804074805004204001a85840700d41ca180107404919a04042556600743d20b50044045550300704403062949507a80040c0180300c070044400192840c00c1d030f1800b140310501030008103207019080041e481030115005002e40c151141d010744004101d00310720300304c1411142ca0154014074191000d50302810820801c410340000c94100301c80c441001601c92000307940003451184070721800411601c140856005017a0160b01d552042c2507000300301c0d40b000a00d65090642c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 252665485 1250 252664235 252664267
    0x3070b0f04030b0c0307120b010507030e030f150601020c03060c0a0f140a020a0c0b09010903080906210601021c0503010b090103021603030f06050a030c030807020303160b043819020f 80
    0x11268040d50230410662050b0341d00074100c0301c1094240c0340004005080c84002824861804840440351007680320f00144042c080340014000c2d0b00903022105c05160b40c0013412389603081250f2007029003105000400050740100c00002509001d8502600200f60700183c0b904550441035442c00107a000941000401c070540c0b8100c0081e001844050b403c05030507800080c0703030410501004101c60408105001907846a03020f495400c44501342c3d484607480c1c0c54000040d001ca08403042c50040c8105d1015118207003800c2c507034094030520703641d03140d1942e8200280a81c0c1644503000d21410142c0c200900603481000100022696109a0b80800c409010100b03c400b0744420341c1142d481400310903010800116007102c0b02c03045a81c0b140341151070f0011800042d0031401012179808042200c42c14010402c0203400120380309a00c500c0641e000b40080303145040000c070b410051103802120700c0e605c0d03030344469100104543c0103802202c440c050944220b401c6060360051180c1200b242c0d80412242941d444540e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 252666735 1250 252665485 252665507
    0x60315130c0e15010c020a0503030a1107092a090e04060203040c0b030721020d02031815040309120f02030d020f19020306270304030b010e10030203070b0f04030b0c0307 74
    0x80000c040c1e0806515001c8110043c000a90521025034031300c01c00c40d25031550442c0100001000d4a03104d052443c0c01900a201c80907910050f4050f086020500d07035000d10600c1e00074014401001500c09680b443d4145171580d2101c2c51007400b1400c4400114403180c3d04196200360702c2680301603180d0402e8a00328501150720b400c05003940f1002d02c100700d070081d4060311034255000f0044020100c400e07549680d0000780304100d00030542d540000304101000c41031404c4460304003246000c0311104603030780c84605018803090f18001c00041c0d03000010005100c043c84900010790007503485025000d1142d0002c3d103030200080c0d039600560004552400042402e000f03030702d03610031086082e4003143c0301903000070b8072228018480c421065440c038465060b5503104c0298010b2010f014200daa403240c80781052400b000d001d2141c0701310f440302a0000b41d149400700303083c00300300d07a070150050001c0381c1000b260541c1d42d000844088040e90b002d01000002c41c440a04440c020082c0c01420b95807824000401880c3c3d00d018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 252667985 1250 252666735 252666749
    0x22d030d0902042906180a080703050714060d2d050105010e1c0602030c040f0305060103020f041811191d07180510050d020d05010509060d0b040b060315130c 69
    0xd01103400030710701c54802000c00021304413907542d920021407480d400604620310041ea08982118400f01d402800000c010007980d005400301c501455503507215a600d030100400182e000f800c24401e981c480c01541e04054210070100050041d000440010240c9005400703c040e0301d180d03183c5004003c59604140b000f010400250fa5010225002e81e10110703e444001d600100010340c004000307002c201c10001950058040c000803500c1d003580d28101301d0758a200038007040e031007034004e034580410070f03e000e01c120440e9800c07695480b0403120094551424481c0010201078000c0055528405062006541d06018144010b02009038007851255229521002071070b01e414000000d80c4040c0a0001407804421520202c48400a0805d50030742140d01d8000c980f161007000d400460f24005030000c64008034160745080ea0325200903951a0204414000d80b194058403044c1600003040c081049060590340c800c60260032110240c4441a0300142c0083c03c46441c1441c940400d031000c100941071079000024125 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 252669235 1250 252667985 252668021
    0x601080309010e0616061401080f03070f020f10020706090611100c0302091507050c03010e03041e03210206220308060415030b070f0c0c050105031305070f0501031b022d030d090204 79
    0xb1b4820000d2f5070344901403014051502e109001d10855450400c1805403c501900ea20012180050302940c1d948850040c00f000c41c9002c04041645403207460303051135688042d00240704609050300484010600c0f4402501099000c01c100c50b22500c441d90003040981c1c6610886a0740c039600d040080c10300d0b0400620b24400e0b4100b41c07881c002d0400000659050340c0d0002052028140018405100c103c0d06600c010070980c5100000160b20075083d0550702209495000e481c919500c00c3e407072000c414904003601500040d1840150046481904010750001c07018100090110448010380160401c42d80101d41c07220340c1d2000c0000300b641c4401014520308043c244000650040e540b503192104440c0111810001e02200007a0300758120304101c011141c020003521101c544866140d56202e401b4007407640464145000f03102440095450210390f001d403517015100207000e0710054400c0c0181c40e140b80d000c0c0d04c5112a107000b080c105000134452024030703500005601105205010139101080f07444041c0b520 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 252670485 1250 252669235 252669253
    0x9211b0c010819060509151906050a03111b0606030709022503120606112e090213050a020403060f0506010207090203091914010e0601080309010e061606140108 70
    0x6040038881c0d8001d115100c00e0b034403d05400c24448014445644500c0e4845022000d10541102c8060721b40310760501918400c08400740000c51504003640351150a00003007081001c00700a40c801c5e0b004000c40382c114080300c1c2c40c01000400c803903400d0200ea401c8d400150805424040d1501c0d04120032401400c0d07619040d401c0240003620040d0090714642c49030300c843c07140d04980c02054440d5044030084811020104125520364400074501e9214244070f40640c481c0b1745c0300d0102d15010650988240c0d05119001915107a442c0241000d491041012a009000d03425a403000d04e583c0d00607a88110403260005032510700e10b083c08000e403414070048140a40c5480240110b50b603000c00e050043d503d02003000b603980c0e140e080e080c91800c808442000704290526002508200003148a005811043d41c000e004882402038900c0d15858280b05460059004100040280d40106544a0217120040c401802c2501000c10029001540502242d02070780d280c140d040082200d41101c0d014050403402845840c1d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 252671735 1250 252670485 252670487
    0x21090308091005251e0f021014070501050a110a0516020a05060403030504031202010c1e0c150e010c0503090703030c02060d0e0d0e0117040303020309211b0c01 70
    0x407140c5032185004600c805941d40e9030500a00072109000c404000f40c2c4c0f0407001c1e80b0001500d21420b0201128590350382000c1c048401e103c15103806950b600a0415842c190440e400c101194500907291320603c4080714401103a141484050441540500004501860595001811a402c00139000c401500170b10403400016401b40580c1c0c03c1e00b03010071907c150414540000f544144255010640c00307140003d02204142d882400f8104980c0720310b1a005d15100502000d03801e0b24a2011705400090107454000859408542d2448810740f05040c9000e0819580e00c0e85101ea40c03400c41184079554503002d2102e051002403103040380283c0c4a14140b030035410500c0d03605454048a1001504101145582105540e42c0c035044070b1042c040088204644291414003a45800307004207107801041c800030490005e540103c80e80d8144035056003040803240e580d41d03010340c02904090801c6c071051090800b0503100c0e030404280f0128480c640f18171561180c0d103004030001042c44a9007083e4154001c122a05c15603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 252672985 1250 252671735 252671737
    0x602011b05030f0a0e071e0909050d1b051903020606031209010e0301140f010e09060405060c0c01020d05010b0426100c0507050615040c032c010b090421090308 70
    0xc5031583c6401460389801c0c44120242200c03907030b0402c05000e0880001000804003805007103c5402c0d0701d81c0d1340460399408602040f900c6800c2c01030100d800103031045242c284150300f09d0900010a9002d4110030400362200307450280c3c0c4071010300d085649500480305147c0c04202e803030741c8050114001c044150764042d40114601034165000d042c031550b00c000c011103076804e41180e01c500030030401c501024980321600b40940b080a00ca2010f440020602150610501044403485150000000c3c900360300c1c3c6880004582c7d1040b40496890f540c213014080c3d030402c4900826000b0003c4401c0c490700e0320304003210a00c001400e04403080c5581004e00528200c2140840c00c1c403101d500c03820b00001d4007030035050191030302c0c40744c080300034094020001044188441400e850301c40c100d00307031010082c0c1c0c66203840650448040c165a103055103204410407440150a00310b01481255440c0081000351101010604002c015a0202e0304a00cc51590039410940307425906005c091901e080e00c5107a2031900c0385c4510f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 252674235 1250 252672985 252672991
    0x2130b031e031b1e0f06040209270609100603021c02011403070f0311070807140708100e060f010e0c07060605090903090102010e010c0e060d0e0a0305040602011b0503 73
    0x103a1100d552181c01040c0c02c1c001d540036942d10001c030206444590800e00d84420044a500c2c02d000c10302a5420341852001680c5040c200d0f810009003441d856035020044016002080700216103102e071b550a0703810b8804003110105040800040c44941811400f650408003075081c4480010f1401e1800c0001d0398942601816445400a19075901c1d0514001242d4140410000f48d0701c00038004107105000750310847d00303c2e403c02d8507501000007560a04e02d0701094410380700090303e602c07810b20803100890440194001d441024401300d6030362680c0c4900709400e00e4900b2400d01b0100b640c505800d5404081406055030110440c03403244240d43c10502d1000c0d4519002d088904494004a51075040020070751120000e0031000f445071100c0e1418071881c0340d81c3c0d400441e05c0c900550030715441c440c10820502420301c03120859202d0b03000c1018a002840407a0700106400c2c503800b82c4940b644004082e06000c030f482e0250280d035503156210700740b40003e400d68580b41410601c0c203894030803025030180d0003000d582d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 252675485 1250 252674235 252674263
    0x6060a27091b030b041110050406111f060905090307030c080a03020d15050117010e01050402181011060907060215040f0b0709060315120201050717070b0402130b03 72
    0x24407201d050038039208240d40b10031915180c1c0c4800b8804024030113046991403183d4070a01001d151403c41d5010b0010841c28082132502161051000b8081d080c02600c0c0710010282901c1125101c150540c60b25120221f2884811411566240280150102030140580c01880030008524000140e64010a054182800a000e021000c00c0040c2c12500ca030b0115010310458000901c003100b9072054102224000703106603804207104000c01800d19190304070700b82c1203030080300414006a10744400e102c0070358884038008030b010075250000f054940d070b010050583d180e501d903610303010046041c8a59240c001c028012503056803002e08100a043c1e400541c1d940c1361140e603084a64561218604001c0007109404020308100740c640420650a50004800341210303c1e80d602801045518814417900140501410b5400702c02080580c0140d4001c5c00100100d5100e012183d950440d022140800d60b0090b200450b8070070109020f000c02c1d85072504140450141c100420002a448000040c0c3d8a0b10540c0c5011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 252676735 1250 252675485 252675491
    0x503030307031512031706030109030e091008030d0c0f02120306040b0406150309060605010f0905040914060705040e07050909060d050102250b070207050a14040603021206060a27 78
    0xc0c3c40004481c4400500c0401880740180200746070103041c0c2041d82c0440c0b81c01e84040000100545814042c1e0901582c050300e4200400040c00140141a04010001307440d211003080002807444003000101402c4c07281ea00300146800005000402030000c1040040c1158804000740ca00e0010780c0003183d4000000b1200081c0540c42500850701928665000307202180c00c0301000354410f074158001d40c1460b4450001089070b140c45000543d411002c4501c42c6000030266081804181819403018440314040c03000b810000610390540c5203442c03400c03980380c0d000178000300c3e040200e9465131314159001412806e0541c00d002d81c2c0d4010a05814000300590320501d160792040080c400e003075048130030510741721185407001090f50f009021102d160701c0e411101c0950910008420f10307c0801c43d0b100303541005010703d40051174600c16400c42c181d820350180d4881c0d0386280010060b43c542d408014928070040c0039008601d0100100301101110b0343c04038100c65a1141c60192070006165800b141c824512800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 252677985 1250 252676735 252676751
    0x90b03090a020a0602030d0e0f0c0402030c0c010c170109110d09030c0203060a06050a050405010308030402101407030305181231030b060a06030e191e1b0f050303030703 74
    0x34600e060040400690810f602140c04203045501200034056030460038014880c9080e0072249070384d5100c03c150310a000e90042c00c8085018505500107503080f8840b494143d04180300c2c001200d00b15540d601c01d03000881c01d100961031200e0880d04d01c9500401a400701000050142000d2402e41c1c0300f0050042a065510f5104034201405041c9a00e04ea40c1c000e81140c0c0c0901d8203031032010003420140100ca1050001c048001404e14060003140d041c0d07540203440d282981c480307909001c00c00c014500d11400b40044604588e0001811001408100e4001c0e600482c8a003070107450324440844505c0c00d00704a8000c13413840f20000e607600c0200ca00100e0100265038054001102191882501c074174001d9001d00c0c0306d034000041c0821340300d2240c01054110f506600c00c603a0f8160540c00c584485c105810340e41c0001d043c3c40d030b0340003140390309a120a01454071608151094002d01c0e008040c200d02c2280c45aa520600103200c40e090103284010301080b0f18040b0a103400c2c0000240e4130300000300349904040d140d80c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 252679235 1250 252677985 252678001
    0x150108070314160f050307090e0309121507031d160e0a18060204090b09010f0b0307030b03011407230d0e0c1002030405010219152408071401090303090b03 68
    0x20425601e050300301c3c05000544603031a1300c1449205210b01d82c4203114414001c28002a60b1150045c0141ca1400a52800b08400c007484800d0a0408488041e40200b4603104440588600d0181c450040d95a00281a800e09a021544002000140440c69000b000e003c8041c0c1c0111420a00b03803050b403502c102d4180e0300d451880025140703100380210300000d900d0507807081042d1900508240c4100d04814080643c4031414022401024400c054241e800704e80200541100d050095401100c5407030042252549400402e00b99814a0800109130810000700024558000244040c0c0c41c542c10014000c48450440304003540070b1640a45134407a03480000d00e403d10410000c00450a801070024141c4004c00c5002a441360041e1003080c5c05400344000001c0c5a40c113403000d8105481d485004040b40e41030840303155004240d009030f19501c0b0220f015040343d02c030300d0b440d02460003020844001e141c2c55017000d42500c0c2e80c81c940c0c030410381845a0440b0030310001e9044850201a03a01c0c6040a42e00c0380c0e22001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 252680485 1250 252679235 252679243
    0x4201c0204050a06020703020a06082701060504020a0507020405160c02040f092a06020303060d0303020a140f07050c0306040503041a0d020d060e1005031b040b040c050903150108070314 81
    0x101c0580c3c0310508000010310076801181b00030449000702d900039a0305513100c1f0155902c0004540c60700c2e188805c17503100f80c040b0705200140b551041c43c807000041c282d42c60304042030407a0b101d00324210220b400429041c3c02c510302030054507400a1350308416000b12025000140142140c1a0020722a85d143c00030410146030700d5100140094100d11981c18596501c54007010000900803908a03911601801250040c000000c6900420000d004500707a049543c804400130340000c0d81840810044a0b4048c041c4251040039055511000c4007107941c441d0103182642c03038051011049030094000300c0c1004007040703000c000c2e50708440005c5945445400c018003d01030b80e200f4407402980702480800c1c110700810684c1e000d101540e1058801c1009a00e90001200030103040c1e01c41d1070346c10742c00702e0000c41600300d03004100001c1c480090700100b100c82544001400b81c034144603080300007441c089000c42032443d04014100c1849040c580000303407075051045454454410b80400f81207498a4030707062444220403c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 252681735 1250 252680485 252680489
    0x12080c10140a0b101d130209040b0f09010312090801020d05070906021603030e06091e0301110403050a0b040807020d1b1a030f04020102011d030904201c0204 69
    0x44140d880d80404640c0040042540c46200d2022155200c0002e010402d00d00c110352001000401d8501d12442c1c00e101141c440d4020201782c00114100c061380031042e12550386080c0400b021030401341e181c0c4d041c0003c0c00304946606010074031810341010404026150400c15038107594010650418040401406442070707862944038144075880003031070307c20307151a9034000c034000c0c5550340c8c981c0076140c0c0d0707000e04a07560200c568544408a024040c2007001901500c910b803140f10001d00b455051000100010f0215902c1c100e0f503c030440d14280c1d040640b0315080c402c80c0101c036586c10340641000c2c00c6880b116900c60403142c1c000c007000400c20108040c0704002c401d0700d60b15075009024481c4141c1d6880c2400360780c29042c1c001c00c0245080080450304803003111640e400482540c6446045035034000e02c6422042c0c0184c0300764155580c945c03030400c0044941081ca42401107041c002c40d951300c03a060030710045850b8080072a04e81e010204a84009100040840c1c40a40e15a259140340074040d49104000707114903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 252682985 1250 252681735 252681757
    0xb07031e02130e0103030c02040b04060b0a080702010605030f07030519031707020c04110a02070b160b040c0b210105062b0e01230f01030b040210051c1a04090c1208 72
    0x3d54000400c050b40084040c0c4201c1c400e0f1014007000e0180c0d010300098035074070301030b00c0501d0006001c480c1036079228440c1c0a512801910000c9442d40d5101c0210741095841e446c2c2e03410302d8100030b5044c8280401001a084004603600405400032030580f0024803641000a242c5c046807190303030200d07015610070004d2660185006004010700010165122130562000107610050b00421400040c40c0098105540c8480503200f03001c04941100d0741c40740d00010004104461151315114045986d80c2c45d500a0101b0944c074100c0300782014007010f240810701c0d0059010500c1054100151100038607004144500444c290b600080980614014000684440f4504203003941c80d040504400340700b0020b6011400d0756682d50040641c44071049240b0340102400007400f42c00059000c40c005040c0342180e561840802c1c6811740c1058000e030420307400e5020100105030030980b51003140912500c4282d2502c0b0400c401c42d01040160f04596817011640311a1080d4910303054802244024000070008540483c036003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 252684235 1250 252682985 252683009
    0x9150d141002041d073e030a02010903090b040501140c030c0a150b010503011409060102030d0f0501060e090702060601110a08041e0e010f050904020a170a0b07031e0213 74
    0x71104131100c8500c101c074100a51403803d2011070019070107907a00f00000c80e41c5080c04256084564030b80c60344215807242d8011990300401540c41c45038000e1015011402c219400480c01183c0e40c240280f01d086a60005041d100c81080104810303030700700444c42d00146c840d503172403a200c1031108480303400c42c043c0d00a01c1d40c084c0100d000c504100070708002c905842c1d0060000411407604d400004442c0f5000c01d01031816641100700c0f00304001d2a148800c590b00000500c1204d02d032840b5821590140c1d82c2c00c1e0f03452403401d502c0d04c006105240c0c20070902c001d0350f042a00c01e02d90034a007665000356901405001503042c0000c60b101100c5500c401e1101c2e0300031540000039503079101e0341c800108404003606035449840280751080850001c1e803600115040b04d00004502907900c1c28801009140880a0012039010032403a000083e401c3e2513f1080f8840040800945582071150a00c03510324040288000300701445c014401d9807503170050042c45a9824500c2d401602c8030425040031004290302c0d0032080760181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 252685485 1250 252684235 252684239
    0x804141c030f020426071706190c02030702190b1206090a060506030714070b04060504020f0102010b012a17210c07020f041b03020909150d14100204 65
    0x40e04404000d41121166410004404482038030000c83c061406010170381030903074400f010000090008000052900b00c103550302c03e80d0300c16002210228180b03890025801c40c80420003010044080343e80c3c0300c084000144000001020700070344074452000003e100b2145903c003120800c01c82c00460380540810301d0380c0c0340d44202a96062a034207004a81162180955900055041c1c0d0300e03002d14000c41c1d102030040c81c25a2520780c0c0c00d4800107100c041c18114180d0602403640410803021050f80568041c910006985c241030050112902600e204241035a0400c0e42100da56680708010440b610300301507105690120307c007044030700c0000450b0090700d610f681d8200907034141c02000c000d0586a41e03407039000b41d29400d00a400c51002d0300440c0c001603511014407140700507003001001c02480300b100800c00030345201d10440c000d962858814481000940c0030559441d81d0400300c5c94590422030411b08606409054000510100c51a400080c07805200781d85007032480f00c00f0030940c2403043e038469066441d66 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 252686735 1250 252685485 252685513
    0x9070504080c0303190f0309060908040503100e10020901020c060304030825020303070c02060712080a0b060405370605030f010e071e021005190501051807080414 71
    0x508140590740c5a030003202031040e0680360020490302e803864501c21000c04040d04481c1591078021400011082c10703101e400003000a041d5103d1018807911034000c1ca81c5950500050518182a0b030720100b01c0c680c9007403080080c03400b00180b080e022105154015986400000c0100d08080c0308600041d00020003000f80420590031620091066810050282c01084203108580051106e00203ca0140c0c10401c04140a10311503801c200101d8006094603142903503a42c0c482000242ea1000d10002a1540d024040c000c100e60241100080b42113400c20304141c00c2c80b00099004402c15030207081181108051800e049a941500b2120208540d00072038650755180003500e01c3c0d100b00c90340d84c411001d400001c2000c00d04000300b00c0c0901881d545a1220341a00d8818a40c140400031030700b4154803500c00c1d4200755484a002e803038410310080d071450166510f503401407003c0e1031068111500c200c112011030500880c110240c02d511100e60320301f28469803160f0500c900a84c001c80c4e25501c560150100b9004e000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 252687985 1250 252686735 252686737
    0x30b12030a0f0503040803040b0730150806060f041e020403053708040f06090f0603050c0a05070c0306020f0304021201060b1c022203051c1e0e090705 66
    0x505803610302e4044800e40c02200c082c40125001030406405101180200c1e6071448200d81c0107020b07003070400303400c018607001c0307076032012640c2d41e0601003420051201d42d030320503d0240000b207100d0002002c01c0941889242c81d19041c008102070300a02d0000817868240d500d0f900700880c0180c0070420301c0e01c41c0d43c00b014030307001a500501003502c01c1e10030b4415014840400c14554a410381405160b25002c032004200382c100422100000d4401460500000c07036825111009040100519180e4070030651801030307010320644140c2d1086062502d41801c000407980744e04215100e5001c1482c0c01952640c65140030301d00200642c102a02c0e80744045814403d40310010300a40c040e0b0300071036400a004141c00c00d02420380b402402207501500b421301011803940380402c00c0c0c03c1c1300f590091026050690400d041400150b07000a01c40a40d103e0700c2081003400300a101c01880301100c0d0b051103280c645601c2000d0966091340e0381d1021000082d15540640c64440c0030007a200800080000d2032500b0030200007401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 252689235 1250 252687985 252687997
    0x312040b1201120b06010c0201030e010c03090b0a05090c09130c030c03021e100507050a0609050a14120f0c010f0606030b1809060a020702030f060a140c03090a12030b1203 75
    0xc40c101e0800118124000e00000b9410503406000c0140e15690140110349801b942da03003c0381030584900114901c00310a02801c0c8408050f5540001d0b00d21035410412003501b80600581080d51810092100e42c405c080f8100000f0711040c0d0300404141c64001c1c59040c100920480a00050b5040d80c0120030050b1755695002100e00071142c1c1444c818074240701c10760420001c100b0542c800d4890010184803400707034024029050052051300d45104050300c440c0c041d10701e81041115075402004940b010015071b160034086c0303040a18014949038581c0c4101584611078201000c4180714081482902040f094214001c4d03081c0c02d00d010300c0603554441015020b442d883c52604d00c2001121002c1018401580c032052240f074000c0002c1c07009849001c0078100a5006040c2039030503000f0070b00c540000c91004c200c6980600100038001882ca40003800d1040307104070103812256505010800e110441c500000d424001300c1e0400c10403400d0b020420030940040003101d60203078004103480b48060b82c260700880138180d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 252690485 1250 252689235 252689257
    0x2030321150105090f091b070f0201180e070c020a081c02010e01110715290102100c02060a11041211100201020a1211120405010506030c030d090b090312040b 69
    0x30703100407500700558050003400703049900702980800a0519141c0800e41c00e405c4911034090041c0c0003440b10362505168030500041d118280000000d00071035034030114000f042c1d100000012082c0d81040c0d142d906011001e4600303030800c40350020b12815561484e039901d00401c05013080f40d6007102c2c07020315054040b050004c08409540f07041e0105001074418042c01041c0710041348218035000c40740d56442030900501107e284041c2d51074094040d0244000b41961518101c01d00d074128800c1318600092500003c0992680e1041c24400300c0c0350b01030340000324a81c0021042001146400d030000340c0e02c0c102d000365405241025001d044010501c841d0300320f82e0b0b00104060f0340700e4100350b0341540260300707078422403282c13100042c4031000e01e40f0104141e5000d1307450038607944405803803c1c42c20b03440c11042800554090701c07165582c00070b2042ea4501044a542014400d4010703224501c04c068025020380c2040c801c4600700302001801d0010340c0e07800d000100480f43d0910400e51035030348070415048a034000c01c000807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 252691735 1250 252690485 252690511
    0x7170405061501030203010b0406031a03070b030f13081602030c1012060e0903070213150e011d01030222060509040b011e0323010902180709050d0506010303030902030321 75
    0xb008a501c00d0084034182c90030542100c0c6050b1401c0c000701c0c0141418200003800c0c80e032105000c01c059400340702d1000209051144a9142c1c20010640c651003400540740c0c0c00a6218100b42c0d100203a0400c050341d9004203645650030b58004036001103400e144101503040d82c400d40410210140302e8000701800c004c0e4850800810400307441e07005409104000f0780c0c2a02a907842840010010b2502008040c0d00000741d02e400f188039400c0055840c3e0380b4a05400043d9564582d00c018044d1a10340c004107440001c02c4804409694510340124840c403046000c0e02c140308500200e8602c4004140d00108010f1202801c0501e00d881c060400800e0054203000304051440d00d148800c10704c030b07281d078502402d880d000903240c0400c08000341c0760902c19401d103030340c812030395250050b902c0581d454211898107190284078045051400c50f0004045807170541040e413240e40301110700c00100724000740140c19654103080002e004175031400042c6c614092190319601000e00e420792015080c0740001b92600420340311081d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 252692985 1250 252691735 252691771
    0x11101090b160512010e0910052403011401051504081207050d081605070c0e070f020c01020d080a09050703170405010201050105010509031b060d02040308180108010f0e0717040506 79
    0x11510fa20400c5404401c0ca1169001030207100d4030203000d19005071445c81104c02004241c0f00d81c1c0140d40e0101e60564406003041d11007001c03210040003031070b03060000314000c1110405602d441d100400040c000c0340c0c0289200320102c0c0221a00d00f04030f4010700302c660111104401c2c02038030034080781e00c41306080b10a40640f1a09200d06402100c60900074100003140c01080400c80700c6c200c0d100e4004680a50301080380300340000e00c01c1c5014807901d00815040e6102c1c13a1005c2c8109010349001110b030b42d02811540028401059030307038031951442e0002c034040400318884059081c07189c42e2001ca500301900084030740c00306840e1105000010000c03110280c0007880180c1c1d07a500151201c1c0980b0680c950160410554556403045100e07440024040061002e400d112b05520040d00305d801030b0300111180c1a00280328408540480b000c01c1100700c0919121107a9814584a501041914407030015004d09160218000c28041c44000a04c10824420400301d483c00c3d041032070391035000380c0d103e1154044621403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 252694235 1250 252692985 252692987
    0x316030c09110d02090d1202030c07080705130f0e010c08010801050603031602010c020d0506070c05060c03010515070c24110a020108012702070320030702010c060b011101090b16 78
    0x25801c01070301c81c451964100f414140d1034801941c04800005e5203c070280c10b00000007000100141c0b0903041d56030045846000340002c1c00d250012903040041298004002004a507640010540c620142c1d000c010440ca00d80361210000340c01440c81031242542006a00c801c840e5202150030304a8100e0002031002d61101e00516403039200b8580c015843e413034a0840c48001d54054202551002c1c40030741107460009417505c403c0e0515000361985030010b100b0003551020b0100401c542038001310785050040c41d5501d07240c009000801c07089001100890013041c1581880981c2c0b2a42c1c0007440d03e03002410114140840810f4484500c04c0700401041d01d0038040700c2c119a000515099041c3d040c1c40b000318036400c104007810000e03c18400c8141c0c02d07151500000b914603d03800505080c600c29243c07040380d81820300c80611184101240038119600610203c8003607a4486000304000da00840b0004510300c02d200100c503131040c0c0c044066071a40c20002c1c035408102100520900c00c1601e104401000f61442e60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 252695485 1250 252694235 252694241
    0x50a02030709240318060609020c011d0606090702030c060901150905040309030206031308070b0406050702060403020a0b151909060609180e0a0507031b0506030c03070807020c0316030c09 82
    0xa10070070040700b604010800701d030283d40312000107851171180842c00d0300030f59104015200d040d04991181900417034000b00a01003402004039000038260041c0c1c0543d80810a95a150070042c103262140340c00c10040f0b20703858001d10886400011843c1a50041d281c02c4002d24040d00c03c14a0f10402000b015500080440e41780c403926000790b5069444000d458a10340030000c081e00090b00d50020005008101e6001424401c0200801c0c0d110305000340d054541070420030200c680042c030b20400e42d00240100000660701003160007160b94480e540994944800403004500125000c4054000080400342c00da002c080407030038070845c2c4071490184010381e1545000c4545403254400c5501c0003684a4141d4000c036000d03045141c0d1414034a0446055403141c0d202c10740780c09444c1c1e10a607281510300c0070a0380382001102c66080a0715080e0340091442c20700443c3d4603501c0c48000e00b29020800d51001080a942c820312032012569070080482d29034050459a4103105082c51004964a20400000103032410040c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 252696735 1250 252695485 252695519
    0x3070509180103230d0e03030405040f0515010519030f0b0a0305061015050a03050402032d0f030307120b030f010501080c04150e0c070c03020a06090612060e1602010609050a02030709 80
    0x400904821901700c18180c1c0e400040d20442945800300f4031020500d0b4545100e81c10b41040103110100c1c41e802c00c584a81e002807005e91441e03040020030040304000721000b09000b507032401e0340c0c0f40c00900120b07200e181c40b004008072505c9a5010745000c01c00020b100000645601411805140d01d0150350f0703c0404c0e11703548501440e5a000b10b1170911221703000740c0c029030120354040d0000d405d0b141da80d144248084e00d0119081c2c10f185c2c005401801e000c024001c2044180c038980d04070b9005500e18202030201500211a00c40740000c2140c036a90705402a8405200740314641c407031740c00240101e50311180042c3e201c41c0c1d0b130214a03024030300c2c01040b00c41c0e0070100300c120012101051a442c04c1602d4541d282e1a0551002c08180c034802d420080000c01a111100060014000f6a1320419041d0030043d0040c641611982100c0e0442d042c04002c0c041100100c00b2150080b006582e055520681079500b41d0161200350b105144131440d10b001c21401d5465030f001503204100360794455402c0ca4032030b95602d04000141d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 252697841 1106 252696735 252696803
    0x2805010204170d300b03010209181b04150e0604170102040e1305060a020c010b03060108070f05030607020304060c020a03150b0405090c01050f03070509180103 70
    0x540d80071500c01c0c000814140c4001e84030420007040d00d4141c00340c84d0803944c440d0b0134850b950f02581140c00c28840a04498100100b07103088511840d8100e8003200301080a00b0000e42c0c40c2d80c4c040c2201c065418040e1440d03048038908008807001a09000401e800c000e00304400326040d03510050030304180c0758100000d40c0d1356080c050780388426074000e0040001c9110040710000044e10202d855a40b10303024910040e110203003041d003070380584101d00015405000e4032002207045c2e503022909009460074036a1118006564005150791a0000c03a141d10058000344014801e01d80f241c0040302e02103000600080c22180c40c3d40314070318034001c6420071103842c641e1884c54940c24240743c0580d5a200c00c81401500e42e6a102000181c22807184002d844107108000001444050090003a1500100080d0006540446001003540c80318020301040d180417050011101c0071a040e210814000006 = true := by decide +kernel

theorem cover : BRFrame.Cov 252517985 252697841 := by
  have h0 := BRFrame.cov_init 252517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 252517985 ≤ n) (h2 : n < 252697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
