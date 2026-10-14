-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:48:53.804049+00:00
-- url     : https://prove2.me/submissions/65709ac0-2a52-4c12-a661-5a79f5695004

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 566726618 ≤ n < 566906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 566727868 1250 566726618 566726621
    0xe1201150501030506030304032105040b0c011a011106040821100519080c0405090705041103040c0f0312030e012703080603010c0509060313020d0308011a09131d0709 73
    0x1e40d103007641d040c0019210b010401d0703520302850001034504407480d1400c0c008035a004c5001c0501d5680e5041071400c01e0b54840391800140c11402d100b0b15503944420707094140c6001100c000d11900c4090a15010210b20303d140d00e5644c960082c4000e15500740040c002c0c681d610703000803411000030402e2010055192003505010312000714456507000b2442e18100b164101051030580054452080051842c1c0080e0310400c0041e12006c2c041103a1801051000f247d16122405001400305100754038903580d04051401d1448428240d211101d11000c5100500c0010009036402491142500e1701044c100c0b00450060700410611108601c005003450550052050009409400034004c2d100c012301076507400305040c240c81d0290820400142c042000c210baa1404801460b0005031001041d64030b00c142c1d6020440040d03c040081d00070501c55401006030180c1d102c03c031249128419103040c1490404c1c0d001c10141d005076205000c02a4442e60345c81030840c1c407003c4131070017142c5100483d010a8dd88212000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 566729118 1250 566727868 566727911
    0x3010b06190e060406050a261311040e030306121c0c0510110301060c050c0303030f04025806060f081212071709011401050d120e1201 59
    0x3404108070250b445080d10300070043c1d800f100c0da1512564940f410f103c20448006002200c80aa0500d240c404840c10408010b4130620602030a004101001d180c1d003030510141d05406241b5200300d050104501c01014003000740d9800c0402903450082c8944404507181c10030f200f44072201240756600c041e9403a107550000b01250f03054012026540220f5030103242c0b10a491505a02410020042004005082c4200700c0c8a1200b40a42e0075581490b6048001a040d1303802994040c0030246600c050205605d018810228200c1c1494480d014220070441c0801c0108411840f45d038440021a49010503641100c03110724010107019071501401c0c902e4034001c40200141d00812003085041003010541480004940001e031580d21101403c1078054200c0d010040340041000d403c10001c910301c1620103c0c44141d29000d1111580040f4103080755003101996000e050348400d100740c0c203000040c070100d080c4010f0050901c42601e042180d10f43c0000c041a0310b03515801e80fa800307039840d0039000010998401e1070302c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 566730368 1250 566729118 566729167
    0x2060c030c0106230d1202120f13080f06040f150e060702011505010c1203060e09030d0b060f0316031b0507020901050f210a080d050f07050f0a03090203010b06 70
    0xa60038003c0031111080c441d80954140e54108081c81517807404200300315542691035030b2510442c0c8114a4652002c20150004d0041c11068030300866441945001d0004c20700c0a04503d0004050740e070708050810f6039500c0c0c0604044d242890100c8140c09010f103001c100e4001c08000c0701c0522002c104007551700e0382e40030304503840001548ac200b4000da01001e501c40740350072524169a8a07000d00d115484480000c1480d038a00420700d5030b108400502480810000c0703200d5181c8802464850b211900544241d030a4980c0b203500c0b40108004240c0a91113807819203800421070001e0395200889050258014040f600089203607080c1c0901b00700c40c440d400343c010400030303200703403030309800d99a0320707000d00c0075103084809225401540d0303c07400d4801d0040413603803040e43d0046204540c02c952854484111543c03280d034603001407640722000c01a580004002194200403280781007480c10a503006409900e00501070400c041540708c03c250750035950250061015508000c10050303413120a007451450030710304980107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 566731618 1250 566730368 566730389
    0x30b07170105010207050f04020904061e0905160c05120d090501060f030809060703023a020703020a050d0609061109090a0c0801030605060105130902250512030402060c030c0106 78
    0xd222120300500300141225010b030024400075007170408208041c1b04142c206500181d081c00f203070f8226651030084000422001c2d1000d620329604182c070540b508070b26008140c3e11800d00041c0310310101110307062038002d0201d1a100e680350100b8a425400c10010210310032070051b0100341010075030a15070005c000144078600802580341d8a042c0b038840140544406040424140306881c81807c00f44000c2c00158030910542c1d0310307900003051580000381d502000840405c104503116014403241100c001004a8900007004d0507840c55002401d00112405454021485415040308102040e0040c2c16001d50201d0203104040180a40b412142c0040700c0c00c074171601c3c4460100700d52000500c601d44140c500d543d583d6009a080d610341b06c001e408007130310701e50400c00300b00009040b10801580c4a0003400300c3c40000369542c60200b00844485504410341615100a8040200081c40014495400424402e0242d440360f403a80000350036801540e24038059800001001591054103501500c2646c0003004d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 566732868 1250 566731618 566731637
    0xc060901051f0e06060f04030519111816050d020309030c070614030f04170d06060306211502041728020d060e0f03070303050906060d05070b0c07050901030b07 70
    0x100d80302c981c050307803140c0f00402110034040340c0c85060040050022503260301d455803800344e4a6480c28030f4520072031144c1c42562400030b048020820008400821580700710348880d841101c82003041c0040d400505035005031901e15990218590064060b43d88048a0081c110b40728900101920746036800501d07101054050f4505c04120301d40100c00009010002d040d0060a40d03660180d0f6001200b4054000e07a001403000c0c120815a02c8a04000c2c05900703262000400d100b0b2a101002c0c0580e40a42c1101001011903000654003c008005404031283c01c00c080d400500d4040f0b45580091140c0e80210004c070074030f92203141003050000b0f5100c40c4d00010340d0707070580d2101c03800d10701000680440030300035486120081c02e080450181d0b0407540c880900748060320b1001c07403034602403403460740018801c0300826110f00c200300c083d40e000d01c0110741c814429030307100c1c00059640e0303100c5445840e1409884003154010071045036210082214101600c0050441070706540c40342070140d400c1404a4102c80003841102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 566734118 1250 566732868 566732911
    0x16080a0c0915030303020d0204030c062321060d0206040e010e0c13050d05100e100f02131a0f03040305030619050114222702031302150c06090105 64
    0x402c40d902c0040314181d0066490541ea0200c02962140700554951034080c030001c0013140781d02c0c1549009140319280c90116490a144c0b0040f0b0300b1140111004000c03090110b80c601d0480c3caa0280702070030155103083d0036907440d94000b410b94101d07850081e40080d004900800c6265985031143c0c180c8480d01e101840c180c3e150070075110346214652040c3c0d0408180030041000b41004903d0a9074144608282c2d6215200b00030341900301d44214101c200c0365484880003141800c406e1207807400380d202d941c405518010070f0246401112150b0700c1a4040c603114401c00c100100010380c1994040c45010740c40513aa4203203400e00801c19002543e9441c400c14980d8030318500b001c071681e0f41f04c0807100180c42d003c00c80f038a4102d0185941c2c101c100781d003070800314541103410409000111040035220382c4456413514064041108e0f2284603085004561510400502c1103c0c20003903010441d4583c1150701241c0e9614202851025008104100801d8880e2106103d0102010f400080c0718100e441e048010401040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 566735368 1250 566734118 566734121
    0x2031303180b040b0c010b1207051c1106070f080a05070b150904080306040204031a070305010605030915070e03010c1706010c2f060406020c0913020f010e0316080a0c09 74
    0x14482d82006400802003004110880380c0034243d0843c5030000021042c002001246045160b02c08038a41900030307102c1070120b85001c048180750094004803070115500e081e640c61003105401070400b8425140891018104481c20610190075540591902d031280550040901540c1203c0c0003110701d080d800d03000808410741403002a40d0036600501030229030701e03191605a200d41c005010548c116408200210203d9500b0200303042d5502800810301c00d07441c20b441700500f01c807010303000341040100420500140e000c00044444060b9a41d58980019403134541d8180c803d1041225410307015400c100c1d035294a1908a501c049410745410b03904100b503034501004442c400d0507030034000e105a81c02d80c03900d60741c8160071340850007030a00302082200b1350f0042400100582c000d603201e0b000503402100e9070801400c095000b00d4014008070380044c46a0059400114140a503403409410030114060218050f50204a40d50510781410484420240c5840d400c4e51223501d40f04054035020458040000c070000503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 566736618 1250 566735368 566735417
    0x218040b0a0b0d1524140a1211011205180d020d1d0303090603090601090608031303030f030603021002010b090f0609040f060e070f091a060306060d06080102031303 72
    0xa0a40d00d1407050f5595400c1e014030b0040a80b445035681c0c1442d44030b90301c80c4002c0b00005404111064030098a04104403600c0715514000d60300540440310104500c0100c03240180341161700c40111801c8190b0703100100e4141c1c204000e0b913034902d8204024004041900d20700400e0051302d070800d407000000c409201740e9844500401c09400604040d00711814052500d03100d81d1403003c0282a80c1c0380c07424040015100703400c140d84034003403034100000421803000288101c0004064001c080c505081d4120348100d0324181611001e4140214010703100d112030710035484213026560041110001090741d00e0024000d060a4424501480915000c01c402048007110940301f8480108000d0141d0761303580e10200c590040103411200c1c4e0391112800c2c044014280200c0020700000c43c101d004a502d4030304030388113480f4004650351110308001c1c04020305807141d004599024805032040c030758403a011000c403c000d04441d8013a5605510100602c030070800e43c1e004050409010f9644c0041e94800001020001004d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 566737868 1250 566736618 566736641
    0x90a021e04060b0d0e0d11060703110c070902030a060504140103080c15070f09121208062e08060306010e011404020c01051024081f030218040b0a 64
    0x522154091030310000c21949000003800303800400c80740e81c1e855038001260400c2d03107070600294941455003c0c021080120030b20390304061910b0003091007650043c9440c1d00024006008141d11000f02081c07444100f4112425064054200c81206070788a031030700c000350000e60350b90b41c52506000340081d0b203107098007440282e100d5841c040900703646503540780443e541c0301c240307a4020b501078000400001c0028910041c4105840d44640714603a41c1444020007030f10700c580040c2c0001a00c01d18100224245900f50440304080d4101028641c4910380010b103405510204100803040040300c48400c00c0d03094039004031a00703454503581d0f400d4072031401305074a5090034014030318494107010041040c160800b2540d82c2001000e480145000d81854540742550400c40f400d41442018078030030044043c84e940030030b4140003190221080d22084d43d000800c0c41d440a0074841c8414241c007223080085404119550041d940140701e10740040058411060340300d4100c8007542e007074075110f0000d8100241401015841c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 566739118 1250 566737868 566737879
    0xc0e010e0a21170a08240409031803050304080607020d170408120106051209030a0f0507140313080721060207110901060c020f03010e210f160605090a02 67
    0x1420520020b0495004481416141041110340004111900d0011040d001040f226660b11480d004020300414406066900c06603170480e07201a001030401c102e440798030070840f008101010701d402c040f544190101c0806460310500e06001007000301c000003c01c1154441429540320b5a50410142d0700c40501404003c04a4078913083c281d1541c826464050f84030348118102c605100301c006101146d58026040f81011403400900d1030070080001e0481944219000021032400d0704441000b4180d82c4c140000b070f000e1040c0440c0395410001948102e080b0417100303070212038403998103003a00813171a40e4038803070060035001d02c4502050007142d01c01c1940e04a442c2c444c0e495201d40203903507210001d500506080e101d40c2046101000d0036554040128028256940d0702854100d15004126812101401251007a0315100d0401810300c40402c4a0502c074040c02803541003404070081406061241103000c2c038000c440080d00d0b8203800b40034a48860464003a250400039503840c041f80300d030340b440e002c840a50300c0fa = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 566740368 1250 566739118 566739139
    0x406090e060108182406180c0a11010906090c0512030309030a140702310e251d04060606111c02010209210c01050307080a02070f02060d0c0e010e 64
    0x908130058200307200b0f00b0071400c449a1020180e07001006100c4072a0745402500c40074144052840d040b0026215000d460352050b50038204903200070b0662044102c082c0a000b1401c0245040450a43c005110030b41c10900501c28100140382103041c081c030390f019191040004805042481c10000103591081c1d502c00b000798501030707601d18181d0b6100030740c2c4442506001c08001c0000141c0765010100c030301d0080c140800300c00700c01c40c801d00c036000519884030b2054680350a041e9a004600064107028103c6002c6403950510702081da440e0000420303402c080c0081c058207045403004a0401d591a2007035018040400070319032103400c201d850a46100700d03141182c0c0110406000010110f038580c440c080603000041c40c050070b5401080f000c41c0050380f6094150610100244010350500903015194401d203441c81c03440c501010040c0201c84041d10707084240368045814020400005000e44449800070090764441542c02c581b4006441e016008500040301e242c8600c86a50040c00e40000400c0000c2440f880b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 566741618 1250 566740368 566740381
    0x4051e07020a0b0f131a070f030c08010b0904020c0d020a0302060a05131713120501060b070804030b06030a08032811120405120426030310120309090c050406090e060108 74
    0x144101801d041c0c0c5e0b003c040703110440042d000c900c1c028036101c41566003003280d03e00f19101403c002007001c41882410308042299034100e43c404101c84c1075406031180705444030180f0004c00c00038020031806040c184681c25403660555000195040210300c69401c81d20380c0da8480f41000d0546da0142e6140b18240008004100020101d4081c0804d0402991605041649020302c10b80421401d6000014010149160101f030201c04e01451000d4124410030600e010a19130b0344034100d104500c006003412101c140840d4060380d00f8084402c030290403651043d1030307080c003090484040415048440c00920140c030034242c074491030300580c03a41d80c00344080c45050503040c80c1d0b034030410180100200d40600601000400780043d800c054405014401a41e003c015070340840101808121080e00105030310500420488026807500002641c2d11040104101c181515064801991036040301c41c00794180038010307250395441000380c0100c422a40c1c480c81d050f40e80c4c9042d0030401000f5a0400d00042035900080c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 566742868 1250 566741618 566741641
    0x905181219141602120304140108090609060c130504020304031d0f15090a09050408092704030509031915181709010c0f050607090e16081504051e07020a0b 68
    0x4580054420aa19414603042d941035030f04c507410234150a2085018882c503541c0c48642d00e540951010000d02250401d040060707681c0c0002000b051440700c000802607003000d08080100d0040c1000b0700705540724205464080c0800c0707040c4d4031211030000e0568170605549030410b240d841c2e4000c040c10810007040d442c45004041d9000b81c00058001c02202000110341c0781610400784640e004182c2103440f40c803014200160302030480f4403a80250301010310006036040b00342a054000b42e041c00c000340e84102c0680400e00f0030035141c2c2c001001026080001050100e81c03070070700001207601b6008001416920080d8140c495502d10007070803911048009003961102c2c00c0051100c01c074141000401031802e41e03110340d003403028428100d034a40c101d1b0327045c80340e1f081c0c03c200100c01502811017540e44503d000300145c4100d10340d90b0794203820030031401c000c51216074002030b850541d00c00103071041c01f0791304e061880c1e164088a4200c04030708001c0c0900000f9401c5d840410582c8805d41d020b07650203101d490781101c850 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 566744118 1250 566742868 566742907
    0x302060d15170f0304060921050d0c0201030b060c0a02040f090206030a091209150f1e0203130e0106050d0504031205190b1504090518121914 62
    0x800e9480381007655000c1084588070080484420720b050780d008400102d030a040740b0b000e40d1240e59209010a110707003a040401c041c00c2e0740324110504d56444400203810680251017101925a000f08003091941e15449501d45842d50f0003a01e007440810009410300456101d80039000242c0e401815202c130041c40c294002c3e4160388605400469040343c0350300060000e030300640349a1012641d504c101c80c10045002c00c48120420b543c2001320401d0300c0c024101e04a0081415080c0420424600301d040f614020751030040480717081c0407446e4581c480074101030b5880d800700d4090700c0c04208003d4001050900c6906040c1a5103050b59071904120716100c4041c05000d01800c03c400b4040401c03908041c0c10703090b00c00c10307115106070141c0d00320740e44c0d05aa120045904298203240240700305c542200843c003010003140d084900da490000741da50755078017019481e44209180c4000f14001c01d603100040075107000103400c04556404070480750045858060b2400c004c064001504803a00340300340391444141d403c818 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 566745368 1250 566744118 566744137
    0x519030e0c04060b030711010b09070513030b01080706021606020d120e010c030204051009052805060c0a17130b0a0509190815060f1012020a030c2601030206 69
    0x540c40d0703020200000d4290381140d088035842c200040708026a09521900e40200c540c8608000c01c260000800811400503008142005010001800b0000300d0301c0e19000800858210302821619615110400d1320b8040750300c66140144580d803080000c0800c18802107003110401d800805071108ea214003aa50507080e018003031110356880c415001c0070f10080c06018451040703664016519801d0004100030ba5850325451001c002c200308080c0040c3e140c90071156040085190700032950344559002c0c18405046810030f039045100482c000780c031550300052204080f0300c51002460810bc4418a5400034098140d1816091901d40c0742003100c0201e1030000c1c01e643e000381c50030510f44981c681c00314100b43e124009800003017203450010080321758280581c081c000320108130046103051000015000300c514040540c030440c10600d0100030280505285031520403d90820754032002d207540050000c3c08041d40c48030119022010303000300782000c500c112003060700700031840080364255000c1c05020f070001041c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 566746618 1250 566745368 566745373
    0x1e1509030c04181e0803011e090b0907080615070f21083d0609081b040c03020c06040606030507120b16030b0604030f051006030b0a0207030509040c0e030d0519030e 72
    0x44d1004940d11800a5001c0c204214520040c0b09100e82210a039502c2c0f80d01c05c02c06a880d0112a801c25640d1860094001619141c0366280d40c1760040026100d001c81004450302110018006080050710802e4010250081103040ca021600007d106031601d2001015400140e00c0c60014030361148200004030a51182e0030390440450884500c0301080b01c80c500f26000f100d81404081104580c003965640152030710320098041c01c0c1000da07011042c2a840e000c40d62182c0c0e01d5505a00c15984694140d90941a00b50100e603410304190900c07900611950205440600030400702045100008150450b2581d0046140000b07554000c036845061424035000c030700301502c40390360b00516903400780944061400f41ca50741050200e0f0b803405501e00b41e020020541e00301d0410004100ac00c0c55044e0440d4030804051025075140302c81d01e4111400c0c4102110b50742d0052501061146142e0310655118003000103904132656800c100d036003900c642c0a144469401c010001c1400444684a90071512100401004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 566747868 1250 566746618 566746673
    0xf0603070314150411030105070f051602060c0d1107080a0b070c0606030b090f100c0e091914150108040b01091104090e060906100b07021e1509030c0418 67
    0x3c8203081040291010f40707148107100100b0703006140c01c0c828a500b160702802d2004101501503406440780c0076000c4100044601034410300107545490f8221005a907050082e2080a40902409410440300e134004034150321802001203034240000030603000c2e494111070300c1d9940b50b4074079808031400c0f00c4000d42115460784514002001500c1c4c130304101c2c007484040d000381044c00d101c8001e00e4a4006282c141212803401c0000c101103036a0420300c220f041510582c1c2109080d512503846490284403000301d03400e060714040b01c02600c1c210421100d40520420010050450800340044501203000d41d0064481c4040800400640c0110742c0f240c000000c0d00461341f400c1540d5880504221081006034044235040441000300c1c0604c04d0251503405500c1040402c04503003809440c80791802041d0b0000c0c021102e01c003101111011407000307071110341d00040c01c21480450506014002da0004800c050080c410f0400100d8149400c0c00396100000a403220001501d100d0303210600369080522a007100d5111030032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 566749118 1250 566747868 566747893
    0x90f0607050c120d030b030106030804050108041b031a0f060114310f0807080703152c0d09030b13030318030206040c060908030909090106050a030308010e0f0603070314 74
    0x2000a22001e290901916042c01c1100d00074061b9100f0768801c2d84a41d01d0b020050001600c408140e4064490030310b02400f0903a50743c80e0014451a1240000d10b0b219982100001007081020529119900300c440c013102c80d880d5000c00700c604903000c1da034190200381c0812031123802c0c61140703010346010042d01c43e281c05c0707201004c10802a1054080380c1140c01500e150400e02207108408036401c0200f90980050240d90300d00408a0746451090000400080e046198075030581c041e0b800c26459441440b801101d0740750302c0001a0340b00c1c50354006405403805110091003155000d014250110707a0003c0c010960750b990410114118146804d049040c155100c3d80342d00a40c035180b0801c505c00f8440d400800c0c031410181020000c00500340d100400700110110180076800f00441038a2200030107694410b1a83c903401d11860140003150405034006500800010034154000103c0b412106d408841c0da020341c9588040e1840140c04440107905640070080420020300044c40c00004080d9180c00e8035590740804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 566750368 1250 566749118 566749129
    0x90816090c030b030a060b060d0c0305180304030f030507050705060d0903090803091e04090c0f0f0b0708070f050708100b0a0f032109050a062c0108130314040906030c0b090f0607050c 80
    0x5402c4100000c2e52482044038800e41c41098dc5200c4407039400071401c0520b1070b5500c400c5155034813002420480c000c40c184d01001001c20505001c1d0000030030036611400050090b0b002400304400903000501d4036400010703501008400c840340c1440c003502e1151182034095140c0103158210b44680e8000c0e0382e41002c4804a9142c81e00f8201030614012448480d0346003030030481e1110007682142038103590810484d0001a4100d00b110042e5034003154070204520a404c001c1e04044841d03010145d24002d50182710780f0340803903078031071395180400310b075500306c460b40340c0c034000644c050517010003410a10301e00c0c0d5400820604848021001255103828407990f62200089068000c080e8083e00100324500d480c81c1c0d11080900c0030f00500f22040418440c403200150008114503401340ca024034030103040340700d00241403080c103120500d4900d00001a0750713555540c110a0003407010f803100f034035210f1030f44c00c0110f40418141d084458201009282e0560030140f00108811644058821603d610a50503009065100e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 566751618 1250 566750368 566750381
    0x4050a0516031d0d11060705090a050f0409020301050a02031b09090a2a0207030309050909060a020d0207050f0604050c0603010b031512160e160c1101090816090c030b030a060b060d 79
    0x2165100440e17141040ca116140040240008003070000900420f03040e504e6115960080310380c100c0380038241c0b42a02002c140200030080002c1c2d050b500700307010440d2540d62900114010600d50201c82c0e4010170751120701c80b290203a00c100c0c0b54000919408030300010500d41003003002002104006200040113820065242e09280000c030150b0080c220400030316400098079002440c01792454185464014981a1034420041141003103a03400700c0e0035443e44410342c0c1a145c2c9154020229580c082111100e295100021501141d00344601c04140e01d203428642d007900d048402c84c40d00d1904548414804900d00d140c481e2805411002d9440304000300c0c0307810400d03082e00081e44e1149420890130500b056507113010040c401300b000d041a848010003507920000400d007007608001d00d1203000da080c1004a07035090070b940c040c0e00c1c20710611410000300c3c9824104041118403030381d010405c11841c0202036041c0d400300190140d05810a0600b2404038041d900021018900101813905e0000c0f0000b410044030817 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 566752868 1250 566751618 566751643
    0x7080f103603140f070204050703110d050a06060c0803132906131a010c08070f140c01020a03170604060b0d0b030708062e0305030304060b04050a0516031d 68
    0x46190000d007415041a0943d4038101242d182d0b034542646510307200750070b12400a000380115a5480000d0006200ba80702401d20781019000564a00344d84420704040d020980b1044d6441e45000e400041c142c1c02103c035190025030043c040ea00395078030800e1100c0c0c0f80280c84425074491002c00e4417042c10140c07000ca045040304020b12900c01500304401070003000a601003000506501d48400d611a400d030ba2044840710405c00d02e052a6030401510b0320050368000c0100040140c1c10942c150300c10403405060704441d20b000c5800300c0d00281c400340012030743c0e64110302010b800315407040d6034928001011040705034040405440458410341d911441c0c20a81e101c0004194199a01c09079107400745414850400100f024800520050a100b0000c500d44000f121854440c1406040c64086145600290000841d04030301601d0b12172074281081e40282a18080c8e1520540c80d0000140c524040752080c20b000740b40c2801035041c8174162010640c020180b611420012015900c8000d503800300c1004180700c00c26 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 566754118 1250 566752868 566752961
    0x50a06081b040509130b18061b0d0c0201270c0302040b03030c10240f090b0d050f0c010e09040309090b030709182303070609080d0f060807080f10 64
    0x2076060820010b45c91b000b5203940900342d0b041c104c0b09518000011066000140c01a08800010381c580b04500d192088580d00c90f20941800c040a4406406601c03800051010030360781201d0001680b154100c403210301a008080d85c491a409001500b081d034032105100c00d011741203d2410008529941c5030040c10000d4403410b070f856504202c6044443c00e00c0c0d5158510111030324406074200180130072000e00600400c0e140f9903031103040c4001a920309101052064010081e95500c43d800c10f51652036184503a01280070030009441107602e8107220000b24030940d01941d5a41c0403900f001c001c00c02828140c0d40740c80d8076218129010441c0c400b540f0038000508034205403518054410325141f15290700384003010300360045000301001c24060101c1218041540031000052a82203440e200045004002400107018500507080c1c0fa885007690200c029a003584080b6080d0941d6010705540c0c1d000c1e2083e1700000d03034100110b101040f009940010304104442a904d0b42000d0000000c0d42c400c1803051640f00850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 566755368 1250 566754118 566754151
    0x3080d0f0f0902210312060f0d06050f07050403020f0f040f020a02030304021503070206130204020d06080c0f06030108070b0313050a0f030e0a1518050306190501050a06081b040509 79
    0x149070848804204685035400c1301541e9920702c0000303032203010701d902c002003005089000071303c9030b80c907081c0c02c0f941601c2c01400c2c00076904090070120014881180c441800503001d001141c880c0c0e000d0b00586048a40c01000a80c44a400c00300744403810400c40c290030b8010340c441d0b81c02c1722a02c4013030012786000c460590056480b8a0107004200c21300d0717111400c03440420002c10900030703001d40c08903445600928030382074480300c1c000350704c013140007071040d0846407140b1840c1c164040342c50b500118035118485000c481d001c4107414883c0030444588400c1c440c100f92030b1b1104500b04002c0b640800a950701807040c200f0b42c02850041c0e110780d41030802c0200200c070302030f034035150040c00c15400c0350404003130000649041c2d50450601600d889000b80718060382c0c05104c811a0610360340c00030b0080007005400040c06584513402d00d80b01030b0b0755442014500c544000c1c00d20300041075506064040303e0440c0c440766182002516003001d544010003141000c42d050040803c00813510762140e840950060110300142e0310754 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 566756618 1250 566755368 566755373
    0x90301050c0c070b07080c100e0c04050c09220608070303120e0c09190e030316020f0c0402090a150c33020c0f070b030f06150403080d0f0f09 62
    0x2100e100404840a218050141071120000060300c03000781c5040602281d038031202410320507030074015041d00c14403d128200000d00c0c84800c617045113040b01510320850348041c0f036101c06c02c016900b0455640d41d8801c4140300c2d040403840c14102c14605803016012a1980302201030000040d1803050b0401705296000044c00c00030103a010817040c110075404031080040550202d5180d0301c54042d1207500348039085503004626a0702c10344900b182c0e03d0000e00300421124403006805a16600200c032900c004418103905100b40a00100d502d45564851a010300301c2100034404010003504140d40341c0d0307040028040701007900701080700c07800b02418964884001040081ca0159404454540707000a030101700d10f003a910710094034051030450800c003007002d1388441c280c8c03078004d240080c6071904110341e02c01d02c8800141d01c98900700841c0956a0a00b40040f1582d859060202e00680c1605180000c4c00c100300c2040070400020141c41d20041c99800440d07010290680002500ca19215554102c0c0d940e00710b0404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 566757868 1250 566756618 566756621
    0x11010908030a0f030b010e18010e07030c410c0d05160b09030d020403081209060603030703081509070f030c0212070b04060905030f070b0c030c0a050d0e070902090301 73
    0xe12a0300c0c01146042c0c01d020300140f050918904082c241522007464482d1030780100004904c00c2c80181c40c1003160140394403a1412800c0a1103005060000c52000c2040c1310700c64022141040165240c240f040340e00d05d00840b2103076115a05103107011001010241c2d0b942c0200f035100010b11024940641c84501c0c402c0f2090409845081c188144101002501070103413503885044110b581185a03041e0650780c00141a0540c419858618030b1a480024084100304410003d404c0040490000395581c0c1e0329210116519441620702d150305610502410000030f03c50f250403a4401c0d40e60000e076040101d03150102d0441c54082c1c2d4400c0100300f40d0f814000c6090741c10b10449901451910003402001e151a200340f10900c0340310380281c030044e0b40c400010140052500038400700c0743e2100880c0c1c0d40d002c3d041100700aa40000804981030000f041c0410140305501c003d4a000305c8040603443d20f044a45401a181a0f00407075211402e5910303002c414502d100d09000e13850052841c0740015230b039418254100750 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 566759118 1250 566757868 566757887
    0x906040b06300a0b0106120f09051f02040807060e01030f0605010801050d02240909010f0503280b0906190509033405070e010e0603060a0b010905030a1101 68
    0x3405403034200302c00d005641c001d16211400703001c904802d440d400d0380303254a00c0c180200f850010345580302c1e04000051084d03100d50200c040081d03030302c0208001c02c070241a041c1074501d40c0c000580154028803925500d83d00b8100302c41070140481e080141b50035610007070a41130103c15485000403581812030360b240b95800d40904d102c10108810104109401e000000e009020107000c2e8500032544000110115104c60f4091030b01600036540403c04003114000381000c81c0d201c5c0c0c090a004070170360000003410828034142641030390701c014060401e060a01c0209034003202d003540f0b0080542d8442000d00049109800994001d180c071401030540c5192030540c40440003004000c45c1c011518080401c20741250100039110215050349404c7c100d2002c0113903d0b1840300c1c10510807840c0c4c500d0a0098420028002003c0d01214010f100103040d07681d0310040c8101440d41120201d81503000300c03000440d0401544e100b100440f005050a103a01303911400481d02e89411000200c40071140456450172640c0c000c510302 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 566760368 1250 566759118 566759131
    0x106140913021f1701120215070f0f060209040e0c0928050703150924060c0605180111120c030c0f0309100f15090614060c0f060906040b 60
    0x300a040b68042410b0000b08844180c2d444200300d46992424404e120201c50303003004520492155031202c8440050190702c0703000324801c1403100d48143c91503a884003601d1400c0c0e0801c00d20250301040d0780f15001c4010352a102200c0150f801c000e0503038669518480c69a080741c080b8001c10340e42000405010351180041c0081b48040444401c0716005000003143c00700c2e001c1141c00c0411151502d95042c1e007d007441090b2a0003d001a00020810480c0740d130111040d0300d04c10483c090519110310300c52401d0a00b0b400340030001142c4212032004a003047c0c00036a0000070100b005084920480702080c210307400801c2201c1c0b040c900040703190b1108840c46000e900701494207906403950600c070362103006a1240d0011300c0c151a81c0400091104541400725090703109c140407091029080c50b80b44d9200074102c80035007546d200d000040c04605800d03184207040a440500000342950f0068030100903da03000101c115030340d8414413095210f400342c1171040c18003072000800180388508082c0b41c014009203004100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 566761618 1250 566760368 566760391
    0x90510180818040b0604290c0613060f02030f06060702030718060305060903030c160f120f2d0e13020706021c02030903040e0c0922060603090b070f09030501061409 72
    0x14007004100308650005240510b46440b60901c5500c0020414013400300003102278020082004405800e03a102c0c2e0440c83d224417020001c032201c0004a40880c00180c0d801e222140c0c200000849608143c0010041c0e94001001c44103403564900c1d40b1601074400308480c1400c030382c4804040040000801000d50420310360006181185480c840b80c0199009840484600d0056001c000003400350321143d92030b005030442c9595642c0340880b40f01030002c0d008151040b00207100404180070f402e2076440404809042803464038213042005c5001c451900f1445201ca602070000d038100e400403c642d10041450b2442243c0158441141c10350044c0800c1c0800548520180100104205000003004032819200000b02ea4100c0f919000e0502d040350183d82c0140c0c0c4c20000881144036441d10131405000840d0780341400b4400e15072035800c114143c4c0c41480e801841a4641000b103a5001d010b194030030050841403500101f200d5aa031961400d6403030725400305003c0007014807407030b40174242054601d40c001c0f030f034000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 566762868 1250 566761618 566761627
    0x100501061e09030809090606040b0d05061806030d050c0316064d040b070c05031608031c1506170c09180a022218090510180818040b06 59
    0x12813544902c904004144650f0400c000144240d40d204140d030003410101c51115150004a42d0100c01880300391002d40c8a283c0181d5800742800005070418840d22000c0c028101029403c8420384164115a044a00c03600007072059808000084681092960180c00301150350442c2002c0b00e818480c480034090000754550780302c652000000c565900034440012409101d0800d035603040c2030f4600403500001a8a040003131303042c040c000840300800c280c400450a507810282d081340c1e071244420682c464015035820038828100e002d24503410020740d104102c080860785031401e407241c0d54000a16001000850b5403e0200b00000b101c0b003200703692250100e0900c03481c0009060004842c5039070806c1034008103561000060b030303c2031150140d409850201030440d41c00c400c0b1000b4091451100e0041d030399108803a60b4030040668203409103900c1c0b5500b24002d401c40440d00158107024000c15a030300076946141000380c8001651003801007886003c4500309c518203252090070001600c00c80409070303114010901 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 566764118 1250 566762868 566762873
    0x15090102031b09010302040f03061b051602011d0d14011104030c03020906043b0303150108090309150a0e012c010c020910060f1b0308040203100501061e0903 69
    0x410b07401403940d540700c0302d40f28030311840120040d00c116004800310002009001040140941000305a60341c08444801250701490b000c40340b502400d5070318180c1000400c505c1c009940903022140002e5510003040000f1740c2c644010403905290076504903030400c208460154020800e124207103c040803500d83c280b83c686152600405010507001c06480340e105000418110b5480fa402401d03004028082c0381c450b909580d121090b058103130b0900703204803041c2c030b0740201000401000700c03071003403404207034941013181c10340011101240001d00204140c4803c01004015540c2c40d00c401d140d81c40290480e41c0c0d03841c8008801440c0d910498461414004c0e01c0c041035110540c5005404062120706402c040185190310040310141c0076000c01a40000f00a000e2101c181000fa0b0340b00143c40b0541c40c0c920603a12904400c40303942d10312007120070300d6030511401c51000030701c40ea8146130002d000408a86180840648a4044a2081c1c2c496408140629004413100419904040801c20700e0300b00180c0c00ca1564 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 566765368 1250 566764118 566764141
    0x6060405060309010f09031d0307051302031b030901020d18030c030f021018030801121e03050c0d0207050a05030102120a180519060b1005120901020415021509010203 73
    0x340211445100e0200000711034001c00d40c0100c082c0445407505208030029420083c100420480c004d10450070441d030105d1103802d0000b092401c40b03101a1143c046500c1e54540ca00094101074150341420011510070100d0450050141d402000350030001030351004c000c03c840c1d084405c80307101070b1601c01c541002100426004030f44c2200700b540504190101e111942000c90502c0030000c024a003052918008006981d012100307448054070940300d20b1300340d98031440b030300940005044000f000316404d03c1144c2c20010100e41007005191082c1011400c2000030b8585504211000c603400c8016481464200814034010300500000c1401380c0c021840c00d00783c2d44140490080040110702115160800c2040480010000e40d0555070444103807151a59540b001d0f040340320540c01c09480316410003149211911300b00360b20202c052071944030680352808404145904440042c200c800c595420310002803014201320f8120b4801d1465405041c002d910a810344c0150900079210702c00c1303a8414420400c001d500d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 566766618 1250 566765368 566765377
    0x3021809091b0a05061303060608122b090b07080f16031109030102040617011e0302040c090308030702030c240c16050304150e0f01080c0702190608041a0606 69
    0x200e031800c0d090b000203540400d070502500d0b80a01d402c080300003010304102401c0a41041940d1103181c05009a0b55600706080d550b0f400540c90707104c0d0b410f00300100404045950b442c52408400d000000302d9040d00c4148020480d0515481a20114250010000520350103111180c0c4038401c85640d6605080c111541203280710401071607014036548140d03200040b100603054841c4418010000d5503104c0d02c8a10040c800e1007141c600142304080c00700007080e4440d80c01041161342e8684952003000030f1440e000c1101401034069501c050080120022003c00c01c0300000310b20440f01d9070011542c4140605a00b0310b4581d080590f4270300301340b0000c08490881841b60803142c00c8841e061b4035640f1035030044814040544407050083c0b45200018000130b0b10392101b41100040d2825483d140c0720815110305000c200f0f080451094001162040000e0703054001034083c1c4816030002e0213042030103041c0b40303c00703075200855041680071480c0300c1c081100300001341071000c0c0030502511011680303080090101d0802d004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 566767868 1250 566766618 566766643
    0xc07090f3e0a0306051309020114070b0f0612070303110c06090a0b030705120112020f120601050103021c15090506190605030403120903080f010618150c0f030302180909 74
    0x140001c14402ca244030340c2020019200080c11940010144808039004202900c02203010482e103450182c00703424000252180c981d0412041c1d00d00d13a42e0f071003030000300c490b00801095101c02540c0001c80010410407001000d58803a488403e060029400d920303203080300c04c4469511502c020000071540703841d0100039400b2038111981e95901c0ba16590004c0c0e403070f4050556441c0030300b0400320001850b2a2455644505103009450301000d08544006004c91003020752004829607126500402c5503501c00d6000f8000f55070b1110030710400548108078070303007941e030403c00c3c0b101c2c1c5804583d414020700750203108103a04220100c541403c00315408004840b00310262155400f0b20001000003400d140c0180360000309200e00d104100a8140c29103000b61448500b90b45c01c00300700c90304200205090f8000c4010106e0941c07640d00355915140303400d0101011451145100041201d21702203200011a01c0c0340c0041220b100e500e0268480e80402c05130140014801c5e460b51041c02514280305842c4000f017511a640c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 566769118 1250 566767868 566767991
    0x90b10050123090603040606030213020a0519230d0e072d0f080a23071206090c0807061101060501051804110a1d030715050c07090f 58
    0x900d2200d900360140200b082c0343c4e4109070000700300001c215056110703500b524400c4030314420110094901104034050000403070049001005400c3c045240d076004a9941c0c010317841c0512083e00142e0704040f00811108083e5402440498a08a580400e020302c401c200340b12401021501c3c904000e0a208040d5240182010301260f842d85031040341d4491008054010300d100e10703600e01c1d03943e085190b41e203005540070707181c400c0b01841a50035484551101058014100014401103080584486000e03210003011940e03154bd49155100007840d41030701d00010050100a0070318a850818048d1220810b4580c007102c0d079241240502560317030403a003610030000030321140103c6c030000000410000c140f8402e10b241d011002040c20100c042c0d00100300b000c03c0700f03902c5001da00c50264409155440c0d600340514141081521078405007244168080d1001c03800d0803046445aa598821060460303201c40030080c07500781c66400400c0140f050024008140954001c0010a400e000b0307400b45000303e01c403a07100b5052 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 566770368 1250 566769118 566769167
    0x6081e07080303042f0a0308030603061e1504180605040b010909031409040905061f0f030b06010309150e030301030c17120c010608060c250f020907170901090b100501 73
    0x6040280517051100c9000d4a082040740d01c0c1d003002c1c05590400c485403842031059800080520000c401001c011b1840c0500d40302c001c0c0c842d00a400c0c0c0520382d0152107500140d50385143c1c410900c904000c421281d024030400141401c160404282c0034405030030112416041c00b56240000340d00950520074020f409041d20746800c2c0100028001d4401d6440180140c450101400501259a4916825500c0010032011041d03583c89a4401d41c0710107201c041e0144981c940059903950207a0420040c1900c0741c2d03041e10446071000b104138102c0742045a07210895201000500403c0a0702c02030402800c8500b051054515000401550351140c49202400480000c505810f84200941203040600641b40960760344d0702d042c0a0001c5d9a8000390075201100c070b9101081c41411040c040420740a6810800141460f02c864003480b007804005010807040100c0c603403050100d80b0761086030b5405400341c2c1d1b0000c00d1581141c1000404504054000d4030001d520300d00403c0680e03005102c4608585003070303101a040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 566771618 1250 566770368 566770433
    0x30d14190e0d21020c01050d05100b0706290d231506040f020306010c06050606280e2b1403040308120c03040c0e0a06081e0708030304 59
    0x980c040e501d442504006000058010407030741d039940d03206100d407440500040001c5000100d0380c0f4490805000d001c50420000784805483c0307038000320340c401d40e400808101e0700d5490906101070b5002440690302c1c1e2f6035031801c60600c0002051991a10283c03088041041c446802c002420b40c031003551b0051021111100d41000c03030014a804072806406030068510251394911040701c44c030011680c00d48202d1920030f10001e00301c031034030940340210301c180e40f44010307100256502c1e8014200034007103a0780030f1820710a03482c0c0c0c3e1080b400c544400304000442100c040400c2c00c0c020f0040c804410980d48180041e15201c3d1040f015200c4100706001040842d6a00128a0034403048151540fa0b4101e1a8000010040140080e4000411500100040ba82465914000302c10320b0341c0400e40e002004484900c4080140c0300041900540203c0020030000d07641d95030768040c618049031300c044024155018032501c0b5000f181407054400900440d4007840c958505a51480c2118151441c545003403402e86400e20300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 566772868 1250 566771618 566771627
    0x31017010e0f0c0a0b040b040528060e0103150b2b05161101050910020703050d0f0506100302040b09010c0c0f09140105040b0f0108220b0402030d1419 66
    0x44000c050142c44815401920942e29140c03c0d18801307002c1d1054440014840c45850111000c0355a200c0200d41458200010448464007a81c902400040325492104d04807940307420b0400141505e03110084803500c0b2100140a49801d84c0e0020360021000394108042c00e01c1004980301c10f1714003035540188176043c0b26581030300e08e4020b0240082c00d280000300082008103407040500080b207500c2e160254075400364010b080c0c8600310307038082d500e030884c1700b002c0c020002d1500a0b0500c00d209082260400d48000d016504990340e8a003d0030b016604c40003400071508201c140030311a440245401e501c2d05060800c0790100c1c2c0700c1d140d042410020b440b1341c3d081c14410040b02034809806103072071040046039109102c2018056540c041d182d00900e2400000d450701d054461414054809494641481c200c240151207010b4018042400581b0f031111b0004402e2000d5802c040b0144646c610340460304090040c94070b842c10403c1544140a20400191a07696081080d00c068464a41c0c0d544102c103086001280c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 566774118 1250 566772868 566772881
    0xb04020409020f0915070507060509010c150b010f1106010b0c120c0c090a0c08060411040801060602030714070608220807052103010501120b040204050324010b03101701 74
    0xa0301c1500c0412400c1e200488800141002001200d800160440d6040c00c0040b034426044010100da02071030302045a1401480604180b041c141000c00041070039031034600030300e85014501d18015503602000300140da00082c0c03803d225a59894001001a41d40407125034840060040034201c81002c6081903010800304130b10072190f01d1403040191584d600b0444107940c0c0b09128a4540300d41e0084000910f07075512031280b0022403c40750781b541c03143e45606090000400c4051040c126100b010800458100d10900420380286459801941d442016040030111100c07400c101020f5500301d48420003460340d000d040a03030024103904801e1030010098405814040c80240c00070820000880c642d8140140441c14905010003c3d0031401c512403003440e5040d60b48024012540490860b00c241074044c2070b241d225402c4000e018000500d825168000a403428200020645008003080c070f110364042d00c6902c5803070040142c5050a42075003402c210080d59011540207030034401a02c0640b210403001c0941181 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 566775368 1250 566774118 566774129
    0x80402031212071205060d030309030c0212160f050a0b0a03061d061e1e0111120a0f020d0915021f0506181e061302030901020d0608150103060b040204 66
    0x860750380d01c07540510b441014048070340e03d0200d640c0c107980e2160a0340e039008251183c40c000306074000e001c0300e80d81e05800401410030160108038031000580016168042015010340c1404000c00c01c0488990344a0245c01094110090407144400100318070307104c0442c404184c030000038040d0745a1842c071404400400061348043c0800c8901ca04c1200c3d0007960340030941c0944400c0d92410741c00114007a000d14100d4070980e00540200045e40310390b03016218407a5400034840e05141c8208110102100946001c0d003500340a08a0900054190b0030103804c003002450a4405001605004468200181c8030455a205041c08030700e04030140d206062090010f4903070b141c90410500e032403d00c2c8042c1c80d0010002101d445020301044c4900340c1002a0481a40f0705c259000ca2000941038803080b2070012005010300801e800001e00340b0007207440c2e00240055440b8104680005840d150555491011b903801c6610481803900702001c25925911012001c0d8107503504590040303003039400b50000c10024400e0780d101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 566776618 1250 566775368 566775403
    0x21150d1e0f050d030615020f0d1206050306010803030603060f0f06150415030e070603092a0b0c032203030507030e060c010228140301090f02070b09061803040b0a08040203 75
    0x84600d83e03905940728409840c40801c1220f42115401000da985410504c0d1640403a03014000f2248114800c2c0800400d01d1038005001c41c2c0740e42c0c1c8001007031a004c0282c0100030a90408410865182000c2002c0d0f0f50140345aa010000e0307003401080f01c41c01c0d0f180642014010508010030040762182c43c001c9030002c0404810b00c00c24a04c89140c020001c00840f078038440280225a000104c0754440e004008100d40c0000401418905081d1081003107c200013030580c4541e1106400540000400301070001100c0131000b85954a0300c0d011024480d030b64001154458880088050010035409400d4034000380d418141409003984500000b006400340c1c03003002130250b00010b10050340032190384208038001818a00d45070504020034083c7c940310003084002210301000e000400918840d500450a0001d00610040c940015a1101203400340d007207400c001250f20601c280300305540000804103c1d4100b80c13014500703141c10012040c0786445002c2d031a004101c1c083c400300702076550500000d00b00f03082d80940c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 566777868 1250 566776618 566776633
    0x1008040812480903070803040b03090c010504230d05101d01111204150612150c0e220504140601120b041721150d1e0f05 53
    0x403100341c0001c21154079900c080c2a102d207006000c580b14001e1480c0502c0d080d8a19480101c15222103800200c00c056140c417070900001540034052005001500401c040c46130369191034400709207440c00070b40c0d5450421808100800030440d0180b241190617003800545032801020400003580c021000c4400b4200d40213506035201d044006500c00e010f0003200303a075001107900c9004010b2742214070a0700788040c100b01c03c1014240c0040c4000200754070510440203000c520400b28624002c0b12a00c0d0071442403840b64540e00380500602005804d0a10301c1d401050000c2e0145440080c10b0b420105005800b40e1031510340a4181c120380c8a5503005454040300400c814a414101180009210180c203a03050003024004100340000526480b201c6070400f4809030380340c5440c0d54a03880920b0344801141e4904c018080e07042c0140d40c826008243c59507528012210382808075200881040b06020b0b984642040268000041c40b451a110068600304031000190580f40c18118003503400188014200c3c000c400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 566779118 1250 566777868 566777881
    0x1a090109080616050c0f1507030c3f020a0e0a0801180206131e1505030f0c250609050c121032041a070e0d021207030503030609151008040812 62
    0x100ca0748c401d42c0b0b290b80611208082034400d89820350580d070401c07065580e22424240d0140410509c200c8000400c900c10002c0c03004070340003422030b040203003441d0000d01259112422490a18044c0c009000d400008028100080d000041c1d000c00303002000f8040c031780103d900384c0c003c100b0901060007094000e00f2032901c0b07182c080c1565541c9400340074501d0455016032115080074444c2066a201e0082035420702100d465003803400c0ca05d50040946100e07813291460701c03503020800784d5400801d21f5201c1c4102180c0d424440c50203500302160503103240e000c0e1000d0782c55072604080001d42442010010040011140c06845203030329842502581540b007801c1c000c48640c1c07402400b44109204a006002c3c91030042d0348103480f416011010384035203002030050501c0d0ba1a5190418608842030703c000c2c0000c2030208424049802c1500c203510a44250300b0210800c4210700740480c050b03a01514201c0d02840c502121000124003d011001510402400341c0000b410800c0ca80c040314503503114006240827924124 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 566780368 1250 566779118 566779153
    0xd0611181008010803030c0c0c060c0f0d03020f07110a0509011806080c181f06031e1401180207060603150b0307081c0302041a090109080616050c0f 65
    0x54080d2405050504046000305104030030050595140002a61640d1505403880742c0c1c64200c2000102c2c54061071075500010b030f42c0e22004044500c0070401400316400b0342084a810014581d810700d090500400107074151058400480d903618ce40154590304410117480400c0030003807640c00240d000f042c02c800126044054525400e03040c0b02503441400010341f102400c54a80c0c00d1a4007040d082150022050251003e40e000194009807a0750905040d54250425000300011030707203d4404203981d0304001144e0b0315420307403201600d03081c2c034018403010940311701c080610300741403103a9074800c41000700340c4861888a0b0100c814883e00080306010064a9003080710800710714801070030060f0b282c50718159541c1000b00d05441158107200c00f901201c00344c08400300402004190100405500b0030000c514040b28290700900d1500d41007001e92180d803250005018000320b5082804141d12000810020a00328442120004114a0110380b91a0440103003841d00d4039400035580d5034020b828000b01c100c07984 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 566781618 1250 566780368 566780407
    0x30910020309030f0c3f0a0b0403230906030f060a120b010e011e0303051c0905010605032b0e060d0504050a030311070c0b0f041d0f0a0b0607020d0611 66
    0x2201d0743c91328600b43c0445420024041c00203990b055155070b0300c5080e041e00c1c0c01130084006d440d00c803e540180304180c1c1c50070300ca07030021101140410703000454607c400c9501c1d91f00d0018511810b84061422940c2c5002411900005000540c480074140018000f038036014819070081c642d04050300078000d803910302004061000d0045120149841000252140c14410272107500601e10001031183c60464504803040e9001c9003503a0301000954408442c1c2603400d01c0307a08440c1c0c1c010400020708604040405080c800c0c01700402008201e4070000c241114012030202c04c1d01e0030350f41419191a252040030071314a020700c4140c01d41302460101007005115022030300e0300555201ea517040010340d80346500c1e00d03500c4c0220f11000d05040a0f1010070300a00f03101100030032100406c442c04030b051a666840d140c03d807282801845c0b0f403145510701408240c1c40244c035550b411042500c1c0601210014501058803809002d202900c0307109295044000d007c01988918285103074141c0056031001c032180f00100007a01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 566782868 1250 566781618 566781643
    0xa090b01030b0f0f010506090d05031308010f0e030c070905040f0605070320190309080702030303090a0303050609070f120623011b0809091e041a09010509030910020309030f 76
    0xf5020002400801d80c4075141c1c4c1a548001d080c0e1f400d22901609100e0034200c0000e045502c3c0c4810409110b41400305003a0314000e0280c2c0700041013050a954002003500d000401e0313511345a0050202080c000070204818090300c0315242d00203465039581c101411a844154405091301d4944010301407202d074180c0080c082e0b40104007480103141c001c203103020503511540e4048820741c81c5011000122a10a8100151540c01098058188015500007034115031007600c0f900200c2e800a00c0810070190140607030b6034040402c03600c141c450319002201030400e8200051410401981c24980c249a04855010702e024154011050211080d42d4080e0500743d82e800e5400c0d030100e280e40c50100540801415403c51095224000900f0407142c0414441c5600000e08201d28a40301c8944118503c40c0d280f08040c81540034070804031602034658642100350501524034803291b410081000701d824000021500c8030101a07980b15008a120307501241180100d2507031070740c18000d600c00d0fa0504400028903260102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 566784118 1250 566782868 566782891
    0x71e03020607020d0207170307060c05040f060c02030706030e0a060f060617040c0b070203070306050f2403070506180d0804051504210f020d030801090510031a0a090b01030b 76
    0x12904030b02a03035141004540440107074030110042c050103207602080007910103000102c80c10100305076a0f000503103204c03911030000584003180410803000400b4101c002002c0310306041070680c1c500d8010a4403143c00d8000c14050549955142d00807a0b8100460300d52260880780402c0101814802032002d046203220fa04002000f5542075400501040d8080d4082c44e440311800c3c20051401200c4015070b081120260f81c54080d085001000c11800d001d0148075190701c4e001c4110b01d261600c45c412503007111308071003524401560750302201d80e18002140c02c00d442c0d0880e45192500c0032581400e0300d5043c0003030059040043c159941c01008011400f030002c0d0f9078120b801803102c00c1000750042ca80e000314802c1501007500c25000d08128020241500d087d140192600000c0a5050300440e0143c2c08070202100010180401002180b40311710415804c2071400b40082c00c0d0910310784401c902030503c54090b005080016010500d141c100d54030181c18641c1c0403401c07200d00d40e52418064514078044810761402d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 566785368 1250 566784118 566784121
    0x4020f04051f080c0f040909170a080106260403080c09040c09031502131403010f020c0a021008070c0b0c09180f0f0c1c0f0e0703020307080111071403071e030206 71
    0x14101000e03506804000c96205d0f040916064150f405064040b0301507c1d164400401000d10109401c02049100b210303450b610217035490548010b1586080c55000e9600c4910b002640350001c5040600c40c2d0400d03098504010700b0345500d0941c40152180c211820b0744280342c10310301180c2603040b8020104481c0159008410741c541c00308504d0070f0780300740d1852964000360020140812000208424400007010300002404111083ca500c22603114112400196104a0708182140b81c210700d805940c0801d4a0308a100b030030608405000100d02200050000340410001445000740809603041d47d41c008041c0d40f085060482c0c1440d275500241d4001d40341411240000f0b40c2034000b07681c400d000f00d80c40d0380c2d082d181c81c0301e80b00132504090440941b0cc400e1600c0381000040b4210a020702c02d243c02090016081e0b07a85541304151419019911181e2141d04040030018a10f00d4082503801080c0c0194202c00111900b2031410f0035481200001801c658038404400242da142405400342c40d48240c00700c034000e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 566786618 1250 566785368 566785381
    0x81219061d130b040b33120a120f17010b03041407030f02010c0305280210050c25050304060e040621080c0a05070e07030501150e04020f04051f08 64
    0x403a1807002c090008410781c0b0208000412030100c0c2a40180b45400003c0104000007480c0383d001000200c03850402c03080c680c003804a1034501954015924000000c04c1e00c2c1384981e54011910708603183c0c40c0c062040d10640f4400c030b1713800348034140311890001c0d00302d68480d03031070b4450020345400c140c40c1a5400c2914142285500800040e40700c00d0341d801c01070540400c1403a07070046440c011486400c82c1044424016019030100d18207224032060300d02c502d0705055282440780289412038000b010042681080240681500c802086850485a52042d881e1069542c1c0b4100b8060705401c400820700d100c0094000f41c0c1c250b0149240340c4106086609219070f580d101413119070b43c1042d03001844e0741c614600002002982030002042441c43c104283c82400c0d5240d100c003801c0c400990301100003450b00004108006078580b00e1076014154a2021044540302a4002032400e41060002d9001d44e50000350714410100d1442901c008200061403228014111550001203001070000030000c113640030081800d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 566787868 1250 566786618 566786641
    0x4090803250903060c090801050708060108090d0c080d0e0d090305011802010206070309020a09020c010e07150c08031009050c07030201060e061804140d021e0a081219061d 75
    0x1c485096075000c80c4281503464500040c07040f41d00c0c80c1d0502c51039010000d640042800341521400450712102064940316002600d0903400a00503a82508040002c400d00c40c1c00c4102100301d50303007100703549440749070140740c0a00038400075500000a1180300f280300062940b0100130300540344508001d100000400710b1401c0c0d03040c0300160090240c0c0213040010300c2144254800402207000510015525a440320300100301c2e80f101040c542203075150b0081140ea0582003280da0000c1c0007400005071801c42440700101440b00701c02000b07040501c000301146d50400b9490b0108040c1c110300c1c00c1008170703043c0f40400b403a0a030302400d0220055420a80001107084502e0b80c514401e220140c8103941480c41c100e101050290b00500031210448c00e03038114482c1d403004000301080c0100580017024402456058019071008441401c0b0301903215054100010f5044020303100e1803240410191416117800d10071080900315160002d55072032900b840002c042409200c044c802c031690741d00000086c0c40d030010641c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 566789118 1250 566787868 566787931
    0x80d0f030903090603020c1236010c03270e010e07110706120e0712050f030304120507061b090f08010e0a020f01020703140d1b0b0105010e0303070204090803 69
    0x40100d0101c031000c22296010390000d1036a40c1b0594140c07070030442034008e020441e81202e002d0070f0074841208440c10115036015003072180102c401c0c00b613920380100030700002e2040680b804014104140710b00d07012940e04481e0a01c0d035a000f443c940c00400d070790701e641c1075140c120424840c0b1b6460017601d602043c0464001c25134500507000700c3c07024090090030100159445070302003d1404080d0307991385142090000c1400b925003c4c15551000c142c602e40242484d5144c481c180c0700d038a038203401c100113020006400001c00f6481407080e09129440c1c06107402c00b130b0010701001d017940302910f81d9a48040c551a600011a4042c1c4903809100d030803150725030000900321400074030b20700515804841084050300c0d1000c218407500703d052045802030b548130743d58070446c50b040d1500c4602c1a0701032451960a943c100e840d40841551000030302c00e041000f070311240010841842064144140300c03e0940903510705004075200250060418849504240f4109881303900c21030312601184031040d200500c4130071414059 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 566790368 1250 566789118 566789123
    0x1a041104020a080c0c0a0b160905030708032a03071a01080c030a02150405130e01060605030601050306090a060909050a14031c0b040b040c030b130b0d030e0d020604080d0f0309 77
    0x3c0141d03030781c04c00032403a654004a4024124450929440d0000d64910340007845071031002240212300c02d662001500c845000d0300a80d207e03800010003481102070000546041c0c1c507404802c0d4242d10461400c0a21520030b060300000c90b80000980c0c03805000c0b402d0000900311180652008440e0707a03802d42c05840e00341d80c000c150340c503800070b882120143ca070903580c14071180700c40420145401d0341c2d41c001941c0036684c007c80307031070150700d805401126940c02e10506000340741758141700d41b4520700480000d05512006012038400d10064010604013881648484058144940c0400c9103095901f441c940d00d061440c0200c1d12000c10000600140d00f020003941c410700f05541c103800f00d0110030a2020058012202820b070490b03038500301a04c1c9541c0d14000d800c49001c0c5602c000558040d8001401400845080400c44090034000c01d18056294050640145a01864000e041c844500b0008000d0345402030081c0d48450081400700b168000451006043d003803c0e106c9080e1b00001100a41c00e039034104101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 566791618 1250 566790368 566790377
    0xc020129031b041401080601080f0c060403031101060b040902040512010c050708160f200f030d030c121a01090e04030504030b062205100605120109181a041104020a 72
    0x29000c4641e10301044054580b00188013107181c0c040c962242c02c030000c00740d10a41031948100010841104180408215100441d002e4503030030440b400403d2a600c12440001e0070485803440d0500759210a50010300a07201544285a035a44d461071845c020390003074010944694420075982500800510607042c004242d5140e290034107100791180361075034200111200301070900b510001d0000e038482d05030b01c54103031007541f507440c80c0c503080504001e41c0003003d00ba42c9d01a011164000e55955800500f19006240c0c40c47c011548400384a821112311400299010a141c2170180d4a170112101c0c20b0852400d00007070361804090b59072071402c001103c00556019021440c04c200a00200d240144590341c0038030041c281d04680c042440c80a03013502080899484110303079070700a001310500c1e4450b9540041059160650030311100301e24440e00080c6c10701c116160580d903603480c3c010002c0c1030021794a5080c0c00c907102d40628803e880040201250480d4100d800d12458021040c1c03a01e00744c42a00d017184469600c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 566792868 1250 566791618 566791633
    0x5012a060e03070804120c0504140c1b03042306070c050d080405030609010603110a06021218100e040f09080304030f0201150305070f080102030103171c0c02012903 72
    0x4540340281104008880e0710b00080004802054407030000300024440480c10390405c4400b810008945843c90b0002d512480c2001200345d80301551107003240d0880c0c407255289aa038881640c0805c064010513203101c40030302012034001000e40404480c80207403007400e141026280c210004008040c45120001020b850040b6002e2055091168038610800d1050454038609901d0f500003a2400c0700840d5440e40b42c0e91640700a008108080480851155055070260505400e00c60b01a45542c0c2500c051b103103091001c20a83c0811000e03e4984409041c0982841c000181c808001014000c0e8006154004c41c1801e41040710100280b04100d80217401c10012811a1555642280c601c3e0032003001d01d04540d2281900310402c1050580303e40114807690041c07061a00e0a003103100802d01c2c982c080c040341d9106000406c0415003400040c1542410301d43c0d600da83c1c41080803010812184086040c0c800c0d40340c070f008402030a03015070005d40d4020a800c8680b0042c0c1501d5052030b050340c101000303d60076401407003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 566794118 1250 566792868 566792873
    0x31205010b0c0307111c140c0609010f0320030108070932060315010807030308062b05160b120a0c091206060504111c021e0c030c01050a0605012a 64
    0x141801c030b5450042c000350007101da020380040151521b81050b2140c0807018000702003181e00300025265040203550080c28004402d00182002a161900307209054641441550700f051000c40c11102040c1401c2c3d843d00c0303507140d112913a91250365004404a507450049d071035034403450483c600c0c04c407005200300412036980f660020f45415180582802e406124515656800041ea51003d602030306988006042c01c5285003401070020a000d807540b8018540d0021340d14891241c0d000a0b42c00090f003007211801d603040f0f407405500d020441842c541030f80016802c0801c3d602d845e40300030070040e91540040c1702161214040b03241214500203e11000c0391141d00e040000704074540c55501c02600503507000030f0490b80c801c08542a81d03401c507140f0403050740c00a94202124481100b100c000c4518480840c20070101400251038110380d072801a240c80b00c041340504604600300300b150440c5c94100c0091045042030214580035001b90f025440c0400c070445051070301b10480340d2000c1c0c1303240c45107900c070070030f130070154 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 566795368 1250 566794118 566794133
    0x261207020105071a0a1a0a05130b0a0b0706051605090d23120705060717190b030109061a060a0905040b01020304050a06090f1403060412020c0a03031205010b0c0307 72
    0x2140129004071130b032200314020395400660b0501c505111079006c1018a10742068601035100034060b41d22403d0402d1062020380c48489d03003174040120002c8001070400c009400514080721517400344070701100015124040005982099004010110b00c41c0b0034015006802c6e501d03405502e94549e0400e0403082600d02040201d081a02ca002c540c1003003400c40e43e54040564249400d04485403514880080c550b401c1180c104040384c2e10900d5403800e1070340322075000661941d400e0082c1520301d42003040308a80064040c01d41c001200340c10001c0c001c0051040a00d8140e0240c040000364000003407042e0034404031400c114041390b413150313a01c0c0e40b0341b5002414002044000d06054005034110322091002140039110308281401074442034070303004c8185143c81c0b0500c0c51901c940c1c00003060202c0040395019a91000500e994010368003c80c0b02c0364240070f0400c01c91410b19004182e0340e0140e062000007003403540041c403100c5601815401400740760388860b0440d581e8424030a143c2341c02d0744100030480104408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 566796618 1250 566795368 566795377
    0x50606090d060e0a060e0708011509020901030209061b01060503120d150302100801090f060b070b180d120e0d0e1c061a0f0414070c020a030c261207020105 68
    0xd035000040c0a4040943c0302e14200c00c0010403105680e5440560303020100801c82e004c000d01aa50080c040d98039941c6410185411a210380801b0301e4000c04c05001030380c0250142d0f000075201602c0c00b07440d03404080001409031107000003070405501c0c00c01e0210301802c02003000100381601e80e801300c2c6005500a01e400040a8807012034a42d400681000310060f95411143e2010312000e6903103c0c2d055040c0701c1c160b41210307407540099441c4c0345489402c024481d41c64083e190303183d800070040c400c181e03a5041e0350b240d45141202440590b014072900100b0640e0010402c140c0f01e20b80c0714041090400d509081d075070314450201420085003007007081d04c0c124640000c590085a91242d0215144d00543d5100010348081c9407481d04410303040050704426061140e01840001301c221001d0200c0408003c0d0981258005009801013040c8403248a045d9214510b6000045a12221603240c15a0f903183d03420240c0e03000c4480c6801c2c460b94a05484400500041c0390003c55400a0300c58541541d950064805612 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 566797868 1250 566796618 566796623
    0x711040e12042102120303040b09030403051203060103150b03091b090f0c132c0f070806040603020904050106050a1d22050105070c03030e030a080610170406020d0b04050606090d 78
    0x40f40900800142c94458561402e040141c0007036841781400e00d080741c4103400041880f0641c1d8820300c4200b002c20800500b01003040001042030342d6a40741c403c012806040c1e003954800e0b848484840015074a5809001903114a80c8c42e000d0b14490150800c400728050400450b81d07a000c400100454802040100411741085000e06c2e0107142c0601140e007074002e45900e42c4a40080404c1c2900400e40040ea030704481c80c00745900111040516018100854000001d041360042003104400035840392184c0e0b001c01c02940e00103180500a1400b440d102d4041c1a0602609008204e01c1b50005a68101b41c0c2407d820398108491710001991084d00709142402c010b000350078452042500316002c12001e02c90300303006d451142c0d40c03158400007608024069844ea200f11419540c0200001000c0c03a41c080d20380d940101c0d0485207a41581d0104c02c046500100507080780701d99403446001d10041001c994014001000c00403001c0c0039035030030401004116181100d030f807600820204124101807a0980100b0042817 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 566799118 1250 566797868 566797919
    0x160f15140a0e1503010305060f04030f0819110c0c0f0607080706110a020c03060907050d031103120709150201140a021308010606020a021e0303190201110711040e1204 73
    0x65a000c00543d040111580e01981c41c1d00c00001841407000034461203502400326000d400b8581080d1360300410450a06040c03004002c5158041099034042100e66100e82d40c1c2c140c428006801400c2d00b00300c0355800419001481c0c0300324100041103042c4107020710352450004003014106a49510b4070000350340a14811210580d44110a44940300a100500384800190b4020898a402c801c245031424501404039030081c1d000e02c508110310f9941034070441000f1340c585000b641034112408940c0ca98003c03894000d4030000450100040b0503440401701040f11002e101a00780250505000d07401c03190314640d0410030f00f014000082418040707070014424a0225141071030320300c1ea80c0708807608494240c3c01107001038200f502c1c0b001c19440e06102d0000000000148144da400718400029903034460749600300e01c0403c179036001581446c000e40c40034815055188035580c1c1e4a02c00d00c0c0c2814007140c2940b00c03038442d510305040344811070740000300f502403203655400c0d00d803405090000b00040301300814000b11501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 566800368 1250 566799118 566799137
    0x9090b03070821041e05030c0d0809060706110a1e0503010803040b03090f1518010209030d0f17101505030610031d16030c05030d0806130e160f15140a 66
    0x410f00a402c030b041d100034900a0504a5090030101400c14901421089c803841040c03108002164000c022540540c0b4101c50f240d580b60303e146003140282007000c0c00051407080110303a00051341c0e0000d151400c00e907400b03070080c03401c2c00c00010241d51901083c040d41107140e00c140310901014050030f0085401c10780c5602100e0402443c2801c144c0fa011082da190401c00600b0010700c0f00a0403c80c00e001d80c801c422000030341c245030820f40403075070324a2080c0a02c0d042002d02c0341c00f000205e0050781d4030705604603282400125850f08581200d4083c1c035a200354221841391540103040d00f8850b609403401284004c001400c0802030900c12000f502c1c0d21094140401c1c2c15078482041d0800c1001840003514080c40d04490151942c10300813460080c81d132180740a9003090044841c4035174070070019540194111846500000310003020001802c003140450310501c5603580402e0514034440c55581140c06c0c41c0e0b6030746e0002e40c403002204a4004091505800b00c0e819102c401c1c946c5804001826500c0b80c540f400d080070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 566801618 1250 566800368 566800379
    0xd0204030c06110715120509071a041d04140601170c010306050f1302040b0a081005090103020303220f06020c0a081209040914190b0f151c0b0709090b0307082104 71
    0x1c907035003918030000690000c0300030852082c40394001001b81300001400b600b0310303180c840b001c4804130040d0341d20340c40061070310b0002d000c03c00c5400813b52501100c0d81201d03950b603181c070400e44076400c12601d600785601c0f40301c09040256120740100c505480e00545404110352840091041550051500f00040b940a00c00412075a030401c02402d0000c2103503854240034201140030900325001038000c540658142001400540c80c008104c0700d51215000960000c1c010281c0e551607218684d4210001024030b10800141181c1c0c0044d429120b407404907849042c0c10354814003596584010254900d200d0002d201000307461030294042c2c044280919403c8419400455a8904007140980c84250a0341071080706402d0040d8510b599030310140c2820854101d043c80200401072030103102e542c4e03110340b506000c0d45080001b002000855280d0000c501c1d5038900300610064070311039850003440030661400003c8e94551034005483e00440e01900094032085485c10205070301403404280e41c824142041200140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 566802868 1250 566801618 566801621
    0x50609151c120c031814090903070f0b150301140a020708070b070c050d0207050a031e0c0e0105130b0904060b03120f13120c09020306150d0204030c0611071512 70
    0x60b880a40d03902c04828803503d15010b48001100f111400c01030b00c03507900906c420010042441405281107800c18540e54480411038514821000c00400d0340c405818503204001181141074051810035a050a4141205081c10b00706d402910074550f034041c00001145080c40558001c202c10307030041340705c1c91808819841d00070b000c20f029909880013800385e0b41c917007085c002c0522010700440018405011010300d010001154241c0070302000d4000c0481108001c4001c2400e010071504a61050340d0140143d540c0f40000c048040900c141801b601400303a018401810b02e1142000c1c011004101ca5a43e441741d0715424001c1c0400320a081c1c1511130f40c0244040e10080350050402c400591229079540c4c4070744d58204400f40c40d43d40c007156021994503980d20016448144050954120341c2c00180c686e594000028201c1e080d00503500c212410006031650100140d800a00580c3c0c0909a41840260385c0c14044901c104101c600101ca908804402e000d00b81400c0c02c6844240420320300b100203281640110f20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 566804118 1250 566802868 566802893
    0x10020a0c061b030b31060314060a060803040305030403060b0d0b13051c0c0308040305040f03051605010c03080408030c09062d04151107080a050a06050609151c 70
    0x4030088204000e07010b03810b0013029001181030b200c0f0180710b503010041d45210496602c400d40340c001a42242000f0200542c03113030b0000c50f0042c039160b200c66903820342262142c1c01a1a444025400e00c6004075150100204640450345c1c41401140b42c80e00e1926903000902d2064600765000034011414000f249400ac0380b60b002e50058150781000454034034015151440821910103488810401565036580094214890b5600350829005a607110b24045a043c49160001e2000041c043c0c800300510400041070f000301031100d40c00113049034442006440003922010001d00150010300001d001800c04806160810a09042d043c01c0002c0100000c5030340d0003691044401048855030f4030042924581e0040c40803d07141401c6280504240c086401801403040d08030612a200058007110001040501e00a242c840f054842440140c5042c81e21000d0048040c1da0140c108004a5007600e41801c44134005e65a082c050102d0040400a1000303182d290361459403580003803061100032408005001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 566805368 1250 566804118 566804141
    0x907062102122e0f05060c01150803040f0b0c0a021e0d030e041b0e0418020316061403010b0d05041a101503020f0a031d030f03010501031a0310020a0c06 67
    0x2681111080c50500e44200c18101a0125180c01d20038200031013810302151105440040d42c42c550303180d20b60f119030f0f8050a030410500c541200c0c1260009034001010002d4029100074101145c452691507851000c2400f07080d000c0203840e00011040c03030043c0742c90f01d035120449406005d111900320901c000110000303240201a03001c2a904a4049030a2420b0703c160321300700d01d6014290394040000103000b40a0050019442d020b103a982840703140f81d5804603071507100240e006045542290400502e500c00884602c00d80e00821046002000420440703c00c3e0790503590340c2d1401604185002e440e01010f400c003d0429590301159004490440c80304151182c0318150b098258844103180c081c2c102c94403c40310308030004052040c09403032480000300c021105d008c0c00704d10300230070f4010208103129542d80e0800003201e03042c400000d42c0d1030174200c41005141243d400743c0b020060000204407180b400341c001b0286550541002c4c1c041080b002c0b41e5030281c90380720145d00d401013402030b0f55940d40c0d00b22400341415 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 566806618 1250 566805368 566805391
    0x3e0109330c09050411071709031618140403080408281808030f0304110307080d030f1b05030f0c0d060902030a05010f080a031b0c120b090706210212 65
    0x9000f282018000d16084031072000c1618078002054561400160203034480d190a643d00249580040e80c00b0001099014660218516490b07501c8141d00441c205c1c5a6400b010507003840c0401c1041e00140f0301c680e104941617201c0d10b02c00c3d59076564060103030b40550412006902c000d5031490080b1400d49440100c94016160301140008a1002980c1349041d0f50064180b5841042140301c02c2840d4800da03504280e00c1035222450030f4801000a040100603040815184a011603c0f030070242d164105d45030341642910100031058584910383c030100000341c02840412402c101145084035040411903015130a060758504050580c0840f60580710141d0081c55920f401205000c0c0c00c00180c410300b4010300d542e43d0a403860070716110b20151034008869010b800d0203414545107600c64150301c061040940e02140e000c000c941c8031440743c80010100f1200f038540c0e501e030100140c288000003560b131090312403e0b100c03501c1026005c03468203994134624541041407502401425949000381048500030700d0f003001c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 566807868 1250 566806618 566806637
    0x4031a0a0510060e060c010902030105071205130f030c03023301050d11060d06050604180f0b030303150d20010206070311090405073e0109330c 63
    0x44000c25910301501201c0d0601d054a010426240c00000c07182c2c25138030a45090341c8402e989506207004240a000c060b41550901c010800c07580c1c0d001078194500c1d40c001201304002d4490f580840a8881007a0009003200c62800401000ca0701402030005002d2080c07044485c02525443e5901001040c6822049040d034943e03480b00382101d445400c9800f411f001c2e40d2424a80e501912105080240d040c2c1146c0500b0002078280c010b901c080c0c2150380640405040c1175070382d40d034a0900c9800040c2200c02c810700d02d440c0003001e1503610103600812902c2c4400500460550b245e07024456a048104141281c1c00303042001c1503000924040e19407070545050502e0902980801c800182c00c05100420070001c16292841c5c008000b0505410758014200540e00081c117540c442c0c0c01902c600c820801042101d00222103011684040040414124901480c85114024004906501307803425068010010f12403030405454000510015004440e6001e400c49411b4103121950421200d65000e1480020307072105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 566809118 1250 566807868 566807881
    0x5091309052a041b080415020a12110909160c05010f0c031808030f0a060b160309050420180a0e092a091f06050d06080f0a080c0304031a 60
    0x1031200d111882c1602d06000b00c0c42c4080d090581c580860407954103000800c800300b424440d80b1401c05c0c0314441c10200071596411544030142013600b40070134115181d810491b800184040c01800c0e00c00000015140340c0d00354680031012180a0300031040002007210f61400e08001c14424051890041803c0748001400c8107550001401d40c0c0e01ca10740074500101c3ca1412400283c020f404680e800f01001070740ca0300c0e540740e2001017000340c85590f21400c0085400308848107000c1c8104000401144262500200d290b0741d0020b1009850743e101f502c19000309480f040c0009d01403442d0003001d00601000c40058542124000940155415000071540d00450010001007003810402031960f01000003c0e0464800d021204401a4061509140c02505174030302007602e24540b4051007801071001080021481d49a89008116800c01d0403210202e6040c10070000312500c021800ca40e150200c4009003086450a8542101d40c1e030184001d011640b004000000200d2000408824441c1c26a0640901070a014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 566810368 1250 566809118 566809183
    0x501030506060609030d0f17040501020d0b0906030a0f110901030b012d1e0306020c010b150f0f13090501320907110304090c03020901090f060509130905 67
    0x4146500640003004113085903a000521513048080307510340600240c200d00c00445003c0c1c010a0b00c2c420795076a030300c00d20003000700640203001d1030003c003030080006140140c20402021000d43e01d4a405402002ea8100400c84441820b05074034090b400800c850003c43c0085041312800760310580e8444d00c41c400500c0020810024020b51050095003000300000c00c90702020305080d40c1c801c030807081120900030380f203039a00032108100454004004544032144158114060001009194410400c0d2070003140d100c4010070a03180e150020030300940c00c00c1d0445903640301c40d51160800c0106010000400500d5600300c0c05228060049818107058040b244910b0082100032200e1700001010b1855610000d91200913045038401c01924203041402c000b81c0a050451040307800a0040c582084403290a0680503001040703e00400ea9400c40e50075510016211b505140740102ca00040d42005030300c05502e010a0300d44820b0b50441c0740040c2003621a03807000e00d04909000c00c0d10708545003481c050300c2480714 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 566811618 1250 566810368 566810371
    0xd090e0a05010b0324090a020a1103030405030415050c071814060906090612010e0f070501180b031012030207030204110f1b0319120f020c060a09080903100501030506 73
    0x2080d0a12032541070078004101c90000030000303840401c0c44454414410105417840c0128100600991074605124203218040d60000c40e02d0401300359200025070036400300000302d030305c0703150800c0c080e504007420640c6074a02e042d6002180410081c050050b01003030b100030b0028400034400e95040c007042c04000304012040d1501c0c3c4a059020401c031004202041c3c645890195020500300d4182640d40e94081c00503543c0d4a40506001035580f0b00245007801401c00100c0c22200d400103402c1f01e05241da900c004541c601030048644120021003501081815024030285030040f2440480b4001c15850304000c44804044180660060b4040d0408009500f0103214201d00d6401c044402e80c40d00d00c1003083c0307042c0c61098512010071112a01080303100510140259101c052105404040004c1c14001c01021458014503076400710f4a4035000d08040000e80c07080b5004804c0100c0030381401ea403007443c20b6009000c1d0b4030054500d00401c001c0500f0a5409106002d079540e80742d50001a02d505605109140000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 566812868 1250 566811618 566811631
    0xc0d08070507020f01122004051f09061107031202060a0c05130608100807170d0806010e0108130632130b0c040308270103060b04150509030d090e 64
    0x4104400140c0c48102e80e00302082001e00f03005684185061b0804001c000e40000043c031303206e403175500aa0f06007990780140708840341150380395000c0c40c215400c8002880c540d0980b4000c1241d007141004000c2c0070303030310810240219070241c410003507894a44051150715102307a0300060700103400f0000750410f02c0c030901c07411001300c0ca0040e0410035020303007501a5840f03501072101440503841c001042c11086c41c01c0c0074054880b035401d07203010702c0d41c0d00c041080c0e500050400c400c01c6d0140c90840b503103d52088810742e22814050707650420490801c0e00544100501030850000c1d0500002528080740c0305000b40e4900d08004440c145120f44c040390089481145a00300d41440824801070059250001d4948403005801074002503064440070710340c3c015840780d9400180000d00115822000010010b03562080759440101c0c4450b21244000441c2211114080c0d42d103980d1051100348070081030504a6100e0040c0c0303041080c035142c811000246000011040d280004050300b906001c4103e0386000380d41c00c81c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 566814118 1250 566812868 566812877
    0x210e01020105090c0102101e0207030c03020601090513020609193c1703070b13020906180106030c0912050c01111b0d020d060c1119050303060d06060b0c0d0807 70
    0x20361031300007511410050255410303542c542d60180c61f4029403140728a03810051500071561041585805481c0c0c1c2481503055015000d41000090742c1081e6000b40c078803806440e03406100f0300d0825401c0201d01d4001c032418a800c40008400c14200740710303084030400a06151002d0007005185048203015a040c40402500204000d02c219801e0340042e07050001510341481c40050841c4000070b600b40b07075010b81500a065031403640240448400115a0101c84d18020b031f8070242c0c0380c0d4409050000c041c1d040c40760b040112000c1c034010031016109502c482050380c007500c2c0c9049203a65a190300b005580ec001700070359050b000507500b40d0a030b6800485400d24040d601e8050842207940d8a0040b444228030402d69008585110580b402c5540342614000300c036a0181c3e08100e01603c290700100948801c08011a0034800c840d82c014003a07001909114086500070020b40c90350361140207019603a07040301c3c4101c03106034807943c0c0456210141030140c0040f01c89500180800b59003d0002400328802401c07030000c0c007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 566815368 1250 566814118 566814133
    0x19090e190e1216031403011403010c0f0f0c0606090908090f0d170a1e08090c010306230a1a1314181e1e0a06050105070f210e0102010509 60
    0x50109070b040da0101e0005001001000d18141404e803080b0040c1010307445012000400464001c00b2188030010404e810350080100c1041074400791100b45000d54a0800304000380070200c100c6204e406440c001030321a00012600580e41c404108c01d684a802d0119174014000c90b441c1682d082002c07407a459400100c40e03042c9040c00e59200c40c80d0034074888070b19690b904400034607101c140d4028203944512010b40c541c01d44418084d03910041200038180c0d050740550081d005800c9096100c0d00688003610301c40750b0400c0c0f980b00c1d41101d42044110441200e5048403920a00249801e00e000d1854002c50700c0c1c2c0034181d51020100030314000003000e0b8000210789822100202c046403130f000c005000c7c89652000003500d5880b00300c05443c0082d00540305d034080e126401c0402c8001020700715608500c0b910204482e044c0d8170b600c2c200c1c02c15210035002e000d0004100780310320000718091025601e9600e00400b41a0201645040300c9600c2c000c00780c00d1800400c6801c0d1000f13a41d541c1c244038440c1d0060700c2c00f0282114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 566816618 1250 566815368 566815393
    0x2c012304030b0a0516080a140f0906131205160503040f030209090d050315030c1908010c1d0d0c080a0317010b0702152109010509010e0703050319090e190e 68
    0xf0411700300482d01c100041d03140003450080c210b50111407140c0c0303001450406442d18590f8a150108101c6101009004042c0883c07080075074160103116141d40400807800c2c0025800c021a225084100102d0799080c11f0307000320010510030b0001b08060481c5c682001150b5081d40103011101c0406031107020385603c03446800ba1515800301c2903a80105843c0b1289009032500000203282a07004224a179001c041a0811017094040c110502c088940700c81c001d000700ba09141007514001000070100d141c40c5074104034806186081c40000b91401d1080707180601150f00c1d9105070345820500f0b1012000b15030f80c41d40e01d80d084402d0a002130f00410700340c0c012503d00320855022a800c0e8071000d01038009400c0c045007014100b52440d0821483e01030b201d243c00c0b018502503540700d010300420b641144842d40381510320a210302022071600150785c5c02ca00113601c2c09021803ca208410680480e900030440c04280100c1c582044c80b00303450140c080d02400c1c0380907480054120381221700d5000c0964550b4421443d4004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 566817868 1250 566816618 566816641
    0x504110301050402090601030c170414061b031504020403020315070813030e0904030203040b041710091a060a090c0c06051e0c0703030f020f1201051905060c0c060708040807062c012304030b0a05 85
    0x5110c50080c1560078920100c1012034060301803608000e506001d9031b034900041c552070300f09251203488036030345400301602c0364200c1030070045100710040d0004004041410950403c0451a030300a4482c0c0f0440746800e5071640d510f413241d00305420211103c000042006c825080401444400c0e090a40f0100866040e550300d4400d460754a06560407651501c0001864543e07e1a030018000c1c070a400c4140158800ca1400901880700780d8000c42d1801e20340700200c0d07191044507061340303540080b144005009485c3c4c1c001002d656003080008904050711003220000715030007400502442194a60031340d407101c282c0c010000440405802680c0958104050259465070000c00c3c403084900503505540d5910303c1c0b06003603080000c444440c036000744000078003100300500301c07008100311803004058030081a25188100c4800560301035210004051900030f082c080079040c0ea20041c402c05040010500c5251b291207943d021120314401148007020404109106460341b5895010001800401207882e00060029 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 566819118 1250 566817868 566817871
    0x80a0c03020f0325030306150c17180d06062303101406040908160813060806370902030a060504090c090b0303070609060504110301050402090601030c170414061b03 72
    0x100c803592140b04c8841454000d5100e4400340c102000400401106c46101401d40d400002c0b048030103190f0150181c02c284800000e9900341e030820300410b2480d1100d10200044074114900a03110180e541c0e20001745000307001ca5160488112075200d040e0002e090080500b07080c4c0403013a0300d08040c1441c00c01c050405d05019080c2d445841203a00003491901750804000c41c1c0140300c00940d040d007030703504060180b10010000e8041c0050401682000030f454907011280b841042d2035040c0c201e500601050b03c240402c10040c4804500c010205107054000c41c40b114101d61654015204541c0c008240441d02042c2d004030360181c1016102401401c040d951165900a40c80c0701c0c0c030240c075503110380d00503003954140122005203811150500c190091410031a00500091b1801c8884420102543c54581018010103100d65002851030006603680001540944a4040b9003010865005940b01c401540c4066030b50046009800c148405901c424019251100c003070702d1500c00c40000010404a0701c40e40c81280e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 566820368 1250 566819118 566819167
    0x40b070c050705092d0a151202151c0902030c0a0b0405150f070302010e1911040b031207030215060a0302280b0705030a08010609050f0913080a0c03020f03 68
    0x1031070145e49004c2400c601c45041c0c04401043e0460a050015107501c00a40c90700921121a0400400c1658140004141c981c0d00c203c00c00d480158002801514207030840e082003481445655181c84511010f0004200e0014481c407051070713841b44540158101004014072907002036480c0660b0303d00b81b013600742c0c460103644601c80c8540c82040c5581c0b031045248040d10180d880d580780d0170b80c4034500c6282c068042d24581003802034a1284040d24424828031001030320816800c12000c05a400020003448050300b0300c0c203403281e0544119032485d4140036400b4028070200d8001e9001d096100b1403954140d002610150900e803060201078810300141e070310814688a203c00c10622080100c201c070201200314500c42e070202004140206010082c09008402810151400d60701c000142ea04c500090300c00d8071160082070741002c6040081d00c41070815201300d58105009280c24081d4100c59075406946da4081548540001c60031584601010340400c0703840340d00ca0396000607504221240c0401f00c640713005000304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 566821618 1250 566820368 566820379
    0x20607082208160516061101020405150a0e2101050a050601050919030807030903030e031b01230c0102040f0806130b071e020c01090911072a0905040b070c050705 71
    0x9a4041603400e0b00240c0300340e40b00c02624a0b6405c011500c100f20700d5207224800100f90504120001030106100711b030140c070401011321581050014251211703400840e03d10040c0b1841d1403070b4100315503c030f0401c5414958034003136441c0c02c4c82e1800701c0242034038400740400c1c0d03400e4117080c14000c05a82200030350308130100a5035040700e0011403038000b200345102039001511004001900c582031550000e19281900c0c003d8880740c1201e4081400c1c555034803c00d202c0b42c1c1040c50516039542d01c940c4141400800d0039600d04108004d0142c03000848615804401e00001c10f07903000408001c02c17680d8503610742c01000030b50068901032814862200c2e00c2000f07140018082c48002002641da81c4c000c880e20508001940e01c4821000c0541502a598143e2500c216010462030a00028040540c0c040c907a681c1d1524502c141c2000030b01d540e8110002c1540b40d035080c40c1007120030100d2802d602151060001d090518001c5800c0c10641040490200c0180c0088100a0203420301004075100140381c2c0d00b00e4806444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 566822868 1250 566821618 566821627
    0x303060105070c0f0e04061d2505031006090e071a16050318010801140d0602030601260103060f0203370204091d0a030f03050703090b07020607082208 66
    0x41c801c80707500098220304c40026000c280850b540c0800d0b91000e201c0d500c103d00c00c101d014a00303562046a55924681152941c3c041c0c40da034100045180c10800742200b80d14030003000349484400090910708401100354006a491008006030352060003425001c040c00405095454280752030b10510600b407081203070b940600010104c59503c1e20024907008a9041000d80e40c40d01104858188000b03030304921540004c400500120720568040d0340c021011200070440c5200040d1a0b031498081e40004009505001119400b0041c559085403c8607101c502508451a11741c11454800102e90710301019542c818410700800445d541d013001601e081091000b0030140b040f040a00c02403084d81d00c0070560b03200500201b03000481c05800d4104100018504511044071a00c1841d01d03691540701110140c001400141d40f114080d0113584817640100c42c40c44c01181036031168840c182c030b501c030503504080103078046004c100b1416488541a60416515204200205664074140311044040c54000e0301e81c400c0000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 566824118 1250 566822868 566822873
    0x40e0c0a1a220f030303050402100503070e0f0a050a0b031b030115030e0111040801060819030804141212011e05280302031b030d050c280b09030a1d03030306010507 72
    0x81c0740b10003c0401c410880c20264607498020050700054908074010407100e2491140c0c01d005106a038440c5200d44d54041c0c1b407031100420081900d0007559002e412114450010509440b03941d080300c05010400c2c507580d82c80c00d0805e418450034201b203044402a200034401440a42100b4040780f61100d441c1c81c000c1034001c92640c1c403c0c010442c1d1240f80d10100c200080000340b440041d00200d0484007450300f0340e03c401d01c00301d446919941c92104000c002507110000038002030070045203d080504201e04481181c3c451021214403031f4028100c421b01d2000850040200108285080032441310480202286500e001c0100e0b000448456040e00703002c01140c2c0d01c0d070079041170070710190007580c000b411940f28501c203c81180341c1008c90403d060203400fa03030750410000c078040c900321a518078004006003a5440c2c0c1000200c40c0c00d81d5841da0034155002c1440b41000b0450740082c8500401c1c07000c001d5552400c03034180203464480708145000c51500b51005540e581d68010060380c3d8400c1080c20519550700307492 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 566825368 1250 566824118 566824177
    0x510080f1905011b180807050a2c1003110102030a020d0e062208151005041806050708060901060906050f0c010213090204030c0b030603100c020c040e0c0a1a 69
    0x42d00030895485546540c809941c02543c080d0040701c5c1e241264212900c07225400d0310ba070500d0040e560000380c00c5404111591102c68000d5280d00382000a10608032014109040c1000c142d5907940030014203a01407050203150360b840d20300c00c0b000b40000c4d80f51060f00c10000e500c4500010090051140300e48061800740c903880201c6080308060f10b144414002501c21200b5140c0c1c050181004034415031070010307040c1d0007255120740904030322540540024a400c003040040d140e188828030780c10080c440b981c4001086401190b01034440c5403640001c42c6460820b01c400c1d400c0580c840e0b0100b00300790004006054001d02181e210082c8481d026603140c4018062034003910a0300000f40091180c440300065450035503000d0029071748215024080e003540c50382c2d020389500054034143e5050b00912840b00ca091280c4d8003645810351b03a80103a6104d8801140028200d410210308050950480508420b49140001c5020701400340c000b6800c04070342d5420b0280000d0b010b0003a1465020004088201c03520414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 566826618 1250 566825368 566825381
    0x20108040f02010e0d0317100f15140711040506032a06070b010e10051f26090706020c04020c0a020607080c030331020102030906090609130510080f190501 68
    0x5000108940c0c45803a0080c508550411f51040d260440e001103020071250170090000c40c1c906040d80760f000303800c01154242640341085a40c1c140100c060308486e1448200c0c0c01340050b20301616488000703018100a0109441000707140a109800818020690280d04031200e200007680b20fa01e946485460f40c045241c511900310060200001d0300d0000640540c1d10161600c9905a40f1640500c26130b21014441002d2045c00ca0745501c52158258404140c0720308120804000101d00190b46102090309515000f04103075607508003608014028804250104201c14199030156001c5141c100b0b0f5020385500e403050000001e10030000003601c80180441002039661011980c0c041d02d07500e00340006000202c5c81d501091445035405041c04000c03d9a140441d00c1c205a01a0041c501e003010820800c82e0a5001d68100365201c941440709581545035120607002000c0d564000064906210001e0366940955074842c0c14650720803200300c10300301804240416091295504a01c074ad1040e4501a80035014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 566827868 1250 566826618 566826647
    0x1030533040f03080f010f1202060918091501060c080f070210032f0702040207150c0207030b060108280f02070b010303030e030414221b0807031104050d0201020a0b01030f0b13020108040f0201 84
    0x4001c241c82d01d00710700c21030071402210344dc01107444510980c805000341d07500034400c480c00b0a12100340c02020a4010000308140a810380d030052030a240d42e400203004007840755005000a65817003281ca510100c0c0f6072481003030140340100c450740c00c00d0000348071101c0c494540001d0013030b03802040607420001d0300080040c489014400501192980000c000c0d81c0f00a54401a20210301c01404101c0341c2d4040c2610601031610311010310100c0541883c440780155030310b0b0b00c0d102da043c0e0303c02d810a84d465107840507007107552140c0e0142c03c941d40b443c24020180c90b900086409643c0040004001c14105904010001c00044c1c46510443e0101e00801d2000010015030030000307824034176081541d11300c80d130365100c406034241c0b00c00380d0585038104120119242c4d030060107040d800400090001d85880d98181d6099441441140c1074080d2641d9940000d13203080c2c0c811034050910219420400c01021081c03540102030300c448420761303049a00020714050000c1d01c05003c050118000500b5a445035112803003441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 566829118 1250 566827868 566827879
    0x120f140115050d03170a14071704030806030709020f0d05010501020304321003020a1205090703080c03070c060f02010c0509090a0b030a050d050703020705040501030533040f03080f010f12020609 85
    0x2814501c0d6801510390000c403507c480e24400b0014011768041c03414218111401100685182e4840d0b4043d180103801401e21a4944103034000020551481d0000701401400326a0320307034840403002c0032081512030617003081d415034005200c14800c0005a09100454803002180c0301c10603250303003c100402075801110580c0201c0701c810b1803540c071500358000b030112405507a950161040900d1024003115000c2d996899641c00c40f510803c042880035000d4020700314030f001964a04030240d46c64038540c1001d544601d002c6540c1860b0302c06c480750207105882e40c210180c02c0652501901500007110001d00500c40326046030358907011001d50320100402c100b000e82c0704d0115036808100000203006900803250403401440342800c0440d20342494010681280d50100081000b04c42c0a00f244100d03074500c0001070032806a450105450340594500d050056000710025500f90a090500030701014000f4819031001c020300c4010020350b10301c0205003088407012450030900042c80d10000e04544240589113a011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 566830368 1250 566829118 566829121
    0x703030503060f0108160309021c060b090a0c02071203031d061914010911130b04260616260f10030305090103090c120f140115050d0317 60
    0x140c0150045000d080100e84900095060300c004640c0f01000b1604000d02d040c800c03000c0448503001c0d811080805100400925142288040c61003980450f010155038003038407041140070034140811196085a8042c0e01884440c041d071030041d603144400e2041807446011144141c0901d88a940400088a100801c40258002010500c0d5a5500603151154240646400c200c01c1c074821344260800b4014044000002d6071070a40514002c01610701d101040a10401981ea85407a01e000210f001c1c06550352030380c1d140c50414a000c0415136400f4840110081c40c03842024802e00d001903125072102c60b0002143c0000c012400460743d0401031403860b946041e00e50740402660032034000c1c0c40c0c032400c001f095400d02640c4170748488912121910001d00400d4041280320615486900030404c0180030703400103e0031690f10702448000541001082e82c07118122030f8a68100000107880307a41c158010b4000b0301c5160003042407001d45c141c2ea0f00c0350343d1103107440c40f41940406004d181410403c440c03000000805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 566831618 1250 566830368 566830373
    0x31b080d02250e1302190303050c0114010302241309020702030d02150c181008090d110c0d1505010f0f050406061e031d0d180e07050a110703 62
    0x41e080350180d011900300341103400b210001c1c04042030b101203d54000111005840e4070a1035108900801c005a82192100301d00d2109030900c07040c603800440c466501c16541c1c6e44880141070860349400700d80392564554100400160303641081c50020303035080d413032a04510b48844416140170b11990503505854a104280010a0707101e517409400c000d03009400f40c680d5000e110740c0490312440c031216140403600078030000c65030846000c1c02500310700074864240f05600309000b001804034212a051500007030309000030028500d60a010f44488a0481d0a00300c20300e070320510f00c2e01e071507041032a000741c016040e81c40d20304c0900500034030741e02500750811410411035844651301c440d00c00088c080c400812642900008503400c2602c5000200d44c8981c0d10101d0071141418510855403000a40c001051707152917480c256000a200c0369401c0304103550040414041010b4050510261000640c0000698200030045a540c40352200d60048240c0b0b006580d6165001c020385580d1003808101100d80f01c0c0c82c402104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 566832868 1250 566831618 566831623
    0xb0a0203310308060303121305030c03120103060b0409020306060d03020c1507030215010f051012060b09030c0f0306040f02030a080a0c03200d180b0f090a0608040c031b080d02 77
    0x18490181d643e0210341c0e500c44090607502d22401d011001c681214200041da080c030f8200140c50390a1150085e2032409812805035844c40d00301e01c1d80c918803010942d00400c00c0001ca0300c03440800010584d03050041f600310f500060345640004102c940103011a00c003410415200348820280303a6001404000c45107a04c0045042d0b80d0800074044000d881044902c00c00e41e42c2c41c0d09454103d6800070700300d0b480b00d0300b0030b03050140001e503400d51100ce000196054050040e241d01401c805000103002c0e031a115400c1d541010301e407440c1540000d00802002111040b80d8030702241c0140d0060300000201c1041ea01c81c80400c0c0f802c190300001030164600821205070240d071001c1c40c41c0c1d100d07010b0340c0e40c0840322068aa8212a403011080382051030b80c81500ca12042c2401040700d10440008800305450b0107945800c5072143d6404040e00600300c80c000115210303d80342c5240050b014000034a800e0b295447c141e40c2c0c001c010411400060000c0c030824000c2d40060700003800b0280900315004c256460380c0010040650f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 566834118 1250 566832868 566832961
    0x1b06031e24170c030613030f120f0b040f0209011202070f05060a02030a150e060118050d06090b01120201090b03040204060302280e280605030d020a1203090b0a0203 72
    0x50301070040c241010071904d0300203000c5015000c00d2600d5618500039a4041d82c9000344612200c090214510003008079a20301d1203081c040c155002d1000c602d15000004000458801040101195205100c010401e036401000c110a22846030b60045c0d44d415903062030318803021b1032000100076109040c00c00c051492140c000e180510720b440418070003000a1500c01580072842e02645070b007000658000344c91584a41410100b414250340314134011612540411403076140d18a06a9406444403184020080d195900f54014403146020b0789401d175032580001c1a00d1824490103002400220101e400d641da981d100100455009182c0d0031a216000041c0c0c44100d10120b903150a0404004000340322021500e03d03610590114220b46805009150606515031243c02c05058060b44e07402c022071a900c08200b0142d0340407040e0000c040e0b100052030300030340f0030324a1686002014103100c502c0000501203400250030141500c4050307104d645032409288600001c503d1000458003040d420700341e10007000d0032031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 566835368 1250 566834118 566834159
    0x80c07120c14010f0507140607020c0a15080103080a021515040b0d11010f0c12080906090703030215152e0804021c15091b06031e24 58
    0x5801c0140d903800121072144145400c03d000c11500c0c0069103a0f24410b10080c43d070984100300c541c003c00288900107181a400319121030160b40143d80d24940340c5071850401001b000165a103218148507210000c1c003150301807000601d080804118131012900030f012034040100f65008001039490310b200d817920360303062000105002d42e00d070030740f13040c0c1c1810020030b02803d0ba40c110505007a8448240700441e160385007419070b80d0801c80c2d0900c1000008004000d80440c20109580c3d020301070a0081105d42080d0f006003050b8200d80c440c5408200185d00881c1d41540d000c4a041140c54139568038001c400c814901c006040d1340300b0040c200700008140b10211100201d500154440100700c039148050fa800182a10060740c440c0c00c0201d04800d1b500e400d00040521442040c2801920b03219044045c20f4a0040e0402c4a000c0c134120203640074402c0c007115000080099240500c10441240300d10085446800031254400d911018105080070980c0311805034204c62040781c0016079a18414000c014505c42c005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 566836618 1250 566835368 566835383
    0x5010c05031005121e0f03030901020306040e150a0234050f0c01081302042c160e150103061e0302090c0910081e0721020f090409080c0712 61
    0x1040d00d0800e11307408181e96074130200400c61205c020300c4007050064070096641d11441402c03001c88a528052000c2c6014022100015840742080c00401050782d4511000c01c2c00d0343d022403000d03500c40410311102c9400c014030000060366494803240b00b0f0b05030303540802914941940c080e0b6003a540c6240c000305044d180e02a00640e04540b0103100c03140c1c2c03074800420040d4000390342480805c00000f820b044441c0418802040040c055049207008951090402102c112504000d4410083d2003400e11004020844030845a1380c0345050a02038031203414050040d45018024003c1c184643c2d02903403090340074104002c0701000c1000c211030342c0c000184481c0012409a82400086411009000300350750b0b00d904003c012038094100008200c5905100a2510412008200505a28800c05401140a400580c3d50681c0503074014090380d4030f1190304109440001e00c10007490305844244003e0f2035003e4030442e4040780d890b105085c010054050029562610b001328a0700103a0700f10102010980c142c0708a0303d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 566837868 1250 566836618 566836651
    0x50403020a02100212041814070c0b1b030a0b030c0310020706150506091e180a0c0f0503060d030c0606080124050307050d02060c0a080a020c0f0f0907020a05010c0503 73
    0x24102d0311501071030003007100088280030501c81500c0c8507d0038100100d10510010311000c8100c0006880001500d21030082503080b00003009011a0100041e80100c80070322044078501071503000b13100c5110040240c403106030385025210307082d40c05114041d1f074030200a044503148203803400301d40000d41c0840004c89200c0d24040750400f40c03034100903640c0200e031801002507013032047e038000b0b1003508000c41822008030154540d40c4030040d81e420105144941001c1c4031084145015080c1400311401c0b101c1c0f440902c01c44030990111180d0020480340d03c83e10a440f10248290540b40a80c0c40c520303d414002d000c1814007401049000c01503221079a4000004030501540d04070511009240342c0a00903540c02d034026800622240c2440c0840d0000030344054022460404441502804d111108108840002e000106889e885904000361034255204407010800318007102c0000703480118008030140104e0301d0500143c81103009005480b00c149c1c00c07030700a105401110b040140294000c440d0100b2010b1901d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 566839118 1250 566837868 566837899
    0x3091b0311030106060e031c111b010e01030207110f0a12080702010e060a080c0f07020330130306050a110a090f060503091b120a03080613050c0a0c020310050403020a02 74
    0x14098146c00c0000e009811440881015280c0c845a582e1901e000d0064001d0710f6911a84100104000240a240384861030404100010080740341d40303605904050041c0543c4001c1130180005060070002140c400012900e01800302d0491421a8030003260510490007500034000c05000070008140300b603070b460005040c09401c01800340561b01009002074241c100107007d464004c0018220a14502da070107040c540594002490103440da041011244003540040c3c401c0102c950119141da040e6032039180c1880c0c45003182c000194642d02c000f60140e81c0702c6c0085507d00b041b0381c0c0003040700300d860103442c1c0d0b4038400030710080e280745810b05c200d10091085900004c0d078140f00e5802d0381d00070126400985007401c4072801410030480c6021004e540941c001c0441517900000b000f2001c0b545100c7d40728100e00d07180c40010044441200709112210303900b40020414403289003c2110001a11801d01d43d8500c503950000ca407900c0c0040814070741092405087c4000e058000a6944429200300c491503004990170 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 566840368 1250 566839118 566839127
    0x3031b0c05010b0108013221010f06080330010803040608060d03050403030e130509073020090415051305120d0213261c03091b031103010606 62
    0x2403194410841720301c5032071983c6072810282044c500d0614004e50400c0503080300015000510308c101202e00354550580c900110a0038040e114019035640c03010401c0c2c074540500c041c0ca0340300d02d05050000d101e4032111a0b01800040100304085601410301001a6840e105196981da019004d840302040c4a10002030641c54a903440d4079400740d041e0b075400c2c20907186a5003a10b81a0901002a0703002c001c0c41048034158200e4440d5500c1580303003074014100e0500e080883c68910800d0000d40007414116a007a100401c54151600240d40d402070150501d0700d003101000c1718040902c25503940c822500d038107000c00c0c08040250002c0f00d01d40742c0c008000c2c0b070300e81010000b03081e210504000c04580104101c22003131400340028114030135030030318094504869100c100038680c3c4550004242903848048601e04146804405150400050028060981520342c0c1c202800c949010700d03410507849054841c100000f52042403880000810201c100079100d01d08403d60211300d41040340603620341840021043d114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 566841618 1250 566840368 566840371
    0x1120b0c030c0d0b062106040b03070f06181706073c02100504060608070e04081204020a0503010203190e0c0d1101020c030708030a0f05032203031b0c05010b0108 71
    0xb050407490800c04692003405420501411503000c4014080c60000306d01c1034000001520700c001c41030b100c81c40c040007000115a410201c44e8081d034031030030061181001c00700706078003a141603047c801c0301c030b0300c8003c07680c120012245c000d881981000301d030405080f48000f80c080d02500554460480d20950100030010701544000c1003520303440c03011000d003000d0707400f40c41100c07120610340305441c100401903613020700b41d490549007182c0031550703850100b180c0c0300c0621680380038042a95461030306080503120340009001d00d248111400c4607441c01300d41155203a100c040c0c010f1401070300031341d143c1c5000c031100c804c0e00b840c514480c442241440e42a1031115008111140d11140041194811050507200c5410803400410800d06600c16200c00441c540c2e01085802d006054160040d41e40f034042a80007011001322844c00c0742485400e1003408100c0000314005c40440e100c0c0c040d0803034890140e080031409003c008019600e024807040d210708885520560800c06180684002d0214400000045440e00d20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 566842868 1250 566841618 566841631
    0xf030d0b0411070f0206040b070b090706020a0201091a07060c0f08010b2119060b0307020d0203090a061b0b07030e070b180d08040b12040203060f0c092701120b0c03 72
    0x5040208400191044e21020241d9002a21640c1001d0312a00300d661564003410080c0c8024890800b0803003401010030440e0050840b42c8050b200b00c8840c1c0d40080d00b0300006001c1c916881c0f100c50150003007051480183c4805503008841400b1803400781c107000e4030840c8040410400035101a0010070440710070000c55104040704104491070100c0c89001c1e00090001038620f9901e03003012408506101d080e0300400c2c021b0316006071110744e42e0a1250b40640f038081e101390f181c000d5400a1001b01140c0e0340d41c00c402c00c1180d20170b0800386e0754090840c14040701356005c43c10081130540240240014940d0642c0300d0801d550004088604c055221000840345000b0340b03042c0000740e41c0444108006c0e040c041c3c080d01e629841010442e0030a0784401e8252099000940c001006110301010001981b4080003940d404c6a81005c5804103800d08641304941803040401850041d810a0500f02d140344e00a956400407981c4061004910358503020720410380c1c600d04205903240c450b580040b64072603001800f12401000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 566844118 1250 566842868 566842901
    0xa0902030d2309060f04030501020418090b06120a0f0506190608030915300606180f03070305070b031b0f030a0b1201050f10080321040606080f030d0b04 67
    0xca11081c80e08841d80841c5843e030b007104050080c40001a505406800910712840001da251800c11070380208078111a81c80204081c202144036000c140003120b01504404203072080a0307146c03011540d951502468900041c01100380c0c4030100103000001c0790032402041d410304201403000040ca40300b0141d910a01500c0d02e160000c0000422514182c200c41c050f01d200c040700c050070003060400c601c644202c200320300c1c0d018084061100c02600c0110225541c050030031030b0950301380543d44014410064851045500945184c0d50130042913804010a000556200c0111184d4644038004040d07660800d0b034842d0304001e0901051218001e0340000c4e17580c110000c041c998156600d00004002820f20f0079002c94104540b5050b241041c2c400f0300401e4822521500410041e081c040da04d490144010350102005800600030f155800380b240461803208042c0e40003520b03075a1524103050b402020103500401301e40c4036159103410810f0020000d0440b032085403200b0082c094911061005452568002c41c1d80c1c1e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 566845368 1250 566844118 566844167
    0x1c032304050d030c12030209030105160e04090809060d0b030f03161b030b18070602070f05150c060f0a0c0804020f04090c08100b0406090209180912030a0902030d 71
    0x90078950b501d5009540240380000c921151a114020340c07580560080c00080c0d0001148540ca0500740640d03508849460382c00c15080c0048500144002e86007104148515100d0030030b08284181c0c5410b0340c00f41c41c2c0080c0b640e1360f65658800301000520b150714203540a806002c145c000c0c00c50010040d03d040282c03003064100440c2103581c0711030142c152880c03400f101d03102c21100440410220362201d80700700140030021000060040308070389041615404442154441a801e21035000070b504a101160320036505a440c010384e040d035480103030060a45507820b600c40c100400c011035284880c510b00445510341c081184500141e011142601c04440281d005040c40c0362808241c14650311021480d13000d00d01c9814000d4072100840c1c01d0200d82281e400a4945800c1a161545403d00c126402000001c50440c0b50001400120304002c21480030840001d00c00000201041d109206000d080600c2600c047c0e56850441c2024008022416059001e4402c02d821450f12a0007010003041c19401c00c284407021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 566846618 1250 566845368 566845379
    0x3020d1e120905030c100f031802062d0c0319020f010903180801020c070b07050f0a03030f06050105120a1d0f060108190c0e04020f1c032304 62
    0x1545004054840e0030111069860108000714011080d54401c1e65036103091900d044101840c02c0d03040001e851003a1503c5660421154000800240401c0c4500380801c03a0700c50100d601220760701d4540d029400000004100750809080ca02c480348200c1c0c410341e0100d102c1155512a41280a0006041c3d20b03580204600c01c00400c5044200c099803000c1d01c100c1b1030b128901e40b0081c3c2500c1d8507078011008a00700c41047c41c00e60030068003100117800d00500850038074803075110540c0ea40100c7d202e0441c2c401c0002551105114041c400c513113960b681d05040b640321042a01d0f000700184038100415008a141002c00700c0d540d845607080319290000703180500101d4582c1c18608000389454100c0c001d01c1c44401c00104603140342030108900c00303814034028003d035601d403590840c1450901c0040c0c0c04642ca189540b20005a4245110016104c0300c5050618641d01d0b8401b09809840f6502d400d0740c40410501000c412404007406040024460b90b51070910a0745e0110142c000381e1000c0111040c0d04e03091006119 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 566847868 1250 566846618 566846633
    0x212030103081323030d030c091404020c0f0709110702060d0e160b070c080d080f090115260303130212120a05070308010b0f030103142803031503020d 66
    0x41140900301c5010255542e00388042440400440000030b9403070f132a2200b203071a00b4040d08540001d24101400a00780401004100c0c00c05809030444250207426141841e4482d40c0c1624a82401142120361060314101c402d6580d003242e00c54501c107a030400901480e120001400d4810f100d038050000d43c200811200c0850280c1842062408644285e0000004c10311031581c2a000500b41000c00caa0b80340384900f07000b445003405030001100c076882018103015217a4014003480d80481c520b400d82c1515107681000c1e0340900f601d0100c400c4d01d01d040c2d110104405100e038000c480c0c4055200800001c5458480c0e1154480c04105c0340400d61981148002d005820710791016648032610720169600a0040102c00c030303154111a9514002072804a1200b0403d40c000102901401c400c2d08880d0030900554005600b52205010050104244130301d90b400b03c06041141050002c07a002e541e2031552480040041e290745000d400707500003403d10b100c4000d080c40000301e52054a40180540c1500e003202c0d00e4088 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 566849118 1250 566847868 566847877
    0x305040212030f04031712041b120305120a0e1b030c09010308120a09020f1002010e060a0e15060307030b07020a0615050a051e10020c06030108060a0606021203010308 73
    0x260800c00d041c0030552111801c1c0014000d038440080842d8946085041c6030080076031662800c0c80c802404c0103070010040c04c1c091480d5209511582c0c011320481c180c030000c61031020ba5440104151510302c01d0008140e0450098a0100100001040b040d03440207080300a80d40410726441c1140c11000071640b0480f90120840900c03130000e421524480041000b181c1e044500b41d0056030000400300d100e50340703917040c100c44ce038104031002414810406103800241d9900d81240d103041c8a0124003419030403a40c000c0d00a4203100340d440c020741e00140380018203000545507100005009010b0441210100d01111076454066400134000344419425070b524042d403002c014190405500c180b8042200280351030103040342e1607035682146a2070510300814440e41d001d690700418030503011400c100c40b1182061607e2a80944122803c1482c0710346101d041c0d09045040321441c1c2c0010001001003106000010b290b40a00c186190410506964500c100d842e40f000e0009820030300410001000407840d80e10180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 566850368 1250 566849118 566849123
    0xb0d0c26040b2d010302040c0915050304020d0b0411030c04110313030e06041508070f210b030d0801080d081603020a02160e07140903070501050705012304050c03011b030504 76
    0x2c41480c403070002814180c1c1500c2c1056400d883c03500c0c006100f1424070307002c0c8245150312410408031441c24031498082c000d00792a0302c61704203c0302100080641d6100c901c0443c0b869040503d003160703410729090801d4000704445046011303100d1540080b01506040c40f03404041007600c0d10050554441c01d24503035441e07002c80c500340c0400c1000b59550120350388080c02800181001c4a00006100300c000c00940500030081209080c44034461400707006581201942800000440b401640149480341900041007207140c225014480c408100c8d41c503c2c0c0010440b4141d404510880c0e205101d110400ca950200c2140d0b09108030801c0700031341240c0740c000d40103403400e68914010781d20a0000781c5005038070f8000c160300070f40c00e900708803051140168001e00280e51030425010101e19060b4050042540c07050035102e958104a000106035040c082c003948080c00d0908c4068100015001c03039110700352441300980d030590312401969200c20440c6014418031031740c0c2ca844d03111540c0007803030600140d0080c600140300307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 566851618 1250 566850368 566850391
    0x15050406050c071e0e070e0901030210110607231e0a0c050607081503070f121a1303090b07022b060501030818010203070b041b0b0d0c26040b 62
    0x31030301c000c0301c00208209800039400120b1340c03442c080150203582c01c060f0022007440101c0048503203541303039030320141c1c1525019a200441038982d403004030b5613154a001c07101c0e028094241409075a03640070101408100c105e11280005902250010841e44202d0300c500c0d580c411042c0100141c141d044025040062a90800c00c500780c0480c1c54250600c5411034440c0c00047c3c41c3c104201c02c2c802010303240d0340510002e0780100f0700e42e0308013071100010403020300a0144990740c4082c0300c000c114607074503007880480d4460661000fa0615181c402030000c890b81084000c10744c600c6c00418907904a10039142e510703800034000280390600503000c1e5210754030703601c0f01d90605000000003000b00750035004050080d84506820ba5031081c18200201000d070403221003904640040018402080b50744914540058101202c00c250240b032000c102c0c184400795000101c4d802d000700d20580d44020319800381c100e850458486104070301da40f130a01580c10040203150044000240e0100d004241c10700340b0a60f00c144845078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 566852868 1250 566851618 566851633
    0x503060601200f0109031d0f01121815050912030c030c090d1a130b0c030c04030c0b090118150e041113080f0105010f1203050706020c150115050406050c 67
    0xc9090a1802040d082c3e241a03440c1c41580c020103501c00030401c1c00c002c0e00140109040300b40c00016150030380300b0150a041240082050300d0614080d07024568140342c0e0300001009a035240361502c00d1038800403c00c040d2030f00d060b0004903c0c0e01c02098031002842d585e180320703183d40d940a9816440c1d4001800490303d040040c0524140350301c1c0d03040d201402c0380c0501f14800c02c51003900c03070581140900520444d412116115048002140c800100d07800a50f0f61180f607859944c1c007800c900341750046a20207040b200e0b94080014032016010000c1104203404c1e603d541e548440f4560b070840038101841580445055502c0c0c0804241c802c0548100c3c0760340081c404156500c0b0255610610780004e40804d4941c40c4000c802c0211076400c00080e10201c0c6801c00900040d07151412610000107a0b1040c51100f803024661b05013018032400c00c43d03c40d03503070199085441c8c00b90f10344903ea480a00050202c0f2102c2d030a40003041d001200240d111070b10481d030792124034281c1410b0f01120242c02040600880f0b00c55a407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 566854118 1250 566852868 566852927
    0xc07150501170609010b06070303091e0f0303060522050423030a02070e0610180509011410020c0a0b0901050d05070302071a100b030c220501090e010503060601 70
    0x20300c900910184009040000c00080700608000000c1c21a02942e03140403480070183e100c440135145c00301e415090002d001a5513042005a0301c884d800e2400e07071202820020170030084402d01640001c1e000c0d540800000351a401441110645440420404001190341e2100c102d072907005140c3c010703c1007256610070b0034548200d10016005240540c803582010801c0c100c01b503030401c080320080c0762011a800542c103042010071362240c4201d19036010011612070740d02902d00200b8091000b090b010b09602031035039446c590700908012110160748118060815821481d10003e91125094801041d0f041e8191a2243c50810b41d80007594617810300c2400d00600c002e0291510074284034880603100941c2d40d0301c007072406a0030444100307000c90f02e103000101448840c11581e4000300c03c1c0d95169281070b5032501c410719040910b0240c5044829031468a0a40c405010174507910181101c0c401e0701c0e100e407a01d403030700360f4000882407d00685405500610001e2043c3d031188101814804104000da00b0f03a54045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 566855368 1250 566854118 566854121
    0x109020a021905010e1207110603040f0b2d1e07030b03011e0b0a14040b130c110d050a02120304060b030a11090c09010804020d060605032b0905090c0715 67
    0x1444140c81c0b5940d2468001c0542c13105210b030307913620441120070619008103656010710703c441c08d4491318014100400014100410309040030079007600110b1035203092400c00100540c00c045401c0303051403a82003445110554002030f4035603000f01c61800004070059202416070041440040122041545400c6203104a44080c41460b03042280042d4034500f000c5501141016501144a9203000344c501ea0010400c0e40f01151643c1d4880c10b0446010a803911b480740050205401c200c910040240380c0002c078101660440c040507900184034094a485800d44001a034540c01411810740150b00701203180301c002c03540319004581c054403401c0b000841848030f9010030320b082e20003201191480d1800e0321444ca5845c0800c0300c02d41c0300c080300d641c561804213520002046240c4c00303880203014079840070300d21040046070740200f03025000140454a9031203a0105081c0515107845e09407500d0034240042c8032815109801140076100e019224031455101c0c0d085203401c1d40c0c84050141e5141031075504030740084005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 566856618 1250 566855368 566855413
    0xb010f0210050406150f15020d170411061602030c1507020103150902040b030106020105061c0209151914030703030e0108040804030c180c0e01020714030106030501050901090302100b06030109020a02 87
    0x60031001142500349000f501e226030410f00300b8029035001210000d085984006561290f060201d00c2d0141600c5a10b01900305101c1381078cc8603401700c0d011828055010b1014000816036008400700d4102441100c2030104404805000c108096810410030000d5402a004a140c0040203003c0d9803800d9034130701403801281c119802041c0400c4001004020181d82405401d0b040350086030f0200410a1200f02c01e0040003800c800203000b0711995001403600d280480c81c07006103a001800900d201c002501c8092188a1075005030203100380507011400c0e240c10b00264550a481d4962500c481030416980103513640c40c0c0040084500030400c01c00440052000042c40000300580031000913000180c484140907648400f11361010407221003040f5140c0da0b03002401e0400c84114003520724010a159001c43d01411240d080540158200424070550185c152b0040700450b02950940e041c04009000000c10b4400b60781031640d1258080c8010700c406c80382070340104660500d500495414030014504138168100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 566857868 1250 566856618 566856629
    0x1110303040f17030609070e010e1026090709050c07060f050f06030109110616140a110a1503020307110d020c0907020c01020307080f0c0610090b010f021005040615 72
    0x10b02c0b4400400c2102c1210040384600e00343c440d2900b5481c0080209912400c010700000030400f13101d10251440e40200403005501d10080c05e865501f00c7c1070b540280c540046807400e040c07020058075070030440205d201100b80c0140b0050014010f003900d016100806410080c1c03801c07403c3c0304200302d41c4000610510603501c040400311000305480c41c2510780380341403000060406001340d046c03640100c00600788441c4054078074070481d1802e488840990107080740d495000001003440b0510b080d000b25282000070001c1c0040d00c903c40d0000801d010764244960440c00384107400380005110081d01e02e05001e600655880f1400349004004644001003e0380f030f1107500224400580c0005103110107500b05810090781c44416400101400500c03040002d54900c68034a024008a0001c81c00b6803100c60404219118a03036204100d4400d81414890301407080b0300740c410f04091500e421003c0c03065500a0100c88060240d50b0041c06011001c02d00c00006400300400860b58959209100c0c01c22241c9412008080d10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 566859118 1250 566857868 566857883
    0x51b01111603021c170712020c010b0a0902040e070309020d0b0c03060306070908070e100f080f011a0913060b0406381905040503011b0e10080c090111030304 69
    0x207042c1006800c0c6120740800708240c06514440f001c1c19a040701803280c1e801070725050307014075036500345e001c131140c242807024100d680c1d000003856542d1000541000c04d0518044aa0344801940e9054a800b240305d540b0071210a00e03455000129071500940c0845900f80c00a04000c0c0c20329110f0307590002d8410101c0c1d400b48542004001d00925040070400c0541c4840d150030304420300780c10301c28242e5139a8100d22074822204100340004269441d034403844002040007881e25000180ca03602c0d00f039210703a002c407410945907107002001c00c042040000208007000c00a05070705c8641c1c1700d0160503000c00307002160a031120b50312560240080e89030f0340706130001803503188030115001c55408403030b103140e080703030018a072a03030340e101300040d1035152604200c41080d00e0480d09003100505841081d01c05020b6944076079810b501e04040703503000005a408810f9030500542da80501c401c3c00d08104a010f90301e8841a000081d1202c000802d92140f40d0002c00702c4a5050600d031040c5540744580b13600d15402100e0880f00308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 566860368 1250 566859118 566859157
    0x803070c2303102310140114030901050103050d0f12050405010b130c110102030c0f07050a05011109181b09030a0c14090c0403030806010302070f0209090604050d0906051b0111 77
    0xb2881400060135032610b40186460f0750902c501d0000d9201d2040c019007200110700c080604142e070003502128400c40c0ca0000407500c03445c24a403168000d00c403d00c01600c0318090009400100c40c401c6050101111040e16200000c405184082d8003c0c100104215040c0d96a0000c400583d5100c03c465440707080c03103c40100d400368001d200100b1000e520501e03456a070f0b0050080c01030290403242500c901010301a1502c1c1c48041d0f03410701c54600101d608029119502c4c103064284900710400052000050a0f91a0741501410b80760b41128850111815100f940780c0501400c45150310f0302c000c2041d600014103c82406100d84c640c0b075907160710b5900001a2400c207035041d15050600c0513140b980060414030550805165807006880180d00604940c105980080c8601c10401042000500c4a401070050142d526206248654032181602c090703d2170320400b41c11514032b40c0300d1501001903c680d55605824030905000d00c4c41070441c1c902d21103000c0d548490101c20300305a007001601c52940d0148001404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 566861618 1250 566860368 566860391
    0x3140601150509030a0206070c120602031b0c210c071e0501031803030504210302070506090105060f0105130b13090608240a09081801090803070c230310 67
    0x2564181a507000030300c00309220401c0a61341c080341c00349507643c041e20702a981c3c80345d9144c00380218520703405c24180171a01284000a002030381c2c0c0654890082c401d04455500e1801503004040d004000c01519690300148608880b0042e07030514000c5a1181074004d03041c803428034401808e0100e9034101180c0454211121014040a0744010001b45000c2c01e08214043c00801d100640c00071000c005014507440d18007250411245400a00c02408007030600c81c00030451000050182d84440000e07211449884003107000c00c08184038540c00741000820b0803c03900c0c8100010741d82c5030080550000f01030798602c4001064805400100b880145200c001070100c0d0408041008460f501e41000055900910b264410351400c0841515100e10395501031a990343d40d041c0e001d01400340008018003000c0041003854103010199550410310000362030700181551107940d07180d5603014020300a01448005c40c0100502c1c00308a41c02c503c4100821b96001110140102081c42d00080b40c4100041d550f481420000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 566862868 1250 566861618 566861639
    0x4050418120e031603031e110307080a080604051510020304051504050306070306050f01030b060c0d0e12010506030a080307020a0803130b06030c01090b09040605090c032d071803140601 81
    0x307044c4140c580c0d00e80e060460f140241445070720540b0000b0542011100d02c0c04031b0046e000081c00c081098101c0b40d8803400381c58040c1c86604858178203804582164003140c805e14081c01245d2044141146080500703000d1000c10508861003104041940403c000100355038403039076500c03061801071540b040e544074900018180b4080c0001c2c0104205840d1090a00803039550307005002200c0c0003440c0214840e462000051640d2080b01000d68840c8a50b0015034000d6402201030f5488910807a02410b14114141c021426a00e044a000790701d0b0b0405454800001c10080103190420818411504d00701480e6a03407030f015604c01c0c3c0b040a14501002000fa003002007510700168000c40550280001000e248000b804440135802400c0c07a030940411100140d0722298044c0300108001440e034130b9903042c25a0740c0d16242c1e0090f90b5a003040012a090280b0b20700c00c1004030003600d4000500708502d1b95030b602d07044a5200c0c211542c1a004000c141c400400716125140c41c8180d411600041d00c038551503c3e04032038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 566864118 1250 566862868 566862883
    0x50603100501022802010e0114030f0403020f0102040b0702061e04081015051f030213090b13020703050414010504120506161404030308090a060603030f021b0604050418120e03 77
    0x6400032405134800c0003900210151a1690a0a003000d0410b0128016600c621030b0200061420350003004000c1c1c803100140d2014015400b98096514000c03104a01d142030b48118002e80685810070884440107080213401010a034038026028003841440507d98001070b407007580807074040d60104440c2c5a48102511525206111154150400924040104142040340041c030340140a06402c83d5031035a0180e0119001e00c004065007445040e200d10308030000f0001c054032280140018080000d80b61111310860b00d40c950140ca41e5410b0500d0051900c20301908400900d04201c000d11001441d811880e402140d000d1141001c1d011619040302c10710042d00080b02c4102c10824080d1101801100030000c407000e03260907160200295550381c520fa0703e000c203810801002d43d0710f000c80c00424954440060b9034202c0842c1e09840844200761000010010781803003450380f003001000100140d02d041e07441984010308902290101040f60785901c06242e81c0b1800d00404240e05801302110303845e0500010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 566865368 1250 566864118 566864143
    0x41104090309050d0510050c0d1b050712030e0709060e1308030604090f14010212010608070207120620090109121a07020a0f0606050a1706040303021305060310050102 73
    0x104680559610002c0442d903040c0f10b26402101600a0b8030280322043c40260219056084180260304012802040992148141c220310764504a001505503140c0d100b8911034404070340c0c136113003050710380d884810718200681c85601c14199500c2c40307001b4491040c0045801061100000120a403810102d4800d170384004000302000300d002c4100c90300040340c4000750f9811147c1aa40062440d80300d14103a0f2101c800040054154000207611481c8440d0540080c14150b80c540c01075490359a840c082070710306480a40314000941c000720703414070498034600102043c140c050440412008164140110346000e0303801c0605040d000050302d0320301540c00c400300074001c05a513910400c0b80c40c4651030710302c048202c802d101c0303542503c541c001c501c040b8400c216020070203801101890810b05117241c42c1e4001c0030f80707201e0b8501444001000150285ca10881a140044214040c103d039590325917080300250b001007003050304401003146c0400d0340c0d2621000f441c8100313852815003084a0400001928040201415 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 566866618 1250 566865368 566865371
    0x3070c0b10031e020d06050c0f12091c090612020d0f06061d090129030907050a140102030304151d06010806010b07080414011e0c0b07050a02210f070506041104 70
    0x5a40040e00c40106458005e500300d00001850b40b52001d803440e46100d00e4800c44000440401d44480c40e0030100001c4d03004150b1441110001e001e13000f10b03070740142d01900104d0041861404104607213030250085e031140044480c40140b40c0a111404103040f00c0910540404840e5104030511483d9004040707110b4510014014483c0060038a0020700124014003400304d03c0d4100e514103d01042c5a5801c1400c601420106580c40e840e02c00d007034a40d03c001c0382c440c81c0e1103050a80c20014440b445680102e00103c01070b4017551031503a49881c0d42001a040795106203a50b542d5056407010102d985c038000707800c410100080c0003e540340c2074855282580681080c1c0d4041d20400c0404000f400b002e084404607a00103005020040c840703401615583d28482c61481100320041d40115401c5d80700f6403a602c005c0c070801000a07a03032605482100c6c01e004840e8408003603440018075080c44910200303400d080041009c2800e2910045110010071600445800c81d4140c0c000380c10300040200003100c0316880b541c183c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 566867868 1250 566866618 566866673
    0x5150705060c0f0a0e0d02180406060b07030e011d0a06031d031315030209060f0301091404120e030a020307080115090b1518041406010e09090604020603070c0b1003 72
    0x60300303c2e491003152040740a00c0010003266001d0f4030744800c4c09808580007002c1d9240f0342d0307030851440000c55088504030340c00d0f0710b400e00c0440ca0013040c030142c807007554040c2c0c0c86820f075280c030704c0c0107550f2000e14400c585a880c1e94640d0040003a5a80e100220182c80140c2d004900d0b00d1910101c0419003901d0844441035400c2070010454a1000e244807a0448a08941603001c908070f141c03040d0001d00c00c002c5e065030444c400084880c4100745400c000e5048070f011041c00c0100c6400000d40e15087d0305d007501c006008005404940001c1031050301c6420035040d00030155080f02030380e40d0009107060069846030000340d444500703503030840300700d500071100038040702c1000e00050300f00300001a032041141c4541540d54001007101c408120310168402c034554000b8104100c2c8445103188801c0006045034258001200d0944039200ca05002800c0c50192103a40002d15558440d41d08000b40c642001f0069020014095942e10208000c00d030304500814014403207101c40760a42c2403c036240ca40c51020000c41417000304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 566869118 1250 566867868 566867887
    0x50705090a0824042a0f0b030402010e1311071101110d121a04022b0605032137090b1605030c030a02011a0f030a0f050705150705060c 59
    0x1000f440c5031445440c9072541542e10351804a0384140143e013200990349007201c0802201c44080090b03400c2c2c0c0c146040c9802c1e410b03600c3d100b03422244400c5a0090028003071081c401c50b20308001403800d4900749007540101c5e030303548403030304400c030541100000351a1003a02558840d010758010092440b182444005400041580000500588130302c43d4080c1c480d60391600118070b20451a9010104108000c20541d40da000b001c0094501001d200010b00311605c0b6a8001c0c0b00e0007019101e40c04c1140c2029015240c5003542c48105e44802a95552030703640f02c0d008001e0207220403000320306180307003907c111500c421a003480c00d010207034003403445480824420744000c01e1111650b2041030711004c2c0c07010b603540c2c100c0681c9850501d0460007051a81800f070300c408510080c5080d010b41081c02070101c00803414000503950410032401c0000002980d030541c205d1002940880c44184003245000d01400403104055520000b14120a042c8042601d01500c0418404100305050003a59007028100bc0014140030110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 566870368 1250 566869118 566869153
    0x20d0209040f06080d0815131a01020105011a090d02090103120210020721120c0e0f1e060d020705031605100c080105010507230f210a0c06090204050705090a08 70
    0x810704c1d40906c00d0034800607001c1e040402035100c1503500034000079606607060140d407018001c0c6009030700302c00100c10511082940705120b881c0c122414130b4200009030038000c048241c036a102c0716040c1e402040c8800c04e40056222420303400d000750700c9002d452000000441d03000382040c28840d200340105004210500129011103d0309440c10088d0355000c1e001c501c800020303641e4103c41c0240c02005403d008904910742d400c070401c50342c42001680c070810068040020048039100516141071700c1038a41501d04000d0526401900d41460b14210051925400b92103261868210420362810303a074030340000200b0080140112210329003116414080078040c5400079210100500038a81049004500c20050105182c002241c00900c091202d400e030202c90032140d111081c40110412074072801441c484c071803120181180c80b00444226050030010003141c01c90390350903541416500c00f500c6801d00030240e039a030312419020b4012602c42c5aa03624035101840070010442d0b10500d45500610044208540c44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 566871618 1250 566870368 566870383
    0x3712031e09050a0e0910050421090b030c0f0c030d0f110306030601060503090307150e121c1d0607171f0308070206190806031528020904020d0209040f0608 68
    0x54012220a981c92600ca60328190590903c0106282000103200620800301000706441306a0000c0c1ca01c1c0c5810f0303c50a5400401707602c00e481360b084003080082c0c0c00303701c140d0141140038100c1c40c10900c0d0240a40ec2c103403850308115005030199070741c4e0303400d41c2031311200b489841c0054111000341030840c41e20300c0003e81c0f140c0f0305100e07180c14084004001000d6040034421502d1503544040030075000304d2002000340042094040c841070511806c00c0d070802c5410000152001d00a002c20b0ba083d2800340c0d8981d00c8007a0001c40e2100c1d08115030705400242a00d01030140620a080954880303501c009449a4010074000c041d00030722040b021042c0145521035401d0614080e00d80000300c0c56507a074000d2001c60001d00c5140c00f02c420a0a4401c4181c00003540311615501a100480441d00d90b4104410b91040032841502e4102c90740481e90341441640c00010800c00845948040044c20820082c0200d07042ea030184803401785055000800e1000f07840d1511800e690342042c42c2c0c007001a1070400c41c4050780c43c0078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 566872868 1250 566871618 566871629
    0x30c0509090402240d061403060112020607020a03060c23041e0806040c0303030e060f0402130f0f090311010b010206042004061508063712031e09050a 66
    0x20000000c0a54440c2e040395004801d40c013a88010b00c06148071402d6858200070003c0011600300040042c07800c0114100000400c1c000b8041c05040c0d10b040c000419240780041c080b60801000d0245c039003da510300420b42c004500030b402c003050305000d4a500a1035251540c5007a604220031045003e52540307868140e40c15078144122025460142c04000425940d50f50300c03403d110b02c6200200720412100c1020201240e01c6520244034100c0b0b0701d044180c42e0403007102e03006000c8407584002000340c902a0401c0041c0031907504000341c1000b00080c50320a46079501c90304403016880e0071185040660103201b2a02c070b1811301001708011445240002e45601c40a4005001456140f10500d0b40000e841a03140c81250b000b002000072aa6825086e07052014907040c99000c654030800180440c200003094248a0b00c00070b11301030210207101d16188240a0f100d060090728038084001084040180349101d801c07074005d407226010103802040c00100c4206400d201800c0018101c001c00481e103d85c8a681c0c241d45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 566874118 1250 566872868 566872879
    0x510031203150b0a0309051203010e13080c01050f01140607081e1308210a12020a0203040905130c15090504090f0b07110d0c020906040203270102030115030c0509 71
    0x15186031003858a0100c0c2c0c0100642010001d031030850304c4e40583c40950f40a10034000e94801c0310340c111800320940070034272481d107510003a10002541c50b04401800000107125400043c204010b03491481d0031500c044522605a0380700c40e00600482100165620450000b00c4502d807600050340d0340c1c2c1082e8091080a00d603031002040c244c2100c400140192400216001c224047e0300d607841c16210381c3da030030300044001f0b14801f41e001003101050740c4040f02d014482d6600e0300c0b80d43d0091202084000c1d80074004c00e0f021404140301c08a034146103400b406020b103080410062400c00c2c1818030501140e50b46e440000c0702130440020019058000350400300320b4a040ba0300084101e00360401020303a510801c401054085048100400160041d4140340d14000a20444100d58202030041d0f0b140441720030041e42c014150300000710103162640045501804910342c03000900c000e0041c0e101d20301040d0f41003c1d11340e500400140611704082d02c04001c0580c1c545070901210446c540d014015110300c07101c00d030148 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 566875368 1250 566874118 566874131
    0xe03030702010e0411040513021305010c02090f0601110d35040b0403140d0f1a011713061119080105060909101a280801051314070504090510031203 65
    0xc945c00c100b603400074100509003405a5000342c409900952050b0f6516210414040c4042200d5100ea03d00a491680c050803c41702d9484403a62002d00a0300101141e042102b00700c0e6504191405004041600311940c542d588030411450100004420301c4030708a000c8100c408154a04104951020341c10036008810814103480364141258200c01038004503a14000001d2513031500e00340c0c0e0348071071001e0006000c104120000004001440028a45400c2c0010140342000001074406000190007400d070307951103031801d0a02e90b02c20050f41c0c11009604035142001c20b10b48100280c540a400100100e440c02480d20340c182400030b04613002c0e000140d07014641c000300103040c41d4072055503140a41801d034003401a0445081c1035080d40c0d440f09610703191220100c40c1203000b510f10101c1800001e0240c0d110008180e007020240040b0400d10300003e10250303100c2d80380c0880c02202962450140700315a03142903469003000d41d00410b50300c0c094030484101e5040b00007040807500211a501c00f50703e6a29020640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 566876618 1250 566875368 566875391
    0x1104122a1701321e01051e100305060109080604080304060c0e03070e010501091406090105130b0a1e080906040210020a0203030301090501090b0a031101120617010c0e03030702010e04 80
    0x14080d01d90481002c01e01010000050744208000781c030320f880c5500302d41910b0380d50300188100400014844281c11000000184490700d840c28078480701c41141300ca521005a824000540e04000035041d60000c0b0369280305002483d603002043d04041c1107450000c01c2603003803640d0303022460310000b803000e010311365903a240ba050355210301002c1d24440801000c44149a40707400007130800385028030845021a00001c1c00065000303240e4403000807a02c0092001e07040103208801566242e10280c80120488050701010030f107840c0001c0580800201c55030b4840a41c801c802c801c0400e400740c80c1d040303401d11000204103c080034000489a5000e5410b4034081c113031449000b002d074901458400002d600d4080400081030070031080e8046070484002c030805000404131501400320302441c50001a00902524000103000c0d405200340c0c40c4040001d07400054070656900307003d102d9550202122016035101ca590055480d8081201c03507010b01c00303c6c05140303840059400684200c00e07840c502030099480d00e020246 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 566877868 1250 566876618 566876621
    0x101e05040b120313090516090e0601031e02091c0b180304090e03030a1a030d0c08090d030c05010b01030b01050405042c0609060f0112080d1104122a1701 67
    0x144201032001c5903201c51100c0c01e4598000d80601556170901e2400c0c00152041e041c0e2145049446074984404211500f002941c4c40c103104010403850502d0384071840034131030304a80d2042d03e0301420080c10050315150950708120908880500c40303804940300ba40b540713001c6000641c3c81604105150603034412460b0440915045010f1a40801c03002480c0c1240034200000110045205a20500e4100440c401003000d40403900424448107802d07a002b414070301c45c0540120604e82d466802a030045003400c40f264000b610b803400b10038048002038046500102004401d02800c04000002d080a1140c03d05a100081940c0224401e135440789803030301140103000c0e140d1300349085d411003000c0402090000c0722032901e507100303020341d241040c912600c40002d90840042c095079060f28025410300c03c843c910f5032079410032600041003401420b5075a20100100400e40c00003840186043d14540482c41c582d401e00c50b503242040812002031007503014010383e1440c558000d4806841800182c0200e03800303490051030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 566879118 1250 566877868 566877889
    0x9020a120203090d180b0702090a06050d080702040f0e190303060b030c090306070e06070b040204240f080307050d081b0304060203060907030c0c030f02031e03101e05040b 75
    0xc0041c400014000c14140c0441d200c02da50310181c9564030322090b030110b00c1d60300d200d40303204040b840343e03007030181c08010710f030030145039800c0125100003090054440000402c05041030108031000c540001c6d9070700441c00d080c05850090604054100244117215141645580901e01c00543e001032500b081401c243c080da2041001d4040c0014190f101c0c03801005010304c6078000d24806220384216000120007a02c106440c4803a444094420b5040c2101e81d91014410080640300326401501c42c030740e0500b4500d140084c00d0311404840110b5242e1850541c0409a25400d80c0182c0c0c800d420410003000484d10000700390395441c029140c604400d507569841d0641c10111204001d00040c000003e11050000c541c002d14040e107012076094078184c4400d07106400b1140510b24000214107040b1036840428000c105003100c6607203e0041d20326200c0181c2000c4400c041d0754011248038100032082c00114031014040e030020701100c1c030824824403c60040c0462100e0144a19889141c440003421019221802101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 566880368 1250 566879118 566879147
    0x30c120703050f2103010317030a1103090114010f06140c1623041a0d020109180905010c0509130c05090d03020a060f0b10120212100e010e04030909020a 67
    0xe03608100c542a2007511013901983d20b02c03020811132490889200700700e0860f4100c1758030100405000c041a60400866040180384000e200e40c1da81d074018440c1003e0000754498140310780000390414616009084005043c0c02420000c411080148686904036201185d082c025007030680c0c880410b0440c4604c0c10516000c500c040781e054440000d101100c165809960101503035000e05210010700c1880112000c440318040c10f5228503d140e01d0390f0400e800c2c5004070900600d0003204140c1c0702c580f56070300c0c1400001c6140c070041c0e90b04100f02c18440f081c403425100d081d00c0e2600074941130b225800281e0b5074200702048103105070b4031034613403044a010744101d0b1040c11b0007030641d008600c42400c003c0d4507080c00c004152511420b00342e104504150911580d454040d00070074601141c02581801c0b54018418140d41c0a141d608200c1c001c07a80300c40031000e610508220145d0351000d402d2125000e9507080c1a1320000c00e1854410600c400250020900c07019225101ca00603120a40707020704071548030150096 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 566881618 1250 566880368 566880373
    0x50a0b0406080307060e0c0f1210051e060f0f01050c070503120a08070228020a091a010f02030a05070f0807120306080f0a021807120507051215030c12070305 69
    0x42c0d01c2d040480074221540c007402c41001101c00664015480e0f103003100312580d2201100c80002d1640c40c101c643c10900b00006401c0715500041c9240031000c071482525030451620440c0b20b035015a41480c1711456000509403120034558400701c01003010b007a8680e4071103040c0040820f441b000c000b02004400014030380201140d068022490310141c081d4000c4100702c002520f01c400048840380006012014019006440c1035050380d01e5440c0c1e41c6468001c04200c2e03020313916040000c0d901208d40152281c1d0101c0446103030b509d00b10807002500c910075281200040d034105014850003a40c011055500507908803c00035803120759850203110502c1003410003080220444131481d1101d5050788040c0c04e90712110100e450800703211103240c0e540c48002400079840004429601d82d0440b040c1040d640104140c1040c00100f00e41e52103170402c1c4c0d4401c2310b5650010790049412042a2504034041d134009051002d405146c4038410086a181c42c20b440105003e20b5032189a0f10710074904002440086030400203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 566882868 1250 566881618 566881631
    0x7060b121f1404030206010b0c0312090d0215070c0b0c0702031516020a05060a0c0c02030304140f01050301050603180c060c0c0f040203101719030c0c1e09050a0b04 72
    0xc4580c528514042515001880d150034000d0360304509403583c0c000e94254005007990f07860440500a50ba00c646800100ea00043c01200340c0c04440c0d0001c180255001d4005e045a004c030540001d1611140e48901c18000c281f4006004100b80c100000c46003880c0c02042403520b503a100c054500051150440094041c8660348102040316044213010b4040c0c1d100781000c42400150a0040b82e4555000364060060b0b009100441c00400440d40300000350a29410700c0f4100c4c00e0740d40c0000342982c102d58410040100351021079807062510500914440209081090442d410000890078030f0000401c6111603400000305044820002c01840e544c5103802810582e80300300505d18662110346003218180510722045c59035071203281c00c0c002e6a104031754040000c51180c2c6046064100d2060f05842c140d0140506041c03544041c06070b84900007054040e4a40c6640c400440ca88490b4504155004043ea00d4102c5400305c44c01204030414011140d03240c034041034913100c480e20080207000a8080030f078810b01e01170 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 566884118 1250 566882868 566882893
    0x2070b0d0504020a05090717090106030c030503070c0605070305090603060f0603010807050a0b2115181501090515070201030f0203010303030c17010302150c030d05010803040f14030307060b12 84
    0x1c114910a51003035911040702030f50f82c0280428004107446880220b801a800e2881ca045008801540002d1100c004035001303a9989818003400c1507500181c0c0c064000141c0039060082080449000b00b020346411031a200e02901c0040c0240118925a0b20030000000171484c59520359601d07480c0010010201a66941d445c0c0780355607265031904c03030b05025040c0b8200004402d07021005407020400e0910700d40d54404174004c030645084000030407080c8403000c104801c1d1581d807101604544034800960a02d0301904240301e0300400d0203260700d149410820710310401d10032911203410342d140c840b407020407450b1501d0452005034087d090610403080041c3c8040000424180c0c1500708030750510f1180c9a074002780d20160001500c044003400040d41000c8030520798050004560002c108940f8a54245c9040012403807010040d10310a070301c07606d60b5a0010509000a000c1114004000c004415400d55002d1420000c00e03281c3c095001d014002981d00d441820345603d50396003240c0c2511403078055880c000501c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 566885368 1250 566884118 566884121
    0xd0b031c0e0105091e1c0807061103040f0602032a070c050604030c0501081b0d060510090617070c17210103080304150b100e030d030216060b0102070b0d 67
    0x844032600014018400341d03030194050811965080c8015100100c88028880d40d04140c880006050380c10941d0710501d1400c411800c0c0254044c1440b80b01c0183d45c420007824860140c80100802c60b82c402010014440060340754800390354040c7c1e01c80d60142c0c8036520784100c030b88103409828420b8520b0310030100800c144511180101341a03481000510b03c5075407944240718a0f4042c501000380b208440107010b2100e580280c42d5207512040746516050581c0e2024294421a00641c10010321107031541c00c1840130703240811064441c2607061030440c04c030500d0004004c00b684540c0240800c81214803010512040c072400b4000715654002d1041c41c9241000e01c2c440ba019800703400c9071b9080350b800c0d081c1b2050190358610000d040701e4000301102e0640d21951500c0008005401160b04d15079035484240080f0b03251100720003070384c41041d01d80c003104072149414941860050032325401094410044030400030344044541a920b50844400034060070b203100142d00c0e200c0140c0100314840b0307008c1440e07401710041c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 566886618 1250 566885368 566885413
    0x160303050d050a05040312020c0307080408100b03010b010c02040b0303040503070e0106030b0109030308150111010c02071a090904030c033f0506030601090f090b041101170c0307050d0b03 82
    0x1d4000c1202ea82c82c143c60030100c4c0c00954006000441c02071804160680c0c607009404000c6204040d2031800b107032640c414045620660011304240c100c00540f5100080030301c221884907400354000c0c020780790600002485c240e21024028402d90352088ac840d22510208107440103001f0107021113180301d8440b5000c1858100911440c40040c0c02d080a0007110f500c1480402c5c1126070684441d8055281c44481c0900380100b054403a0404c10728886441e000306c1c00f402034110082c115000742000c01e0815a5040340c50842e4240c50302d201904000e107002c40d032181507603103502030b0b0145040c1c0b031b00800d00d140444190040c1c82e444030601c0c804070b42e4000e020b00c1060141c03070303a94002d000c0c4201c00c01704100070005581040ba0413942c50f07003141004120249841e0000034107030803c20000103008020340d8030001507542c113950a440d81005280084902d50304040f030005503441d184501c3ca4240b80c5050603c600c3e04c0020032079010480f0114501e000182260401246101d000381514140c8054109100c40080c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 566887868 1250 566886618 566886637
    0xa0603020306010f06052b0603080c2b050306060d0204230d050d1803060f0c03060f030b012c040506070f0302040b03010b130b0d06090c2a0516030305 66
    0x10b000002441e8500d11100c8012205162a1113017410005682507001c0480c1c000074040d10918150305054001240c85460b01440c4034503030741da88403603081e002c0740e10f08040008010051180c1c0c50100c0d0300c0e20491849078182c641c042c03a20070354030341c0c07001d001c81d480c0c0c09100b104119682c000316003c280b070300d5420320b9401c3e003608c1d80300fa000460403440100f000d62007440310003030320503041489000e01c0d40d40b080300c02d44000310b8100040030722070750b8aa80f004220340c0c003120040b4009a5031031104e1601640340c015040104442c0002014190440c0c50340d250301c0c0c1e03040c4180e0040d0100c0ba03102c20850741d026104182850742d161036952961405007041621140100d44000015480d148540c0f0724034001d00c25102610030000c149401e6a0030404030007482d60000101a82075980104001003401c1d4071001440301c460510ba010440503c1e0424800a90704084640f405100d59001c4081d05003401c0d00b030302c40001c0c0400222044004030307803e16500b48a180c099516190409800100c14141c11000030402c0c0380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 566889118 1250 566887868 566887873
    0xc0c100e0a0c09050613020f0a0c030e0d0305090f0402040602030d240602010f15060f080414060c0715060312030f1508010b0315040507030f030e0406091a010914040f060306050a06030203 82
    0x48825440d0070491040d580300d440c1544082c000005024815109041012f109044c68003900c0c0c00d43c4001440b800c80d520044002450001e030407042c07410101032010501c40e00f070f40c0c00e50404d8140180030f900c80c050041d002c5003007590750301c030642030001d0402c4542d00500d0a07041e0030f24244d01d940c0024040c0408001d05481142040d007031021040c210300c4520200d4111382d83d03c0c0309848418200301c4030390001a100f0354a0035192445849070940500c0748034000c803007064800780e6950b013600d4104100038001107000072240c030b06401040400c0242c2c505900c1c41c004c0b4030380055258200c0c55164018400880c0400030100042030220b10383c001540082e080c950102d00b1143c95600f0240341c030200e40403c441c000c14a402000301000051010340301028000d10a0a04030803440843c00401c085031200d51240302c10b40d8603940c103540d87d00c11b02c00c07040c425210286024000b8900307101404011410b55104076015907500e03869003040c2d140360351041004d1030340b2084c10300541c149010900d01a080341c0c0030036131290 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 566890368 1250 566889118 566889139
    0x6150801151d04020d2c0d020703030503180a0b04110f0603040f03141909180e07052215030b1e220f0507030b0c0c100e0a0c090506 58
    0x70307004032001201c82c030614a44140d1441000180406500904507042441e80c403029400c42c0350582840d40310502200c0083c1d8204140f5a4100d00d20f040b840917824001e44d04580f40034404a90b005080340d07403241c0040550010a040123104510b0242c0318900588192380e40000c1c04200304480d100b80d108500b040300e11444400008081101901c4150ba0042c1032a034155030b01c00010f4010003192005046c40e2000c1ca0610300030007a000c600d0300203035040d1800a9800001030000820100c1c00710105210008200040e50440381c0c000d917502c40e06d02840d031003840720703880c8200144e1894100d80d52882d03040d4030500c07040c45a00c0750310910030710714003040b9003071804400001d580b07040b1100074000071071a004508240b03444080603116401110700600c0c906030103071260b00c8003080502a600f02d61a20400081800d0341c91410400d07220400074044140010040000c85501d5400040007203045001100025844035400344203407a01e20740c0e01c00113105642003000001c0e107400702d5001074400c1c001912040c200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 566891618 1250 566890368 566890409
    0x50c0301110423042c011d0a110310020406090f0e07020d050306030a0602160c0603050106020d26040302030a0210140115140f130b121906150801 64
    0x9020364050500a42030f50520440c02690100b6046189074015000064400061400c00040140e4005144454050b869486841d600910645004001406000600d01d401401050b240c0d4141c00018149101d84881440c0e80c1d5030a108201d044444c00e18110350326aa40c8202174024440307445040c200070091072000520f81c3e000d0a000d0704c6050b09502510800301406410f959a0300040d04c6550503204118039440001c50600c010000b05801c003a808100d1401c9141c417204042c00d5401a004050600700108103070f80e00000d03151120b06042c2040d06000c0001311143c000303104080341c81c0c0320920700c1d0030a01050540120081900d80016400d40b00c40c0d00b64180c5500a0b20100e50201c4100421040100101d01c40520200c0b800c1c580740c6013002041e8003034183c0018603000400c0821106d140018001c0f98036500c000d050006243c3d1801c401e082c035a03041d88096500030000c0a051004040709188880c2030341590100010700741c11003031100a80761280000301100000d00400e2550051480762800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 566892868 1250 566891618 566891651
    0x1614010606050f0c0f03030a06170a1e02010c170310090506031906020c060a0e070503150a0902010c080c03071a130816060e0a1a0411010c02060c0109050c0301 70
    0x541c0c50035200c5a03d054a51841d904980d44103d500840c640a07000b48000751540c240001c5001e40005071000ca030807402c00061800849041002c86101c0d03111020100000c1c6100f003040c0b0081d1051950700220f481a800180c40200e0701c070500428601900704c2c40c1c240341403100082c41c0a503204002010f407040d00e0310103090495106449103035055200c01d69a104410254004501c0148615805414180301540321450510140d0309290190746440e01c0d40c5440d00100030300c000411049004150051403029100a1084050180d841c003d40300c2c83e0401c15a40280041110240d000311807982d00c44041d80d001343c03030307420002e0700300c0d81d402d010840105201080329095001d500030720249405a0813960381c8412551142000616085043c400b2750007080061266008005600c4080c0c03c80882900d001184c0f01401e0400d01190340040381484081451007400101d01f140a003091b04003900540002105e40c002e1140704000ca6082c030407104100080843c030030ba1411000ea00030301008503004030100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 566894118 1250 566892868 566892881
    0x13110c0c0d17070c0801021803120711040207060e0706020c040b040b030607030c0909060b09120613080c1216050105060f1e061b0a03180b0403060b0f0402161401 71
    0x805071901d841540a00e100b011006000315881088581416942c4464042c2a40c0084585210710300c44041000ea450034207000c00d48500c0e80100180d841c1021564400e43c1410b400d4407511300480e40805c0140400c0b12030341c8461241c9046130122a6083d0b62500001d540d04034034240c2a009a0606a030038403541441c0c02100c0301c02030300602800b603581e83c440f400c0740100545010b0404005d40760750001034220b114482c41d8040d0900e6400e165680441905215030f50184065850003640000208942c0354550108400d00c29403192032190342d6880f2040d21840d0981c6443e03032008107607000628000c1c1c1a4031501d00c85c0c44a2081000f031205e030303803500100911038510400054001c154011104404287c00ca0902c2010500520403420441c001d4100c00d012241c0c45945000341e072016010005242d040240244c0c401074604034121520b00700b01800c0c09502440c80700818864680d50500210742d200769030303603e0100e0050030440d00d41e5950b519400700035074400c20940c0d62201040454255940600910 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 566895368 1250 566894118 566894123
    0x60414032d0d022a0607140304032d11070f06050f0403151a0301111c060b030c03070206010e01060f051c0504050313090207021c03180311090a1a090613110c0c0d 71
    0x1f241c482c80403d001262642c0010021000c001c052020b00f80ca1060340707090b0803100000d10714200d184011243c3e01404440c400f1212210a6000706c1040051101e59040b08003030b181249030198070b448074040000500c2c00340b500024211402c101c80320f00c0c07408446d807180c0f403400200c0c6014050440792106044c201c0e0500010703921041c4003045041d44241c40116030650000d2181000101180d8920035810507130020f480e910061035000050101450341000700c68090001c1310003103c4607516158018140074607125251040c0000401c5284022804c0c40d14074440c0b1460960600c181c0c540741c50410b84a51201900c030007070b0075200e40089180d02a5100742d4504c0b80e8060401c40b070001c0c0410029100c612900e1084081283c000300304580e911180c0c03070200080d0311074681d02011031400d41c100b00c0380b1180106500070003490310700c5d030303a030200754215900550700c07420317280c0fa802034541102041c0c1240300101103480040c02d01005412035401c81000703240e031004400a0300ca4a450034010844050003a0001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 566896618 1250 566895368 566895377
    0xd060603090b010306050c090307120605071407030c11060a020a0624030602090a24030501060f0c15020417060604051e01030b09010f0e060414032d0d022a0607 70
    0x50002445c0d0707610031134102d0a4404940d06040c00d0500103444c1c52559003012198605008002007001401d000307168210400e8242a030340d1001e80d500303002d003600a100018040011403c0c4450074064a07c00100c1d0143c0081c001c43d5a80c0c40c5400042d6448495210458040e49051345100c03a45050101210340c896243c28502d800c240342d6101c0602170340201202686c0288070381030003d003090f000ca4141c00103194442c2e0074640f840403e0000360807103405900c10014070100a140030225a481700b20aa40198490480f801040c00d03e8a914003e01594201c2426020000344002040340005a164070030581105c0910a5945640b41e82c51142102c01c140010005648014030000e030340c0c00c151683c40085c6000000b0074006038401c4030b0507540100c03041c0e042c03a003041041c070081c0208191064048407440c2c0c01145040c8a101f5035601d070450b07042172030130011405d040d180c2c000c0c1e605c030301210981101d0540c01e6440740064542e00244480c1394211072800051003060700c0e021500400d4880c4240320640b00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 566897868 1250 566896618 566896621
    0x71b0e04121e020a0f1103070608040b0f0c030610140301080109061508120307020309151b0c03100e07050d060510090b060405011214070504151b02010c020a0b0f0d060603090b 77
    0x807079010300000c417907040300c0b0380c207481e140303101182c070208106c5004154646c3c8019150509040c005841d600107019203411256103002c0000c25420701d02180c0d04128240c0e07120482d0605d115044414800c5051140d0807060000000a61000c05400c040f5449001e202c040050240004980c00c0001f0180b192180380d420944074010b8424202c1d002e50780c00075003801560303d041b491900140303603200131800b0030346050008202c08841c1c40f840300340c0a41d044400740040020ba20070100290b5180013101c407444900f40c0700c2c4000740003400140204c0000b0400500300941c07100c0c0301c0c41d0441c09000101e511006007085818001881c0846014203401e682c40079103194503103418100115045480d400190000544840140d4815144140c4051148030641d4542d0f44a50814000d40b5a02e4040b90200c001c214180e01082e1021240c083e40f07c042c6642400c001d0760b10156031000c40c0201003903621407400382e0300c003049058202002c01c00406110340f0141e01002210346405050301250003406019010710300c00b20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 566899118 1250 566897868 566897873
    0x90f030206240d0f0309080a05011a010203391006090b090721110a02061906030206030c0309160f0501090608010602100b0102030d0908070c0515071b0e04121e020a 72
    0x1884c0819a8004d240c052002522a05180e20348100700e00120340680d034864040b038041c410f5014030860300300e00f407000d140390510001c0152104200099054800d10f0f00c10100c000100754425052040c5080805403151903c0c401d40c0900104028815200c80c2c905100d40a089460b000c81224400c0b0441d880300349500d01d481484401d014131a03044456807590715400d007609820300300040c01c0b1032800765000f00700310b103800c2c40900001c0e501c1c45031000d5043d0030014140016a540b205407135111100b400a1902c3e651103c030818035013100c2035150300300483c010401140205407140a81d00f0745500f0f0325980b54899842900329524042440344000503017207200450084541c940100d07248402c1407041304c9c117006400d81c000085844004045480440020f1080c1c00c201e12110020002c0004495841070301c00506028000e13442000070040a0203026804a041410703406540005061240b600303030281d10b03003813031302101101d120304500c40403c981c815a1840300054007800480d102c043c1e0301410070303082d069 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 566900368 1250 566899118 566899133
    0x30301050904031101141f050108130b191b020c01140703030b0f06030a0e01110a08040305031008030a0e03010b030a2003070e070f1704030206010b03060301090f030206240d 76
    0x14031a24502d5501d919070b560510302c07a030070118000e00c00f56415074401f074524540031950800035400241402a00000c010048140210190600b03070020318001c0f181d03444141019050000541c43d00e1024130f818001e0045442071011151400420380172110f0a20064005541c080d4106100d014408810004400080d11070303002030705061005002c81d6000d4040f400082c0c1c0e982c10480358680040d039100e5100f11034203c24051240c540c109001c501c1e10388007440c140149541002030002e804e200000001c83d80385402c0f05880c0c4010642e02042d2900c8440304e010003443c0003404074185129600f0602282c03241c0c0b80c0800c054840990101c400500b0580043d84810000c1c500110380b0b5050291180004074540141c83c0a88241360583d1035031001040a075000c0c01c54099140107000c800410810480007a400050340c2c0d05480017900500e07107954817640028054484094010192000c101c4040308042d000519140a00b810501514145940005c801c0600d4110350211f40c2c000c200041301c00215014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 566901618 1250 566900368 566900387
    0x602161a0712051216020712020d080a180b0307090b090a051c05060112021212040e0c07050a05070e13020102061308090d1209090614011409040f060e070203030105090403 75
    0x403030800d541404130fa10102c1201a2086a0340e404042e0400c54a10b641035042c00b440024003075510007552040c0d201d07004600e150312a20401000d03020005024215140650401c10782d04401542e00c0960300d403035030244281d80e0000e4a0700f10100b082d028002c50b16030340c1d420903034850b96009090202802c0c40e050810068010382c082800050f61200c0ca0900030403414407115001e0b00e01c00c281c18610503520700c10300c00c0c1d2200c0c0250145050300003410002e6002c080d041100d08880400d4100411034558488124980c891850020114404e2201c010200140410100210f030380d0600d00400300d9590102d10070f0004400c000081c01a000500020500000c1d28480007040340640b030702c40c1c00c0100305400314194074a0a1820350f1541c0022101c04882a403000504003d000e00d58801e00c410351412801c00310f00a1500b00c201e0500120240901d482d891700802e64111a400420500c0035001041c40b000080c8030768041c2c81035803106039000400c01d50000040320304aa01c003030851070195440b45c030101c0750a040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 566902868 1250 566901618 566901653
    0x9050f01030923060f0109090f060c091d180706020334030801140a0e0f040215041e0b09030304030803090708010906140a090302030307030f0b0405010602161a07 71
    0x500c2040031403d407050b00b011030b5519040e00a00960a011815003840c18050b44407051990a100803800041c2608081c000d0300d95009202142402c05280c0690f48482c940d0094503241901d02040040348050700040e074060000601c1a07001286000212626003906000742805640f04110608140011640e440d01c000b00028110b0019840c0c0c881d4000f8032802c1c840183d0001d601000103122000c0d54101324094143c04544204140e442c266200d4001c0b140104000420980c00002600355120389083c90300c0000205d00e4507030b9031925404103280c09030181c2402501009800c0c4042050842c01d02102c541c2d001c000c0007181014510381c0c1300d1400d85c0c0020504076090041d82d20001d10340c5024010842c9041c131495000c07030804485284600f511400901120115040010b10300200e40c02208a0781c01c00348514010603114007548040700034040103080650424509800080c03c1383d404900002240240b034640707080350740c2c0e0740000074542c0b21042d900700300394070100034600c001020300c003100842c1c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 566904118 1250 566902868 566902883
    0xf0606180a0302030d08090712050d1407060507110d140906070302071703043006050601020102120f0a0c020f030d0c0311030f0a06050105070809040c02071e1509050f010309 76
    0x15283d60103e4106480d42c108240411002ca00380410700781c0178000c41010f002d6141540d1560282510350350360700c2ca8000b140300301b400590a5070304000300161089500346074111006000c203060160000f018070039081d440c1c030b10a0003120391130400284911440803140c03481a40d22810162046d04109065115100c22000d6110300d040000380840000100056100d0850255031114030b0040105c0300d034004603e01c100c91408024a10114122812810469541002000a681d642d01d0010303130081c40760100d9a00c40861801c1007100283c0b01035445480351342c0c2c003002072241000214059070707501d540d0b4411003190b0b00280294034074101e05a01c400604d11903460b002c501400002442c07425940103642c281c203034804400c204030340140da178090180101801e01c2c1851038209541c40784031480c000c100e000c91017a40c81c1c50408188070320800c2640c018080b504400100c440b452034105400c0001c070301c28588200111050904000c3c0612403403000c548015000441c809a6080110300801c1003d400b01c070610b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 566905368 1250 566904118 566904139
    0x1833010503040b0c0705070e061306081504030315091e020301030201091202030109120815030c0a030609020402072f0904020603070804060f15030b130314031b031e0f060618 76
    0x2400c10047c0341e0040c25680c901258908045c8248224600003880d640280b034108003003000b90207400200c1c2030280300000c4080d00c1d140c0b02d81c42c0441c00340144403842d4090076010307036002c10314480c5a803040500c02c00d4000c8002c80c02c078840d10760009900092001902058440504000d2000228014078030780348000c1c00000c010301b4607520311550011120070700e80020a08000c12415032011426070003900c508800429401703c0c001c0029400d1000d501005007001d03101d40b680011900c0300d4055400b6164031107034805d0964002981c88030b02120445e61203401c0c1c0c03824420304409040480215000700d0300a060607203150b4480320183c90442000c0c0c01211842e60700c0c010001080301c688908290038941d00041c0300c2c03951643c02c00381d032507200140418241000440118001035009003055001c10440318099460755a0440690b070241a03920207041e002000004002d0343c030100020110145103451650001d6843d00016520030781c0c0304030360554010600b0441548006d902082d44440c00c00300034059243d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 566906474 1106 566905368 566905373
    0x31b050c100201110d201e0304150908040602010c02070b03041e050a080304060518121317030d0b010c030c0201030b1833010503040b0c07 61
    0x10480c040100754414002c0d000380e1010741c105918152074620002d00c03800500010068400045103111140701007100050603544880f9100d9030b80201e6003104c00102003903502c05403055030080014008880500705501550300c600e849200411380701c5c0e01d0207401a0035900001948030035500b00040a11400c901001a2030340507400c0801101030082c4820004504084480301030018000ca0910313600780f001c10401580643d10845080040341e64150000d50300d425050310481440d0080c054407401840e20b80c4c0036281061100385042c80507640c0320341100d00004005400c0c038440d000810b0130305800b0b0783d62152111400d800e08209005071055940202505d4684000a06066440076110b00300e03100c1d103401c400303086081003180748503080c04010401034000d00501d600c6d86013903032040c1c40500c40c4040701444450a06840b55404c50b00c545d03076926080304000300340740311080741071000c07001 = true := by decide +kernel

theorem cover : BRFrame.Cov 566726618 566906474 := by
  have h0 := BRFrame.cov_init 566726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 566726618 ≤ n) (h2 : n < 566906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
