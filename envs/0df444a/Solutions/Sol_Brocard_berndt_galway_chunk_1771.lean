-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1771
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:36:54.878097+00:00
-- url     : https://prove2.me/submissions/8cf04132-f618-4e26-a99e-bdfdce3490d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 318345323 ≤ n < 318525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 318346573 1250 318345323 318345329
    0x1211120414040f1503031101020c011b08060312030703151e0e0f0f0402060304050102040b0d0e1b10110708030a03050105030607030213050121092d05120702010912030801 75
    0x6401c1c8140b000070f40d0311004440c054000180240189141480046d115a2400d08044107000000d410004a500c00d40c1c2144e12054070141c1500324882080d03c0c00d0f070070554055020034120007402c010040200c0c10141ca100c02044081051740d60b42031410380c0802040001c025102107003030005003441140d050310030300000c0c0c010320704144000c02c00a0402d405603806644a0f03036001081900c1c2d501d503982840010b03080071340100c613555000d20011801c1042c032400342c85501d08842003c02c5203d2510211030500d00e2507440c075000d06108809455081c0c840301040c048080c01440d1101003200707483c00302d07400c0c0315003a0454441e900000071507810a50781038004505a500403020b40c0c180b40c83c2c0d02030030343c100d05c80d42d031904601c5090302034100820740c00380c2943c402440c403002e1003078580c2249140c0241103074040001102d109000e213001d01101440480c0a41c10b4040002450f204030034143c035082e90314106000104001400001c1c15021a407207401c08500030500710002448040360f92a01400e4004240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 318347823 1250 318346573 318346579
    0x60503090f070f1a0d020d0b0405070c02030a031d0603010312090b0a14130302090a050714130504090804030b01090b0f1f12180c03020315041211120414 67
    0x5005522051002c21420125861419210300b902d14140000d00e444000070142c40b0111002d22020ba40e4183c180000c040c07040502030b0000e01d04054908000854401400c100d04000400c0303441001602d000031a64400e5415080c00c03040d660070015840c000c540c1da4400709800141c007100000c01c0001104070201c5260303560729558011511208075000c1401013600c0540041c0035052402e41020154004168188020714180328070790301c0c0d070045800701c6400c3d035001151582d120208040954800006000d051090b0300c402e10300110030b200700c0034405040c01458800d41e5118003901c00c0250306000c4034020b42d4044451807996a507602507a000308541190b2a014103d612450007883c40c3c034400c91000d92494005034111104190001c6078000301c5c0140e5200856a186000300848400b48100d240d034600c60500e4804650942c4145800d00111403810b9002c12042c00038400040c03800844042c81184602e04403180394a00b6581514001c00c0e60090410580005008031345548283c0d40040c01031026 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 318349073 1250 318347823 318347833
    0x4050304090c050d0b030a12110c2101050906060a03150b0405040f05010b0d080a050d090204061203090b030907120f0b01030b09061e01090902210a0c320301140106050309 75
    0x140081c5034a80c0c844107c0141280b0052901c00c44582c01ba00141940d0341c07410080f5804c002000000c41c2c030a0340201d41011008448080802c0005800d00480b0703404094000517250500b402030214644002d50b0000034104400c110400c1c010100075480024201c400030710034005414141050940c440c0f600d541680c8550a0264076078071400c0409980807000d610107010341c034100349072208441c00d8204140c03e84220b40c84e50440c0006d40c4d214003605024000401c04512000c4c02c6280c00b07130900010342d0003203008810a100700a0601c0c0081411000c0381c3c0011403a000110350752500d903a550103070150051158a801e40048140308150088038420504002240c08645440c01c11401400c42c1c50000d10708403040030300502050516421103401c051018003001c207030881c9101d031000398441800c0d0582c043c0e44520105401e00000b080c081c8000c02520500440c0c0420600812098040303642c40e41c07942002450000075181c900b548403601814000c101c00605503103501e4010070340c3e8000c6d2030300302c464400c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 318350323 1250 318349073 318349091
    0x50307140d02060103050a060504050f120a1701150513090203010b0301060e220c170a0e060c040b070201030902011b0f050d0509031504051e01060612020c0c0904050304090c050d 78
    0x20f185041c0d80d0480001d0441460554400010b081c0040003220725001e0104040307500903040064804070607902e0003007a03c80d08070b854000c20043d540410ba540505000c2c1c0100305a84e441c0e0300845000c0c50310319166684002140340d4002d2000c66a0280f0402440080001507800741070014506840c4d0954410a52064200c200514108500c0c0780401004d00d00003400c250040703035804030711074081c00e007420454100a21034185012104454030019241c42d0f20740350341958020320409070311004c209042ca00340f034100071460009010340b002c02414996030b419450156801500700b600c49403508980700c640b0580303e103000080c00850b40d80031035043c81500c000103010f50103502034401d0203001500a00c0c0740d80e1058042052902c0c041d01c00d85050161168060b01c02004548041d09551010000b080c080c1c40c060300200303a602e15010f10340b0310b148103001c1c0e407060040100e144000c52030111407180b419241c5c0d051440c114480d1740c2c031a01034946052030010505800c00050404c024405030b0070445032072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 318351573 1250 318350323 318350327
    0x9090111070c090c052b0f1104171603060c090b0c010902090c0c03070807140102030915070903081c0b04020301140a0e010b040b0304030c241b1e0507050307140d 71
    0x181031040b592101b03017900c5c0f0310940e6501e904181400c0540d2601066004940e103103142110581d01502d00c2c1804001400d00c44080e260130b817031b40700c80c3c2e0010007840000803000c8100c1204c1b03014040107000603100d44070442282d10411410000d000001240c0d80e9468007002d40500038403e80c0c0f801c9000319004000604030911250556140302c2c0e0b80e0700514507015042c0c0e41d1251580c001d180c2100c281c50600f640c1d04202100344051031040b0400790062840426650000c03420310300080003407003041b03142441400040c1604064070100150400001c0d45460080d0460303020700f11041c0d0b0a5003052010000003802d04400281c22807041044c1c984850854032502c1c2d800754100f090080c11025101003004000300f1400000543e8031900a02c0c01c051203902664948031680810700728201201c48402400914020038800d1490074200504501441c10002d1405032080003160303a180d080450b50034002c00001d0041c0221400c082c1e005090381d54410701031038000b0141c40c9280240c40b50344039600c440c460240c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 318352823 1250 318351573 318351577
    0x304141c031409060919020105210f01090213050906120f0706031104050a15210507030506060901140c0120190c0305030f040f0212010506010f02010606090509090111070c090c05 78
    0x406014004406260286e88601d83c52840224104241006090745c0c845400300340c845085c0c2101c034810501e003402c9040451001301a00301c0c08c1c00c103104000003110119000840022a9002e623014200c40e512900094071003000441c490140d07010350821f040201c080410880151342141c3c401700f2003010386c04280e2115002e030780541c3d40c008402400c1404401805080820900380c41d181c115040e900381c80c00654080c24440503200810346480c14850304903054002c5991000b016907225060a0703009000804056407641c1000c12504000342d0504900029041954518068104000c0b010b40ea1207803840540e02036581040d00e80d85000350211000d03c9130080c0b00105070107031b59450458a42781410a400c03032010b80110703541444c1c15000001626502010320b070581d10302000103070a16040d00050400d29202c0380385001c59142c500140292a003041807071064900664440a0390350f13903003207060300424810424000d0a02c01203a12070810003140780b504140c44145506012500720014140c2c0d00b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 318354073 1250 318352823 318352831
    0x7080f061b04031a0402030c15070201031a040e0604020f04050f0a020a0c0b07080a05090111160503091206010602160e071206031b1d07050304141c03140906 69
    0x5400c00404a0804048141c8100c0079484804000e0314080e41d0fa51104050202040c0000200120100700170544c41c081c0031a64014000361070001c0c030701588242030305580c8103400d40203050603035404c45c000c16294192007035181448041d1041200f291880c1c0c40396903919040364101d2052124411443c503d04040c00340d54054031003803082c0c507400e8688105000c080d40020000c641001104030028011400c2d0250180c06045c2d83e4903080414186020301405a410051220302c1986c104540b1102240525003107072210300351108680c0c03070340340e01c4d14040e425481030312004c640c8810a170003140300d10384001c1081412540240c08482a0001031015507030b8107c00d40c8607096416404000045d466402040002d501000e00000028034075109c1d5918240b14580c3d00381560045890103090120b0000110702c8009844040706141c4545050fa500500910000300010040740380484d072008111020000300c0d9504032041c031a000c41c0751840e03e006008060407440c00300002810004640290320100f000c03801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 318355323 1250 318354073 318354103
    0x12011e0b09071d090103030e1e0f280602010506011e0c020d0206070c0602060a0605040603050a0807020303040803030a1b03091a090f030301120201020609030f09190b130303020708 79
    0x81a90303403000c181c90810661003041c00720750b8010a5108691340c0c0340c0c1c895019510075260354001e41b14403420701082802080c2d00210640d140c800000003681c480911103181d00040b1303900001320040d0041000b04a4141e0164020480c40704000b01c0d0058064000501c51a405c0c0d030382c3e1b05e158400c041c81d0490b03004d603010028003081303400d80c990340981021030b140d440d40790000d4a034911b018000d03035071140040b03c180e0003a001a0821000e0094200340c90060700b0040c5003c540c14001942580c907099205c80d0301c03c40040c64141d00058203002c5440500c03d030380007080e001e41a00d0b100d1030007600c2c03034015015040802c403d0412001400c102030340a449001c4000350050158001c998100c4040d1520003c09088031159105803601c0b9050b904080000714060401e848052919023420320000e880c0560141c1800c00c2a001440940c940b01101d06c141c4980103411110029070851460180e494092583c10540074142d0000c1c0f1450701032500f076003910440c0e10030f6080303400c0c565841c0d04c290b07200c80052000001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 318356573 1250 318355323 318355339
    0x50609100308030606220501090b070302060c0a0207120c030b060a03120f09050d260901081302010c060515030609120a0e0a08030703090305010b0303031509090c12011e0b 75
    0x4040b0318240c0c09150700c40400b0380180d1521540d00300441c3c00b03104205a10780c141d03071040750500031564003880f114010010080c1d19401c00340e066501030340f1110000c02d90801007902281d87c5141030310030800e04008181d0a0462400c400313031401c0c551901d12840c082912140702281c0854142d04103403d48608503900141d0200c803407028080d04030380d074007030750020801003020707415010901e6642e00ca40aa1928800c0340154822111409209411201603d6028001606006404041c0d8001007130030340c088080703800c081e1020014401601c10340710a100c083c040c20320b01000c00202e001c0d48100064101c00440c21140c0383d6a07801580c46c0c0d901c002040944410409108a04000b4002c0e442c94400840c0144030b1018103440b184540c0c6107800089003540010b111080c1081840780a02c151510050150003841c071318a800080810b40c012070302c68050042600100007060710005000582605000802120b0500f089000060192217181e0280c0c081031542241c1e2405007040384140d410300e03035000d03040d02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 318357823 1250 318356573 318356579
    0x21e030a0507150603020301050c0a2705010f03020d020f030a18032c030109050105101e03020607053408060402090a0b0105040e090714180103060f1d01060905060910 73
    0x1c041c1400030700c0f0311252240c0354680800165002e000d51071240c40040b07151600c650600d50021301c0f000e040c4c0404030500c070424040040d41000a550300041e20b8080c24120300f2007400781c0e03088009208500300762400b1440030a840901800c6a001140509500d82d000d100054981079102840c0540f0710005011844071414080816290009121144040b9000d44000014203011909580c0000b4084541e81d5449080150300448003480c1c002401d8809032f180803000d441000848250002c1c040684a040041209070400c00304100d0047c0c1c00020220255035888600c120a0303c041c628021040b120703044890100c0e61039400228948555001461601140c9459203000000c05d1841c1c4128100201000302183c00420241c0141c000c0103404001d00019107000e0680340003071080144540702c1c03140b0002c1c440c41030510b20f8130300f41541d0b0407072000203d480c0100074100052803900802c4912021844400641d000c0641c8818126011070a0070300c01e56035034108101f001001254048014854030901b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 318359073 1250 318357823 318357833
    0x5100509150118090509101b02191e03020601090609020a090b09010212070305070b0105011d0909011e0f0f110d020702010909060e16020313030b04020d080a021e030a0507 75
    0x8012450306000750304205813600300300300c151072044990500aa1000b0001138030300e416481080c1c00c1864100c0591450591040000c0d103400b900c5d032004410740076400020382484003071100c8020401c14030a40b0810b9034000d290280d21540c0034807540101c20303e0060000750005240c000c0740c204020303c4d510780c4038590408180500e10342040c40788034118403a000225407643e4491000300406806916056100d68051804040c440701c1600300604016a004e5500f006480e0b403102219070700001c503090a03c507074401408a0040c02c0c4101054641d0b18804110b0441100319486100c1c1820704a500b8400400c40c2e42450041c1e514064505600b15410420224281900d86c094001244145040040540e403594100c05039095600040700114651085c46212410b90406000c0d0b00304a001642c10030001c0075001002e40e0080c80003400300c41c84200020215940d0b07120508410b50f0004a0030703240c801e107400080da9000e00b1060302d0000c140007200780700c82e5980081555440c0f00c0301d81d6807a01e8044a5030318 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 318360323 1250 318359073 318359087
    0x70e040c081b0c0a1407031101030c09120204090203190203010e240405030d060f0e090c0f060d110a1e0206130611190f030612020f01030c050f0d051005091501 70
    0x507012809111030701c134001503403203600e0341c60044c1c00750080c5801d50844c107100400140040700e080c1807502d002c00f000710a54005010808550450041e4100d10030f0703600108010380076540c0025418080d02081950007186240d240c480940250001c005200342c08070119a41c90914103540b40d4031550fa010426003000c04183c0a5000784500c054170300741110604400d050b12250f8109603a04100782c0310601149100d50030469001108a0040003008101c6021840f260b20f6100704038003c0308000b848a02c0e9000d647c019802c180740c40342006a80d2510044002c00c0091000c080c4203d00018598a0400c9840064098000d41e030a19900746135030b0344cd69030700340148001e1140c00c4000e142406400e4600300034000c408441c001c80d03141c60581c28544013000303045509581154101010710610803002d0b0301c0343c20000442d9502800d001031000300c2d46100366410300517980384003081840005e0a00c00710000b0340200780901085c034441000140c4072001c00140c2c07001200c801c556030940c0701c058556503100302c613 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 318361573 1250 318360323 318360337
    0x90803072a0209090a05061302090903090904020609010c08040311040e0703050c1009151d041e0203041e150b0612070e0f03100623010215040c0e070e040c081b 70
    0xc4405004d00b546d01c0368180942129420500120341103040103605202e03900c580c2c4075130b03c0406545000c10060010720140400380000c0d00900010514500a074040c48180c030a09401c1407902c1c0c1c649035a481c01040103901d07201064022800c00f0400781d03400b600021410203503a400005010a03c0c0e416060000711040d5820070000c0140048000903031360310180840325001c8550380c0304030708030190301d98540e500550400071a000318070b050304c40309000e00680c00284560390100c00160b5241c40311f0a0600101d00440080d1006429120502c010480c44c400040b0074200010300c10f1050144450400110340546040d6950f20311806c800101958804c4541d180d41c07060080120740740200c0200443e14080c1c01c008007268a540e20703107081c000c11103580440c1c0c901c1d03040c00c400c81212000390300000752903007103d4a400048034021004a420820102009406040d81c04400c3e029031030000350050140315080700903402140350401e00c0e42c4030386c461200385202c1e00902080ba0041d466407120140190300c071075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 318362823 1250 318361573 318361591
    0x10612080d021c0204120507081b092511010509010506182e03050c030c030a0305030c040312052215050f090414100e100506090310090803072a0209 65
    0x2038000c0c000080f60b01c082c0016102840301d840746800f41d0300c1c2807460411f245e00961450b138045080760041c9280030701c442003204400d440c030705030f603890385450b8949204910382e4070100810356000840c6c0300380c1d020054240c0c1100f014005d018079100c1810090803142c065400c160008041002016401c20401d1150b0b000017240c0708516040f16141030b444041003941c484c0c0401040c40c03c20400601100b040b0541803040c0413030180c0350419102c0e002980d40e9000480080c180100440041c04140c80f5009440003141c02504801c90313031029503030061040d03008545417101031000d045520750101c0f03801d13480c00583d1503504002e841c8103070420f41940c0d07170340081c0b40c41401c3d0102004980419103440c019449a24260300f5803080d1803d041d030015004020035000002c8000480d410041c00032006c004010840300156940c0b03950303030b400b1404170b8180b5801c40b41a49016081c5006078040010042c0214030038800d44e5100c403042c650703510f2941d601c039242d143c1454000c40702444080161810300350f0345d50030a4001e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 318364073 1250 318362823 318362857
    0x90b100309020609040c03020912060606030406050735010902210603010b1903060606080408120c210a060611120a2105010306050601080f040b060102100e030309010612080d02 77
    0x300058246c4d09940c2d2075200107500803502a010781400d11000d000a8912406080245400030114406000040002c1e200c45c1e00c40d40403a030042c0c01208400d070302200c564522401103d00c3d04103104480c1800c01d05094011014000240306006c0740f0036910070044941000740705c60b0391607002204140c4040c2c03205900d07542c0e070b250030402d80d0381d03448144003c4142c046402220714514280752040b074a00b43d21000900c213414040000254160040f984000110a51407242d91100c491542e068000c3c1d1254030296000551616518001c01c00e580d8402c800130402840f24580724082119500d030355200c0b4841c0c7c1d0b0710030b00956040902482c09801e86802d20300c0e100d880f00500d4040c500060742800950398010780e03518014002d0001c40e01503ea803010081c00c1000040c2040d003100b00d042e00000704054604400c01d0085102c0d40e2081c00303840030070310380300c14180030a9498103101512a4000d03a80040158a0f205001130300d0314a2100300001503412422480c1800d11080062029511a031140c03140e003921 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 318365323 1250 318364073 318364087
    0x130e010614040c0203031b0d110307110d1803111507080403060f051b281805030109030f0f090308040308030403230d0b0d0b011e090b1003090206 64
    0x24854400144651040e890300303240581e0501c422100001407450031034104004000200941c11138040740c02c19011040d5549441c081d000a0003000d000c030b030701585031200105218000d03911280040c1602084010b0300c0c45603030313440f40c180d0f210f42d000d0040840365984542e0800c041060301c50f4051256102800c1032001c40344281e11600b4950110700c08607060760002c601031050280510900f122662a000c0400c0340e03042400981030340c0d43c41c04a402004140c0095520b60040300364909860200e1140200140d0740c0c2e0390603010702070a106280d940004500e5039070000d4245414090741c0d501c0303901501c4440b664014007504032007060180c0c0b552021701075544d1000000401441c003c000450140c1d40c015102c1c04e00e403070010000c140300346d085d038120b406402001e80380d84083d4044410b02c80c218400090340003041400708101c52441c410140000c0040d00000850240140d50f01c0c1c410910800303034400c0316480c3c5000758222842d20b211a604003c0703802e00b4100c400e010758041c0b00c4103030005050a00b8094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 318366573 1250 318365323 318365351
    0x11a18030303010905090f0a0201090b030a1e0614060f0405091e0907150c031202090a05040504051b03070e060108071e0c2303030402060d0213080c031501030201080613 74
    0x10081e4001310321103a40b9010400d44000c20700032030041c2c01020025044200360340e00001d10003a210300881007000e0000002c90308110b40c66115000c241801000d04c5401d8505141c0d28000744003034412580403a1030035031040a5441c3c41e00c102d8100c032501c807642d40d0070141440140a50703003000a00d0300076000c1c1c450f00c95010720742c80d100b882c7d84600a0b0800501c100c0303084c0000040d407012031100c9003040c4101004981d0003e81c110703402d4441c01c01200001601c41c14618001102490f0540c802c1342c00900d828140b0050003400708141c000285040d04129004094078189507448181e07126074411200000003040640d88207802c220b802010500d00216030314139403100c2115980440181c040071994980131f0104101c2c449901c4561149108a041c64400c02c0c001026260f01c0020002171181c00000350b503608101041d41079482c0c1000c1c2c107440301161601d440d0030903074648140c14160300c684107901a203e28206024480c50580b0ba0607510304010b51203003014420300034101482d9010f46601c03100084200b00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 318367823 1250 318366573 318366577
    0xa0f031101110f0124030b041b05063123061306030902010e090118020714030a0c1406041106070309081207061505010509190506040f08010b09011a180303 68
    0x11256000042c1d0b484514030512075105170102c085907001c8003036010404601080c103a10790241e0051004400d400c881039000402c401c99402907070340480c000c101e40e0710f1203194540865a01e240704811501c400148070b00da0315000c0c1036210342d080846079807044403203a210704181a4179404001e44014102000c001c10022904001e40203400000c6e51483c0003015903a001c411403007030400c00d4540112550401400021a010407604100156000143c8008102c50707580b032540c0090080301501c4c0c4a00d0001c0d001024044001030941da000801c0442c1100c0e980c000c24007a00944c0e100b0460901d03040030900380000c0d40c02c0020203400344150740000080c3d14205104070030b00884540c4001c1c1d83c44c0c14500d04a001c480d4528006d910200000005100301d9800034221442260304480200e14554602e00900c004101a00b040f030700064040740005400541c2e641e01d00580d080700c1c0007405074260410070b000d4400c10074401c0300341c0d00d82200540036001a00c00007c040902e10075000d849000c604c400404d141d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 318369073 1250 318367823 318367843
    0xc0f0b0406020c0d080f01090c0908120a020f01060b090f040f0603050c0102010c08060312030424060315052806050d0807032003030705030c16050c0f0a0f03110111 72
    0x1d00d40000e94070003a010305001c4500e14222605100c809420001ea03286250780c0140035110321b40d0340d02c210b8003030054000c1c0b40706070042107101c00701c81d00c0b1a400d45108a4a4102c82c202c08058030480ea280c030081641030103074a0550710052995405e11504404000f84401d0001c4401e820980e64038070120400040e003c0e0384040c502400040040c414014002421070309800385407000c2141c0842408079a98000c01c2600b04603840c08005a04c2c0c0d1546d088c400303006201c0d0a04100615610680c107102803900f41c10107401c803070290001b03600641b0304250749070aa4808a89414035080c201032080c80d5440000d0800610580b4510f00055144e02c803008214400506d1400340c81d103403004500c903400c140e4401000d0601b00082400c46460700d2070311296a6490202030700410512102000188070b0040700c034265805500100b0074403030356020504150b911a10702211041c00307080e2a0403100c54030300b0b004400d441113400311a2100c01307491543e11895042400303031490f1030410828030740c2080341e084100800311113 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 318370323 1250 318369073 318369083
    0x17070e10021c05120103060515031005040b10060f0c030509030f010b040e01020f0403060911041103040b2202061e13140109050607081b030408030c070f0f03030c0f0b04 74
    0x40d80441001c0c1d4540c180b840c14a080103000c111011034042c24003007507411640e2000011403a505e40f0714281410b5800b511301580c061003014903006041d64103070000c42c0107a01a1000a100d621244002c40621205010322004100603000c072400c001c1c03003034000007405030181c07416509044520000034207000000d250a08160746036035020b00c40340303003030310401130094420b1000f1840d02150461081c1140510700c00501450fa4850200007404000010200d807140d000344100002100d0a1114019820a55069400e41c80320000512001c2e10b040185050aa5010028903078480b01e03401c002803980301d0480300c0c40d0f03041c64001d00305205080001426014621208002c041c80c02c2c606000b02ca50b4498004a0401c6a005010401521482d007140d2480390080c060641d90a0a03079403800003281c0280d0442c0c410b00c00003c0c0010b685030088080c050301c4800c042620000c5969601c0604c144011b40514a0000304000d410000031703019020145400c1c0c80342c8142a400c5c4a243c0b10000060fa045809442c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 318371573 1250 318370323 318370333
    0x4140c04020c01140a0c0806240324010c03021c050403171e0316081e01080f0106050103050606030f09120403061d0a0f020f06070602030a02180a0617070e1002 70
    0xb11144040b65010b0340301c012018200604001000300500c7d0404c041c01d200c1c0079030403011204851605100040714030311024036001d5a07a041110840080d02081c03001070000c91110556540c86610540780640d203e50541c0c000c16241800040c2d82c40008901081c080912000700000400501e8107080000001c080720002516520bd40c041402c01508a90706100303100e82c10801c1140300a0760400074201c0e05024504000250340382d085034180300c0070b000070325520709500b80000070f1003100000381c003e01d1780b0256000740b04003035a03032006606554040e12000e90144083c40010761030007400c00c1081e80030b0a0002101c0403040391300300313a01680d0b00030b07002038680036203c0d0384075840c0c0b11060395100c0301410042c005040707410907615551240c3e03001410003441115010105c5c541540ca80c82502d0310280c01c45000c65990800303040e028029446071401d0014510a141c080030545025114002160032076140e2030341e0424800030b180440034000b000c14040c81448540d030285a181c0480d11060b1030001d4000300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 318372823 1250 318371573 318371591
    0x1090515040503030c070218040c090f020703050414061e0c0d050f0a0f03060504060b031501091a09041b0f02101104170106050603091f090b04140c04020c01 69
    0x50400600608964a0121160621001a50000880c5d50010000c200e4940f141d4646c0700043d040b100c2c000d000514034200d68148010b1100c0e61000208a9500800400040740c10003055400d038026180003802141c0c06001c100500c0c14604526203a900d00100b40e50301e80708c3c481076082d085056007004000282404186400349a50400901c002c0d01c1c05400c1c501d007412590381214426102d200070000402010303800010855020f50042005440007d1041c0142030710380c0f4814002e034008503000b10004030000c14102c025409a8800c03403e8034181d918400008080c0748541019521115509030016074626007a040b242180030032899103100d6641e08200c9074005039000785001c6290070780e4440d4a00d00189207120800c64800c4408940940150170405083d2080b020300400c116403003d908480d001041140180010a601c0d030f002d81422544101c00c4440141041100d04681d40100041e4078030000c203010403400e0465201b6100c0100489803d036009402240980e040b16504c12403030380d100e070044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 318374073 1250 318372823 318372833
    0x807030b0603010f03120314070e0a0b040f03300e01170105010912050304090e0a0c06020105010b070209130f0302030c1209100302030c0f180f040e1c0c060e0109 71
    0x110110100840301caa0555040010060801e03101e4031006140c220201078000710345004c0d07046081c07201d00360800101c603883c6c0300710042c03c1c005044840f07a1181032803003404500b4008410a840c15100c0c12400036041d6030566940311049070b100c2c0c42c440d10912a041e074110a000c0545900030148803903540c1e03e0200f528800c00502201e00d15800c40b1050b10480005101590340a2514011a00d0f100a014480307074103800c1c07041c1548a1030300403048550800034903004090340080c1c0b020780340344a1210350358000d5030f403001203003200d800b0701507103c142008105550140c90310f980c01640000310812040c415080725520591000290001180903801c0410701400301c5000f800b04140131042e000d9007510b0302c1c4040700046d010901d40c3c5000c905041d80072020845c2c2100c084140c0c3c0390170802d2200c4960310074070060200b52902001c88100d04c00c0040300342d041c4080c1094007964440c203002000a01541e40d6180e558aa840e0710310310442c003048040034500020980350301540c15880d1080e4000120410705041ca = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 318375323 1250 318374073 318374081
    0x50103120e1c060f0207050601121202060f0c09010306050424120807020d110d0303060f051c1101021f02040302040606020d1710121a0610050403080904020f0406080703 74
    0x80c0b0801540d014680d8000c10441800c198580c456400142d0142d040d642d0350003805a0b84c0091700b0340c41001d0001c1607115403441c149031080d0095410a842a001c0981244e6500c0c00b100c10ba69201c074042c002c250051444c90103828009014100812031a40701c00214040f901c6e207400601d92100417140d103504402c24100048050108120000c7e41092141ca42c051030b40f10340c2800902440000083e070050100d17400c03040c1680308005100401d2801181402009407200d4059a004900752500004203450010f100b0740f42c07800001c101c565401d045032507a40c0207110080185041d40600100711060485000d5008007030500301c1e000680312401c40c0148070489542c0d030080804d55000040380d41889800400c0001411114400c1c0c0303a07140c0e0380d1040e482203410aa80b24921381c000d42da60036820842c0c11050304005501c94a4540101d66409041181c00140701e000c01d400b14400300010b0001c107900b10000e02d56210060800b502e4403401d0030103610300f50310692001001500250a110360180d15001d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 318376573 1250 318375323 318375347
    0xb0c01020a110c010c0201080a060b1918050d0201080a0605060f041404090201050405060a020304080604141c0503180c1c021003050f01092a0e100305100918050105010312 75
    0x100511456124a0002c1c0500d001704101038140144280020142e80f41c0b03400c4200070709102c02106e51100d0394034103015030b070f68100501100402d83c1441030b03488145495002c10103e03000200307201d0b109000c0e0b8005443c199009418903d06544030900402c81d511200014124a80d00600881d501c904d800304940d51810000a00c9204600301810000503070b902800f6a0180c80c81151990350306d1310b40d1641a4514425580103500a0085904100610101d4904500200034074400c0d034072184444204003102410b00300300d400105505001003100760b030315100107000c50107080040b01d40d001e540c50000b44c0d41179910408403800b620542c084d98114180b108007a10364800901b818000c90611140710b01210070b0502618440f6a40d40601018564400e03a011102607664090a4108116940010480054030f07411601408599001c004107a10a02c00c2a21690700c030342900c8003171410a4000000751103030317170b240010071022051084003003503080c42081c1c000c3d84510b00b00c0d00144400c00c17014002003600c00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 318377823 1250 318376573 318376607
    0x804230d08010501140c03040b2b150b0703020d050d0e030c1c1d0f0409020d0b0708010506160f0f020a06081b1204030e0109150201060e0a0e0a1b0b0c01020a 69
    0x6c007041981d85400401d46040d00c0308a5032140d15161a98045c4400601064032400300341c2c0c58030015146c0402a5212a01211031100c0c4003402070b489050029880c4110500100164803d0300150301c60340c41203001e805032034541940403680b540e0140314103103560003c40c0c1000e03040d004080c0f011402200044043e064120504084034a8804100340b03085000c00501c4c074502038031965018240307541c1c85910400b4840d038000c0003d03840783c0081c14483c1807603404a903030070040f40c1c130b00b800407402d4a003070000da41a90280002c00c03036041d0140c1d07540b400002070072102210408007403c20440140e030744800c104044c0c400390744c0e5600503182141030210300848503212158074078010400c148801c01c03440700d40d1b83c0c0607425090503c1082d580400417900f000b40365000510100c118a10790351880c1d4190000005c407440e00c4240151926000d04050840328002107151055100d104602c0c00900c10030030071040300b0f8526407204070142c1da0709980b5800398000c0388041f090383d40c0000d403141c0e030760b81080865510301665 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 318379073 1250 318377823 318377827
    0x1502010203150a1503020a030f050903090102160506070f05120f0d11131e08010e1006050406141e0d21080114041107020301020c0304030b010806070804230d0801050114 74
    0x4041444002c01c2052200801c1503000941f074004940240c104003030552010f03c0401c0380d840c0c4803400e580c481c1c10040d542401030140901c610010100707070803024140c55000b41101c1ca05140c641d1140200e9129480c112018014200709100c031846210291180c3c0700d00c8a81d95580300014141e50003198542059245540420b224038a11181d1000460f01504c90340c1010340b01e042500e051074900c168003903106201941c00d00035000700c40d480215218124a40130307442031040545960801c0152601800b5191484417031044080161400d40700c10254800316070284a080d000b0203021610246145100755130030710707a580e050140889100e503040d104207035a24218020754104081030200201c105e41d060710541d10b904040311100034100444140035401002150f541c4c0b10001c0494884d00144001e8030342141c0ca100000d101134000c600d03284112180e955031900703940c540c0c0e1f841c003154182c20b51140c907000300c2940c0c1114010040260710b44c21039a079107602c4040d62604000400f01c40144003003070091001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 318380323 1250 318379073 318379079
    0x30317090307081b1e1605010e0f06091c061a0f0f0906030f030d062606060105030a0b0402030403031d0a0b06280b03100b03071205040c1502010203150a 67
    0x250a840d102c0080c402500300c10003500d40c0c2c4904d450b00ea920b1420f400054144400b8440e40c1c00106c0c0581400784c01ca0030500f0329525401502c800411901280d00061910b01611441c42c2c0700d0010503034241e005050300c0c4c903a4011011041c0310a124035040750788540d2000200007076904403c546552510868001c3c440a0140d0041032046101c5441035005802c0b14020940e036039014042e4011000c5040d0841c0d07100d0741d01481a4014007441d100d240d514014100340503500c03e0b001c400d0700c03884000c100018001d139203032540112120391000380001e601959400c07000401b03544034002540502d0195030040b550f20400420500010390f0300c0b0400f0015400319041d80001100303004143d500c003608490520b503001c40c40c100c6100140140030b1410f03003d841d4079408103070914400c011314090003040c203441c103c040e02c46507c940c507448180c500001040101052084000341504441e034020700c10481c01100070b40d540780ca684d10200741c01320b500160350041708210100d240200f80c202c41c480c0484480c00c01510f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 318381573 1250 318380323 318380333
    0x906060512042102070e070e030318030c04061d0708010810020d020d0501060c0b0609102105010608010f20031609081204090509120f0a090807030317090307 69
    0x1041d6094800300041c070000240502c01e0102441c01d80ca140c1c4050449880048000252583d009000b50300343c1a07403440100e8840ca100d0300700c2c0313210850050000d5241400540510880c002c1920420b075041c455440411925191070058038010b00c030403801d01d403a801480078840c0850800030312140c10880da030f1004020580e8000391004e42c0c800400300041e80d4403001101040a485002424000c0c07504043c00090040d0340820b0302c0f4410303400307208912115101c08003000020340302600c11740e12980a03607800780400b41c01d21404601c048042c00038008074800f540c0d0b8040c21b40314940d020750020b0355128200665000c01d400307129540068050130380c0c98480200c624807200e020152981d6040649128180c1e8200ccc0100b5689000d4040307401100d45554905007222190343c02802040c040034181000301d0540b95000442c01c0326060102c0ea03242c2882102400c41c0f00f079070000c01d480c001300086684006101381081c0440d41c060f5009540301d540703205c0c45c800d240c1511000501003103020b510402c00c14020034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 318382823 1250 318381573 318381577
    0x1f15030e0c031b0406030c03050c1002120909070c02040617071205030a03111204061a0609010806190b030a050403020106060c0c061d030f1c020f03070f03091205030a0909060605 78
    0x4000680c2c564465a640c030104e030050825820042c02e00c2103003000401409400146245190400c43e0032010b0050010002c07a00c0e101401c0318441c070020305210000c044d250108140c2c0d4408c0c030f186021035411410360006030503200c5aa005410000d20f13204002803c6509008a20141640b030b25082039005295403038507906e02ca008554010075654500140c4411035100c1200c3c00d16642640420460800741451070003032002d400841034490011220801500300b24056842d40c180584071040d6980e690014408004002240010100380180010883c18101c1d00a10300034035030103500040601e403a180103402c40300203800071024081c0c40070b40c90000a564451001c00d842492400d0090203a00300c00f44120038102c1001c803070b0306010b005043c50a502d4001107d1380514088210243c5400b20743c88180d0712900c8802c00550300e1b42041080101046d0b140305001d0b01c0c0c0b8840e00c0d046820030744d1903203081035030280120101c406410001d0f10340b41c141e5000b24900090b268540d8101303d0b9524210000c1c00d18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 318384073 1250 318382823 318382843
    0x1020a031d06070c03031d040621061104060e090105030703051b0d0605090a0b01170307110d1403030412030c080a0f0605060301181505030d05031f15030e0c03 70
    0x14004080e08400070381c5a80c1d050700e920f2640001c40300d90042c2c0301d107000b42c075041c8143e09801c0d801030b4148007807265140a00940f412038584205500350a0034120350701c032000c82c1907002650307069100c07069000301c2248000208001c05056640300c01ca540e81d03404000b55000103034013180c8207901034181400030820101312088a2024505941246400b02c40813031440c0c01c0c145405003996103000d041228142c0f010592a640070b228140f4174240d0303031b00c03140d06512b5182131403000d0700e056100340603080c001524802c00d0045004018000c000700c010540d5120b42c0f4500c204041d069a40011080c40204211020f542603100d030681001e001165010078010b1031001c0007070681c031210740c42c0c0c5c4803201c140500c1e0b4008400350202900c0e4595940c4c40d49610b510301c441981c810f8244a142c50710b101d1036000412040f90554000402402d00d2400401c8100d9032900301800314034014020340c0c21002440d040502c0d150041a0000c1c40d00c5800300840c1d0054120380e0b10099800480c0c0142ca5042c0302c0d03aa02160540603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 318385323 1250 318384073 318384107
    0x902031e0415020f190f021009060b060d0902011b0f030c080d050c03060109050d020a03060207020a230108011d0103032f03040302120304030f0b040f150504060b01020a03 75
    0xd240d50380d003051090403a100340005015440004c5038180800c00e40014010200801c114004410018404440a081c0c1031203441c0141c110204a802500b20b0741c0004d52150700841d40031070540100800111298450311704c2260483d950b040d01c8085580081206c0803003442e00741041c64024641d12900711a0030550002000c00c255615018200078144080d9031013100440c130100001e182c0b01c611840c6940c025180140810145000000d440c07a1041258016581c06000e600c1054616626080070b5086007000726440603151002143d41506c100c402c40c81d0191283d04502e501c00528009054108103800004101801204007024240080700c0241103d5240c5005004400ca4400a1805e0403500c10341e5072100e620010168400c03c8000701800230703203000300d1b07100c030b40c0d090700c041485d5803880b0300d1000511501c1160500d5011881c50b24029511a00880c020444584030b41d80b00d00700610002c0c030402c100d170398130780501c024030403980b0955500500a00082000040c65200944500c0810340300b116 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 318386573 1250 318385323 318385381
    0x90f0e070c06020304060e0c060f0f030a18030305191a0904060b0d03020a050114010e041401060b030f10090203060d08092803030e0d210c2901090203 66
    0xc0303108400c00008580c00c10000c5480f03003828580318014020891245003103200b005055140c603c1c042007107e05008c00828018504609000d240c4210b0704002e01c3c1506079580c032900803155215008900c84514800d03900001c0e9440c100000303181a05402001c840250300d4070303c40c061004000c144140c64420304444200381d542e00c91074800d001d00445444d003600444074204500c20540c00003202c0900d039111304024840d6a60203101110141c00911805030003021280120340440d41c107480d1703466844000030021400e103444003440c9256034800c1c1c44442c03c981c2c0d64000c00880c4105545044080e003900c00007903141d414050005008400c07c400d01800643c03001031602060780d00c507031501255050304504c20100c01012950880120428803003034010814030300010409180c40e140d24080305500c00545100c40c003500884030444030010003420244803007084003a004c1100000011501c1a0304102c3c8640401c0e4031200d80d144110607800003450600600501041c40c0800e00695803403280e44002d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 318387823 1250 318386573 318386581
    0x60304020d0c06050405030c100f0c0c21030e0108071d0303090405070e0a06031401060305090f10020a090806040f0b04030c080a0c0204140f07050a022b030c090f0e 72
    0x601c500c1c5010100414110350780c0c800244107504080034000b1540c04605a070801080141030103900d031440303540200003400102c20002e1242c004d03488c080200b0300500d03107021182d860320928003407a04091080c000040750303402540101548124400005042032901c4081400c0c0104060000152405910b00c1c0015950780480d441c0c504009949000b80010010f20440c207060030007600b403100d4061081d02500044c0b00100c0c60741e000313000d25424540480305111441e0b107090340860040c40007400810440c0200c80300d02c0100c107030401c0711141004004000590326902a00d0141140c000d03a4050b40060708000d041002080d509030010340555040510140070360758610b401c030345035410001c00424001000c100d07200340f981d0103800201124801d136010003003000740d4001521810412900d0310460b4000c4030004000910039030160440215030f0040301c03110284001c844405802c61650b2150b0745090b0030260000c19414000d00310440150700f011100c06041c10107018034081e440c000c903a80208004041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 318389073 1250 318387823 318387829
    0x30206010504110c01021908060a08280615050307080c060d0c0e060a0c020406050609032505030312091204031a0405120309030306040606110d2a1b1a030606030402 72
    0x4600b5980d421001b10b41c0e8400e141c030b81c402171166141c402d1001402e880c000a403981000f4a24606907042c0c1801025211031215165080302e20345003c4602640c1503e000748001a02401600103014441d468031410b641007800b4940303030a00907404516a0703402a6032000d515114a0112540c1e1003181e44042800180c4a13030580710380d40c41c3e00549400c80c5000642500345580045d80c081e04510882b000d2000755034510403c0b03460701424003802e5264000001c0c440824205400e152000d25211401e885125520030006e400d54000000d40c0400c1102002000f512520038419620719000c0c821041c1e0a041c110b8884a4002a00d50f0200b040030143d0b5003c6800e00034200210907a0030a18480303641c0e6490000c44240e1250800c2c0e0794a80501d050050126040d405100491072030024040181190790300e40c00304450051540781c132000300c8202e444041c00f81c0008808002400c0340a0506440e0ba8202480f24502000140d80038124811000c02c1e4000c605480c98200c0e608440211005500c03510f4034000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 318390323 1250 318389073 318389077
    0xe0d170c06010608091011040e1513020703080117060c21130302010f0507050d0c0e04020a090509070e060d0209121506011704020a090c0507050d081b0703020601050411 74
    0x1103030300034030903203000007035803540001d00131712460a41d020fa4810788010705401c402da58400e690452400c800b840b05108030b1617004500c952015511040704c1d00082d9420110f1144400b0783c40c4090a25000102c02c01456007010341230f80100303031515400d0080c403550450342c1e4460001170019a00400005a0030320580107400300701e41d0a0500912202d910705080808005034509180c08030095428000080421041849218030480c00340d12a68581400b4105000092400068403424490002040c034005e4460384058480c1402c2501e4894155003480100107032030341e00030b00079400c10514480c2409240c4520b001c1e90540882c00d6405a1141085030010350101164a8070b400c8600c180202c0c403006030704002030a4021b000a8a6128a02540c00c16448030004110303030107504581703d18010000100340741d010a848944501d0100d081860700d950715030908080c0d501c00000686410b052021034070300701d5040e14006c03414020701841c1c080243c1d0080d45640c0c051260a00c0380c1d07928510310b10416030240c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 318391573 1250 318390323 318390337
    0x3090f0601060c030822030f0c060204030b0f09030a020a062c011b0e0f0d0512040b190c020108042406030c081c080408030c0d050103030507050d0e0d17 67
    0x4103580140da12501c00078820201e8820136800034680d074012940c0046c2c01c43e00301e80c0c0865441c84556550206031415903801004103035a408001d410072070400407541d640f0181019504ca007158000504003070751103034201400900300062540040006151958000440305841c940c4660041907007680e04000b030140e21209400f00d040b4640003c64440780d250103500459032681d0040300000011440241120718089203151035400188050011120b480c060718a600802e10841c100c460050480301c0640706600030342e2180034040703001320316002c03000800303100c41e000c00300c0da85002c4504000320340008000c03c03030207800902011200042c84170080c0000740500305445110800f449050394910309003800541502c155802d60045030290007050004e946140d000344241d682c3c082e659155602c581d88a07500251400d148002c0800c1440250041401380500840c02a240c054540e003881c24928144102d103123480e402c02000560103241d82e030b41c5110b15400c164104840000010120009164900c1641 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 318392823 1250 318391573 318391603
    0x908070b09010e07080106080304050d14190302010501050402160f02010311031008060f01060807050a031e0911010315060507061e0e150c1b0102130b030105330309 72
    0xc00304440000c054008456100d402e400700c4038010f0740c3e00714860881d26680917428161b001000104583e28120034000c00141c040d6040320320380c0001c01500761a00c0f40f80031001e51a03681c41da140506154080c400c45004041c159003d51601c03100b04280b00030400d003035000400c0d011803aa13000c029a4800d0380700d48015203103030602d01d0b034070700b81052a06244d82983c03003444c0c160f101d0000050400007842540d40d04036002d507120701000d038481210950340b0390002000403040599525100b802c00c031440b1580b03206a012070000040c40c8103981025079221032407c0c280c41c149410000b02d1810400740c404941c0464080d0b03c0c010751200813910344007001e00003104d0a131b4401c4292a0380d440c1400740b950700401010030f91008440b505050200f4100c0601412608680300d0318040c0500d803640d01d5110b403203120078144000010700d0504c21048041e11510590044416150b0100040c07081e428101c00000041c5078030b80c090000e0f25a000e1890070f07600030307005890421510100c0410542102042402040c810413 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 318394073 1250 318392823 318392843
    0x403030c15050403180501050405060a03200f03100905090a0210090504110c060f040b0a092f04060b0f09040c0903020604060503070e1008060f1212190e01050706090807 74
    0xf4113009288181c0403810012414072a1000540c96020b0401c0781d0446801034045801c007245480305800500040c032080000180d02980481441c9401e002800c0702503580d80003035103034102000c0b043d03000c0c44035400130003545203071105001184000080c0b44d4481d66045071480404a81080c0861380e1071225800b0035003203800c00c0b0720300c460103031048050078008040b4000c0301d4050341c4000d0002c204280595018001c0a54000862000b0446030810301034a070040d040301c2591110362500c80d03002100d010140760815860b4541145510702401802c0082003010005030501661002c1c065080c400c0f81c1c9614891a40d80c903a091b200c5000b00c01c05001103030010003882c0c0340c41d0b5604000e02654002c941000018580c1154100140740808408035040001d9503090080d9440340244400401d0103941a40e200715400107100c080030007002603440a0190340078040c3c413a40503000404c0c160700411144014850700041035001a40d008045d912055048a03011410750f00da81003001c034030310a00707034050949400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 318395323 1250 318394073 318394081
    0x6102105120f04030614060a0b0d0908070516050603280608011112060d15050403021c020705031603031b061e06170c060405010e0315040c06021608030403030c1505 72
    0x414005081220700a2030706000035410104403c1a060b01124800d030b03c9079142c41c0c01c9c424200064085c100b188980040015100318540354070110740c000341d400b2102c5601246802030110001c0030394800400041e03c425065042010f0f1301200380043d180d44280300e200170f800119041c050b5030419402087c405008200003d070110103080700e54818101c0078448110030001c40c8160804860000065170018411320124100b1201003000c1c20014006070210302c12010b0501c0c020800144402010401c0e80080140e50b203440289402c00007420050440340d6000d2104101098000048000348402070460048007a5a45401d0006014508400070b40c031621038014269065103602207170580e1031850b2000244807040360310b503646d00301b00c440664010805210420041d4001c41c514246401c9c01000da8a0010540b00b04420101048409684034042480c0400a82e50180310080500b07103110000d1284500b0500700c071340c1e01d1045100c01410030079040702000c00d21014441c00080010f0306201806103041c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 318396573 1250 318395323 318395347
    0x181f020d120b0603040819020604020d0816060e24150d020d08030411120f070501080604020c01051627062f0a03140a02060103110609030703080c0610210512 69
    0x301060161b40f007e030f0319000c80c40f030600000e503007481703941e000b420804004d11703d03950a0241c0e0001005044004c86080080c4d0028507070740280700c8055242e134014060b005841034010200846800d03c01c429044000c180f0200301c0c10003005929140d03040c0da00d9000543c035440860041162441c000c0c10061010040c001080b001041c1e00c01c440c6400c407054081d004990b0006a210480b62000640700d41c4000020403455008d0360285a10080044c00141401c0c1c1010303c0c24252502100c4034440c035800d12940012007900014045004062107403150790851820000c603115400e940030b03480a000d030381180c400489591450084070380300c10440b200c29041c0c032281000e50b10070a824085000c0381c0d100e03410782c9059a629080d600d554403654001d258907440c584941e1207001d003021070b080e0070900400c1141500e0702e01700b10120081d440780c0495a80c03138455081d000d00345100a080621036554443c42040000303061140c44800707501c4016009000689032514a10b41040301d191824810300c01315003400615 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 318397823 1250 318396573 318396577
    0x1101020304230102150112061e020a0302120c0306060d0b0d062309011a09060301060305121305040501030c09050711010c05090a08030408060117070308181f020d120b06030408 77
    0x10084c0c0807215000d01803d18000000002d0049428401c81c030407603140802c3c05600316041802e58031410500c0c004d02054044103030381c440a160710120380c001882450400f5554461740d0300036600030301d80d420341c207180c400504280700f40008481c00503240c24042845e540da98000c00ca586a00001c100320050300d00d2150b03803508000441d85a0800d046000103049070a041c05401c443c0c6e0014200c484200003003100308906103001802e5640c00d0340da41c00000c000180c040001d030803018040c82c100c0c1e4541c0b1803241000b802c40035030303048540128100310041000035a05103e01c0183d40c2582d01c08a400d1b500d4900c100e402008420702e1501d90f60801c002860380e00d4105004044001094031001040c940f10020b10b0390b6442241b10700c1c4071552040c00108410440c42c000e4032203c021041c00c1e80d0f0040d50701e0b103d4039016004521883c01d80020403060b0b03c2c81d03280c9441403d184c1081e804101412040800340a91101d049440010a21045000481c1c10303102d0766100304000c1100800007905c0781014207000d003103a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 318399073 1250 318397823 318397889
    0x3091213051201151703130b0309061005030604080306011806083112051902010614010c03020a080f0405040e0a0201030c0809030403150204050d0f030305070c02010504031101020304 80
    0x10390810300b148a400307901030158128040380b020b40410000d10300520b8460b040d041d1084081a0b0000307024440c072030341c0204003100041040000064580c1010000c950501f28040c01d085941d0401002c2000f2640b0b000c143d5940c840d802c05606522907440c08010396160001309141d01c83c000f600c4c1c80108115402180d454046c5a0035000ea20300b046200b8240420108180400d580c10074081c6a40702c0000c103021b0303a2181e038001c0b03843c0c42c500303108418400303848a0443c03021480250751035a8003172013000c041d00601a5000000d11700300325001d4061301c0194641041c0360018085c441c00056074103c1c01c6811089400410000e041080381100e0050000d0300e461125904034000707410801c1c549410742c86165254041c405c90000380d454a4607590b280c03809400e0030700c000e0860039000c0c480010280d41d0560b0126019000786508450403141c4d00d401021990000d15034002e010060750740700f0260368410240c0f001d490303004641405002d00e100042c0e01d503001d1035100d81280c1c00b0b0396075010b0348030b604c80401c5640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 318400323 1250 318399073 318399079
    0x906050a0306120f050601060e060d020723010506090a0c05030a0e07150203070b06100906081518070825051309090c090b06040605070f020f06041d01050f01140309121305 75
    0x101d81d232030f1032007294503448400409511040510420504500340d0f40101141c5214000c240c6c200020340e01c03051084601d030a1040c5159540302d041240606180744c002d54403000100c010002501d0522014100340800f401100140756600610001d14000308240300c0584103501e150f0070900100a0020350f80d91102c1812600710020801182a50800d200c85c0e6030355540c280c17200911181081401c9416110041401c1540e0341040c590710910380b40e6591200b2400700d44840564145808a8040c001e0700010b0b12031085011028200d041400c40240c00350554401841e00302d0391040c00030120401c0107015000103211525049047c3d04202420840030203c6295803400e10a8041c2c000c00c0050b14015441004045001042040005280c42e060302c4600c9100400d442080c011a0b00400d41a03001908030101300380c004483c4d40c1c81000b50484460062400b2103441c0c00000344040004c00400a05001c68100100807000c154500c0c420b00883d90300754140e00c0c0e05603c81c03021001d211000000da214030b0340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 318401573 1250 318400323 318400333
    0xb15131e08070302010f05040b033d2601020a032403050606091f0303050a180503031207020708030307030f0605310608100203010f06050a0906050a0306120f05 70
    0x10084103005844101c5040341c000d4560145950015101d6010b984a101c2c00c022041101240c0e400e200406140074000124411034001e198403600c4014906080400c8555002c0d84070084101010702c035000162107070350f0240c1c0c10b40400666805403071062002050840e50001c01d100c442c841e0701d035004907218502460b10001800e00c20141c504240070500001d081f90b0890380005016040c0356848980200c107107040c6540202004201016600e01500101c0c006540054450190740d03004840c0324507581c0c00040301c0413407480c140000380e0702e10a801803c80100c03216000078000d0b41c000d200c824002c214040a5030f0703403854444d100400600280c0410b404207864078001082504011551188408442c100e0b1a1500464184a800012801040c03200c003030716500041790b100014800f100005c044807002580340d504009024080505913045501048800d00100070500d5000e071480045401c641400c643d1524a00c100710702502c400e400000641020480314010403039038008483c0c5050180007995 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 318402823 1250 318401573 318401609
    0x5150328021b160e09123f0603010e031204020303120106020c180115030b0609060a0801140f0108070804020409020a03030203031005060a02070501110307140a03020c030c01080a0b1513 81
    0x904c1c4e240c800d60300c1c1503041c4d204005982c10006003030004c1045000c40340820a81c602281d450340366041d144019413021001307061150015010501d48141c10000c00c6000340264440d45070095601d00484486a880301301010226003075403004c1c011a000c1e010b072031501e684251b03103a0f94040e54581c850141e0501a80301a02c07400325404049013201e049e00c011000d41044265518011006004010b071296440903080000700a2a41c44800801064040c4d4503500419803401e0003414502e08103038151030261f2800c003840a81070780c1c0445051380c00f1045080034170749603c4900202d0002c02503104001d4210b0248070001c410b040e00007001d13500c504000801c0c41141d94459091140d94003548040c0c03800340c0d100030010302c890f41c0074119005c2001006000c4070300b483c1c210740f41c5050904c121010400070f6008000c08009269040c46802102d19090b4000c2c4041d40108000a1504400804142c0b400780d940e04151129640c00d08006550080750b000709440e141e44c01038018131540d2601c110700d0021140601e40e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 318404073 1250 318402823 318402839
    0x4051f090201090b032511070506031e10030b01140f01090503060c0d0e0d0c051204050f040c030b040f0f0c020c0a03080a052205150328021b16 63
    0xc805410341c103a5800244502d41800100c0e50f801c050100000f1081c41076030340d811600c50312400c1c1c103607003020f0769100082854000360030300f007c0c0550030207402000e00b00100900b829500c00050000c0c01c188106100c1d0765a4200e41543c00c00701900010071160581d000056846402c2050084840080f5100100301184c500151201c0c18107206558042d0840d60004802e4030301d240240c5600320840c0c2e00480e0400d04a40c0c0103040c118900511008503e00300b40087c1807182c200514040714034880d1916103400d080c0320000d101d02401d214840d10a03615a038130030603060b20a80160000070700180c428081030301c2c407003041d0b0094000d03c04c1c16914203103041d2411f066280b000548031030003400900241d040754210b40703d441c12940108032030001e1080030414201c8110000c1012100c2d20001c0c9102000c0302d04110402c6840080040701152600301441800b04c10035824441020100408042c1e180148600c000344020740500c5d01c10006006020000c0035401d00301055811007441c50880c140000c980324190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 318405323 1250 318404073 318404081
    0x30303060108040b06030a0c0f0609082b1119051b01080a090c0f06051c0207031d03100608240907060c11060a0509011805030a0f081204051f 62
    0x400c078002100c0381c0101e00030884d40c10110340c0104002d42541e03110030300c1c0c0c1c4134440d108440741d20000ca92900c16004001d6554441c40603400707040e40310042d103440e88591441070404060242d128011052a1200b22045405040010100c81141042d1240382c1e038030110900d540e040020003901c0c00e00400e076801c01c10044000d440d8012010584400120742c6a0211580040c200d0030340c102d88140e1440400700b00700d000303a014070005140542d603203956420000c000d084116060050017516a0040c4080f200094000003040035001c5040503541000175404000780c176004183c040f0154080c90300ca00441c040d140030417201420300c1b0f400c43ca01d400010243c13409001c0784003100c0000b09178100c1d94051000c28410040c0130082e600a0035035420608510000030310941c000b0781d41c5c030301007a070004140c507195070071403039801c6541c1001c40460324440c50140030035122440004d00500c24004244003030100035142d4103880b4212100040c1c1e101c1c501d040d1070480c1da034006c582908910207a562504081c182103e0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 318406573 1250 318405323 318405331
    0x1020c06031006110109050601030b1905070f30090212060403051b071a0408010e0a0b0c090102010f0c05030106180b04050915030a0303051b070506010e0402030304030c080601060e030303 82
    0x4519a091450700fa02280c800c0814005001c09540b5414001d0201e1000c105260207540035000440c21401d006640e05881c5051030444540e107400c010401c2501600710b8440840303520241000801019040d43d804680b55000003900039500060240e00c61401c00c3d80d100320750092080d10011100052043e60540e00d810440d8000c00140c002c10802145264401004841004007011075006a03150404044091250650011b0415000c80c04000c0c2c0c900900804d21602c018201404682c0c03156143d0b004052001458071491007000110742075036900c02d51103203580d410b48500801082d01c018100410661082c4115800140e0903600e1210102041080b8811109640255480c04d454002806002d0900500364002891145803092880c3c8040c090946864425034000400340780808800450302c60039040c8454410041c00344070b0000300d000030614155092123070f855890707540700e1001a1540c45241c100402310700401c94001a003941c0007550700c3c16140643c0321400750003441014155a80002c603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 318407823 1250 318406573 318406591
    0x20c0906040c09030506040f1e0b070810051f021203090d0e220c031107080304060e0c0310020a08012111060c0d17070905031e0a0c09090201020c0603 66
    0x5008290580780950200c01505540d0814a040d6582d81c0c80d850306103902290140c620350600004002000482003101c02d48416208908101c040b02d03840303402c0c49103001000c10003400665000700e4080300c01c9030002001024002c0a080d040c10301c1c581c0c1c0000e80c080c0400c04402510464104803c800c07401c45c03d0324860860340c4010080810406004c85081d41590205030300105402c20441012292030b41400424a000c00d02042e5034020703d4006048a06651604a90302c1c028401940065040011130f03410503009080441c0152000400d00c1c20302c440c04414a81c14401c00c40140883c1c00d6603005011320420f5038450303050507a0b0b030f0041c91001c101050307040d8000b24200c141280001d02504014203070000054401418098142c0743c8a142004c2d4000c4000851a0300c600007280c2003d03c00c207207500c07807405d00d000c1e0f02540c9001c001c030307036180071182c0303140d031132a000e00c0742460034100400402802c00d8000d4100c804550380c48850390300400d40058241d0050146032001341403400c00768112070041c2601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 318409073 1250 318407823 318407839
    0x10806130609031b060b0906030607170c0f07030f022e0c0207091113050414011a12011421120c070f0311130b09060d03030e0a0b090706020c 62
    0x765210001418501d00071002c1c81803070010b02114802601c03007214614402c900c00201d0003820401c1001c03498000705003a2080d40040200203000e64007100004d1220b44103101e0307408039114220024018091a40780c1034000c00d0100b801400e01d51710018520703030300750a9000d85440034403060032080032180500e4402da030b10140081240daa52404e41c404540341580e071040c1c808035a114100d4205a600b41010740380c0b51000451480c84520300e0503216001408101c4e010041f81160390300d006010380051280451411300e00500c810840c0ca010102c40d0120011003904180c1d40e182c032010220110f203070b042140550f800004182015103411014400c4c0f04210300104900365002e241d403501544140d41030a618000c0c040300190341e011803008a405035208500700450700e80c86400b807295810914903940045824000e240c00300d900c030a010f41c1c0e007000d416992180064068101078018100395002c4901d5441242102402d11882c913008074055500701d4140c80f0f04a0703803903008070b90740e402d0303284807540c0700300d00b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 318410323 1250 318409073 318409111
    0x203060609090702010e0703051c030e122a06010303110a020306011e091a10050406090e040311030c06150f0a0b03060d080307121b051215060d0f05010806 68
    0x1900350326910003c54030000c285452440310060400115a000b190307070b81c1c00720860b21032400c00e241500031800c1d03941c6030030000ca502c0c0d034000c15507a00c1d106000903003000000450380c207004660841c074031820400070003400c10707030740c1a840c0195150000d01c4181c0008032554150f0041c00c1c40402e040881e50740040041490f0790800100349501c4050081d910229080d0041c0003031441120300071043c0c80564070b00e0010302030200d441801013401c000310f25801081010081880300641118400c0141c42800c081100d69035614a42030340c0c50f44203110f444605100c041258100650000b40e554411984180510b50f03c8841409003c184100402a01d80c07200300800d0520820310b4450281da8002c4000300602ca10b1540d5480f901c006600c2a01e10340009402c1d00b81e64103800449003e81c21032070141046100d60800c0d403000080040c0200c0c9108003240500c41701140c07488018005600d89040010722203551545a0a1b62000524500d115143c1442c1014000100240b010070b405100c0c403103a10380c0d13841c0391103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 318411573 1250 318410323 318410329
    0xb0c030918010b090f030f10020904050702060f01031205090a08010c030f0203090c040f091b060e0d0809010e0f090a0c1b02060708131e0602010e0f0c01120603171c0203060609 77
    0x510180a59010301c51221f40300b89101d810818160303034540300003006039500080d078240701c20340f080108460195401081400b02090003186920704403900242818100c80082104650b0340c410002060350058500c2d0300464041010350065484d1000c80e04c1c02c01c10506459040b4090303010807a002c00e01e81d00140c40f80241b40c281508a0081005041c800068444965880410a42030744048500526018a0074456290001c00d12098900f003258010302c08c1106039144d1049100315500d1504102a440c2e5116041d00c4800c101d02500234020800422803138030050100c0180446081c07040000d00d81c85c900c2100d250840d00c908100c64001c2c00c09450440c0c2c54940c1030441d80a180d40b001e040126171000108543c200740e601907007440300300c0100003491525000a0a4500803080d4040d141c0001000e0010761000080d007010428080c20004941410024004010141e0758405012039884002100207180e40782d0080c14050f020441441b1a000c110030312408a0104940158000c00100176002a500d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 318412823 1250 318411573 318411589
    0x3050a1404150b0f040911011211040603110903010501080d03110c030703211802011202210c0706020f090102070f030b011e0312021b0d0b06060703090b0c030918010b09 74
    0x600501310001184280010808640c80540140e90b155419810940e142d0390242210340c00307100350002031191007400403221036a407046108850506d583c440040b0904900e910940d0650003009000308620340c1c0d681d2100d034903200c642d5840c0e8002498000d07032942d824108030036240345504100c01141040d050b80d50079640f2000040641d00c41c2d07106c0e1524658100614000e42c5c22044100e403081803100444c0c8000760401d07181015840d0103138014032203005030008203002402c040c150280422074949440144c80400d100b1613001610040c000600e10103500b02410040868030000ea085403100d0307076540902a6981e41c2c03800000c00b00d41120300108000d0028010400c41030003802110000c441d9250b0f1084460507030700c007a50015801c9450b16001d41e201101e85800107883c15a05803007016200c1ea181540c46800401d00c0d07124000114070a0180b620401c8000041c110301c982841c1d80c0d0b0801c40c0c1c0c90b42e40342c00102410b40b0a84010b00c40201031155003034400d04840c0d07617038485800c2c2008541000050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 318414073 1250 318412823 318412841
    0x2100b060f0315030106030f03021b011b1101051309152903060a0e13020f090c0706020d0204030b1305060c040506181504061d1f05070512070303050a140415 69
    0xd917407580380c040f011230941ca07004070070507100303400400c0d00f0324030021b58500fa001c00000003810b11554051908040b0350400d42c65050660150580041c0500d007801030b9194080c102c80c030103403000c603800c0c04500440b0640c051076502900e40300d40b112043c1d8800401140c2e40712000790319002108507141950401c081d07030140d030304414010241900680c843d40b00240440c000c84840c00c2c0d44400726562000c1d82812a094004050141c61401c12483c00c00b0b0f54100c0340c8074081004004d6940090b400341e060800d94180c5d0080c5500c00c0d09201281010b400e41c22110070045030a41c1c0c103019010115001c400540100c0d000c8900207003000d030420080700d0a111803201842a0b03035820140b50410303c0441c0c5205c50040026117995101c08081d20000b052029280b826030b03420700e00511880c0c401c850440c0402c1e40800d0100518601039940c0d13902c51400318200111008145245400480d01e06c0030981c00d070b003002c0e01c01c040030300f410001c082611001c50313560700303041d50b0180900c0041204018010059003108444c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 318415323 1250 318414073 318414079
    0x110418031d0618040c09030201082e03050d1101051021050f0102030a29040e03040e161220030703060b0705030702040b010903031d0d060c02100b060f0315 68
    0x701c464800400c0300c60344445025030703882e0f00c40444403400f072030584a0429004201e1800d6a0100c1c1554006007503400043c1c12030000f403580148440c4208002c1000c070504580b00762124440542d01c0c030b445c0e9501d0202c0341803200800d15048060007540414420240b141032201200b22550389481a02c0c0c1e4001c01c42c2d0100841d048154042c2004a001003220880c103641c60707400140c0d0392400c030a800040300c6d8001c80a040b1050501948140101410141c0b000c1901c115000150320303001c0d08501c3e180d0b200320352051760080140010003004101150300200c401c6001d44690044529600720401100c03c95244004040300c1e4034140e05c0e410521074003031544208941400a4110744440981800b60003100085800c0d030300000d035050460a05000380c002155081c244680114150f950240109100f1079420b041c0031000035054400b075440e49100500240c110b48104180310260600940358506844590300305810074540840030708014080380e90500f5200308603030841d100c070300184840d40b0354503d223364 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 318416573 1250 318415323 318415367
    0x6010603020714030c07060207120308011503021b0d080c07051b0f300c060d111213020427080d09050f030a08090c0105090f0d0606090911041803 64
    0x10850000c00017041140f0140b401131040d42c0c58510028036051464124480031496601440b000903082591141510844100b100500000c80303402c030024014403480300340f03194031b82900d05106903022035075444210a540c1c4020042c0d40780d04d1900d42074481c4120051241e8441d5544004c42c00008c180844080801066401d11a6070f00c8001558115103070208400340c0300300c2c40c4409406012079000703004254030380c000e0080e44059500040017030103100313083d0802175100d242c0c0c00c14003c5c031030b000c448848403140c0b2102540c0c00c0c4821511545900014101d018903e000003500c42200100c0b440c4841840e11580361801601a540d924102e4004400e400c1600340c48130170000000300d01b40030503544003174054001c580300d040b0f5800013044130b4009015000d0300d0b0041c08103035660382d9004c021a81e8224040c0c3d50724044100c0b0401040307140c2c40c810405084c5520306100880c0c0f6100580018180c0c1d40503902400c0e48000c0001000101c886600d0070450301d040100304140080d014401d1f000c0d410007070f01c2c00e9038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 318417823 1250 318416573 318416603
    0xb0a0c15050c22060818070b0f0301050f0d08090d26070b0a0b031207081c0f0b0330040803030708010302010306081c0810080f06061c05060106030207 66
    0x100c140c81d0300b998107007a001c1c1c001c074145041c12103002600000c42461480441440c1c41d01e04080d050160103403c2d4103110910840c440d80f41c8104000300c0008040c40c4020b10303551034a040230421107400a000b2035100300030009202d201361400001503000d039074209200d2854016008100580314034004400ca0b0070080c06800d20021400c0000d0f020b00c00c20523a07500309da880c0318a00d00049100c50042ca4600701524000301c904bc136440002c0c403060340d07004030341d42590b443c0034a003001135582c0501c908280380f1644112110740841d605030010400c1c0f450240083c041440001d0816489222024117100e031407240401c13410100000030b141c8440d48808842c19403409440e41045030a541c01105d03004c0204408100420465074984654002040d1480c05440541c15020900b41c52006000034001007041d0500881c91035821070003007200406903d011109000c40c1c184041e51075041c02c89620b0702c29500007610f0304007010303003407103510420fa4403401616181c4e080c908150003c1d00100d400f541c3c81c20800010b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 318419073 1250 318417823 318417863
    0x702010b0a0306060f0b03040803150a0806150a06141603090b04030b06150a1b030e0a030c08070602060c0a03020d090c080a060b120c010c02030c090f010603060803040b0a0c 76
    0xc01c003840c0030740400b054a6050401c101d407900400c1d4072448550700301304104804584842e06590300800c0b5040c2c2642c01450300c10000d10350602f181c01c01043c0e80918030900c40884220300c40300305a69400c2d9440001e4554640040d030b9000c0c180403400c60443ca0800c100c243c1d120703164103506801031183c2050491a40c803607030313609920303001500112041104442803048516003661740d0034500340c400700b4051520300e80f508010b21180c2d0702202d42c84048811000740003050300404940790f424034041c20503020760fa9a42448214a0310030302c5121041d001c1c0101c089402803011076180d20403080000c69500d4507441a20890096121002c1c011020b95540410800695150907281c000d243e200700030403208181d030801c1422915070a5a03a8071640004030146502c0c0000308643c0041d45003406c0c1b104a0b01d40d1800801d080034800a91590700a40c02c10400c10841041012036042c0d0b69241c0d41041410b07100c0041981d2445140070702e5540107418040500340038030030385403844682c0c403d90305040e140600040c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 318420323 1250 318419073 318419089
    0x30d050d02130f03062405010305090a140307020a09090b010b0c01200a11070608060d0809031c08100605040e061f030609150b0417030c07030605010501080906040510050702010b 78
    0x1403c40714000401001807140c0350003174010b402088020421703500c2c2d010700884400b0605101c1e403410b143d21040000c5001c0014080048016085100011400595400c2035140c0d070052600301c0c422a05c0364408210b80c0704500c140544140d020034070410507401c049001c0000e40100c43c490850390b41303c041c0703018026104810366010302c00c4c501d081d503218000c07468058800e6280c902c1c0c00c000c03640180350410003968003080e5590031200c29a21080c0740c9002d800e004000384200003c89401d445001307403100d90f0003014002c00f102e450302035880302041c2c0c4541e46461000030f2184103210024000b40024000c0050000c0b02d0f5800c524010a50102c450155441215098584000340042031b40d4020400100d80c0f41c0c00350032010094200000031050400e50401440e0240f40206400c00d5041080c0b40d00c000c40c10412501103405101c11514079070f13501e150010117442d0900549000811090100d104000e00040c05c9003c2c5510102800608548100310130040500030600403c541d00d82d0090703103050301c0d8210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 318421573 1250 318420323 318420329
    0x603040b180f03030609010603050f04080c030409060f030501230a270606090c020c0d0b09030f04090603110429061c05060f10021009110a0b0d0c0e030d050d0213 71
    0x2c0a15201d02d0907004000031010168441d409050502041210644031090110390103a42f0000c11920303940004e5440e0300c0d50113542c2101c00d010b4601200030a401ca41000b01d0021280304000070710105500e480f40c034481204032404940382c0d07040d00300420301a00d41901300c2d03512444084090031241e0402a541d0719480b41036402514201d50b40c0e0000d202c070525074000c44070414840c3c0014500e890840d404585080710052001c1d008200d200f0200e021100d0038001c0314030a14800401c55111904c441e140002041e0340d10003100c0d5000440603400503070405010301e01c07074400b0309070802f100b0311142e45506400d02420340c4100c1d070216040081c84000d0501e034003020304048540c400090f2910f00b0b5000e0100154001c0c64143c8203603050101c4043c207550015179089000400400070a0a0610317281c0014624080c103812a03000b102a000070856083e0034000d070080005280062200c0d110f840c0301038034084d41ea441c100e41c05400071585011070b00d0144009102c103041701000103151801681c40074142101c160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 318422823 1250 318421573 318421603
    0xc1f090c1e09060614030c0d020a11150c07080313050607021510080322050d0f0303150b030a0c05090303070606150801061b05010e070e1b04050603040b18 68
    0x101000000020807451032002c0e0040d0241049a02d003841c6014040c0a20100c0c0c0340f0b40308070000000707001c0302c05400584101011243d001e40d140d01040d00040c0c103081d4817004810544c4181c0e50160103503801090024007400300400300d00d1603d0019141c44000c2da00041c050034004501c403c5040000302c003007110510403292a8043c0201c1c0310032005481054202426220b0350440203841440f8810020040712030b044030349903044507018840440c005003030085901540d8001745411601e400d0042d848948818248079940c02c201c0700c00c0110400c80481c1c014090442e22140600c006180744500360701c072800500003828800c0c20040041d000070301d0b47c1d22104085843c113172190000c2240126011010117501c0c4d90b42440e040719030408200414001e1443c600c00070000b00d021b201005d0010039440300b00c45501107802d0380c5500341c541d44150801d000c146d86082c80039080f0000740078a074441c442582c0c10340c0d0004103203501e161196114030304030181c00390100c405007044111100c011f580401102846074019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 318424073 1250 318422823 318422849
    0xf09030a09032021010b010914190807180605012f03070209010b120f190504020f03030a030b090c0c06040b04230105190b0906010c0c1505040306110c1f090c 69
    0x203500b43c1425034803406c04040c180038100009002c01546c100c480d52880360140d440300c40305070380420000c1e000d14095000d0402c5014542002c5a030a00030f150f0480c00441e040424000071765218011120f0b41848000c1c8444964074024001050a44120a01203107c3c400105c23410464250002207120f0320aa02001c0c01201c000f80c2d8504048010f290f80c1e41c0307c800034201600c00c6c40c226641403082903510b00710f9004c6558880c0001c0031561002d110305507000c400b40c01c0347d4650351039480180042c440e00b21480d00c03420080e000130306805068421110303100c0820000c0c1560740c0300c90740d845d8424a4090010ae0749804a181c444c01c41420413082c814000c0b45000004c07605040050741e10110319204058101d495050460520080d100d20740d949422807000c2c80c01d0703031303000800e42017007a881c0c401500240c0109c080186002c0d1041d52010107001034900a1104002491010010245074405c42540003072641101c1408206070600c1040c2e00141c4503c503001040060141d6288000380c91960008000700b00700c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 318425323 1250 318424073 318424129
    0x519030e0f0a0516050607110109090207050309010306050f01020a03110a080f030f0a1118181f080303011413020409180303140601141803150f09030a090320 69
    0x410000200b0208141448100742810500418401d1080840140800d00c2814234001e051340f084080d0b01c01001c0c940811502c4008078501103860f0341c00514007500080c103140001c074040c0b611a00da000303d02c905030000c0c84851041c0c0d806955200c81010b010005008201e207603008100340500801e041d14140900c695a0710f420101c450000d1805020885101e2810041c8844143c0b4107003201c95251049440ca00045100e50015441040700308420707181c181000b00f4000304480d00311440700c0380c0c2881e80441029580394200705541303010902c075400c04030100d4042c944582c00e081111495042080c0c001600e00717a104c0c1d030302c070041d220420900810555035544001c00d06905114200c1d140305410203a81c42c5040c1100001c00281c05c01004103854400011104500046102460a1598040c00380c2344114122001a00902d40480350710340c41022a40c0081c02c3c001c8080100d82c0c1c14000742e00d42500003401c0d1340344c00701e0480c4c101440c0d02404002c440003481b9a900c01302020500340e0070b000c607125821a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 318426573 1250 318425323 318425333
    0xf10090507170109031b050a020f0d060609020306030705010c0c06030c090902043b01060f0306050306040c170a0b040305031929041104090216080309010905010612030519030e0f0a 79
    0x54240e0b48002c106c1404103900007840200d03104202c11f8040b140c2c0c140e003400705000500d020070008001441c0c0c503d0400d000480080c1d940156114580407800d807040781e540c030001905d242c8010803008240c00f01e1141c040c8a518041e60060154503045c3c6403903115035499510440803688190800100307501c954411080c00c40188031045000c1e01a0207049e450a03118100340c1d490040d06000b5101030281c80c00c040d03c5543d02c81d5209000400c0010112401401c2a0034158180720450084031402000e00d0b02131641c00d0000640d01810b15403014449206980755101180e46420284c0700307134005000600600503812480c01440ca041c800076100f031960b800c0341c0a003800e500003059020390045003058000d081c00c204460507503003111401c020142ea100c1120400310703444094500001c0003100040248981e030801540514105071040c0000c2040e142c544142c41860100c1d500003d0000d00f0070410850745442e50680400c6940c0a420b02003520400f20340001d061446c2005035510b26440358241c642445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 318427823 1250 318426573 318426587
    0x4050909060f330f18060f04020702030a03080c1603110601080f10051801020a051c0528090c1503110c0307081605100515030f1009050717010903 64
    0x2116a03810302d020011248080741c0c4070800a200900018507580f0040003075182c0d646050a10000285201005d030b00f445800c0303180c2c85040e1201070040030f21140c02c0c999070070715100b00c9182da50001c004109174070403541c08a40c01c01d0010845e60074035109100301c3e09e03200d0103282c0ba04803251280d01c44200c0d1580003401c061603c0d02c140e0100d911541700510000802002041c002c602011000e808242690b90040c401e0000010705000840b56100060409a5a5100c8060a588002069540d100b1582c00701c02c00c069a0b0255078615840e041040002d40911031220080702005200102042c0345213a61a00d17510715a040c0e00c8003030100440182c04d4000c0740d042c401d080505050410039800e01c0e4044003015600e0003400c070004d0890030300141d8025490900e0003008a502e520400b12000784840f40a07080142c801a25000000c4801c00001711082c40e003c208260150f0b02c140090420081c0241d086015040c6a20150f0702c40c00b03100b001013004c4401440c04180c1c402002c0000c03409002900d0014109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 318429073 1250 318427823 318427831
    0x9060503100b0109090e03040b07030e10020708060a021b062d012102060f0301060c030f0c030f12060902070b041a0405030409110d020304050d110c0604150504050909060f 75
    0x20707241c440b030041c0503a08558483c0549641d03140000b580d22464400c44d2552184d0382010361150f1000c41c0a42c1015881510080846400d441e111951650f8010503642d814484c01211b280d0740003500012107410042c0c0c05010f450031010940c041103019100540e05194058413032500500382100340000396105000e2000d40110040c0c080c140030740c03510b00b03c0182c4941d0118084142100403c0a2080d55034020554141030455001c2c2c0e541c030b50b515070001c0c00c24100748200301c0104a004900030085030048c030b404041c082d01501c4410300d03000000030854561460017142102030340d0320076000c914550a0f04c040c041c0f56104151040071401d06090031080d00b2040489040301080351801c200000e1404001d80e400c45241030700c04034800c0e0640e0300e080e5081c010b07800c0482446101201300b005001c4001114007c590168641305840c00b07084070410703211450303550641d0700104100000c001b0040b15031064000e501c011318185051544030000920f40d0001642c0c04c0c0e1265000c41c003401400c041e144141504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 318430323 1250 318429073 318429103
    0x4090605061009080a0809040b1207060e330c030705011d0601030f080c071d0a0606030e0c0607110405180d2a021206070203070606080105010321120609060503 70
    0x800e032070711070600d5642c130300c5d428000c04121010031960707500d85542d04019010b07031006050054084800300c105983e104503100d09e0b0002000c01001c1c0d055820f20780000c0c0340034084032040c0c0303505000300c3c4034000144103c0c0500d415440300c10804074005041c01e10140c54003510450000c030b401c208a01c10410014403400483c660b54014100400014062442198000768880c56003a150725001e8103040c18602181d000304820030a03404d401c00351003900010940319001801081201a4071030700100c044034034a100d6082194009840003540b458400b0282c031005105075215681202c1c81d0f80030505032502500c8440008200c0784448101d58020f02c4100c0709040b003031600c2441e111007a100c00c0003030100d044600080043c00c1c000c800541d00c03281072414850034041e044035680d08054000030340d40c1e4485901034490900c1c100d80451100810700416040303d0700701d04914402440155100070710060004060300f80102e03901c0c00c00c100240f41c003d08001786400c4c00b001404038039100526050515000030260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 318431573 1250 318430323 318430337
    0xa170c061b0406140910030c1706011b0f1703061e010903032a03020c03070e1303052101120201110a1a0903091305010305120a1715040906050610 64
    0x305618042502e040300c0c0f482c5040355014042e002c031565544107007440703642c011544c0302c06101780d1a01b54222010f280c48590b250b20300c20280402880d42c1000649041340020003200315500d0030025503000c80c03005c0f40034801c0c0c858030583c00d07a40ca000c0021007120b81c000304040031082000070329005071201c0802103103400d00b461501e11440028407043d400c3c00014117020074000d142e803860045101540b81c140300000c14050403005403e01964035000e41044510038400c0710000700f49140075213509400b4928060300c01c1d2030442550750075555900400000d0803000191014003010001e456443c9008090f506104006c0c4ca8860000406038180d04103e02140e511401540780011700101d110800300eaa81c44066095888490447d030952141a0009521800100d450341c0802e6455224a04a0384181c003142e0043c9504140140c06005e03018192000c0340c50900159400d03092408400d07441600d11121325000c0550781c0002d8116080d0300f1094039800d40d18420000741e410030041c21800e0441c40d00f00341c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 318432823 1250 318431573 318431611
    0x330c0906170c0313020303030709031b080717010b09040b060102060f0f0a0903050903150105100c03050a0c06140c0a090f05030d0c02041d0a060501060302180f01020a170c06 76
    0x10441c0d201428903202c002d0000001904086140101c0400c194000c09076640c90400400c0113200e9016804203642182d00c500c1e000d49050b02d094011801c490303c9070003800e0f44c6032400000f60025807500101c00519500d0b2a0741050315907c540a0511440c030a40c0d030300d8454141103000a03c0d001c001012420000c2c000f400744100a0002004a584100c1c003100c04034040c1c06500d000ca8050190192403a058400e600c00c02c58481145900039051760320581c0c0042240070824411190100b0b035903409030105904100d0720700200c1c843c0701c450805500500000c58141007a903c1e81481f0704048920609140c00030500e0b44641d0750009800b0018400c0804d041000307030401c0c0009031150a4220884140815100040c2c1107440c0e51b0230548103a0400005102020340c40c2c880a0380324030002c003044403c00d01e003000225880c3e0091082d54203000d030308800d0130300180c4e502c81440b50440d9480c9041c3c3c158411003450100190703c0901c60350700054004000c54551118044040c900740001c1d07c42480d59441c2640381c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 318434073 1250 318432823 318432857
    0xb06060304030c08220611120f04121703010e07030c030b06040b13080d180f030c0b0703170c09100503130b070c060908190e0d330c0906 60
    0x103810f10f682c01803501503580c07040b0241100c0c8540c0100403000942044080007034040e8004024103002c1c1031460543c0ca0108407503004230041c0c440d4406641e60194240001d01188181a0791455040e00c80c41c0b013094651000310521007260001d90140c000001f00c1410400c0565041c00341414502d1745003820b20091100c8000103101340218002d07500b80360400320b00050000d12502066008200100c1501d0500000c180001c20b00045440540000308099100048011048600e00226508400d0101ca49820406448503075070211800344c0c00c0000c200c002140952018040d2409682072150075580e407503400703041c808140d0510321034205010092081003040c034030042900c900594003078000e522643e42c00c942540c0801e06460702805240c90072000d9030030050150000c0059504501ca41e1410002c050412100305201071501600400310214002c005440590040c01d8101e01c2c80c0c06c121101c803080b40b025080400542d0032941c10303032a000a0b514032030b042402c450140640d4a4220020f000340015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 318435323 1250 318434073 318434087
    0x20310030b070302120c070308010803040b0f071119080c0103020c12030403020106031e0323220504090b06090702030304030c1e14010b0f03071203081f0e040b0606030403 75
    0x10190107103000700c000482d950f11941c100c8144844c034002c0d403111405c18403442c1a1a40100c3c4040b80030907000400802d8004c40001075030b044800ca01c040340e00d40101180702c1c00e0341350054081144d403071020134000c3c042590740d0b03000550500003480178050640e160000039494802c1d46140c0a06052040200c501d00c0c95000c145041825503d2030072580c0c9465500e0201d00514840d800500340c400c000d807841121554460802a00d82d020381d079031011a04016103d280340304000e03007044454003420889840f14200e5040d000680384070041b0000407842c1d1302e0740801d00341c031040c1c481248c40d00000d5003002807a00d00222443e4000926200039400c501d416a07002d4006000e103c2e0103403c3d50f09186030003034048110361040c540d459101d0841c654100d800e490707842c043c0269421a0348a88402d5250010398140050940100c9a0350761408080030b0281c1c0b800e460790304c40940301d1084000650818070103da44506898020452141440610315190900200768200900b0440c0310b40410001e000100c0e80c4120 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 318436573 1250 318435323 318435329
    0x6090c020a020d020a050d03020609010e0c010905130e01050c040512060606040e18011d06090d02030316050403050106080a0215040b0d0c02030c010f0e0d020f06180307051603060f020310 82
    0x212524054900e000085ea5610b5560180e64454001145881015408149203028050440c024031111280c3c401494440c1c800440d50384c005030509404100c10300c1c021410ba007110340039007000240e0140c40a1a942503030001c59208100300c034005010080c03030a00100c6502c000e0310440280c00c0c41e05007400010302c544501e11403030b0008104c040c04241c0d42011505601d040304217040080004011501542e0400451107040440034010f000004840500100c1c0010701c02c1104e038003a500d984c0d5040180000020840103000c00c1280a01022000840900c60080544200f100030034030503489204000050448407004510100140410000e400b05070042c4c078000320041c1c40c0425080039061081b861405002c2d4502007030b41c201400014405401e0f40440c000c143d180c415a295490799050a03690341b102500d0340e081d00d520180000c2d600006e0901014445602001582e00d40301903a16860714181103039004400d2008012403c01c03c02445210f000c1483c0c080660640c1580740420005207840210700c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 318437823 1250 318436573 318436579
    0x9042612010302120708032704200c0c15040311010c050a0b04150524100203090f0a0b0a020708190b06100e03100609050f01030507030809240d06090c020a02 69
    0x4669135000280a0100c0d0014042500450352683d20010000b100860f10000403030311440001220412420309000d00721140c440c8160072840c0c840b2560b460021a0b00c450f02040045c040c90204a15a99600c0a0100204245501940c5960079420705000044071100c1c1c890511040c2d0348580b00103034022a201038800d820001103807031079640307052181c0c90381102d0b40c0074912a4901000c20030703200c1200303440d034046075185441d802520b6012018440300390448000c10016030f00600c00485285850403200e6201c05003e800e8070f1050f55507503070b030400760b800c010aa000907130032011007404650001c01420310541101c0700208500c1007951151000070201030f00b8a030144018000d01481e060042c10044905007000d8112525490700c00e1108000300540d004043c0360b80d00b804080f990928408002d14184ca812201500c401e0b899a51404010b40c00700c00615003000402c1c1c0310380d0f0071a00314041d03100581c0c0da18411036038514601120030f08507092504880c882520340116002c29690006541d54840d60507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 318439073 1250 318437823 318437839
    0x110103090c0603050a0b060f18010306141c122705090c03060409021c1e0b070c030c02040603060905100c02030904020c03040f090b01081501140304080909042612010302 74
    0x120017200c015103c072140c065080a40020a01c400410b100b00130300c1039007011512000042c03a098011001d55441d44503000b0111110f40b0b075500315103424480710391988503428010f50003004030380c0c3d13482222582d454584041240e80505d904401942c0300040c010645540048407041d040000117503208101070400c940020001c00040d04549559101106464000344a6141140306042121880703415510880c1d000403103001c0c1d082e014000c0700000007034aa01488061041e6140c0f141200e02c504520019000c2003550304041c009a10b5078440c21020b14090702c1c004c2048003040c100103203445480e040c6644d1040c0f800a4111415601105890542c003040b0350240c2d813407088006580ca10f010343d030088003210304d41803400980501c540d400a54040310a8072400d5181d9a915001405034000051190105001680807601d0312024030056601a114030400b504001c00080414480342080701c08803440d24a0030707030306400c0d0031b85298004101402d031a0300c9454080340e48040b140c50030041c03000038028004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 318440323 1250 318439073 318439081
    0x15050a0902030708010203011e051c05070902070f0b01120b0609130b01090203060a060513062d080403020609210c010e1902010906050906030601140c030a0804110103090c060305 78
    0x80d00142100358000702110803998a030300b404c600035442032280140d0500ca09603015039040ca266419411070744010103580d0a5240c0c8810220b100304ca48104079080e01801001081104d100d1000d041401e004450790700052150f46010a030f400302c1a0081b000d060035070004d1000044908070010f510000c2a50a481d0340d0f103404441640c043e81124000b070404c84a0300c004501c906060f0301443c89010219000701d4190b40d00c0701e05440034454013011041100c2c41c1c54060090a001c0e68000c1c0e061083c0c000754101d8416004519491814003030801000204d00e90140300030300d41d04004141c2c02500c1c60b0f01801c4d0310041407007100c0a0134081034190048180c0810b0503481104c0a602002501c8408000c0c1c580d003140103800c551000c114040101d000c20070070500824407610401c1038984105000e44407914544802005690413019a41048158403007000400d1510f0740a0010f8260300c29191100d800900b05494001a1000150f42407810903207080594404241c8025800701191070034100060b080d01d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 318441573 1250 318440323 318440341
    0x90e0f150f041d010b06070803070e0d0c0305030a030506040e07090b030a050f1c03090b010b072607020a09020f070803070c21021c200106050a0e010f060c1505 70
    0x1240504041d8014a840800600c09200004412050300700c0d1008100030146401000211f018a2102400200050000840341c90040482c5407403c600181480c0500c151561940d4000a2941007211a0b402c0032651000181c0c160090070f0304401e04481c14000c061000b078030140c1e9044507200b01d83c000d54440b881d680031500c003403000b0056182c021080e40d43c440160780b0440c0e564942ca00c107a00c0300301c0c200309007414498840d204070040c441d80000541ca5503464115034042540040d141907440c1300310459104401040c0307000499640d41400000390f101d200c0745c010454540400c9d803150790064010040c901c07501903030108603001c0d20340c01603102d40c5035118000122030078854107000401c0310f2a42d0000c1d0000388407460603041c60000710b50031190310750344070200e02c54013a1809400c02e0100d00100c8030801d081d521500c0d00140144440b00000701c995480c400103a03040080d51202801d0700c599001400b5a4100c2540080039050508101c0101e140d6a5209108031003414a01280c140e0b82d8008910100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 318442823 1250 318441573 318441589
    0x302090103061d01030b0702060c03131e030e100302070f0308041406040606140102030c120d021c0506030c01020609060103061107060f0c0816090513020903120a090e0f15 75
    0x1000d442440d2075400f40c1030b0510780e07000c07400380020b0711000020310002c2d072198400030304240300e00c1001c0025400c68179034211a403403d0340c40702d030304843c1d180340322250000728031284500c5981c0c00d00903681c1c0440100e498040c854000106400d207400c05004109440c0490621120ba01c01507606184c103c02a503510b08210045a4406494000d507009540500080c0542600b0842c26590440c03081c3b138049c07880b0343c016a80c912501c1c1446410360044481552042c2426001d00380b25928200c0141c98000024601142c80c00c0140c6820b0005503204140081da00b07003048211030594080c0020038075400e008034000d641e148c0510008002d1900c03210100b101e800714a0580c0c001a0340010103211200074915a0340181401407003000c00209000002034412400e010a01c00e200c101d501e519000d43e0800040c8031f051a1020880c030141c9400700410031107510200281c20400000301062926450302e550010820700c0c3d580d0007040741100003c14481610f00702518a500880094008074004040502103a80c0c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 318444073 1250 318442823 318442829
    0x903030c03070c050306070507050c010c05031306110f2d10060303020a02130b011710080607090303030c020304050604060c030201110301060e1c0b04020105030a06030803130303050a0902060a030209010306 90
    0x141c00045012400c003d142000c0da815030304105d01391110303690346080032030780c038002e43c0320141050f480200c071003a2650080c809001002c0c0960141d0340703801081c502c80c41b441130640c0c5c403480000300085501201c54005019440b03040e402d800c0078181c505a5402c41c40c81c1508002000303058800c0b040c0c60807400c200c0410266400100c1e808090103055501e0030701035101d181d0114145d0142c0549445107048026500c9038880314001610303080318110600340b141b10b000000800d554000c580c0984040742d005010400d0b60310455099565600c1d181c10b6140003815111044003207c159441800240301e15501e000a4030242c0d17084d40f17000580b151060038200c0c00b40408804460580000000100e1080c0e1300442c0018a54000d448107600490f8a20b010030b84080540005408614200041001584500e00640d001600d00001041d0306449880f03812141d030081d607502e800c6070050b003445810103416000d040d9010f52803881c02c02c007a1100e070700440c03841c0c401d19041741e0405500150f81d1545a009506c00006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 318445323 1250 318444073 318444097
    0x52502100903050301231516060905010507020f0106120f050a0c1412030310060c21020606040e06040201141c020403120806190506091f0306050108101a090303 70
    0x945049410b000e00b40e0b6100307000d80e207075041d101280300c000e035102404000101c400203449010f812140d1544051507400c50384000402c04004080040807442c58040c0d840c840380034000000d040d040c020700203844c1910310304910446034108001007140000310500c03000b001c1d40010600108402903c0d10364149900200003c19802c0d5040c80030400717200c533a140c0c01d10494143d5984041098000400b5500d02040352018071217a0b07800d00070300c0268030800e182c1e1401352140c1c1d050054003c600309100040d0f600012903100580c4010100b000c03614042c00b40109804005000c0c000a040136000280400c10761011000301c5000064562036051000e401c80002c0810401c0441d101c6480b4942010f94000d0400da4900060350180481d040b8a4807500b40d4440d0700c00f601e00d5254003482c20003808803580144488640c400c030004d03ca44c000034000e012003583c00c00c481d40c2c00036034141000b0001d07100c840040c000c15407440050b00103010074811200540c0c03c1200e0007008603141d205460010b45903204224030300300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 318446573 1250 318445323 318445331
    0x3090b16080601020102040305121810120b121b031e0a0227011404020f0403060207120f0f0503041416090605040213150c06110403020406050405250210 67
    0x8065080c4000c2a40c0506496503940c00640707401c0c004900740d0040d400050f005800c030f5110043c400900100400400c0c40710b0449800703080440000510384d036250702e640e1011905820701500800d00500c00c50180e0102111101000c240800080b59904c2c500d0000c8800040501d181041544d810407800f00035000202c4414242d40c1400005919000016001c034001c000301d5112001090f01060740451540041e006943c043e8a4980c2c90720040041c814000d40003039003003043d641c039010468001d2015502900c0b015903540c81500d880340f080f01480f0310000070005841c035000b010720382c0300a1a11580d2440e1514a44980310740c20302c030864400e41c502421051003010445001e50611205000454041100400c9016550018081a8880c051041d41040303038510f0140701c0350401c080d828402000f2881e11240c805510342d1580f08589010f8180c01540d08041030420440c6400e004102c0a00340a81d000d012500f000004401510700c0384111000200c0401500e4119502c00c10110500c2d4005040503c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 318447823 1250 318446573 318446581
    0x61e012f0109140a030c0312020432010810060c060f020309240403021e0c030a060b0a0803070c0506031b0a031d030c06190e0313090518031903090b 65
    0x350003080702200858402e00d40c3c08030118070480200c3c41e44026505a00c840150000c5994100c0d002c0d546401c2c83c07070340c081d424080454518002855100e592480c5001d40d078402c0c80002c000511340340e4141841b410000d01c0c90800042ca502c80300b06108551203401c207030030303000014502003000d00000040680300750b201000700500c0003400180c0404010303200000310030152946e8161489181c0848001e00035a00401001220403480010321081d01b0b289010381e81601d8001d80000d05240700380006032555911190414041c1c0b50a0001c64000c009040080d4504400d5968000404455105162081d04003200080faa0780c80359a82e41d04c0401c20100d000d545030b03400390000c1c0080c1801c0c0555150003072070380c400102202000080301c00c000341304402030101d0b95450042e00202422042d05144042c0c850500c5020440c040014090071407001241400e41d030b05000c0c20004a48006000910a0b10000301101505002100700d034041c81204d01a1903210385000c0041e000340c504080300a0055486100b00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 318449073 1250 318447823 318447917
    0xe13170a14070812090610060c020a24080c1e0c0f03040905091005060f040f1107030809010c020d09032901180f1b0c1106040e010806061e01 62
    0x41082c80401c1c4004d0805889201c203143d07480204a9074012402d8034240c1c10301c00b09004041e00000d0030b00c001c00c1500e03203039200c25189441c8000211103020f0785003d0708800300401d4000d00032542c4000c20300c20640c01d21070141c845200c00701020814010300d690003c2d14100525051005000742ca1a080891f0341e100ea940300080014141200e000020703000d80c2003c0e07010b0503a0f5000c0d09001e46801814044000300520811005146881504102903901e2480c002c40f13440f2600130300303040342c000c1d201e11145140c240748842c2918550024101190441c0c00d080359800d07044401724041e031b604800d1810b05501907440321039165901d281c501c424400c00400008800c0390202049a44000e4044140b0000d00d07080585820385208419000450049216440245200e40d06032604075006500c3c0d800320001c84004910260302540244080810400044c03201310020861940c0280060b20302000a01880e0991749820721007010a038108024a80ea07407000b40381c01e0b140040114030920303194102ca000100f030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 318450323 1250 318449073 318449077
    0x16120f11030a0606030c0e010305150913020f0f0102120a02070b1605010c090308090f01020304030204020a091502030903030307030c030917041d0f011403030f030702070e13170a140708 81
    0x11192040c140003001c280181709000c0d01c2140c0c01ca6845103e4481c03081c40064000c3c0200402c007005c0c58168800040f5550780d1883d101c1d0040c0f0301c1145030500141e4034010702203803d001203001c2d4041d800c02200d0103641e0341d000410800d54581c50700f01544035200311100f2800c001140d80300d8040308002007100000c207001c4940e598203261140008100314030200c04181d401020f2803102400501c1d0500c5240c5050802c1110541c8007481481540d10309a00da60000f03040b60048015480090a050f50521001004000122000c07015000560030502c9140000380d03a03100060100c42019100d60b003c06002d802608a4100c0c60750103103500b8450711880300c0c16045034000c0d2140f03000b00202c84503064030b24446881c00901500050305061b4560303083c00d00c41c552010071080d00c0c903018031003041100c0c10062514040c41c0a1400c982c00340c60316610340341d010324004001602c40e200c203a1210703642000051003120541900d041c480c0009454145011096603280010480d08044200000d0aa804c110301540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 318451573 1250 318450323 318450331
    0x303070c1e060e01020618030403080304060b1207080d120e030d0f0b04060803040306050403021e0304050a06030b0612061306060503060a06020c03100213050616140616120f1103 78
    0xe01420710700d40d581c2003100d100e0751480c0e81502603003003800070a03814070600001c5044410b0180c200e91405a0300e81e10a031180e8001c0780c3c00d071150703075950b000d090b404d2a05811801902150b03400819015050044143c0c6920740386000c0e205118500744148000c40e0203403c0072010391562070581380c48002030040c0a0140050352107011307040c3d2030321200c1c12152603c2d204810580c2d9100c0c004504080c21a1755040043c80080c0c020703400c0d4130815001d448140d9460141c1c071100d103038140146444a18100600007040110380200d005e040c2080d90400c651707242c03882910b0050105d002c001c400784d00d038400450207440e00c00c040c01d2310060500001007131454204d0000c60007900140e5a40c1c1000e9620703081240c4032515a016154150010b03c14041c607206180c014058200b80311402c49075107996000002c0d1143d00250128901c2d030000c16000c4280030910101e14482d01c01a0050040c6207861340300d00140350408080ca500748403145120080d90714055001000c5081054000c204881c4500007810a50304116 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 318452823 1250 318451573 318451619
    0x6031c030c02010608160b030408090a030f05011503020d150e0d0c030e100f230a080f1b0301060c11030304030f0b0c0f090108040305070203060f060f030c0d060b0303070c 75
    0xd0b02c0002c5d80a400104002d4899403561181c042c07500b0300c0201c443c00e900141099807034420a002c3c14840e65103000c28440151f00c540c0400d100d4880034600710b0b081d641ca035105100003050586040000d40ca0703c810300c5007540c2e4891140322808800c550601e0090030300511b1151184146040c4140150700004142070160003504e07500c1075100402d00f00910021201500300010302c890440c41401400740b460449041025165101400c683c4131081516400165202000844140920508031490803000d5000746000510140140860310004035034030040c40344400700050300910100340101d0031a4a00140001000c0d00d070786036520305001c41d006480f0b140030b6412180c4600401c1803048524100c0d82d4a0b441c1031050360400d801d030030041da504440200300360306100e001c210000044e5014016540f0030040a002d40740030b41044001e01813148803200c5560301990103048000e90554646004450031a4007080108440070b140011a085000d01c94000382000611440820b8642500d050b440390f469440c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 318454073 1250 318452823 318452831
    0x406170606131104030822180b0d020f1c050a0503070309080a1703060301021303050705041b1b020a08060702010c030b0f0303120705040b0c07050103110405090f060a17011e061d06031c030c0201 85
    0x4134003002b54143c80c0d40e200a41c08294150f0f0050241400107100300c41203d40d030201c0d02d440300107445a034100402c00380d04691580000490004240d001b0036408081c05602e0300406504000c0c0da02c1d603041c0c0c12a004685841c40300840010041ea03001d404861107071004c2807128600720703035034981581e448489000712445241080301c024103071004200c58150460741580e0342950306200803210345210a201d0f80c160782000030380e8030100e82018101702d850b01942859000080c030310b490410003011a800c0d604494440c00304400c01e07a4041d6800003c1d60600e8403415114961511400000d54091251341d03c0003500200200d0090340248005c0b03900c000316070007030720240030b21000e606504000384214083e207944080c10002007000400e01502d01544400041c00803101d0742d45503200d20400846d004403466450391182c80d13054400c82c110340d03030254008003042c00f40002418850800f00402100000010500b45180058050ba40410441c8015460710340400d04403e039141e07005001d0038008802c0c101540c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 318455323 1250 318454073 318454091
    0x10030908040e040f0b04050616090f030303020c01061707060f0305040807080a030b061602181b0a0c021305060418120c02040617060613110403082218 66
    0x24064161000d038801481880e00d4102001860191030143c4107861429030302c158030001410b614400c500070340c0244c008150074504805010720001e8417941c040c04200038210200807118003144403c050360b6050401580303901030320821724010120713a0b11804030700718814444001c04101058446c141c81d15a51540d074841882c2c502a01070b03031015100100910b40421400e004121168060031040c00c240c82c0205210040d40001100754100910403140c40312402500070841c03402c42c1c91902012000d04280e0718500e451400c0307500115022800700a501000680c2d601030300e01c9000b9910300ca5074001d2641d407002107081c400da00104000c03201c941c0102d203008954546881c50389080303015076034407980a012000c402502120300c50160b0404a0b08280c40d140f000c00d41602c000c2900c070f9005454001001c0358074040042180c041100842403d040b46010200600403996804540c19a900024540c0c0d0700d800c05440c26401d5018842c0080c460a070003900410340e4642039160340f00249000d6400c0c098020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 318456573 1250 318455323 318455327
    0xa0609032001050a0e0423090c0108390301060905040c05090a06030f060b04121b0305060609070c0b13060e030405011706190803120a09030f03050405030c0a0c0510 72
    0x90000d1201c0c0c003080c800d200d803540c0144607044061300c075000541b0102c0c480e21210340d0341c00d81c2c060075140705040740015010005d24100030850542e41002c00d01e420161410403503868a4180400145401c0c1e94041b804400d0750144142c5c88061060300c4040815a42c1da500c00004003400c9943c05500c1c40382d0300382520032005031710941c1542d0214000500304003006d80341500a90050802c804400409138442c40002651542140544000e0240780c403511882e1916180040d0226401400a440e14007081c2050020070b8000910b654005001e894009040c0c84090041d101d41070060700c01002104200c0c10000da01809564101c2424869207086c044402d801100c5034a9014a008090020341c10b10840e0cc00c000359003183c16003050020f4504118001c2580855410b600e00303420a8840d43c1c00020710307280c0e851102c0c00486d40302101a40402c80807200b0b50b4020181c00054628008041e1218080340502c4020310860b00200310010440d10a0800e901d00107030441e01d54032403244665202c40354800028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 318457823 1250 318456573 318456623
    0x91e07050c06010b0405060327030703030504050c06030c040605180d201e011206090905070f0816030809040b030d02150c04060801030318051011060907030b0a020c0a020a060903 78
    0x503a0040a280c19543c8500127074a5840c100420b4640d00c440c4161111400402403009241940c0290340114a51826003042440c2030b24071080240580e00030000c1040701a141800e44091310141d1a1107656548881e100000350b1004403100c942c0003020031100010440d184006812150001001e07001c04a40b402c100000146615034031102d107000125804030079031003109000003c00c95080c0000b80c03152070f02001c000320354102c542214541c1c4500e03003d110358107908410328000e240d80ca00404029000c0201040c1110961200410f210404500c50107503581e45d8220340030b02080942210080e080342c40c0002d648400c9100035240d01030140020078800808001164144c450540322280240d1070355500b103500c013074110b20f002081c5020a5003c10141e46405159418103201d98503079940f11103080342c00c0d04002001d4040007066006403010000180360b03e80740e90340200710010040c0c4407103a24007090308040d03408074000d6000018030310101e02e403074005c128802a0790080040c510401d800031110b41040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 318459073 1250 318457823 318457829
    0x4031e03050307141c14090109050d0e0402071719020106050907050f040f0603091505040b060f03120d021305010f0c12030f020307020715030911091e07050c06010b04 73
    0x75004000180c8803c0c0140c0c180079504109035400b40c60108081c40745500280032184401c21030381c682025242400503d01c18035000401400200170412050342c406030303217141d1a00d001091084603000d45d030701c03984d503507054400303a640211502e0104490840c0b002035561058408034880a20660441c1d000c5105101704400e84c1c20180000380710740c0320f12806607001e07086120904640141004040fa5001044c44d02034010300080e140400c1c48082031500c40c1c3c51501c02c400b501c0d030b1a4a4041008042013189441c40c2e005681501d40450384200440401d00f05014160001640f060015901c078600d0090b41c01851a0310060318203581c0b054961004540340400d441c042c0300000c00d4914100c002c503900c03101c05441c05546040000d401c401504142007640c100f1900f03c40560420b1500b08850881c102c1c43c540c5056851030200044201a540c0c881d003000c544080c18020390f0f021000880c001c1c180c0c00000c41c41c01e245900785070701e49010071000301258801c900e52407507800740400014201c803002c000d88007a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 318460323 1250 318459073 318459077
    0x120f2604051509101e1e12110412060f02070209070e01170408091302030106120218060f0c070506070f060905011103180c030601030201050418091704031e03 69
    0x162514007010000c494440c0c0e903107031449080801405080c0d44c3d903d03120b15030101d40d0340c807201d500c00c03051001c51201c0d9404002c11410b200440300302e050018654004c0c1c41a442d04e0b800c0203881c03506144c400b00000c0c0380c0140c1c0828072000c00600452600a00b0315200c41c4984200400c0c0a010040d4558070140c4c010494000c2d0070000450105051038018555100d0848043c5004210045800314049040105450560384400001001d40903400d00c0c0c0545502004003240c04d6186500d0304000502d031520302403940d18441c2c0d001c5004020014030400d189078405009100c55200d40e0000c09000703031070748801340b2058075200d5660002454140306040d03d00440e0008800f28801c05103455500241c45d643c042201d030782d560b0b0100b501a40c06060090740c020303406603043e08008801035401c94606020004003607c00c0d8425001040107070b0b481b004582c292070840074074040c0340030a410321001804588070001c089032560082928040140b40150044a014001c4203164850003002c201000106c0d00010300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 318461573 1250 318460323 318460327
    0x1511091e01210b150a02060a2702010302070803101d010b030c0d020d060e070e0d0b0606070c0812280804060e0c030f03031b04121704120f26 62
    0xc0122102e0340402ca51105403076010810030155000240702d00c02e1900014880b07440840c02c1c5503115410400190310180d1806c0400c541e00b1561103204442440c4844900c005003420280e07011640b09405940d01180d000d601261241403024043d00300a4242c0908070440c0c80c140d8110b50003600004c51039040301c140000b2135265442e68032082c0600d51003113500707d9056800f00f104002d5562603220b000001d20060f00119847d00b00104001c210401c2c004039603100f0b42c52008408085044069802e41203901200e40a95624280c41c0c010f02286045c0e00003441d50284c0076004070801c0120006040c03071560400005a401990b5000488040d40d5a40307100009414500040000d00b03241c0c0300f500b11210441c101d4800c542d04100092500601c1e19140d03c0359000482841240800302c0c039001c0450f566014041c0c100340c00c29590584620707011901500401010f032101034001c18840171540544546004030544d01114100280d05400240084580440c019000381980301c0c10034840598201d4010f6480c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 318462823 1250 318461573 318461597
    0xe09040803060f0a0b0d0f05091f020703090e090c041b0c0f06060911090a0b0a14030604060e18061b0d05060609210c0d1e1511091e01 59
    0x4116840f80311145500019404000320b64000042c000d080300c20141030010884142100025054820182c114601940100d1003901c01a03408003420000c9100b4410040c1c4070091410300300c500c225142d010401155202c401c1c40f6070780304080b400840070703d02a47d05000c03081031101d206407001040901c490008440003550000681491800d0388420301804010450507110005041101c012402907035038020002250289400c0c0f2440c041d00400060400e42d0a003030f00c6050141c0510318240a58041c1540000011055900e41e40120058480c0c00074100c424a030140c18521101100c010380c080a11811000075000c0919091075a80380321480380c1c4a040c08682030f5040e0180030013814290740f110091280300307011344400194550045000c1c2d0070305001c1501e21042e509100c6108882409501c03640e200c031011840dc0054100e6044945981050203402410014488503202c0d40d03060300c40381004e000d24a254603450241071429811625168100303004c05180c00703100031440601e070124052110714 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 318464073 1250 318462823 318462829
    0x60103051209100806031218010e06041a030a0f060303030b01121509090c0503030c0a0b07050310050d02041b030b030c0108040f060b060c030403050109060b09060306011a0f0304120e0904080306 85
    0xb85c0d0058400384c03c0f00c01d820031045034601150400c04003c0380700030380032104c010f45682c06905540508019201d0350324040c1011303112003840e555122030101009000010030042c081560040d050016441001c114498032031034005c001d0258070070030a0003d08000000402c19146116491304e2002001040b107000e840c05d4101405401106400e8903841c1070000300141a440030b0004012526010001c0c00002c4450725150000d80000390444041080034820041030190003d0044146c070300c01c403286500005a0b2001501410318402e12040200602003d005da0035015000448604421800c0e03500c1a49a940116240b83d0b0803240980341414003229840454003582c800d13140d0050103013407685081d11541c4110f103554400d500484a43e0355903040502400356520940e203041104032410081d505000c1e0000f0358a0350107008102505111101048908408404a45400c091070800644a00d4681840c64156031682c5054020a00101e8080880d00c0c0800391680700315803005445065480315424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 318465323 1250 318464073 318464087
    0x60a06151706040e160609060212071104060306092423220b04050c01030608031209070f0e090c060306090a0b13050a0c1d010e0114040509010806010305120910 70
    0x160b41c0e0025a071320202c000582041c0040c07038180d00044904504070b483c0800040000c00d2541c844011174101c04001c00c9526150070890b110300390030845d400d031507030a2880050003d0400d58801001d0614281401d020000b803411074848041c07080000103100c0392400e0501c0c0c155501c8084141140504071900c608066050403600d402c00c489180211061002001c2e41102410300c031003d440c0200780c0420001000b0b0308106060300c3c1c050a281c144103291a0501455490041c00410707200e9550980c00100350700c8040081e01c0c014040b0b520804005652a0030060301d5a03c2902c0070801802983d045a02c0f900745542280d018190140640d907890b035600d5007c0000b003400000d2280d011454180201e25481e80b4001c45004640d138000c0000d554943c2c6401402d900000003051107480c40c2c5c480c00315216030700035003c485040e01c01e09108604081c040c00c0320219204d1604523a610007500d10000c5803010000603182c2c143c074480c1d011200720900910b0110040d0003586503403640401c1d090489005680700d80c1d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 318466573 1250 318465323 318465331
    0x1202090a020702220f0c0519031104060c020a0503030a05092101150e090a0506010b131a07051b06070201030b040906050a0509160b030c1608030405060a061517 70
    0xc0050418400b0fa00048106035140d41c00f280000c400407061a182c48a441410456a4141010000c00389500f4002c0c0080c0503400f400400358001c28080041e56010303030041c0440841502ea2295180e07240c4c000a0004c28403203105a01a80c081403000c42c00307090000895a440f52213460380f80c103000c00c2004000c05900100c1c0044010350490701c200700c050030240195400d0082e42c907010010281092248010f056004054284c90b905c0301d519000400c002248503415100c0c410007541c2e9400e16180c1c9095250300300d52004c45010300703404945007805600c40103480c40d503115509503039681c010900c90440251065044560040c030400c500da00542c042c4d44074a0620b0f4020304081024642521500100c4004651016000b84c96004020b03510b1418884003c0006829040d00516410160491100d000c001c00c2c2c551618400079920b4400c0400603420100d942d405081503a80303162900c0c1940d00c9035000c2d5081c10509041c09004180b086080c0030b003140f040c2280e62030400342101d0080d070a41c8050003034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 318467823 1250 318466573 318466591
    0x6080d09062c0307030501050705190201020304020f101b0b160804170706180c0504050702010e2a03060a0606030f0b01020604151107080304050f03070f03081e0702060916120209 78
    0x104d00200103902070141b14454085516019140ea034000b24041d81100e41c0c411132000c43e4410000c2100680d59180355803090042607c040a1660700c4003016100c18009003d0700350854600b440010804c0302d10003c6910030603a059600021000050083d95400015a0010844450080014a0120b0f25000740201d140111400300c2e6103525100c03002d404440e02002500c3c103501e1910140b0450400340511138102070140f00802c840640c5c01000e0b61200500c8a091380c440c5983c200054103015400003044884400500f992128240180e401c00100030b41d105060100b81010000132050503d0b1255a0782900181c0140c1002c2d6240d58071a0000450401001038555440c043d600422081c000a07058080c441c5818696900701400c000d40303094030301c0b010700c04035600400240d000181d41c2030444088907410304142c0e100d03881300886840c0c1c03c0003e40882c1100580310080208655000503d1800743c00d0707800c00d50300303c13600d460203c000c12034484c02101c1c05402d101188070014200f4010140e4000c2c038003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 318469073 1250 318467823 318467833
    0x303180c101206050a1433120106020a031e090306020c0c01031125080d050f01050f0405150d151103070809010204030203060a110d06080d09062c03 65
    0x110340094000c680301100c580004042c50001545000700740710740005440210b80e0b0000c214941801401d4403c00c0304211805148203010200110140d4a03c45584d02d402000c1d915104c400c0c0700b03030509140c200003583d20300100074900010b1424000305a103940150191b5074240ca0038a201051350b001140c40c0c08038001c01c41450b100202250540c4090402a0744401c0544010050382000409541c030255010003062000c005010303078000500c06802512440c1240102804854240613646000d0060601c0e512400c08040084121565800318140da030b0454000264264100610044640842d1010203002080c4c80a460525051843d912001e1284224004d404aa43c0502040d13035070710202d0384020302010040c0014503030407004003035101030510000c40c1003d140d1780019036158005000c07000d40c6aa81d807610030183d80d1450486001200c050320a02000d99222151640ca50038880e1440016141c8400840c081e0320031a0741c0089800036290528424024114540134060103d070020340c14414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 318470323 1250 318469073 318469093
    0xe010f110d0305011502030301050a05040c02151e24210109060e0d051903020304020d021c02041d0c12071703040f05150307030f020c2a030a0203030318 67
    0x300308601e048505141d0740200b800d5241240030b28030800040000390564200380700600958031a01c100004981d021100410642c1070000140d0400c60181c801705254030070041040021054080304c800c02000e04505101d45507200c9003d1680004407406e54010a082042410002d00d00b04040c480c00750b1a40602001c044030403040182100c3d00c1c207400301c4200b900c400800710040c03418020030003000b84600b801e5282c8082034980d102a5400b903034185d418154080085400c2d525074908403400f031540039180e100c8001c188170b42c0007100300b0b04180c224030890500520034240b60301020b01d6030f001e6454900401c0020056800c00c00d511100c04081c0c0f44501c100000021b0b0b1507648119042c0c200d0390071020b503680d6824544440031010f4550010b9010303007006106d884d03e00c180803049075440704140c030740000c690400c5414940a486980504c4c001d501c510709190700701d48180800301440300300610740c0d441340b00041400c0c50707200c8048001c040e505400520004001c445001d40c1145464204010f0307405000e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 318471573 1250 318470323 318470357
    0x3090a0504092a0816050a060804080301060302160845130f090b04140a1a0a060513060603050a1506050a020703051c110c030d0c060b0a0e0402150a0e010f 68
    0x245e01202d02c8044d110713100d020000c0c1c3c00c01e0001513000d0300c0b0741d20345902030785001d80701e0408510062140c2c00c1019400594050083c1100b501d00e6109503010954954940714209102c0c84150f5450384000c0c3c0c03482900006449c52600308085a040741c211280d01c60340c02c015020881050300c2c0e0b4070305005540d141d1b08144654803480c89500b41040c07040300141c01a09150a20903030070910b41491700d400780d01c043d2134000441d075880c1a01c1241c0fa5040c6016886036100d00e003240282a855018941004030400c00c4018040941c010078182c0b003142d5030420455440784820800e50f254034802d044002824242808101e2043d0018130b03610362540100d0301036565030354501d403401e00b1520350350b025a104200d0400341254031207102c595001c990801413007003041c040d001a03100c10480104c0740900002500910400c24070380c02c8000c91040040030700005a590702030052a180c02202c04034801c06116107603100c202c5201c4244d0f440c1e844640d40d00e5a070650100300650b041e4510702c03012003d1020404041c0501c02d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 318472823 1250 318471573 318471583
    0x11100e100b010c0b250c020a0e0408160b01080c06071101300b0907050717030a0f0608010f06080703031d040902041b0e0a03080f03040305090901060203090a0504092a08 74
    0x10021032807807803c9146218170711807003c450910780108100d14442c040941d03100d582050603103102e1180c503043c0b6107031860b00c0b18081c80745114144003404214038900a0040b0142a20304a0300d9590030b45401c1c2c0045403c00003280302e89240104050ba0400401c070555100d50665405403c40c09103500044103c140043c0e0782d4841d40b400c1040d00384e107680035009a42032204420750000c14070b003001400e10469a445450300c07550305209141c1c46001000107603891000d900058091180404104002600c610429000e06031200b1000c11250400e05c0004e100c5100191020480e609580c0d484010710a0a40c600c20a2148540e255401503e030620880569224441c031000d00700c202070010701d0b510400e00054154040c4802840c41048002c40800110314024121415412841000c5a82c0d03610741c5010360300c9000c1d0741d0046400048140000c501700d500003004055080c8112001c8000aa8440810058554007540100008141044040c0b0846015040c1c0748048101c2c80d0400d0868903100c141d4500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 318474073 1250 318472823 318472831
    0x209040e150a0f020304050c010c02031002120f0601090608070f0311190e03060c07020415090929010b04031103070e1e1003030c140c1011100e100b010c0b 68
    0x81c000400500030b814115120325142110800d00075410740c80c04c0c0d15074603110b40750300f07411074188072084142d80b0441d034007846988107000c5003103421510760500d4941c0700d0f590340e0308943e0341d600d000c41d18001c00c070f1a601031000d00f012500310f81d0303a1200c1503980320030489038000900c6441042c1501d40e11700c9600e08040802520800c8102182c100080030001d2009000946100c4142d019030082024042c020704184111030080d0340507900400c64240460705010380341890303403000d1403462619911104004000ca103180b402c41009490b000b0f07001c105201c41500d85420302c10118000004c01c000c2000070b0f01601c405a00d000020300b0b42d121a80e03a00841c220780c0e0340031501016007800560039502c83e0001541103540001501c90385181890466402030311013850502c0142840b0020800c110718482c040280d06580c41c80034003002e6580b24240d07009480e010002d403940216015030303416803020150314820100c0c0e44100000a10b545d0b140001c01c030000b02aa140c800e41000a0120104080341d5504101c0b805 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 318475323 1250 318474073 318474103
    0x12060601110f0a15150605030a09080904050c0912060106020c10050c2e0e0304060e030f0d120b01020604020f01030c0905041b02060115080f10080d02070e13080d0209040e 75
    0x8810111860340c4205da0030141c03d030514881e0190140301d010b91083c19694044039a2400140e899aa428021954003400011590040c180810030100d00300180240c280c8510584440e1200ca401000d007903103a290900807000182d000d400d80080514021104550704400360506c0ba241400344ca8000c0c0c00d1851280c603039226100702d45050008440c1011111510b060034400070030040001150b00742e03e80c4a9072041c10104100c5800c80d1415580500001c0c81003413031071086441c2c0301607940d405400c0c0c0030f100089424151034042000b10550001c61220b2089a00410452010030a60011b5000b455080c10034400c008850300040ba1588a42c400c803049801c0c3d05156005070f40345104000d140410580040008084214140354940d4100c11090380200d50b05407904201e6503074035421710b2820145c1c0d003c6101441079441210303503950042201c005450307007002804020760b101814110a204102401444074000f000616120310842d40944808040108046010003e020704989405804480244 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 318476573 1250 318475323 318475343
    0x110f18181501020601050a0b0301090b0a18060e010512030307030911040c08041205120c09030a1505090601080c0f190302091e16090302040b04090b0c04060e12060601110f0a 76
    0x401983c04100304c84c010001200d0320a1030310f080c820040e0484c00180300d16158252100a4041c443c0c0d0342d89400c00140c20304485220030620441c01e01340141c8000d10840b06680c100038000b00d41c50a15005411261144000943c1b540e100c600046000b03200055041ea454a451801a1020f0380e5500843e21a444070344c1d115901ca09203400c2c1800800c180d503450206000302044201000303010404082d9020780f034104440d40703a40e41003011138285842114001c1045d0091140c2c0d0645111a500050050b0b007828200d46460380c03650b1510340ea0b80c0350030381c401d50301204160514200f8034040013940081c6009040c80000c8544e00d9002c617218280a8a040855a221880a2000358144c05146034065001d11a0003800503084c031000d01800c10601019015948030901c0b54000c0d141d0b0780180c034600e98015641456032030310300c0b99000550450b00620b000600154002055171030721500309110141c015014004644525005442c01040c0c1c4070900c4281c007810344940c0060b04148a0146018094000e140f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 318477823 1250 318476573 318476611
    0x8030907140f03121608030709080c010e03030d0f1404060902101b0308041e0c05031005040803060f0102120a0806010e1906030e19060c03110f1818 65
    0x503603a641c440e894030301071503040c1c508014507074000030401c0700c0e00d440c000010303a1054141c030244078284a501c009012450700009101c3d140d0361201103441185c180c04280c1e11400780407001100c00100d050112a8103078000d014200306800031b030b0b014240c998802c010004034481e0852010a25290455041d24401c1d5135500860940c10308142401440c6c08034645002c40c0101e00d00e184403501d41040703010b1300300405440003400304a180d1100340f00c10140307250507180f2074005150070030128070796001c0c0e5406401005040c0c924201180195070003035038000e03400c506541c2c5042c14841907810b00101c45046100d0218481940a034201c000e0542c02c40a03500d90088e80b1f011030001d0402d1103002c170010b0150180f107074004064480c142c0903d00b511880d290108044060b520064038105108080071200d141905030f05d000c211584d0f10561091800f40ca00b8081c505c6444d8070140d05d4010721250281615040043d1802c03069111059559004005c010000344901d20380500300c03000046070044900c120560b502 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 318479073 1250 318477823 318477839
    0x70c0315060509090706082d060103150e0414030915040509010f080a0312110f0304050c04270302030708031801050108010b21070302102c090103110d08030907 70
    0x901c090182070310201a141860002541e503524284604010014100c0106003083c01d11172070484003017003194120b040e003040380300a441c4d414005d90b00240868500710060315003c0180741d021007220846624800c0b0380e0f5860b00c2d0650282d8130139214641d140410030100e4207942e900c10611840d03024014655484074207100c2400f640c404180c001c0c2542155400e020401108001010b03900305a052820107180f40d51501000701510242143c5483c0c15000b10f501c04295a504003d0f41c4514040c0c402c88100b00349003c1800211048640a42003c040c92081e540301c2140c82c200c04003050340710b881142c0c5094800c1d00d851303901c0c2e00300b40c984508004500d0140c88030b580c003d00a09000d02504d50003005050400c1d000a085c508080708544001a0701c015000f0380c0f8402072013000300458002e440300000f2020300c18000c010f120305184190720380804401d9142094214130082500d004040d2000c080d40e421600c07a440e01c0408a203190358080884480500041c203090091801049820003d0000130704000c08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 318480323 1250 318479073 318479081
    0x90c0804170708030127020d0b09130201051e0f03100302090603010605010816020c0d080c150f040303020306130e030a0207060e0307030f1506080a1109040c140105070c0315 76
    0x288a10708005000309804105454101d80c11191030100441e0820080c480c540c1da0464500840e40b401880800d010800e004d0300d070848101d070001140c0c0d130f00160752101c0944018448900020340001c43c184188941d040c01d40c690041d81100611a907420800d03a01c080e01002d81c801ca80704a094000030808104509002e40da031608103130201e0003400740c076062100003010182c00034080c05090226081440510f8000e21607201049d00142001a88035403606100d6141d600981070040e6a100d0f0340c41400785960300b00000307401000011950485030301e49840850180d00054292648514241c0100004120f5403154088400384540910b4949490400190520040340e1150041c440001c00c0703504599008208001501d0b4000c0101e8080942410030b5062180e0500c00b1900e101d140c1000032400c007000040344c0e12420710650448a8000c9da01d0140040b00006688c010300000c0180401e011480c0416410380b80007206240c014140310080e2100c81680d8810703841034443c4114050701c016480d0f46801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 318481573 1250 318480323 318480353
    0xc120c0e04031e08070c11010c050a06090c0b07050a020f04181a01050103020703140f09130506091315090503090d030509090c070b0109110f04082d07051504090c0804 73
    0xd00c41080c2c0340080006c0c15000c40f03050018860948080841d03801c0e8051845182c0d401c0d040b00c202c4a83c07410038648100105035414007034404003801c000001e142c41d0481d0403a400381ea0f02c04060808100160b00303102080c211044c42607803081d2a4181c442e03440c1c403c0e103030110340640150342940300c2042422020680303680680282d810103004010701c90100360005000300104101590b01a0390f12002541c101c5580100c030b68480e030005001514100f00c1240d81c02490280004491207030581d2514a024806c2c14200f9500038141c040090180318100315aa020b05d00c071500440940345001d4079000003900c5c46009040850100c0e8020030100703040c2c01c01446540d409141f21002034500501070300c80320403071801441980c03c2c4949859400700c8240b1082c0c281e03403100480c03035541900c6546078040780e80c5601e079821100c2082c4160011041309801003040000b01a400b01028181042c00c0a050203442e8030207001d9011320b00001c02c0005041a603601ca090740e4081c0541d5000c210342401d1500300e4680381121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 318482823 1250 318481573 318481577
    0x2f0307120201110909040615060c030f0f170405070302060c150c0412120210150513050c091201090c0e090f0f03040501080402041409010f11070c120c0e04031e 70
    0x3c48034480009a801118601c1c0411602c8508a5540780b41c0400a407280144109042c0b164503400100542c014005120180c840d40300ea02e03600002078421140030110304406000580c000c4403d141c61388040003025000b5009109841406449401141180d800040c8604456203c0104040280705500c0c3c02d83e0005105200145003d01d007003054000c0b2410113501824070f10001000000490082190b503803114041401400080f8180d00f030115400083c0c0b103002e014440100ca0100300300410701c689803085800c0241a410080300c40c050102440c14407012000395981c0d900d91401089802420100900d41c00d102c5000030318082401d107007013050001108059074001c40030002a0b140c0401560f09540d0b0a2030610b2040d41c49000140c0070f000c1a0f180c0a10340c1d0b811138240201c0039010f4100e010200c003c6c83c0d00303000307040c030440100b006032054600c05091a0000c0b203043c03141414050481c1c40c0c41e80500c1c020089580c0344d14480c00e051400b42d90440208a0409424041c443e04035007556008002d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 318484073 1250 318482823 318482831
    0x80d0e010e06060603060d0b0103150f0c12020d0902120309150f1e0d05271b1908031308060a0b1f02120d1509020304080403032f0307120201 62
    0x707000d580d070b42c0e140509a20700c2120040001900e42e20b0300a003500a060300078803003503015696400c20b4441c181c11248580c00e41c40c24082030015299140c0103440300030780c2c607079240c100300301c907003528130b030094008206800308075480c0e04200c00565524142c0224030503405c005103aa910101d410041107002c4d010451b0b40c181c01c2401001020b42000f8241d4480c0e0650f10402030b040300e40521003880a104910f800c9852616010521540190741000200e03aa60030380c6007070080180d00e2884556403c810303040e07205c010782000507440030740c07c10310b032584a46503250301708030702903078940640f030782181c0208211501c3d4040102c800c2184d0482000404d03001607183c2030821991941c0b2003c103030980c0500111040300c81180301c1c00c03a101442040b60300050030403044156110000c18605401a0001004444d1410301c0002c1c007142c1040c43c0e108807070060381d00c0400c4038605890350307606540c00ba0712545130000c4100284c020400d00710440c80c04c2115000c06030081c45d1740318020704c0d0011301e03e1041501300c01107a0ed0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 318485323 1250 318484073 318484091
    0xa0c05030d080f01030609151805060601080c0711030703050d02060f061e0402091203031005030606150a08070e0301060603050414071a0f090a0b130806060a0303050d1503080d0e01 79
    0x32032001d090545e03800080104100d1001d06204034005884200700003101c0c80c00315444200001040020b020910840c02c1d900703035488040044030036800544904541d00c1c001c01180000a4131200900d00f100006800e5400b00c5581c5c0c0c072707028140101c0601d40c00160700a04204002600100b0040d90310080c00c03140502c40c0c41c040e02291340c80c5882840c1440c000c0c1d50026048140d9903c5d010f2240b540c6440b003040f00c1d603a19041b118070404100c14071504e800307407045002183e0b251610030005c0094150030a035145c28071941900c2111280c5003d00040300f07110360403103070101540302805580c001c1c00c40c94401140d0b030304080c40c280410114200c220021500041018010008202c540108181e424501c14dc4c513001c4074415441c0b41e00c14207240a90040c9011400104940c051000d441100c1c01641040d6402d5a6044401e4540b0b2049400720ba101103880c9041c000a07000e0300107004000c0180300b0000d82403102d0700050b41061400e030420f4035002008204602c540e40503000d080d2801101c10024440c90321 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 318486573 1250 318485323 318485341
    0xc07090507020a0b044b0506061c080304080414031c0f141c0c021c0f051b1c0c110409111809011a060d050405010e0a0c05030d08 57
    0x350182c020b100d8003500300410103022080d007001103540e08a16040613803141c0070b824000310180e0400a004100f240303813032054140e02c1b031501e040350380c0760400060015580c50004005899600040304070740e000140140c5000f00b40c82d44040c0d07114901c0385641a81d128108211207007201d0080c000c00348254810f42050180b07042d017003070200c0090802d0030020301c00d01042409507051741c00c0d48a0000c0a501c0810045440d8024008014400031416402c20410111017801c0b40c0b1000b01100364802c0140b415044040b1500c02c030740036582640700345405420540503090b800c03040c44102c0780541d0a44d102c2c0240d03103a110852000c14041250030708105c1c0d100070f0b5540c1c8080c08206241201c42c8610323903500d548000d00c40d03031541d031908400b00208501000155011071038001c081c00d1350711002542c0780a0100d1140c44c451702d10210214001008a400d095141c09400043c0c6401401111076540310142c0303940d0307031000300103182c4490b05c41c054481c5aa410407003850718054401240c203081040040074400490 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 318487823 1250 318486573 318486583
    0x30201020c1f2d05030429040308070c0c0306050f0c180402071a190e0c090105132a11011506050706020408030a1e03090b060402070204060506030c0c0709050702 71
    0x40700c0c200518100c0c210380e003a01c0400d40403c04104002d54864550050076882401148624403821040362004440a0303500040c5401c5003c4c11040f0001a02180200e0b0080d000554004507a207003002c03501640d6030314915982c511b64412035140703498000340803a483e462030340070742d1001440a01c24200015001000c2d480c01650010340e0140e030340040d1600a00c1100343c2080d401c03100c400c690707030890b0410610041c2850301176424009003d2a080e180c480c0d5080121f014240c0340c00050220800741d0030103080100c4d000380710b850441400e555920080300c090015540e16402100103006804140035100007406503151209031224a900d4601018040d41d8550080b50030b60300e1614055803140700c0c3c0d00c2c0900092056030024011480007180314445140d00003800203403020502d42c08168640011803c2c1d0680f80b0401d8001c0c002c04044000414600341760b03001e030203c0c03400140041003040c1e94502041980d84140d0700a28401d6000070500c05414041001d20001d005003d4101700c2c80ca0b001400a442d6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 318489073 1250 318487823 318487879
    0xd0f1b0329191205030a080901200a050702030106060509040c1106070f170f150f01080105060903150a1b081306020a090801020319050106020714090a02160c030201020c 74
    0x1030005103080094a04089511030180c0704810408401c203455050131696900664a42d8001500410004078211818091014010703d000410988a58007020031650798002001100c200311f0309100120150b0303000d014031001406103407a029a00c0c040b0b8001e01080e5100d1003514000d110100c0300410170b0b280000341d8150f10145501c2d04450719590202c0c104c0b002d40261581c400f10581a40038011003a01140d07450f4011400e1500c001d006c2220081800390102004143c60b0210380308600402c450f090003002881400002420340d28140c00040400440640a41d40300215a58a01c01e000c8001da081d00d100b0b0280615040c00d0003a40b4180d411a40c440c0881d04000b841190041141160940a82c07500c0001d404414001d54903460301450307540040703182240d0007001d02d0130000001021800403844506a400c699030429041000c0010f000002e20b01802700020160300f0000e65404000b640d0100000f039118401100d0038a281d40002403600e10600c00f00c5200d600010040c0c02a40c02d055101400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 318490323 1250 318489073 318489079
    0xa0c02030124031713030605011d0103030e010e0a1809110306090304030f020a120302162709140102070f0c06090509060103090515091005010906030f080d0f1b0329 72
    0x101302800b1001d02c1c00d02400c03400c1c61304a85445004020444240c0003a410303102da142400c1c11500c001d03803a07038000000030b21000d00450081661a415035208000c07c0180c850003500c1e22403165500c911213100c44900e446030044080c2c0d030326000307400c100d40715514000d00c00c0102d00030103442c1407006900b91248114030000707140302900318101c030440d1a54140b0b00000c0c024402c0d050604041420040c0d02c0d166544000702c0d08515146012036000d030440c00303010790800c02880c65040e45904c04d1049004080201099401648100d140d200101d030034002000d800d88580744294a1a40da490005c4011501da0480e206104100b0002c2c0030584407074410907071050003468045407008403810102d02b4046610f8036024920400010041030500000e1075418452040000300800d82c4d0f1081a5022030b00c031804014036014581050f00c2c041245500588064a804000003502040d6100010300300c62128142403c07045410001c00b00d80394251052041481d01030a10040c0700c80c20f442e003d000e40e60000c06042c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 318491573 1250 318490323 318490343
    0x2001020a1115012303030412020102160f050118030512070219080327030105040302062e030201032309010b040506030114040230030304020a080708030a03020d0f020a0c0203012403 79
    0x7100310070360092044c3d0203800e07030390b40c1e03500c901100f141d02e0103c41c3c003a8054840d11170340520800482000c0d10880303076803c030450b002500f090011100b107100d160901c0e9600744401d20220208000b404669185006021101e5440c0c001c0d1060000c21019019810040081004c080121260200c00c440c0c440e10060640c10f08480c0300d94103498082080b200c4140c042d07207482d0402040640000d59075010f80c0340444607e90415410b00c1d00204040c3c2d0035441044050403140401c0154002c0e005551810007002e00c41d200640b010118482c040d20454202a09a465040c0c0c410141864880d8a8011109800910a245895448140444010300020f0054011044101c480022510703070820200c40c4072500b00b401114448100d41c4c0350001d82d0240d1094158101c0024406400030342c3c0b600b150180d201950070901c00441c158001e40017004005501600d810030403001151900c01021981c281d41c84071240c9481c0b90041c942140d00d10b220766a00548072400c480013820030410541c044a50007070800b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 318492823 1250 318491573 318491609
    0x1060f031503050d080f0c07031b110d03080f1e1902040b0a091701020c0d030207110a0905040605071b06090f0c0b07120c02061204032001020a111501 66
    0x81100c01d999002a10700d010b0705411180103540150710a003d0021241400003e8a40e8110020701c0d2103580401000300d01c092401d04048184008840012030054440141c0081741102195010800c0d07a021400100117008001801c02c00418050300004c6040921041083d0601c000443e85406802e409000603d0114907101b48a180c0484000e401c0c000301158480d00070b80d00c058100c1119001f628101c40c210a45c601c880601403003a80c0c290802e03500101002c00e81454140d00035400300d5002c1d1041c1c01c0c403011505903a15659a400c00800c001a80002d05141a0505504440c000313000c000400110b1700380042c081c45030203a1029125004507001480d100140340c04034502c00282c0000303052424140c00004c1e040542c0015181e550b00400c9440300844400d00d0440c0c040c0c5451000039806481400b050a15500c100d007129409403003402c3c105d02c080701007180201041c42e1943c550140d40e400058102c01d10b40d0104943c008000e00341e0041c010715800c007038003209010050041c5450325403400448 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 318494073 1250 318492823 318492851
    0xc14070305032b09030203070215070605010b19020f060711011b1806031514270603150c190c0c03030503010e07050309060c22080d0e01020601060f03 66
    0x220085502004480c2c1d10a441c0420040070079860386445603030150341e0303401140510903000b00c07030700c19034107074069490a0816400c00424205201811000c0c290a00500000540130701c1054042c2005440c03e64890002a0443c903c07101c840020108540001030105414030001a6654202009041c01049549000b00103401000f03480303540c4c03402040c58281e0203902030b04803804045d0380c50244050307480a07403502030a60a888803050310b0280190b0350f45040140306181020790100718070013020202d4502c0e01c245403180007445c04003010f008100c09000e10800c0d01d4100710b50a02c480300300032014940d180c06400d40c1c03250f00511920040d40d040344101c0030107982c810040c102410740d001c1100f02c1c0c10381e141d0600a105420900500003843c60304004580c4090140d07041e03921030b180010040c10707241e4451500381c0043e0880506002c5906104144940c01403000384403c2c090b200c158000e00444040c0d00f030040000000346405819508110b0052241c00d92001400000c1071381c2e802d0100d54403801540e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 318495323 1250 318494073 318494083
    0x50f030d08090322030b0717040201140706090606050405090c060f070c08030a0c12110331121a04150b06090405180f0708030723060c0316020d0c14 65
    0x306011344510084954055030190540b102039900400b80185d6030754034260251142406443c1860030340e03900200040c0190710071200070144456040c42503060220607552a006c0d52031055007144c400d45c440a0600003810f0600c10035500550721001008030000000100701030740301d100040b103c801e5001030000240074145c0201c900420066007200d6444282080050079805200000c44035100307291078108525200d144203540030030058014529114445410700c0001c442031040008a504000c0f0b12003483e03100310b40100c01024040c0a40305e2100c194a07026195480726042958131044680034080030840d011640c01100000100001e0108407a40c005000ca000e280011030340300341400100510f20080c9212802c1010700b030421074071205480e40900c0e0f04d0348158064500c880e80240129000703c0c548200009540b003915680c010810b00c0310340980d00f01301c4122108a07116034000140490349901c1c042480c0e80c050340d072018285241c02c00c00018982c401e02d40c0b0103001075648089440b0051030a03c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 318496573 1250 318495323 318495337
    0x250c060905161203110604030f030c1101060b0408010b060708070f032703140705090a0b12030f040f0603061802030405010212040302160501050f0909070c0813030c050f030d080903 79
    0x8015560341c0703a040001982070104900140714146428000900050858003a9032305480c0c42540b0101b4541c00c40003002258540f0040040d500c4504040c01000c0c0f0410010b44503e01030a039889040c00c50803402d460164030418000c11003040108042081d00f0290750900e58410b400c03490b09100d0341400c842c002c400c020b20f00301d10801b084201c00c4004c800b031880f8044130311412500100d0002c0300c50117a161585072041031340000461000070298900c5501406001c6001046140c04d050203424461031900101d07084000c0d1040000c0900c81c3c0d25a501d40352008100c4c918041c88128180802042640070502a80c1a055000b00101e010000290103680c003110821540d00ca00d0314150030000c1d960300040344825904c2002d01004642544a1811540c07651400603000d40382c80d401c80d05025090382e009281c0420821003400402c001518200104044080303283c62802903421424030598165036680903d1080c2c042c04d08035460303a200070807404005241307070401c0c00c0950746c0c100e4043d00b1446150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 318497823 1250 318496573 318496603
    0x303040306020d0203040b180d030f15080f011b05180a09020c01050a0c0c0507210f0308150a0503190c08010e010e010e06070206010b0a030f050708250c060905 70
    0x200d0f000b8010380050b40514840c3d07002d502d04083c56151050307040c014410b003030700c19441500207032103480825010b40c00400c11040d0711360000501d0711004400308840030868000000c0d9030083c080c0741600c04000d00411542e403c09403c160440300701d00b00c0140540c46280348413503047c0c50030a152409956104140d20040c50440d40c01c1d55100e50040f201030003010126180ca80892501d03080030074261091540313845ca6984000103145107801c240b4112011a00029040e00302881d24609070009030117401c500e46503a110303880310382c1541807030b180308210700400100b11409480480340070441c1e681c000a171954040c14030202e2003801210b03424542c00c0703050070380c000d03011071742c20300401284045055204282e0124000c00030000724105003004c54035400d05980610050717000000521407a58010002e0444021a0400040c1c1c40c15040000c801d450044451001144421041000003100041d030a910901c2900104110900550021381042c00c042009007235641e8481880c1e040200412032507080e20300d19 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 318499073 1250 318497823 318497827
    0x20a121e050d0501090c0c02060c0f030703111b1318020604080d02100908030c0c0115090b09061f0c020102030918061305042f0d0b07020d170411030304030602 70
    0x148000380c265400b40c515101d03481c0c42c0400025540849106206544845a1740c082e1410310f03c3d0204403c0d42c00001c50b4025a010340100c21000e10010030081c9026842502e8110101c1e00b0204400e0a00c128110b800760284644200001d01e561901d141064910269600141c8a100d030b00514240158591000b9001040007030045250300300000c058003140041e03421a000451904040b80c161242917030018140d82003407010070100b0341e00390007418483c1c28a07000000c0300100b0031960040107080f0790001050311360b241c0014102c1d040c44000d05510072015030340702c0e0041c03030b43c406e0302d02e05403000e07245a00c00c1003291106441103a200b8821500121f000402e540441c20350710345c25580110041c2c0300c240c80344c48200d8074844112180d0040d0b9120702c0e0000c0c07a1504c004100c0001c28100040c04102101c058a0043d520081d503403038107024940240144e26480c80f03031030100d1010386015400346110050154602d40c120500b10305004840d8055404440b0710b03417520030031323004c24030314002c40d00014001c03400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 318500323 1250 318499073 318499127
    0x3032a07060503010f141819020316110303090706030b060708040801060806180c040c0e0d0302010b0909030909180102040b030c0c0c040524030319020a0b07030c020a12 74
    0x31110186050745d07a41621a52410740d102c15020a00d451101c800741c105030306000700e40b002e2071007201d00303540250f0a00c018010241000440c40403a84101d441e45001c08002d2004019968854540b80052103028021071860400076006a503940301403003100708042d19100c00c0b64403a1501e4003560b02d041d0b13010201d84d46603a119140e09018022070f01a40609128182c0092074080c140e91b00e8190443c000070141c441281c50b8400d200181c41100b84080074002100b900454079110042004412406640001081c140c6001000440840a0300c0c0d1b00c2164400d0241040c40e5880381105900071802c582c40700400c040b800321441c0a40150340c4035500c030110100c20024100100030041581c00d2046040d208420180d80800044402c1654070401c6190000410766041b06070203400754188500a040303a0612a0001050b20400b403400104e400503005800e0b000204070000d811103401510508040c000002c8441e0001c3d07440c800881c2c05025039034034682901c0780f280184071000f091002e5640702c82041c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 318501573 1250 318500323 318500327
    0xe01020d1e1a01050a0f140705011401140f09041a0414070b0301031505060111100b09012102010f0e040903050316020c030601090b0a0f09050105030709090203032a0706 74
    0x1d00300d9440c1e000d40d418001c01d454001180542031101d500161111030504960207812103000c001d0a41400511440c42104600070040002a181851040001040c6800d485c00341c40c1c540841a480712410700b00140728000d0960b60000242903842040e0765506a981e03503414036041000c52a45100d80c414020014002480000070030054503c080c1c0045900035075907151080c00b144001d20001d0718180c001000e990382040c140d048070f0341045052412401180394204102c0c107000d0a80c0741c2c0380155584044910445c01c0008a46004250704140108000c0c600e0f85210103600d1403150007410040651a6041a44e000ba0206e00d00645d0140c42040001d0051070080c0041d0300680d030455032a150046a1400c03103100080380308910401401a0905919200c2c0c584050a410078039039902c41c14070003001c00c4075000a40003000800c860720000ca001e504d000103041c280351322a08180e0b00d00342080041805078400004540e505081c1501264107014400204501002a1903c4d00032030b00800c0e400180840d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 318502823 1250 318501573 318501611
    0xe160e0402120f0703020d02030a0611040611010e0c10170108010914031905090612090304090b0d0c0e0a090f0308070f091208070c1a0406030b010509130e01020d 71
    0xe00c01d641481590615000340381e90b0f100c07265100c3c82c15901c08a814401402c10046107589907201a013141c252141a644d150181c030150002400700c8040403808107d041c1c0d000e0b0710140b40204180081144520b0281d1540d01e550403c2ca49900940000c0b2182c912284960300c3e10000d0031031804084070f01c5d61541200c5003c1c0c9170014098800701c03000c8a4142d0128004000c85d100aa00c80700d04e40220484010156110741210f608250300032000d114001090b0112581117100c1d00404001c1c40c1d0b21400c0640c0e0714115101c030780e1300d00e0141d40e400c0c800c0030000300c0e000988c8041d6204006c800f02c3e965501c01c0c8000250415400040001404a0442d820150069400b0f802827907551520314000944200840b00840c252140e802194003070081d104c0890306240007418614060703105514156203540d03442007403007400060300b1305443e40017504102c40e940c9482030703000050b400d2030400e01c0c0410481c0010380c6012481a450905951013102e840055025070403181544501c820500c0f0b6100e620944000d15 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 318504073 1250 318502823 318502831
    0xc1a0118142a041d01080a0b2e030f1a13080c0a0c0f0f09050606030a0b130f0b090603060105062d3001060f030e160e 52
    0x3401884105840d241114003901e5000400d85508001503554101400040d0350001e01030042c4140c10348681c07841c181d49600030006000701d10246514000700b810f0a0303420b403805900030040394200340b0303c0c20005000300d54440e4000e55164101d0078101d500030064005404040c605110302121a41c1c00010000700d21100390300c09000e445260f5041a09542da8440f03940120348030751203600d01c01044000200c44d00098a10078403039104030b4203031900944d2401c4160100e0781140c28202e01024040200609a641a0020b03206801060016061079004036000e8003014058013405a101c1907030311090f84502802079040200a40184540900400c8900c003c00d005102140500c02203000200c0030f04001554030f040b20409421546462204080002040c02d0307002c3c4446110036404a00450b080d185024083c625103482400b84030b8060422380340c41c850007240c030201141c03000e940100b017040d40080b0700da10030007034504002c2940810384a506003882191100e92681280c800404607840b900000d070a0302c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 318505323 1250 318504073 318504089
    0x21e0304230d03091401030c02030d021309020c06090f0102040806040b0703020d060f0f050109050f060322080d06061107171006090c031116121101230117031206010c1a01 75
    0x114101c5e001101601d0403e440800541d00811007603401040a60080c90760700d1200c54a0341c0d4094445080d0001d982c080e458000503540b1010611500240601500b200065090000c40c9072614110850382c8901004001030a4100300344005501c40d8000d8040307941c0f02000c02c80c10487c60381c40701003d505e50b010a0052142c1840716100109540d40200030900507100014454906e0310740c2d210405c08540d00003401640c1030304100c0381d040080d0941c3c4245507005803150090548a25504400d81d08941903a4441c004100e02400001c82ca9000481d01c0810b440701111004034040c41020101c0c40d28800e503845540044c035000f000101401a039001c0b504921855a0902150314501c080700300744d0190303c9108030b841000000c2a0000713200440c10350506807240c207001c418510959009421a07415869030440101a6602201c2d64944564224003521640c05030a030703a003484001c256501d010321000c0248820001010900d90307030003499135001056001e0310302e0703205840ca203c0fa0752620000f0f2169101c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 318506573 1250 318505323 318505349
    0x11030316020c030d02030d0e0307120e04140f0f060103020918010801050c09030706050d111b060609011208070528030305060603010312080a0b190303021e0304230d0309 74
    0x5540780c040b4207020407140d05e43c002d40c2800d21164490b002008a04015003013031200304400c00014841d40020790b0b00685503150801d01083e00d500344416996074024000c00c134040502040407009940700425004814507038403a903241c0c1c07140010f070300910843d11000e0f03000541040942c0d1040071041d009044c2c95a100080c007003502c9040d14a11300d806111032056258004441c10b114240c03052010301895040c108000c140030102024603044d42d8052010121000c80b40400ca48150104010841c0c0103501a01c142040b585441403045d07818952200c000c100e50000103000e130030300c10200070048800f0251106008407000300d039210044070a62103c00c0700401d05050018020b850401c06607030480750091480041021581800c4035000e100400510b134844c0e89a420741c1141e143c1400b8584040a07089aaa410318118103000e4600483c4d13080b1007180c02a0b100c0c40c7d844d1480d0100586044641803881c84003081c10f0700b841c410070354401f40101a004910101c8010605a2013540c00c3c00300c40c055200b8203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 318507823 1250 318506573 318506593
    0x170d0b1201060e0c0d0624020d020d08011208070206040e040b010801060b1204081c06060e0604120210120e010504120e180705070f1101080717040809011103031602 72
    0x1400da482e580320f910108030f1018000340f04941600003c01d13201242c070800044480c2c035410042101c16080d5031030b04292061a010b888020b404014800c0c0c1c0712450b000a10304845086130003460703440c05000751036034201c20342170080800c13050b40e0903100d4055008100e6a00c0340c1d2503001807203c3d0302084070140c80d02211000000795600381031089100390341c101556070345404402100f40403411000b070411a480a010410001148070f1090004995540e400010030b04070700d0118014401e40854002503c0b4940820040000e01541c02c80449115419500045032048407201524040108001304000b14101102e0759815132065201521030385c820304070074410301010700c0200c6003e0720210a1a402400121004140c2103c820007150302282920741189802c61955030a00315112024048030118044804850300b503820100c40c0c2d501400034034020848100c2c00740b81c0441000003a00c080c0074110300050765141e513440388164586406004086941c0e0b070030982c1241c1030113a11020f06000500030810b6007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 318509073 1250 318507823 318507859
    0xa080d060e0114100e100f0818060103020d020d02090a02090910050108072703050601030b0906070903200a12020a05191a09030a0c090c0f1b170d0b 65
    0x840c1039443e041e8207100c1201e002014018100c542108441c14081c021141c1c01d0383e6500c009510802142940d20800c0c14000c01e03030090b040400145c085a4a0300011525a040d401c3c0005e94604590301120042c01c0c00b0403c5c000300701d8007198100c2c00307908001808200600c40103903400a0510850582d5400304507a680b094084213900305000c4c0b640054445004a40c0325032041612000307105840c80265892913800d0300c2840358440c1039000300c0e800d0b04a040104140034103003001a40c031070001c0303018180503e000c440042800c0070f24040241040c801c403c200c040382041e079043c0c0350300c240c0180050303802588554608400d0813030780703500320321400c858500458a420711007882540040d074440c08010181c100ba280002070ba410751038044084206011100c600d076000c00821013818080c8215400d214203011924098442651001d801c1c00141d015102160354461584508903e8017005203030105070528005003400300000015a40c2200030500003900003440d03000480242084400c001254020800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 318510323 1250 318509073 318509099
    0x81b03010c1710171e070311090a060530010b010c0b10081006090515010e040b010e0d080726040e06010203090d0302010b030c120606040b010c080706050403090b1c0c020a050a080d06 80
    0x40190302c1242305005541000f52000781c01511a80001c1016910340740807c4e0b040c041080b2092041c54899003240c2e450b00d40d1807600311075220880007402540030b041c001800d040880324006003d480070b0740c0000d200b903055481c07200c0070300b074540107490409001700c800c80d0140080d8002c03e40b002d440d01020540c420b142e0992a0013100c030603114440c290f05200c0410008261a60a9605001000d43c6d48009940c40110075120346100704500c0307456484a04050a9801b006080c404a9050300c00c001010403000400ba10116400d03404403070915621800100d045008034110305410814030301c107030b5003015019009820086810340031602840c0c2c403c800c211810a240500d1495500a2400716950381000c0d080103949107010b0402c21195500c03643c518042d03a01c91070058500070742d1001803204050f403280307031100200204000c19044c110500b24111810301c200c03918102c01a41c4421309a10389000b8070001240c950000141d401c00c003110304100180342d00c0200c680c3c040346d18254000c184c4940000d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 318511573 1250 318510323 318510329
    0xe16081b06090112050a021b030313110a03050604050f011a01120507020115080d1e080f090f070801060f0f0e0417070606081b03010c1710171e07 64
    0x6000c10040d9a400034010207500100d040c0781080134202907980c00450038029680646080c0303a0050740c03650100079101110003015005071341500200107000d2014a400d030840c61881d0050110340c070804000c0c0015040c3c007041d5000608500510041005014002c00c3c40000290118001c0c84114031601080c3c1e04003100007051804992140102d40514446a02c07040e88003120380000200000c0c0c003c0e1aa01d210f80e032ba8030182e0380e0750202505c84a800e50024104668101d401c019280005090402038904030009051070400580000060401c0600f04400303400c021882c01600c42090711400f04902030511800307240080c807465000029080714039060041201c038681c40201d1a41c07a9656500810607000598105400301030081c900418603e21640c001031019200800c42c40324099580e40b4101031225115100380d150440e0080b0003500a00c00e9000755008454100c916a100500c52024142940002d07942d0041820034500a4000080101c40c0401c50303000341a4402c0103100480c0c0e00c1c000e0340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 318512823 1250 318511573 318511603
    0x6010501091205030d151e0608010918060f0e010e0705030a0314091008090c010e0a1511060406050f130809060a02150f010504060b0f09060714010e1608 67
    0x360400c08070000e401032802c2c0d140b040060700e01d07144c4070040303da058525054140001c40100b55040050420754003189106c1a20550241c1c410f618210b0041c092100502c5503810302611400c02e420b288043c418010347c82035221400f04400b80000b8804001000e180d01030700890b610b0007410300b8140c0380009041c02100c900030001e1020554035039040fa1300c0007003480d110321569003d008100303482d942c190318600303c0826a07646a10501e0401d11840c589021102010706000c600030182ca004e03260f00300c101701580ea01040c400007500b4907850441e40310b140c0c07083c2c0f4030050203440140801c0290b141c000b2070007000c1d000450380e07840d254841c600c1840c201c0034400500006082100010f28180341c405489001110f00546803e880752088000ba0f840084400411442d0068010b110038a01441880c0140c1032442c0c1c507600300369075040e4603100c901c10612b0301c0784501c0000c45c500c020801c18035400c50055050100a0100780100c103185c90783e400800b01c0e080802000080c0100c0d01c0c2c800000c940840f210b0385 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 318514073 1250 318512823 318512837
    0x19090b0109030f060e0f030304032c0a03060b15160c050306070804030e151b010e0111070618050d0c0303050a0c021e101d010c02030403030210050a091202100e06010501 74
    0x16588080c010040c400c45c140080c0900040000c4c00c0800740003452003280aa03d40c0c42000c01d8846651a000c4048100038410b0344049a00d0b03005504e07403070035160550b6400340c070002d910340d46c480000303040000c4000e80070005000083c0202e03c100e40d2000c3c28480314460b075047e02209440d003040585440c4210341100018104c00b00103004248641d0700c8460000d0080c001207800c0c03004590a2620786c0c4954030b850070421580207401c001c2e4609200e51900103007103034002c00c40740e180d40e641000240b0555002030405512a20442c403214000c0128a1545a1010850344071804094001d00940070040341913003c2841c11000881d280c001d4014000c0c506010303805066901100074070410102006c1000807250b100f8007628420000251081540302d280d1490001c0d42c20400011007030955441c44600700031508140001c00000b81c00084400380640007100c041029503034042c9001c000e013125600940702d40a00700d04081c3d40303600828030704810f50019005100d9071800a800b203503500350a01c0381500080750 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 318515323 1250 318514073 318514103
    0x603140c03010e04060b0f090703021e03091b03010b030106080a03090501090509060402070f080c0f07091a0105030c120106051b0604050d0311040e0906010e0a050c0a0f0e19090b010903 81
    0xc3d600006400030014071180c000d281c0d481c04103040c407404039140d5022990000d40301c04c5332885901c202c0c11800300004030a19510704400b01c15250010040b00741e1034007031070250040003a81c085d0040600440090020051959280150782d41c0d0a070f04c800941c04580321351000320315948a008504140c48000e0a110990780755501800001c1d0702158082d500722102800000c0020341c81001840b0950101c0000c1c06c2503402d50798501d04060140c0d011640417407030400d4a811703102c2e000c02c20405241b02400c000786c40340e48420310000c0da88034240e403c02084c42020300110320143c00001401a00c4080c00b14000c0740b02102803201e5840f281980c001d0280d90001c01e00e031350781b540701e50003040d24503a034444264185681c80f00c04410038441a51040c1c1c584e0400301c0188400c070a10342030f459001030300d880113201d0383c00c01d850710380198451721300f41400300305203c0c0e060ba02280c0114a00d480b03208000d070940380c10b90300d414284800300f00f00d8040c806049003041000c403604d40c8a0450582a01d8001d00c4010034104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 318516573 1250 318515323 318515333
    0x1e0303020d14070f0b06010207050609130c050f0703020303010e0a18110d140705120d08010605070c2105070503030c100b041b020a020f04140415060f0603140c03010e04 74
    0x50003000040c62000c100140d00c0014030021040d09180d01ca0f03417100c1c0c8a428198006802d115141d0440c50140c00180100b1001e82d030303503003c13002104a8280340002c0d0003c2d8406e0485603072040c20100d0300e541c440083c020301016400401581210040300307921803141c03158581d40c41512106500424802e080d1144440898005c46500c1c0c2c0644008144850380c02c03581d079880c0626518994002d40c943c20065041040f0b0400003105215090b241001d00740c02019004060080780d0107005000c108940405c030f51041002c0200400050050001e182201e0000070701c180074143c0c1c2880e01240c1c58040d00307000040e40c1c200007007980e22003400c21014106014842124000800701e280f09283e100d41c45084540ca0600c2819089803810043e601420300b41d150348c014041c40829a0000031b00441c074259a0f83d0ba1070444121690b006640301c928840700101091480e0b000e00041d81011003401d00629001400d59007643c0500040d10400c00c2441036540d5028400070140801d21451401e4051703000080c0c0029 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 318517823 1250 318516573 318516587
    0x1409030604240e010f060f030c090c030b06180a060201110901030b0d1707031404061b03020a2004060914130c08010908030f0f01060e010e031c08011e0303020d 70
    0x840e0740122100c002500d1a5640d060380e40f49000010345940d140b5091034080c26030301401018181e001d041040483c50341d620710011128510a5030320f80c9945040c4250021310a400455508200504243c0c0342d00102d032800c0743d81c0c10038910081c440c1e00300560004a09006018537105c82e0312106465041c01c490800550142480c0980306910000c007028550005003401d0b0f106101d0030740390303049507110031181c540500a20b500322040498008140000c000c1c090380140700358481d408074003540086c17180c503181c160315040c04424024015442154810501c40050429070550741c000c64080c0500c42d5a4461802290b0340c803100e00c20383c1c003070800020b45040d5078510b0002d102c500c500104004160344904107400c44100d5202103a582500000744813034102640f8216400600c014420703a10703540b4126002e841400110a0315051010650944055650074032240d65400d814900614081c10402002010036009004042d2107684030301c020150004084040004e5980c143c008100c06400b082050303c02c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 318519073 1250 318517823 318517853
    0xc0807031805010e01021201241b0b04081c060515070302100507020a151a04050c040e010e0403031b2106050d03020a050c0114071103010e0313061409030604 69
    0xd1001e144654001490901c2030f0403c10000000050b21002c0e151802ca01c0c0103010b0303101510489801640030180c041303031000c100724284035044c00020090b0400c1e200c2c1c00944090800f40c407000b81b0508000500154400614584d00c1c04c0b6500d910040c0a140d03420100c4034907005258000c5010b000300c0d080c1c07018040050054501030700441e1003424960b290311040c1c0d181148d440c0c1c01a008151101d040202c00e41d4508801c1503146000e0100013074500e142c4806240d03011035175101d203031988003040c040001307042194050441600221b60960b154000c00401590540b0101c00207441e004072094802800e0041888100c0d456840141030100001a0701c2c01c1d02c440f0200e40701e500d076142030004455507002d10327800c1024442e40107001e1180b1301d0b0414a040000d80900b450521281d500504c82c00d50900d42168150b6600088032085480c0c00b00120f8010710900c0203260072407000042684d40481c01c11a80003c40303106640e44800c2001128052203540030b05030102c2d8041d4407040106002400d00702d808240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 318520323 1250 318519073 318519101
    0x308090402190905010f0c0b0708190c051c05130f0201020106091b080709080705010c15050f1501210e21070b0a0b0d020108130c1d0a0c080703 63
    0xd01c054609410310b0505801c5942010590101003040740c0e58010030321001031015401d28419180041c1c480302c1480c4401006181001030800004242094001a250107003401c54020444103040b11400381c146d5000e0b07052400340104207001e200c40c00344a030155600ca00b08414448407089010303542c000d00001c40c040d089066548500e00891049000c7c80b4142c45000b107440d004031070241d0f803080a00031750f0002d480241000a00c1e401400068000110f032012504280b8101210346500c0c1031030285405000031040b6010308080c00d1001018064014074080d42da1141040c40080d0400c0c01904d0b42d00304003401c0b503803112a0781e1216107150000e42c0700e801c50064500c152603289400c1840944c11841c40345101e03a00c514080b5110341030018040007290301910b00e072402c0201000000003c0d0004007a50790080c100041c080010700250387c5106c0713040c0300717503408101a46003649a02d403a102c803d100d00300324800100d0b80000944440032034007484c802c0050300d07244d44015031140c400440140040d4a0503100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 318521573 1250 318520323 318520327
    0x50a031208191404021207051c0201120c091503090b010306090f1403030907090501030507091e0608100c02030a090b0d0b1c03030b030607171003061404020a0902130308090402 77
    0x2c0508502d005014a1400140c898601450140304102900f0840000341095501c41f08050100e901d0308180c202040c2d0a0f00c12000c0031081a00c0121590b040d1704103c003c0d11404c0a1080900035007082d101c0083e02c003800f00c0c0480891340c1080442c21503d0030503003d441946200d00400200b4035507030040400340c1c0901418140200c1a07112500001c1090207002036607800082046850a820300c0f44102415400000380701951444e281c095a030b008a00a282c0c00c20355a5882650002c001080c1e0a83d40307803441c505001181c0d49002540d21030041000b8842d0300c90903d0301c2e803e0f40501c00310886403002500c0d115010400d00b429030032042d580001501d0501c865440c035400078280d0720038044100c001d02055110b1040c00040c078000b425210034146590180d4442c0b02844100b542101c820101a503c1c107410110755594242800121010360f131001d0001481d0013105002e5801002200c2d21950098400d202ea0a5642103004100d200342d215026000b41c508109200155110000704141d120090002d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 318522823 1250 318521573 318521611
    0x11040305030307020610080f0309060a17010f08100b0102101a1e031014220b04052d070b030c040e1303020c030615010c050a0822050a031208 62
    0x185182d00035140c24025a11203401c221b03980000c3c01c2c0e10f40c09001c005001d007043c804c1589105a8900450322840c2c42007001250340d0f02424401c01d000c840c0d4032034400b030804d03107541d49900011400e1098010340440d070040d2441024941070307501030a1409801030f030080c142c0e0200c403c5c0036001400c0081c9122600818a401890255100e1170701048903013800f454803030300b210664101450b004004124035407690a00200c450f0400e914410700341c1c40b0b80d50b040030303005191902e0704141c50411002d00c001c00291441041c40180000081c0c4d0030304940e5003181c62081d007280103a1760070114451f0002001203a000d440140009440031001e1a048110210711900700340d00c80749403007680d4004176059004442500c1800061560401c02042d142105801610340380c03e0420000001500d92200e083c14490010703451410080c08205002030a600920660707117070800020304509482d489028501c58140b0300d0800b2455145c1541c90000300c9038003440b00d04042140318810380301c142c0000d0003101120a001081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 318524073 1250 318522823 318522833
    0x30209060a0b040b22270608032a0a020a09020a050903060703020a1215300b100501080f01030320370210030515120601030c05030d020c04110403 64
    0x1620203081c070200f586481e80320741d00701501e40ca0048241d0a0580360901c6041240042d403c4903100f0300c0c2080c00152006d012644050720141005510603031061100042c42201c19045d41e510310840080700003141000000d040e40c1c07981d81d02c58960080d60100c24041d003040071015560082c11400b01c6400c010b41804220320000f803d0030303001c4840402081e0005109220141d0044042c149013144507020040344810507100d2203a000c80740a2144102d0000c0409110038001d800409250180042045024042481c1042c119101940c40580400054102042544c001c502a6100e50b10820304000e00343c0c40c684080303820010445001151401c4e02000400320700040c0702d0001011454441500d00c0d444441c3e202c03010390072400074014810b10760365005006965148005000046c0c92501080703d81b241051558900e844131265a0f01c0007e4400440d885c000206485041328010148105150340d66000c0c1615060869910401a00300120300000c41c0f900b80d001c03441c1d003603111091504141e02c0f5524 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 318525179 1106 318524073 318524077
    0xc020f1912090825080a230c060304020613030213140109020403150e010f140a0c050f0301060c030215042010140f0c0d0f020606010e0901030209060a0b 67
    0xa031300c502d400a100120007502c140000c1d01c180c0440342c41c1c4040d54084030800d0a09400303081a100140d550007050380c40d04940c1c0035020902d903649075802c114095208281c445c480142e001d6010015858848104460303400c1c0b0140047c0c2510092030583c25050140c0c00a51281e004210078400541d891580309800c020b102c2001c1881542c2403403042c050900303280b507800090f107020b00d80b000e001009a1110300072040c4840c01c001a508070300040307880303100b003200104050300304100401000f44590b281d40e040ca80240306481c00b2124140101d102d085003581c0a0758900c4114541c402a024403000c0400550f10032a00403004001e01ea00180804500800e044160080409c0d100d00f212604400c030b6a20f0f903050345c140c80003d0101c1402805074070302040200c0041c868000040e405500882c02599800c2c0c004040490036071a5500304091190014480c079002103845400140401c42400 = true := by decide +kernel

theorem cover : BRFrame.Cov 318345323 318525179 := by
  have h0 := BRFrame.cov_init 318345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 318345323 ≤ n) (h2 : n < 318525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
