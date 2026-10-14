-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1402
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:48:14.524673+00:00
-- url     : https://prove2.me/submissions/efeb7255-ef99-486d-ac9c-2a9964ba1d3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 251978417 ≤ n < 252158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 251979667 1250 251978417 251978423
    0x2304090303060603150f14030c0a120507060302030c1b1f0605030c03032701021608030901080f04020a090b0607051b01020f1216020409021806040b010c0825020d 71
    0x154960612a070f9034180a10b114460138580305008030b529110104440e04c0903071054a80e500491400210180c0e03007400810b242c14002441c0070391140c6c03240160082c40103481803c807854442c040c000140e0b68080d00969120b00c060121035414250381c4110301103080510190100349014a080005402d210014450395001c445100000c1080c180b804bc0361034915000059840b81e0300903c0300302039100e8296980004402126030900501c115400180d1030b1260744114240c80207160440450298400001f4221800c030981c0c03000007503140c114502c10170f00b405607006504081c409030309105040c0b03203411040c04910090b01c004e10700356031a201e043c00d0001c0d0814250418215210040c0070390380c10003407510019040700190841034440c45080c2900e11508404288400442d9038900541d501d6910031040301e60090308031a180c03030a85011082182c8112429407099280504641d4654401e500603e28141d01142607841c2101802d490241c0c040500da420220010721090080180c039591404210148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 251980917 1250 251979667 251979671
    0x304060920151602040c0c080d0b0118061e050912100b01390b090303060a08010203010f050d060e030a0f03050a0c0801031b1505090901080102132304090303 69
    0x8071840400c2a6800450307410418000305020000304166500840641c15604a80000ea02240c82c1d10030345034403400480280040e140440c984500003001d4211130070280c006d03610301040903c0743d210102100302c1801181b00103000030008e41ca0384100441d0081d0300350144d090031400d00000d40e0000b01490754000d1041940c0c0c110345c2c0781c031a4000300e0780103030f2141c540d0900344080c0902e0130b100005881d801c0c2c2640360065045412644032201000c01201840c0c6801000d024424a814480303070360789030310503100c190242e403400344d0000d03020030b0620a40341640c140380c0c175030f84a070be2501d4100b03e00e015012800b910404d80e1032048101b0340004000800311401e094680311201807410401404641c80100780c079850381e04000321b090310a40e020b884141901c1c4e06c0607102130550200c52140150f40016046a02003400d85442d524100f5040740203445145422038200c2d006a803a984140c0c203074011605007400e0428500320a00c118841c1065014405101c06800e45141e4151800101a100719078800c1d00826 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 251982167 1250 251980917 251980973
    0x70e01030908180a0b030f040b150306070903120c0503040501120b0414071107030c090e0a0c0f0503070f0b031b070507060314010e04050a060507090308121f120803040609 75
    0xc100b40003100d0040040040c17450952034003040d882c2d1500d00042c0003c0c10304101c134000a04143d00c0e1610040d00c0980502118818a000e11010300f00c02e100c1d0005941c1e19644007122050b40d4450180041c60a9201020f10f0a091800005440706030034000302e003030080d03110074044045466501c1001c81c00061f04003002601d041c990b1010340b140c401d0480c0700c4c1c00f5420041b42400410110701da41801c17910308c0c80000950101c4595410708016901d02c000740021540c2c02c0008a188001c442c580680d2001c4054903017059440807604100c0d00648503225507004244005104008a401e034880c006440740c1c103040c45c142c83c55480e207040c1529500810042569071900ca00842107010b030060240420940009607070900d900c0c0e40740d440100d048010117854460700003590581c802e1074140c000f180d00c0301b101500d843d80c90000c180060f0007100e064a04852001805030701d580c4401410003103c220805150030100b039502c400a903540014410350311252902c3d00d100c000b07120b400c905031550000c201500380320 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 251983417 1250 251982167 251982169
    0x301050910030b0708070e060a0201061e06210e030a02010504050c040b01082a1602090f0c07030c1b08030c011109011202030a2c0106120b070e0103090818 68
    0x4100c09092007003450241c0c0814000a48412046074000c0414181040150b0311000300b1100344510b02d1809070014004600e440003c0d4054000905507018001c030140421800407043c0e49210040c400c0e54002070a0400c443c40400204030f0340c48280c001180c011a901301c0c030070005455031380030405110050b0b65030000c1106014081c01450345031202150140140010f40f40001e080080c00b51029420238120420f00203403202d81e04500c0260794080c04010780310750581c40781d0f83e0381b440f000344143e001d060000c0004003601c01690140d0b00c12800910305d107081c441951011036807504100c0080303c011081c020806135401c40404410000d02d5014000c5544102c01c80c20f050a41e2400c0c450111140800d002640c0c1c681e1b0001116401030b14070100043e2a41d489504880107461030383c050b4800c041c50010301d5180134a43c2c107111660480844024449241c0d20031400c586a014060003070f00602c1032502007494103105414002c00d803907051501194295450701c3e05841680049403100c1802a40f0561a4403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 251984667 1250 251983417 251983429
    0x18010e09070b0f0d0617030a0e030a0302151801050103080301030203100b060405100c060c0c0203070b0703020c0f01170f191505040207050a06060906170d020a0201030b0f06030408030105 82
    0x401580319015040681c54010b18080c240a9000032296041d400702c1c43c0102e40c601948808014240b8814501c2851400c0c90040c0e02c2e58015200d0100146084001c1c800600300040c2100c4074507070603401000880300ca040e100202d07100180101d515110b401816420400090046d0340c0a1030003903010a54030351640c41058500b0710500b4808010b070b41400030200169448905480031550160f4880340c0007006940f0465001c2914080144454540300c0560102a400f0706510701e91407080c1c08481d1082c0d19403081071118021410001c006902106424401d804c040d000040c2d10a0103042100c140c0c0081c1d1401c0c2018201140c60403410701d842d0041000d240380d40c0d40284000c21064904018030307a850340f10380c85c50f08070034015240620b40008524007004400c01c2040041c40d040242004042e440711119000340c00944207040c1480b003040d0f071080002e03101007500031400007950007c0400c00145d60065000d040c94102c09039000f6900001090103403a04002144928441c203102c80c1d4940c141030400003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 251985917 1250 251984667 251984671
    0x3051b04090c05010e0402070501110702120a0b070c1e060b01030b0409080306090903040e0109090507150503040b060303041e030b1803040308090a0f030305070b1f05040b06070218010e 81
    0x300c0303182490403010205403450404426540b0a203007034850800d800021602a05c50040014015840c00360000c00c0860072034058001030b03200f112050142280102c9140d84c800a0400281520210901051115005100140306284180c503131080703440780d04071556890b5200031002d842c4162a4242e0000b00d40e45841400740101c4110b40c200011501030b20752460034000101303164081c032842004a0b0a081d02002a14010008900d07524070940c1c440207414050141e54000311042d105580b00820840800320985294a080e1703a10281180c0c0c0d40d890302d5402181c060b0840b070b01404100004100d2036901e14450642c0110300840c0e004091461415207403008004000c21420b07001c118544014600110845080b280c010280c2d58507171211000085215020b544890030101f00308000000305908500a03010300e030f0013000c03203a040383d40e00c810350707084a64401d4851000e1081038000740202c3c6025401968540d0003c1c103003c0c282001507010070601200f002d9004807400c0400c00400421303000d241c0544d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 251987167 1250 251985917 251985919
    0x307080907060219050c15190816030c090905130c0b0f1b0106080319020c0f0f01050a1206030b040b0a1b08040312050114011b0c0608060d05010603051b 67
    0x40c05142c980025250840750f414100c281ca40c060342241032090400280d405c501c1d0080040388500307d0b4282c83c4010b039000e10000000c81c00b8455014441c6801686502d124500340e100c0c0d04103030f0b00304000c00c074010403c12442c0301c1403000da240003068000c56481294400e481030b611542c106007503410b100003407104a07803040f24400f004005814507004085e003500c10952001719400062003001380540e0150040341c0184405101c0031900181e400c2c0d041514001031541c40c3c080c3c840d210307032440501114106180c0b00079000407605884a03100d510800080c50b0758161b03071508075900c07030890f9500000d82d05103900541d0705803400d07001d0205000701e541c5100d40112055108008a089042c8003460f8202100c40540c14007848200107024113004804030b4952842000c000c1043d0b68585499200d14a07070050118001041c041c005000d88001582c203d5120340c002c0500c08420349480d00450b10800020b104030f4114000446801c00240240218405948603001800d2200c1e082042945401e051428031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 251988417 1250 251987167 251987173
    0x1f060b03060609040e0703060218040e16051e151e0a0801181b08040302011a0307150e060705070923070c0341030408031302010e041103070809 63
    0x803004079610b0100f15000f03007205580c00b04011248256182c00e298503076001800c41400050080804002421000031131401258100100c104901c2c505a656030140300b08640c000c0b080e10306000e01d140504818004914140e9029000e1040d0000b050307040c8090b06c2120b1010300003203203c400c05030582103100c8140000d00c071400cac00c0180c039010003004044180300c0c811498480900c4401c0380d0700250003424a1040411b0b075840300989032100202810701c211000d03001035181120341840150008a05940084000c0c01003041c3c0f41045503126405500c500c0c8201402082001101191100f0020340781040c0640c0103484158074012781e01381070301d520021500c030000d000081e4000a5018030304007504983c2e03070b14200440821070300c0c003564011280541c03000f403150328102c440810f0071080c071150741ca03a815604003511140004e24510f1140002e4400420f0f01c1401c1c00054500d56490382d071302d0781541c0149403411444111101140441d241e10007112104200042044000340e0040030240d040300d070182c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 251989667 1250 251988417 251988421
    0x308010e0f070c0602210c0702090604020405060702210d0203040905011a0a0f020a061b02100203070903020108090a0803010f05030d021b010509011101060e19050702070e04020607051f060b03 84
    0x3c200f040001c1e40204056404500244031580072082240c4170300394041e4180c0306080400341180320740c0000000f01e00c2242340b40e00059941c2072a000360341c01c44802030510350400303171594200f25903a036440740742c16038061030248036541111080003040b141c0041c64001d9903685050001403829540c05030482e030700400340802084210603002e0103c032406000d03031600c28030a24503818124200258150041d06c040e003811040b0f00018190300081040340c601e5000c0712100c40123042c420051380800ca60b00c0b00850a401e030b017000554006d50b40070750302c2030078503041d00c100b2400c1c2c0d5541900b035002a080000100342c6108180098142040040d10900e02c500050254503400200c202c24400c0c1509901c0c1002004180d240169000d401c8260b0b005051000900c6800d844041407504100d04172a00503041041e0201d03034102d41102e1007114040d03039042c1d000d40905170610400310300001c0d02a004a810850070440403001c94070601156050a502003000d080901c0c00036800302c1980d100790080c40407a001002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 251990917 1250 251989667 251989681
    0xb06100804030806010c031e091502071809020604080303040c17030705120a020106030204060306021914030103030f0c020607030215010504020c071701060509040309050117090a0b06040e0106030308010e0f 90
    0x40855400202440c159220000c0d034541186c28079084c41c014215101c942320a00071280d00700d24940107a6145d8184c906540303d00341800c903601c4815124088074050b1203003d410844074241c000d03007841400035062600c1e10340c0d0b5003045031859200319010b07189002c0241080c41860701c01e03803000317185020b030000941c2003002c0703500d406840d501c01101c1114200c2000490300000e5000303402c80c60045400802c10010543c0d281810006907000c02c1c0401c8a509175040300c4280203002d0211502115032001902c0e096a00310381c3c06070f8030a08001515801d00264400d0340d00144d0750790300241701d010f103c0e41c09418003c00400c0e9071441c03e94181c1015106900521141440150005511048403401100066000048200c0c0b40c010318a81c0c020507004440c031000c03c000c6c16000340302502164001c0e0303951068015a400d01c1d039100d9200703030380c80c003081e41003403c0c10b1011038102e860043c5c02c01c0c0020000103100c0c0d54034410900b10b0b1b0481d48200c001c109000c00401c06000c222a400354000021030704007180386010300c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 251992167 1250 251990917 251990927
    0x9020310050108010509240310090501180f031103040902030c0a0207060f27030c0b0c0f0a020a0b07060e01050114120d091e0807060809010b040615110c06070b0610080403 75
    0x8000301e440c1f0809415004550340d009010b08001c0e80c016090f41c1c2800b07000c08440d006050404030540e015070824986c2248035403070071003801e038058005042074400042507404a40300d00c05150003401d20f210505c00410f89490510095000c1c03a901720000f40e0300c241c0d07180c01030305005655000c4024440304545440100d50441441c44004000c080c3c107089800304002c5440c010791003500003400c0d5601d217650215030510018002c00851800700c00f10b031501120090f00503554030140c0402500f00351456010002210701c44064a8400e02ca00004121200710124250844200340e00c80da42c80d400c42508030710181041c01c81130b01c08400300d001821102040801c00b500c1c110301ea10613003505401024207100e610050f0b210300300141080b04283c48840d5622a8001c2000b80c040e1900c1c04954a03006490303055240c41d108603130840e50003a0384150600c0904000744c5242d1101c4040c5c440d0703406624800300e07840d640c0030001d000051290382070700d1840c04c1c03980a12001c11000c010840c14041004e0034400803079041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 251993417 1250 251992167 251992171
    0x8090111161511040608090601031a0703180b06190f03171909030c23040209030705040f0603031b17090d0b131b290705030409020310050108010509 65
    0x240c119410040403071505540002ca110350a08286280c03008000c2d4920014000300211403580d82ca005050701c4805401d42c60381c3c0b0a1000a11100c0d0b6882c02008001912050551150181c100010480303c082003a421104c07141c00100c1c0c0703854018080041da0729003001e921601c914000c4110500340c0c00e007030180d08405d107640005410ba41990900051407200b0a045542c1d00fa2046414070603489154400f070034015043c00112202c041c170300c4011540c0000300900d1b84000c81104510b01d00d0154103400c0c00002d5202442c1e0a4060181c0c1c3c00103d181c3d00c89008040c01091080c200090f02442c60900400c0300210380355006001004102da0310100d400742403480c1106800e444110b1343d030b040c0c100c0041d9a0b03a4142c040141820015003c02c160300c140f0064034404c1c24015542c0c1400307503100322140f154012060007443c0300855000c00044804c410100d49002030440310580300e1a0000c4c43d02d4080c030b503402c0303944661079030b580000030082540042c4801c1c0004010a007841d50103941840d001420001c80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 251994667 1250 251993417 251993437
    0x2100207080702060c010906060501030c120e07150203030f100e011503020405100c17160f060204031e0512090603040f061e0f0e0f0d0f02030c07060306050108090111 73
    0x800c00c80c0901074400101c5032510f60051200713a40d50b105419490203858200c03001d82c1c100e482c1040029055000c2d0141e5205e000d026500c00c1040c4400d81589402840e02ca0f01940c0c080c1300302e1038082111030044d0810f002602294005685a10304040010310000009100266001449100b00a2160f65482d05419900042d580e1105240b040100710003d000f168040c1e0390003210b40106208071a0015041c2d29541d004d400480040c0350301996190081c130030609061081c0030407000c03210114144a62628409105020240c0307407698a4803400013121928840904100d500341e4840100300b4104050080e01c40c2c940c200c46d040139010b00001e4030600004002802d07200010f91140c04110255000d03512600d0f0b5124840c3d10070103181d00c004020b025410301080e440780741049200c040f8000280600c3e160003130070028040900404011500c00c240b503181c00013940700034400d460002c1018461304015041655002420717616140004107200700c06842c2c444d01f6490710081e8030040710800125a00c00319 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 251995917 1250 251994667 251994671
    0x3070c022412130f08120f010b04050f03011506030e0601090c080703020f120c03071107050303031302030a200a0e10031211030f041a0316031a0315040303050c0a0210 73
    0x3e141002512044001e060040100c078104214004000c0d445000d46082c610813850810b607580e0b840d1304031103882000e00801d008218144410030161510f41d115034002e09004d400442d000400300784040a003115508100003082c0c641070b4030640e03000e040080c58010485d514040c00251320141c40a414601d014040c20101070300024800080b0094208560400803034202c1d6244500c0d1141c1d000401703800c180d03403400005285692848d0403000015100c8103071800140a90310710380320a100e4072139000310124100e13050f0181541510100d0301c08207400308602d6440030f2007500480e1f94000c000128256030481602c6c10018810301c8158400141d001066a074402c0b140303080c0c0200c0720400d90b407403084051646a54440003c0608030001c4500c060401c40d86800040c44d86182101004101408210b8000c01c0c1d0024600015011902c41d401c69100c40c4070b500441550f504410000c80d003844a020303402e6210000d03800a00040642c9031150136400710401c074280c1d091002c0c268000352555507402c01c0d015995 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 251997167 1250 251995917 251995921
    0x3030c1b03030b010206090a030509100315060504030b070519111608010b031c050d020708041203170601020d050403020103020c070f0303020709140f0c07150203070c022412 76
    0x30302a440060000d000522002429525807800a001d4800008564018010900030909550303000a00c0310b8581e03450745034a030030250302c4010302150391284c0400000309516174100d01d49000a40d10028040d050580d226aa07ca01b14100304440e001c01801b484200407040101c86401c01060f6111041300d041d600c1d05124500304961f14600c2d210a0b40150260b1350701550001440040c15802800120010781c01da1314a00c941c00d041118079822540c800d00825800c2210310214102c40d401801410b1007607034910b04003501c0e0394190441a502c00b40c110045020744240301c1020b030000b0001c5501140074402400030b0305c48040014081d0280d440000d05054010842848190f400e104000c050440208860398583c0e0343d0800a43d00d00700c0e072045a001318500410070f2000300140d608244a5170035030314100382584540b010501650b00061041e01c0c01242071960a0a0200714001540133038040d554464601c00103004000314900c000c100013004880c0240380003802c0742c03a2815200c207020b8540c0f0495060b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 251998417 1250 251997167 251997191
    0xf030109050406290906031c0c05030706050f0403080a0603051e01090b160801080d0903030c0212010c03060f090501080c06031b03091b0405090a06020c011d010b1014070303 76
    0x241030264075002d504e4405640035801c41c52035801041c01c1910413141007140e40c9540007810f4486a011a034117041c0f407c15001e8118860007501e00000661140088904e072000540340d000441d00291981c00708400540103100a0690001801c0e8201c200d04000f080f0280c030715030795180d440d89103140c85010250300d8000498a8802036205070541500a1040d0800d85098165005074a0141c01200081141c80002060341c00000600f0032980426072140017042c1c0c1181c506440450610800700e070700510030a0b56180120307080c0034600c0205402d460100f40d05042c5240100e843d40c99401c44034080c0d01c0e20004000c00000041c4500007100f007076030015501c3d03c1c2c180440319000c4030b040e44034818490010601986810004415504103002c0c00050034802c128001c11068a00030f485080b1542c0c05514000040340e103682c001c25044498100000d090340c11803000044860700791380c0c50083c99568410166486c10b00c4100b03190b844a003440e216040c14030013a0b0b515403502a0380c802070200340d5107544400007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 251999667 1250 251998417 251998421
    0x608060105211023030d0c050d051e13060e0d0b010e0405071208180d080a0f0e030a08190206060a0311042c0706090815130212070311060f030109050406 67
    0x740103e4800554100d00000040c03412013411840b803400f038440d044214080d01d104a0204183c0d9502501611400311046001c807016004010b080b0301088a90755960800304a00d40104144400f204044699502d070540203032943d001081002e0141480107040d40005801d0f081040c151042c28031155219103450030158582941c1d5000f801070581032072040300c14051032030040c01010346203100203010103004e0424402e04c10071402c002040c0f41028889220340c1400741d150540903000d00c3c589501481c01810000b0f00d006074051041d60b401400050551444482c4081507480015a000034410350520703902060749201103101c06460502c280703084181c00c0d40c441e04500440c2d00a94051a8031904013180c00c5611295a0a8211184540800010312501403060801201c0c0700802400c084040c0081c0f0342c42c820801030090f00c0030100c40600100580e965041c140703101910000801c42d942c01c0d07281ca0a00a0720100d600c5102d513400780200320b007101c00d0300200c80c10b541d058407020440352114604200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 252000917 1250 251999667 251999669
    0x3100615090f1a1b032101080c0607060b03012702010809010209150c0c0415090c0c0b0a020c19030503090f0715050c0c0411090102010605060c06061219050706080601052110 76
    0x10450100240200c81d9a544d404202c0c0c01116401b606641643d842824a5880600c01900c0390040410300c40d49010450960200e507500b00c01400108840d400c088034002040e003007410440110448100f183d080d540c0c0121180d600c00c2e00d001c000c40c60302c0c01450004091a41040740b855611b0b80005400c55101020704c0b81d025401c10150050100d40c0b040304c511080c0e500c05000d04d000c0c0750300c5d01d03a41c4a04584214a0300056540088845125454403682540030b544142c0c60903079284101818950b00d15900e10700244090b00903528a9200d0405490082c1401801103900803190f01040c0280004801600d202c60201c1c1c603400c0c00b654032245281501c1c1044841c07491641d00c14a04102c4140c02412000141700c0050309900030000b49446102308200744c010030110154075846131001510500300300d2401c190741e020a20031641c0c400055400c0e6881840e415000300c507140c100c50800c20540d5040004035411400c00d0070002d0500e8124109180200c80c01a031122288612002094603001c190503660 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 252002167 1250 252000917 252000967
    0x90901120c0305030a020c010e0603041106030a060b221203020d120e0f010f0c020d0c02040c030b06160506060a051807091a04030209060a0b07060b03100615090f1a 72
    0x717900e606101c40081d440f00c02401e0481e020402d998207005c8a45410300480744140d07446804015030014000500a1681004140c11889903807180045210072070f48002e040c0d40700080401c1420a07003254040c4403908070551001e66440610107442002940125507c00307686440d1400400303030b0954121a4000c3c00880040c129180203003804070301030310010341101c518820f160105000142181000301d07580c020f00710b080380000d501d14403104010320749071308003000d0014940b5000c0b0b2140c85140008680f544542050324164003968600000c110080c021240d00c40c2003120740320b01161801e000b082455450f00c604000101062000a500e280103264580141039802014881c0c44da01c140292000d80c40780c00160312030040c120002d1051725000d0540f40503120f8100340700e0300701032440d51040c010f400f8601060750b00d40180d03001110f0126803440f071880101348004403d4100d14800d64054a45140b03074100c400c148003079240c280003500110854030b50b11200ca207545541c80c882c0d05441d9410a5a00c2069 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 252003417 1250 252002167 252002173
    0x1021009030512070f3c210902010e0103020a0215070309030e03060705270402070605060913081e07050a0803070f0e0a0605090f0306161202090901120c0305 69
    0x104090503484000760001c004034180f810641c1d00e8020081c0c8002c0c50264460b8001030400015911030704001d044001e184002c40e0252003207a440c1c5413160380c40f60130011610002184ca04890741c40c1d1085c2001711040c01c41c6040c0820250055030002030803042e200034481c0c141500002c090b00454400c100880c600071020b181c40c1d2250400e102c004024041808090340062640c1d40802030514001ca00640030f030324640c8035185410161100b6494040c1400c2c0f141e40030b14101d5401d0750140d10f807400144540c41c80f40300002090b15080080004a85000d40360701c09285180c00e6500014415204440002c00e040754414404803140502c0b1484e0f00c47e282d8024903d00640340f5090030000024017640c01540641c40342c0c0b035541050b11040300c154411500040c0d010201803401c002080c0904024107607448040c0c6001030070b90000380401d2411009844035881034403104411f09145500220615281d41424400d52620144100140000106004124100c80c01c0304101d01004190103062000310762040a07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 252004667 1250 252003417 252003431
    0x50c1501091b080610081f0f030314090d0b0c0702030a0b040302010606180308090103060504090506060103180203060a05071803030e0321030a0c050c01060f09060b03070906030902010210 82
    0xe50000d020031084004800b0407410321110a507016070582c910440e4041c0800000c10043e08085648200c00340080c1d090b07104840740d0030310400384140e01c240036024840c03824501500d940b80041101c1040081609008002d005941199403840307030405001c0e40201c01140c480e103070480000358a2081c650002c1d410f20481300d8510401c0302ea046e40c907110b03500a800811001d42c0c3c44505072401a80d400000c3c120fa0030344201400040c800001501c400c00040c580019000c0d00c43d004036084032204103080d039050780b00c0402c00c01a9a031501407044400d8410001d83d100800b287c0c0420f540e980040c00380030b8010303126800180030620800540c81a104543c54501c0c3c1e0690301d003400b405101ca0414414082e0046045650a84450a45c0400400c50010b01c1d1031071a9100c4074088014502c00040f101004010001140c142c4424001c2e0000351202e00f0800840c145480400c0080701c07042c1c0d1040340c600400b4810071003140d0b04112210100e45103405c012601c40300c14030040b414401c40c42c803011200c0d49403400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 252005917 1250 252004667 252004679
    0x60102100501060e010e030c030717100c1b0303090c061e0203180d0f0803010f080c0f1309050a080f04060e0319030507080702090a0504120314070c0303020c1e1203040206040303050c1501 82
    0x240a414544402a0350413381005608420b0b540c140000c41e02041e00b040c1c0b40d6844c4d80d12080d0401d0203500a240c001942d1002c0c0e40c50100a40396507111000040c80840d807c258403d100c544003219001c140025454840d03840748002c480b20710a85e0652017100d80e00703a400300744001145500c01d5144d000121a60700e61b102e10282d021420180100da4003813140c1482ca17192400d0030300820766402001405555420386039080840075001c80341c8102e40c2801032030342d40303800114842c029049041820260540700c034100070005040f40160300d03400c0c2c86035105d4518a20f1f0310040107040b07045a5014546656507010070f08000c0300d54850120000d4005003544100714501c03126a0019009a12031120b88030b0403200d900e07041f1b055a010361021000d00411401240c80ac2d805460040c2c001c41c402e00f80941040144170049017004100042d0070004840c0f005144901c42c010f0003021115801c150005045060680104283e4019808001e0a0010014260a040d48204841d4207010284800101d1030760b141c203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 252007167 1250 252005917 252005939
    0x5040213021b03040815100e0105061b0607021c080417160c06020303010521070512150a060e0603070e010e0a0204030f060902090c0703050d020d0e15060102100501060e010e030c0307 80
    0x1450814220001030121f8203410010201008403650031189110310f03400c2070704005450340028040c0249283c0d98090100341074007488400d00c03c415680242c500500241100c1c04d2300c250220800e07040203100003c100010790b40303505140f030300c650f003544243c0c0301d603c3e10307401240460001401130411620300c0b0340020b60590000065040ea2015914545811004841d5400f442c00c44c031041c0e9202e400081041c0210f040c20f8002c0f003420503582d0b08071800c00a0019103010b000406031141040147c031601c090052052074100e40e070308840240d000300505c0d8580321022180040600a8001920303444002c160030440a0701036901650b000681075402013040e01e01790008199a1100300c0c041c0c0380000000b054280d510080e2485240c0689405140982025211000754012020742c8126683d4084c2070690ba9020001d8240c44988110034a51310b007441e500192400e82c004054445450410006108680d4003481d901c900c01401c1c2000701d4884107400019060442e42c805054042c81030b4000090481000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 252008417 1250 252007167 252007183
    0xb070b0106200a0605040201050d06140a05090c0304030c0201090506030702150109021314180c070303111812340506040501020703140309090c030601080a05040213021b030408 77
    0x103071603410002c04000b08000b45100d030340c15044103a400c448203050218200f60803071540548140742c02480c0c840c00300401012103240e41c1084400070044d0604c85040e090030310428014020072100b80c1e05074600b20f40c80700b80610005100904110011185404590190b91103d01500c40140300326200e203040d0354000d58071160748544164442c041400058801d4444c8219100f4580c0e07600b40540345400c040404080e00c01c000300032070704041ca00811001c4114005285070050348260403042c0d5032003207410024140c64594040070350001c410003e0b41100401041c0c00d460520003650a00401d0702e501e04c1090030328000c69101c0c40c28030980d05034079200ca04550024100d6245c1040c860025648490520030103010b64092540940d10090040c00414074400004101c4174407030045034645078070000801d49020007640c030300c500f041010003030150075030700304002030f1b80440d940800704406c0c0b5203a000600500304540300003204650001daa40c08507664104c10514000301d0400726560743d9a80c4102c19916044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 252009667 1250 252008417 252008429
    0xd0e04050f09070b1b100b10030b0303070f02040b030714100c05060c030408220302210a0308150306010b0706050f0709090f1413260714070b070b01 65
    0x5414001880c01d52160445030184503108002c00303145051084464080d4800c05a128950304000b84c01c90030f0745820000c602c3c007218400000b161001d440414020f110074080300200500d4100f041d0980c0540b00041517030700ba039802400320b0145a4803400410007c0c480c540225030507014414000c00c1c41c4002d4070f0801c0c0d21007801c0d940460007a00115040321500f4500c0c400074910b8001001203480300c0389900255400a024001701460440c51104600b07020104d006200c80071000058104190f18008602010f0145100e129060408158080303640710350303904800906100000005c500300400b680b02142c4180340c00707011211b040d6110a04441c458100d6072049413075904200000d40945c911040320f6004001e01d40f40c40f015a070410040704080c061204800c500301e40d680c01c41010754041061082c1c0150707040d0603010f10200c224140061150041d820074610b480341100322504040140080b926a290440c0900c8494404803040a09000081d44070b640400800f150301c0c0305010022105604a0768 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 252010917 1250 252009667 252009671
    0xf120405011d010212040f08090a0e19180b0411040e0304093204020d0605010e0702010e0118060b03150103050303070806040b09061909020a05090306010905010321030e0d0e04 77
    0x30b24508030909074802c031280542141d002e40045000108841c8605c02c01030311070320249003880c4503070001c190760394026030010703c070300350390409100a0ba80040480c4281c216820703424042401d032032400c0480d0400100004010110000c0001e091051511182100c44030042051012a058680c240d55030b41060240034080792a04078180000c100040100062190701d0380c0f207101d0301c603c1000034010b8800042081c0d030000e2000502c00700155141c424076001c2d241120310049a03040524009084070144c014444040e0b14100c030403840104c10180070f0311480c0d88100d000c03501040d805c02007402c00003040000e6621283d0312001208000010010f140314100fa56a0b59085503a9003040000340c2e40d1940e0816007000f00103000c501c15080085005528041450180e000702c0c1d0340c0d460301b00803a40034603004800075001003904156840e0038000c15004040c0c10303005000550458071400c00c0034030814509851a032100b03600805c218001e03040b5100007481d1310250355503a51010405050b04101e02410340c4030324 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 252012167 1250 252010917 252010961
    0x504152f070f050a050f0904170706140f01180b130923030405010c06020f0c0f06010501141c09051203040b0609010605191d190f08070305120f12040501 67
    0x70074465034000484500400010900e46890b00b0b01c1f5610300c018000741c52036514030011003206000d26000b449154490031303000510007400010440d60490160458421001c40001040854000030040304900b01d0f901000a141d503d90b00018a8550b0140140303c807641041e40110a00501751584040003400108805800724100300c466220300c180c3c003450307010900c004c00c40070200320543c1c00382006216246040d49000480d00025140c010030340750104082d0b200d100188020750780401e41000a0390341364600c078104030b01214030843c00d58044268010050740d07400e141040c0802005401c044003140d01141d60b4a0070a1300700b81040c00b004803038a0340906450400001e1032807123a0101c60840701c0740460a1449078109074100c42d00d04030490003030b41019030a50045155500d14020951164404c909200040d25010908203249041d9100350129001003d0402c04114080317500311004005011040d03407405c0102e101c4885029243c818000070312600100802c000c030540c041c0301c07003100170014406c81e5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 252013417 1250 252012167 252012169
    0x102c0f0f010f030b0f070903140106090c0207032022020a17090606090a0227030f010b01050406050a091203020a020415050f0409140105090304030b070504152f070f05 73
    0x1000483c4001080500c486000443c941d00d103401c0c45400682500c0c00c1c81c1600d940b500e036112002c4008a2103026130359502020820781c003540c07060640c10849400a040303000d1454803080491848901c2550080401104010641d500c0c07095002000d65001c9021121a4650001d90000e401803654000451410940e44452070722401200d4403601b10030000f0b0413169541c0c41840340e003d10140cc4284002c0d0244003401c02d200107400c0200d400c11808412514580680c81050715254074905281c20030792404900c02c0e8181d9100e0101c3d4265000c0f4104030341d9880c421007046501e6680c590040040000f411144c50806030f0108644036454001c4405100280211107401c80040e203610416074000000c40c190006810280c108000b070500501b0802e4590040540c0e8a083d1907044400014541000500b441000100b556198000040380b420354205420200702204034440280100188031041181c03104a80e0381c40007801c0e04510070340706619042e2100140a903940d4060051030200e0380a01d00201715 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 252014667 1250 252013417 252013439
    0xc0f16060507120c02040905070b0901030501050402090f09180106060e012c010c050c03060a0212070206070e060c011b02010c0212270612040b07080609102c0f0f01 72
    0x503904501c00f00c3d8420480300003a20f0b00d86000000301c0c2c1082d221101d01c8003044051000c0b030014845404420b50b110440b034001011104140c10080c0310354814441c1cac0b10b041e22035110076641c10206483c1c0190a841e00f80402c284442d0b6100c0c8903815600740200030506560010207034210580c00c1e26090016001090f180240441c5005280e541049502c070510582d8420703920080214002c1e0140d0304198240008241020317803c4958140d059000030741071800b40140204150301140603c081e10040c181450000c049940e0345030400d02c00c03040410030005980080d807240385c5010301110803034541030844078040e0192500402260150080840f1303410010341d44401c90b0313810b1228240c01004070100c0340000ba590368150403505d400803820320841c421001040c1e0b10304d02450084581031941e15001e04000c105150090000340903407806010310506220307810400d03042c0c83c05c0080040c0100c02d00803031640030450b07000300360498012520a11010041c254585030181d0000d25811a0707d0303803a40001c00c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 252015917 1250 252014667 252014677
    0x20d0b1806220608010e0a0c0609080a0209060406090c030c0206060a05030c0d03020316030504050a0f0e040b0601110d0314010b0703080109020c0715030f06050f0a0603050c0c0f160605 81
    0x1e0801001c00300a4000490301c424240b14007840640064225103d0904c142100d10f609420810380d070001c0441401d00140042080040007103140c0300d1580ca013401c0780c968540e0040745000b4000d0041401081c2d981d40e954102c940030707003034a01007040f00c00c02001d0010050205e100c2c009025010300808580345050503904502903940c0680101640314400084c492010700040040c3c0c04c500041c402c4800904000c0c034200c0c040c5009030345444e1101e08102c200500500198025656900201c0c2c04111500d0008038440d44a07402202d10102a9a0400183c40c4111061806140750140d18501d40500d41c2540c00065a440000c40400b460b0b03032181558920b0b80f1401c0c00c0600859003030f00040240e1000c42d00101036008419060310215a658004002e0881e01c402403503012903110701c1c1406844090b403040c40c0080004071181e6080203004004680c450710180100c0d03042541719030004d050040a5070803502040403500440384100300700350025458003111519030300c1d211040e8800048051081e01038075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 252017167 1250 252015917 252015919
    0x31e070507080708040f0602060103060c030216080903011506050c01060e06150307021507120b1915031104121403090609040903022a0f0103140606160501020d0b1806 73
    0x207407408096464440e0203401810086810940800006c0b580c508420175180c0103100329001092203505500d00081a940c0c2d0590b01030402d0b206005840c826114158004ea800742c119101c1c0d5928200380010038054040700240c0b48200c040c0d0b4800050350b17540a40100f2011042000030081c090300c5d00100b0610309402d0310501d0707102640d81ca100c031598101000450700171885004845c40040c00c001041c4404800700e0703c45c0d010480980c140d8191134854051003080307200458030514843c5400071466035800e6580910300c400340030224101c403030f58000e501003003080d407030700c1a103544807a03842da80c169a2001c036000c2280c200d04105401907d16a00105680d0300400003030009040962800c14400108200c60050f81188108a48401039158442c0c11910240100d2000104d800101e001e01102003105c2801c0ba04051410316168a03034181c1e100c103c3d4000608444040d80e50142f4158642c1d00c86583c01e025117954400540c440745010164811764003940184c4048103492030014100c0c0c41031008170740d12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 252018417 1250 252017167 252017177
    0xc121801021b090c0c010c08040b090610030b0901020d1802030f030a080c03060607060e0d0e03150411010e102307051005090102132d03080414150f031e07 68
    0x41c40b520344070141c594089020240b107402c000c2805a000d094400f100c451001082005040c001444003101c00c0c503910001c11002000c1e942072a043c0c2c080e4078040c9200c0549000034070004224200820340480f038403206180c8085c0100c15614000d00120704400e40c00300d100c1d10a074141c0f020b003000e012007943c440500b20340b80d0204550380c903851003c05510040010703502c110100100340000e610391142c4038040c0d034414010092003060b50307006004144600d00d02d0348a0741c03000401802c0d05c49078208070341e401540b101c080c401c4103480e180141d03045400611003c1d4061a0340150849285d40980c0ca0011156015080c0102100030040d41c2114418904090410781003201500d00e800d45a802040e0455030283c00140b9048050303828502482241d00700100303480041401c0c0407440081c0c500080c400b5071010100c43d0040c0b80d580d900d01107101e05d109149207584806000c08250380c584131001ca81c401c4003c1200c0c0d8402418030740c1c441c0f550040702c021a148030405500304401d18800d4131203205948607203076 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 252019667 1250 252018417 252018463
    0x806030a1407030c0b090a05040528060b040b030709121a04020f060f0901092411030d020a030c030c02010b0109140a3803090705060a02030c12180102 66
    0x301d04440001d22501c10452107030282c0040007601d41444000101014035907076072a40700c04400c10400c100c80e513000034400d9003000240084840380543c900344016624000c2c02c0141014020034003d01032039232151001c00c2c40454005911081c1030029441803041e9030301d0414841d2220f8440c03071070b07142900d40905540071001c10503408a4501d140c50b50090b000402041e00d80403601c000841541c8007071110000d040d00450341c5151540c100c990302c000b0300400720706405940c0501180307504411080501004222000c6851009090b082c42114010b1f03500800039544d8102002026002d0002040b100d03000038905a4148040340c410301c00c0c510704c10016500c001c20340d868030541d1051100e410004d035500c50303000040010050042e40303c24a1a21201182d40b16400d28662207220800d011407040d04010f80400801030050400315001d400e40c0da0489286480f8607075210102d15501a01e1040010380c0311b0b18601a40e03411000300a005054175609040004031568001203840388012071150640000301030f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 252020917 1250 252019667 252019673
    0x11a030115050d090501020c07080c1f170f01140d0b01090b120715020105010b04030506040b07030906090f0c1502060c09040b10120b0a080606121603080309010c0806030a 75
    0x164070808050149489800c128607005120115400c161040b542ea03940012424a241000c4c07024100503e1400050101c00b2003103400300d80003110039036041d000310180305100c202c0b990046003034400e00300300d51800c0006850100d88816071080280035083e40b40c0c10340402c07980e562400d42e03d15414158000c03200710751640b803c0b50b100d01521121008075844072030b071401c4503e02e0804002150003412142c810350001c00070840064216201a0400c2100350070812080c004120001049a0040d0348609a000c00717030388800f8210020140d1080041081c1c1c14090507030288088280003505c1c0501038502261280da0303946401c42c1380c941c5644002d000da00600000f54000350740b1005401604070150000c942c2d01462070004100c00503418645000c90021a0f80d280e8180d5284158049110b06444000c0e58906007030380d050342c0305001040750b4131400d080d61044080e040c0900c0f500f40c0300c200d41c4440382c0209490340780105083e0011550203406610702440c3c80011031091075041c0c000c110260260494003100d80b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 252022167 1250 252020917 252020939
    0x3030e0c04090f030c020a120b041b050102031c14040602090301050903090a0e0c070506070909050606070804090f0b03070b1b0118020118030b0106030203010311090105010203160204060504020a1106011a0301 91
    0x1101a64451086d001c00150001940c880c0d50301d02e1310813488aa55441c01c0d00e0900c42c41803150a40340800bc0c8581410301440c2d8001080b12100e0f820031a41c80b002100303c1c1514405000c01d00351a010032040c840034002088582e4010b03148181c0214024000366544100380e0b9544d001d00980c0c26480395401e03008019003031190081d550000e42003508507142ca81b03d61071f054a000c2066882000041d031003c01041094040d2107a240c0101040795503500d00700c3c4645450481c0c0c016400b0f12800180d888001c102c1d201700940c071900c2c2e1480e0240c19200200d0b51796035402c0c881c6d0012009c460800c0110b03140282012018441e09060320ba905001c81080d800d00e0700119000201403001d4030f180d03c00c5910100106401080035030003001c13990740160b6a581585445015201510100c50051312854010302841e078001c016034000c407021311a800100101030002902425190703000c0703900180b00242004e009540601500c141d40c2040d81111220790b43d40c0c2c01c08420304104100c80081c00c100344014400d81c0c24003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 252023417 1250 252022167 252022187
    0x4110d060207050312040203070608160e0316030b070e0409020603010303050c10050a0606090b07120305070c02040504050717121608040302041a01030609021c0b040e060403030e0c04090f03 83
    0x800c40141000d0950391502e19580c002c101c190841000c0c1403c00c4110310742080590054034641c9400c2c0800d09044143c07421040ca90705220052052202505045450402c104440c072150f8841050381c041c0d0340e0078000c402c03100075034600c40010b4030405c400380c2c241014002c085a45d0340c0608460301e942e1950310304a900b608043c000700b60360301034511800302e0803180b030045e24040c3c0c1000c1c00008906242c410060308201084c1d102a02d070798410b01104e4003082d58045070841030300b81401c011a003681c8188044411801c0d03101700039406031400003030105104001400b00c042d20f4900340070f068070084000303c1c269103007201e61030303222034031802c1280340c6c64031119500c01a0000d01c00e0304050300f07064032a4000ba05480c0810000d4018103510300c4031003042d40c3d240c09204000c0c140c1e0041140381c0440e210301080441002c411407900c1c2c0707407146c10994a0342c55030360151062810340390640b101400c051400030082d21010b61011041d00ca0b901a42c68540b034244a18007509510440c001c08003034403681d081d070f020860 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 252024667 1250 252023417 252023423
    0x40b0d0b030102210f061c060c09090e01141003050303070507020121021e160305070521031e06063106110f06060607080310050a030309060f02010504110d 68
    0x900081e000400f0101340e043e8903100340490380c030980c80d28900d804141c078001440c0d2840741d010300710901c00c85400000e210407104e4004501140f2400700c0c2d20181c1d003440540d401120203070729120580175940d0041d448400c200c500207118081a0b00c0d0b09001109524003800081e00607002040400c11030341c01440106081c0b441810030300d41609410a07825891a41c11840300c135000d8000643c825401c2c41c0c850000300301d0f400740404c0f40c101107d40300040d2403205800001070510000280700810701c0004c1012803100100740402131940035028000b24115003040c1c404d00c85100c0b0905034003820101a10b040745c030514000d4441c030309181601c4e4030b0314491090f00d600003041d000e0003c0c4a403807100410084002401103500d4601c410141c4800c801d1401c0143e60107440d40317812034030a01c01c160707444008580d401070700040c0c1c941d01d0781ca070f40c0540e040d03601107036218691100341203400000b016049022101100d509807504600c1121101e8140d090302c40c02c9400424000e2519003540d00e91904100315008a40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 252025917 1250 252024667 252024671
    0xc011710030c1203030b120316030e06160b0109020721030b0915190e0f040201050d06080a030809010b01080c0a03020904090609060b0303071109070e03060f040512040b0d0b0301 78
    0x2581c2d840e007aa0742c5401e6000520715144189500c0d06040d00b500510404c0703003040d1801c62100034001805a1070b4080c1c0240d0050072800304203804141442a84000c107120801800c5982d10f40400d841c0403852040c0790001c540c503080040001030404458070940300c030340303400800c004030024004550451051010002c0c0c0285a0b43d10083c14040c1c0300c45481603c5030041080104000d4481810800b000c52007820322101c1c20740001040c01901205c00700703d908004000c1d1841881d45440c40143e501d0f01640e8145a0061314004001908080005000c9042d84c040d44038089140c440200d840d0913201340001c44c0303010824940c082044282004010070302243c0b01d240042c1800d0003440010f0a0300c4200c00c5c15540c1503111001c820510480d882000c02004040307000b149002c800d0754501740585083c441d95481203809000182000740907040c0d507a09403000405a52091a001145199940065809072198480c03454485d00b84510b040840d0706a802c0402c400703007408d542150900240000e40d4200d50155 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 252027167 1250 252025917 252025919
    0x70c05221d01050f0106020f0109081911060903070210030e251806090e0a030903062c061005100e0d330506030114010905070201090b070e09090c011710 67
    0x1e10300f8407610b40075043c0208a011a0351403c0d070001c2c9005002c0c1c00248035645043c11000000c3c1c0340d5812240f4404420a0100d810300c4c030307640180c54a106003400007805010351801c11544120120040ca103540c400c075040c401c26549448100e08a64160121409a900c400d03040d015100c03001c6261481e4800a02c11140c81c0c030340320001c1a0b150350412024205041d00c1c2c490a0010602600500c508600c0400052945144984005244c0c2100e81300140c40c1c075940701d1146030f0804400d4642c9003410070002e203110605c5440e18586035102d10880f01c11802114413000400d103803a021900c05030f5104180d5070700f11540c044004000100210b084125901c44d1004901790501071481e007003860b102000070121010745c0307940d04c08005982004000070700c43e9141c08040c852a1504180340b0b030644103c800c0002d00d582c1c2d00c52050340103240ea000c4c090064034500081152099100b5035440c1071400c147c2e140402a00c2da01c130000e03070b00c1211051441c0403610404a030403151000c04011747c1e0240c10003018200c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 252028417 1250 252027167 252027221
    0x60a110304080c281a040803070c0807020a0f0302011e05090f01020f0105090c0a060e0913050f060f01140f030a0602130b0406082428030206040b070c0522 68
    0x7031030052005000304c90204a92000d00c0569614007039204140200402c5500d09540d52800d2880010300b41c4090020f042030070801d000c3d020003664040c55018042244082d124074002e880c020a91004900150321020050b1400310680b403480c3c218191a2161402c24a03c4010000b170243d010051504502c1031030b41100d1034040c07d000c0c00703020340c19141c05080c0e5400c103c010b0188540f09608003d06120640d0b0321405c003500c074444441c3e44107004806100c40d841c450f190103404c0c424440429101446000c0a010360710214540082c101d942d2603c0d20381c002d00b0000244910001d54029442c2e158101180b280d002c900070350000c0003850043c0742241e0806d500c0b440109801c2e08590011000610f185003004044916200200b0158050140c5001c001c5802c10001b021007009940c45800d401601940b101c08005081c40c0310003644d402030201703485a80ba408041019004140d060380c100e26400e00004281c104030000c0d0741e424440601030070202044410740c03000f5246428112052580c071561320004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 252029667 1250 252028417 252028453
    0x15080c22020c070f09050c03100b0f0403080c0708100b030307150902030709090303060603090f150f090503130501080f0c0c1c020f01060b0f04060e0402071a0702060a110304080c 78
    0x140c420a40412484c900f02503c41c0c0880d1002803040c00c10300c1c020014800760000c030820901c221500c40c4040d551700c4071040c02024250141c3c0d4801001c1c40c40c0450210505100403c1080545044070104c91151201c0c0710301c10180d507042401240c01d5041040070001050400c01103034040701c032004020a1400c0309501082c80d044850f0300c640807043e5506401c104056140c050907004104500d030510111f2559100c101084c3c2007000010306580c9642c125484150103a007100f02c0c00c1458603420812203c40b800c00c251280d014050240440c1108036012a00358055400180903402a403410001c0759510180c803007481d0301c201d041560700d11806420503008a620598080020302c05d0380039000541241c02c0035400d640b442d030010041c0d0707402800200124000207096404980c001d15040b201903610b01e0109009120703410001e04070310b0300c0903008644141ca5040c0e050060b5032030307402c494060b5540c425400448100c3c8180900c0d0490800206011414090181694400340700a44140812000b07805070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 252030917 1250 252029667 252029669
    0x501060b03070c030305060f010e0d030306030b1513020c03030106050a020114180f070614160f0528210e0a090e070501020c0d0b190504030315080c22020c07 69
    0x2c001102181040c04243d41401881d401800641c6d4090a001ca0712001800100034204043c0c01241440e800d2020b042c403079001580210382000c0003024034181402c403035000e14941c0d044e01d405801d03642d00721540c03c0c00c01d101f107a040f400240041c0d4256402c1004c12511a809085002c0856488110308840c40c0c02d055610b600807241510411103c0d403070b03000403a050200c214403068060700702c1141007120f031360820803000301036140c0810700f44c1d600c400d04185514041c540d00041c1000569548071340412800140c841c000003001482c14100e1010448010480d4407081001020340007441d165682100d1000b450140d044080c2c00c0c0894032414070700100700e40031010761000340100d868003052411200140320b5030015003420302c09400010010f001040158203074500041c0321103001000545ea400000c110f400c3c0c0d00408020074051030a003410000c014000c41400d0a04101d0290740c0007e00703032800203c54200c04006040040e9045507402072031040300714520708401c5543c00304000c0000729001d0003a54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 252032167 1250 252030917 252030931
    0x1050a0e09030415020a120f020c12150f06010e0a08030913020f03071d190e06010516060e06010611060f060301060816030c0605031e04020303070204060306050f10150c0501060b03 79
    0x1010344050030495030180079203405d9818443d0b10323080d0300883c035130210340d80418040644601407100c003001c5080d40740c0a000308a5151030041c0300184001c8e80803030050a40201c20998076840c141e0503182c2041401202840364000c250300400c8020901d013850b440714800302c00c940d14010300385141c800c1d400315994030850b208800941c01c0300b41e05001c1400100501c00c100000e41e02002c81c074902456141c81c6554600030041c401440708001019030f841a8110742032a07036510880d500b2000c19190900280100028420043c0111000450150300c1200c2604800402c0c0c03000385910344888404180d4a40d0251140381c15540302c0d0f0307004c16104010410311000641007083c0045440c510f00f04012034104580016003048410024840081504501d150320007882e400c1c10707001c40e101c41c03000a00d90b01c1250f80003904142048800818001c943e4002445018107811521241c0c4d285d21024080707089074014007040b40c0401420303420340c078400c100448605200f4800001c4017500c0e00b41056082c0c000311008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 252033417 1250 252032167 252032173
    0x50c04031a0711060c0d091104020f04030b06041407030203060a0b0a020d12020f09060f1303080304050c0d2303090301060e01051905010801062115090b03030301050a0e0903041502 79
    0x4000880e52200b0f9151681c450305016000e541000c4c4521905032142c0d0181c90002038894048000348048016001c80c6140000c204555031100b41d0b0040790389811038401074404004031000075215081074090047e078010b520300c503013900d41c1e0b0f20740c1c058009401c090100d941142c0884800b03d02901a034000b005035100d190000d02e060b40911000800c1a07800d0991415828010f010f0394180341c01050555aa04408460040c0c9407401e40c460191180031710f592402e40c94502040000600540c00300440c01a4020802d035409030700548184600360130301c0903004009202901003134408040320714018481c900c525041e245010002d100282c25542e0a8001d0035039580c48900402c114985030654400d14400103c2c0c201d1480d2030b120002c0c0503208144a040284410000e0403003012041070000c0712504015030b420010002400800b440294a5025402c001e510b004814002c9182c00000c0c0c0e07040703400050020441504000035000303190b10280c80c1c1c4215200a00011800f541a40080e2036511034039401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 252034667 1250 252033417 252033421
    0x70501090602091e0306012d12020906010c0b0c160609140c010206010e010b2809030c0501030216060902041103091c030e0327030f0714030705090109050c04031a 71
    0x100310802207880d445800c10050f45544ca9a0354801043d002d0443ea003c419520f848020189446d00c4030401000f48582844200008036281101c4810003404074003e41e1140441d80d221001580c0c0b00c003100c1c0c0054405140c800000e595517a1420081408034036150802c0542e0440d0754440701a2240d11038212101e0418400e444c031245030400195072200c0c4244020300c010f51406901c01c001c800d040c002c0e03c1e02c42c0d40004000240c9260052500100400200411003001241c64005c0c420011404111540c41c0a884006203d62290080e0782c10500004d01c00e0081ea5666a208001008040380032a08191541010751602a408014500c03030030085000e0b014016584480e4910b0400341d200c0e450031b02d89403640c5450300801c00001da400c070104c0000780c0480c100303504e02441603813403c0070401641840380c220b41000000b00441c0355402c444075244009202c8095004150721611903008194010044030010011030020340c10140e0480c6008119515007038494a68240107001680c060710441003541c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 252035917 1250 252034667 252034669
    0x30b1305010305060f0417030406060b07080a1103030720100905060106020d03020307090611102f04060230030403030902090f090c1002030409050a0605100509030309060f07050109060209 82
    0x91a40d109408003400100c1b450550744140c5511040007100501910210000d01003015540c00000644074814100d9200c116503d0301804981c4541200000203104046100721740c0c13000010349001e280c0310388070400300005c0c05940c55103100d004901c02e140c80c800c030451a406030343c10f48600d840190050010b02519810400d010345042d08a05d80001014410801c002d00c0c2e5500c13000740404e9034410325001c0c090080e92a0600d203044410000024054a00314120102038401e108c1c100003813051b8100e00c0750103030883e0300300c031124002c5104040140c1c02c00310610200003c500c440c6980d400c41c5c484074100d40e0a82d8403c190032070300100c2d02100421341d500c412605524285144541c02015071070035080514014135440d40701d00006203818000e00a0b044500d807a10700a10031b0344c01030000d5810401c0300d4981507100c0b03400b03400e16110760f5004440300e80140d18890b1240040b525030010142c021440c1019a009103d007590218054031a440418010b00001601c00e000d200b80d003900415000d40c441e14218 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 252037167 1250 252035917 252035923
    0x10f02030f0c0d110604200d02090c030108160308040b0c0f01020408010204090b12100b21071703070302120a050706090609031116090b0103060e010b0c120c0c0f01030b1305010305 79
    0x100f07444c2d01d0b900100c10040000c442048072650002c00c0406c0740300c80c000710300c04101100d07541c40000754000d140004000e0041d800c02c0245040362003000c102c0720000d007400c01040c080a00c0740805003010100300410701c08829500f0050450b80034031021222014526507009023242c1050300410300b6650001010081e103c0e0310b0040581c0444110754400450f1070030040b941c2d58040c006003203a101511f511070700e1081d65a600c1e504840640b105240440300a036403140546411316801a046181001c030351030928a800003083ea07226661640081103030803131000c41d100c420340210051104000d0304110340000111607019a5807800d00c942008a524602c901d0064a1705080d9141401640d0040d14a07500d00d404401c2205d040350340100b0300054508050004901608864020640e040f8202d80005450180b410081045021500035201c2030030036074501e001c5602c543c40d260340c5950b11001c1c0310744180c0382040c12081e8100c0c0504000a111a8200200d00c002091a410081d840d030b4410040040c01414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 252038417 1250 252037167 252037187
    0x402030a02090c070b061e090901020d09050f06070c1a040c0504090501020a08010512030d0f06050616030e0901030209010e071815090b030f07080a0225020f1509010f02030f0c0d 78
    0x22a491321003a02c00e01e47c48002c00440c9000580701d0030501c000301d2010318080d8119642007001d0360050010f5003ea041003a90f919808a000e40740d0300c500d5000400a40c40345542401e095440011043c00440086031340c5004c03600500281c40c000c80781900028940e40e0f901c41e03007140d980302d4000581c686105001c0030345803420580c44640550004e20001e00301c071002108031280c0f98415000007e100480c500200000d01c0550803241d00140c0003e6254480c0e2040185e000d00c0500c2640e0b04c049646594040c030803908020b00c00290450407400062001045c6114002c0d031108151070441030010050f07650074021201c5603c0610504e4401003c00070a07680210008040e000000005280d0f050200000d40c0d4144000c0c01d81c41040010000b0030090107003030701247c40314101003146809185130b003200c030402036828030012072040707521002c4007034a4140b51b0980c4900e07403000700d000c41c1050900340054404414564140c021400200401c280001d042000380111156101c02001c05000303c0c00083c00c41c50307070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 252039667 1250 252038417 252038419
    0x3010f15030204090219030e0d08180f0a2f0a03060f09020a030c1511030a030c0504080105040602180f010e06210f270705010f03090b0f091b010c08030402030a02090c070b06 76
    0x403503a1035211a039045901c943d00017212003400f00c2181912a00c15084c07840681c40cc02c540e01401500c3c0040c003c002c06071034459400b01841080c6580e003044100000980c1421075500312000000400c081410b50303120507500c0b0040324020807c3d1803243e0002e4654152a0400c441d1019029000c2c0003c0301444031034070005089003404110b04c1c2c1e40300341d00399a1f401f03403840103001c240e16000c81420980c42802554020004580203120b10308040c0303803080283d002400c018102e03021003030b40c5128030720746800c0e010350139201070310785600141006007071103801c1d440301046134500024019111420a824040c8030710030310000e5601201401c1035251480328036411030640e41d4021740c00441032030440022541000300d030380900b0000680c83da141815005407042c0395000d0824940c1408111a4010300004203104805003401e991400b00314150f10308940800c0b014090010f044c03e211100058044001503810500040489450030f0b000d50010b20100400c6401584803413003c142d0400308112102980c1d04024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 252040917 1250 252039667 252039673
    0x10031509110d0b13020102120406120c03092a05100e09090f1b031612050d02070f030b0604090506011503060603050c0a0305070e0316031703010f15030204090219030e 73
    0x405500c40840852000d07080da0101441d013520303502107a0080101c68001254202010385580d42c90f0b002500b540c07211030135020058100980b00c80e042c2d12902c10f100900e94082000904640c4c980c4203010b11a0000004280b949540070011072903580d26090204808241d9481c03c103405200b2050141d000340203440c141c003560010303400145510001c1228440c00b00c5003041c1004040e40280060700c0d06030761400c03400080100e0800411200f140c0e51041020307500400031a2401501600120780d984403520400840c0c50701c694050000410022342d05401c000d000300040703100359003500c2e01400c28100380d001c0020a510b4404298425406004280c002e003501e050400c0140341420300903156120f41005c041c101581c4030300107440300b8080c0425184511014085400102d402401020700b40c140b4001a603010040700d1081d00c000f01440e0459040c1c0300485041e14440d407030b2080c4110840c407010410301c149a024080428002d0b11480074100200d00d110840c48150340000015089604000c900411a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 252042167 1250 252040917 252040939
    0x110106270b060406050d020d1505030610080303180705030102040b0901090f12030e0d060903050a0311040b04120305070b040609120e030d110c0a12030305010503061501081003150911 80
    0x1986003401d407000c0341c8503400d0a90b40c80e1b2a41d16100b00034800c2450b044a4185042100c03441700355426180c2056038400c0d82154065201c80d4010144820b1900c14603625134000c000088018502e030803000801c1300d60008542d001038490001a0a81e0016000403907541004220411345680c008030020051520921007640c0740e050264042d207500b402c03400036081c0135015207440455110029104030180e00100c08009401c82c510b8010724960120a101c80000d0800341e4550b00401068100d5007251868054103107402e01d0708a0072000000b03004416020301c4004d115400100740008042c074820707407065000150002e1507180204902e501919000101700c400c503e903200030344001035008650b01043c1411541a103114003410700d0030946009640d005002c0d881c00082d80302d1440002052140700381c03401c0c08682e803590149641e552040f58520070a5500c0b00b6050704035401100d102d90407010f907c0b06552080e0700c03900d81c03203030303018181544a03401c075640c0b207627042840b01e0040000d0140c282124612858 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 252043417 1250 252042167 252042169
    0x80609070915050303120f060a030317040c080307030305090f070501080414151305070f14010c1e0803060a291c18062f0c0a06090507030b0c0406140307110106270b 72
    0x33450070b4062015042d00c0c1c00c0041000e018003082000c0042c814502202d50b1100c0da8034009000c6c0c0750a58120711640f00c0d00d4010100101e001c15018261141a918259113603034945078405501d0301c2002040590145000c154000d4a884140707d210704805021452100164904a89418040e03806100c01c241420002e201642c01e04000080d110000d10f000010300d02c0710b0420503101919003146000e07140054aa801c00c2101e40005503115280840d07508408a5a031140c9507031001d0305589405a10301000b01e00038081e0340030005086081e488100f8191842c00000c40d1004441007581414614500309260000300312940c001c1c4c00700c800e0050040380240c00d0600201c502411000340440507000041070403d88500100301c041112508050244504c1055040580d12240701c2d000070f03502c1006a000285011045504507402c0f02d0075a42c410b01512504a0100b10f15000586a00c003007005503078075600c0072582401600040c06c100c00d041d0408124408101e07a60300c1c2c0212595914a041080300407003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 252044667 1250 252043417 252043427
    0xf0f0c060910110a1206181e06030203030405010530010e090f100906140403030209100305011d06011b212316080c0c010306080609070915050303120f060a0303 70
    0x1020b60174142030301c0246450390910050314a6130000c5280e220b1441403965802416007281d9640b5809000b01c203030300341c0111011415075082d800080d402d40c0c020031040100e07500c540300a141c40f1081092a54840e0403d0200f001901d486001c80445603000c040144441c1d01808a210b07003207400d80000b003a003103200f910300315100d1142c020036607029541e460040041c1714841d041060300320304404240e0b00c9460700b0715010f4000d40200a11078003c011000d080d1840070701031701c1641c2c162105071102d4000641c98086031490650014100ca041004004102401101100c2096901440382c02d5480f04800b401d99909030900d41c000344c403000c220713000407100c2103480031103251240082c4004c0400c1c2c1d51100d205c2d000200314600b8400420300080040c0c82e81024070041040c0038000d00990342849a6680e4106095642d0801d540d85429504802d0341000b04003c55404400505a0408001c88141d56170002034155000240a1240c0309028410410307400e42050209a2042044650a541d14103503100201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 252045917 1250 252044667 252044677
    0x10305011a012c0402040b190e0328080f0d1a04090c0b030a0204050d14060109060b18031e06150904330906090507060908120f0f0c06091011 62
    0x40b80410f0700c60f501070280c44a40448028010100c00181d40e048801c65240108003480740d000000748040d0850640d80c5008100409034407000250100080e4284410310740c04e200d0405d040300c920804100d21101c00315508050800410a48000901d2004041c000402ca0084c9501c20344034919140b0110001040400c070101950810500c02e51a035035171000303160007481280c00080d4041381800b41c80d030401c001015121040141401a1210b0366030303030700214040e503045008031124100144060f5004260308070403400903070307801805c450b505800d00d50b065407401c1c0c54400d03012407a049481040310f408040a0708a88403202641d150601c1d26203512001c9030400d000c200c1c102d400745401400c5e886174030350f01101c031001e007643c0da0200414070403854180300610013138a0803511401001d0000801c10b0254180d00708841c2990090000c0b1410100150100d0b03000e43c101c074031030800c00d10a54040028101c00b03400c450581400801031414a02945481e0401c1002080b070020b01340501030511b042c045080d60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 252047167 1250 252045917 252045977
    0x1419060e180c070f140604120908061003060902030106050a0612060510020a0308070c080d0501091404020f0f03100f09031b03172502011e0b0a0302010509060f03010305011a01 77
    0x108070134210f03140c0035001015208541c0a180308a1040c0800d100f0164000c48500d641d548504140d42d80c0c0720070890719100e0447d03007140c1e04030405d2010004512650081600e9510003400058820784030000a4074490403504140002500b00e0f884440c6c03219036215004c06001c08885941e01009050b0000b91f803003480b880010200620000030554981c0035095002e00254008001a03d4200d41021900201000d114000246050000301301e04100303005849401190085e10714944c20380c1590900121203503031641580c052141c416183c0303e88030729110b11500710241c50800f1451211505004100206100044900305101600407002a401039080c144101c050f9031100d5943d07407900080002036000810105603001e50a202c030303140c0c65040d80b02e401e440300500304840701c2d5401021686e040342d996861040c0c1203000200e09102640c002c1010703110080009208e20325001e095009484550820ba000f201c040c1e4440070040e20070184001000e0040000b031900c81461100302c2c0e02e0f0403810104807048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 252048417 1250 252047167 252047183
    0x2010608030a03110c0d0f09170a02060f0d0e070504110a0815280e0c04060203180a120305070201230702130213080f06070206010806011419060e180c07 67
    0xa00c4c548041100741c2e55240c5040d019030b80760305000720000d407040203400310b21000a040c0340f2012038240054000c052812100600801845080c0d5091000c40d40c040c1c1018602104280700d0129490524050720304c1511444001c1c1405910305414001a1110007114003d4440107001500520350b010f25803030341c80000303442d8200011001e140480c0711102c001c0c402086151504e2014451950400c48090803a00180f900c1d135100d03175903d0440c040c1d50059015110068004000e043d0182e81ea1080a80748403078000d240c0c1003450365820040c0322a41d61400b049000c90408a295820341d0b03042a0b4003010644d0180106055100300b90000c6c1180c0304440000344035906c1803441c140511074a82c1642c080300b41c811007039a003903901ca040b45603031083e0303d4243e011070b4400d02d0000707404188080303941c03412603040b01e00400780d59090000706696140d16084003a046404140c607001041030710b02d04200201120f4640c03d00c01c000c00001d004040550400f2000016003c074184100500b030701d400c8580c1a5080220 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 252049667 1250 252048417 252048431
    0x1709031b0304290a140d020a200c060a03020c010e0a0507060e04060510030507090b0313061b05030403080705070209010605030105101418040603020603090606090a050601090b09010309140c1002010608030a03 91
    0x117803410034040e1400c40c07070384a4404200707092099046004565940e04031068001c0003051440c0d41541e0b1071700d8003042c076003040c4240001241d4078000d4001d003c2d030108540002c02c0c21918010803601d4885142c0d0145c50b107a001c44400c01805400031500311a060003501c092100b0f904001c0414160042d100001c400c040d521000604010b10901c1e1141c06003480c502460307130303905181c01c1c0c02024031517448055401c107180c080120450071058401c1d8140302800d0b1101c42c15980c0e2610162410140100349000744002000480c006a0711001c400d400780900740c48080d00c950404090082d40515003441c041032141e000d10501c0302c922990140c0d030940c02c25840e072148414000c4003080242400c1e07400250089404401d2141c4010b01188091280c10280c40000b003950f224420641a41c40958160f80800c2040000f8040c00400300020500c250042c140440c0c180410342c1d5070340303440c1814140003040c0e4000e213071404060300c4c0c02d10080d2880310407031000740301a505102d10b8989038031030744c01e2000505a40341c03c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252050917 1250 252049667 252049697
    0x907081c030b031e0c06120406090c030b041203050c0901200c04020d0c1b170d0905060f0702100606050d0b04060302120127031709031b0304290a 64
    0xc0b1000e258007030240d8803c500044200c2c07004003031043d909070250081e18060302c0c1c1401d108055a940c490701d040c1650b103544030b98071940003c191045082e5032503540150040041402115030601031352203110384002c4178044440040c2211405010150f40e0306041128040300ea9100c0500d41040f82000140c540c00f0340c403060400e1510500d920a150418000305084404c040380c0d50188000c501e8035120000ba4010402c1319070044030003040c1c000c29085655000f658415001c0020348420448004e00203150002500d489150107011030f003001c902408003042020b0240e0500003001c0000d40c40106112680c28101c0280140c0254030f02ca040c010366407040281d85a1341d035048000103640281442d503c0d842022400c0c1d000c1d001c2e01080c6810301407820324041061409050b0f206420f0780542c3c0d1258418028040860220005400c00701284420301c00b5031a0f1507a00401d4084806000c0d00031a515890150301da410030310030b000c440070101d015003580841c015044040314100c61a03450070305041d0003106 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 252052167 1250 252050917 252050921
    0xc0e010819061e091d1009030201060b0c0309031506030c0904050304030c030803071806080604021303050d09090e160509070c060f0204051c050325020301050703090b0907081c03 78
    0x50b20000d00340710182401e8880a5260f00300c0b109403840100c1c184103005842554003004001e60544032501c0e8000d000249986600398404c0c14983c0c481e01c004201a5640c0300e072411150080d804001d580d0b0400100704e10149020070806003511140160038542d0714002002940311031540300d0050203441080001000c01c142803013101c0c05585e02c01001001f154413801d088810307410444004000c42d0300c40c803010441e180704034280412500250788190340366890f8400d01000e900480002412010118070120000f9010b2141a0262880f542c403c48907a241511724003d80c2e0107840d6254864114000780c44076032080302602c0c0e091740c0382500d541c1d0298450810440d400a114039019207043d141c00f128001c0e865054004204481b000c0303804540c1581181e0031490540d20301d02005200c1d03442001140301400c014165120325000c45104113844c0030035500801d0a40e2000c54007100069034a05000d400c1001d1485580c0d0001107200040c10350b541440040e80e60b5001c2c050804403811824141c00b10800e1190b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 252053417 1250 252052167 252052169
    0xe01090f2310030e150405070306110910030b01030b0a05060304080c0a08120f0106020d171806040b04021513090b0604030f111201020f190201091e060c0e01081906 72
    0xc0c059606030503074408018010003040550000a01030070003294505691591a18051b0383c002c0040c114840c0340d5600d403c010040c6444140e00c02005100101c12551180c034914004005510701040a1402d0000141165500c01300f10744031307402c65101440f094499a054a40c030550021820b582c80c90f03d02c18003031030109048401809900d0004404000d021510841402403454510310f0005e40d0b201c0c0404e90b00c0d0000009158005580300380c40300d00c141d41012601e50040c20a032020451b1441c0e01c01001d042041c02c45e02904c104072500180800c50030502c2d1100580310311400e1f0a4200841000c010b00702500b9885a5070603240c80c1c0c1311100d4107070384040840f0001d41e0300c2200c110f420100c034580301f41d65094242100d80305e0101609003d44111040c02240c003081d1154a02c18036120002051000303019500c1038400840d0350b41e12240300020203a28400a550103441044184c101032817406100752a20034508130100300d00c5a0b0081e80c2641c22201c03554010041d0940380d407034040680d0010000b0300e19 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 252054667 1250 252053417 252053419
    0x180a02040203040f020a030501020c100506030a38060913080d05060402120106030b030f03090d0f050f06010b0c070f05011b06110f1c060e01030213110711010e01090f23 74
    0x6c0342000010848158001e0442d00007000c2a183d4402c2e8024070306c0d044460072900640c0582080c0f090a00040400c00e4900211a4060340031122005070315800381545100055410f605004000f0b1003400d20340480c0056208201890440b0704c012580d907110107500032000b10601440d00e41c004220241d03540e03015908005040410403480390703942c000080c00780621510250003409000300b140795200000c0100c3d41c0c0c0b0900a081c0c3c840e03100c900e545650b100f40c0a0803003551580540c004040c8000d809005103402050048005034941c0c1d6648000c07803d02007580d125208441c1c06400c1004103980000c942c4500c0901596850105491030170510090010b146a1001328400040e11079908040f00f00541060b00721404109001c40d01c24034a04115082c40c06003003d0354440400400c01441c1001c403020700000040004545900152254042078206241c01c81c2c0c05079003100809000d5030300c000c0c204d105020910b8a6640c480c9041590f2009916a02134080302811407006c12410b8503810b00c2c07011500e14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 252055917 1250 252054667 252054679
    0x1e0c06070312110708030406050a060812091801030b060a090203010602060a1a120714060301050f0d033005070e010c030f05071e0c0506030412030b010e1f0206180a02040203040f02 79
    0x402d14100c0d0170f9600c1100c003299164546008210700c03d440303225900946200c0300c000d0003000c00c1c240c24244160000790500354082e4000076052400601a80e0300c50003103100c2d0340c00c0300c0c040c100f080801500000c42c1c0c0080031001c0c0306100401050f40e0001e0342c01e40000c0901ca001501200414500c603180b44a01403031900990201d00f0000d002d980050035030120394604590b00210100d0004000d003600c02032080680c88241c03036140801c680340809910540302d110b410002c500040c441c20000080f42c1d0a15205840010040301d2044041c00f4041e640e0300480c58030301030100440890005e0f004281e19400a8100502c42464000c118002c504440204c2d0f005425408000400c002d2a00c00040d8000101c580d014444400151810488141c80c090341d40300500c02c0000300c850f0400c80c018280d4202071030400030011614031403600c440000307100c0c0c480351042c0228080500507003c4c0ca4804060a11900d80c400100e2400a1240214070702400e140d0441d40540c2d00e8546080c00c0c03050f01241c55011f0b52182d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 252057167 1250 252055917 252055927
    0x19050409030e210c120c060306060403120c060b0d051f0f0228030e0706141b0d021b010c02010809100c050c060106090303080114041d1e0c0607031211 66
    0x307010000f04401144140120780207601000b061246210740c0d82d900303990b1503101002502e802d140140145505c940050800760800b60740303480b0030204140303034807181020030a07440d0180c05115245c041c05004090640704940fa0902d20755a2958954010707074484120301440502a5249580741c00c1480b200107500820b644507504e55030b05c4040c0320320850050399411602d202c00e00b4548e001e4000c00c0c40020007880605030061a016040d5100b2244074139603100c10030b04012034040000801403201e50801c4000040401c0898004064034000a80c0c40ca0a4a5110009034103c80d85c0e0010402c6d410a0b03081c038100d8203a45030140480c0c03611503085501c000b1113042050106d9500d82c084098200c1810704021100c413a40d03540c0056840c9102404041c0c0001c8411005200364080d884100165200c060f00c0081d4405101020051001010b4440f94660b04200f81040c101058840107028180c0b0a602500c0b030460000c00050962080d84001000c1c01210038005585840f00e80c0400c0154200780c13007583d950 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 252058417 1250 252057167 252057199
    0x5100606080105042d02040f03060b040b2b03020106080706020c030d0e0901060c020607020a06090f06030614040b0315010303170f0411010815060403150b19050409030e 74
    0x540100e00548000905000001405181c103004801c1c2941c1d07550b0b011039650b05890140405000313500f8407601c0c400d40030040020004c3c8980d40a90003140240800500360445000300802c5e20540d000c85841a484204a4094070440700302c2c10002c0d010440300c159208800d841c050b4090030301540044e51030300440034006032040d0041100759140b1b44c100d054a242400c00001a5404401c510f0141d410031941700050141c40e0196104000c0c1600040602d4240901d581c0096124034142d0001000100210002c10140300030486501c042c03c1c050406004e0141801c8a0501d0484601d02c5a44255158035412400713031024050707825980d6081d0100150744da10b80c00c0c05402c610314400c040800035401c400268081c1203040c10b13180540da2001d2401c00c421440801100e5210f0084e00181c440e04015960740f08680d6404003c100640c82041403d00702c4034204240c80032250381d1100d850240c1d000914140245550303100e880103584048500242d199500e00702250000000c265454025192010040321 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 252059667 1250 252058417 252058421
    0x10204030506070f0f1e030f020c2a03120322080702010e090601020d110309041d060c0f030a02130512010911060903030a0e0d021008070f0c11040f090510 68
    0x4150b40301d488030000141090b1341201e0304174000c0c0c0c50350001501c1c0414007460008004101100003a40e15020595820b411400c41c220b03071012048219984c01040401150340c2c40c2c100e100c881f18445414141c0d00c22540d0082511031282c0c12001031b4107074002000680d44c0d1054500361030800030442c030786005216285001051070b842000700b03901066403900c02019500c1d018280c288280c506030b02400c48a0320307001c0207035000c02040c1c00035819070009002810b0f45071618401c0c0d6403088804400105000c0308102c405c1d0134040040c0c03400141c054200111401c0400c09400c03250403802601006a40d4107a04918210050098010652002c00c0311405503103000150004010b0703900400042d0340140858041080341e11034101101d4040d00103000e09900c0d54002c4041e9000d6200c00f92010341145603550018020b0910301e81c400020500050902203843e60052580d084120b03141000c1c8203842160300c0c1d82101d03154030b40d40180710741d07103071051b01d0400c400c0380e00140364184c1c0c0482101d04c078441503800c3c440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 252060917 1250 252059667 252059671
    0x910060605030406110307050403110d021210110c0706050a0905030105040b091902031b0d1502030108070b0702180c0706150501020c0103051e090703080a210207021e12010204030506 80
    0xb1380d007810000c0c019000c00b410380c00c43e4094039581c0c41d420301d813524540e0f8220490f0b01e103030040ca0340003811080c40c1000d6101d018030000d06114001c0a408400c07603c1c04542c08031051520641c222000a118100c031181000811005079415424900d860340104203044642501d1074201c181c055081105010410991a200600500c280015900c030188141c400703580070b5160a20280d070641c443c1100800001c074083e41480307800000f4002c030f403071103030300340c507413003201005200c1d000591903000004101c0720f9070900c030b004040c01549041d14a008003c1e00014840711300c08400300400c007103000120342050360a10880e5401603010324140318080740e80300801070005040c0701e181c0c0580280c5400098561181c03242501c0ba00319400c54201c135600c40c40c2ca00000e204000c1c8030742030740e115002c400f101040280700a003e0301c80640d9a049650a221214042d00408018000400f1401400b80e8070050391075400540d01c45c8031070b8840c4110307a110480019000321350341818a00075413001502005103d00818039038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 252062167 1250 252060917 252060923
    0x50a060e0303070e0306042a0306020c160e1e1504050a140604060e0411010201090503121b07020105030415060f030b100611070303050702030312240a060f0809100606050304 76
    0xc11303041c0040d081c03545402c02102c0003090450b004070219945d2005c0f10141080c4005440c1d51f04006440384c0d603060490303000500388a110360207180b0016510711805a41400780c00c49512403421801e1140c0356030740c1d45003001c1342c800d1100740a000080b201075544041402c8680001e005000508007501c007071000f0074001e1440803103045140000341090a060251004a9071030038074240b141da07980e4886001a10044e901c079811035484050203c080358040000d400c898540092140207800d0002d801c0c48101c0c1e5040084481c0e500500078940540c1c3c001d410b4940c060382204000c2a000d100000242c000c05164000d62a856030080020080c00251720b0480c1c42540c01e040c403440b1681e00da940607500c000d403400c104941540010010301c000380c07040019211440c4007a0440703042643e4070044198501d01210011003c903c2c1d0489142e0009070390161320f440074019640d0840441c10b00c400140085017681e40c42d400c0c0058400881d40c0e4601c00c20050341220400c90341000307120b49411004100ba84244c03425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 252063417 1250 252062167 252062177
    0x20a0c03030509031e0a02040f060f0b0301090e010504020d141c0215010b090f06220e090c090601020304150504090c0f09080106080a060506010c060e031c14070c050a060e030307 78
    0x582c140a401d1020105c80c000000060420f1511942080042c1002003001481d4039110000095142c038800c9400c2c014128900c0b4032170305da6043c8041441250240d00328840d103071303040ca01404090b889010398002810381121111000c82001c4111519100002120108010728109200e412942c0400c2099060640301d40c000690390780c81d10101c80358090114440c1e80210760b40c041d12403d1401c0001045161081100315804001f80c1c181000f0340c041c0d9501506158240d0010051144824005403882d075500b103402132018205a00000d65a0046009041100d00d010f46048450345c040d10603070307004181c104014060107905010041c2000c4501100402091810300c0c0070460750b0b01030045506075100403001300104d070348030348560f00689405041c00d03040c01840007070100460b40c0c0f4081d0000782051203000395039960400551120b0080f150940c5241782e8238101782c0300c5115003070600e80b98001e081407401562a034000d041c0f00f230405110302e000900051805051003100c0c50301201840c4075120507150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 252064667 1250 252063417 252063433
    0x120a0218031f0e0f030403060c030509031204060c0203040503030d1a0108012301050d0c091e05090c09150d0c08180309011101020d0e07050f041103010b0a020a0c0303050903 76
    0x2456502d42641504100e05940400c03050010045039100040f104440b0040340c0c05030380510351960441c0d11a030025607516845400700001c054140c0102504250610001c40c070b0960f24040d1040314800c0688020304040d155548000440e10800036039020f01001000e403959007207014242c400400f5a40710041851198400401156001c2e0503e01d0403180e130080c2030501030060004000340d0b8180c1c420b441c1d0500600303102c0c010003500240b107540301d55031460b101c02100741c1c140f00000f251110004981002c442c86e0142c20b07c041c1d1107520700c80c0c0e00010303005c01c59511003494900041c080204a03200044045002c551750344c0a00c000d400000f012442511000713602d4903103012100c4c60b0941902c00d040207034410400707940c00354418502c003048441748900040c24885500c5190040d2000c0c000c48200d1030740030410500040c5885065444942c3e8200e800700504074182e585900c45010500c504408080080f07000c861540c02807040340d00d4280d21401c4004656103c4c0740160403a0003030ba4030b5034000e02c10450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 252065917 1250 252064667 252064669
    0x70c02042f070c0602010e030322240608030307020304060c17070b160206161b02150a0e0a21080c2e0b090c0a12060902190c0807020114120a0218 64
    0x11840c41d640220700c01840c03560b43c2b0118030203034081441044480c4804a0210500494412a8021046c0c540302c84824400030200191038181c901c03a17041951a500308106000d003540c0c00004640840d040d904007603201c80d49505104494910b03c10503080540d000180c8001040091040c40740b14000709459943d4003240240203d9076640104d620b505203a684500401a15000b1103035078070081da0216000618540d16404501e504911000d810300c5014040313805140b65070070201640712070800740d482511040c030309142c02480a140104000c442e0008501d18001d004518084816400e0a4002c4452110610300c072285801c1c0d4550290001554a41400b4010302007402103400c018001019280142c071480c907040a01c3c0d2040a441c3e003132051030b840d503002d140e0319400303010002c260400d401038560403501d5a540b1088920713408842002040ca1166001a0805045e0386941d502031814525995101e01d52034010710a0040301c00cae07030444ca0010052106c440e07400405092600c4050145003550200c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 252067167 1250 252065917 252065921
    0xf12020d06030213090f1e060c050405030c150a030b060d1a1c02150a200c01110601060503010e060d02090405070302010908121b03070c032108070c02042f070c060201 73
    0x12000300300c0041d1b40768103000304022440c00095400010b006400101141c3d0742c64044a010855400100c1d1011074200b0042c42d0911603010040c206881d110166003503090250414450f00d00010180366071440c046180b034981205891103100d55007800c102200b05480060080071900501910800b410301000d01c0200440c5030314001c099010342001c400305e91448428800f80c224440410412440031407a442c9050441c907a0801034800c00060507000c400000010100c2c50108070b0000968002c0004100b4242d22008890450350b00906500c4503441d444000303001d02d242250040d611072505400c1c4800d015000c115007084134800d03251075240341c0d600c00030380c0e0710f80600c2034190b40039034001d03c4808522000c011a00c01c139a8580016a85012015138940f0300f00e00e210303041070303c898103191138003c0302c105000c0b14210504542c0c20101101c2c6000400180361481c8107070001e02a5845000c0700e50740040c0071140c80c200b085d00480543e01040d80800c05251a08020000d07201420310080003d44a4018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 252068417 1250 252067167 252067181
    0x603020102190204110714060906040201091202010210050c03070914010e01050706110c0304030b0609040b070c021f1d0d0201020304032604090209011d01020d0f12020d06030213 78
    0x41c0c01038144180c0304a032129200150b80020b81e0004d071503803052080110410000c0603124410741d91082c500c05d04961140c0380800080001223541e210f80184400740c0c1e0840b0b41101141c1085207000340744685440100d04002e604000e603000e41d0304042c184150900b6000c0918030808155581d01045503484005400d02c1c10703000000e6011030709a0b840c2c1da1030b03544200028280c0b88c0c01400c000c00d80c01c841b0750080103030717a21081c3c480030076030030104c0c0500410003480c0c0000d0304a98111034100c3c00381865100c0700d1130310750090904001e00101c444a0b00440d12581503c00036101d2030300d07401c0c0e004804094041c1602c410790554204008900e505c0718000e14142444940d4240c06070b00079414141507923a8090603150480305103a82059500c44602034100880041000c1c0a40340005a02c2d07840403000500052100c0c1d00240b400d0301c2040705c0c1001640d00180011001065240100c0700041242c015114038034145031106051f4000240742c1000d510a40140040343c1c0f007039a8140c0c0c0d0204415100b41210f0768 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 252069667 1250 252068417 252068419
    0x60d0201081803071505010302010909051b0a020f0601060807020c0406180504050a0605071d0405090a110a032a081516030209030d080405070902070305090603100b160b060103060302 80
    0x41d900460000b40d1214203400306030244404903460940d99880b072552400c039000f011481c01da201c100600841d40d20180c0300d002444050000d110608204000d138004880403281c040e03403d1000302d14541c00358401c2021a04085200c0c0946150b961224401080d0070812544071000d44074007060035500341404e100d040c1c201c41e05130200905110342c0410f404050100644103603114820307409000c02284a61017260f01590854942e2645002e403a80030340b90a06401004130b01c5240b4003002c001c3c001902240c0c2c0c1c0242684008616515400f11001415101441c0c00203000081c0c030705030103c0d035125280105e02a600001c80b58003241903686119507a07600300c039460505000841070102e00d000300e4200d002e480c90700640c1400b44c00d1021000200f4a060400701c011400160440107200a1100900c001000351200410541c54000c41d40c402038558031a01c0400b5010310f40000008030390601100082c80680030392030500e41d4440340d1001804000c1310002c815075450800700040340066000c2e02c0340d1001c4980c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 252070917 1250 252069667 252069677
    0x7030504090c140d021911030d050601051303031101241202030106030b0a0b1e0612060a03020a06110601050301050103030c150608061f0902030408030105060706020d051806060d0201 80
    0x2050951103030281401c040e0010a10107049040f2075680790141c00b41040c1503075000b0050b00c0d0340811010b5901c01d94048050014400c603040e60b180c0d543ca0105c2107560400540320089607a449180041380c19106414041c01c4031118890040100f45e0f0020410b00d00c007084c1e500a000c010851854035500c00e90502c2504072907000e00900b04041c4100c0f00b40000007900050000400603074a882c1c084108c0001c44914400c10365a001403011498140d000700340c000352045940c440751800c540464000d00c1600754403122811010001036441e40c5a046d43c074065a80900002400c0343d94802c003400210440701d03a24050300440d0300204230350405215980c122601956140448900f903100c0701d070484500d0041888427a00c0b004003180e0400d04101c030074040c0c019245501c8000301c1425000c0c0345030041c0d400803a10580100103100114a030481920b040d1042180c04070b54451030340c54924000d100700460810f0140c141420801c2c0105a1044044c2c2000d80c5010340d1000d03a10141000003500011170020b020407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 252072167 1250 252070917 252070919
    0xa38030603060117030f12061f0912020a1d010303170906040807060f050903090a0807050a05060c0304030f08030105040b0d0f121b0602190f02070e060f0913020901080307030504 78
    0x401100305508090301c040a40345401b401e501d5a00ca02c0e48540c03c10540742044200b888868101002804801001003400b20984c0e03200345402840d00301d052003138401072440440b948007903548030800c010040210903446403e401025616241e408000d100c1500480c0c041084820180c2c0030343c1e52984203c0d00d51000d0b00701c80d50745540e040c07000c2d0001941030740e9090b0380701c0e50030100c40407910401e400f42181b10300a688414880c0104452100303242c0003c00107400200003006503071246a80c06c0140c03881290f50b030382c442c5810749180e8507500655101a00b8034104080e40818829401d000710f040e250241d07014811000660306005103c4100301e00180348201d118801008600c80020707105d00c1403201d15062800301c60f055a094580c108070340f0b042d01e11036400244019404441c03c4140004251400c000c50030044086010f51145403034803920101c4848440040c54a030f0f00c02e0807400c0001c1c0c0c020584102e40c1007440303c81c01c43e92901c1c2d004900808249002040170100041079920302c3e03505640e030500d42 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 252073417 1250 252072167 252072179
    0x1051f1209030504030b190e0f0622051204030201030b01080601080a0b3d030510030f03050d09030c140705060d1a0d030c260304110a380306030601 65
    0x10075501d1010b40c2009400d010110019448001d202e016000604003041c0e06808152007600f142c9440e20401e983c1d90000c0212043d0740004101d56602c425841c40e02c4680451200656100c031041150061680c00f48001101030409020003500c2500e000317a0f000c100c18002213005565100c0c00b929000c2c003203072040002400340212500045d40f1800042d0008500001c840b840440201c00d0f8900850011340b9103180c0003030740705203010050000300d091600b84018109072400440320f07031090202030310000b100b14000c81030500400c00c03500b8011195004025a07849418007c20321080c0d40c0c000c40d00303c01d00c0540700c0e01c115000a5141e003070340c00c001c0100d072074000d103410001d00800104000d05101403850300443c01d0760b91074401c48150310340030342c440102a10301490070004040074a940d0000030b1000e03050580002d0040c00617079a026501294490700c03030702c0640010364000c003103034003582000c4c030801e01e210480070140c83d41104030a90396214404000b07217070302e008019001c00c5500c00e81590290004002c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 252074667 1250 252073417 252073421
    0xa050d081b160f02060a0203072607021201180c05011e08070507050f070e04020a06030204060e01051b070303020102041719020105070c030c090209130207031e12090b01051f12 77
    0x4584942c40e031440d560504e6000c1100c0360409072070303003016801c0440c2034400e0260300e807050300c2841a0889000f102e07030004a58580030740500400a07015008404d14080d50840c2540524041e09102c41038a07950046403070020032206550068500007000c42500880c10b0540c100b205980d001d00d51140941070b44c6410b0212015040440c2c151040d11960405500302401800303000f009c2c1518500c0b00e001850179006000050b070259012a08161040100308681540f01002c141c85070002d20301107540780140344e41000440c082d1349081c0030390f001d058000020190150f00034402c032a40880c9040800711008152034654184108035882081c43c0e031207202c01584241c00600c2c11a129015260442d40c036a210b041c3c1e5180b0940181c039040f82c1c00505e5032518030704003100b8048400940000d5160920568000b02804510204c8403281944200340c5d403d07542c041c00a40e92640c03803604003000580030604003484003000038400c6030f00800c01da40341050842900b202000880c40780351194124484031010000c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 252075917 1250 252074667 252074707
    0x100605041b09060e18090c040c081501140c06070e040c0f2f03040602010609050f061f02030f0a08040b010b030103030c03050915040314100501080a110f030a050d081b 73
    0x40c1c803c0043d10700d00c000170200440d10303010b00010b4000b0719001c40d40c141884101c8110160a50038000130750704000390110150117400d285d15003860310039115030324020724460b80d0040c803111600c9070041c081041101079001c078048140620466041c840032004000c00d03140e59002003607490000e440c6030244440d040c4101c1c03c1400240c450020741c102c40315005092411070704075401c000e0060b5140d1508014603540c0b8003610741c100d4011388844209041c6000040c150740301ca0901c51144813900c401c51580c0c68000c3c07003615921030b01055919a10490f00b4001440410700700e504070f89200b00d000020a4402a140c1541e05883d4951111034402c001d9450039107680c0c01100400b54000c00381152041012403850141000798800e40305002c035045440c0e044d500340044802040c0c2c0080c41c0c00b004000d0b03044002141d00085400801014404105501041c1520403154505425116030342112042080008020031401019900c1c0b5281c0c1d11000b007280d455088004c01c814402600b0b01841070170300e03a02e5500d09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 252077167 1250 252075917 252075919
    0xe120306060904151707140409050a0b10170a05030306060304050120190e0109140301060914090f01020c15090c0909030a02190b01030303020714100605041b09060e 72
    0x28180500b0400140c2078500b0000100f14421102c8010010602c0310721603c15030b080204044c00480d420048214a01910390606601c669211458002481800e100c0542442d8220b0500105460700611070003c55509100d1124501080c107180d5031000b0000c141c1004650f809409907245866610400c0b507e40c10143c4151055581c40300403c0c8071000001c00f404400751200341107510f80c0c805282d200d00341c06c41070032a40240145c2124944060707a100e5100f000340d03844009080214807031100460b005040941102001601d001c24902148c030554240314414500d01003144d50403684110100d084c0c0c000d544040785aa401300c0c00c6209521403075000d0f10707031120f1207600f120000180000001d4100c1d1054400d00095000000c02c46210340c0d050228010b207030701d18919988951132035540d40072090b00502c0b01900309540451883c1c2082144101c80d40030b00c00d90000c0303031005000409410700500c55440b54a00c1149892034100b010a050311540c0501101900d511064924080080d105604070213881 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 252078417 1250 252077167 252077179
    0x3070806030708010f0c110a02010905091509041103010c020304270f050a0515010f0207030b0c0f040609080105060f0907030504080c070602060105281e0f0b0a09090e120306 76
    0x3c42c1070b02e424407888400803002e4101051b2046442800342004600c208894541c0e042940c0c4580940d810102e0308040750801d4a0104080d0b44581c1d0007608400c8035a0b1103a03105111500740414030251004901c0b00e214120001c002140800c40d00760380c0e911462080340c5006040340784004624044103501c1010404002000c00c0310180302c903210084074400c445805000d80c3c0e5405000031031401549501d6056028203001c40f81503120803020f075940e8200c2c80020550800b000000d126084120141e0704201565440319071510f4460070081c0031075099010311100da40c60080020003514203407903e140030b00c80140030f0404645a441c0100d000d440c00403c1550103d03000c100c450815482008010000c001d65401340016504000c10082d9003940c24080448100e0b480e01000c0c03c298004000d0402c0703551282c210404080200c0c40000403c04d103078030a9102e03500c0300c44001102ca44942c000e10b890100360380c480801c2c5899055050032503440d803108090b02d9006000c4c8a03119881200210380225004040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 252079667 1250 252078417 252078419
    0x606030209101209080304030519020303072a1a0f091f0203070201140c120105030d02030a08071205040804050316060e0f0f0d060902090a18020f0d060e010b0123030708060307 77
    0x17451010790310954089002070000a2841050603221444a00c001d9051002d503195040188004104c40140c81032a0101004144c0f2520030715401076049111035800b0751a4a0700c540c0204102c079210000711001c04141c8400000180d0080707011401e40c60781c0400252420f03100c2c54460940d0300139000100f20000350340d600e0042e0b4482c400081c54480c4a4100d89d904503a4502843e4604d50761020f040c0c0c09240603522540c555031655802009640000c44a85003041007661242c8085074559885c0780303003c617082d1411080c081405581d0008005592040d0210380c40030240021000b0300c010740b80f285034009145c01074906800c2c0f0308440d41c2c46070319030700611f500000304e20003001640c0b02e140101d0072507c107039a9500107011420321001c42c7da40080e00220810428000801c9203564402840000344120444060a002ca6130f03400c0e41c0613485500403408000c40c120341d500c40ba00800c041500c084c0456428128928441c0c100b030403466405810102907411900d4202d010390360382c80040c2415030b0501030518 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 252080917 1250 252079667 252079673
    0x1e091208090c090903090a0501050f03041704170615092502101d0606010c0807030c0f05011b081308041e0e0703051e01050609010807020f0f030705010606030209101209 74
    0x80345409013044001030350303681030f203581000446402948824103002d014064a010303034925000f40c0340c0c03058010a580792600c0028048100d58404c40d0405401a070400c420311090140025886114843c0b22224005c210341c3c4034200608a1405c980090485070909508080c115140c281c06049c00d1260045440ca26240d001110030b4942645160034100d41c5554000c103446000c200381343d08003400782001030405000d5144c4c00001e10403240b002d41403080d002c10901c10440584801c954580d0007038001c00c83d0181d081000300c100d01031000050f00240c003480200e24180400011030105a502211291400d0316055215446642954942c0301d4000c042000050006003a00c0042c841c4140b030f58000b440d881c01e4081d02e400380480408405002c1c07c4100144080d454090840e09021000d0a1240541d03903941310032071420f007005500740d0050080c40a1444460000070140c91454450f600a20240e074030381078100c00b00d000d0007109680c401301d450200d011440c0035601894000f280901c0c08254400662 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 252082167 1250 252080917 252080929
    0x80a030b010e0a06020a0c09060b0a031104170303070206090102030907060c080403141e0c010815040f0c030204050f040902031507020106080607050309100b03063402011e091208090c 80
    0x1070711100140e0410354000c1c080103418607c0c04060620410104201030910300c10442d2030140841d01024166141d050a03080b03030081081e1760041100c0a09402003465480c0801e899801c10746914015100d480046204000306000b0b80c0c1c841e0303401c64010004103203070500403940a00030900a13940c0340400c000c040041042d00030449a203080032001000804031800010b00000014805040d542d0003004044200707031b03030100c503e0b9048242d01200300700200740700700080c1c001c0c4602c0309428000351402c1103620070180c058014100300c94046a11400207607210301404155004a90000d5054100e516001d02d102400c0c0039030b9070801030074400060001e444a00c55803522005031919000b1400c04001c11010310300401016107034101004042c1b00210486000c41e82d00d410207801d040f00f1041312440c1a80c21881143d039842c110307050382c0c5c0c1010b00e005e052102034020b0942308501101c600031001c40041e0003540d80503003645180d000c2c80b003200030940c0c1130044444401c0034002640b2400303004c035003420640c2e0704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 252083417 1250 252082167 252082169
    0x105042d15020c07060203160303020c010b101806030509030a030903110307030e0906040e060105040c03110f03040308090d0903111c0c0503010515010c0f080c03030c07060f09080a030b010e0a 84
    0x50000140c1d1554140c0000e4031305150b13544070f58210750040114108041c2c0d80000c10103201d51500b8056202c208420015014110402c84540c0210315850302000382603000140c2041e1800301031425220a8407140210b040e1002120391144980c402c02031061103511a84c0700e50381e100d010303261100b04e01d07084010042c156403062a080c2c0000e0041f00101c98646081224a900000b080740c1c10001d4090082c551a1500c20503c100c42c0b01d1541e6180e03603540e1324065089580520525041d0a0740c4040d01c0c1034011050304162005d80020340c018001455542c00064000b99480032600ca02c0400e528681d18004891a840e0000b074000101c60006a5120360145c401d15031035200e2126014403e0030319082c1801c55000800c1741544669a03640d00281d0303600000e42c0581745030042048904150a42840c0160b4411404411201c4c4000000c001e4128010000f0340025486100d0600c08140c81c13800070001c2d50000840a0519502081404a00c0d80607511610105a060402c03551100303540002a4100e807103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 252084667 1250 252083417 252083453
    0x41d0604020f040e0f01090e0d08070e0301020d05091204050d06020702010504050d0609060b190608180607020708070b040501050f0319020309030a080a15051002120f0c06090105042d 80
    0x113001e00f07010780b0341c0d50020b0443c09050b400700d04126164066400d031755100e4040e0585030600004c1f0b00800c8030b05208408981c02e4160143c0259075500e0360280a034000c0c281110582094090f04108000c20051075044a08556000b040190504601c0e26808001e50101000300d0600c14104000506034580180c2c116466008110020322104242046015030307124551f002c1c0306022103020780c0c030f40c2c0d51418103080a6400d41e141442c030320723034907245144458022102d800c20b007445481d04100f07407180e0000e41442551005d9041d591084e941d030448142600031405414017041c0b05104041c4480d1046014550092100350300030f500031040240f84040364015148400c56420000c0c00000c0c00750454101340e0000b2502d0b5040100c600007000e245036401ea20b009440c8113508040d11404803510812002212414980c0e03000c0d541e0080940e5042c1640c0001c5000d000d50050000282014006200d100d110719004482820290707a15030107440003120944038a00e4241c0d0201c0c0031008604c0264000d50700303983d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 252085917 1250 252084667 252084689
    0x110a0203070b07150603171c1b090b07050304060e03160305010f1103040804050402070812090a1203140c0c010230061c1506180501031502041d0604020f04 68
    0x25181070100c4e0130007007242103603101414207008000240c20f81d030340d2501e0030078464000e035258280310f00161182500c1c0d8041d091800d003028034450b01c5a542003003041aa4106840b40000a40e130703080401164004d5030b0b0b0192880e0824001004210b0051161003102d010003804e17201d5400041d8070701102c0c9685a0000d40f602d039544c11429204034010b01c590241000c01e01d400505502c0c141c0d0303034083c00d4802c500074980a03580100d0075504000780c2d0700079240340c27001e100350078101c600d45182c089070f4034100381d10190380440e80b002007550403034060b1080008041c0502d480c072509990303a0700c1811042e404086003113410341d0b08000d44241e03468002c4000454444120258501044a01c9041074407031014011511035402d40300000c1c1071081c482815910140d0268040c1c030580c80c0411341c0401011640d00c0041002c42000d42d4660701c49040d03126034107807885103404583c3e800116041c841240142c1c010045604100240a0b080c408001652544070000610251a1880c007020b04c000075003183d4271503c0305034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 252087167 1250 252085917 252085927
    0x212011b0801050f0d110607170d0b0904110d02031204081b09060a0603150e0a0e100c0504030204020f0408010207080c010e0a020a15120c050702090906060108010303110a0203070b 79
    0x20740c4803000754010032085440810031404180040c031a904e121000074440000e140b2000c032130b6112401620492908038000500000c094040b100b215440100703c1800c1500d012400c0c000c500d4070041b002d01450300602d0103150b80c90481d05001410b400c0b100166414401e203290100c069401e0b0b80200003411380d91015001d5041c0900420010400b0300750041d2190000008000880c2c69250391a0101c0c0c00a240101d0b84600c08015182805115002811242c000100704014944241c2000640e0340301c01c0121a81c08009030303004001c0b00c02c4511450005401000100054542600500700413204803004510b01a61070400380e0032640300050403103104030040b50b468846e05080c8201c00d003100400c3e003e0700f0308980d0796002850368056406248407442c0700c00850b000c03141c0700b14050000c10114403c20041c1e022070030405803c582203004100d05c242d500e0f8000a018400208120340a4441038490300c0c4e4907401c640d1b042c0c410005401c80141e00b4800c503400f1401581e02080040c00800c1c900068550310 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 252088417 1250 252087167 252087221
    0x3070c08161a010608061c0b011d241306170a420b03010908090307060e030c121212010e0c030403020a060e0705041415010f1209021201 60
    0x910a07210314000030980b04010484190030009543e40681704072501c0ca00c2c60030345a59541820019032001c1c0c803900328000003181c20b00c02010741980104008190100954650110314400400042c800608010041c1c04002500701880e0628520003640000301e5100c6e102c1c0165405003408001991156001d20070510500c2480d100e0340440d4030851003140c80300c42e030940000d07182000c030406031200c1c440c100441c103000200c151310100015000a00030700c04410581000c1c0780c03a800c070307140081c03107800380c00000110103004086002000c0303805000b400743c1a940c0d00c10000c103d8040c0c42c80380618010070b01d07200308a445c040024000480803a408610035410100840f18500c4020701801010804000b480040703a00002d0040903103030b10410100b0400c4100f0f610505120065014a42003800c200d02c92013503041e204000c0c4d12400d4900907801c2c0c41405c042c0110341c07545082c2e0742c001c0458041396a4044604190700079003074160028104000740d02ca9000104e0840f03c0401a0800b0300c0c1c030b4160130180c0703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 252089667 1250 252088417 252088433
    0x1603051b0a120f020706080105010804060e01140a0b0a1a07050109080a020a030e0409050a0611090a060309050f0a020904171216020609071539110d110603070c0816 72
    0x720158910051170540e05001c0c0141040350f040c0900d90502048000080411101d41c103c070b10705020400c024000b80c40c0c0d078505029103440070f446c0d62480302e0400020380d0903411300e1800c103000c47d09403205003084107401d20540641503102d007000f070b80d982d52140808400f059000004213000c07140741d0300500d207032440e5040c000c050140620040c0d100d1403c0c030b072056000c94400540c2450082d009800010b800070f1000c0404094801c0c5220590091551940042d1141e01a03100207015805001a80c03654010906410f40381c01101d90000e501c03145240c080740124000a500307050f1010302c1c0759418500095a014241e07012811500d400e02c043d6414008801ca0f9818455650068010402481110300301003441d414185c4c40700215080000d003103542d940e989001003044050342c1000c14007041e0007044500e881c0b5202c100b2503007a2122a20510030791218102000d00300394a40c0c0200c01c140c24804d060042108590000d4043c50800a01c40d0002d00821081001840c840d4410451100e1030b16543c600001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 252090917 1250 252089667 252089687
    0x30f16240e070501080406020d0b03071e080102091c06060e0c1b0f0d030b15160314210604330905040f0f0206040b03040303050612031603051b0a12 65
    0xa810303000b0500400c100c2e42c02c13480d0190060ba120b413025846e1069400d41000034045840d03440e5061140240000703a00310308945000c081020751303004248260301d03002c6407400c3c0c3c861090100d40001c0b000c0f2180105186d9103406007003481c421000422010350b42d8850301810315003502d03450543c8400042c05011200e4101c007241c081064600a001107450500300103031541c481d0103003081803603220342d5415016900d2044400c10b12000b04100c83c1c550085402140c1d0040700d0410460108100411078120365842d042a00c07241c04803280040c482414a0341d820915000140405800c142c40b5070364901d07041c91185196250303c402c24642c0c005800c0341c0ca40c0d45a18605540320903009441d01090101081c01e403c0449091a0081c0d01d4821600c0035201056240c0b045c0c1d0301030350280c440401400f08055240e0001c0d40524421120a5012403c0548254036481081100000c4079168215140020701440141801c8200ca1002c40021003010000c1414200303038141c201c9542c80c101c0d0002c0c1d8903c2e08650882 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 252092167 1250 252090917 252090941
    0x60306011e0519020a030e01030b0a080f01020705070e01180f1407030b04050c0906180d08070b04020a0b1c0b040e100204051e10030509120703110f010509030f1624 72
    0x10141c45c04540380a894259200e02050405480c0c011050440d1108281c0000812014040b00c2e014072580c00c47c05d0007034120a4040b140e0307002d103040014405404d4150f443c181c136050203555203030790380e60bd541030014000150f90701c13822030b2124445c501d0081c10a42c0345210310150744001c58a22000340801c011036800030048214400103101d80145501e618040c0c2d02640350b15920300b40510498030010704c00d5403400c0340007460090002040380401003901c40307450041e442074601c0d0b0001d03612040c00b025a4068000b05040024071102a20300e64a4150440144031720301034400501d1203c036074926800d16220102c040e005640020b010841030516542c0c0f44628020407000042683d01a000503254105c800807040030580ca0b00040351001c80c06105c0d00b42c1c0d9100b1500195a20b9440d0302c0d0103040396000101c800e2090090f2440804441c9060243d00e1050302e01c20003952802c4a56a600100c1e07400400e0b1400008044298079030000d50b0540c00103907170308903500e80304100d40340e041a450162a0006464 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 252093417 1250 252092167 252092173
    0x30507020d0c06020c160320090c03060409050d050414150a050c0313030c031e030926070f0509090c1e0d061a0102100614060306011e051902 62
    0x2041069011035008000403151420000103082030500301c0180c0150101c41c03065003d0442ea4880c044000c03a4440100c91041d00400401810001008908103003a11201d802001241c0050300b00b16811004644c03206009200055020440d200c162425440c111440003140001400740007241d000c2c6001d500072001140c60055292940d0b40c80011409030200460034400301040c001d500c61024025100c41c81c0c401ca50450400355a0300349100080b800d4072040d1144911041d2490043c5615140f00300d056405440780d01c0c1d403030f25001c1600503040d800b803000422101140000c3c240d00d04e040c41440c000340f141c0ba40c80380e14282000100300300d041010b4050041c0c2e80c4100c51107403854607100355942c43e80420381c1101c0404c141079000318100101c0c6440041c605494250791846010b8950502c4952060a03403c540c0c44c0c40003045013804a5000d802440d0382c0c2c4000c05103220b000e00d420f1006541c014010300d00403070f4880645065842d5003200304c44279000700301e0100d04541001012a03105051200c54401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 252094667 1250 252093417 252093421
    0x5030603012703050a091a04030b07020a0c1502011410030308010501210b221b140301050607080c0a1101170c0d0b0303090307030507030213290d02040c08040c060305 73
    0x112100000c0c0403800400f0b011000c05c240315400c0c001d10320880100920341d821313200080c01c01449000d640c0580811900c100c600b101088205200080b01c8191503072002c0c074455268140309101d82d0842c424100001107640328400c0001450034615480d000308260303214160a1030441c6405004008142c101904201003d000038070856484140f03001d100d04031000000f40803044101140e000400d8a4002c800151007c030b48152460643d4891008d807006445072a038062240c0710210385418075401d400e841031400307000510181c42c04000800b503d6200d242c5032450218503511241c1130445001d800c2d03880141079070000b90156004104000300d14075090301d0006503e05100031109501444050024140c3c6c0c4003030403051a102081150342254008040713924281d034030b180181d41d0b01028002280161403100341000c2c541c229002c1c449042804400820301c0464455030307550300c0c22442c3c0b100d5030b01c180062403038005a151849204c0c00c0302e00c071b13a03a10030880c80d10341401c41e50825143d000343c08141c0341c802 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 252095917 1250 252094667 252094721
    0x4090308100b0c0d11011b020a0c060f050d050c0d05010b07050106060e090a05040201020a0203012c011503020603040f0b07081f0302011e1e03021c0c0509010507080c0a030503060301 80
    0x400c11132848071810448942d41041c00003034010300d10b0342c2509a660900b20303144440541c000415100c45440ba00d00100000e440d140c0c215181c515043e900d601268061001c0c2540f448a03070400d550000049003124185402c602ea024142c0d68203a1109058500c00038060081c050700b8040d40010380118245102d8030510b00d4086140d5400c01842c14022544e540085021684244411102242c000f4003e001c40d0000c03000c0d10560740244a503090308800c140c3c0030450041c1041c064410320b01c1c62a455000d0350740c50764091004690005008035416008661010000344c0e490500e00c0c010046c0b95145035141ca4600c03029070000d44480a08d4200904e1103004100503a0303c07880070746016000300d18000109600c8102560a0444104020f85041203055070000303982d455400383c01420390000c502c0c1404074070400c003601120504031101d00000c40410052009500070001440c21030b2282e022989440144a485410305c00021801c80004500200b40505860240910200710000e64075155000c10441c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 252097167 1250 252095917 252095923
    0x40c030309120218040305090301110a020115082e020c0d14031006050c10050f09070515220b070b2707030209041a010806011d0606031b0904090308100b0c 68
    0xf10139003043e4402d00c800902014410f800f41c40f80c18402070020701014003035801c50840c0360025013440d0b00641ca8000d44035610000c0003840f000302c3e03205002500314900c00d80400d0040881140c5908000248a02150400740540c80100780c42d401c02e401802640c04151002000e520320900040222078007403041c001c0001d42e014054045588606183e0364401a03416801d0420000e011120729503894403082081c1800484000c3c1c3c8601d060400b55442d007a00c4004110300d5070710020440c800f6410034442d03081e152039031041e104c1d8464074078800000c0d99135a810f890f005a500c540c000b1141c41d4080828050008543e01ca07150091100d811041007a10410414542e00d150310701c17000e0701ca400000045400d01c0600c0c10012034905a00211583e5507071078146842c1d83e00b400781f00301c0308080003c0107840412018684030901900000741040d10715110040c1039195400b420011f2010080100118095651070388504c0300e40d1446070310b8003002841c0502120120301082d40c800c1d8214041040f141c11008008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 252098417 1250 252097167 252097189
    0x12160b0a020316170f040e07050a023c010c0905100c0201050913111908010f030209060a081608010b040e070612020d1a0f01090b0d0c021203040c0303091202 69
    0xc4034030b80d03001c0040c0d8240051130001641c44000c44907800286010980f0850300203009030742ca10025103003640c4558504842d0f034821040300000580200f62204482d010701141d2840a10903102c2c0340b4008122104c40000617417101403020400d80d9198459a4103d0300300008030010070701100c0e14803000580c2074002c0d0071030451410003410080c0001d042c00081d40c0d8120303900c0d903400072943c0420840e14440c0c85a1859489059130500140c6104240348286100303901d6181600d442d0746c641516a891a828000d04e40d07400740c603c550000800c0c0300030462107405c00842c0030080b040070040200b01d10b00b0510030f085a240780b112501031401c0400c02c99200900040e40307000c0303c0d040d1500d081d00d00140c0740001c0007800384c194258556810043c83c0da000c1c1401d150503080d044811203010000b81120340c0195215002840340b05d0b03819200748501600c00a0f190b0081c0d68040c41401076403c100c040c010152020361085500b00e4260394511401e109040d44181c0e0040074007403030071401c198441c10760001203d080c61 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 252099667 1250 252098417 252098437
    0x60907020607030e0a0c030c06021204030f06020a050c10052e050105251a0a0b131107050f0d030e0f0703020d1a070e03060c0702150306040b12160b0a0203 68
    0xca002c09211382c0c40c100195034515400c00390005c1000d8403842d010b41014100c0c821007005201e540040d082001d140000c40e0102c1794405155104408a40d0f25140a50821207154083c00750038070030041d01980c103100380300b4440c0d00c2480c0050646012460700300c4010b0405032402d814004075a03195400389c00315801c0c2042c0e6509090039031b126880310b03103800c1c0c0381a0f8803084030340c2101d030b0394240e00300700020030242c00c5074810301c0392010325170b0350340d0f01d25140c1218550040c0c50b502c80310034072804000541c250300100318400300282c00f6150400c59103445141910303908200080b580310380812040d0301d134140b0440e0000054034000c0c4c40c4903074134020340d59600d42140c00082e1080a1311881c0c00d08104c107180e00440c00c040c2c1503000e5841498040e2001e800311001c038070094000e006d100005a40c0011900c2100e003601c0e40100f004454001c0c161078a06240c1000303040315000f9684d0085403104e41d8582d0007004c00003880c90020000500300032541e032042606c1d54050407601d001400b603620400d030003109072900010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 252100917 1250 252099667 252099671
    0xb1b0d05060a030813050108060d03020c010f090504021308060f010305120f12070c060b030d09030b130204020301030530041502100e010204030303140f0105220c0e0906090702060703 80
    0x1ea00c0c00103502c40c003207540018586200003480c3c03082c051622002508a503002d0300c41589650700c070014000d6001c404100100182c12811150f2000e40c003031111501c02c0c1209d45802d9090f02e032100c01040403a840300755004294050b01c1d0b0100030719041004695403066440b2103800c20b40d451a0f44d02c65488049200c0750b8883c940228407100600f0f80c45e07080e41d01482050302840a1420502c8000c0d000200d0a2025030344c40b8107219500c1000e08000400c1d0316072980c90303910001158a161507500b84440c2c054840c50172810000090310160355580040d41c0654000c501a01d441031224040400340c0a0501031402009450304118100044902c103580071511a940350040a03091044101d003000c904080d51081c052a11884104560055010300300782c038400d0301d04000714080c0d20711580102ca41107945030b64100c141c80040c0b0150500601e03000030225100401e185a160f07246501c0140c0b000212020300054401c030465442d4a0280d000d160840810707240c0221600708100c00039203c000061410f0705040d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 252102167 1250 252100917 252100921
    0xd0203030f18040606110d030629040b030114120606010206060d140106260c060306010e030330060105030906070f110610060905030712020d0c0e0a090b1b0d05 70
    0x142c0c0c0300e000009010000b4000c03c003031621001c000d041480054070400d8184240300c550242140a0f10444041d16103080030014010303481c141d2500c0c088089480c00341d880409200000e8a80c2699015501034080540c41440a8606e41d0078003590102c140c81849143d8450780511031903980108615400900c25034003442025024149010003501d4680108055842d0920005104900b00324000b40c52413400d0512020003802d40505966a444000466100104001103007030f40d0301600b040100302d0005000c0c2ca0030203594001c0100944075540c0c00e08064000302e60b0722808030b4011441c499011609007092170840c21f2490300703284e855800030590018401080380c1c0c5007149000e08182c141c241d506c241203e00714541100b80c0039200c052841a0000f02d00d51240208080c9004900301041c1c90111800d886462515020400c0c2024070742c1c0309580854100d100440c0984a9401007403240c0c680f86001304c2c01d12903e190083c05844d009044030035440e04103032800d18035001c0070111044900803071008101a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 252103417 1250 252102167 252102187
    0x100b030a2c010f0c0e090f0a090c0b07170403150b06040f12020910030203120a0905040603140d030b180a0f02070302061006020a030915020106030804090b0a050d0203030f 75
    0x1003801040d101c40d801d07194900c04030403a01500301d40011078005405001c110014a0240c5402e105419250790041800380001c8a041035110035546c0140c0c942000b0800c56100e89901c0e03074050158002c0745649000107110350601000300007020128000c3c034005442c2c64236540712042281c008a03c14420551205d17500c00081ea5804d060310302410541c0012050155101c0d0940305e00307920094101e009002c40310014403d56214a0f80c18101e9030064040d101000000d15200000e5001c40c600c1003e019028401148507103a40c41601d0141d407081080e2250b80f000722964a207800c000000200816040154128103611003000e9917000c400c44007a8070045031950048000501081000c81007005d201191107030925900080c3c141c003e03185003c1d03d801903616550100c0e1240303007000015000c1007022604010301180e008804600c40701c0c034400000c40039100e5503052510b0b40300b50300c40186940c49aa10719620f1070081c0440009103000c4808a200c3c040e40e0380807035128011010741240d0318001040503016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 252104667 1250 252103417 252103451
    0x30b0c090a0b04090f0609061d090f0706080601172502030c0a0303273801081c2109030c08220b0a0c0b0603030d0e060906100b030a 58
    0x20781500d5114a80311600c4d144000d00406844c0c1102154608010300007418180c0d5206680c10b440d403608022520240b0341e80543c01c03086014000e1080d500c1800c40402c5191414401e880c0035090f00c1da2282d80c241081000105031700ba10140030f26480704000c0620410b83d85101e00701510018070043c3c4a00e0718180d40c8240c0c218040c0800750f030024050840c2c02d00c10554545d1240300103c08020140030062582a4400b0188020300d05c000c1c401c0380c0214607101c0d5000094505120302c40c112400d1442d00d485040c004201c0325080c0e00c200300340d500c10001d035500c1c04901c2c00c809404141038900450394000b10107102c1e8983c00d1208203140c071103075142c1146051520521031071659503000b6405aaa4101c804150030b01d14800b40201c0b0000000e400c80800d0560359003003115071a455983d2101061203280e00c4c0c41004a0014001c2a4503100c1005600d11412050294000802c00f44029160f5403402c48002c606005000308008a545102c030710600400800c1c1d000d8035000441c840300010007e405888640c0c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 252105917 1250 252104667 252104669
    0x2010221060d03200102041e0f080705060d0209120a0303061508060d030e06030108071404020906090405090f0a0605010f0503060906040311030403020a09050a060905060d020d050a080a0801170601030b0c090a 91
    0x4c0c0a5000150118511700b10103100221032030040138140d81c60b5658040342000e01c00740e0048000d40d401101003000a80340c082c0107000d14441341040146071050100c0002c1c10701c3c04d416051100c2f5001804c069082c103416200c0c42c40200311104040c001d010003d40020001b8200403c05481540d40c8000c00003414492551099000f2014203031075581c4d619100b160307035039000740d1003001c00500e4140c10346100c604050082d08c20211014100a05115140c01080040d15000348240518030400d1184c2d90085000c111003a222801003000050a5040983e9541c0b4218241c020303600951114040c4540d242001a089601070b17090b2400800c5840b040e04142c0c21445264070180d445841c51501007110341550b44518090145020308202e415903840290781550030481d011036100d500d20b9004400b50a1144805031080d100300141e520210156440b41c0050304012100070025820300010300100c0c10940204441c002040014503056146540d205000000109400098100030404080700e8596824503c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 252107167 1250 252105917 252105977
    0x181d0f01050d080f16080409061e1214070b07061103090309190b040303081504110414220209100201140604110702150c070506180402131502010221060d03 68
    0x320005605041101450300301f4010400362520b000e2002171407200319901070402824010006105034603000f1448080001c0342000d4a00c1056180346c033070b450000340421406403540700d80745519030303071a070030850102d40313030540c9103140032038200b05120741400c3c000141e40801c1c0c800c0303178200c0180c05400c1304407a505016078041c2000c00c20200c5d01008054112043c10b11400740c0340d40c07213886000450208811794020181209a440701040b00f4040c140c2030007205807690070060103244003402900000100a06814094001c07a079010404c02000e1a2240700b13010a00e2551000b07000d0300b80c40038420f443d0400041c2805c1d01c0345a0fa000b0f0321110400c21030a5800c0d8580051078041c1e0f0318001c074030341450355001c02d010f41424024990007041c2d52521100b03881c1880700d00b417000700800c1c000c0d40c00e110095020010328203440c5040d0000090254001c4a0184641680d50000d6182c0000c0200c180500c5608848614403100441c00c106050315418034100c5602d070985403950840c4000016406012549a205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 252108417 1250 252107167 252107197
    0x1090c170a120201050f130f02100302120903040611070e0f100e0405010501030201030b0102120403080c012a030f020903100c03110a0801030c0501020708060f0601181d0f01050d080f 80
    0x40b0621540642c004c0b407180007aa004040b00b41e03100c0860400c1d80140100040c20340b40044511009420902020104c042041c00c2c0149801407030b5801c114604004c440f180074030382c400241440515805201d009414490718020420541003003048411002d00038000c41858030941300140243d1649504d040c002e03c40f2401420301800c03d03082c141d0181c00240410703404282485a1380b0707020351000500d00d4046041012050405080d40d075540300642c000190f405140d034844071601016100a141c030650090388000038900007040c200040c003aa0307074080e540c030025441400b40491a40307020840c601d4880000c50002000c0ca0b11410950042251111083c180280420602a119045484d26040c0c9018101c01107003603542d030b401242d40320010300a81540d50004404070f0ae55000c403c04650700084141851840403440b004280380e424a564014a04100e9442d100da1172142ca4120894001440c1d11600079190f040c2408180319694481c40281504000904480f55a0071442940c3c94414200e400d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 252109667 1250 252108417 252108443
    0x50c0c06030c222709081c0507080c073201020901030b06090307060c0c0305060f0f060301090503181302030901050712050106020615030a050d120c0201090c170a 71
    0xa510180c2c0c000c603070002440d1440094143c0300040f203000000441da50360b01d40506205080081d11603810481e80b118540341d4450700110300084980020701940745444050080086140c42080306442000c1d01200c1030264002c1030140024803c030454440a80200920b041c0100b200384003a00c054010181c100e0345270000a82c0c1c00703982c0041d0000c00c4007020982c0d040c040c00440000700441841090745070742c0d040c0c3c8020010407415014103004240b090040b841c04118580ea134031124200142151030071140c001c40000c00068583c9041d20f0354100130142c000b00991a050f50341d00365217100c0c262283c0c0c01c5040d0b580c5000c00c0780c0d45d400e40b0740070b4111030342809640b0782c10402000b81c043c10043d03a50b0008101d01c2090010100d0952244d60b0494400e9402860561118080903401c8801007190b40d030140623403040031010a40400c07109804000342d96410000000d0038101d03c0450740320007003030004c590424003058040b60701c503120201595044051681a043c08000081c41c01c49400002007407a0b048140b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 252110917 1250 252109667 252109681
    0x1031a0c1e1c0b090105150409090503040f17070303140d11090306070503040b01061d1206040c09020a02060c090301140c0304030816050a080603010b0409050c03070e1006050c0c0603 80
    0x102038010704112181c0411000d40110380d00b81a25192010380b84c21141200042169140810502c00c202e1138031401c0303510b042d8941c1100c0b419910040d40a4900d988005010401c1001d50000500200300901c840708550340d07101c05840d100d20345880042d04001c14140f451702106060741c00c440402c1c402c03c0042141300300060780707030800740c1110407003070b120b400b03004001241c01d4002c1c002c40b440b842d44a01940c00c242c0c00e01d10300380e03003003910400c4c854004604041130103406e450700d17880b00504920040090945203420718111484103501c0d00445041070040c041d004040f600002d089401002100545880d80c0443e000710740185184045810340c840780ca000d00514403060f070000d5000350302070b46c1da54442d0765481e010321180200840c82840096810070416000c2c5101c0d2100542010008002003401d1081d0710001c0c05860b10504e0070384444e00425022011403030200200001041101008a4680b0340382c100c41a8948280c41064103101c0d000a5803c0c43c5981400701c00441000188907079207c3c141a5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 252112167 1250 252110917 252110977
    0xc120b0406150c12020d201e0a05120c07030f0f05060408040603050c0a1e0c08040f0810090201020718022101090e0601081f020910110d0801031a0c 65
    0x2000c1030740d0790680b209113842068808600000c05107403a4448004c1d41203619012242c80031840648aa0390040c40106410340740d254180118000d05d900c001c100c3c0805174103013503042401c52104084103590402c0384081c411b01c00b060032001c4136001490355200700f6403401e10300762072182200d008145000382d00800c02000304e1500644241c0e0003980d030820640e510340165050500c07841c4500004a8000385803003044c920084050380c54000503141c00302018140d55510009034115030050030315216407084c1031000b800100007034804500030200622072014150001303900c4110380d00811403200190300600d8260301c0300e901111040103810b07480804403050540030a141110038054494814200001440e58940005807541682c4604000d080348001805400f680c0c035000307242e604052602030060140942d03592140e98924034041c0c035410000d0010072201400e00f520103030198203208a007801030020030744940e01945030443d649000d044e0754030b84041c042614001c0c1c1040403003000450300103c240521034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 252113417 1250 252112167 252112187
    0x110904020d02130b03010308030406020f070f0620040e0c071b091a042a0c020d0602040302121b010807030209030d0e040e0102090112020f12280c120b040615 69
    0xb44503050f0f80584030030541446100c280300c05040c5503401d20101c3c0125206900826008080d810030918010f0680c2c1d072020314040105094a0310780d03031902d400c8506080c510f0440c40ca01c40a00f003071407816060603510f1403111070140c0402c4000707001007103e400304610503100047d0384240780500003000e0760f200242c001800050481149072080451112590f050034011100c1c01c0c0e0319407042503040c4402c1028035440c2c40e4115444810048000c01a20140e110603000c501c442e400703900c0140e60385046005100e41e403c44600030400d00d40c8900c2c141e03030b0f48511114004078010024644141385440e000c1045001c0d01400541a9260140016000301c1c642c20045043c04603109550034490881d210445600301c0c054000d4190205801d800d1610070085103070300402c0000300310443c00b800d001e00100118011242250541c041d404464000c15800790860f401e90013191910000b4000d81000e41d5008120002416070f2070700b0030741c481c072546189958541011000c1d15200d10101c1001c001034000400da0072034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 252114667 1250 252113417 252113437
    0x10204120501020a020c060315040903120c030b0306100e040b1003020402040b030603060903040f120c09060b030403110102030105010e010c06060b0a020109110406030f03050d020408010f0b090a0519110904020d02 93
    0xd0354003105442d047c40016207124071001381111403040204410302004d400b58503802c07000c0080824a4401403142f0b8800d001d6124584daa0014844005030141860f24030041c1001002d80000ca204010b00040450400e904c19400000c10081fa100c410740010160070319000250701c2070001c2008680ca2681e074024501c605410ac084a80c20340ba403101c9030703890b84614054099840441c1005105551014201a1600d031007031840015050352406550700300c68464100150040001081c00181035000c4040c0040074564402140707554500340020340f00e003c2c41c13801c19040c801c0d540f04240910629074030180041041480c41561802910402802000c2410080310850100300400342c4500b03042c406d41c0c060325484a4040041d4107191410744194201c0080455400d40802000c914500c0a0081c00c0144121000115204004404000d0361400080c0004481441c1800f0040c0007400002240008001e8400001d042c0502414044039881045c00d03041d006130000900b0200309055030300415022070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 252115917 1250 252114667 252114673
    0xc240c0307020a1836050f060f01180c02070501030902310f05040203120c030c07080c1005031006050d090b0f09070e0f07051303050a0605100524070302010204120501020a02 76
    0x1454404c0d280414941d8a454203250700880b641d4588080c004070784100d45c1d0301500488948810046410707250003000c80300081d80c6000000100001540c2039054800010361000500a01441c9600255101c00b54030a8504050710f031b40d0701d501075440e05a10070b18203030108a6005007403a55000750ba004042191014000640781c0340c1403940200f47c0b07210355400b5560040c060000845028030051454005810181950004003c01a01001c00b000204001d0001e40d014103060b1000b00100302c8010140350240707003401020810044000c845030342290542c1c0642c10403545480c1c0040035100204460940206140300d03001c28004200102c6c2882c0b48100603c030200c1e040380740c4507402500c2025054980005904400c40481c0009000b00c010b8544111904003006000756651944c61030100b42c0c03182070b140295184144610940021345400141500f6902c51101311902201c50f032035100001c1940385407240c0410b00c00c08151007901110020846618240c54182040c24058002c1d484035041402500c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 252117167 1250 252115917 252115931
    0x14071505060112090c090908090307081b01080112030c030315090f0606051603111006120501060501030605060d050c0405060a0906030c03050601080f1305011803020c240c0307020a18 80
    0x100e04d008580c011680300c40d11480d41d514202011001d002980c00031500900c0901079000d585e2030403c280c0c00100311f00c4008142e030401c480c08410a400207000d03001e04000c0080010321000c0c0402d580c4150480c0d0502d40000c4007401070804a008001c5220706008401e001c00e400030700712410340c020001d0003008071001c0000c1a514030050380c81e0b02c5545441000e11200450000c007083c0943d0840419081c8070081d83d040704594018401214082e8108000300790b448107501c410310100748104405404203003002c200c170307505002c00108107009208048134100c1d1500000b88030403441c03a043e10011300e806040117446400456020700001c02034094030380003030300e41454448020b110340210303405960103864822490312000e500320380e1040000c00702880d102c185848040050402d1182410307103504103280b0002c07000c0d0703407400900b01200c10382002d129010284294221981e80d0b07045081802c0c4100240d65038013031215100d8250b00420398042c1d405504c07842c0014440c0c0100c0e203142c9a080c040e2104115071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 252118417 1250 252117167 252117197
    0x30706090e1f0e04140a080a200601170109060c080f0f0f0408090301021603051804140a150f1d070315061110020f0712021b01140715050601 62
    0x840d07441c003001144410b4100b0100445100704103074581250182414991000c4901c1c1d946160002c0c00c0d40c12902e51100085c052031941e801244840d4500502d032211203807107030f2400d10a9441d0018041e0242603c2102e80a40c0b000d007003588106105580a0700c10701c000c0780b5841020b000c107075003181d006800c0541140000c11102d44192050700c60715000b21017000075200d945035020759030002d2440c80d41543d800c00071a450b0320480410205214403d9481d50341c3c441c3d030300004403070500000d20581c0c00b450820340301d204051854401c1300e9006402081c0094081d0301c0c154100c80c6d41c2410b0340b02841070a1203d02c01f040d5102200038a8000c42c10445540801d912090011022101a80d611602c9541d8038a4203010103445100c036a4034160420b4116507015020144e074400302e070f002c0c5080c1403e00c2d4000415104000003080001405200c0e030010303010010440b20780c07201880150b0710180c1000308440800c075100040b001900c1025401031011008100340301305510080c5404d861041c081682c01c0d02403540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 252119667 1250 252118417 252118441
    0x307110901080a030c020a0e1003060b0409030801051311040b190e010f0c080903030f0702040f09150207031b0503070506060307050102030a0315080d0f0905010302030c030f06040b030706090e 84
    0x102c1e4410002800c04040940f01254501400b41c012a44101140400103040941200c402d0285110080f54160360340303145000400c442c0407013103981c059801c0c000b406000c139801003042411180142c9102e04c14a08450340c0c04000c0940a03040740f180d0401007808607900705588003800c0c2d98a2076484100700e03404540819101003840d0891035002500e0315883d409940e00c209030300481288284942801e0203da440081e0850b0404812511400c034082107480c19450180507046410412032000c000401c1d440c1c03100b0740000050012020160f80004244040620401c6c8154102100070048840c441d141c0c07404548a510100c1d0545087c4600400709115240c0420040212101600210700d00344900c2d80503005041203000003a1843d00441c800030f5001c5090002844107940c40d560080ca485440001400e0040a90425030400d4070510801180143d118210394004e0301400c8108550740d01e20300090f01916980c060f2680500070a000040d5041d048640d880990304240b803641c406903648266418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 252120917 1250 252119667 252119669
    0x6080a0b0f0103020c1e0c03070918080a051303062901020c101809060812030903160f140f010c0203182404030308100636050d050307110901 62
    0x1d0321035401840c54103550300a90080031510f0b0107a05484109401d00103070301d2041d8064509000c560060300d00c46015141c2800f152005c1c01c0b82c07020400c000100b012040c006840221001840b2400020700444070f5401541500e036003540054000c218203489142038406001400c3d00f20300030411107600c16003003c0b00d010240e1b4254006900030300205034403404200c01609003245840c01d00803004c8800c41c2c0380c140d4840302d0019202500c00820107520784078400e4a80050340c8c80f050800c04082c414420701c1d540200031035800d0140380111010702091403c10700481298141c0040c008120011445a8090f002c1848191074407000004c004004c0710b8031040e80c5070702c2140100e204200040e118540e203850180a401034a4051a424080501107a071100c00030790b10980054010400c103008100c1100c00704992100500b0180c602510074a00d44c0761a1200c441c2c0c5031041e1041e40f40c40385055400c02107420111001064010300340848039030f16040c01903cbe54445402669003130f1406d40d01a04605209402074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 252122167 1250 252120917 252120919
    0x8070906140f030c0f040608120c06090a0c05040507050f030703090209060105040302010801171c09030b0c0f070b090c0315220c0308030c07022110050c0f07051c020706080a0b 77
    0x304c040e40b11002005001c2d2076101c841c40d80960f0b11305010030024020000b2020b0b0540c4460a1641c4241070080140303048001400b0780550352001000500003050b125882d012140700750f50200e4544c40d02c841c16a0f503805a444442281c41d004410060312075071541002c01d04500a88032842c0903190800111040c0c07055010113400b0403411030040003500303642d40c0340200c05046442500c02da009404030307840c61211900582400981181000d10501114900e5150000001c2c1e40303180ca1324500001c1d071a4540114003002d4200a080000100115010700a801385001d00406a44000080c411450f48400c002d903500b088025100848101d1201070a950f40c0140c0c2d00030541402c074601d165a454a182d10060124014950a00114006032194200d881900a4020108840e02e0302c03240305924014901d500030300120b0410b030170b100740f080c202000c40d05004011460542d4980642c01c04919200b0720301c7d038030402c10700440e05a058080c0d022406009491140d5140000741e103a460005042d199440001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 252123417 1250 252122167 252122173
    0x4172b0915153c06140f090d0b010e0105010e0d03110c090a1d03070215070c0f0b1b01110306120708030a03060e070c02030304090b121b180f1f08070906140f03 70
    0x240c65042c01503c06000e13682d407100105843c180d04a0003080c238001c031b9280e08442100740980144040400080010b01502080ca0580d94201c12040001c2803158022400340034440382900c5a8006481448411130515010b02000b5017410100c210100800d440301003403005c45562203810300895030100841d6185070b002403043c02044d07200c4a940509500c40314040fa8174000c030503400035620f0744003200e410040c004060100e4540d10074800c41c1c0c18100c0052902403082e45040e04004064004ca8256a048541651f00088001d000c42605261000c01d401280039441b0100d40d00c01620f034160809001c0c0c4005040c1003c403504c411605603010700f50088000d50580040c04240150b6049600000e07020100030401299002a441c2d21801e011041ca0091480ca0003110300d5081ca04001c403a41c0821568800e103000d80e40340c0380c00a100340c00130182c00d0465000d0f6014807092054800061200600301c034000395160207a694101c10010502d074407a8003203200800000060502d0409140c1c4039110024000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 252124667 1250 252123417 252123437
    0x80a1106100618090f020409050702030918060310020729070519120c020105150a0302030a020d020d0203031201080d05040605030f04172b0915153c06 66
    0x241c07051600f02d216040c1080c100e090004c0c003501d07030b4090020b51a030107450050b560340c10f081090095801c001e2400e07055510030070025019441e4284503201a1401e4042d4494940f90000000d080161b079941c840c146900101d03440c028031160358050780346c0c046041c0098190f0b40300d03401c10800b0081e040369500e01203603050011085d15183c01d480a4880307407652500390311010241303d00000f01d5040c0c0c040c1c3d10050395030b68100704803189441c2c0f03042c001c18412035540000b075255600295035401c168800070302403680300705c41c4021521180c88800a03540c3c001c2c00e60751100214004c40740308440900ca1003e40d03100d40314407a68030394015000c880c150b94a40e900c152555503842c59050740c844000d8021142c10201641c17110003070303004c10007500c001340b8240d00c504c611448440000215000d064006462640350090007030014942913102c81040603502ca01142500f241c2d1510040180c0c4c03540140c0030540c0401c00015048002a0080952a501d0046000d22214596081d820100500440b0089200d07051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 252125917 1250 252124667 252124679
    0x6050a0503040309030206040303030e0706140403080c0709021615020307050706091a19450c060503060306092d0f010c08011503050403020307060522080a110610 71
    0x1903900600a05120b070030030340d880c1e0101d47e496115074802d0300029030b41d1148040d504001d02031180100050718000040700300c0040b03100014880d6200013442ca9030000b403c4240e801d402e0090300002c01c2190002c54450601c1c001c0c2142c01e070f40b50743c81214451104007206410607501e10a8a01030000d40d580c2c141040242e564031801841c0d105016501c42e814922041c842092a40c0b56074450040d60f00c20740c8100307040d200200140d900b02c0b05002004840b26840c1003100c80181c0242c00c3c02007503e41900021800d1141d24000160242000b40010800c03000c040360640e0003400550007038100381c0c05c1b00c0c950394608001c00c1e119494480d4070079407460030000e500490440d4114212200078420255001d204041c80710500319030119900d400421108c0004201c1c00d56011040880c0002a08040c0260302c1c069400070f46030b11074000000c0c50903030f44001241c1d04104480c009241440150381c2c0c94880c84d0207003001c0005030400e45441d00000c0f0316031030202011402150f0b142c090b07a01c1d840541001d500f454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 252127167 1250 252125917 252125927
    0x20928031e170c0c010206010b0f1e120417070f140c03190209010503160501140f0c073209040602090d0b010303020d031a0f0a08120d06090606050a 65
    0x28160072082005004080c0403410214031a280b4400d6000365075580c044520703420341850062407400d0b0664000744010407483c00c0346030444076002d510340c100b5599001114100b6011207000080c1803940350011405030b0515400000b01030043d1f018401d40707121410851052440e078420b401000f010341758075100900c0081c01c02820700086440035000d84040b0040000440d00c2c0c89801065240039014903200b12017541000c0c0b042074058081680684002c00e042801241414070f1441854104846442ca950f070100503542940d8001010302103250342c0b10480348003540d0700c0e0f800e4000d0003c1c0140108a000305444000d03030a000c03c80520355400c0c95581c110040001d40c450090090f14601c3c0c0800180c200c030f03a500ea8441d10b40d41d205280b800c496504609000f03143c4481c2d8aa184181742ca4101e003041d091060016079144500101c1d4a20649c2c8000004200700c2c802c207507c550064854130034005543c0225501810b4282003800041081c4d9584048a2059034010310501c000314004004000840d4490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 252128417 1250 252127167 252127193
    0x7060f050c1c054809010804110d0803010308030a0b062d1e071a07140304050109050f0c190303080601050d1506120e0105011a0a09090f02092803 64
    0xa00300544c00d0b40e005040f4244500f594a1500e011080605001c00c03501d0001d40c0f80080d01038aa0109a0400d4420000600800809000039040040c411000f42c5a580e5403c1d207202010f610502007034981d6924506904642c0060360608145800c2c4501c3e080941031981c2560310051100c0d41d4082d20340080740c22504d0340c111030703004805c02040070042e0401030070040c0c50f00c1d80b82416003031000c1d5031803e041c02c5c844100d80036003c0000c2c0d03111403141400300311a408107a50b03201c00281e01c26542d0707a48413840c105004003043c070300081060190f03803144500200042401c0410120903103407034102140c01d062950900203075000081c0490b961802040c04c13035101c1c001401c7c030200350800c0001d00c3c210040c00e26a1105403948840c0020350800014110070044e800fa82e0b411002c810001d010a5040c44c0c41507642c0440d180d503001c028000070130384e0304500e4822489500245001e1000b000005180b01d881c4010f0360080e980c03103000d4040107a07669401e0100001b403421031500c080102c2d05040c103507521282c4c2c001d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 252129667 1250 252128417 252128431
    0xc0907030b1302040f05090a020903100b0409020d030201050105130203040c1a0717070c080a0c030b0a0213140102010507020616030207151508241909050307060f050c1c05 75
    0x802040c50302802c0355100400180c18049003041c5214a00020400e50890080c040c100c601c1c01408084401d840c001401c1e42111514000410240740349804180204102c1c48040d41c0104090754034030a00d5010762146042c3d9005888401350780486054034400d901c800d5800400308030050000308500031026a803086480e42407800e50b8902021621001c05004880e43c928403101d10001e0b14400300301c0081d502d0001401c8a802030805001715440b9000c0c494005d10000e00000b41d0040000e040209560440f0200e48034800525030300d50701c664130701c49040c0d01a00b5031b83c0550301c0d02c40131075095400026101d1252013845610707000000d030349200328080c6d0000d0b1401c03903034102110407003005d0354498041c0c01301c102c44040807000c0d4145058400e40c50403903403074040000c280d07140990803e0f20b042c080c10560f2095071076060103070070b98441a42500034900070101a007140404900c0d5010803140d500403410200001405100a0321001080e108510801e950b4840c0841456941c07008503110303030084c980c0a0383d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 252130917 1250 252129667 252129679
    0x10f0603090302061503120703081f03020d020d02040204081605040b0402121303140c0c010f0302180103020c0f0609100f0c09090f0f052a0f090d0609120503180c0907030b 75
    0x30300c031f5001d502c64001c018110041a600c000b00001c20000303191890a5500c10b0318588422480c54000c1110318020403000b90140d00d22855640c10f54503550119802001c003482221090300d10b44031121010900780c02054441c90400c100d1002a1519009031155100301c0c20703803040c10391180c0521603030803066410201c003806030420700300b100d052000001d080c07e005c1c441c0242c4508044040014030101c10030140105040c07060000201c0500c11040301060b0300b1007802c0059565043c1c1134000e01c1c041080401450a1055004008120f4004203400303034040ca000f00d091006400240701c45e02506c800d1a502c0c00050300b41401000710399078541011102c0d8203c000001402c4116050303e0042c0c0d00d080390466055075000c6010b8851017829410300d00001415141d0f18200000c146d221001841064030aa00c6001700c20301003024021258022190b43c0d91180d0082c40c0d89242c5030014096400882c1c20741c54038009500304100540f00401d14180708040104058501da0f0b400c5000d40090104000c12030304030ac = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 252132167 1250 252130917 252130933
    0xc1206010516021c1b030809040213030506013803040b13120806010906050f0301052b11100e03100f09050a06021909060c0b0a0f0f05010f0603090302061503 69
    0x41c03205400c1c40e21250300c2901e146103c0c00c26091401610550b4a440c03800317044180d80403c0400d580a0955103440d401300c5000d44d03074012214030450710000d20740024015010700300000460000401d100310700100c011081c002d80028406000403000303802d441c0a04150300400010780024040c04016034002104104110303803008a459031200b2580641c611004a1940e0090210946e0480815801001c1c0d03450040e00d040815040c52659002c18400d16005003c81020403002c0801d00302001e07036a0b84044100d106000c82400d211141c51031407083ea038011020415441c0456106805043c400c0c040035005150410401383c0a00060130707805101e00a280da6803d17802c001840c280700d501350440c012000541c0703d003141104104444444d210284c2800007a29040002a0b08020744100240d0000301414003030381d820102c0ca010384922440200741c24030302031020145407890784c441416a107031603480804440d200c200585c00c55400e400c000c0c0140c0d00c8440020b4801218140c04074414801605907040a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 252133417 1250 252132167 252132169
    0xa0e130e03070c050f060c1908040e0c040501090b04051c0203030f0a1806021f020c0709020d0e1213050603040501060e04140622120c0203030c0d02060c120601051602 73
    0x180c0203980c04841030f1028801c02c0050340742009504060000c2260720707514007802017000036580d001c051120100745460703030050010700c180c120035a001807502e9401c0440340c0c03800c5e000c03140c069800b0b40601808112802d10110707032080d25600347c400b610006090048481c2452069030700c403ea16000407641032104100352181403420384050405091162549104104505201d000c13261032a04120215801480116110744140742c1082c0a82c21400006070f40340c3c90400d2460a224198124490581c0009484a01d001d12035201941e807544030816619880404200c054032481508013002103d9001e0340b06000301e01d0b007100259006446a000000c40b2a07446040040d06881110140c03108100325000658005040c40100d80c00700e40000060035400e4425000421498013820203004a14120003034440301b80142c0d05000c281e41c000f42201d466400e400f0302c0d29940c103401c4034903000500844010545e812070324800d40300d200c40060800f14060b17071402c004440d42e42000144606071b407107540c005005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 252134667 1250 252133417 252133423
    0x100b13170c120313080a120c0c090603080a180803031504020d050117160e0c030403170f19060506070209040f0c0b0901110303040b040201031104090501081c050a0e130e 74
    0x2003205502c007540c1c45294100e40106120210ba1060145401c010b11010000368078040c6205000e41d14101301200841a0503c0880f0320120340004410a1038204040305002c0140003601499801d40e966801e080705600300c50142c03419902c40d8402a6100b03001241030400040e01058101401410040c01c0c01c0c0301d258204155902a4403602c0c66030741c0000d4524ac02d900901560054028107a401c40c221868000007000106004001ca2461000800844c04052207200b0303803034042d0f1031781c201c0c6005400c1101a40310728200070349248074810202c540340c114503401c50203508210360004015a051100a40034020464002002211141d10701c0030b590300000e10b4100302c4005094801c90f416106c0c103604d40050070180381504402010f5006008105c0001d5201002035801079081c6008541c1e842c0f41d50604040c0e006a4114544050605c8001f00f1002c500146056a00604c41428446250190000c1c0d84c0c40c803421200000140743d80c0c003811800d00341800c02120f03800b000b0764001020070b40300b020641 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 252135917 1250 252134667 252134689
    0x7050601091a1008010504150909060f05010609080307060507052203060c1407060b0303040504231609090b220203060102060a0b06070b190203010608100b13170c 71
    0x5155951103282d05a81600c84801d000b101100303949550750480e0581c2d02424404051184030700c690f032034840c110302400000c414036000b000034030418020007c00e490b018000d0126802c0302044d051905000052851041ca012412264682e001d140381114903290304000e8400113121406000042050703c040445840017101071b440810010704e5598158501601038400c2c654000c001c0040030030300c202106c030400007110100c0307a2200f00040d542000001290030750003903a10071640310f07182c000e03c1c03003000540300017440d440706241c02510712590b200090304144850001b41c420010340409400d0000d890f155100151540c40144414802c0841c20f2402c509564040308264110340c000c410b100d42541c041200d207800c4140d0900030300241c454a0701080860152903c0030f02003552980c04207455000c00b40c42460341010701d08066586e517031101ca0260120b242615407104000000b040069289014000c1c6c44140c104403119603540b515001d80141d0750140709540ca20f0500600c800200030b680d40002c0d000f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 252137167 1250 252135917 252135929
    0x2070b0106020601030b25030b01021c0905120105010b030f100f09020a02010510081207080403080c0105091c02030a030c171005040b030a02030a240203010605070605070c0f020108060607050601 85
    0xb03d0360350705528020074098000b5000c0122541d00c074401c5030103800320911148200b80b00d4500001c000c900c2d840100d10340001890940f9501c811f540b05c000c440c2e540150214140d941c260780384071001d00811090b42c00c842c802d1103102c03e0807000381b01140c42c0a0840001340d401c001c81d200038805440d2202440e8050580c5c9034441100d041d40011510200c079020b000302607100c10321803604800f903898410354139218007104110704e100384400a200b0301048849000d070f40103103402044290700c90000703003801c2c2d00801c0b065a800045125100c42000480c0404001a10100569020350306000315081e00340c003d8010707008500c00784408101e060056201c02448540b1800d8103448a0301c406180c101408201d45010120300c0c042d030801c0c5510405601c0000300d501c01598041106030b0903042200400c00c00c4040c004081d2403c83c00040006001a071000280c100c860160320100b110b9143c14034203451409400d40e0042015005058000242d0b00400b8130a50082c0c002c0e003990b2500085a0350241415801d821034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 252138417 1250 252137167 252137173
    0x409020304061a011205070306421b1103100b090606070c150c050a0b06030c0a0e181905150703060b030a1a0604030b04020123040b0d02070b010602 65
    0x611860380980d101800050f400784520140c1c400008280c03400c0049005182615000403813130b440e1081c0c0c449801040c8610304101041c0d0034000e4080030a06003a051a50038031820810081114550314030400340301c198940401030340c20310f400c40302d003101c00c0801902c0d25510060811990b49042c802103503612584030f000198a600c2c82c0c1044020040905114040c4c1424031417040000c5402c01245c0664282d48100d0f50140968202100d0b03800200c0340040c00c1d4000d12120b40c2c20000c018814500a050841c15a4001c50440d0213010715003040380b00b58165091524041003030b00c0c0300170038000c45104444055403000000c42a0070b00110014100c105e070640c1c051040034035103621180d01a90840100c1c503003400007510308a4110742900024054155141e514020320418010b8025140100701c80075098648442c0e80e41004105040200c1d01680407588120000d46180305070200c0710f1000c0110080d00c1d040a0a2250160850b0841c010310380200f90b0070407084002c2500162101d008105603401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 252139667 1250 252138417 252138421
    0x4060209030d09050117061c0506010801050606030c120402131104080606120604170409050a0e010e071a070c0e0a0605130c02120901031e0209030c0306100509180304090203 76
    0x1072501c2e00b120401c0a2041140d440828401680d00652601d8003502d0b00c2e240b140c031501c903040000c80070b15950074003114081d042c0202104005010035414100e07001c1301c000b00490381c0d9240c24040c0c10b11040300d824841d50020040008040602d441446d00b080c005409291410714041055084800c40b681c440740c1d1040104040000c20010428240d01a9084c0c0d6003072811100050029650503001c0d00082c01054000c1e03442d500d0f03011040541d0b0040c1140d2000780321b942000385000004000c201102c0a442d420510394091b80c44002948408860304001c51000841e0410f07541d422a401c007180441d40c0e08001c2200181c844415040c0b079024200340040002c400f8580740401413003038550440e00c10142d08010060034019004500b21441140c1c2298840e0380c0c401502c0102e006000c4503d10000d40303c214040e2b1400c0c080b0030b5000d4080040241c0844070720440940805541e030f030044858040381503203810700b4007071800c040d0451a000021100240c40d01015103000d00c1c21900690420000d0541c0482 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 252140917 1250 252139667 252139669
    0x7080922060602071224020a0503180303070f0e011110020306040b09090a2003010e070e060a0b1804060f09090b010b070b071d030111130801021306110106090504060209 74
    0x10411000300b01c94001044401c0c5010003441c4100100d21003e01a00c280d032400783c91000d450a070b0148119450312003156180803180b400385c41074006482da043e140f15444090780305588000304580c042c001d030f502c2e07010300042401e2044580e42100a6010304103c5090740e1303044890810004840006490040036072a0319014003403004485030114030a100340100400d201403440042020b1403620381140140d0107025848007540020003044604940540ca42248042400000f042080a880c4151000886030b20b50004100740d104a074041c0550449082104007c00002c0d800c03495414100604046078141da00c401003000502c2e19840035403c1d644808100080048190784540501902001d460821202c0d07190b1900e081300081104040c8036440c8207058007225076901540318030200400034480000d50f42050b00054200c0104000045244000840c2012044c000d40d550b40340e01d91140901117140890455401d9021520803800f95a101004212002d81d8002c0510650103070b80e0150750b03105000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 252142167 1250 252140917 252140921
    0x102071a070b0a06050a14030312010902031501050a05180d0b10060912030c080706060302040515030f0f06040b07050d050a02190215070302070602040b0c0606030d1b02010507080922 80
    0x800343c80e84503142c45000d0109982e100314910079210102001d440d070502c7c900100e40713103200f04c5800d000040884400042c0c4040c1540065100300904070607940403096100055590380690007610b0041607040c440190345103803080245013800402040c0c0d48121041e0388a8001d00c440c152945011001105070900455400001140c014084d003004184004006d80740140420000d001c020015840007900380706012042d00141d001c0c6800038010800b5041401503511001911250341d4001e000d002c0b00f407502080003040d1140c0d9540500040c00242c0d0311565820343c600e000402d5030007800418840c803903800c00c0380d21030360344036015420f801650744e024041081942582506c1240855001c103800c0c410340290009026080b44085c10056111021480c00324060700403600908035040c00400c111208aa00007a8540240d0042d0281c445a18111034102d88079111b058880c910405241c00b07190047d44104000d104d0140298551070070a04100009074031a4090782024584d00c0368814141646034480c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 252143417 1250 252142167 252142171
    0x40609090308041709150c012003012309070516051b090604020a200f0a0b07031103070815061b060103061d0a1115030406020705100902090f060102071a070b 69
    0x212091342c10824400300146000c00351003461101240007155010400a094111840720142894105000b91300c004c44d080e501c1c2c1092158604101d4213568a40100303070090708100910f01d014100064541d42c0715016159640201e58079501000c428004801040046c00320300440e64203094600d4800d0305c104100320300c606000e068548100e00c1041500c0d000380c0c00c95030980f07030001007001204040d01c1000e804ca0421013000c44088403401745c0c1c041c1c0d0701001140a03c40e449140c0c02d440400440c0d0740c2e003900c1c48290200300c5196001c00c02c000045042415001e41420300010018541803403c000e00704040305489010f944055031764004401401001468000c080001d40e4840c19180c9004001c2c1c01c00e69a0444844041d006045160702c41c00f480d2103902d8404100c07442c1c410240d80d681010318251000b0b610402017502c1c00d0140e0740300c11080c00601c0c00f4005000340c00410103d441d450b00002520b2654010b480d5074103500c50020005031210a0035030640c2c0701d44042c61540c1d258581c07410410340803200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 252144667 1250 252143417 252143453
    0x613030215030c090904150e060a0c020109021021020c0d12021809061206070c03020106121106131a090a0807080a1407120c06030c030c080c0904060909030804 70
    0x5004101e01c51407824142d0b00c0c00c0200701c445505c240c03a581061903a5003c81c2c040d01050724141010b05100c2000001c00d0740c002d10300001304102c0031a08401c04c0303080300c0c028078000f0340c014114080c10036010301c5601c9c0407040581810300c1d041151000b003100303012640100013110f590f4029188010700c041d0400081c44052151103019442e11000340c21f8007124420000d100c0e84511071410100303282d40c541c00340881a0701e83e010102c078818141008060107055039440120300540c202400441c4030010000200c50b481e40c410025a8005503140c2040700640004021411005001701300141c40300d003006040b101000c0000c0a40d81d90310484c01401111601900404210346c42004c0400154a00040106d48250032458901003141c04050704d60400c0340c19070240304d40c041b002e00b14805120003001000c00300c0c0d800e510704101041c0e2000e03064007500e40d16070750107010544210004180c40c100400800c00050010000544161921500e4003119170380c81c4258002504607041008202c4c20040c507195840b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 252145917 1250 252144667 252144709
    0xf050f0a02031e030a080a270b060a0e010b0f1c0608070f03081c0e1b0406090e030403141504050d030e010e0607051605100b21030d2a031e0b2b0206130302 68
    0x404c1c8014215040c3d4103100c1e10301a42d1000800130fe80c2c232402e02c2540d004603a144000b0790003866900b000400743c101e80c0a07804150041c058001107103c0420301510880341d00c1301d10b860a140f5041d802da19403d00010b840a40d00d03448005d1100c0560082c011503828007000404c4040d0036100c0d1003404203e404030780022840034908403c0c0050b080d0f000082c4c4c6e04603a84943e031041d110990021141c14070710f001d8240c03040040200309010400c94082401030b03007013800796810031030100c00401550a8074a18160761304582c1050000c01c02c0f0314400d41c010980518066998040910a0b640342403414102002212140c0da41e460042c5140c07501c41450b00d070030300800a03001c0a4038020011103440c0c3c8030760401c010a0300d540d0036461041e103004543c05900a54060502e401d401a20003024024001c0007e00c000910924103001e40d141d0620700c0303110380341140a000519034142e603504010714040006240c90307540101c403a42d080107945aa00900e052400786071402503042c80e51051140302480c0041c99000c2ea8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 252147167 1250 252145917 252145919
    0xc1205161b120f060218030a030305010501030b0f0d03081b04060503040219081e120a02010e0c030d09030305180a03051510060c08070f050f0a02031e030a080a270b060a 74
    0x81c00d102c0400f0990798001d00700580da9188030b1125030080b2099030a8607018003c3c801c100c01410380580c04207040b60700a0320300b4080808450200720703043c50344010b0243e00425000c00307a40400e100c1c01b04140c2c814070490345040e9642070052140b0f2960080e901c4200015000000c010442c10131031000d0b0f07840d440300c2511000d01c1d410324a01d42d880d040c02c01d10000e0710040503441c4c0f9180c0d040070800c51403514003110702c0a50b12480380500a0103003c1d072622006c0e0714442d941254540382000074950500c50110f6440ca00c0843c256070b0100c1d00d030f51106041c041c00c07440307050000c1c1d40c03682e501d94110011032040c2c000340300240d0501c0c2c5654400d14001c2401000400c0c0e00c10030400c2c91741182030348810550141c211503692040340341400400718554000380480c80740b0410304035646800a0380301180d40c000c03030071110940301400070030f24480301d0300e408a00581c00a000011031503001d019459003180d401c460200d440c2c1c0c0420088100c0b840740303001c0050654841120f6005110071004c00079000141511003185030703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 252148417 1250 252147167 252147173
    0x2412010f060f08340302041b08060f06030c070201020304030606080d0f0503100504180b0a0204080714060d0b0d050604030f080705031501140403140d080906070c1205161b12 76
    0x24144910700804c400070800200c1c01c03003204000c0d00c0519402041000f400583c1030703d0703045400b082c510820209003000041200703450038203588038510000601d00d51031035980c0f007540d4009802c0034208034194402400040300080700d85c00703500d0150142e0740c003d0000c4019800001c1141a10307000c400700740201002071105100e500d9002406682003944c022842041d04081204066800900613010000350007d015081c130f83e580051007241c00d01c2c000c84000c00d840d46e0041e03520104180c49913a1100342000318681c0c242c82c9802054180d00004c000b620204090b4a81c04c0c03d1403030855085001448200390101e40c90f80010703040e03030003603090310740035040d1f1404001036080c0103094212241030107030107003002001031440001c42d4040c56000c40c083c4110341e508524180e644400f400e00170040b800480c0083c0c0c01202c00200142301700250741c0c605002ea0401c0e00da80d90f16000d01070740e44c01000070401141e001400e45400703c8100300d11030481c02040142d200045820151035401194101143e80e9016002c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 252149667 1250 252148417 252148453
    0x1240806040f0828030b0109060c06180f0501140709080a02010c0507120602070c050118120503070b0c03160906170901060302100f02060705032412010f060f08 70
    0x1001d58003010b114030340406030a10420900070185690b0440d0211a20030740e010030348264035501ea1400d901c1c10300c0b410000310015580c01d441801201e00007000c402e004004a074040c3c1200d01d0b0405a511421f02c07030200c2e903c0d80c008115203400b0903940341c1e444d8048980026140b218141e800707003813490000c01003030402c0344040d01c1d0090548040e041103820400101800320902c40100182044000c1c03d40300c0c3c803586000006074003c10360030769000c801c6510009103075006160030b42500d0000d10f143d145460500e500b0303812403080000305440d00d100912444001404400b005800360b0b00e908440f130348a24049241024010504480d0010020580b0b020000280c100c07554148140f40d0804014155031403010240c01030040d9400a90f109042e034034102c020940280032210504055820742c1e900f9a00c890095500c0d20094901c1040c50b0004000c40c103080410341020308000c88010002c000300341c0c1d03c04810b0300b582e892110030103503aa0b40b00f40c10050341d0040f010b90f8000306107010140580c80030401e0344d028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 252150917 1250 252149667 252149671
    0x3180e0115111c090303030f020910180e1008060a110f070317010b0a110d0903080a12060801060503010b0301090b01090b0a0807030614070201090b040611070b0901240806 75
    0x30500c003800b00d0b0706120076818008140c0001c040038098541c0740c4003480044c1206814030042d07010a1408803c2c821052160080300d40003580500780c000d1004549500f140e40a848580b00c400001680c1c04c0032410302691010503002d90480c1580440c901d01302050030b801c00b0005004a5442803038251100c840d1081403054030103129024010507185c40f41c40c10107807081a40004901c00c0a05c6001c00403407246200f50160500c0718242c1d45845844403050000d56807240e282c1d9401011441075001003000401f00c400600002a8500e810001c4520007010716068580c1c0303401c41011651210030600c040d09007441074480f041030440092000074010b0325500000081070245d614003544444c6071003c5521040c00083c01442c2500454241c070b5502c0c2084e0b8020054640d90080d0f00003858040344d089481405101c1c0d6503500803000e107146444550f1004020f002c03150004c1c0e8000381c14400880424a00082e83d4883c002000003c56802c0da00020302d91107001080d403d041d58900c44106200b08a13002407055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 252152167 1250 252150917 252150959
    0x309110d0b040b0604110408010c03200d0504030e0d03020706030b0103110f071e0c05040510030503031906082a041503120507020d05160b210c040f0303180e01 70
    0x1e0035a88078400030802034241084546d00030700002600240604055010311030920250b034080029001040502c0c0648004d04140541c0000c240311001c440c0402c1c7e409150824072a0170a00d54100440010400030b030502d050540c0960402c1004100b126010b009103c0408002d10b82000070300d14165605e0541d00071030340e21151040000c6801c1c0d080083c40000c088002461243c035812510390b500e88200b203640e00b4042c41d0b00890030040424910600c00c100f48040d207501402039400c56507440c00310000d19041d000c141d4503454030344400285c3c0d40030030b008140c18013660303800c03415403003008683c01d4a031865012b0242d401586060000158601000c1d451003e9907448640008281c014083c02c88690150340b00180d8030501e10410442007140007c1d400c8003d6120b50041d030109540c17881800010302505054020074401501003000c04401c404007030b17510480c01c00031039082a0b2501008032001965800c101c0100b00826102019401c06040202c0148183d2885103041d60401c002d61464610b40385008c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 252153417 1250 252152167 252152183
    0x801110d0911041815060e0a0905070e07030606021b060a0f020111180102060708060f04090201120e03041e0609060c061b0509040e010e07030212070f060309110d0b04 73
    0x2550800007400c1400142410090081c8081e0030001001118481307042e404888046a498848250030203e0245c801201d6030080f04a00c0ea80d1807502d0301d0080d05140204070707198044d01c240441c0c14003403604600e01075400d56500140322030074240040c0c41c0c2420341d82e01e00b0f008126003c036541d1a0303607064215514400c0601d4403189803601d003102680546000d0700300c040181d8011a00085072000c0914000410f0381c260308807481ca450b0440b00340c4592105407251908009601984402402c00e40c014603841403062400001c41c0c09201041c804541210b10070705000d03040085c00300142042c00b520010a03004c0b04c011818000c1c0f408501804a050341e1144030140a0b244501d2018400e81b640000d405214444d06c40da2143d03030340000101140e11025115105a14004005640000500c20b4511480e01c0400510300107042d40c08006011480b5261101d4030b1060420215201401580f10700040c4802d84012035105418034001d2001e1481448184c015622121480003095401d461141c2040d040600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 252154667 1250 252153417 252153431
    0x20d02061c020c010209100f0804060b150313020102121201031502040801021c15050f0f0303090a08010b011e120504030e030a031808030306130b03100912090801110d 73
    0x1c580310301c120065a8a9055101061800e8244070640080500b1300e0b08840c2421200c051035016110300440c44580030004070401c1c0080d0000c0c150703a0040c3d1401e000144040300804000ca202000c4c1da1040304c49003034085207048131504550301004005011218031002504200d0a485020445201480b005d0034429964072504140d0350a40d0496001e4407030000207558800d040d00c01c805e909207403a0f04c1400e040b031600703982d43c241c024050070105c1960001002003100c1202041040b071060000c07a000780e03050004101d01181c07603440101d01c00c0100110000403031440c14240014100b000d1141c400510b510320210036440131544401603c468191034070300090152030b04d040c111105440c10b0343d00c1d5018403a54040c40b0a05070000c0a10301c030158200c00000c62180c9036008a9181c1c00140c820980200c01402c00e0710754a071103038021442440001d8110b40c080300f00031144d4403e0358401901039072070b090840d00034074080b0741c444104405402050001c0c001100110344080062148259409503244e549a03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 252155917 1250 252154667 252154687
    0xb0f0604090f0f030e0a0f030b041e050a03020c19290307050405030601050307030b0c3a1a09071101091208070216080312090f01050a0b120a020d0206 66
    0x1c4120201d98011440b100019641e140401071916628001d40120b54441140c00c41403402404920942d40500324001000b80b4690702c074080540e01800807111104206510594a001c039280041d429016074001c100850090a019060000104241e0301542184041002c010b054202c00e000300c07001c5400501c50f441f440750b07034159118081145100000000801d110741c0355400745c0076000341c4004800352056a40d03035104140e919140781c440240550780c02c0c0002151118408041e03e600c0910300c001001180340702c0c65201e180c042079002c0301c00300d1101c5008128480924814002141002e03c80a4088601040040c440000090400d41000001d142d4401d117624203421400b1040e51201961804001102015012050844403003005219011a074407000f40d400d203a0008540f00301d400b440c64900400d80081d00c00714024402251441480c060b00320401c02485114402c0142850024070300d0183c00030001c0319041000403405690042c080c1c00090b0b0303180b070041d001099040303500c41e6507400110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 252157167 1250 252155917 252155921
    0x3030411090a0e0f0d1701031a1003060e0106031a09060408030a020f03010e15030304151b051b090603010b030c09070905090103210f05030402010f110a08190203070b0f0604 76
    0x340354185603028211320032400d81c0300010514400007940d1076051000405007082c2031640d109100203400c481424a010314207105020141e50000b5488800400c92900ca44a41041c2c03080c1d034031030704000c0c1e5450b0010003d00c074a1040b0800c401d140c45211040508000d1840c660700c0b04083e101a00302003000011a01403403681e0304481030224040c819030340701d40c0d484400d441b070301c2c00031151440760113002401c0d855186030100484080c2e4844504e00725031222512422602c610300c501c1a25910002d00c40208040741040020290380342d002d007251403800300504144007441c00c0c064401402681440b40409032950086026404800181c4040314035680d031010484607a410b0f83e010315080140382002105001c65140764901520628440c1c820410802d4000c40340070191010b0742e0f00040060011500640c410b80201b0000030451070705d088045c001c4148a810b003140c10104817103901d0009000ca80c81501d210500041e4a128000340d1b04052143e260401a420010080030510622a0010780c1c2a5595 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 252158273 1106 252157167 252157181
    0x7120803070305061503012603041d0606070f050a0605160903030e1f09060908010902030a140f03031e060d020f1203162303030411090a 60
    0xc900318010540602107560005d00e074069174800203500740145010700403000c004604424048d144010400c0109440c0c0d041d83c0040c081041004901d088903002c0f80b40030010070203550399450018100b4800c40400510f2600540d90200a100d400114820000e104102c10081512132210b00307603054103540c1c82d050000b4180d88040c00041c1c41013061018015020b84101d10161300480550200c200081c82a40040c0718134108008640d84030700d0403001001042c0081200303c01a8000c29240c882c4da0300007508542d130307180701442e218004200100c40805130900f82c9859090404541901e4030b02e42c601000389803c644007050b0146040112207030401c0d401440c5170300f28a9100140400a001c1103085440c0d400203010104100a500880c5404148036003541403408889a0f000c001c42150080380c05800d50052042000107040e40340c80c80030144040f120002d00c0d81d00c0c0340a51024004c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 251978417 252158273 := by
  have h0 := BRFrame.cov_init 251978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 251978417 ≤ n) (h2 : n < 252158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
