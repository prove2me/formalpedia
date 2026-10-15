-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:40:32.586018+00:00
-- url     : https://prove2.me/submissions/f330f4bc-d1ed-4d18-b857-e8b82e05d381

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 743884892 ≤ n < 744064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 743886142 1250 743884892 743884901
    0x103030e04020f0d0207110612060319150b132307020a0519080715090515010f0e0603010e010c050315040203041109180607032405030c13140712 64
    0x5081d14154034240d600c3c08160640d1140403440403600d94045051010020044043d45001e28020306250b1280c0d2744480d0f0382e81140c015181c41c0e100303103d49070700c1c220050301c212412000a6001104000c40c401c0c0144450041c0072160f50840e80300c1003031008066407001d20301c2480700303417a402440c00c0e0044169040300d021248002c0c0640c01503503c4030000320002080091200d4107005d10300584000e001d030520305040300e405034900c0184441c15130945c2c0c000c1003620f60b12038441c150154007100c50b103180d503d00074905600e0038091f45610a00d05041401100c01e07070f9548640186025000107689101800d565003107504001000f00010380000a00c0490900c00c2158202c05070125005c40c9035003020766400d036118a4074240ca50242501d000080d0070706001e0b00020f15203c0c44c1c00140c46091070502401001080342c2800864802e02c207506845090b10242c48603800c3d100054018004006520100045e8020000740c14102941310031012802c40c003c0c00f0f48500070703116501c0e00001d841d8420322040940e03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 743887392 1250 743886142 743886167
    0x1d010b0a0f0506221505070b0a0b1f0c0507030b011502030f030a090510060620071404090c12030507060c020c0d08090102030c030f040807150206160e09040b010303 72
    0x502804070500c000d6540d0011200d8030340c20f4800f58021501c03809001c49180b403003a402240c4281d01d280c2d030380e000e040d0818002c1104a10800c21a146aa036594100c821540000a295000007a07041b45040501d001c0400f1307a20141942000c90b005110350391144d1400360079800c1183c2007411300c4010403074140c034520410200d0b5454000b860400ea104585010a0f01005254a032815113410021051080c14080428110068107050284070345400c005071118400700c0c07210515154a505891000501241c001c4c140d0700000040d4078005c114400301301c0648403180c0c0546a910000c1070004111040203140801984243c58040e100c1c18642084022148051292800d54000600615450382d4140308003039081c1d4000c0c201a01c55001c4130040f440d40c00f4110350b841e110f100009841c030101507400017901c11540070200301d4091030740320b41c402100b980608140401507403100700807441081010b4000051140d052034204410300c0030350b000881c0c007402520140c1e56045014014000c0c10340c0000c210182 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 743888642 1250 743887392 743887409
    0xb04060605040506030f0a0326072705011215120c080c2e1101240506041511010b06072a0b0a2703080c0d08010612020d1d010b0a 57
    0x500f841000c24540b00c03514446c00904000420026851691841c9e6034040c907856040c0c0c035031003103141c0344002030208040c1100c5482a01c7c1590100e6280c2c1e003000e0200001e581040c0d4440c064042c40303502c19030213807045050200007001403602c08623903c5048203e4061990103581c10781c01092a0040c0340c5d081c0300b08500000d00480807070145100031103290640e00031140d8080c070b0b410340e01e104d0214100e40740300004001d5149035080c844000d00b400c2000400c3c011540320440c40182d507a0f501c4040102e40d00c910b120b03000070003114074199010340f40a03c40441083c1807500003c1041c59850300080c0b045d40c030080040b240b000058610704050710030494266500400c0001241740d1030308001c1c2c5001c1c4e038000e1020000400c540036005900100c0412240e85141001c0c400000485d91646440551900101010462841041e101c0d0120a100b803500c14121111074482c2c115145c584101c1c40c010707500c82500c03442080d80303e401071020b415032520080803d0403140e00011345d804140040000f29680d03039100c100e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 743889892 1250 743888642 743888653
    0x1107050a1208011211010c0c09140105030313061d03070e0f0906040312020a0306080f030306090c030f010302011413030305041701020306090a0e21130504090312180b0406060504050603 81
    0x124142e1344440b000480d4202141c10600c001c800012109509100402444200d100ca00000d0200c502d80125101c0070002d070001d400307a81c882c414160780c1d0040e0090701c46c905071a1142000502e0250354085002c01220081c0d505245211000ca45001080c1e40882c0b64034044078104500d0442e840845900700c103c0b0380c0640340c1070915071402098030201100602c2d2031540010500c0e0051f0080c3e0204004160240c00d03981112400400c10303489030000c40340309008000032710001d800d100b80801100e1007054144141000da07401d6400454401003e082401c518400c1048008440071456140c100150b2080d60780a0340c840c01d00119210700c1241140780081c680c014810702900e41d607041d40190f48404079100c00142040110129407030407025002452100c0781c80d09885100e6106100100180080f00300300c5000513998000340004c40e0364201e4050002501e42224840401098021100c05600606100b214540c980c03940f004248054504890040d520706080001e801d05002e1190b014104601404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 743891142 1250 743889892 743889899
    0x2010c0206090d0605040b0720120a052101080f01060302130917030c031509010303050a1110110c1204050618060f030c033c06041107050a120801 64
    0x20010888000028420940800c4035075007610740704061581e80c2d81000040c805410507040c803a17200001603461100207402d08110300c08540401e03980900a000400c002e09046040458080560300542119410004200302103141040519000c0e11454401a5a05c41d44e5141003400ba00c0e04102d6056030160381d05180c0b003000565115201e40065080d8084003103005082e07807428015816082c40c205400440200510100350524030255108031420900003500501600402400c1c003000d110003400142d040181c07101c4a4031910154928401070fa040704d105114044c5140c0076180c4c200c4881c901c0da0340110f08904e18060400c422891030012500c61842c081c02c01011071058440d03540540c56080107012020025100c4408070b60b960758000300180d80302e00b81300c44548016801501c9003010765045000207484041410000034844445107030035203521743c8640e400c2108a1000704001e03405541d07148899004500c2038010022141300da401340042c4483c0b0306d072030380d00b000c0514281003c0261100051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 743892392 1250 743891142 743891147
    0x206060f030105010825050a0e07030b090c4f1a04260706031b020f0d180506030403020601030c0605070215030a09170a2601030f0f080a021f090201 65
    0x182d64281c50404c000c206107480f05001d100c4080706c5c2c0e200a82046d00c0c041c0c0007912140111203240100302d41d41d404e1286200150400003c0d060650340d08200032000c002c610140c19484249559407800d43c0112840440002068a05003420240e00c0d05682d4480d004a682211100b2060f03001e8090811100550116480881440d014030701803500a14003500c0b404d03082070400c1c9d04120b0b0114010301221301154903628014068124040c08945c0104a90180040705001040c000343d81d41003e401030050000ba0200ac03504203c44402d0131046032001100455540c8a02005600c124020f40082080d03524619100d10030184030343c0711100304841440031b080160388034000c0061040d50303004200c1c1c4a8440c2c0811900400380c1d4080240540c0081c40c001030016522000780c825034402d030b280d150145985800e400c8494504000580340464410010b20014091000444003680a910080b814540c19644c90020740c0c09401241c01691040020100d494002104000a0050034800f8032007a40d07241e001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 743893642 1250 743892392 743892403
    0x50102010f270201110609010207021f080f0c0403050304030501050403090503060705070813080d0e03010b0109060e21030c0105151f1419050d050c040f0303030b0301110a0206060f0301050108 84
    0x8041d4250352450540c2c0940e80314018440240302c400e03040d41c01c0b03414085171050003980b21410403130250090440b80e11184540403130300840900c05032909501a074031103020030070041e002850183c0c805014440031010a4081019201442c4a41e000041500341828040c00e500c2165000c43d1096101c07404000b01c0035407101c2035070340166105650507103038102444078a91b50b090703d800040b2603100d000c2c849000281c0c01440f5454028080c0c00030080e0040d49001100d0a0620740203890202c3c6003034480d502603007040c800412075500701e158007542140348050080e0a40e840300e4035007420350f91260240907082c42100e0401e14403070340403241950100450465040380c480c40410620600100c8243c02d2240394507181150100004503509002c40c40102c88040c4c620b0304140e4100090303629040014010b0ba01d24804c6030156514208103402c020b10710395044001c0c00c410303a0a0394055403104c900c0041c1c846054050410351401d500988150310301401808280740d07816004904c030368101001040a0440400c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 743894892 1250 743893642 743893691
    0x1509220b24061206040612150e3702030102040308030901060803070b0a0e0c0303030709080708030a020c2704060b040c0242011d0901090b01060f2007050102010f 71
    0x300b541c160f51300d00c0020000c0400e580100c06d01d0740c000380ca0204100031500f0b40380311180440ca0400c8054110907800b6a60018601c9210060804410109402c6404242a00d02c0765010320016081c08040d40400d0170f90b04180d208540201c0044203000da8036601380503040c05005220021810308100e03480f41003400401811110f41690f54880d542c50305481440b4121001c1000b4040380d68a060108005160504612403100503000308400403503866000300894a01d01d03429401496500207040c01c2000c3c034101c42e041c02031a01d140e4200b0005100b00c13a1089440307503000700400202c4842050038001601c1219041c2d00854100c0c030900c040c1e09000750845082100d40c4070758085a00981441240052080900324502496000000501480001c0e40e507040507454524024039071240146d1600303031540314038003c1003012140018070406204904841c2c415801389031003455030308481030412103080e03511018a0079400202c010b00295809000b40314036508005c00070005140d40c3d0348100d0300b010b014803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 743896142 1250 743894892 743894917
    0x9151704060e010c11011404080f1309060602010c080606070c0e0c36010906050a12020403081602010905011409060306030109020303030a0e0c06031509220b2406 71
    0x20205040c0030140e84488036100011008101000e010b01028021400c031081d41801c660a0000c684503030740e01da02486003c1c0303901081403820b01002a29401454001048800303c1421030f0704000742a041501517000100429000060100210351009000c000b005002238051001003181c0d00000e40c4c81c052401c110f64140b681d140c04c1c0e48a05417504c040348510010b650b410901d0f07510750501032980400654100e40d040030303509103d141320001034a490341c1034404c09004c01c4c03050000d509030764010000c60000c2c0e481d580005103825200c0d51008200c0c1c1040c18a06003941d021001c240c21960450035410141c6002d0800c801e0b17448940001110303078800c00000c00e010310340220206060340c900f50402c0030140d5009050b80c0d101d00d030445009006241054a0980c02d01c991400c0c0026400c096084a0161b4000c0301d100903006600b00c24454a0800600050300c152181302007401c420b10780314130340010f03207128400340c111904000040d9600305280d040c1840c0452031040c14045aa40c1d00c0c1700300c400410000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 743897392 1250 743896142 743896187
    0x23a03110d0f240f050103060503060705130e09030d060602010e1b040b0603250309080d09050a080a0e01020601080111070b1008150402030115060e151e0304030915 72
    0x1040c02c030050002d40c14407507501c1d60451a11003404815151980035500600541c684041e80d0b24011402d6400520980d6050b40118010071709603403049000700541021030f503101c1c5076243c2e60011348003d900110340d441c0254001145c940e0460340607006103030090006200920012040043c800c0e1074111070f000030050320582031101c1034191034641022017100001000a512844d010f46030301c400c0548881c095500c10a9450041c1266000f40710340e950890300312040c41c2c00c050f48101d402000b000c45000507142407141170090800035074605d0084c04100340310b0351380c41032203042c4c00c001a11705141030f0031500300b076410700c0410014000007034241d9504942000e411480b40c0c80704800d04017400c4007030b0030a800d1406050000c140d107a65030800d032070080e4400c0e07000b04200740c6140034440c10200c0b2805113400140184140810310314005691003894280751010500d05a0529500040300074440386600c88540c001c0204410701d90080c5804c1b0040c140802910001c0205a6006000c1418a642c220a40810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 743898642 1250 743897392 743897411
    0x5150a06021f180c060206070c0308010e061f1d0607080f0f0c0109030c020f090405070e0c1204050c01090b0c21120a06050a0803071e0201023a03110d 66
    0x1a504490a000300084003d180c106550034101410b100ca4000d034809803040d05c2c0490140380c4110b600500c0d07541c2540e6007400990a007640900c079a1005080320794450301812a1810720032003401101501d0080340c1710271002c0600541c1030b040b0581c1c07103800284a048244071150205001c1800c4440405055000a68071481450030310b80074021a00b120310701d580f90603910010541c0151141c1d0b0003c0c000c581e402d0941c003880041188061007203400030280e4000080c10030100b0040131546400410a481d40f504203402c19100d0600001e0486c2d040d107099100007004002940c0140314640030745820303074a00e4604004840140e641d0b0034440e1a410aa50380442005c10307a4050b10103a0b8008811500c092039181005001e9501900b401d0041610030140480001142c031400422200b5242d408040c03510b09601f15a07610fa0704403e014416419401001140c00c844481051100300180c001100c402c405100808043d62641e810000344050503d172950340c896940e8500706480d021000300e80003142040c170 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 743899892 1250 743898642 743898703
    0x5240d06020c240406050f06061e1e030a1b0c11010216080d110c15070c030b0403050a03180f021003060906120203160e01030f0f0203070905150a0602 66
    0x582025048a500300024020243c100c03810485015034001c94080c08240c9503110360305c4440806950391130b400306041000240f04000721001a45024041da08207003040e150248880d00380c0103400b01910001000010468860304c0c0c3e1241000e0311002d88040289409203d20140c000c88641c003011300900700c0c10f84580c000303038400c0000994030040000c08a010b140c1c0e850074035a5541682c09003002081c260040a010b400c2c0c0001d107002c0e00540140b9205003c01e120420140c1a44044000e4840b02c0f090300700400030846410225004500c81d03540c1c69a00e001c0686c0090441cbc01d0b518882492281c20350244020403251181100070343d4040ba0b0212803202e04140a800501280c4d0042c46032908000b0001007070fa1960700004101d5001390213480d80c0fa640c10800d01e4403480a8043d07620f000d00700314018004103108a82c691401442040541480740c81ca8001a00c1c04005a00c11014103444004000380d41c003d20803201510403064032102082070804501075240e495410900c0c100340001000502804c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 743901142 1250 743899892 743899903
    0x18050105010e1c170a20060a0c0e040c2a0506010306020a020102091e0a080f120c1f05192d0906140601080c1314060405060d05240d06020c 61
    0x543c807010101101c03040750044c031040d03080301c5403600100da101a05000800620300400340c065070a0b10142006607109440310009004d19240e060400074034041a0049480c3ca1080c003064456507126405641d010304d46116502d001852003c2250300a001c09070b0000382c00045450640fa07200501588540c1020790481c020302450070700d07641c00718040201e08440d1020b001c81110035502558811030003610b590f40c0e07550b01c41500712890483c0d07020003040c10b44c40340000b01030002d00740098103844100214134001c0c1100c03402c0d2500e02d410140e403602404181080d0924084402d20260802d01401202da20351007031030010482541c003a440095000d0b02c0704076499010b000741e1580000c0412034000c0d50800541500400c8800b60302045c90040814071801c80f002c160350b14101c910350303c452804d040c41110100480d405582a4110720140300110712540c2c3c44016040c000304841740000c0900d001d008945400591001c0c82000d041600010310040d1034400c00c887ca201d4000d1005651414021508c1d0300c0e08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 743902392 1250 743901142 743901199
    0x40605071106120103150c08040611090a090e07060e0906010c0c0b0d090212070f030f0317010b0c010b0420070507030b130c0609061e0212030c0418050105010e 70
    0x3500042c00d200403c04014089040c2c030b0041c0c200d0100c19550308040d000304e5854481c20408070704c40d01d00240000e0300540040742d01061880d01241842d442401181d103040f10b42c0c210303400c0c00d600c4010110803140c0030800140207140c50f00c0d24912610603c804111800e402600080c100401c04e07030b030307401030081d9240d00c00d001308902202c140e03a500240d03a984c0001c01c0c2ca43e40891207a62510711000c4403140014629081c4c501c080c540c02c803018655030f84d9481050b0704201c01c07824410351a5281c003030351002007507060003425019100d607680c00d040603899003124800101d1900c9285890380c2911040c4c1c0f40204009030304074503051b15590300e40c0341c1445890034030f00c0d03030004000441080030054080400400c90103224030500100410640741c01094034814a18025100001c031015140d10106800280c2605400d07211f0050b614031004d0900321847c564000c55061804040014042094142d0101c0b10b4444d2142108200032a50402d40000d24091001003003900c1051200c1c0e0a400400c4000c4907614403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 743903642 1250 743902392 743902399
    0x806060d0c1503110c07081e1e0a050303070918050c0a1d0301090809130204030305030a110c0f07080f060603060105190f0f1802071203020c070f030c080d0c080406050711 75
    0x1e170603030160741c0c030703075688040c00307590020700841c1d00031400d41d160130704001180e00c030100141900c10340c60417079084a400240411a030030304c208029038010803c02c3c0010f5004410650b83d501c01e4609200d0002042c42c0d00c00040500d0314584401c0142e950f11070800c2c1d40b01100b851410032000c03184101e00308022800c500c03c01d640741d46003480300c0d400c0190840090207181419500c003404140c011401c001203010b10320025021038800c000003a180b61280e070280d840f241159020347d0500310780c010442e20305140342c44c800c03072540e005072401e20403000d040140b04c0d107031102200148124501440070a0703e45006118507030240800d010003440d00c41c06003c0d00005000b9460001f000580d48986150000e541842400f81c0001c0c034005140b0481d055008035002250002c24258140d006500110003c0d03201526144c1c0a020700d00c004207909408400d520029405030030040a0603050814190a00205d41585404c0c03200c5030f040d680001e0f01a009403011101d490a040d61244050304040108400d02906e1551 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 743904892 1250 743903642 743903647
    0x50c0d0f1b02030c0c040213030b070c05010b0a0807030b0c070503030a0c0f030e030304171303060f0608012d0b120f0f0d0507020f04020c0102070b010806060d0c150311 74
    0x30030341540400c4480540e8121080300800c040000d0fa00c0744070381d5501c095a5040a10f22401c3c41c03c20390020035540f4904881516416903a407501c0705481d100b03a44440018400402d81c9003800424000c0c48420b40d8210781c00e4013a1450850020342c0d079440c0348801801007241800080f002c212500644054075080400c3d00d40e42d2404032032160041180f060428041241000c041c90500e200380b00b24000312001c04011032950301c90ba02c030a8400d210034a1600d000100030003080040401140310b40008506c070311030100f00c0240c1c00388020281c0b011034110030740682c03600f05907650680d84405540a41c09082d0982c54420110080700d02c09882c0a543e190782100842c081d110034404000b41c140e18910f81c000907100030345032078854036440f0b0340c0200b4590002602400b440c0053714140139407000d0501e0007400189010086e00300c0609a801020064840d5401c00004021080080c0216680100201d82440e90145a6a54441000c2603402094403030400b40c50f002d4802400b0b64445070640344100c82c41c07034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 743906142 1250 743904892 743904911
    0x1f080604110702240a1e081506030a0e011a1302090a061103040504090b18120f090f09010b1909050105120411130c020d090803040909050304030615060e0f0306040303050c0d 76
    0x800301c400007031440001c14141802e11704100d01c0740c9a4980100d07023000d01c4100c01c8040d0001c03c5881c1d0006411800142d40e5071917500f91070a4248601340350410740c00d64a20740d1008a80c1040a0006810748103480c40b40100003a40c115603c507000001038821a050003400c0b9102c03107900b1403840c004c2c0e4014a407c1841c00f21540c0030311120f2580076104041000c1c0c202280c078001c10f01e040d140c030001004501181d07010710192641003484000f8004041c3d0103403003440c0801410001820002d42a408000c20460004809440e1404030601600e20001400c106200707500c0c3c100001c01c140b00c0c0c1d04c1100c10815182c408281009800301c1182da055500820082c014105410701400420b407440c2c40740054807801c142050094080c0c442c0d81d04503800c3c8000786040910303000b145005040d03000e03011a80f40c0410040840020311038030404043c0075200c01008212801c2c40c501030440000b20400d14410050403041195580d0000f0b21190702c00d40c035242c0800c45440320340d40e81101d0f0140e5040b00c80440c0c100218507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 743907392 1250 743906142 743906147
    0xa051305012903160b0d0f1b031104080d0c1a090606010207120218090304150905090f01241e080627070318021f080604110702240a 58
    0x21001c10080d9a900b500d04900c080405036519804074080d5186403241c02c08002e03c408000c0940b881401c0c95902081d181101d1401e08111610410440301d4141c11007985080190301d84241c20403940645141e51500c0d0400f1081c1e41d5440f00405140100b0041071418010004445501201e0001c10142510035050075070005440d0401141d0060051048090001344042c40d0308020007200e8003e000100c01011001580480010061100305248002c0100140c0c010290501c1c00070203e0784c0e610a4030711424070040052101c8094000d1140e420840018460740718250800759003500e15800c185030075580c842098a860b0503c070180d50320800311811100d0181c0e00498034603c103c50403180690984a8040d540102d0500c20004000038111000000c0c0a0741c0203034030400301c40e02c842d03145044881d4194002a80d4252219542e0000c8013030301070f2014596003180e066074000a0032601840000755038a91046140680f070400fa215a480000b00034040e58035050301d44502ca49034083d80d03030340d60005001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743908642 1250 743907392 743907431
    0xa0603081c0f11070206071103160e010905010e070c061b030f0b030604030c0b07020a0f0303141005060a030f020f16051e03192006150105120a05130501 67
    0x611045052602103010b0001601c2544001a00300744214180052602031040d95088500d080380d203030204541960040d50100f0040d41000f80848038210203600305a0350015445060b030283c0f01031410140103001d4124900c5404c1c1d445a4285040c000780030442c24a00060602080c061410018000c03040308002d03810341001e25031440012044c01801d004c801816a1762400311000b42c0043d00782900540018580380480740c104040c0e00c115100c0402c591a14031054803405000c801182d40c406002007601e0080050541c403030a040c0d0b2001d03070540f407c4003240c06413040030380c01c1c8100755683d0201c890075082e6034161042021001c401e00e45640c00005145104410350304103440300d1051070704910250f100c06130014407080808010314100022114510b0f5103501600d03000061062a8598003035203500203103c2d485200e82480100303801e042c0f00e09210305210a0708001070401000b040007640035502c4654054100c49609400519580c48609400204103010b500400302d50a094807111200482c50341c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 743909892 1250 743908642 743908687
    0x5040507210c090e120913020c1203131203091208090312011205071e0b090d050105251103070813230a05010806091603023702030307050d02030a060308 67
    0x11911400245d00a0952a01a102c84540d00248800f2500248081500078090071038400c401c0b205000c181c0444003015420840e454040640410030b200f0030310202c400310b03003410911414204030202c010b4aa6400741c0101080240900103180017040306c8200400403142082c4400124040e556140c952220080f0046071040d80c4074421408046407044240c07421604101e0700060824410b8908190351040790445000242d009401010840126000f8014903100e0003010b200080c1001035070110405400e410160741c010851188607590300018008119410903030850300d580c0d101c0401e080084021159508124941900d203461070030141c6082c0107031040002c089403003803007094450004482c1d0f608225281070b413080d00c0368007142d1a112204d1ba811002c82c4680b8004d8588500301c1060705004849a0b8000d6955010b94069159009800094540740345244007844c954180040001c019014180d0b1850441c1d90000104a440c2aa680440002c0d6030020150791a442c04054003500914000c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 743911142 1250 743909892 743909921
    0x60a17060a0f0c05030424050705030f09010b0f24040609060215130b060f0603010b04030b0f06060717130b04050f0301090b070309150e0601170105040507210c09 71
    0x102c2c6124910214001c00e00c001045660301425a03440c0e8981d0080010024104620303d0004445806801118000c0d43c0c8145081c1d02c0e510390700d01701825170020400b0004c04101c03243c1d24000e003510980d5603040001c884040300b2644c5086d40903907170304100345e00c000100b580c802401e03000a00059103608603d0031000c4035090b03000c6e2008a140c6180000444004490034040d40072040d880c00d0010b03071140480c2c0d0f0030200c043c04803032100014001048055001707070020700350803001041c10000c000b1000c440590040121030313503000c2e509010f808100c403401884401004820000212550780340840181c450803e0480380c0c6500542d034401ea2082541d101d8000c0381e01032610481d040c0f560341014084c6002d017071b60010b0f000406683d03025040f401040c02180803540d120710300004040c11308403400740288180340703103018000c02e5240000020010300c0380400d280c21039042c1010000414004514041261000d51030182c0445120100040d10700302c80c08010b06080b452440803603044d40b5603224010707014554 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 743912392 1250 743911142 743911151
    0xb120105040218161215080c030f190209040312090b0103020a0501022e06082a0d080304030c020d0b0403031a0d0507290316090902040815060a17060a 66
    0x12031004884200715000911680240003130000702d48a0221401207422000000900c44002081c9005000c690b44c00b017061075018882040e06407809022415110310311500811005090b60701c0e1880b884d40310100030303214503c01c90018003070502401c90805050784100741084429200d2412a030154420300007a0700800041601180550000805c41d02a0742e00700040e55103ea006506a0140c4207040c0200c0d1806407288400240507a0801c0204140b21030700080c04260100c460700c81001010a01034070b88144602c2030718101041c2c12400326600682c041c030302200a5005070000c141c02c841e618100500c0402108104001c1c1a4107601030200c2c0006904411901401d01c0304000410304049401b0b01280c015a108120425081d007440f10b0f04102145c00040c0c40c3d40c80080038848d0b03002154001c441d0f009070b4a000006580c030000d0388015040c1c41e00d0460405040804d010343d1403042c108629640d113100c0010549695540c14507a0040c031348910741e403403500e0015940603100c10041d1030440a05050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 743913642 1250 743912392 743912419
    0xc091a0a030201051821010905100605011202090406030b010e090f0d02072309010b0c06060a0b0403061e0c020c010305090105011a0d06150519020a05060c09040b1201050402 76
    0xd8201208a9070141c3d0780340c1c1400000b101c01c1100040101025600110294612403034030030390048602c03452412000040c0070b0302d182c24503a082c5100c110402c140b046c6054410f2080f683c0104801040c1c01108200503101c15041c0b010500070145a0006001540c0c10300c0002040008000c40320b104003000000e440c03841811130419a6550648158480560000c1b8014044503a4400f00b00da1502c100003200558000285e01085004800b80c010072412840021006590441080101d030040025138100c7c1c00c561034050649124060703404000c0c8000e4440100250000041800ca07801c00d40204c0d08001010001300040c5d955041c03509158042800c100008042e50818410281200c00c52a000000420000a21407543d4448110700c82c65558440c40452a50010182844210f1440d1200382d03030b45428100f03c0c165401c100e024001154000c00c1000005a0b0114009400c07070980d204154440b4072a10008024107007544c0441d40000c02c80140c0c00707030f21905400c014052402620302c404100e08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 743914892 1250 743913642 743913649
    0x5160f0e060d0c021905010605010f05090108040803070509030114160912080306060c1005220c05041d010509010204030b011d0c0f0d090b010e010f0f0b0c0a0c091a 72
    0x14a08aa941c000418050204044499000701000b1035039841601c130700d8940440104a05011404203840e41d039035691043c03080e941c000014000214042c14118240980b03480000c00c2d501c00103200400420b0080b003c100094020380a0740c2008000034001d1007201702c8110100e030085021074008035018860002000140c1c0a1117208065810340500c0b03641a800c50f417186c904560000d07000c00e03046441000790840481041c8115119404540c1011800d414003904d00c003450000d0504c003c030b259240c40b0300c2e00700203500c0101e10303000c60303005850100d10301c10700841d81280102e541440801d00d500340310810140c03141c1903000304180da20030800402241d80300c80052650481d800b0b03402003100d01c51b1020554621060001d40340341042c69401d00d2038480e860643e0800e0b2580100215030490801d00140004171003c9034031405028200c0e1124804d901c0c00c22407492040c1d0501c20106081800510054a5034003841120801a0000d20b119000307039941c3d020301c000b4040d518148060000010310849a840c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 743916142 1250 743914892 743914907
    0x1704030f0207210809010507080d061a0a0e091504021819060203030c07080403061b110c030d0e12010e0a050c06041401110f0f010b010e0901080a030c05010204080105160f 75
    0x5010440300f5141c000076943d2402c0340e40080c00241c103216041c07280100040141e0014212002c0e4410042000f0f45401d04800c0c01c010845800c1215000c1408595485944142440310741102110705001036290b204410b042c18401a04040e0000e00010b0800b960514001503400c0050041d60858600103101c150040718038035a011300c80050b0000c10204800c40b44010183ca203040c0a40751440c41c0c2a9607980302c0b0b080304c00f0b01c181180940c01c1d0082c00b411003504600ca00d60b4201c55000034041d0211314000180d2240201c0025409102203664106102d440300902c1440b030440b407400802c08060b03e049003580d1000ea59808840903c20b9804103919428800182c80c12034611400d00c051520f201001034800050b4070354445464880c4545540000c00104403251600b80104000a81e88240c0c8000400c900c43e001c200c4d50007500d0039001002949000904800308035010700d8403460403010f038600325019120310788c003410140d0308040c2800000c500003003500d5040101c640b11400d092600210031344082 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 743917392 1250 743916142 743916179
    0x41511090a080307170c030c0a0629090a090602190306080d030c0f030c030f060308090a09090c0306240b09090114030706030b03010603080d050a0e06011a07031704030f0207 76
    0x417103510180c050340341c0310076001d0400b03100b940c000d40c1d0510030350000c81441c15030003d4043e0392441c0c4905c6585d8400c8902c180b101084000c1004d42030b0001c840f480440c00307042c00501141d031201c3d45c92058200344419907041c0d407924003841c0000c0e98a0042544000d0260a01d4003424001e07000e0291078120541c0684070301320604446444a0880c00d81465040c1d00400c40107040e10185a22012440341a260610951020b5441745004544950030482400240143c035040549441c4c070700303902c0b000810300840d40c00c0d0449030703c00d1011918290f04552500224805008007000444035a070100f40959400c0180074008020341d140ea010f17a80c2c40854082c00010504e01d0b5406400c42d40741031048a100307410000b42050090000724040b5a00c0d0390f00001e60344044484541155900706100c0c0000480c09010400f95060000302107a50508804510303100c0d404154035600003001078030b00704140c040c6c0f481c1214601d0552941c103551900b410007070301084800303c0800c018018200081011110381c070410265 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 743918642 1250 743917392 743917403
    0x708060f01150504030624050f1c03090e010602010b010311071e0302010e1614010e0a0902092407050601270504060b0603040507080106141503041511090a080307 71
    0x550746016282c92407111012640030400104010100200d10f4074010180200d10041040c8a0414408104500b640581c0c020610511525201c115503585035201003000e0140e201c800c82c00b81440b450142c1d040402640404825034020300001002c0b5019402001b08490a8805010b01034010402a1591207600801001501030602d24403820030783c81085408944240000140b6002d5070300a50b01c0c0242c040054819000c1f890014040714003581d90082c1a500c080c2030002c44600c41c0c40c002510b45140380148400c0c207a01140da01c501c0d81d52103840400030207482c10300300320000d8904085041540300c0503050700d4910a03240002100001200f04a070300c84152070010b04040e5804451801501020b0001d440554481604140c642c2c3e501005502543c031900040040c1d92800d0152030075200c20398005204040034040c18442500e618015200c22150540407586c2d980d142e190460440170f16881151a03d440c1074001540380320160024403403038608480f440e100325076548080d80d4901c11500000c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 743919892 1250 743918642 743918671
    0x12091a0a0c03020403210c0c12050c03070b030115180b07110a05011b080c01110702010906020f030307051b010504150b150f0901091703031602161509170609070806 72
    0x42c0051078016844d981b84685014004095030781c880c41c10601d030940280010600d0003200b08100b140402050060800680140611618012030401580030501c03600c9540c0d082607100c1034416100750b6903541c2c40c0f2906051803070b000f9281c2d410078000b50402102203905005035040c560041ca88159400100c800503541c1c540e60070550b6a43c4840c80040e040e044a00038030510980c3c1d28001c08cc0140702000742c0a10341ca984440141c000180040031035031081007903401482c000390110102104490340140581000707540d4101503051890176121240e1266003d5103840103000800c540886401104005844180001e0000a00b0820509107103040441d010008000001e9825140340161141c890141041502c4c2a540d0101454408140c4001000d9410000800c116503040c80c8407109450054401032121035821000340e6503035105401070740c070164007074030101054910588031340d006892094500c9401d60104443c0541d0384400f86c54801c92806141c20214084000162080c030910b072188034200c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 743921142 1250 743919892 743919923
    0x31501031e061d0c06070b040b06060d1406040c17061e15030a05131101080a020c030f07120807120f1d0c090f090a0312091a0a0c03020403 61
    0x202803240403070100100307045115400c0c001c600240726607104080b040f8410703010b801e0200d501038200002240c4a901c81e45c4140300030030100300e241e94510740c010b1784a070b007100607070b00c68000003080340c0581040c2d0340c0294108240c0c08401810b1002160149030207480500c522105040c094803040700c0034081c5031044041d60300051a51604c03504201c440301c10400701281a4012801044040d50848452a00c0240c0042841102c560030f1142680c440c107220712030080c050f0250f0f11241c42d0398804041d203040280d5000829000c41107070341140d90b5500d81c4002c5a5451403207106004d0103802020058802c000303a00102d91907240501244c2c0c1c0314010703903580c0000c4102d0310701044006000c2c03a92180c0311903948003810382003603010300420411401c04030000c0000094040800242e414010007000d4500030708800e2084070701001900040c1a0343c1400d00b0f40b041014042c80400034010355101034070b00490b000c018064000d0b0205182d010b040d01c884140000122300f20b06a090388200c0c84020100d840032042003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 743922392 1250 743921142 743921153
    0xc060a1e0f0c11030f0d1104030803041217040f0f06060503010c0e03010e1903050a11070f030204050a0903080c0c0f073c090f02120108010e01060e190504020102031b0706080603150103 81
    0x80c60261401f0346400e060030340b66100c071596500f0441d41101d40007100700304442116080708802c1c10078490705980d15640e150a60307481d10010b8884c03038028005200406a9020007244d42c1043c1c0c040c10004e4020413900700a1034008100144116510703020f03500e000c0591007100d60210341494045241c2c2c0c403420442941e0f5404039081e51003000c19104116040d111581224414411b05009110309000b18020900f1030041004881014194141440c9452503c0000030b4101a500d0352099103003010716101c3c500c0c000028140001c0300c1c11380c005401548000701d0360401c000c2400f0106000d400c4841c034005401c21000e035011080700801401403410060401044000d0b410002003400101000340c00c05140355108030309a2400c0c1c02412940e51035089507010f0581c00d11801c4010100c03800c40d00000d0401ca201c840344416042c18030741340d03162540300060559000304100c03a1080c6120380c5070201c00c030707042d02c00540350f00007030069000041e0543e021440501d000203c3d29600d081c034904042041c0d1956171a17 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 743923642 1250 743922392 743922401
    0x10503040302030d15090e0609070e0a0906050c0706060501080c0301051915090303021b0a0e07090b0f13060e031c14041d0105060c060a1e0f0c11030f0d 67
    0x12800c40c80104460804944540030702c8180300d21941d000341c000c40c2441c0041047c0c2d8414066581664455000c000900c100010344908803548004911880e03180c4001d42c101920700000040c0059051000f0b010300400d04000601403140583c0c01005516221401147e26100568114441c0c4070107000501481c6001544010015002e400d00d1000581e6907210310003980051007000086801c0f00700030810b141d010300102000307040c0c07241d864084110120000c0c0c0200c0c030710b0040091130400c2100141c4054091995280034001452445450300e2440e0170a10982d0702201100c613442d81c0c0a440060303264025041c084100b900100504410340076052510701058910350ac12003000502c004030480a074111000300003500c80380720b850007a032502814620031030f68113a0006014880c2001400e03e80340c4007088503034014690010100311490b038a070900b0700c0e0b0840380a090440c02c0ca0001c104603400440e80c03045100107440c3e1900d00c3c0346030294021075200c0c00f131401c0f140b0b8003480400207080701d9040341d400b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 743924892 1250 743923642 743923651
    0x90608060d06090302030306011e050a030e0a3503040807020907020c09010f060e030f03160f08030c0d05061005030105100207080303010305032503020c061602192111010503 76
    0x159070305140302500d5680c01d560440d90241c1c0075800c000280b248950b440303020101176141c0c9420035101c011310300d070b001040e40c4a2070100c80100351b516000100050010b101209d60075800120f14600300e00c50562502ca95800b040d880300301151807228940000a034101603e1040da000418282403c17215001d2100743c9200910410440c000d941c0c07074440503503c00316458060b00200122a0740d0a0a014010340300f6124a90354500c254403a840400c030000f400003c4a400002504110508400c00e181c2001c1e861030342c540040c140500802008048403017040600491a0507005c03e000d03036168042841a142c42800c482000503034100010701c1541440c00c816281e038000fa1044540b01d5585d140501d0440d00300b83c000300d175240c00004580300150b44101210f024419804512180407000c0d82c6e010b9610046040307c0b5014140220310350100d03204a07102000000e401030843c00c0c1c0031008111142e05542240202400c070003d00d001c0300424000c02620529240d0300105d4404140980e40041d07c40d81c000a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 743926142 1250 743924892 743924899
    0x60203031302041b02030c10050c0d0c050d020f12072f030c03030916050109060206070e1c061509021821100c020601090504031205100f08031305090709060806 70
    0x2044c4130008107240102c07480c1059a40c5c041c6881c0d4503c240c0250a10402c401e40c8000345c4d043c407040c4000380ca90141207440384031041d44c0000c0c00c01203100050340c5900804080300c80d0300d031021071a46a2609820b0062044c0901c440d000d0300d450742c03203034400d8412850a101c3c0101c81814647c50717a10b02151104001d000340b603660112402c004c503040b41c1d00d1039075004413200c14031034002d4505904108120504c4d480542004d091a140140c02c08600079039600d4000c1c002000c01c803982005d40742d0fa4592141565400d00b001c80010010800b605000010b0078100d4000d055582400500003203807040c0d8400e03215600c1d411140c07129499040c204018084160a0760041070104521054114103410054407419964074100414210013080c00a030400105a00844040781803c0030000081c0d40401250600c01e401c0700002015212604da54905103881c0e000104040c88455000c41c180c2c1c0004090400055010388450b851070b101c1c03080c0710494009072410404102c4280f0300b4410301340145c41c042c0d0310032000f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 743927392 1250 743926142 743926151
    0x20610080607030b0111250e190504030309020607060e071e0302060d060b04031b0618270c02101506020c0114090406030b150922050a170405180106020303130204 71
    0x1e141035040c1209002c43c21035504550060b0285107d51504050040c401440e596000d85440c005a03800b2445151071441042da64500140426000c1c1d0b0000102580203090b0b43c0e1504e9051600d000140110b5440d2a0b0354850481d002a809450004050020307100711040c80c0c4c0c0717070324590038807020360026043c407481c080c0c81d00c42c04039058038488054001180600340055800c55121170307c5d031010010360065810080c001000200c541a0101c0c1c2d43d003101c100d106e021184011002c8a02c1c090307103403070910005040c00e2140d11008160300017110320100070500d80801c40c1205441d1022403c4455108030005a0441c1c030340040d20750b0145503e2212002064002c6240030380c0b8100241c1241c0003900100c03040170740743c02848952004031940986d140801d031000c03c1c2a007820500c16500e00e012040b80545001e6400e11a02005030500400e40c4007a8080740000d040030044401400a40140c001e0702c1c05111911601c06d2003034582400b0703c0c1201c000c2d4000e18550b0b12110034464203425420000c1c2c0e005500c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 743928642 1250 743927392 743927417
    0x100c0804170c0109082a010507120908010b0d021f18030602120717220c08060105090c210c071a07030e0304030201090509070c0c0e07020610080607030b01 68
    0x40041d461021a941d0701030722203810280000742031404181c209020550003aa8044880b2228020181d601d1110001a00860b58000012a4244140400100202c1e103695035401d0580e00400c2603401c3e1003c040003440f10107101b030140141c52104410203503200d4440e2140701301d0705200d040160300e02c0000e80307403001c5a44444208000922410350045510310750025104c0b6180d440c600a072504003846207070803c0100c410f101c0182e10303684080c00d80014880400c0c6590452641712443e80005684080304440156640130403545500e17007442410b020711001030024801203034510844400d0408290310350458a1140c040c5004007600419104040004010420200308009035a44103007500300c2a06415243c4030800400752030001d0701c402c2041d4001c2c4010310041c2c0c3c111010005440f4251070588442e40d0f602e41c11240c801e1a8003011380514400880440c40c40c0d00c00900c5071040030940c0845090f9100c42d20500d045070894828a00340b5080300300440e0380d1034400d4001d28040d0805240025004c0038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 743929892 1250 743928642 743928659
    0x160b07032003040606060c080d111e1902010b03070e0402030304120b0603010c02030f180f0a080a0302060702031e0c01060f060e01030f0c0504031e12080601120902100c0804 76
    0xc007011048412030002c0100800c00204e4040c03d800b070090f5182c0101e91201540c7c0310781940c0151102c0d8012107403120044007080c0c500c0400d0b10307008107040c10407681022007000c0f9010365500400814a2403c2d281d07006400765401400340a4800d840038000b044503a00d0a8085803501030050000c0368180030801c00028041d003e00d1107101d40a000e0011010b0354284403042600b10b444030121075040d900140601c0b0001310390542510b40c1e101c90124484a6418406d00040010b15103080c0e0701c0e0f000d00302440c08140d80100190700c0518910a07000c849103030f1101001a40e0303900443c40c140c94030303808000002c00b05440d40c0000c1c201e0420803100200340c0c6d41d100d4000200c152116080b04d0002500c055820740700e50303858010740ca100a0080410003021405c058014498410b40c040900340e03002d10803038200c921004000f40c401c1c0540105400340020090301009140b40b01c2034072280d000524200740090304a044d48a414145c40c1c0c020080d904134104a0029100f522449a051355001c1c000e0000041441 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 743931142 1250 743929892 743929931
    0xc15060e0705180108060603070e01050d021b07090203010803041202040b120f0709090b060f0d0611030a0b03033901060b36040906020409021204060c0302160b0703 72
    0x91151282d50710766400d16403030b046400058401604104000043c49540d40f5403100301d07500700e0f1081c50062141080880140c609111b161916001288002100600581001c0c540c104000d01380040d81c0405a85084501c00c0c1d010a01803107a032038000b0001040307400a8051880d140743d2001e400441c4003501880018000018000c0d11807281e00005802408140140401d501900c01c09004020104075074440b416400c070000c00844c043e9003545100f545035618107090420140e4006001d01c00078020341c140d2800c0d0b8000340c5a0b429100e06103080100540740c04001d9415203039184c042ca60064882034050310b904002100c960800c03026000d0600c4001c4801e01400c4064030056003035a0f6a00804660003d15000408056104006503030500e6500005180c5d01c1102c5902140c01160850b001d0911400074070484e840a60b403a48001a80c842c201078281d9007600c51801810300304400d074072003441a8286d105454294032044114101700001035410810707580c00009900e00003580281400c10a1030b0754 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 743932392 1250 743931142 743931151
    0x81216110612060a06020a0807200a0609210b15130f020309060a0b15030615041205100e031b0c04050112050c03160b180402040909060605060a0c15060e 67
    0x402d040304008650900c4254031000346402e100812810506841d940c05038010500c0027044107840a80507a00c07540c000e001e0070000c0c0c000803d00c1f00104d40d2000050419030a0341f02d80200c0051083d1441c0340d0000c09000c3c242599003028107010395176070b5032032400302e244140c1800940c810700030b007a0302c0c0380c0c0801446a031081107100500169a400c104400d03916209d80103000c071640c03d0411602112517124001110750680803540065281e07101c17000059900351088110a810301404103000401288030011003032418041e005a8440c0000803201c041510814170381c3e0045580100103440000501811045c840700000c02528103d0b428000010140d510a80c40752140340341100c24401030081c140407421582c0012001018005425010180c00eaa52445080c80051001c10007243c51403080d00d601c912800b004104641e17898071b0788081d00080c028920f0646104c1e00e4008089510b0814408603100d44003030740c44050741e0690315134070000c0100e00300201c0f07054151152030008244020345251400b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 743933642 1250 743932392 743932417
    0x20a140a051b0315130f0b0f0906040305030105010c0804050306070305041703010e040213021204050d23040312210902330a090503030705010e070812161106 69
    0x1000940d0800781c2c03405214000c503416603201901c801002e03650001d150281045800504120303580d841400307a603000c1044c4805800c441c5900300440c10880c20010203441200d400001c102a80c0310000b02580d035240454005022600c100010702482d03005000503036400784940c0c0082d20b020780703450200e41400420b44001021a4843d0140402c0040045c00c0118110400d040d940c210342c54848484404603000d400a8003030500e00b605541d81e28959011034401220100e0f01207118201441c225540d0072418440c03800051408500e0050614000c020021340355603210104c0c00c02e411a216560401c524680c1401440310b04201c0030489203142c1040c24500d000c015000030000e41d02c1c014807040e0320000788514111984103840c136014420080d07601c650510026400d60b1908240c3d03400391500d00d40e54101551611000c03600004200c8150005815140b2000648002958a0b102c2c1c80d0f0345c40224100484c0c030002400301082024001030f20401c0c030f0740201009a1201000b501044072940000318802c2c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 743934892 1250 743933642 743933653
    0x19051f0303270f05010e01020d02071a0706150509070201060302181f2709030804061505150d1a031207030e06040b1806090114030a0608060708010801060b0301030201050d0c020a14 79
    0xa91b82000c502c01e506442030002d0002c0d00d03855000251504103a004292560803600c41500d0b00719030710420f90740300d0b0794000404c201011031801521003e000320300ca40362161101e107000441d10ba20600881c000c40c1d174050045415411502a044e1901d140105081c1e2a051040c079201142044884044020844503001400c00c4503080d6103080f038405c0c2190f40990850134004020b00295110007041c0d44660800e04c0042c1c40301e124080e220380c0d5a025807003180c4c0503400034050504100f8000c02070409003440002000403080c8800150404440950b05030303803541191580688004040d4010841180300b07240c0401c0c02c0c900b0342e0020752a03800c560041d4505103c045030008079400d8240c020800c00314100d402d107060104a0340000c01c1c3e0f1079000001e114109012020489419154009001603d50306050710100c0c5050070008144400c01d01c85c0480c50b41c00d116001850030f2a01c0200ca05032074042e916240b800c40d0390b034010406840b810008030b0840c4901d21402020902000104607103c20a001a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 743936142 1250 743934892 743934899
    0xa0c0b010501030236060f21090c0907020309030a0b0a051e0114011b060203100f050108131407081f0525020a060519051f0303270f 58
    0x1020a44141c12081c1454410810642140070b8480c001c4001c001c09016401c4d08060140502c0501d80e080c01e1041d0003400203c0c10418a00300003000d4004003140c9105101c6086d42443c9244040a05491102c400e401421001e421814211031032035000341c10b40122854000d100300803a00c1d060000c1010350301031803603006000400b5094020240c000080030003000c1001101441002c5998040c46002c0080f00300140e0304145034010521000100021804000006101d0424501944c01254562104102c0c0ca002240300380a043d025429a10182c0d134003016569000005040d2420400c0262a021400c2c6d20842e400c020400c0110040c292850103080106404911868950b0b400c984070300045003010100610600400315208d0009001c40e18202e0301d42c1402d4059060030782e62040039003440d05100802207410140c1e000040c1005900004210301d68a412055280020380b450303401401501c61405c2001c2840ba103903010320540000e00b0089030300c000b041c88100c5802d96074449004d0b210480f0082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 743937392 1250 743936142 743936153
    0x30911090606130605091c03140c0f0f0c0307063b03030313060e07050f130b19140405070c17040b0d050901230a1e06080a0b070e13090f080a0c 63
    0x141c2011001034207c3e44400c0040d035016141e914248040004000c1c00b007003040e6400313810803284004046040541d12a82ca190303a140752203620194a250091060680c000740444c841e201e43c140d10205240100c200016402c42002200e07061511901d030090000c4911303c1650301480254008e202c1d200c4c400c54511620710b0b24a007901c0850760060099081104200103d4450074449040303042d0407291814010100040c940c01080002a8513801001c0031500d2000941038050100c291501445070f1441c0910410800c000e40b44111000c00c0044c80b0010725000261440207010700c0031109404041c1030588074060001680c014800254030103441d102070112140c001c2c4030f141034041d0350b0482d0b028805030f8460140c41d4588082c0c00c181806644540340300b0f160301000d1108103c0c04105034184201c9a030341c0030450307903100b40c21015581283d05c0300200d12460b0066120400e042c10182c41c17900040e04401070040144410f4500396a54803185444900161b00d90700101840c04a585aa0a0564217410038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 743938642 1250 743937392 743937409
    0x3071a0703270305070203010f050708040309150f0f11010507052a0303040f1a101809050709090f080c0d1709031630030c03091109060613060509 64
    0x54401c1005445902c03000d00e28410036845015070107041117960f51030503202090041c0080c1c2c81c0088281c0c42d200a005086502100003801140255610f240050321041082c46c81c0000e800300c0e0780441c44100da8580342e28020313403804208000a0421107180e02d03034102d1003400e444045815000099000420241700344640844002000c00208813010606100c0c070480d03038a00c8081c00151090010028850400c07036514190001301e0b00c0f1604268442c1000032114000c08014041c6d220040c01042c00c81c1810030180c415100d6044c1c00c1002000100d2030444500002d04071500103440c00d15100210340d021661603001006c0c079230f10010041c000800329440044c060140d81c140080d00385c00c02001c4c001182800800c2c1d8500115504c02c1c016052024541840b001c0303141d000300300344d40301d03550b00d8a501011980c0016601921607102032040c01580c090031021a45038810007840003d840003404d40c58140800c03440e41c001c0340a00007a141600c0016000c21107451948010001000064115901c4c241001e1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 743939892 1250 743938642 743938661
    0x60f06150503010b0a0305090f100b010f08160f1106040f12050a1d1f030507110c0d0803060d050f03030a0f0204050603060f03100e0f190c12030203071a0703 69
    0x14894295418190b44d940184035017403e000c100340e181e00200c0c0d1a00002e00031110400d6011041f41d10f521502141000503140b4030b1070380c0d800710f282d8103013441009000e0084144140b80d000081c1e1401c045202050310030490141111742000b410758a041d0914408010190055002e40803801c810b01d86840c00400801d2505a0301c02004014054010b034185c00800414104110844540d0341c030000c2c02c003103000c0480c0e0003140030300d071151000724081c000d402d6440640624082d648080004061088687c0d540044188442c0c0009084070a10045070400f4080d50300900010915200c000c0355480d0725180051410010708560400400c2c806100114841e4100510424a0542c1028580b4001841c03601008081e075005114110035418180c1e03003440300344061204d00c4000c010600328511696034030300100010080c0c0340310701c00c0342c44489103141e00351040044d40035010080c070300d05000500500d00c074550001c1303055210030b210b44d01c00a211222050291502031200840c0ba141c2035000405880e140750 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 743941142 1250 743939892 743939897
    0xa03110901080f06041e020d0821070f1d030703080301060905101205040f0b01080703020901121e0812160f0f1b0809090c0a0f0503090d110109060f0615 67
    0x2081643c1261000c40e206078800e4008045800e005441440030b00c0c244143d10009501100c112111800c1000782409080c41315071a4a00300ea5400e849072040107800401e840201c0401c42034010150307038920845083c000340750034051150226180340c010034a4408140c1088600b1400800140080d540c00345205004007811a84d800000d00d803400064545803881c4503041d801500d9900207028026242c5206040c5607021700d960b0000d40e91180041d465a4060000b00e12510024000040003440071003000c0e8110380000340542684540e9448902c00142444120742603002400948600c01030400600e11481e01c580300b46442e1041d40d00001c042c2c10800e42d8140a0248041340052001e03840b040b1555420440b02c0003421207102400c01d40c50354051651696846800501006010f40c60072019014109258907aa4403042040e401038596000841d400032150303000d4030722a5105841011500e0120202000006081d140d81d00c6580564140e07408520100c1d482d20740c10801c040801100032003201d0350b0f1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 743942392 1250 743941142 743941153
    0x1a131e1b08071106271b0415170d0908030c1c12060b040302090f13080a03090f110a05010f0801050402030a0e07080607180506270a0311090108 63
    0x840d810441014032126041086995800208143c0c00740c400900105240c00c11200c0b41c2ca02100007050407503180101c0d00081d58003501e002d292000003c0d8000c040500c1c1d0a0442001300036406100003496148a000e101140e100000140120f201b011104542900340141600903500b85000c3c102c01d006511407603660348104030000e522680812030308900a10040c028440d062514003c031081e0030821290f40c01c080c500100010100d0440d001441100c0c800d4401d9510f660701c1d40e400200c401030841d0185510852010020006480c41008115815031b0782030000350800740c1e0710703030003d040100345049400c5207115080040030301d0402c0c0d4400080900b480c040c040b0181d20701c030043c44405c061050500480d0080301007102c04040743c120401a800071400c842000b540c808242d5030743d4a0546006c808120408000c0080d41c401c500030300182c49010b4020b501d0030041c0701c2c42c808425840354040040a14410785012159500241da0004600802418100150180812540d410103901041c0c595005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 743943642 1250 743942392 743942411
    0xf1c030c02191d0403090b0a0c0c05030607091401140403060b0f15040e0603150708011509030c0501080a0e030a020705030c0f010219080d1e0b040504020a05041a131e 73
    0x40100b8602110f0f20360343e5003000350700c0703d1070141d030b01030300c2c03500710316001d500c082400003402d54001c3c2100e60260080c1c1b82d105003642d8410a2580fa81004e46146001600c0100d05010604901003c000345140600d0030300c072004011229000603070400d400c01c8030125105c580010709032401c01000444100700316881c80542d1000d030b04080d4203219910684226041440004805540030720100300300c2c2403041340150f203d107084c44d00104a50b08c00d019070701584145400c14440d15106503010000d50740d00140a0081c0b5091600640303410030000c0c0000a0a5110701b03200c100e00f00c050001d171884681c00c0d0010054941060105410507108015650050440340130b02c200c0da80e400150032003a9a0300480540c03645040742001140d81c42040881e4910070305000d03400008500328482d0038506603111404000c07190b00780080100707880c0c0a440c040d50160241030f0030700c880c0c50546e00c0011403010700c004242c811091100400d03d06c8071551245800180e4035441c0060000c0b2040b59503035840c0c03902100304100c104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 743944892 1250 743943642 743943659
    0x60f010b0415020a050d020c090108060618270303071d060f1606050717060103052701020d140708010f030f1101052506290f1c030c0219 60
    0x1d51152507000380b40b06007460081c600a11141d1403142d0004140c840c17001ea5490069a00c0612100207809107150000000724aa008148180280c00c0204032881012010007144a01e05014080704142614030702d00a00c0b061b1076180c1c00040801e08005540c0340e203444903020b81f00005c42d102c4480c018030008880411903503054103c071000c85a21100b543c64480320745015a40c4000107800400721440c107820700401030b4214450030704a03488460203003510b50b1750b03200440c261207094030349074000b840d902010418408407000d400d0005040c0c100041c2002600c400a0042da400d482c403101d951800182808017681c1d00424031800b50403142005d00c0100d1442d62480d10b0b414900b203014000c1ea44205a5204581c802e8085401d1210310176907604213200500c1d0440e28070859010220307800c0e4500090650b40c0e0101c0740485101c40c2c1200c0707244251010203400d1020204400c044998854110141807205440d441107800465020f0798032129044c06c24414010307200554a1108003002c151802000b00c007a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 743946142 1250 743944892 743944897
    0xc1b03171308070f0809131509020c1005071112030a0c0302070b040f0f0602040306140703060f0527160e090c07031b0204020f070203150105150c07120602040602060f010b 75
    0x10382c0070010310000305250900b8117090040402244e0702010340010281e440e02c03150070180e11034003184003c80c0c01c40c0e501c400000c01c911618480b0141c03500000d840000c52541984a40d41c01074050826181ca0303c0c20780f21260810201c144801404800071080c403040342c49034840c0d0251052070341000c6140c009952140390711454000c00080c10001c0b200d440800304298800c6c02c3c803030305a0140d0305648481c0c8901c0c0c81c90141480c11804444040020001031540d8071900401c812100c186005008440c241000d01000c81c080703840911600c00301d215640c000c14152450503110b0300f1a8900c48140c1050070100501498601e80d81500c207a1042e01808124021401210b14040d40360414080e09080300c1c1c08500c16102c0910f0203940035202140494000345180020000640300f241a110041540304201104200a00490b07030030000d10700c8280c00d500c0d907403401003241141117000c84d003105a03910030740442aa00c4207411201d040d00480e04101d81e907010854950403040400c0403070043d40c1015488015070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 743947392 1250 743946142 743946157
    0x1112060904051c0e190510031406100e0603150907050418020306041811011205090304050f01050d060f15030203061e01180e06030d02060108060a0c1b03171308 70
    0x600c4201440302881c081e62851181380c4001c1c181900e0744d100c1d1203014400081c1403049a0141d40c890a00140c200c0c0f180c460b6a0350024602048500b07a181d040900000030402030200080c000b003040403039107598400c00954851800d5850310b1541c6d40303c24050000c1864040c100d0320a0103030a003c01d1040c000d5503400b03024100003041e40161a56220340024015100030646e2421540c924080b81c820300c40002d40380443c030b8000f038880e4200d5142c841c400b6012510220784d00101d94100b44000e111500d02130025156407501454001d08140300f400301d0030b045540560215000303a014210030440d40d0750503141036240c0d2070941811415443d050000c02c01805092012405040000c160310348143e004d030050080703801c0740c094280800d03520384810040541c800c0d28518800c0c8200a6240921440012003605841c9100c01820b8140c03202c0483c003000e06124541c880030721081501a113202c28480c245a41c0e01e40c046d5546103540028540c0402000c400501408081615103c2c00b1001c1002c050844018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 743948642 1250 743947392 743947423
    0x1503090d0f051c0c0201060f0503030715060308030702011a041812030219030b130608030a0516020607151406030a2301050108070e0601090e0105060a030f111206090405 74
    0x1560040c40c121078902c150f1a5015141481c2d4020109140e0746500151400519400030802607847c0d400059000c4928441c0540c103610804c05180040c0b0b034540580100407014801081031901d0b6030718031b0301a400071500180184c0d5114002c42a80520700b031701380c0c15640151000c10560740030000e448580c0391081405060f030220351ba89045018820380c1243c0061103403109210035100d04440c0100030340320159030284200310b107041601014040b44100c80403200d52000451504005081c10b442c150004840069810b580c0c48892000d42c80e80d0009003222480b038080b200e1601c1a01d5a81d0007160b002d13184240420602800b00a030030f84001500c003013480d801054403600c0c91450a0b00e1041150040344200c22542450f000040ea1507001800d0000c1c6c0c4d86104016507250b0300c02d17004480d5926240725111048080400400c02400c101c8020072403d4464030700411003481d0704101d1015110703804524101d00c3c3e0005032a044000c2040d07449908900215403180c0d080c181901ca2aa0340c801c9000e00001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 743949892 1250 743948642 743948657
    0x90c03150306130c091103010e040c0902040308040501030510080717030408070b03061503071209020402070b07091401050f090906030708060103030f0801090e1b0402090d050a021503090d 82
    0x50000206580c041400000c1c126030480c40c0c401031640d000c807011981102c40160041d804520903485018007078049841700c0304541540e1a0a413404540d91000c1c0082d01d46401c50040071594040742e00041c00a140a40e03c01a03483d45880001000c40c2c078001d01800b500c5110b42c5091051132004140c00e407c641e01d68076900034002d015264141513210ba82c0c448102480740100015080180740d005d0352050508680202d28940329032a51245407004440344000074005002c08281854250322401000d800a0801800d2181c03581d14240320301c005485020214407400c900708060095036000803041502841d0140c2400c1041d40d0030403680c043c201d0842c2c03040c004180041c80d5624200000d6006155840c1100e440c0e5130340b400c019205150300540c4c0070025418000200d042291402240d03004c140c040d00400115080500c24540300e02000320055205408004070100c07651104d00070140d090058018040888640c810440c001e6229003020010707003030a20810070a04008221200340c1d6030103090805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 743951142 1250 743949892 743949901
    0x939030c090b03100602150412120e15090c01050403150209150a031401050a05030a060c03020c030a0e030c040c080f15041e050c0306032e3602090c03 66
    0x44207007203903401c02462503402004126801c1c840e009098110b0320f00d5001e450070801d40741c4154000c1d18040f240074105503001503003486614403c4002c03000d40d1401100c0090148440c241c03c078100200c140341802202010000c0c00a441e10600c03142503405400d00b8454a040c1c03840c0c0d6080600c40d078050054046950120f0701ca40c03a03403100f9003141d0100496144090340d42c11100f8001e40289040603400c4030140400c400401c03242441994081034900c010000c1455400c143d603210082d00d03014000d1001c05809224103005032500304050f0520b100d40d03854100d412468070050500c3c207240d0342c0c82c3c0c912440c1003c0700080016088000c0b1500440c6110603842c040d0354140d0341401c034050050751240c0041c034004248501d03c0b8502043c4801502480701400503031526860b807446400700b41d0f9140c1e0305403c051180d41c2c10701100f282c01000e0540c4403401440c41c80114902d0801c0351940c99a02d200d1219030000c04c01e20205100035003488080030740c2105110003907500400c541003001081344201c001c0000208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 743952392 1250 743951142 743951147
    0x6120c040b030a1209090b0d0206180f093c04031b05060a05060405060904171e0307020703120203180108340f0206150f06040905010939030c 62
    0x141e0403d40140c1eaa2420341e013a802d00400d140c07000d02c180703417840340303000440140c030301e8402c4084154940081a00382000d0303038410b01c102d00344900c404840e0702ca00c400965441c17980302da0038414880d514901580901c82d001081404485000c241020101e0140312003401da4480841896a089900742c41c02c0e81100c40d5000300003000600c1c80304080d1983c42400204020280c4a4104903c19031081e981400140c4a070001e101240303100f5540200700000070080e81d071102250101034444014029040c1c4548000036441004550017615980c005030003194040c0180090751007070103100c440503c0214508000210100c51841d62112440d04001c4034030045808481802e011480c80e145404268001e4602c60400d1000088030905000109050490050406001007805846035040314198002c5540440803c00c4010f00300c0030a5601c003c1c184000325090896215982c06012564400503012824002e8611000141401c40c0001307141d235220a0300703083c5064031207a1171070060305010401034030b140f0b0107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 743953642 1250 743952392 743952403
    0xd0507080d0e01050402041802180a1e0203041e0308010509270106030308010501170402092e03061104030302030a03270807020406120c0b0d1b0201050f06120c040b03 73
    0x44140442c240804408903100660000d40114400c81d0b04001c4c10f03d40b482d4120b83c654850324042d60164642e96200701425500140d543e0082c00000000703170040d20b082c06c80281003040800e50400a50100801c0104050411a140c901c0021550305140031f203d40e80003402190140111401540d421012070301c242c800801c007080c2c900c14800341107000762048203480e000306280c0c0300c2074002410070700c00010b00d54051840040c2c80f100b160303840002a40d5a0b001e1040c8036101030019481d8401403002c40d0610303000d5a842040310400c0d00c2151121500c0c608102050701c807500c2c010f02c1ca9000030442000040e80000482d0042e680c1d40c20007081070340b417050f08440302500c1110304100202100d401c0d5020480c40340020201c0d580308640030008107444502c040c001c0c0800c0c6500902d0b8081a8400348444005000030304000b001c0c075103010984145441c1540c3d02a02548601d0001d80c0d111360034080705580111019038404c0c1c0544004654400d1403a449980702e40c0c00d16601c0c0180d5a4a001e0b1481d5101480b1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 743954892 1250 743953642 743953657
    0xf16020102130803120f060a0b070c0f0e18070e0a050601021c051c020f0f030c07060911030c03060709090c020c0315160309020904170c06010905010510030e0d050708 73
    0x1040419540c0380f0ba899100d070b228800407000c1e408200001303801803008140480c0500805032040c1e0445007415244c1c403003070303200c100c060ba6113103d0b6020000b80504c00c0c0c41c01c08090b101808440e40242004140c9154a140c403d10303082d503a0300641d8040c0b03d80f800d0010f1095120782d1701c000200e06a00c50000503801c1580c8459903c041a230101c4c00003023451f800400800d02d40140040700c200301c500304c40c40801207018504600c03107071000c20404007102a00c104040e540105160041910f441d00c2551b5810848001020440b814207141d890b0807045c0c130b0240005c5420007002c2d0047e001e10700d4199001080b41d0540c1c00340c40a90b0b40e6415005807000d1080095021841c4064202d447d1045000300400314494111410203150080501c8410014403c2c001d6aa2440d13000d00754640c40c0d200c9907500d0350030140801c5601d5550310244a00c0c2c2c02d04104003c10380c000c040c65500080ca41d410202841000c0c032003000c11000b0300d41040d645469601000030130b40020b45080c40c040da1140324524106055215012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 743956142 1250 743954892 743954917
    0x15041508030901090509010b03010302090405190309030b0f0415020a03021b0724020a120e0409060507030605010c020a140f060a02010b0109150807110f0d180e0f16020102 75
    0x480220391030600000510b100e88090b01c800003042e0b0741d0420070840040034001c40f9008036080c801000141005c580350b83d0030070310800680d8210000320044680c11003800800ba000502e1804040081c0107003101e00507000f42a44a400c1e03800d02c1c0c2911103101d102d000301c240f4072220b41d0020301103040c0d034400d6043c0c0c4d0908080310000c5200d40f01c51540301d641e407c0b281c0a55030450051003803200c814078030b42815140a41d1142c000c2c082920f06a200c501d150580b04811605101019800030056a15441140300c070522801c030014a9080489000342203c0c042c0c1c00c42c9061080b04682030300965180c17102003044807800412044c20038490004285903841240e12a07404c43d80c0402c0501a83d0b40640100c0c43d0b5420a80c0d40300300d49070307403503410130211010301c024900810b848501040b241c80c8144a0040e10004400072110311b400e40c451071524080419400100044074084110365a10650381076400034516405803811070b09040701c4400b001100503000418055900c040c03400c085001b034040da094114107a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 743957392 1250 743956142 743956181
    0x160f0c1b030f02040e030a0c03052104050a1a100b030a020906040326070c0603050411130c080105060c03123102040c0201090b1315060b092103031504 66
    0xb03260000300344254040807407045007843c1903100c200c10000103480d20301c2565555142d440c5d20548003562240d00072020b517540b100d50084a810701c1c4c2d031850a29405035204200a000e2400c0c10f0030b12014145401d124280c03151000307001d0000507030610207000b040d1402c50380c015a494840b411071030000c3c841c81c4000781c0c01c00d60204000040c482d440104407100075500024102a0010a0440000c1d01c1346500003005403a03920001d1000620a40c4007561044c840d01e2400c0c0302c007900c8400100c17207500b002e006000079074480c0c1c9107203036141c0d00041140c01060706856550801c41580e141310b4403401415007240801d02e46000040303810551a400360301a1800c0300e50070250085072040e10b1180f91140300113900031410407441d60181c9105105800300f40360018405400c81e100c0002c0b032100482001d900b51102e603184d81d20b94403a0380c003030300c90f6200900a20b0a00d0342c1c0c442184c0240050600c0c0c58107541c4182d1030520f55111452004421a82c2c0714402c01030606c1c001601400140041561860500c1c242d1101d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 743958642 1250 743957392 743957399
    0x302090a14030f010c080a050402031038090a0b030304032f0f0f13110d09020a08030c060609060d14160906121202070302090f01030209160f0c1b 64
    0x1901032007412401c15030645100300b242685842c240e032503c01c00340c000528107400280104c07441e039025940062005050300c0840604078141010748540a01000b003400e001003400050070007101d03000c402c5803140c0d01201440c13134901c800200c40720f500420f01c440e0f03186c90740450406541c1c140100da0246034001178400e090f90b05d0313a00d80422006000124401300340b01c43c0c00c5105511707003800d176154082401001c141d80d4000703400521207c0800300d12100040f94a4410541e642d1107da4060302c0340c816107800c00125200c0b5801003007481422580900850b8008000d110781410000c255103601040541e50300516807541c3c004111110103034000517000b48840c1ca80d203140008041603013405440c00707421786641c0c0da0f00d9451080c102c504521030401141c05090700d03a00011030075035604c02c20001a0040d2a482d642c1d0b0340200d50003110441d42c5001c00c0c44110018000c516040c4039a0350070098081d070400c1154614000a4441104c2211020601c0f010089203400c01420681078800c00c204a016910f502d541e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 743959892 1250 743958642 743958659
    0x8070c0b03010603140a060b0a120221040b0a2309032a0607110d080a020408070321050405090619181e05060102280b010b0c0c030c010503010b0a0302090a 68
    0x22244442c000c10707410345d02048411280380141c1c816200a806803900e40300c0d0134002a00c102c01b058100d418800c0d0207000b5000500900b0b442440040310b0940c400c400ba103072500c5d0014a83c2002422100030600e0f10000c040c00c5080080d04031200c000c005c80d24000c1d61600c00446195000e020121707040121000312011580c401003100e0b1074960005021102d460b1660441275840910340d070011503950340002e080e0180c1c140316640c201d421100004c0010314003030701c41e181203081481d240c106403440032100038401c209000342500e0000d40c4200e890310500b464280800143c4003003015041a00c104000b5800d44503940e0004840001003100340d450840003074080311204050401001a824080c540c4901c40c14203807154080c07248034040c16405091101244140c2888040f07001c0c483c024071400c405c0361140060402010356011f4082101341d00c1d2a107840094051070164442c1443d8041d4100b445058150790700700003607905403810100341d00d4581102450450080c018900d2540e40004200000100c014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 743961142 1250 743959892 743959901
    0x60a0902010f141c020d020403030306082b0807030209040e25030507061b08030a02030f061c02040b0d0512070b07020d020a060b010c06050a0e1009080708070c0b03010603 75
    0xd2003070701c0b01050380b03002d00c10548125101070390085564400f081300b50b80100004035880c80a80e001d480040c00d1041806006080381c220350011002710303a4a01090141e00c0040003205081c00e0526005450540703c116031440c20010340c0d07448020303c266000429980c90194059038150310000e4420001c40d503200c0c5005035180c80002a5124100c2d180e140340542000818409098941007001030503003914103403040301c1c108030401001c3c02002d924481d8000017040f807801140520314600d0090388908140e2080011401c018201611880c40d0944d0003041c13902c68409000c404da0111000100b0302644070104860b9490401e00402a020b00e60250703d5a06490b0f0140066600a40143c00c8a981d846016a510345000c031480340982d000504030300c0000c0c1c0036081403454480625255200320311035a6844160350b020796450b80030f0750f210701c02c1c081185c0c004c0044100c0980072000c140040b015030b4903156610f00c1605c0f000350134035400007001030034444e0103c580d1000f442801d0b039840e969a90340710300a0060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 743962392 1250 743961142 743961161
    0xa031b05040b040c08010e0705090a03030203180a0819080c100911030f071a0d0212070215011203080a0908030c030f0a111611030f0c01030605181f030203060a 70
    0x15860411000d99604040c0304944c0400669107511419034244a5035000c0703000e00425910401100304520311454651108000003180303e0b400540d2190b403880540780701c0c0320720850024041c404030001082407040002c0e24100c204c0c0d03c030703454602199007801e144287d031165a450300000e02c40c44528118242c1c241d4000c01c000c0780241d104079030150076a0704054994100d078103011781c1d40d0b0007580107101075a20310300940309140050030054540f0300c00d0b04220701a07030010081c9000700032a4404024280d6014400e4141e10074410b500c5616642c10501c0b81079405440a8003d810800c1907030004a0b000340d968070940406410020407601d0b454845010080341e4000c841c4c8a01d0902903501240e1006034070300402030a982e8031800f450824000402c10014502030007002d80b0710301c040b2991741e015618180000e0a5910482000e44420b05100c0005410f0300c0050307126500550304c40c0390002005035140c02a40c2c00c00c1f000d618042c80c1503107180400d203071900c0c03642029500d40210320911580c058190f0101821 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 743963642 1250 743962392 743962399
    0x812042718050c04060323011806140907080706030f020418020307171302010e041b180609140402070f060515100e0117060d1403030a140103050a110a031b05 69
    0x4250f8680500c0161500751100500000d900200f0301408181401c591078800700c1c10000103880461007014210b00b4503001000d68050b9913400b8941903c6010200303644e03200345804000c05400b0700c0d0841c007555904044c41030130100b5944584490005215404a4009040d000c5507294070081d00d0400340001c1d401629010f02203258104071100809d001c69129126500b0310010304010120b0380c005565200106040c581d1059441400b06801540075940d043d514000355240000340c0528080011000000e4200009000d402d040070041ca442002081d030740c0803000e44016841e00351910b425801b803145090020207482c117040402164001403044031403c00c1c0d04407031b030506040306004c013510f20780c0d034480403640002d00c03803d40d000c03012203220031090f080440030b04041c2c1030340d00701e4a5040107548883c0345e050b000e0b0000010710a280c0300c00d00528189007d103948003c0346514550b15256113082d400c0d00103180038082d021815840c0c0d01d00303140344001e50b0091003188400000e003030450480c0c0ea4a0180c940b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 743964892 1250 743963642 743963653
    0xe0604090f0b03210d20030702070501030b0d0209190608120a030b09090a030c0804080304121b080a03110c09090f100203070507020603040c03051f06081204271805 72
    0x3021203c074184013400c024682e184c0c0d40b900c0e410484410262001c072000c0413078540c1c0140804190415100150300c0b0b40801d41c0038042080c10480010260782c10b032000e003882084000002d0380580d5520800390f80018910765130183d101c01410200010b0300c820b500000c564084e20000140c0058100001c103600c08840e40c0410100410104114038900143c481d0717a03440d442404507000003130140c9ea4105a00303001340442030030256982c0180d03145500c01e800250241c26212501010004006050610326940c104c085800d1410703c3c201541e6280010006010040014100c08a00e0000d0118624265000d401d049940c40e14140466448074400714410b031750b12403900788203202c0f1a28800e6a00603540c6598403132030070180f030b001c01c212504068429900740f5800100000002c13020405a448a0722104e0002c201c6103912000000f10340055101003019080b243e030407502102c550040b10152014001c80c4d024803680c039000c034440c4888901084182c01c3c500300010b003101850b580281d0000744640e08650 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 743966142 1250 743964892 743964913
    0x70311070b1312060f020307030603030e09070e010c0c0f0b1b0601321c12030e0d050705011506030f060f030c062303040f020f01020c100e0604090f0b03 67
    0x865a10504002c0e40c0c50304540d80061154000c0a80320121860141c000810b03282808480070302240d0080c0c07652800b00348d60700010030400d508254011071a80c07007190307140301c0d030315114001a20001c44024411704003d02d200002007000000c00004000d0407240401d070144075120351030b006d0554401c60400807410b6001400c850180e00005e407040c180c40c41929100c414549000740880105540f40c601c440e400301100d00710f01c19454120482c03941000d03051084000c076155003001c2001d0301104d04600100b50038107030544003111000412000a55251808541c0ca400343d04040b0b0040201c280c85003400d40440500050349a85034100100355460302c8030410501741d0740c84482250f180184001044410607407002c00c03806000341c103218005155184600d10041d0200b65103070056004540484d101d2222000391801e508044001d92514402070006001c2c0e119448001102c1d150001107640800c000a89a80c00d56284e880c2680c006000e03a40e800d00c40039010780f0407500a009501600307402841400c9088 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 743967392 1250 743966142 743966159
    0xc0611071a09070e1320010e0303040b0f030a0f05040b04050613050709050c0f03041407270507030f02070308150109031a060303091008061003110a081503010207031107 74
    0x35030052a410000f08521440c10b01a03541d0b142e4000c2404010326440e49958000c11030101d280090b40b41d00500c00030f910754903080090600c8909007080d0b4001d40c01480280f1004290b90202d4002c0311010207229101d40d514824480506000385006050702d003004203000c201303c801254030740a180305001b40c41c00f80c0e80302103004c0381c25038040385c0c045c00d1540a03a20410100e000d650000d904506806110791a0104484002c03020354030a45080301c21141d84040422040b5060028902410fa000b0610100885803282502d10440340c0700410121384ea20404548611b00036840740d1000001024199240d0700d05003405009510115800022041100403600f029881242010181c0364007030841a0300326002102511121070003400709406100c20840c0f00c415076282d00d4800103a0100b0b5441e88018a014401c0c003440248000000c002e041c1004185c02090105205803000200d5074946040e966275040981600da503002d0100c0c0350554070006c0c10703800f131640c030a000d606503082c0801124401a41d07038200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 743968642 1250 743967392 743967443
    0x20d1707020f04051303110c03120d0e0102090d031b0210120e0604230115030b0a15060518010909020c010501030c0803071208150301050109060501180e040b04030c061107 75
    0xe0716003a028080c51400640690042e0031f0100c094004c56031a00281c1000c07a1900c1c0c3c505550305100700010612100c50041e40c002c10b10b40d0001030000b9400d150940d0080340c0d4240b28200010180464012904890038501ca580842642c009001c003101d10203040307024080644280382d10406504000c0b00100d0f420700003072028051507000207d204401c2d0030386c042946110441d411100c82d9501d17042e02807490b010148948000e1401000e542440e4140305402034101c4032020440349440240390810000107070440181c07008452040f209601e04248800101d0700c1040c0e54004198851001c110340c4960201540098140c07440b0716000800c65417910007060350380c06400801002903103050900c8a40500c02c1c5601a0880c0341c000319080c0640392500041d003910350076000b198280c1e9644504029540c4c1c42030b400100351120801e0781141500708591250030340f0004001a01c1c0d6400a000705080ed440f42900e00d10b090f0300840100071010f280c1c11201841d40c0150000e40e411001150100c2401018100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 743969892 1250 743968642 743968651
    0x6030f030c19240b09071701180f0e030703140f030105060a0e031b1e0d0b060f06040906150509030c041e020408071d01030816020d1707020f0405 64
    0x10841025405040c4140480742d190840d240b10a80400807103448014a03100c40030492001c000c1200010441449501e01d00248000100f144180c6080a8001440c080e00e0640b00c01ea80b482c4561810624428054485002c143d840e0b549070030a9001c4251010000e000b00030721960b140558201984e200d41c0e0f45000784040301c02d00715800c100400141c60500c00810744062300b03083c0402120a00000681040110701103100100c80c0407805141c0c2e0f117007050260b14042c901c101c0541010401401080c80101c150710300414045407680400c000e6551300b940400c082e030009200c00da540da00e50090300e000d40314502c900c001d41800c06801440250240b1305842c103041c005801420000360072404c01010f0042046581290300400c3d040c1c024040c524002000581214001801d20314130b040300c4590707140c80503958003014055030b40040c400180040101c90101d000c072404013500e08481c0c00000c9652000100040c4002522140d03103c0403020342000e0440c0c2e50003203850a0396900c1c2402440140c5008030f4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 743971142 1250 743969892 743969917
    0x203010506030a0e0c06070605040501050703020a050702011b0f080c010b03010902010c1b030819090b0a08070f02120a0306140d080a03020f070609030819090519051f0506030f03 78
    0x40000c01c01c3c811a80107100403601c0904903035a809207200405c0266009841c140c600030b441d0780c100304c10301c4000d000f0150000c246e0b00d0118601032070203000804a025007070000741040300542c0800400034240b4141210301d50042c0403101b00d1030444c68101941d81c000c1410300305035420440c1440b000d07c1d041c45502c80d01a010784882d04200310070307528503042c1491036040d41d03c4852444c03c00320110341c2d44005084594180383c01c020b25424a200060111b80d00350384400c1d881c3c02c0400042543e90790000380e9a4001d031140c2404000f400c1804010303414026000030000e04d01c8808189401c20744d500d41c102d04105c504040c80c40341414010820700203107501b80d10014240c440204402c6081901c00d600402d074018403008000c3c00d041140d5030700c105070f56559070241e00182c0350360b0510000f4a03400c141642401104401040802c00c5036031925211000c400502e00c91214004100045c03100600854180d42610801241030700201120b8000920059070414064070540c0c400051008002040354400100e05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 743972392 1250 743971142 743971147
    0x1305060604051e0a0605010e03011e020c0723040c08070c140705130f141311010c02061603020607020d1b03090e07031413030e042f0702040e010203010506 68
    0x1000344409048040c05141e000303202c02c24190001020314200b5802070403551380c08250a45460300042c000e01c100c81d40743d4826403409102000b8800f81960050341082c2100300503854070400039061b0b00742041a8825251050101104048a07084034a0b40c00fa0080c11a070420403900780707590071261031204850b4500403402c199104001b0994005070111032000f01800c80e00c0d21a2075601280080c3c0c1985196040e00c0e03140c8550050030b030040d000d20509103c11070410310351440c202c0218510342c441240c0203031100740d9054011005900c14011440140c0d009030809030388d441b007400200440c508524080d4014050701c03000c5545140b0126280b504614541c0d90030800390b2074074007121050307602c2d0364046080c40b0040d0000540882150a02803144000d23440004030144501c4d91a21300324001005004103080b070b0891400081d40044081d8000718040e0740008401e92071146074480724505070a820000e00302000c1e0801c041401e2401003038400e01c25074041c4591011041c405090780400e0046503400b4809 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 743973642 1250 743972392 743972401
    0xa1e0c0b0406052205030c0106140307150c020a031401060902030618130b090303070219020a120609051b0f03070e1801091a150a0b0307180b0406050c06130506 70
    0x10340c000b1500040c061a6000030700c0c0180b010280c4c0100b0101048495400210f0f03e101b4040084c030800c5d00a01441e90a10350085484000030f48481c40b6019031080802220194100e8074030842128052990107490105100e0300c0341000d80d40d01c0d0000c1d900404560034090080303038080c2e272402038900034a8090240c081110052001c0c001c2d00d43c0050030681c001d01001d0982012800800c0442d00a044a00103903681e4100010002e08122065044003441e0b0300c11034031500162159400d05045030722221030204d8000d11171400340080d180c0100b001d00b09101e00861a000042d00c02401841034508541d480b10302d60448042c903031505014803079030308040003480006040508251007540c071502581d000184c10381c2c00e991384045440d8070040d40c9500604810402600390b40c56500340c240448200c901100140c81c0540300040c900c00144000c003004200e02181c42240324400f0140058403501190070344407603c43c0c400401036001080d00031980d2160802051034030303050034a103400041d0082c01401042d5039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 743974892 1250 743973642 743973653
    0x709050f012a0201050d091103070b03100b0a0e0a0b0910031406040e0330060102061902090f04051303081008030a030b0a1d0f09120409090807080a1e0c0b04 69
    0x3a1420240e042c017108003c25502c0c00c10038402d200c103180c4240c0e9124a0310740c2542c18940340400e9500501090502002400041c083c600500f00807581e2140c0d00c1aa9070720200b90445405800c0e10b403468000d910b0312400700d00d560501004d490820002e40d007080c2180035084040b000d40320709032445040444003034040382076824507030498080b05401c1001c0b41c0c5028000c011081c60490350100340002010b004481c0d01380d416030404d503260005024030042082d030800400b10b038900e4088200394000280c1c00601c1d400141c441355098403080703000030810000c038a03010030044c040c1c12440c8003c4000661840005900180c1c403c242000d98000500a40c10460300c00000e600500e424215103a000c600000002003a200d0311007d0010944c2c40032280030310b0308000003030301a00354010b001010140c01280845004201c820144d8040311200d5801007039003130710b07420241078030b04c66a84042c2900e01c0000f84d60384c946802c22144107040f10310004401c1d41d000b04131011119103030b62800042101c6020300c0458040f64 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 743976142 1250 743974892 743974967
    0x13090332071119030501050a02180108040327151407031202071e120306050d0f060e0f0a05120a05070615091d010b0405060619020c090709050f01 64
    0x2407282d0800c86503030035500c0000d03c160201c240e1460032050222018001c0090070300950b900118018010750034500c00c0c0d18060b0441e00070300010b504020048000038181445132031120300d006407201074417000e95005040c0c004084894011080c1121100d1a05d1302810310811180e804160116012414400207a074211450070250100f041919000c2c000030000ca00d0241c040130701c2c5210a0720a2141fa14240b5003007414104100d052400d040c6030910810042d12550002c030003680c0d0040391001e1000d2030b0b16142c401805a0b9184e0b040b54414001c000314050000611170074000c0c000d00c01c40c2c5807006840454070041c40f41c011540c0025400b8403e09000815a812428032080401d42c4c0e100c800303460b451a00212110107031440e50039000c459040741e00420a1003800d042c12026a800d01c15442e1070000b060f40c2c1c0c802c4403030300025102c01621003d0010b109100c000c1d200100141100000e051800c4000c1c06541d01e801150b116100d0b801d0701c03604542c0140109078070440c070300c071005038000701e106111001300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 743977392 1250 743976142 743976157
    0x1050a291908220b011203031805060f0a050403020d0518150a0908070509130f0f0803040c0e06012f150a060602060103171813090332 59
    0x111018005512503508071071120401c807046954031000d5241900c41c0c0401a800344018420100101454101044d108000181519542e0380f018490703281502d0304a0007005400070326030401000d020340400b00714011903543d00803d05c00b000381d086074403074281c2401203c20070f94004015a001075071445d0918021400341062408240001d200c0301303000004145003100340c0442032400c2d500002c00c68401500101c3e4a030140041c40e000389a0f5030b0800010500205002c0c103028a08034001c001401004259000b9017400ca62117402c400541181d4601040950011f0360f0032590321282c0d8101040d803201660315203108481c169540c411400c00b410140d45500819900c3d1807a09651000c0b07098484420801d18901b091042d00f1038a184c5801d440880840d04141c20080442d048040100b0215101d80010900c0f05080c0c2c2c00159542031901803c01c03804001901640c000e004020301e41010401641310380401750103600c8102031902d54961291224045001065001c0c082440c24031602240300041d0201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 743978642 1250 743977392 743977469
    0xd09020a08030d0c0f0c11060304111305070206060f0918030d1419060b0d021c061404050609130807080412080a020d020106060e100314090c0901050a 66
    0x80c5070300d9601160855214206142036241c40702080750400da0b20918042800c203d03032502000c015040d58401506406103410140f1a20010021605216014600c12140c4000a1207515200803001c512800b86c0021141c80300507000b0140054464200301e040743c4c1e030111009140140e107035201c80024203410350540100d40c5911052101c9400c49890b84280c1798200120301901599240000319060031304008880303140140d051806c00c00201c10340205651f990505a40c0260322400d400d00000840801020501c041e2420000000b03031240b560150810fa41405079003d008941c1d8900500020040a94010f01d00c6120342c2081e0300410110320142640600c90b00150345015907407080581d000c10864004d640c0c1c0c0c00005111110f103a010842113455400900081c01107510302080980049021003c043c000c030307851007c0c03000c3e076403003a0701c20000c5410180c8080300e1401c0148200c1e60300d41d00c50020701d000e02d103c68000f1407503140c00074881d412510b05400360b604e81000202c0320b03410090b03520f840300c80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 743979892 1250 743978642 743978659
    0xf040f090609021908090c060310050906060a1e120f060611010e07090906060302101806090506030105060901020a02130608100501050303070f0f05060f07090e06010e01030c022103040b0106140d0902 87
    0x1f5a40d0361000841c0101029828100349506200800c050700304041e00d0a03124400400c24100c0c00c94020408110101035405050403840080c5411780c1c40d50140b05040c3d01c1a8941140d41c43c14920903401481511040c0da50444040031480f104c0d402c030360608880c0303001984480801c2013a10020b0300405049440380c0c00114021307540740c1c042010010301c2c0d5485404a408190311601007140d09484800500051178030075089403806010038124030042c010107009810005100030380340d000b0400d00c21440da0241089030500c450b00e8007400104803074000c41c0c1040c00758801111035080c031406190305a842c020040c6107404400d030380300350080c003c0000032250308120541d5807010442c02d000d01c0d441038400c241c41e46c0103880d1210740140308140b01d070040710315002844203110950f6032103101c550303517003400307003000202810f0700d0f40281d00d0714404080302d4900c032525940080201410300e000d14015846600a114540d0703e411043d02e038581da04440d003080c81c0c014000490405000e8001c0341095001500e803a5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 743981142 1250 743979892 743979913
    0x1908030711060c0712020d080c16140106090b06120105041a1f0305010e0403020309010804060b060c150601030b091605071202010e0f0d02210f040f09060902190809 72
    0xd007000702c11109440d14200105081040c0300c0326014000d402e504504c050100d5042410016080ca10080c2500c83c43c08004264044001c0010400007540d40c0c20403c4400101c00c3c1e085401e000e008580034603040582806111809420040161070702d01304c00d9502d00716240c1c01d00c01400000c100c3c00030078402c8944030140e81074817601e0b2403070300b02d89200908840080c034407650b90b400303420380c1e006900c1142081100010000465404001e55003030300300918002c015511a42007070300c0540214032506034000703000540c59081c001c1c0002c41e0410417250341c0c42403d00d950f41400541c1205e8601c103c10360010f1407040000c0007003000c13140e07460a000e11030401d1030402130981c46a14060700881c0103000540e54800d42110300400811200c1001b49a00c00284201c2d0f84480e0000d440d9071059510404840c0e170380622003042c1d412201903031010b070022885103403100d50700c0198046190444c8152030100346846404280c28045000b11082d42d02e8415002e8410150404200c038041001040c24408d03008052401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 743982392 1250 743981142 743981177
    0x70e0402030c0f22050303030402060a03051008070f0806010b0901020a24090c05030609010c0e0f0d1719050c0c0d082106210c2808030d0b010219080307 67
    0x14060401846001c1300c082c0c415814420200e030080e00140c0c0300703520501c07c100041e0350f950101c5103100014036020482c0c0d203640341110384100180c1c100400034043c680000c0f5902c2e13403880e080021200d0100860750181d984841d12800703445500d0b106030051300805220000701d185200e1500350842000a04403174050540705803421503100038001c0302c000390701d18000c2002d031604000c0b0741e800501c510700800020105102c041c083e10802894030b406000d44540c0000360341c2d1101001001d90ba040b101c003004090740d484020b40746900c091009502a0582500000f0f0a07110710155815146090011f06018980c90308005825801d90740c00c40703124170108804105646840181c500c500354000781d05903103050081c01c00c41c46003010409100441000d0402e515083c0002942102c801801e6849903245103002002124403c02d004841400c40e4422800041d88400000280382240820f101003021040c039100480e11000100008016024561821341c082048100210b41103000c0c0c0c200380540c05000c8842 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 743983642 1250 743982392 743982397
    0x31e010e01031202030307020d0e030106050a080105040c08072114011e06060f0c15061a070303060506161103010608070303170a05010e0412030b0607050d0e010206070e0402030c0f 79
    0xc25003640480004008006001e103819601c0710440c0042c60440c60b105900a41d5a05820604410031680807000724154800398003d001410024240000168550030304c01d01810050764129142e00000e0000030780e500e4045a40002c0e80c5480e5001c0d090001001c00a052a911241003a00c41c5e0255801d003000855003486050b84242d4000000440071400f09510b6084030300540c060380c02d018130348001c0c1080550101c0c80c1090356511aa042000301c00300c401030402002d050704a841914120110910030112500240c581c0c1c0b8481d40d03040c03004940f00d60900205014825500c00714001c00000c25001030301c914401021044003600028030315030713200c19142c6001c00952060300803a102c120301e080c1720048201140c0d07005000c3d6205115651500c0701040449a000700040d00401c089505a078096219400511a0003002000c8c00d403203050b0780c1440c5450391100241003010a000c803141840300c0d40003240c0c1c140704000a0310345100c2c1c40015070601020b07500041c007000c42250200a10402c0c040c04030701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 743984892 1250 743983642 743983649
    0xa1709040c120c050405130e010e030f070c060e060d051503060106050408011805070e0703110409020408010c110309121006030302030a021e030915070b07050c012f031e01 75
    0x2103480160040590070001c4494003118003081004c200300901171500c640201a03600e6494450009600c1120ba103024014078004010707246500000543c4007803030400b41e016180540c000c214524036556200010380d41c444400007096040107080c801c4914040c40c43c0d1005501100e440001d101d2000c80400203410160241c0000000c5900070605102c3e9010900c242c1e80303500c404002c1003506080d6511034540e100a03500c10000049884000038500707500c40d03004260b03a801581c000c2911141c1b80c0a01e00040d41250180380e01540c82d018a15030074501c21214102e0b4040e05c8409180340504000500014020901050352980301d400c060f0b040074181403040784001d6000354080c58031221021002410312600c2e0070700d084924421002815210004411100000c80481e1604440181585d5410303950145080c050852440001080107040d0420010140d03009418000c100031500713400c0700340c1c000901a600d03800c02c1460070900e0054080000046170046c030581c00c6420129000c810040c2003250980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 743986142 1250 743984892 743984897
    0x3100510091103010b070c09020d0209040c020a02240405121e06100905060d05010f0f05010518060f03011506020a110a0b03070c08040801090605040b0a09050a1709040c 74
    0x3004a1051038a24080c054078010900340056080000b09420501042c0690183c0000000c3c9040803c07140d17808440c018000520195200c81025105100075040000c02c14041c030b040c03c00320140b251012818000f100d43c003c24980383c0011894a40140c07603081c01300c10840380010003003c101d95440d45064211020309034010b09154480e6941c06501080103c80d1140e43c0c2d01c100c062140542d01c9041c0d03003090341d555080008681d580e040001e9201008218060400d503e4802e02c40e0060400d40c000700480b00310140140404d0366a902802155450503480b04c0d041e00c42c0300d001c01c0e038901d040841101c103c10010700200f8802400c01032540ca1303400d154054001342c0e000d03a00c0c003020032110640c4c8a500500845102030a42d14024038540f482c40001e086071308008a0398078050400a04400b0740d00948178400003000043c140349845401018291810b4840015100009200602c0c0380140301ca6503a010000e040701304029560800c00200310784c8100d860303c00c18030400c059522644074403100030700d495 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 743987392 1250 743986142 743986151
    0x613060b03071e060504060f0c0302070e01171216020607020423041a0c07060902030f03130608090307020a050d060209041a041a0307050f0111060a06151106040f110310 74
    0x40742000b140066a101340e09100090104001c6039401400808031205141006505802c6034901241048916081244050b10003000412190106600c015180f100c0c2411a0242d10030811075603030fa400342501c2e07580f50343c0d00c0f614200014107081c0c0c080c0a50610290000c2030071414070380310350f0304403600d50094100780b4042403c11040c421300c509050354141700300000d5241420642c0403800184150100544200d4407502d070b904c2107440811000c0076241c008130030b40f91102ca001805120030b0001d80f00d07620001e50030b880800e4040c2c0002c401c8440d4594001d01c01191790340703440d05204400560002c2510810350901410034561030b6801072202841c181140080445000410072080301c850303140c0542121156620301c000340d10b00181000580c1c00c100c0301c040c490019000100c0f061000d10403501d0603409101c081c0b01c0003402542000b000d441410301900b031031202c101c800b2518040360ba4043c66403640f02002080c00720ba140001a05400e0040354410101001500800e19000201d00e041c415a07584 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 743988642 1250 743987392 743987429
    0x21090f1505010302091b1b03180a0e0f18030a0507020901091a010819020408060609011e0e0a110c060a0e0304030309030b060109080d020d0f08090613060b0307 70
    0xc24609101034144600411495045402084803640000e16540704d43d00e0030064040180103050a841d5001d1131042100c4400d050004c50035100c2c2c010700000000d1030310034500440b141c80e0003c9043c00f9501c4040d81400381c2d5480030f00600049101910720701d10f449000200700c07000c090900080002440d00e45840c1d80c3c0d0310302841403008007041680321003c2c036803828800e2401009401900590190246444051a00c0300807200c10b5000d501840402c10301c2c0b0004000400d100c0c042041442600200d441032103580c0d880140d282001c04060040241034640700051000300140d44d5031307a401142c4450700082c1c2c009200116a06d503800401e485405070702c44803c0204a07d4103000344035031390403480061400d26241da03502410441090000801c543c100c04000b8501d64442d0301e1904c001c045403012a4410b801d03045001c0d4940079004010400503450801c1ea0f140c40d405801814004d10400c0020865551542c1003007040341c1011104803106070711503406044c141d038108082d80203000384d1074421444401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 743989892 1250 743988642 743988653
    0x13080a0c0e15130b04021b010b1003050f0112052e0509030c0c060f090d0317071b14120301080714030a11090a09021507030201140c0a21090f 62
    0x24000e0841c0c10b045600d0303204000c01d03100c100c0e0f0281041960320f00480c00a000c0f500141c0030780510086500500c540b11070f44610101c0c150062064180180c800004044201404a094400403115260741c0d41c504401088078410308484600f0700360040301a20348072400c07804400780150601904482c40081190076241c411510b01c01d00b504440d8030300007035240402080c10261a022100510391044801094180a01c0700300003c4540e4010001c4c9162282130252401810180d00704d0001c444a03405580042c407a02e005120144841c080e00d02304000c04c83d626a00c92204003064500070003070340500d080c1101c2c2480c0700009540038100724009014014100355864002c5109042260322a80c449401031020403d07162860f0310358401560411b645030703a1b81c94014064440410029000440700c0d030072202c0c00602c035002d000424469402404140c1052403081210b90042c0c0b0141c0041c3c2c001c010448007240101c0d01c0b680801145c000345000d0841956001084401180c0240c40c02030801c280c4a08202 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 743991142 1250 743989892 743989919
    0xc070b1306050a1b0207180b010909090b16030603050319020307051b0102100519020c030438030708061908010501260303090604030e060405060310030b06040207110613080a0c 77
    0x41307520080c50120300c0c1508048400e00c2401c0742d00b420076541c106401460344540c1005000d03210100c1c2c10b000c00307111803074100d811840450700170020040010040d0740245c801d0091000301c81d041750045040c510b04580002d020b04d120039810040d4071040143e00c0001d64284a04202d1a10a26845682e2000720b0006820680c1c00900310700e45a00c0c00307081142400c0c4e29024200052040f1400686035900b03081d1407880c602c110382084211011143e10200d4072542d000840710b00080c003086e14aa64107e03450400010700081c1c44036404640440001412420f0418012021000c1c1c0400e00816a0f03480007480e0844e2000e80004010f007941d20000030b0103100a00914001c81e017038030000c500d0743ca00b200c0301580718940039000400f002a440c503403140c541c0e2014103403000780c5001401c00360349003009030999011b840984800c827200c1c03101c4000140203261902c01c0d541c607550030001148251660104101140d4015007041c502c1b5500c0c20300104814408004003052540f1903d0224400b40c28000309000c1e01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 743992392 1250 743991142 743991191
    0xa17070e130c1103131a071401022a0a0f06020f0403140c0d0b0c13330906050703031104081e0c0a031a0403120c0302210c070b1306050a 60
    0x50b8000c100042200401d05141c100302c80034805142c000040c0c050490000784114a0090f08023074100103c801c042d4810b6006240e43c4804854111000b403400c02c1070524170f1074071081e0403111340006182c100415034038440c045009100c0c940c0146881c42444185010790090740060700c81d18441c840f0110b03140010042c0e8005000e04503004140f01c4107554036021004e10042280e52401300101d002c000c0101c940703880e00098007170001d06d510700704942041031303a14050b27079450f6001500600001c50070041c0202c80c40c0d402e6968964442d403501000f503d0a40203015401010501c1a03410000052901c4007800b40b01d0181c0e03c800010701c1c5803901004290315160860881c107201d031280c075508200054130610840511785440988110310743d11070900323544540c41110004005c0381420707403068015074594000e084104030800c0c20011440642e07008906014115074003045807034100b04450114146c60881603118503d030000e03407440d04082d81d0b0001611816100340d2000350f1100c0802045c0540b039081c40806 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 743993642 1250 743992392 743992427
    0xf0209030a1707050703060e06100b030106031814061b1312080909100f08120702060f0c030d1a0105120720060423030a17070e130c 58
    0x9220a4100090300e400c0c080300010300c501c0c4a42c08014401c08003905983e501c64101058841d010b07501c0c00c2441c003804103ca10b18566020f9680080d142c0c01d1011803282c15540d116000a080da03007001c009400600c40c1000704c0188a00c03060724640001d003c00034212102d6800400751a21707050155010500600190300c048200c1010700480040850458980d4219041505804510107a03428019014424820256041541d84003004040b42002e21380c0b10032102e00c22112114603035034a11950300e0700b54010030030080d0482084044050700d0b01401401e0011201c0546c40e11700080d14500c6803840d800700b01140003081d240e40480c0f01d55030020840307101140c400e0815503d40340c1c81504104243c04020150018042000964070106081038445401c02003400112006818136081c40c0784040c840d2955070b11000b941d0114804848004070a40d40e48040c0ca0f2207048010003100050201100e00804a50420542c0c118415103540e540701d00d1020705a0141c40050140c884c010020040c5441e400300100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 743994892 1250 743993642 743993647
    0xa080c011104031a0403030e0d08040312060f050f012f070e01081e1603150b01030b0102102301031a0f06060d02071104020c1c0f0504180f1b02010f02 66
    0x8104011045544104c40c4a0302c40c0d019a03440c83c0540003412284442c1381c1902c1500481015241c0009a25020728001d0f00c4910001c0c61031044101950101d0081000011a02c2400c0141e42460b03156440700e8101410503540c02100b161080445080760240c944801d41c0c600780c4030108910074018000039207010651041958107140d140c17a658614403503d00601c219115110100302d40c02d00c0070b0090301c00b40b4400c030080c2581e00c0c248011300000c2c3ea040e64108628081c3c3ca01c80d60340c0244070342044c00d00181c01070100542501e548000526200da1003c24082451044803002001e054129018620840359103105074036109094140c1c500040c400103091545000303202c070a540380401d40e0300381107103200d02603a00d018919110200c8494064842e800500104000100c5030f000320b4003c00c0803102202c90b04c41e81a041d03c00b00d1710410409840740205904100c2448040049400040d12981c800c4002c560701d032901924004449106a40c007945140c8000405841a070a021f461000602c4031001c3d0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 743996142 1250 743994892 743994899
    0x703110a15080a060b0a02240708011e050a0308030a05160905270a090b070f2a1b080705030606030c0d0215030405011505010807020c010e120a080c011104 68
    0x307070620918411102072140090005041c030050340c0204014000c1001529140d12030f800300a5502c2000c03405004991030282c422209121610b800301d445024141c0d43da4139689d00e42050700d40540d0840000b1020208004801b003441d44800e10b205004612a80c83c0030780d80d180a40d1208100c3d00c0141140380005002c00400548662203d00c000a44400700d4101880c00c04007405201d00d040e50b1201542820110300810030700d407400d0790003038080d0740c0140c41120842c1d60703136402110310758003080140c804a500c80305400090f031154480c5545980354012400c6204940340c4450489000c100d01d0000d0250f6540c0e800d000d141414000c520041a059001388120b00b4010002900c40102440b1180600880400e8a00359603034000d0307215100304441c0000360390b07090034200503001c1c2408028500c0c8080b0000c07030024141d4400c0e2a07075481104550702402c4c41984d18801110107180b09a1001d51145611001000d404028803201c0000e40c82880f2035980d0b42501c0781c003603003500d80c03d000d4071843c14400e12040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 743997392 1250 743996142 743996159
    0x1418190e161707080609031905071a340e010e0901090e030412050703050601140f0f0f13060e09030301242a020a0506041a07050307050607020703110a 66
    0x11025290101442c000841d80003500c0c074502021a0701a420611072501032003100200403000340784030001d00d04d085a10300560380d0165018031403844010454448605d0306007060b040001c85580102509940503903d03429400600040e600684c405400e203c00e8462101480e1b0b00705c84a00c84d840c80c02c0c2010606680c0c3d00000030f0021105105424225852708001d50000500744101c230003922206010000001c43e600303210303540b640a40000c852031300c582000410099a43c11004220b504c004003003010b000040b1090140d512480341215070480b0020800b1080d40d074441207402038504601200190591421492443c04100502103000c036400400041c0f05034541482c112550008c40c041c1c0c0101841c1c9030a04a825000901040b4445240d452401c010b0120080c96500c0c1140212650541c00751240f0801c4010b110700e2159104100b0f41c169070485c1d540344540603021550080c001d0f1381c24004da030b803982c0d410100c0448525006812025041c0300308980c1170910075030840c041d2980c68420b0300b00981d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 743998642 1250 743997392 743997433
    0x1205010e09030d050406061d0a0c02070515090f150c010f0207020904120c020907050a020c0f030705040903090b0c0a020a0e0f0a0908210a0c0e0a1418190e 68
    0x1803444a454900017424803403d50000b40003460008900341d51048403070818402c05001f924a404c9250602d404940040d20008410055031001800320840710a01500748206600100d41150424052051400e1a50b40d511480311003800c001c180301d503602d802c468a6401c4075102c40311200058814805040562100c84400d507000394401d12050540300311080c00d03190f0142e03450009500045200420400b9a800070207031100600176001c490212020404104c685809140310603015070140340200440c0c83c180d001500d8450082c1003081d4102d44030600c000b8560300991b41e0781c00c3c80c0d02c200700c604114140f007a101001048902490051810032a5032050780c04409010895000c0d1030b0a108014000e01c07004a0b5001e0000c03002c41e680800d581420b0f0110b104086920580303803850b050407101081d01540c5015242c0b00010708144040b410052220b034000345000c0704c01d401c00c10120001c129140c03412041405210100981002a4484180344094034048a4511410b412101d400d200c46e00700d0101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 743999892 1250 743998642 743998657
    0x21c1a011d072304170f12071502041e050d020d020105030c04090608070311030604030507020d1110110c0a050114030c090a030303061509140420121603050702100903140a1205010e0903 81
    0x100c45a0723884003400c01c1200003490006841d0018400140000c40c1d103034240740491074181c0c12a21190302e1382d560b41000038017118030401a400c0b807404d0302c51000540c03040c40103691244090104504054481b4844000c440f10740d00001041d601c00d00c0107009004124008180990702180204450716207035034005e120307004036400240903140c0d20918108100d104411a900d01c10040d203a075410010200004290303080d0f01140d442107014849880d240d90510200681c1a107006842c0e1500e02c0c030302160a0340c042d51000b416081d0004060003283e00c199604000040114000e40d07001c00d0f02400c0112400418005540038010300241881c00c110040c4080000b0f14542780480380000d000a45c40101544d00c2d02c10004000e500d480012a110340803d10359420340140c0c0c4110700c402d1340c1e0440c0d110076011284c0580d61a00542d010300303c800701c010243e400001d49217100e40b0702080c064413400345446050300403102c5072020808254094000c20702c5c0e032168030300600e1440044111414044040c03500c034403c401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 744001142 1250 743999892 743999923
    0xb0d050108160314150f0f010e0c070b06030a1e050601050f0f01081b0316090e0f1b0f120a0e0a120c02060403021c1a011d072304170f 59
    0x281c1c101e04903005000055510302d6030b01c1d800049280c5410096105003003120510031f5286004000f103086104540e81d00c2c800c18040e086246410310680b1860400b080040c1460342c544030b03101d500c0c4009090782016140c0a442d004003558800340380c1ca001403c0080c142c00560044030f10340c4941c0d17100e0369040f9113801003403004c0c00e00c484c80740c42e8045024000300c0080d84101c075800d000001e10003490880e03088110074070310340d9a0b02035030701c0e803240b0108e071200e517090720302401c6100c0d41e4021800b1010a00448242c4a9070000820b10b000700464002034150007010880200311020010442500b17524040c892450035400b02400548910b503840c1201440390740c02c500104003083d40c00e80c0c21921a10200da003c0c5400508020000780c01440300c090b01031034910219030705428681220903225102d40d40c58141c0f0003061040d1607282c1609090001510000c046108003c001802e400900002c850380110407403091184550f40c900b80110101c50300c0500503518a0f0354044003540303109000c00724a14040000c0300c1e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 744002392 1250 744001142 744001163
    0x6020d020c0411122a04050a0e1305010f020d180f080a031d1011130e040204021c0903020d020d02060a0c030204170303010e0c0a021903180b0d0501081603 68
    0x101400f0301a030050030602401400210306110250fa2116900410203000d10385610100310041030000b942e021303a100306c80c0c000c100a64140078501c000c544159102101c0d19a00e0b2035000d403511590300b5500310664055200b83d0001d0300030714558040c0130350182600250480762440c00c9030703550002c56100c41a0064011480460a00650361183e003003120354201e104010011200d0190b095625502d805804407040c904d000c1d16242ca501259080d200c500c0e40352055101d800317107024500034071804011310403607106a080010b900c081521000010001c01042c0001030100d0181c50040d2806100340400020b6500400036016019030018406500c0110f5190101d0395142200090f00030380a140c03c03070302e0385510541120403a00000400385d8101c0d04a04039084035526000042540c5110303079a001c02c010703001204c451188003980b0004221040c8240340c184214480c04502c2078000300e0310740041d280003030001620101d0341118012640509550000703000c0e05400b42920710705c8185288002000b84214 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 744003642 1250 744002392 744002411
    0x30b01020a0b0621010e010b01090503070b0c01022104061116021219120216060c08181e01080a0501080703021c0816200102030906091201021207020706020d020c04 72
    0x71031601075130b07000106521444088030807285601070000d0788107881640d0702e00101d80d202503114040620403100f018000d4001281865440348a5500510220300e01e913400b000a55241d40c0b10100c1108200c000343e480300080c2c04c061400c0416540d41c48045c201009082c0410b2a4291003201c011019550454010b0003200c0c44000341420071002905403442079444c0320707503d030600c1800000c9d8000c560050f0709481d001d0101840c5405940c0b0940603050016400e20a10b03000210030000800c03072900700d4078401c0d80988480c0001025204200c0a80300101c40f0b40141000558001803095000300e0b61a100b80710560418511035a107030400e00c0302920030403110f10340d07540d03c1c68401009030301d498111240c0f0350740c2c0c480f0203c00b444021724090100ea05980c24000c8880000c0f503401320b0507034644142c3c00b451070180f03a1401c000303103038000d124041e81c00400016004494802440181070384404070b0340c11040d501c0d1280c4060f04098065100e83e00350340106007a081d002d6804244a141c10200302e8000861840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 744004892 1250 744003642 744003649
    0x201081503101b140703020307030f050d0c050a0e010503011809032d110604121d090109060f0509010b03460c14031302060705060703050a0b01030b01020a0b06 70
    0x1c941041d0701e440b85081507801c1101001114412200c0d0f0316203031000d0305000300741c102c4034611401401a00680003171041000003480780d00001001c81d540d00d480c5051050400102e02204c0850642ca800301d40001115020217402215400d814035090802d1421580750505020701c8171140c0700c4607410640c1d146541020140503800384107072001001c10642c014146d04070307040714100c2d001200001050607044501c140c4140022200e100e264010200000d400c81220241d41c00c011032141e8500701c0031074181d00303c0c10781c0b91b45e00000e00030a119440172071820300c1d0600b040c2c12a0001c0d003009001c0c0e008400140902c1185a0441c2e8001998008250500040c0c6c81a221881c004a00c03a038032400702d20300419a1401251030380d01c841c2c1c1e0a0b0004022491003070109a819030703c00402041d031984180000384041020300d00c844001e0740050140c03407600c00d41c0c3c0c0d540c40c2010f03400c84005000c6640ca205005514580e4800c1c0213038040282020014110341c02c0002c1c0d92540846c000409151070000001d0b800c0c0c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 744006142 1250 744004892 744004903
    0xa080d0e0423190618050916030f02010206010e060303071209080d08060405130c0b0a09050406060201140718061817160501140d051003060e0f0c03070e0c0c030405060a0c030e0d0201081503 83
    0x700d079071740808140e0b220300e0080a0260512b5060340180f10b07241c00440c4541d090218140a110000c004500d0b0505642d41c5030369402488241d10113100ca100000501100300307101d030418080207541c07404610300d0b107081000304891002e803040320201803c851440020f104024a50191140c03220384a4494065180c111030481c1190082d44c1c100c0e0901c03000044460301500003040740020b2a14070251513030b40520859900c1d000041d0b031260051100420842c01e4007540c9040c0b218001a50b851003050344a01004400a5058400341c50341e6005060114040d4032001c9840080c02d02440c056614144840b2107820038051036410301d108031303690300100d81c4c000e0310b042d0350500550f48000184200c145d1a01225250403100840054502541c911b186080c940465420181e5041c0c090500b4540c69106030040785410690403a0328900c010480869107a442c400680180c0856036a10050f0700c0c210b1800603c441b0448441034005c021140400740142c2c1c001c0d50b207603030006000c1e906a004d9400000002d03d0324 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 744007392 1250 744006142 744006163
    0x12180303040b0c010c2309011103130f0609230301090f0b0118050408040306050709080a0b040c06030203070212090d02130b0f0a080d0e04231906180509 67
    0x500c00080c00246072500500039001e10f801da1002003184018111080d00d01c46940c940046005001030f51a205d81c0d40d0900161016000624080096443d030315200c40c95a440804003419617071007030030b0820000000d000903402a1074a49003501e15249046c2003265016013000c000075461b0643c0e503054074180c600b5881806041e400c1000c034007030758400d400e120940d4002030060342840103414a5000c00c09070140a032a000eaa4042d40070b0343fa081c030355100c00c0014030020b0b1118040242988000496100804c000c0655501a080440050500d0f00d86a01c00000c2c99211005050040c410421050340208002d004030059402442d59003020340c00185004143d55030007544000c400d0302c822045800c1e5032008624060076603d902e8400591010084030b91441e210304070301580a0303480321441714070550303481e4191070010344042aa040c2102007041030244c00010f0b0300c5003d4481081250101d0a0300c0d40001c0300d55003050801007141400e02c101c1402140e00c007005140368441c400f1410a020411004914 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 744008642 1250 744007392 744007399
    0x3040e07050c06040c0e0106030e0a08130f0b12070318030c140d120f14040f08160602180118031704090c090e0703050c0d0b1f0c0218091218 62
    0x1345080d1801e51010040c03805040d11030442e410000c15103030f02030310420200c05840401480c03000c219035541c0e101c5038031038801919130440034180003803118800e06903c0e000d00b072600c0915441c0d582084003045940c01c010803140c01c26082844003070280c1c0781d415202560b80d42500d010344c0103208604120200ba01a100400c24603c68130981880d03466109078810403003240703001c0074441c044020002600342c60340700440d0f800700e80c950b0000c0350000f10428580103d0610400c6014100039042040c40d994920f0310500b55603050300040c2c40c440000d12000d10340c4200000342800f1030409000f00e00d400d007030039440c080200480b071580c00106811401c0b00940b070041c02501414450a50168002405400350b84124604900000042030342240203003d624481c41e0f81d1a4001d090100c0c01440c1d1000e0300c0c9403070549402010f15203100130f8400032140b09002c4a1016290010088400d01c14480b40c00030490b0708000c111115818807400c200c0200f0801d810074104083c20740c9406d03e0b08007803405140c03421900d961 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 744009892 1250 744008642 744008653
    0x3010b030106230a090f080a03020322030602040f260d0c05100509030c0d03020a021903170a0e0f03040506070209090f0d0228030c08130315060302150c03040e07050c 73
    0x1c0f040e80b261461046c5c844117441130b41c4450303640e04207680e280c202d041e006016810520680c1c11100c1c1e1850f003c100b04102c0000707141640d80e43e4682d48100c0e400f5070000510b40b145001300f444922035058450407881c003002841e0000c00700503820140c45490191155003000024a0000148042046800340032400c00b0b00c10083c9050415a05a6941c0130840550a0f800360802d0411094003d102b41c480740d40154000e4030610011100394a0b00391100e290840500c4012840a1400041000082c0c810341c428a03000a10340300f4002e0b45890840b0710941e07520f8980c0104018441a00c1c1c82060700e54460341a103000c406505e0703223901541455030301a01071103144201c0000748800d541c00196036071503802c94003c1c901000d070103290382149100d0416024000c5000402c008000401810051078082c0c26031108595050b03d0781c0d03a00d40700e144901c44032080103445034007d009501d001c0c02e00c04102000d860382c807490440040700c510b0300c0f0302484c030403000c00031781580c00510500e005504554603101217109940 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 744011142 1250 744009892 744009907
    0x150109052d0a0b06030f01050108040201031e0c02010b0607031403040812150f0a140d080f0708090405010905060a120305210a06063f140a1103010b03010623 69
    0x280303a5204660b4005807604200702d69205040541c02c881c00369408810782c600a03030810005407408100a04201e041558420b0944031b5400130f5003800c0307010b60300c9003004603210342203500090030f66014101580c810308041161a0000c6c1c0c00c010007146c028400058a903d990712400c00011a000300d1042c12191044081003101002e07400000d030038070b0002240c0880b5a11407030002c5c0040e002c0d850103810f61498648041208600d024100070300d8542c03242201600d050103c0d80c09a4054005010490703400e070000c141030085103454000c6070701511101c001004185405030000d0300040e0346100712011500e0002d4000c00b494400c40442c0c1c40c45000c4400d0742c0340c5040071218842140e0049403901d560503c1d1007000300c0c3d1756104140081c00c0b003503105440c41040742c1c12980b0340440f50003480100b400c49052100314444185038011f0500c0004070110130a035501d0240001e10035110340340414400f41030200b0060003c510380b001980e055481c1807402c6501585070220f004141c500d80b80759030750016004900107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 744012392 1250 744011142 744011221
    0x30307050703150501030b06190816170c01021c020313030b0402132a110d0207080601060201150311030109020904060e0d181a040e0712060815010905 66
    0x301c003201c3c42403601203c3c0e50154640300003107410a00000f080041c945e0040b4046142021034001d490801b9a1400c000c1503581005900d403144007050315040b104444410050401030f0a6844a0601c44070003400e019407900c0c000035280c001420100710014012203030000144c0c820000d80c1c030400b0b0070038030281c000707603c0c0e04120030140b0048404902c6102030750220840000d546c01800740d849841c2100102030014509100402100c650104041090b20303801e80800402c100507083c100e05544d0094501242000c0f0001d0501d10140c015405580c1000b00c01c1411140c1181d000c400c50f508038280c4040c41c0721000c0005d001d020b58001c0a51b00600c1c820601c020b1140d075506c10340e299485030b001c5031700c10298407106668002004a8080085842ca6003c000148120303001c887c590618407000c40c80e16465038060411200c0030f60310040042c1001c81c601c61704007840d21890b0064844034005040122800c2c0c50409030b0b080500501401e1070310707400492440100f040c100303036410310b10003040804412001d03580c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 744013642 1250 744012392 744012403
    0x4050c091312080a0e01140103021e0406030b04060c090305120d0216030f0207140603061530060a0e191506030209100c02030a0f0f02130b0f010206220c0503030705 72
    0x9801060f203484000c0300702c4901485101d040030314801240e00b0b02e80c0327503800700080e00740d00108a200110080415824544c1c4a00c102e40146108680444240c00e0a0521904076030503000c28105200c5100000e00c007240002444401c06071071090f1312550784404042e580068000d402451070348507000c4140700f04040d0440b1180c002d1403441e0303086030080f90780c4001c0c214020980d0460190051800c0020408a0425400805401c401100380a10340b070030203030402611505255070104200032004098410140030801560400001c40c0c1464000d0305201c0700f070f0f80303965020f4910701c000d0400309801c8602400c29040102e11840107444100c0e6a40d03611001b80107035000d111214400d90841c44e036213519502461b402c0030130325005001130503044c103282e40c1c03003100401b070076030a9511352500554100140d0700c0b42e03e5008901504c00c4041113030000f0400703005240101019950640d00600c0400000c0190b002d000d507103540c600381a94403e4500350810111500310f135003229806000005240741400b000044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 744014892 1250 744013642 744013651
    0x30c0303050a020307120209041803080421120e120a050d0b030106061e090b04140f030c01021b010c12020c011d0105041208190e01020d02010504050c09131208 70
    0x8003405142d0b20100280100d00c0200c820001007440c00018624032803986d4054002d80d075000d04000ac2d1411200f6600e001c0c003400c032108400140c0300104000400c102c0340c4c0307800c0701082a1114810750a0020502506480c42c10b00078100711641c400850072486010000062489140e48400b03079551501d41004015501c802642d010350b03810000c20603400d080520800e422101e80d81d07582001c82c0c0405c01c4200c0c400c445100e1180400c9018800841c00000d00f030300034001004903c1912081c61006000d2114400034804e00e103203e0703040036802981e10398010480c00710102c202084070350a0081e0381c00507501e5000c802e4000c1e02c8072417910b4801e9580e42d0001800d80b00c60000340c03501c00c07501c9282011944540a0001c5c1c0d140007a40c284002c1110109503030001910a1103400c849040034050f0407840c0d40d0a254800002c001841840c126406503010701003001e030030103540b009000703600d010b1302c0d0301d076031200c01c0d006043c000c011003c009a400801e4000002407264849040f1191072000900101002e0b420788 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 744016142 1250 744014892 744014897
    0x61b030b0f030c060d051905070f0908150c0c030d110702190b0d050a0608030d0b1018050d02040b031504050d090305300a081806060d11030a0609030c03 67
    0x44070850245800680c00e00f40346802000c143c07410b0341d010301800c0135001c05495a0012600011024403032216802681e108000d2651031b41c5407890b80d41802841900c0030b611003901500010403045400e642c128660b988403510030095940c903180454614070b0740c880c003003044045a01d003c0300115001c1d9400c00800e203060080390b80c414071b5400c40210405030a828440c1c8140080200011461b8840b5500082c1c0c4c09003090360001840e581e181e01c03031420766110100840c03078103603204101100c8e8a0308040040210700e0900d04001900400c80e080c2c01a109c05000e024454940f600780041196142e8222010b820340140507641d031000d00f010842e05039101130b83e0848035800b4076100e00560a214050450441c0e8020005102603605800820102104084200c40c555040298003030904007140041500301072541d55243da0349448005107514401600d04100c098100c0428030903555a10400d8501c002d07040346109071202c0044e00041e2420b96120b4000b8030307440c2003402c3e80d81855004000512214084d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 744017392 1250 744016142 744016159
    0x1809020c0f0d02060a0510150521010b0412110a170c010c03080f060a030c080d021908030f0a0b040504030c02090a060521030c070807050102070f0506070807061b030b 73
    0x2401e4031078807503000310a40c0c00107a03c04000959210b030981c01c49034110070003020442c0303a10b440d030781c6002d600c0782801c0c00d440108000040c04004003003000450003400851503008105941008684801071240748642c4140c044119080c00900c40241c10f680388480c401400780032001d42d038480f402c0342c0e87d508040d0503116008034008180075501400f2840b08041d8160358000c9141c0c1d460120150982028008a03040403070381002100040300d01c00c45802503d008001003101040700b800c02031401c10b0b1102551408215026070b000016406405c0c3d90304a014103580c1c241c0307035a400d40d0410040141012041d80a407c010910003859004030350b100c031090007030325500c1181e51500d0403d42a40c07540e100e45a04815074202481808402203040e00d1100d190038282c0c1d1500c824068414035141c50f80e04a101c07190000d542c20445580c041200e41c00a0901015110007540792a00003121801002d4016107206000500a81003040caa80303c505c00f2380c810f02802d0703a900a8820014014004001d00030b014400c44c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 744018642 1250 744017392 744017413
    0xd1a04030e09090a0c0504051503010e0304050f01021c0f0c081912090209042d060507110d120b0604092f0c0604021003150806040507140d02101809020c 67
    0x10941d148055000b12605400501d41010701002340b4006201e00302000c550780c8e00e02d146a4080c001d044000d4401c4004580741c900304800c00c5a0b0491300b00304541035520005014805d0840300510800091080c2829403054407006402c0d21300401e04d12000301142000601041007500d801000030b40c000040c2d80341a81200c400d01c1c0d10f0112640600040d40c488410710010300045c0101e94900c50b110b0403e8084040c0340b18658085103241c04010f0122003040d1543c1c01c000e00103902140c4000c58107c880018001c41300840406030040b44d602100c2074140c2d40b40c40c0503100740e81340d41c42128000c2002240c10400040d5880080d03c40742c20261441600e4600c4408201c0d210001c0c8003a00e00460001001d0260754940d43d00704103a424141034503030b09060301e905c0b4182c61800c0c1080321200900383d0102414540c81d1518125040c0000c41e04080440b61088824401a80301ca1001d03a411581c1602c80901a0b41d48420039100301c40301c070001ca69461503c0c840810364204640250228540c2101241c0c0300c11503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 744019892 1250 744018642 744018661
    0x3010f090e0c100e0a030605150301093f0e040c1e050717040612050c031302090405010906020f040306060803090105032406031e060a03110d1a04030e09 67
    0x40c20194540d01e94080e6412641500d0f20042c04400075559051070207030b0108241c0442c026150951090354042d58500402042c85441e81c04984002d504a00030040b100311592542c610106915035602134100100320604003c034907890780322450055512a692124000030000d01c0c0502c039258282c00345040540e2580607901440001d15050002d0714040c1c400749291034120b51940100e0390a50b8071240c0c190142030390301100402403000e0249961007613a03000002002c0d500347ca401401c5c0600f01c0004108001d4120407030840d00032401e904681d81101d544843c10514090801740001038142440096040f03401c61690004004491184909022055480c04e0041e280d000303104009000c501c0c10000074011490152030042c0c40000701c621050307510640317800300d030041d00100e81c5016400880041ca00c0c002d0076103884164000800c4600ea0041421a5944a40b00d681380c0c801030b001e029034504940030440499400c4c121030040040015052506080041001480340c0c10709020b9199480401c01158 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 744021142 1250 744019892 744019901
    0x1e06091e020321040b131208070b18030403023d020d031a090405121305090c0703120c170f01290306060d060312120501060e1804061103010b03010f09 66
    0x10f100c00380c500f802e16003803002c1625480701101220049079001d010601c1d080c3c0c080b1b0000d285008216681d1a0655490040207030701000e020300900b008000c14030f0700101400000ca409a80e410b4500c1e2080303200c441c2c11460524400196070700d082941c40c2c0400214192101800c0480b2019800c40e251070f0340b0f0171004d0b02181e407241440a01114503070011030007814208019a0414498000c80d02c00c030b9864a00a1955003001c040c100a41100c09820051460082e0362640c011050141c41c070310b041d560b5600540003c884400310204d6907241d02c1441051409400700c04608210498080d03540e1400000e040c0082c070003402480c2944030002c0448001c4540c0c3d80d44c0050b4807200d018041d241d0b485000030406a600700c0c9180c0001283c0352000400000c2c980c00900607403030010344451000402c0440b440f41030f510b058110404119241090110542e2140b0000078024182c00700704803581c41e5424048040d00421010310311411002000043c008940b50045040307404039840c0c401066180c041c0b00702900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 744022392 1250 744021142 744021193
    0x61b1602281e050d0203030903031b1002040b1602061614060a0225061517010b090c0403020108040c050301050c030403021006031101080711010f0b040e0a1e06091e0203 74
    0x3906540b50922007804d021990311400d0f40010101c1e410903100e100080d05d0f40c0d001e041e0a6008449000d03600c00340d01d03000c00c11041445018802981841e00f004a035850601440310290000e12030420f0307603410b541341c0a00320785c0c0070001e03011800d01c1c10040342408940c8210030740c04100148902c500085d142c241d81c0c801c1c1c4401da402c56046194070210118201860050300710140d605990b03500c0465075014000c0c1409004100543c900c002c00500c5580e85800c441c00d4030179890203950040c041100701c043d0507040354141d82d0309003440d49180c1c6031130500c401a003226401c00381e00f40d0319240074400303440c2c43d00003e148070301c2c030a900f03c4000d10100e01482041e18880d100060140790012819000ca42c000c091155000301e840c03500c0103c00a07920150350030350314040c143d001038560740d003038012441c2803a0040280030070701c0740d00500407100150303510008101c21110503168007084c1c10204007005100c0d04401c401d182c00c90181101170042c21102032954030320b80c03001ca00c0783c0314401800a040303007014115120b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 744023642 1250 744022392 744022439
    0xa05031009022b0b1503010228090f0b0a0e0a060507140304060c080307030b15130806060603011e08060f01181b030b0d2111061b160228 60
    0x40d1180d680890800020380b12512004003c5e400400c1030310240702821088580350344030b0110f0704856030050a00b070b641c148000d0800411000510401d11054000c004541da01d00702c0d959034500501d03040b40d5442c0480c214a0b0700140c0120000f03405540840035219144c0241464849003d80c6c0301110b40d607226038030505000c5140038102c4004a1402c0000d0356200da02805d0200c0c1180c00400010b0300c1640741c06855564003c0030440140301c5442c4a40003018104c071400400c0c4030300385070f030000e030490005100b100020014a00c040c040d03051198409070043c1540000c460385424108541729164009000300d424102c9014200100d03c0058040e007281300d2003040f440b00c03000b46482c0c0704030301400034940313a540c000f4022100440007031001c1c0490101b1411819180c0e00e0701b0110300380280813039a84044401c0313551104051200055194030006070300e00b44c1c890959650f0094013a01480d001001c1d4000e9400022505601c416841c2441e80141000402c00e0070344038030380c4803010050381a03040c4c0311070040d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 744024892 1250 744023642 744023719
    0xe12030405030303100614180409020402160302100f090c031401021e07032d080903090a09090203011d0d030905070b031306060510200703140d020706080c030705090a0503100902 78
    0x2462700306540070120190014101511b40004440075000c04200d5000c01c1740140d11407254516601c6603849460059050104240b1560165449400c1900d000d0f0201401442c0c065190b902440c0e825811210031180c1c0400820031402a48084501500015002d80100700d00c0301f400162030010240030380701041d06210390782014117401000c5800700c00003060504584401c100a490310369804441100400101c500802c443d10107105140c25101c00050440404002c0e9030283d0f94404042100c090035109440c00082182045c207000e841c0c06525401840100750000c18812044511a001c0085500441040c07040c2e40e0b076031060007100641d080001d00011101261600140f4a250b01c280c0302041c0e5000325114181c0704d865108044803003000a441c02c2d8050012425a40d40500c41200201450300b001265031800c02e003400300078400145020100100014201c2c86a69503200c414044d00004e0111100e0300031080a0030001d200c62801a0310408400ca0901606110102810310410844d00e2070700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 744026142 1250 744024892 744024937
    0x1150f0302030708180a080c1b04050108060711010612030801170c0a1e0305010204090212010f3516081912080405490e12030405030303100614 63
    0x1080e45c1000701c1490940904000680487c124201602e54141108040d202e00c0d001d00440300202c0c000b0910720340c00340d4107040040007018400300318254045c030982422094940c1310318005004140c56080000304401d4005001d003415441040c5c0c038140d40c05400d014410702c92046605a4503603142079501c1c1c4c00a4041d4041c0040c1c41a80c8152009114880001c440561030b0f9a40c142a0b0704150400c1a80981c08075404610460b810400c07401446d10302c0035444014102942842e00c5841d820300d0302003c1c011890b014605080c03441091380c40348483e00075a0502410040860b44c00c1600e407041c140588030300585501306210943d01d010846501c10420301220207100710690780000c0040043d540c4d03007c0c10b5400182c440e400c60120100100c101c2d040c0440410030b4064a01c40448410802441811143d11100307583e007003607907003511070411074081e58010704074074807031703246100d140c01198040c0808414030440d13a410b8440c40098038102c4d12040310411005061074240d0280442501ca0000940c4041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 744027392 1250 744026142 744026161
    0xc0b011404060e01080610050108040503040509100e1609170717011e02090306010b0f030a0b15070c0314030724090606140108010f120809040b0901150f0302030708 72
    0x400803050050408a005641d4100c511180f0388240d2240203280c015104010700d0481301e207440c1b03010b4a0242042c0c2010309064071900d54a000c0e60282901800710342000c00c1243e030f03881c42c0402c010a070381004007010740f90405010703051140080103e404281080004244001a42110b00201d00440010140645400010001e0b21001420b51455550760501a00d4a140001400040701d640a10169480100300141807500034141d00192200302c00303011102c1c50010700812a500105a0017000c50341d1080d200005120280d2035010811011000030301404208560405104890058155585954080d6080c64580c81481001030082110b44d622070340c2c030340051018103940300614100090740c00c455074036081120229041f4008100c101e000c0c1a010350381c0f000004e409440d00a0300c58601c58504400b080454203aa00010701c0f0b90800708000106c2d49172030740011400000140f0012655039a05116245110b05c0301d04580028070742c07055403003042d00038000c40e805408503643e5000340e90340b00c0c01e41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 744028642 1250 744027392 744027419
    0x108030309100b0f180106110d0c0609140313050406050f060901050a03111204210203090105070f0209040c030b0c030f28090308150111030702010f120e15070c0b01 72
    0x30103034013400080c0c030303010303c2d445020304411110940a200e542950400038080c24800c2d101000812651080140000c556804601a100143d00140204181d09645842c0c20b2a1006401000143c0300208a00b068a030303150110408a6505803000c20040c0e4462041c00b88101c82d4160030717030304609d04101d54080742d407180e00100818012480c00064000c03040310310300c03455400030a00c01080b85451050006218500004801068120710034203107411305841c01945a001d000303a4641800404100c45081c8088455a80b101680c000d0a05090389414503064820480301d000070380c1c22669000000309000d100344112801908404064425031761400810440500303491168118040d03a0350071001b250001c0d025a0664034403070340307482d110b905d441034680e910150403981c0113040144903000402c00040100407101c0b000d0702881d00044504e08104292483c00000220381030ba00c0c0307800c44013141c032000810360405c414000031017442aa19414000c94007034080601c050b04582c980001003000d800418503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 744029892 1250 744028642 744028661
    0x60e030319291203030114010e0102061302041a03030f0705070b03251115060405150a21020a08010902090601031b0804140d0206040c08010c08010b1606020d02090108010803030910 79
    0x315008044042d00721070b044d90000e030311850442d15102d044908540c1c0011144900d00820301c02041903190011070b80040714445c00380079005651340c03200c215281e4000d40e65070340c07034540143c2140c0e52070803d000220410741c42540705880314010014085100094803007102d02031904c2d6140300010a610701c4078102034403600c041c05000d05c0216100f41500800074403203000048a81350551403945024018442502c2c0018010200e80221a00c60300040d901d8684000c2940d004000c0d0b80a004c0c0c210194100140000d800a5405400786000151840054000e4901c03144241c6140070a5154000103400750b481e0307140503043e15150075030100c15030b51250a4480c1c1c0580503020704964040ca1103201c80c03d00309410b00c010010f07003251080200b8040b41a52800c0108a1702000300103443c846c0200034101c410601401c4d1009000045024550300b268240b040d006420500840d0b46208034011040298800780c001802f04100702c00014180f45c011007517030b2040700300c0b002a12040072507200d8172004025444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 744031142 1250 744029892 744029899
    0x90b0301141f0e030d020f030f07020d020d0503030108010c0e0d0303050603070e011e0b03040f232407031e0903030e010914190201140f07060e03031929 67
    0xb5040c10720003111880c00001c0341502d841e4890410080d20078581060344220b020815580040d00141140c6000002c45800d255281c54068a580d120700c001000c42c8440d0030040d40c0a540d40300d400d000e00c1070101c000e50484105c80002c122850402c00c081d40c13000d001d804107030350003080780300a0344c0820b00135040290700c4a40101621140c07900e507240c90340c680c04281c02010115840d8080031000c0e1075411100c00c0031f091286203c1d4250b1910f075070340380ca040950520003455100c00341c401e04030320601150000004400300003a40c9880110f81d00700d000f94101d24401140785a840c40c081085a4000d214100c0d0365511201c400da5800220014000601a50a400c0301015030703a0b00a148080303401e00c6042141c1d88602c10706640c0034142000c0c24604006810300b50110380003000c20b00010b0b07812441c2c12031144043c4141984610422000d85030380d010b8020040c0040c0d0130109001c00144020000f1442400d55411218100c010381403684211280f5005580794400501c41e015022401116800c40900c40103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 744032392 1250 744031142 744031159
    0x20706021303060f0e01090f02060714190b011401200a0807060507023f161103060c071a0c13060207050f060309030a08090313080a050d090b030114 65
    0x48440000110542c1d02c01d640c40350380c500300100e0070096400303511034941140c2c00078455021680c460160040083d007009220300700014000d0f0801c0b000d1411000322040003801d9400440c00024003050491925008071049800c40d4000f02d042001490248103d10069459030b548000030180d0559910110758211940d00c2110582c1d80081c040000500b0100d1040c24080b6443c1040000a407500400ca92581e460308901748120900807039184130021001c0981c1407810f4112a81d00342080140701d49580b079024031820016800622a5189148400c484150101c23003460382c0c2c03145829201d00407a08020320300d01d20980d51751480d00da00118a500514006100b9281108008060001d080c05510000240e0443c0c8030402c614500300c04030582c0c2c0708090f40d0b6240340d0f290402c011a02c130b2080984060500c406a0041449440100240c40492010009204541e52640c074140d5540c10303004001c4500c3d01c20040c0d1896a24441e00b040000c0f11a4010020704690810203000d0780d040301c4080868121061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 744033642 1250 744032392 744032407
    0x6042901031a03240a060b0d02070201030b04020d020a12020a0905040e100c080a050c070305030f100830120705070f08360102100b040b131d0d0504050402070602 71
    0x40c01310074200c101076000f82c2c8492a414109108070100102400c1103a40f401d001000007613441d60032511030501c8001c0060390740d8081d10058008200000c60310350064408a100e0000c003081c3c1c0d00519030651302d42c4403a410059105400410303841154500c07000114100c00c1041107042c0780d003182e1501c13240c0c002519141c03000112000116000040313101c6c000307400d0341c060101c981402c1c4038080d0040702c1c0740b81043c83c0a1b5030303840c090300d03600c03000d8842c0d001b400e581d4000800d440c0d8495203020140c01c00605450510f902007110190b880d115030880c4401d644e2040301c80f64142c49803822508400701100400361550b540800959441d00f05403810f4a41d626009042d60002e0b11400003000030300b5010000c407619810301c04505480510000c0031408160a0407080b0315582c0e00020801c245082c00300020480b1070800010034090180b800801d5044125500c1c40600045903400c469000d50f0b052443e030000e0b004030001c245c0d54103074800702070000c64820401448203041c2a002000c1950007540050b140c88070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 744034892 1250 744033642 744033649
    0x21060f29070804051c030203190c0c0e010501200705060903190c1a0304211b060506180403091401171302030601090204210c0807060806042901031a 65
    0x44000c88030208005001c0c07081d4600041202400300788507950b45c1680c0c82da5034029540b449208011308188a911581d02a114840c11034120314951281480c4000e940c3e400d026500c42c44207010307090201d2540d240d482d68501030211039541c10300c0030070300501d15030740340c0405d00030160b1003008825014007036000c40150140d05102e01c20041480f440740302098034035020380041c040b001c403003c04800c403108200740000714001c291082d41e4698041640c10700c0c892003d9054460507a040781d07100306440c010401505005281e4012440f880003030f039184006443c0210013000f514070031140103002c2081c50000b4442446140c00c2580e0584041c1888074900319010300c0085807080482e21704080b0034014698804505007407040034014900344a0550809051030316000c00720700d414070b921002800035560b071024030107148202c200410369681540c440d0703a200c000081444100321b0306180920300b403280030302c0c8a01c80c907404000c10024080d2403010507958080110060010a03a10200080c030300301d80c14070f4a0b039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 744036142 1250 744034892 744034897
    0x3e0c120304020f1804200d060b0f040906020d06170304060509040b040f09020f060c070e0a1104080f1504020904141c0c06051006050a05030c120721060f29 68
    0x4040c008013040d0303844d0034940b0001048040303421010803c6002c40304e4185444070101c00c820a5407219021940c50907040c04140c181803c245426030003424020300c038051000c01d03401030445031611001804581c0d164040000111403580f0302403038550040008100180c891005003040000081c000f06114003000b0014081d145c9100510b0b101c2e540c5e500d1074404500e080501414000c00030b90717215003002c4e224021170f80c48184171721070700c680002d401c03002032100c2a140c1d2201c64400c2800d034415450307135150b208207951741d11601d03050b6045115480614480030111207007540700e01d030b0040205e1100e80e65955442c42404507400b91482c0c42c85100303070f0218002d078000550120401d443e5643d8130194068200503050ba0302c0134110303044c00c10f1b084070309106480c2d0143c00c8030560505424401e5032526003c40b200818890291840215803e174000d01c00035a601c490108902d14030b0844950b60340c00d9a14036134046804a00c070b41c01e500c140300c21003001b28001840c0c54488507051013018480389080003000707142d0b99 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 744037392 1250 744036142 744036169
    0x3070b0d0b01030b0303090114070c0e06011101090b07030902180a15050a030f2301060605040e0f0601120c02032b06121205030a3e0c120304020f 64
    0x8000c180324125030014403a582141009103800e00c862074906010171b80701d01c16452003034100007107100c042e202d035842403007151013882c2c1c08188100c0301952030903100d078002c405a800c580050013600c401c0003000c0e0140030304001c00b078000480500586603c401a802045550341c100e0300403164070300008940040040d407521a138075252b4003003040c641c040d4030b40061084c213411040c03090140907010300120b0110980c109680350b00803100c0045144141d2070703849010401c0100c00c0c5c0c9600703210300401c001340c0c41800707071003264045803240c1e24940f0303000c2000209580844050f40010709843d5000c0d00c0080f0398000c1c1204465500513a480c214501104805448a60340101d4481c58121500c80b1400c03801e1103080b0040c0741c1e500c0070302d140d058595103521b00d801c03614170fa000801c4800310100d08a01c00a0f4002a040000029a400f00b5001d05d00d00064490882404481c00c0340c4840f0042c0b501c1848034100c0748a1049000906840c4400e00250101d540000d00145d81040c091501c2d13240544640044039050b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 744038642 1250 744037392 744037409
    0x1926090d030506040606140906070206040303051806161106130603060314010c14030903120a05040b06090c04120c0b07081b0118110f031b0405010e0106051909050307 73
    0xc40d00100c10140076200c01424450140745080801c00c401548941a44503085644c28101d0380c035486400020354034046c81c84003a505c450700003000020950054000c1800041e4012003e01030914101040b1440c002c1e05507440254000e0208080020b00042c010120702400400ca0f40c100b2183c04200364560801d60800c4001c00d507500317414018071003010000041100301d03034001e0102041c000d00c000c002201c00086030b41c50401c0440490468002401039079001e6110342d0400189181607110381d006014191001c4c0c945101e08800314205082c0413046a1069a10f0000b09103018030300114803408640554080e00c01c0e140ea1000810341400500040884900580348141c5030507506000824900c5015081c8141f030b850164400006c1c10030051021803143c1110030001a28900c83c0480d4640e00000700591703240c061100d2450b540104001c25000a00d0151404c2016a807103100f800c11104083c02042d0100b0014403044102035114005c51590000701c1c903000b1411079907040440d16205d05908625107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 744039892 1250 744038642 744038653
    0x602180a05060408030a18180f0e0f030f0a0509100801060f18050d1103250b03010305060402100c0f030201020d2405041503150b1005192609 62
    0x6450085031080203000c04989061070310f4501622955039100b405500000d01580000c2001500001e1b801d08004004d40502c0c00c000c818201d003494014840d010b40c500c2c036603141941402c0e80c5400040e03003a034100c0012005529014907505200031541004141108004041240151649038405644444001502d5180c04c1d94144540605012160a186007c2140c100b00c4c0901d270380707050300020b000c40c0e8080e54a54400791940c141042100325a841940e010300c40c079141c00100012086000d0300c1406005000100301b83c49252a05d0248022710000e4602e41c0440086409807405491069441d17603142041018823005603943ea0040b042048254050b0b54042200f00241109010b000c150304505900503100c07041106502100300c040e0700402c0d01441d5a9079040e894102c16040a0000d503410a1281d9200400f8090000251581d1042180a2040308500c046078030f000e0410380d000c66400e954402020804410f044907081c0d500307400082c0b5582c000c11140411024004a540038800c500003515 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 744041142 1250 744039892 744039937
    0x91c05010c02060c1809040f05011d070b070b010b0d140412090f1203110f25060c0b0408071109090a110306010b12060310110c0610051305130602 64
    0x3420084000c0454680010800110302e0480c05000e0010451201b2500320295480d0760410114100300b80b1001440740d80307000001c0d09801509054856290004000c8801d1540c6440d202189400b48450084c9044e0740b800040c440d548180b0701810102110007000984589424911180c0d5070095409941602c01c0c68050140260b00409220190001100100c0c0745841d10783c0d00c0c0340e0340c0d6403054080e003001000001003030b00100c1170020001030102a411595040c05041051002d000303a11600c82c010801118002901801071500c0c441d5181c001210207101c0e07583c2c0c0ca07200c6003548402c0080700d05684c80030b280741c0240e4943c503405006400010052460f01ca01d841d150307e114280b1a10710784650f00020042107103601180071208c0160003885a01c0151b100e40022900c0d00d00301c610602401410101380345095100308002c7d006d1800c0400851b5600d440e80049000d80c648103024052700200034400f2400c0c05050764200907084012004442140043e503103c00c01260451004520700441022182c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 744042392 1250 744041142 744041147
    0x70e010603150608040b130c0b04054b0d0308010302030c0d11010f09120b220f02060906130e010f170c0d0213091113020a02060705091c05010c 63
    0x40440d0058940325001c1a824800c0203403c0d8400200001c001981110015207c4541e12090840701a0300040d0015840d03142e42d54603020b44c00038018140108407500b924102c0804100500c050485550440151040c15000d20010170342803012121160030040070006240d124041d1a100c0d0500035500c4030300b6035041d80704060921010404aa20800040000d0744c00314481503d000c440c0f02090824250040c0c212005503464210740d484040c41b03402400150040c04003420401e0f1107440c00890651500c10721880007202c0c82e40d07010001c0d01d800041c2c07042a00504203800140080c3c01c00a240905140c100d6440c10b1081d00181c101c50013034215000108030310140422110058401200c101500c8010090b030b07156100341e0100014410183d44400d5429500e0380c0a0440501802c400103110200d800e0030100e06030708900c2502c600480510040c1d1107151000d20950b1031961045d80079014603180e04908480740d82101507544c0d444141030341d0540480b1103241d000c1c81d00c14818800420310188a1038003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 744043642 1250 744042392 744042401
    0x10080303250804020f0909070e01091b080c030103060507031d0d1e170601050f0a09080d0e0105180301180b0912030615070303021b0a170a050d0906020c070e010603 72
    0x41d041c05404070a000059680c0603098000705001c0e1001d41c1613694800510386400b02e607521114075a544600007080c000266000564981035242801c1404107240c141200c203144200d542c5000c1c04d000b40300500010b80c0640003260013078180d00d008250051861000015070f843d159900c4400d9101403903402c080c0390061506200c5819007148014560102e9801420000e01e4801c1c40300c8000303089000403042d85c022030607503c240c454076100c1c81d1a207402c014081c11041e42409200741d544104152065900d2041989161071441a55075900b003984480d03e007018032001403007165043d529034541c1103014842510700034045010b00f030903004a040001420b82048041d495204841804004000c0a078031204401d6165100355209940d6034211401c0440083c003c1030800c0c3d20030404000400c100c081c001030052405401280d48803030320034064031a8140791088030b44c0303800070560a00c1003e03681440303540031101c0744e405540003610f0983e800c0c8410381031000940010b01104041401813040d164140319 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 744044892 1250 744043642 744043711
    0xc0b0309100204140123041806080106050618010e030607020106030606050406080c06030c0708130303030b1e01110309090c030f07020d0503060409020f040e0d020d02030301030c0e10080303 83
    0x1d0862409080c1031680c80108520310900b41441400504c00c094500b1380360349000740201116540d52140d417942c00841d0350380c0444408184c00c1c0c0c28040041500c00b41031141408030f40d8001c00e454504045c1c038072801d07402d40030742090340d050002d044241c8100c0e89050002c18411a440e42c0001075160442c5080d0049410f0f070341000d4056850000c0501c0315800000b6010301d00d16040300c1e81c40d00c0765100c01061311b0030301c01c0c0c0d000180465004101326400c803000c0c00400c0180c91080c3c07801d010310184402403140c0c800c4040c0500d00603810303d2448002d05c1d401805040d003a140309400b50f078076080300900030480721501500e030144041000401c001c2c0d0308002d4501b05812418605c0581340c0c0200f0000010028040174014600c1740b690780c680070045554a803007601b0740c007a01400900c0360002d00d290b102e40725a03424454a0140c010003140000c4144040300b2241030300c0d4800d070313010111030404803481c410903402070402c0c031158110000400c0850041026610504216845543d0418800300c07082070703900c0d60341 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 744046142 1250 744044892 744044923
    0x5040b07090807050607060518070f0501031b1d0f03061806181002090d020d03080a2304120c0c0e010501020c0103061413060f1206150b0f0306010201090c0b0309 71
    0x80f418413490391403c04175200d03290800d0380882c4549030f039801c1021201c2c190302e4440243c40b40741c074002032004002c0e50500498100362020005420348602011106000c9004440054032000c0d4103e4042a41c403031101507010054000c541617981000031901e030483c19610020101d40f1800480c1c1070303407020402c3da03900030140c00160100c0124905499620036003021350040f52034011071061510b4a84040c0001c119070000d007081c001111508028040c040e051f0b4607410000d041040c0305140d104415034100390005610880d020300d035960344569401514041d98002041102c04c15400810b5001a454014041d15031020500754904000a86400c003600805030506040407003c0040180c030710a1219002000d4955444c0304e1411082c010040c0700c0c580040b14007400400010034481c0040d0295803581d13100d4582080f036000c441501c000021614403070030000b01c1c0d081007004518807081d0043d50700400107000200b1542d440740d503444030560064124003048a03000c420407400d48000c0000340c00009002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 744047392 1250 744046142 744046153
    0x603090b0601020c09070305040519030f0206010b0903030a1412041b0509063618071a0913020f0304030503070f030c1b03140406022a0904150b0405040b070908 70
    0x7100440d4139000001e25001c107050ba81c23000641404400d0080a44c41a25401c0700c0210241c41d240183c00d4881c0c403c0b1003001882040c00208010700701e0740445040d10360050082d400c0c41e410380c40840c0c09544c601103c00705241c00703006042c03000c080d6191860245104401c0301d242e035002c600c40c2c51294546540034a02c00c4a4400c18020b41382c5aa01c030a4140048000c00a4900407091100503a103501581441c181092440108507040c4e00c020510351904041c0020b0b00c02150382c5a05d91425010104072586a9203010440040140341c90180c2c807400181d0b026005d403c1042c2c000c81a12550030440c0c00740c012030340000070814050317840400d1030706c030100c02e060400a01a03100801800880a040741c2080507140e5000d810505000c1d001031109151418840c990b00da4440e0402034075030361180416002e8030961486102040303103048800e80520006464041c0b55a80c50b1075001c0d0060301c203182100b1083e40c07942044030507111401070a00c00c07800b52600c41c4050034800380091078030107160701805840d0000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 744048642 1250 744047392 744047413
    0xe04051f09020105041211090703051b0306030d0f09080d2316081e04090903022a06030c0f07031805100c0809060c060f06040f2a0e03070603090b060102 67
    0x204c0296406d54000c2459510f12141a00d0b010314002120042594000103040c200030380a03a01d0b4000034810510103001c0c0e49014014000c481842c08140c8106900da0003007400200518403441009010035a91f1031301d9208640c0c1c0c0c40802d400e201808010000088504a52500ca6454010140d0544072005e69052a01ca5100302012188443d41001483ca50b0000b64000c00251941e110310045c1c2580b01d0354550340d503a5840d11800601303074107e045015005155204103448034201740745043c002d841101c8500425024104649a4002000201d06407401d1040381400c005071805481c80911039140c00c000d05855131848401144260b0089108200209006c502e4517813007160804ea4980c0080c22307603211403c0c4400140140255515499144500020071000248884500d8000c40040c0d808003d04203900c0d40c118252030b1200b0001d0301030402c41b2116211007011250584242209280a0340148058130000b810541c2c0c5610000002c0c0d103072441d1301c091265220080344c11000c2400140300101c0c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 744049892 1250 744048642 744048647
    0x80703060605060307120905010b0411030402130b090f04080d060602030c1c020a02090c160c03060f0b0913050a140c0111160324020f0a0210140c0c070e04051f090201 73
    0x500c55444c0d0046d9210560281045000d400c040708030003004005201d402030007854031001c0e07007003181d0a0303100f1182e03480007501e850102d110340b00e0340010151240101e95180743c4005a2600080d0040b10300800402641d0100c1c22030f403103884050f040e40da01071944d5001444069142c1840b600d41032201c94140e485280c1c42640000d00a040b040e810f41d40d0b1000c0355680340c9200d2840c050344051201c0032000c644540104640a400501079900c07d05040110101421890085910b04412150031841f1074011880114440d480c01801620034412074248200c81e41c1d585140d204142214980ca034055600102a50781103004001e098441380000d02c0d100b1850032800340c5618840c400035007100d1a0400e0040380800e501880564515021001e654079120b01b41161001e40c000601e200060040e070f801d804000349a0b0040b03412544c42c010350788440b521404075910241c0c0c0504034a500c14481c2e10000102c034800310010070701c50350048005d007191140114201c0c0f200c0d503480421102241c5040c04080060781c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 744051142 1250 744049892 744049907
    0x906151e0d09031d060a1d040e0a150501081f0b03010c2a05060705130e040807020a050f1e1215060a1706150d050105040b09070b1c0911060301080703060605060307 72
    0xb03087d00c0d01a5000601050110341704e456524070b9074005081191521200b5400034296000501c10140300200d8000b2072451004c941084c041c0900c0d40e00040d040c0c0b03900040342d480e0240030801d00e14001409004c09400242140e0440c0c22100201d0700d1907510f21508850b40900d94024190170001001d045959074a807915888010820303828460086650b00c0b07640f118104600113025005101d00d101d05280c1000415600305660481c8990b440300004034403400e04102d815542000580110852017030380b40404007610480d200702d81c20908a610a81040b802000b458a075083c10110791480e9081c01824008062481c0e000b800c440c1116002c0e9134480b020004d030040e4002000500c2d443c100b00d036400096901d00302c02e440a81381350b0a11040c44180200040324a020b402054219102c090380d5501d141d506000301d495058406d4003444010780c6080642e0850844644078494200201100c0c0000480715082070304051340d40d80c80f07920709108002a504c94000503003011a0514150318041c80010700e00c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 744052392 1250 744051142 744051157
    0x203060412051b07050a06031116080c15090d02010903080f070216140f12030427050c1306020c0a060f0905031b010e0906151e0d09031d06 61
    0x41180c005200e8124031a0064901040ca420940700c109444828801c3d40c1d10018014180b05096106c000901240644603145140c068943d840d814008131442c800709a03001100e040d11040020440c1c117442031410300c8010a00b001205451301a401c140300c00900e003102180c10b0606680c9020b500c200403076041144182d1165a10320114016501c0380d00481c1000b10f8025040840da040442c003040048462034500350b180e10940b40584560400410080720503000d0500658907041080244102c4070011300e800084820b2080d0701030310261080e04282110380440b2030003181140820a6034040101d00c100100800151005002081e0b94800240c0204051700c01c0c030007485040307a121264103006852400c01810018140d801c125a01c404400c50b503c13105107100c0c0002d803912080b41c141c0c80c0a0502501404014044a9040f0343c1803240d0762841d407007a5080409400ea1030404443c0d2a50346005103001d51880d507000c50000d03400d140181c9181c030061180c614110b501c40007401152698415940c00c0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 744053642 1250 744052392 744052403
    0x1b150304060e030d1b081006030911090114190501171f030506191514011e0e0f010503040f1506030f23120904050604111204020901050d02030604 64
    0x8944961400078000c00361000baa90340c0e80030220f03250307010f018198444190801171000062510444603411261550f0441e00c03091145104507080c480d80340b00342e01c004500c6200d05110f420161070300c40010320042007640800b00180003565921000d04090440891410000c4040742d150390421002810301c105000b85004003003000000101010001c40c0c0b4100b8030503003807200c25412a100d003041900c5001c122104200a4620000380d5000022440344000402d00b0600442d21181084484a4107010105000341081519000c282200444502d0000084142d46038450ba4103031400c2800040441030b00701c1030600c541403003080089009051400079690380102c0c00200b598400c4124402804541c10242c03410029050407010400c040a0000b0551580c000d8120290160341c03016581c1c500f040c40043c220348080c02001641e08058210f9504414000d1001c1510300700380c800000710345c008021a0151491180922042d030512565840c05090103a81040d00c941058022036030320000034000420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 744054892 1250 744053642 744053647
    0x1051f0806011d0607120f0c1110270602010f02030408070f0c090c03020306040501140a03030513122109061413030f0f0b010b03040c0605090f0a090e1b15 68
    0x440601c100b40c0514040300c0102003585800c164180309040c0c40146005031b02146c16284038030107242c01010040003d6900640c1c80751188a4041480840e000c4020f802d018080101b451040d96031000c090710500c64003080381c10800918203500242174a0984851424651041041c080412000e070100c418281d008103003450751072400d16109200d0b507002d92001c00b61a243c40c841c04401075040d00150300504c0202ca0501c850f90301e50924900c101264044980d000d40308800400001c0d02a03000780416041d0041121a115a58003c83d080d0400040c9c04175442ca004940c41541c5d0603500050341d880c0685481d01c11981418068007414030361001c1100480c240c0007140c1c000b04079400d681034002440d0301c0058484030035440d04c0d00d44050f6201d041d08031882c04000c000400e0107141e603001d491180790480b4000d054646001c1040c0c0da140c0c021b074040c0f03410409650480e2166102c1071215001400c1c1c00400003035881d0f0300c0620508104031380140503503104090341203080c81d54600d4400c01d20004859000c03507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 744056142 1250 744054892 744054917
    0x170106030b030f010609140108070608070f0c120c05100614010509040b0d06021209010219050c011515030b060315090c040909200603060a170c030303010e01051f080601 74
    0xa18000054081c02825070031301c0d0003c920740030280c02402d580c01c0100c0407d045640c90755100c9443d83d1050003804005219070000800d01e501c154050740b0300000034202408150f685850350b0501240060141003c503141c00e102d02c08114080200d004e860584510800c041410107030b2440d54010440101810000003160321001d548d219484480d406000038151105030256283c0b02001e03401181c043c941c0300d0020b0300018507042c1c3c180211002e00804071002c1d05030303c1700b0701000c4d43d8607084041c4600082d96101c080708035141200c84554090801c506022070305a17007018000f42a5400829814000e1310b06005000452480d01d9612803244022510760507940d40300c2f400c0d60000d0189900c049070140c01d0056007030901020412503045c01c201e100b44001d401d00350100340310841c482039805540042050204108901490f86c04100d2402d1050986103400b5489000900e1764000b80c00c401000c04040004001501c2d10b82e011150410b0071011102e249810f2031005030880c11700601d01303810b00100a40c02d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 744057392 1250 744056142 744056149
    0x9011e080303131b080304052704030c0204392c0f040501180b030304081b0f1009030605150a080303150613091a0904120f170106030b 59
    0x901402048085075243d141c1102d600e1002c6148400030748010301c00c81c2c59004050241d22011041c0c8102c400118a01454001400003210101468020104003000c0000224034104400c0b4000d50081d5903000c0124040e004100445426200c01600007141040345040c2200c50306040e100340c1a6240c8110103240e00304801d4070210007203403000d070b80a00c0d0018902c0071264500c41c0440301000079100381c0b01e120b2100060000b00c0380c00380504a081c1070f02094800d0b940d0026085000120405000c0e43d05050b5551805803514142c0c5143c050100b445500044540c200300c0080856a601142c007100503200180000d4202c0c212030002401c120344a00c000358290a49141c8580603100c00b4055403e510b0785e40d05026280c0d04192003551111020346103506140c5460030645038959500242c0907141498140c0704070080480c00c006052210b141d034240300c507580e58801841d220754003d02000c2038034060a000186050480710003001400390080003040c20118100310241034804c7e0381000645500443c001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 744058642 1250 744057392 744057449
    0x120606030606030312050708060f06090301060b2a070e070c0c0b040b0406021b032512050307050708300c0601090204050406080111030705031f09050118020304020901 73
    0x5082141800800000c05501140560f501002100b080001f0340300d01038225050802a14120343c09405802031000c40c0c030b8240014880c51344001c000144080d59118030420315001403000094482c1110300000f040c043d145400d1070b650440001404001c1c0c200481a0340560000c1c04c0c01003080761000c2054100000e040071000588000b8042070b80f80d0307a40c3c041141541c1d100313000c4c1c0401400350f00384651148040c604010b44401c4001c4c0034242d8840709500000c42c0c4203201d01d403440003026844000030198080381e4950740e0781d07008a010b10740d900c5081c00c20916100c8668032180c020352140ea00745811600ca80d103600d44100b0500700684451099501e240081d01604101c440c035802400d0002580d0141030340144204c40095406010143c2d54051642c00c8400da40b40c242c1d00c200c002c03c0000c244600c04e00055500448501004951300c040d24a8070004611640020442c150344200600004030100328659900c25601c506614502d030035070200b14050010300c1000c00c5004184010160707000000c21 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 744059892 1250 744058642 744058649
    0x110304110a0308040e0411040c1e030f0f140907060c0b07030902041a040b0a050102120306060f0a090e1b070b041e110a0e0108061501090e0f041713120606 68
    0x2000c3e070315552541160249080295800c40b04000002c001807542c5c101801070421815082c0c580040201e2144002c0555071903403000507042542c1d4030180026800c5038490807003000111100050080b00da202d2121040c034015180500e0760341b168000700308043c0e01c5600d90f05100d5121142c030910313880c0c540090b4050504c00b00000d40c881c3c01e11b030300c00f000030080d0b0180400e00d03d01114140544061401401254865400745c98016040f05409074041c0c00600003c5030001d001600d51480c0a03038039404101030307030030122a82001a0041c0d000700803440749241426041562294500450300e042444009503200328a4001d095a5110000809203c84021090340c00703215844a00340f007003070516180510340910714069101f2800108082008080500c0740c1b8141d0ba0020000c0c891903d0318a4000c1245900c00c0f8806e0401100703440c041340540c000415a0b0003004480b14118182c1003e161041c0c080000300d88100100d41c00340007407040141845401c2c400c0743c0324110321a110200758280440606119007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 744061142 1250 744059892 744059903
    0x506090c0a18023006010311070308040c080610031502090a0303110c0604080304050307080f0a170706021c05061008060d060603080a020303040506180d1b06050c0d0f110304110a03 79
    0x81e000640c0c1d91003640ea2108035090344e00340799010750b0313042c0041d02110306034800038452070703c2400400006402030300202d030414000d2002103145603450707184a140503030403241300700e49240101041040200384403c0d00050b1854540541c2002100000f02d0241e100c140b10142c1000018840d90b0303003181c0148032009140d4006400e5540d102d0716805890307601d0780300b4030407503000707200d0148001210035011624411400350781e40034164906c0715440350382200c0e910101c1e20390741c92020420701000510314030040203070300718250302e034440b6014407042e000440c2c00040c807540c020314140c5201380b81203078000803442d8444812500b10070341c14400d041c4000140381540000702420000034820034601d80010155104034400d00c03c807045652180308210220380403550fa100c1720350046000018590081d40403280c0c0004032030081c45040495220181681e40685003100b0f02400000d4032408000c0c00d02406004031300011042c03016402c9440c6060f202d100c01007000d0650761510f0350b07040d000e0347c0c1c1135030300c000441c2c119 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 744062392 1250 744061142 744061177
    0x50106060e0a0e010e0c0315100e031b090a33050109141503130515060f0a0806070e04020904020a210221060d0b040302032508031308250506090c0a1802 67
    0xa00024042d8880030045034842d02c40c030340a0f030140d40c0c44540c28981d0810090038030307016901c6d166103050152950f0075040c8504154200350b603a5545050fc01c07400c0c2e9009080a422000340380c83c002401907551a0052418000c1001e101c6000d5151883d0701c05551001d00c0381303540d81c2c0c0c3d0303040c083d130382c4c1c2d4403001030010030b24001e406d1b80a1040c42c40c0c9032800d0182104075030200000c07150360b0400040e001d662050b2061070304190000ba41d043c0c010f4040d080c10001c040d10141c0b501d101180050300700c0c1c1c41402e0003808200d20f200007811084109522200e00060000b04500e0003ca80c82c0c02c0079004c0085070050b0610041000088403038540c1d050008840342c0c06407000c55503040031700d8007a48036040501b886001d1036130f00d0b030000003420366400324095490700200741c0303840d640342d001c40b0014400b0100c0d420b80f42c00400704244002c0800c032a0740521040306100d24031220615034070340b00b81444009058040701c0c0d442501010420782c4c3d01e080342c07000c030f0305c181c480210001c5000740440040d004640c808003181142 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 744063642 1250 744062392 744062419
    0x70f030c140901030215090607060f09050f010c090e06030319050a0206130f02010e040902060a0903060b04050f07050307022509150e130f050106060e0a0e010e0c0315 73
    0x30580020256280e8840d0694110205424009014030034030019612050700c401e00c0300040d600c05c0013840c2955010341814540246610380205413801d111900c2000e070303600c400ca03205201044c0721150011106030020310081017840c80007024901d090140d82e280d4a110000b007150369804004483c41c100c4545011103000c544a44042e14940080b00580d015002d00000034401020880822011a038071000e04000100d442d001118020149482c81e03801994810500b000350b40e80001400101d0020341e950300440b030540c41c1039001d40b03842500c1d05028038206424070856400080c419640100b06291407a02c0781c0c0c4100c000c07450841a15510511118402c0031758085050521088040e10307203102080c00b1105400f070315200c1242d40b611a200083d40420089a000c8000c0d000260800380079043c540d480d481583c482500311400741d800b41000c500c0a10503400e0313708100c08810002e055144881d41d803589041c504d2801500700514044150b2000000102c0640a06000d8100380790007800407101d0008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 744064748 1106 744063642 744063653
    0x2007240c0b15120c0a0e0f010611030f070b040c2304020c0102040f090507080603071a161a0601120621020604031712070c110d0302070f03 61
    0x1c00121035159540d4450034800f9000c1950141c800c01c2c4014080001010313180c0e20041500d00c0c41e03020401c22030b00d0009241d0450320a03061031202504c6000e0081e0070352103140d052140811001c41d544040c4032521a10f80d100d144290020240152034109000c48200d030740d000501c1d02d1702440b00802031820f00360081d082d0700c0300c41c40000d0b040640b6840c041d2840e0050350807076080541c3d12010030516990040d000b580114055014204181c2014a41da03c1381c1c003081400c01c065500058a011340201c540750803441d441d04105030707240f4810400041180d100d130503a0314a00090b111846605041d1803842610122202001100080540800c0c000d80d00c00c1c140d6016a40080107000010118014103142020480580a5559903082503500305407156805405a0200f08a2441c3d034070016190000e828040c00c03007202d08079044000342c03070f00b03d28140b05078024610214080724001304020 = true := by decide +kernel

theorem cover : BRFrame.Cov 743884892 744064748 := by
  have h0 := BRFrame.cov_init 743884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 743884892 ≤ n) (h2 : n < 744064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
