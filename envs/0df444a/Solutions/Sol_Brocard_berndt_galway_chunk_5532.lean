-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:10:16.921975+00:00
-- url     : https://prove2.me/submissions/f7ab2523-7ce3-48b6-bbb9-d6fdc5cc678f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 994784172 ≤ n < 994964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 994785422 1250 994784172 994784221
    0x6010b0f09040231060f021b0d0c151202090603010909050a080c16080f060f060d02120105071112040e040c0905101e0b0d0e01140a23070503 62
    0x1214a14100145080c0703c044203a9200c2c40e2010340640204c0524552140c00000074414002098079415500281010700c10754804c142a00c03400150340011010900008040c000c90404080800c1c502403841040e18030f15880c1d100c01c6150b0540d04081802c0c0c1c080d036005140d006009000400c17103045e41d500440101c900c92425528220101e0741c1b503c1032900b1074200301070603034001156030100d08010401c4901030301d040c0b002400791802d0140c10a90301c0000500380c0b181d82508001280c0b0540301c2c04041c00800c0d074028695600d0f42d981a006600800d02101e074480046c207079a080744152070021681014441003001c0c141c0c500341c2002000c00f071003840a8002c44080400c9400024418a20b10803d4003600640d00076203800b0380780140050014031030300041100c62256002c20171103400ca40080b0350040f40e420001041030000c00c039600f8010314141240c9110358030130f40100290f80c41c0c90344c840b1010b00e51001d40a0140300b44000b00c144080710496040703010550410200b4404020589003190a502c0503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 994786672 1250 994785422 994785427
    0x90c06120406021b0a030e09130201030e100e01051006030207081615020705030915090f15190504060f0512040b0604060810150509060102030f03040525030501050906010b0f090402 79
    0x1000d403c001d04451301c41c07894141c001c00324100400d603100c080c141800808864a10141c180344174603000e9a882040001e042c10368a00c1120f0300054240706007104000c0071700042000010152066003c1d0a088038443c606544528011a160f4081c3c42a942420f41081341c060a18004c0c400c0141c1a1070500805d848154140c8100d601003000c031300040041c240718201650f140d440d1081885078110041c426210304010130300c401036064542e02c0070138140c03e07012a07144805407030019092080d031107040089200c1944040382442c005802000130011141c0941e100d821013400c0700740841d214050707065035911403498103020401003005c0d8070748141c03c10001800060129030f28071889141556000c41140300a4603000c8000c0103802400310341c2c00401055038540744900c1c1540000303490784103d017241007e20102001080501600f00040da9003110b21006c40040c454003091580b0166810b444221915030900d80080e0102e44041a054100c4e6040c1030900e0428201d0040c10b40790760050003046410690a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 994787922 1250 994786672 994786687
    0x30103260a030902090601031a0105090409080d090506180c04020a031409010605040609140402010503090f06190609150b0d02071e06140103081c0b030f15090c0612040602 75
    0x41030050040c081c4a440020b07400c4542d2062110095000701114141031a01c0c0440c4241046a801c0c04000f06007480c0c0749a07184110b900280041c04802d0f030252240402082c00c000c118190b40c02068121b0080e0b04880c0d65a40b0310182344192140301c51540100d41111411001c41d06058024014045171801c0c00701d00c3c1150285050206001160f2244043e03455542c108210304080c401c240c0038007001c56050041c4180d00c0c92503e00258050002410400001b0000350790306000d020642d0030b0760030641990a103003481c100b0420090307038000d121110b8605d010000102c4000c644191004808ca403501c0c0400b9a2904001d4440e036080705801e0351034107070200300e070344001405a0611a96007405a80c0781c04880e80c40d0820304101e07100c00c209030500404400040c0089a01881540c5003000300e01d600c920100840e12818024200c100c5031380f901881340444525400c030300460034104150741860744258507622060895035071040c95801b190000800c00020b205541c0103c29130364000e01401025190a25 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 994789172 1250 994787922 994787993
    0x3080c0403150b09150307030b0c04080a08030906061017040312060b07200a090b060702130b030c01081521061303030506040c121a10020d03180305030103 68
    0x11800c64500100d56aa002e0000c81d1130000c445030380100d000c103a030341d441c1103490010035525182404003a0540d41800d00003102120540221800387c154030056131065515403070444825042540c01003098087e580011301942010594011340d16055650b16000c8101c40d201a5080070740074109a08001040584d00c100140600540c402429845819552610300e418420500366011b1341641c00c11414040601140c0d84079100e030000d42ea45d036000001c60304070000c0007480c0d0344101c2c10000c1d00b110309225140c41845403640300c000e80c40300c03e82c04d450710740b1035100044850142c00c490b40040c0c1c1480800b900814102010154504400d0340545021000c1c049502440d068044440d4448105200710502c10103a05016564002c202a5014003000707414a0300544003c610350403403401550384180342845040c51200c5401400000b40400c0905146444006c0d21303403280e00816401f20f03081228244640b003104810002d12901651200d00b16421603454460b2400c1d00b680e034034a41c46444103031810054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 994790422 1250 994789172 994789193
    0x909010605360a0902070b0c2d090f090403091802130e0106120e0705011d0d030809070e0c03070c030c0c090f27081e070605040302060606070f03080c0403 68
    0x16400042d50000404801008480005030300001360090050010600040824481c15001440c0741456174595030030900d03c200e080840c955400509003e0814400748200b0f01d801020159029181109814151070034481180030035580100000c911400412095030841c08006540d04c0604002d0b01e010503080204603818440e8000c8103110044400400643d0b41015804840340c086034001e0207905024200c40c0e0700c92074644541411b2010300b0301c0c1032125950855020744207041c01004400092214100203103410b6088411980710f00c42d464001ca0050b540014442c4210b0741c0351080d91550b034641380c04440e1400d03e00421014000f40c0c00b1030718000381c8454160000741460380305c00030b41d05602c48040070564500b9940c6100000c1003032040c1a1095440801001c41c90f008032030310b541c8000304001d00b4020801c01d4900060800d011070307228108101c03070704410700440c021742c03c03540c3d60303280c0e401000041e1050541c01401603411a84641c00070303026132001907010891091060405a070f035215104042e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 994791672 1250 994790422 994790497
    0xf06030a0b040b0d030e0126070315050d0f14030720130603031e02100207050c030d080606030f0403022b02011d030708220b0d0b060909010605 63
    0xc1d80750440d40c4418105441200b110600442e00b81e500c05615480c042d08404c4201002c60401050b090988a003a600201c550710729103924001684620304404000e00a1020020b0601d0702020071400148034a0180c011600c1280c01548415103104c459481d1000203001100320445800244944000308040f40d060342520f105080d5001503564203a01000a002c80c0243e20a00f0b192030f120090010907030140d4845240c16a002c0c1d1208103182c10401030340b07800c40301c4001721300c55800043c00104200011920710300001090b400c071465414007541c142d50310b1100711807903a0400020301c001071000818418030798001d40240140c0342440c0b04161109031070040e21802d0301800a45a01410f42c0c66424810003030360307000d030840c40c094030180708600d40d40724418070101506404001c00c0d00c0034030220600c89000c00703080381c2c50207141660780c41ea00c50302950042640241c0e201e00d008152102d500303099040303072112100184484d00503801e040041e10030741c005620182c085c40e510b0400e01e4024a030010303080c060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 994792922 1250 994791672 994791691
    0x10617060114030307031b020d0507181505010e0d03031503030504033e030c0a030609051209060403020103050405010b04090c0f0603091a13050d050307080c0c060a0203060f0603 78
    0x1150305044040800b0000c0a9280f0301aa01c200407540101e5400301490b0907810207031600c84550462400019580c26450b1030180c1036001c1c0d60380004d060380303885041940f00d48962000f440300031605603200b01c0340c0c4007905c1081c1c0850f41c5290700402c14582042d0514096200c0d0030f00041d49090301c1c0d16621510742642048000c503000040030310601440c034991447c090300b56145401c220f18280030215003503014020f541c4d4040c0401082a015030340c01e00c003000c400ca901511034078503259603003040c1c40500201c25003a90207010369100700740d1144403902110300b00d01025012034078052440c1c0c0110300402005105039603655841c080c04140b90340b107000b400d003a14003904245034050b04100a4070300070a160740c1b05405040c5080c040800042189911994250140290351205d541e05c0350174000c40141207070b000b03200e07005008200e11416040300185000702240c0d540c210700ea80c2c2c0c0c41c540b145244184901c182c000e5100710005036000300c41e90011540701304007500441c0340311156000300d2200d420a85a1511 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 994794172 1250 994792922 994792933
    0xb040b09011b03090b0c0102070203250806013213140a0c090b0f0912010f0506060405010c1205090402070b06030606090f040b04080f03130b07020f07090e010617 71
    0x1156a1101004080c280e691580c010250700b2036070042d142c03100d14410b000ea602004113040428a00a5069808140d0054181e820041d11f00181051007207480314800840c0c5001d07140482c48510000e1554140c0309540103240902031b10a0400048500d02504003122912001c0d1002c52511103190705504110341e98008944241c4208400501850043c80c43d64680d140c402c4410210354041850000c480808000343c1c2c0c5c8080020304820603103d40044580c00003426207940301e0b8840c05500c0052080706032002040180c45490800c69144140e10450740060720b10004003011400168540c1e61112190400d1450011250041010b80c2c100c0b04041e60020421000c103c69418180155079020f0800c9a42000034a0100400d8000020150018000d6655100000c040208034011610540e0030100c43c80e40343e1402d44856800c04600001c120740c040201b1740400d01090002600241d074400c1c02d4003902c10b0a0416030050010464040f01c6030040d03403130f040c00040741a1004030180391602103034003404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 994795422 1250 994794172 994794187
    0x21905100c080402121606050705150f15012c030f07171903140a0201141306140c18010512090c030f0f0703020d03120509030307170103020315100b040b 67
    0x8503030400320f90145c00e140c214032801c03030300c0c44c1c002d15400003503880c181031080c0c5814007814218906001141d4801e500c001d030200381f1802e00c4141c4d01d030134862a284515080051400001140c2d00c02846041c030b00c107026180e0310344c0050840988035141d85400901111040200040703070529004981e844035901c000a1460060f49120600007002a61441812800032950782c2d600140019100342c4031035500140484d100043c94400e401548140100445810860410300320003500c503000410100d40c0d0610b000030000b074800c00b490140c1e10640441c04064105451801200440154500544d042000c02c000c030403107864012007a14068400c0e00300511844080340c05052811541408150080e486180d14804205000803c60190ba60584d01d520b030518580c0340a80d410090b904003c401c03642000c04100d800344000001d14451170090b507911038042e12ba4813508401110a02000c0d416130004040703a0b07181e100b9102402d0300701e485030f4907550030569914807840558100d90800011080e001034003d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 994796672 1250 994795422 994795429
    0x5010302090d061b0e18010b1e280e1516020402030c0a0201060e1003121b05060a050c09030703020d050a0c030f0b0a02310b0408010603020a0f06021905100c080402 72
    0x85440078002e48004205015400e46648500c50511a8085c0c603c2c00003000070301049501c11820244014154481c1c8ae1410141c40d104002e50441134000b0081e06082c564840500c80c5401204103c0c020f01542402030f1201202281a40100442e030044c002500150005840b54801140301d4030f2a180c0040d21103000c034a000382562030681c84040e02d20480014000c0c000011242e170310031607134807100c4282452000303407050b1108084905172411941440400606215011840314828448840100300d25541c180301400036001c0c5004803601640048024001410000c1c100c0d054280104116652802d05541700e22510585400446422940d6901e001c2003202c800e154035000461203005604140e0b00b09140041d0580310201c00b0040300354185844d01e0070f1174080444000c2c003401c1180d150b44a890741a0396010f070109100c01c80c020880600005262046401d055081d290140d0160101ca208440c0917545c03600c480340c0940c0e0314003a000301000c0e10780140c8200058902a900c1d00f00851900c2e0040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 994797922 1250 994796672 994796687
    0x1a10030e07090b0f0a1802090a03080412030f0f021e07170f010609021c23010b0a080108152703160302101406011b05060c1b1605010302090d061b 64
    0x5050140582505c14410f4002d480040f850344110100016141c10180300041c000aa86600181082100003030202e000c9004101e128a0240a51244000009022421118031102604540058000101032802c409003156042d40307101c6010308a910041c1c80d244180d800504100b8900919442a20314980d080c1081c0070300c40013846071202c110300300040b40c00302c02d0220500c002c040300081d6885200d0156040b40a0351402242c441c01c001da1140d60315400007070b5042d40171005513000302d00c4c80e000004811a0000300c14030440002c3d8080702840e01ca114485428200783c2004540407800c2035040040060200040c107800394803003005e0001c1c5219810041e0070001c60864402c486030804001da842c0210702c03144a0b801404c28070300010000303442c60707402c0040c05030400002c086001d02028407038011008800f410240300b115040001c9850035281e641da41e1203621207203040000940008008a40c040c1c0d01070100810302521400d240300056440c103084481d01009540044c281e103600b0081264003910 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 994799172 1250 994797922 994797949
    0xa0e1f0f0f050d2c0a1109062706040b090c07060509120f03070e0d050c2808010c1701061403100302031906180302100c031d0d030507031a10030e07090b 67
    0x141025050988546c1040c20005560501803507103940441c050307447d0290283c0d8a4880078540d425050050b41000105400a03034100c2d00c55400d110540708607107014141f80f8010a40203044a1800a41da42d03001d019100060200003180901c0c42c28200e070400c050014021000d5400216641e440c02281c09800c5119048145010300e81c0301d08140000b5100241d050411001103070840c031884007204100c80b801c03808400c900c0041107a00703000030b00940150000250843c107a00c0384500641e600b0b10420300440d00340716081c0003c180320f2040340898402401540c00541041c803d03503601751242c0109180400c4101480640344401c5001001e000883c458600208101c01c2c000c004000300340c034000d42c0c039040f02001c030124070f56800300b45038180e000364000c21005070b81550340d0042520b451551038842d40405900700120707060800140e0a6072103031140552440c80d000020001408081c14400040c40b00c0b42c098042c1a5140301c0350309038403002c0080c0c8009107600c42c40854102e16a20500ca000403840c0ca = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 994800422 1250 994799172 994799261
    0x606050d0c09050603090a1e12030504111504180509190f0b0708060a091a060f2b0b19170f1603020a050306070219050307080a0e1f0f0f050d 62
    0x183e200016080c90300f4001501e00c0ad18003c5201d403101e040001c03086030900040741d808005c1b0f90030010190075107400b50040f209103215940100c900000d40c082521011607c2c448250802c12042241c02003006141111038010725410302002000d44d9000e02054003591000007088610042020a00d8191400005887c1501c1d0601c0000700d409543c0b1407580300110502c0c412580469240c0080c0515800e86000c045990340c50090706c4240c03000d203592a1540d030402c113581c0c1e003000c1c523000c04c5090180e900110125642250340d1190301e488884070140700d0b071081400241c041c013020900059030811503100d90305204c1824810f0f0518510400c0264421640014000e802980400151580200307401a910b08006400d500c0f4a40c6440d00c2ca06520404500806050010558500b21940540c2a40c0140e4040e03c0500084040141004151421b035544c8000a01c1c010058003a462107100e043d0b82d280103a08000e418500c1c0c2c282200c0c20754002c1c910000d42d04500c0101e20950b00003203007902c0c90014210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 994801672 1250 994800422 994800473
    0x4140f0a030206070f0e040204030b1f0302030a020f041503050f0f061005190906030f02011214060f030304030c030b0402010941100c1103010606050d0c09050603090a 73
    0x740e60280d15100010031150078045e191072402e03050340c00761500d14071319600240215034603526071401c182050019103400d1403544007134600420303014a07240700006507500200100140e4085a0800000070707a01494240c01903100c1d48110a0400e00d600044007841c4200c0c05805001c46804060f031510840125280c031030f0f4010320601580e55031540044040e00c10903107422540309100e07040a2211203095121a52480c68100b00000380402c5003038203088c3c1c0f40700341c0c0c4e00d030180031240c0380060a44030070b0036003145c0301c45540020480602d070100e414140b00d4409002d40381041d54a403502d10086407580e006a5842c0741e031500b00411907900121010190032801001c500b121403c0c0400150340601c400e04003842c5a0325034110340034030340c80d03540601e8840c0020941e40c00d10b0413400c80146035003a44a030484c0c40a0015010180c5031406000e41800d48169070f44141c2401c0711016540d0150401181060038840081004200c035112640114810300c94000100602c40351031500d02400748066003280c110380c490 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 994802922 1250 994801672 994801693
    0x90b06180103020d0206070c031401051003080a0807110d0323013602190906030606050702220203090a050d0903080403150f0e07050a0b1e03090f01020304140f 70
    0xc68100a0550740c050781d481291180c00e1010420901c02d5400c05030100311754880c000b0070841d291584800c1d04668400074811920f07071411160f9407031708601006003241002d1044c41d8015118600c0e0130303031008035450401d08031690380212600700500c141c29040004c0c1c403030500d01d0200d00d50020100700311010301d005080c698900494261101c040030703030601030b41e10741000f65003010b03101490904200c40805021552000d10224504014102c00318880108000703030b100155141c02440703038400b21015902d85d40c0c50400780364200018403501c200760011070311a06140c40d440b56840d00c040d6101c3c07048000100b202c90032034108a494405407108210400c00046011f100103104642038608507a40844114210543c10101d08080c103141071000b5202490580007007400d00b40000c088041351810b4918180c2551130391207010303041c0701c0d41229024103103e130351a2550b001140f80045030300c125072000707954050b1985581c040c00e990080e103058030180246000044103100502035612600d40c2c3e1001880c1f503030709 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 994804172 1250 994802922 994802959
    0xc0403080318010f0c0305070e0a030b010b1308030d0b0a0e1303030c0507141e190206090303070c23042307030b0603010b043b190e01090b06 62
    0xa1801407000002a484440304000b5041204d5034400301d40c083c0202a801c100080c000c14003142c00c10009200c040a5514078282010301c8016030b500502d10700c0703880c0c0c00c1180c00c1c0310a611103c000040b0180401d00095014410b0005d0b2045a25182020911015110401040b5005600169180500036042c00800000080800c1086505040204100c41c0c20401521035010b0050050101c90419850b80200c030800305034070100d0a040000c100304034020300621650780084000c00d0301089807004600001d480d10304080c02160302c0082c101ca181c80d03015560305000c0700c41e6501540c40d070403900e40100f00e588440c0c41c10ba40296000d480c100442c0c01200410721054440388134072110f01d42c0120114801c82c1c8241c01c0110b00700c3c0e01522482d81c95035500049a102c1c3c2c4184603200092004070800f80c21202c02120044118402c000307502d0340344217445d0068130000005000a060055207000d0f00c0d06d110818010700d21111004000021040d1880c01c0c06100c0a400400c0c4910800880c0d0b10324803c5c02c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 994805422 1250 994804172 994804177
    0x30a050117030d110910080702011a0a0e0a090515060411070203060a0506121e190222021b0c100302030c0d0207230a0c080a08030403110106090204060203070501050c040308 76
    0xc40120000c80c101c400307060390100d5845240501d1303400110b108250704c60384c2d1f08050040d0041c06268001c00003802c1d004207005180501103101070f03000d24204000c0ac140c195141560b070300700c05440070004412039203a8900d4945002e840da0740f0007a0410742c0400c84e45142510800300c0e52118460700b82d1904400e5800a5102c40c4020100c64110b6518008112292203034520070501d8802c084c21141c1352480d8807a05140750750b404051140c1480398858074100044010808201c05a000d0500c10050808801a0280c0d144e00442c80d81c04581c01d000c0543d500715080010b00750304999002500810030100244030b00302910f0b880c0c440501d40104144401c4030100e90840d000131011a00068554010b440c0c1000d02e02030017558101c504140f8019414880780101c1c801350814813414440207260365609800f03031103040d030300350181c4420320a0002a003c64054a00041109429000001d00d10385850a0a00300d80064100400503030022529404001d800d12a40e134019041d21180f5046ca0718564402a0b6032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 994806672 1250 994805422 994805437
    0x10c020f0904031716092303061f05100512090a0516051906091202030307120915080903030c030423010203070f0203181512040f0b060415030b0705040306050c030a05011703 76
    0x1d1551f41192642240e0319284003540400141502d002d42082010050000141c0105c12410040700030001054030f0007000c52100f58003940c03580c6041c9940b00c0011201140020407404041c058030030700f80300252040c44810b980c13041c4921500440e600308001d00402501010741048843c2c5544403c1c090b1a03002040e0ba401c90b440e00c0d0804030021301030b201090441c00b50380301c000c00c80300180c1002034150303421680b0141946c46118500b81d408203007100442e8400b500352114403040e001040820b2080340301000030351740240030b100f19903016200401c5020168a0020a2450b603035800b0060240c8a41e1090310b040c2d4241092009505080b075017811000442c1c05015440e10400e00c07170001078800c0c22803200b078483c1d0400030141901e00d4a082c1c14400c0036a016004102c5051000d20300240c9285068411982440c0c40200200c640f00e0170348c0d80d000440170780504404284a000d100c00800283d01b4064988111408000309480e030408001003c03c0c0d131810b03000700801041d460802001c0900000a59108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 994807922 1250 994806672 994806689
    0x16140604050606190e01090e0d08010e0103020f1503090a032c040203100b0708041805220c0503100e0f0d0c06020913020a08190203060609010c020f090403171609 71
    0x6040120003550303113204107940305c0c141e05035130381300005009881d43c0d122240420218095581e409504482201c0801d024001c940f076000c0c01a006001505214010804194000c4c18400000700f0042045516810840d00410164804401c40080680c05174074a018085554240b91030107100b0070440e0980098101e141c0d0249601000040080707014003407407001030050264665445055003400d14090b4000c2c06130f0358020094250400220303005100b007501c159220b618101c01941c0c1d0017003110328034001550031f681c00c02d509500840c403a0340030700c40d00b4580a2000c07000118080c2e869107050402181044800381c9400812000c1010380d0000c3c000d41001f54020030040e682c0010742b001612180850003400075141c808034002c90000d801c01070720f03401242c0804080400340702e000340b1007099110440d030058000c4028413140d40194011104019141d00c024003501242007103001144075414119001c1d030000708144504140c0215a00f0201d4100c0043c0070081203042010101602401003441203144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 994809172 1250 994807922 994807939
    0x2003160e060d02040e2401150c0c05091503010e120f0c160e0a0f0c270302040509010207120c0201050306120f01090c0f0603180b07050d0216140604050606 68
    0x70255034600c1c0e15444140d004008001c1c070405010360702e544111141c08000c01300d2520310000108940031403490b040b205e40d4103141c0000d8040400c11900c03800c4400040311101013040001c43d1030b6541420b290712521140d80421074134003a840805003580c645942d410101d030000003002488004400845400c0701d0a109081d40e41c502e00d40f100782c640400101000c3e02906807220102e190318089110b02c1c050646501d0600c00308600188a100721400c55030010040384d4400c45c100c82038201140382800c188a100d13400400942d40c2d40100307013612402c0b152000e49035030000300e04041180d202c0043c00038600602e803224485565a0000e05a84006824144120700c003100a030440d613410030840c0c0c24408180000c3c04405079500d000e808022807401601d091a6044202280e043c1c4a403145107500c01400d68450200100d503114141b082901406031420400c08010014803841da0380010f21150b800154154400d10b090f0901c0221009001400111030b000241848080345000800c190007140454800300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 994810422 1250 994809172 994809181
    0x10c081608181b010e0f0306011827020a0803030f130606030218060405070203131403071a030108190506152b0c050a0b04180f05042003160e 62
    0xa00030b4a003550030411038070900301c440344400d25260340c040d0904400e0702c401c1c400725000000c0000203003061103015015401040108400040019851030b010800400010304402e44c83c0b40201d0b0000c2010400d501c0d4502100c920114205a02c4020041280764065404c1d03050409128840030800747c032400d4842500c0d2040e10500140b80e101000030f59005060030701c040056004041c0000c8204c40280c0b04901c0d110019542d640041704854a00c0c0b074207408140c2c420704042045035070212811115400d407107000c2c030100e44c842c48a290750341620081c1d80c0c92038881d85045511490060030300189200d166013041100b00262000030300540101c0c0200000e4005908000800c1290f0310340405d002080d6400511001c0110f42242154107841c060194884030f2030301c031024031990100c2803090b03003e0320204020401055543d151594075a241000000c2a038240c09405031080e03903000e64081d2401e1000030f070300071141800682646c4d42e40000b5005030080350460b2429100705420b80c80391403d02413004001030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 994811672 1250 994810422 994810441
    0x609260102130e0406050609010b070206280c060f09030c1410051e0c0304080a140405040204090c031a101404080304061e0e1c0311061503010c081608 66
    0x311041e02100b150403000c0c41e42c8950701e0b25180d40c10380d0706481a920f010086803082c14040c036420b0683e040d400650b4500346c0e41d9801d00400b03521241c03d9158280c01908039038802c0300b500250444000e00c44d80d0f0401503d0090030071004660704440400303092490070301d4800010707801009848507a504414440d03800c503100d6812904008003d65001c000d0307454101080030750010050101ba45210340112410303556a050940d00c06440242c0e400360a4072010b00512910520501c07a41c810307003035001512410b040e51800840c0076030b041a003228510325100c02c1c0505030294103206203246d090098034200b144c4c401503c003081040c803264030301c07000300205d5800e92a60f6141e550708407001018014112030f559951101c2c010060b0424804c036020b22250001c100b40c0d0248162041091080014107640c440206407026812070780b00502d00300c080c020080d010554a907800c1c003060740f2912070208401503080ca5a0201070840f118088461b0502c008a001e002c0030102000140030000c440d401e0201c01c584501c10074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 994812922 1250 994811672 994811677
    0xf09090e071503021303230a080f090310050a0207110904150f181218030803060120010f1e06060207050904080c0a05030a0e04020306010503161b0807020a0609260102 73
    0x4014508010741d20000820008004000c0038038840025440700307c1c0185240354841d80d20050141050b0030500152070075001810091040807002011a80700030440740760300007914000c8903040011540480c2c02020722090054080e6042002c8400600a14040e541d0301c6804403d01c042c0d0510f5656101980d52140140e4800030600d030640313404280034a002c0c50300800901e00c00324a0f034000342402000507141c492600003881030f2070780884000e0555980d01c004491a1490059026000c8900c03200160b0b0b0110030f03c2400c1d1505241c80c0c0106240e2062031180c592400c0c81c40c8050800c6141141c02c118499000ca402c8098403c2201c220016850b2410080e846018042060380030740107007001d483c200807002004015450300340e21707500d100e9546002000100d0200f16040e80c0030607010000110324914046510580a08609080e520494070441483c0c00c01c001e444101c0e489000000c908056103043c0c1800d1004000710300c2c10600719030034a44040785001215590103442400d0b4082c020300301000390107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 994814172 1250 994812922 994812937
    0x20030d030608060c09060313260d0608030c07090504050705060c0607090605090f22060b0315040b0112021c0c020304080c04050114010c05030d110307030b012c041404030f09090e07150302 82
    0x2010f450541102c400c1344270356403000305031010081c40c024000410507000310540c3d64120441d806011070300d1034007000c030000c0d09004100300c03618001c00901054170350710300c0b026042c0c10000e90000c00c3d20749400d00d40034000c00b4454002501713028003403007040e20942e41d01c008611481002d5500c0c1d05422072400c203c40b90303404811050b80505061203008502d20600d00040d43c80384c1c0308200080c1907440604c0c04c1c03000300c0703070151416800949074002d4041d85002c141c0051501765504840d681c82e0400007409442141d0b407404c4801c0050700006001c1012000803c8a1030080e0700446040145524220001c960003c50a4150341441080c20104092201c14002d2b1100e030210344506028904040d0541110766004882d0f05000c44d141c50f905000b07652080070b01c1c40d174526a0200b01d004440031510902c1601c0f50491681d64841d0712420603000403160341c200c403402144680c588068035a440c80d80a00b140c8000d401001906103004200301c0c03285d10010314102200d1b00f1198100844070801c0303007100617126254 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 994815422 1250 994814172 994814213
    0x2060307020a030f090303021b030f070e1006050940060e09060709140d050102070c0f2102090402010e120c010915080420030d030608060c09060313 65
    0x20040400e40100b00c1204140c480d03500e01846105081061712803001900000d030043c0c0c0714000312206010440d00252401d000181210024005915668134208803600b10020041c1c03041e041c0301400107000c035440f014082c00d0078031710f06006a48001c100011441403004507071500c1e0009440070020025100307081e4100c032001c2c100400030640d60501c05000300344a011a83d0000000240f540c10b408130b0a0760080c1280c0c2d84042c1c80364905410200c030005c0c2e200401d1fa11a46401003032001071130920003480198031441d01281d180d468034174403400708500e41c0d208120004442211143c8d849900b2441d03101c40d50b044400c000a5261800102c0f00c3c01c2c040003809d90000c400401c0031090000028003804400790980ea0192306640f28580780c40e0684209090101007000c403808940003408000603814803c80c075081000b000318500307000034600382c44072101c0303004641e0743d5a041c01160014000103922510f060112850304042c4408500e00f440004c0ca815400100084070340200800501c01c5141900e101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 994816672 1250 994815422 994815427
    0x100603031b0f0c031101091d041704081509060105030705060d0213030807030e130b0a1403100c1e050f03070503040c082a120a0209042a0303030e01050606250206 71
    0x74a0540305d10200d0714841401320707d044034001003d805441c0c0d034000700c101c1c8480e408543d869940e00d075008906020607698a11106010103d0350050400c080c1a00b1032a00002c04400e04110100c40e007000c0341a04054029000203405020756196101101c80c5040103010042e55151071008a83e42004143c00080542000040c25410f00d07a000c0300b004c0c40d844e030458056450880000c201c6007101c0f1111f50b007a81024005804000310401c4042c1002d6074400036007507645601300003440604031100803030784101040300d4007583c0e500000d25845015140159050461519504240c0025103000c000e100d43e0030880004009810810400230030700041ca84c11048920000510b40300c01c1f15000e100500f040c0040510955030010310f0883c000070000d40c4510040d01c0c5800842c0c082c003262840091080d034194072003d507110022550301d8403184504500c944030044590861400030140c0300500942c4074240c1c14807043c0415540c03582c040301c000c09800c4c0b80c0c04000e043d82010a06042e281844080d512001c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 994817922 1250 994816672 994816679
    0x1431031a06280911070507030f0308010608040507091e060608180304050f01201b012d0f09030f06020c010c050403080307031503020d14100603031b0f0c 67
    0x1041441e019078421a6030209911540701040b50340c010406410810190503441000080b40c541c2c07101010445180540f0310b0f1144c0e98841d180340448507030048603d080b40070004024940d0208015014080754607210401d81400d440b4580d032489107015102406958001c0a41000284034032079201210000041c80400d54614020b041e0483c21500039140c078520300007546044101104607070654500829008900d0402e0004440c001c808908007030956500d001d528a00000030403425010941a070b044e90402c05040c0c000400700403000f07002c100d41c41b001d50480182a042c0c1424030182401c04d20308400c001c01d42c1e103411160390b4851740c000340102069006181c01d000b03194004003007140e41071000344500401004221800d10940c440604000c2c002c0c401301d59801e200b5089441c0c0903031001c0d40d4100381a02c81e000605000200d00c07003110810641076120101130000d00840c12030240203c0b081200c03d1450304c001c0c00b003039040c1c10325606950400310280c0820000110b10225243c005980c3c880351500c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 994819172 1250 994817922 994817963
    0x61404060b072a03140f1e0322030209040c060e06041401080a022104060606020c13020d110301060f0306080d020a2607031206050d02150901030f11040303143103 71
    0xe01b90810103442c0900d81000c000da440300302c0044280c84003600210310b003052101c100742140c02d500d00c5240780440d0b002400030150703a9001c80180241d000d4840c04021521703180016040000811609000301001d20040110307188040060131100001c1c01c00840b19555039107207100034030605a40f006c80316035403001911880010030007144500d1191a01300700c22511101c00340e9480000305485a880505604e10030803125143d0040c6c01110f14046003c02c80c4c2c001c2108115031500260800300001302040e070b284c040740b68503009100007090100701800524591250080d105c0e4440c05000d801c402440f1559071520340d000440c3d0019041c83d140240e160403540c9030090554040c0c5152415660620300049407a1030812000607200e54001c1400503a1108441c4600780e0b40c207c540c900d414140d480c014041c0303102a6000302c5a0310740c01c0c80707c3e141d0384508518000c2d1440c000c900c1c195510000601c010803010b031003000040a000c602103684c0213a898640c0b6450b5a2254a0308010b200070b00c8140151034012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 994820422 1250 994819172 994819183
    0xb070903050c090c0901051606060b0d1503050606012d0f120506010e15120703150b0c06130c0312020304150f140309070306061404060b072a0314 64
    0x28419401c2c0e80c84008520200807000c40d0569400a001004200602107503004100801e01111280070383c15000d40c180e2070b40000c484540c2d02940c0300280000e0310310300300d114520a02900003d80c0d400d840c1441d080d41c80703103507407150010401070601c00c05075910100400034044420414101c01c04007054110703040e0008250100b13421403800421400304c1070044640e15801014803071003060359000e40407189078042101e22898070650041000c01000702805c0038641c0100c00f40708082caa20b000c03403954001c10b80709120701001d9021510040083c82501d243d000003043c0c0d40d40005e4082d00c075014030f0b42d2a040226045002d94401002620265130100e840d50300807010f001112441c2020b1184508403c40607900c0312001000e8400040040c00d4101d0407680314009036401c809500f0031030708116140d646440403600c0c903412051807940341c12105182480c050040380090040001d801d1b0410b03030701cae54410820405491035400c490f0791f44042c0098109028102200071900903482c030b0039040f909c00142d5201c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 994821672 1250 994820422 994820429
    0x1509040c020601060c080f070b310201092c0717060d0807060903030f36030c0f030c02150c060c09010f0305220308070e0904080406050a0c0b0709 64
    0x450030300319511856800410507504803480340d141c10442d0345590f5078082c610780c4158444d86030756406005220100b51002c8050744141064082c1000e03c42c0d88030031030010030048104079020542c4403088200182d900c45a010304451110803100c1003803a40030750031b89000101e00c40d01001d03d0203000070800602d0f0b00c041c0c07840e0052070882c40d2495030f0302d54600707025202504580190400404010800c005080b0798000061180645000a00780304401c105030309850044000c0d0151564200000155042c0c0c43c500303141d000016801050046501c1d070b005420b406209c1005000554140d480000303040c0100160850603078024003407002851003001131a180d402440003010144203410009140c2180d1000300c8405c0d040c142c41d41c042d041d42c41c0030200c1c003901004010344003554007440e075551607405445141d44260702c641c0b6410707032901e03000038000c1c00001401c105902c644540c20034040840c4d102d0003101c0c00d413011450499034a50031154107031424200300c040100000401420040182ea201014001750b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 994822922 1250 994821672 994821679
    0x501021204110a12020d0f060608071706100506070510110301090f0b031002130305150f0c090a0b09031e060a1404021e0d05010228020f0604060b010302091509 70
    0x2490b070940c0c03c1c080c080c85140140b02614890580c44000b618010f100c2001c43d0788100c42030140009651345541c00d5a14981c13100c0714941c40410240100c07204080401e06204030000241040c0c80d140005e03461980b401d11850780150310015484040c414280002d18400790740348400d00c980501103140c106d1551003403180108852400c0142041040c0c02d014600c81540f0080c01045400301e0100050029807084040780040d008400700040000c3d402e110404001c010701c01c5040b503604e442442040e100100500346407602c80b04101c1113039141d4500b40800183d81032a0851900c0381488400700c1d1034030103031001c6c11450800c0903061594003200042c10724030410b0150010700001e030101d540840e8000c8240d5009601074030050400400301707201c002c0181d04c1680105002d26060450b2070345801c9a100900b50002081004140b00e030900041c549076040c0c0b003440c40103059034211900203580380d10015100500c450b85801c04034400e42c3c0700350180c07a076049004122030108550868442080d61011050b14003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 994824172 1250 994822922 994822943
    0x140d020705121501051513080d0314091011040b0c07060f090e0c0c031209010501060e090903220b0f0904060603020f03040305030402030a1a18010e0c1201090501021204 74
    0x61610114910f00f2204050000c041503900700000c2100090306c0e1484100304070014040410076011002c1c10174010140c1c1009029a8440c45070010300ba542806035000e0444125814000d03802c100043d1308401c1009500e0004081c0c03500400965244a5684261081e10000c20701c100744c1361000c00c1040483c0c0250302d0340c0740410b20940099880d95441d03c01d60020030004e000003500211028002d11182d80e12005a900e8000d07044545145e1060686030b0b0b13031441c0c0d943d80050103410b07001442c1c005021001c8441810ba031811145c025541d124009035642801a00e01c10318485802a12984001c0c00c51924107075156a0660301d0180c0c00e800c07011100788600d003880d0001403500c0c00780c0300b140d002481d0411420f03d540d96a0324192540d1348050f000302d03094421008104042246903074403503c078240c2c0451600007410450001100e441d00852146050703450490b0b40049440e0000701040d40440c2501d104030401c418a2075240107004520f800b030070550000602c1203ca0028400c81340c45548074010385403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 994825422 1250 994824172 994824199
    0x1205150d0b0609100b0405121504080c010c02060c0a0f090b1902060c0a05120405030f0f0d0506040b0307050409020f031c0810060f12090c0905180a0c0e04140d020705 73
    0x13030034054441c51100150400c414440c40c2400b404010b6448428411a4004040b4642d00303440c0c07103822113094030b0a90f000300740c020b101142801040811541791000703002c1c038104441c10700881c0c82204481400d00c0b4040f5516454140100360f414010044014140d40b50040c124507445d660030001c0c12b01c1c00500902c0009045114440c058030842449940c449041c1a0486044d0000000161040e1030504c414042c1e0108220004001e08003000070104041e00c980c402c1c0340f207100784c80020b80941c1c400d40c2040d10041d00c0b5100000d0b8107040b54000c44003c500c00c00c0700e00100c0d1007000c44c0700741d5a4040c011030b4210014043e0b10828641400c08541c2d407105d055441c40c641103170740b82150148800040d681c60400182c0b030311030034040241062034040010780700078039607540450790a03a40c0008041c545039003c106403150003540081200c1d8019001c0c1080e000d0590702c81000200e40d026502e1603070b500d00049010b0250170041a011566a002200c0081d420344078069a6550540304042c8244e410300b40c2d2a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 994826672 1250 994825422 994825441
    0x18060f22080a18090c030c0e01080601081515070605100b071a0a061d0103020108070509150307051b0c1f0f031a0411040e0105040207031205150d0b0609 67
    0x8012150400a01410254044000c5680c1c164558006085141c11500131071030300024858106140003c0c3c4000411813000780c40a0031402e80c01444505100000c02002074990700308442c0c070340c0480211124106410f2010010b020070000c102c503a104698082116000c11207180d00480c00b5400c0c1703485981805d0b070340d11751012061180000080c19030b52800364082c0140f41c2d05800e42e03009401c0000101382c5580b40c1300421120300c9850003410125641034010003e558004588a8001410785003113458401f602000c0790400d0746c402d0004914440000c00075a20f540f24000b50391b9080350415010030441da03000c881c945e46241c01d80b582d900c51810700c600321302a81c01e00d078a041203500c00303a20f03480c4080e01e0720703803003900180000c0c441d40d440103903040880f9102d95150b129510700b1074241c40c1115152800d10784500d030002c10580096005500c1009240e02083d00982a414190040034001c141660b45100f00074403c403c1e1803116030801c8801800c5810841440f605900c075941c16101802190380c0d03500c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 994827922 1250 994826672 994826731
    0x60f0f05040207080f0331060c0912141608030a02190209130c092c0d0503040b1012060501081921201c0905090f18060f 53
    0x818080e02008036411700d09001c0c0207190f00190984040501c0041c2c6281407807401c0f840c0a01440b0140c41708141401c01c2640c0c4100c01076852186001d410280c204a02d071144070003814009006480318046000c0350600401c031140b00380c2031140d1100d51041d550304d44290740e50400144c10016014100541c21000c5140e10001c144540080600c0c240351208401d00c0807018001c04141ca0541011034003094000090040e80203820300030201d40340310b0b80c0c0d03166400d401d0b811142101780c0c15080341c00a00c0e02950b005064035009500306a82c81c1307150b00d481755000840c0990f5402402d6103403105a003801886000d40c0041d0407101240251064003c40e19407005560281100007130500d00c000b00d558404800c5007800300004c101c60300b002c0741e01102981c14400106030540744007400798054141d2600e8a40d460484e000c00100c40d0401c420800d007000c0004546410091111440300c05c07031700000f00300d082075001d4038a10700c140b83d05903440ea0410718040d075544a0200c1e43d40d15070729240880141640c124495 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 994829172 1250 994827922 994827937
    0x30705100b06032d0408130f1203050a0c0c090903031109150a030b0d061a0607120507020409080a0e0a08190b100503060c0705060c1921060f0f050402 66
    0x82e0b14a1640c8442000d00c0c0040080d1040030a42c0e603840f0a101d26151303440801d809079029804507500e42c2c5001e00e400034038007282c1e0011682045648001c010b410591008510b801d40d1500b0640d440300c18501c011034500340e0514001c0d00406070214006450000c6500c07000e0b10500999080c069807031580405038051042940741d03600074903216070308481000114090800c046861a001c610350340070340c0003e00004001841582c5941e039481c40c40c04102145800414002c0c410b81d0315505202c05900c4610100450f561030310180300780025100110360351350b444860604e40c40002240ca03818520070081100c1c124080860044403128004124040001035110400b0b0400404000d8916242c1d2070a010400152180e14500340b00c100100d00b50760180105841502500c000035111107150510b5490b00784007a01e0420000020420380e0601d201d50f0b0301c82841d504080c01e0040d65142c002c203080d110325500c0c240f03a1030740324a48400400d66901c9862030008031018854000d5555842d002000100e204440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 994830422 1250 994829172 994829179
    0x402040b0909060114070605160c020a140112020307050d0b190b0f0706060e1e060a0e18061008011506171e040b06130b01051c02090a08030705100b 65
    0x4401d07441c078901182c180d80e1058062600381162104c58400d035489400202c005c8030329646400400c0202030708498030840c8810310349401c05502c501c680100c3c0c6260700900034000201c007010b10201e00740e401200c4510650307565071f03411980c13031038040b03401802c0d07412100c84d09e101d050605900781c8203441c00114000c002c0c4e003801030035410b0a14084584005a0101e030a091066000b4070602300840c0d06032081c01c0003000101c01491161a214620551b1075007004040c0440c11801e2007801040d03250704410b40246c900b0400000f885880340703000b40082d060503c07001461440769100308240e81c00c03500c0c4420101c1d2141c0000f0f00083c200d0b4200320700840c40f5401203400144211124074a020303420201c2c1d43c0c006079514160082c0f40d000f15100c580c542da044806a0343c1c00545c000740703c039a0820340034034800b040540c80100120030500340002c00300d01c00c04001507402d0107003451108001c04c4580c100e4400000041003080c2d410b0303480041b951641c01442c000c2d03c245c040d01543e1210ba070628021140c0b4104000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 994831672 1250 994830422 994830427
    0x302091503060a1805031204020a0e010e040209040f151e1130070801180b0d020f0609120d2012160f0f0b06010c150e0c0d030c050c0402040b 62
    0x3000f0840040c10000840fa584408102c9030700d002ca101807004080840040c510325003d85024010f000e05c0700c3c880e900c26204c030a0b100340100030307075a5001c556070b800950440e08080c1644940c00c2070852080c0c5518003400c50780321450144004034150740b04420302c0c11014041c4101c501c0d000884000c456000200e8000d1841c01c1051140d00b0080c2105580400c8140390031138840011001e4842c03031010112040000301759443d0043c052145629a000400001c900051140058001c0410400071905800070700075000c3c080d022869a0f65441503900790040a042003c14040d541c2e80c059480e461004184013203561a02010240e5500c680c040400340f002800a1014800509114034140c1c007044800f515082c8805150000880103c00000824003a00700034a07a04001d0400da1140c41c0007030450f0303061003c0c024407000003414824805403440700b0300700c00248440c4040039040c24190a9040c11b607210b10b410600c0d070105030b0008441c8034928010401c80e000140614240b00403031203a07005852131282c05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 994832922 1250 994831672 994831681
    0x912030103060b03390607152c0a1203020310030803041502040b0c070e1003140106081c0305060306070c06050405010b060315090a06050607141207060501030209150306 74
    0x100d400c003c2d10342e40058100ea41c1c1400e05054281d401042202d41a035852a002000000015440842c500c036001220030f2464482c0076503800c0c0f9134901c40304600c06800d8540220000f80d86880060590001b5800d19802200390b04c0c0c410940c59803e001403c840e220003055241161502c00e2003582c0c4548404500c81c1c1c0c0180c1141c030341e81c07240c0c2c00081040300d1407160100c0e884541016400034000910501c40c01c65241e00344441e02034240081a0414801c0e40216010444000101140541143e070042509610f000c0c5401c1141d014241581140f174203446081c06186018003241c8110645407800d580401c42ca0b100c11f410162900800c2d2034440025041400d0000418000d510413500301d84141d00005000f040035001c00c1380341d0011942c00824068641c040a85814810003841c0c0c050f801500410846044c68001303002c1d40100c200c09002c000301250030059a013420460211414000c0c000742c1e444030180c0ca440406420240401c0b4001c0b040320001c0746425801125007201c200c0000c0c090300c039a969 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 994834172 1250 994832922 994832933
    0x50306010611100c080603150f06240a05090a0b0c1c020a170a02010e030f030408210406060f0938091003030905060a0f030b04061d010e0912030103 65
    0x40b4855480342801210009401c01e0300600c01e81c01144881c2c1c41d110000c0c6016400c26003441c0864102070b1681d100d10342000342c0310b8802180c46510010440d03c0c44840c4010424510320326000e008403020340d50b000100700c000e40b600039001e011000800c0300c1c5400e00540304c3c65070003081d00441c070a00d00d4607440080328002d4041e90320b40e0341c0426102441111260580c0d600c50031410740921034040418440000c034140c4003503080c01a4600c4a8258008515103c60350010300114800104040c10610003c28000100080e140d4088640b5501c0c1000450301c1c10903082000003084248104240d10000003000155181503020365402002e000105059a0001c40c0140a02d0145002c000703140d0b12000540440b156602c0c080c05019030703110a02010b8003429494090a012225081039205d50401d02070034400c41c2e8428400200185507182c00714803c0e20300c00110300a08115049854841006a110260b00d03508844460490702c0740454581203032528001e040e00c4e00740b0800b441d1000042000140003048 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 994835422 1250 994834172 994834187
    0x103090204020f1303170406170916091a0d02100e060f04081c091203050f19020109060b101205090a020d03020a03032012130501110903160503060106 66
    0xe00241001d03107002e81000c8160083d6001c2c500840803610010014020300c040d5540c225240b1100715002032809080c0b40024001601f03e02070702c1c1000c080d01d000204442000d200f400c91504141d48500241c50b21104c400e40502082c00091003050692405100c440c40c0a600004406030080c000e42843c03023040f40100c0e408211400003a810040400581d445003580f6030003080105890030145c403d0742e4446201c6801d06160201140c1086048941807200035405020403a109606091060b500c1500001060142c095802115030003140c2d41c01040c2441c1c3c040d0400700115100b82e00801c68071a510080086040d83c01c500000090641b00507a40b22040d81c1d44000e400c1703034062040f21651303040e0b6400141d02030a040c20440060308444400c108058240c010103a40300651b405954003070302500340400881c0903040700081d8014600d000b08041d100c07140c3c2114807564112009201c48030280180709065401026001e0191090314070002208060000407410f0b0f680007400340580781d1800c6411a60304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 994836672 1250 994835422 994835441
    0x702030a0e01051b10021e03040305091309061103011d0709050111070e0c04030b0106050304050a021314010f0f090e0703080a1701120b01050609030706030c09090f1a011d0103 77
    0x10240444c0313080c1440410041010109280d61000d0380d600080241003c0110751a0b06440800742c0c01c2c028440065000000e40e003100780c003520798903407440100340140064441403201924081c9411041c1545c503c1210046041c2c91001070400c81d11b5800c0f1801d60503654003201e942d0000348664209000541c1315400c0b20341d01002060032100d1143d01c6840c0c2d07142c0c082050310500161307000080c0030002c000c41d01700d150340182510f0408a007907107000d80b02e27641c4940c04220020300c40e85140d034160000000d9507000b40007020703100c42e80540968481c0f5125072425510b0044440d4202c2c0240300068109481c0101c1e551411081c010b80702c2d841c0740d5900c211403600a041e074523003031143d42c214920000b4040800076000300302c50301d01544286540d04000c3d50004060704920f000e0302c401c0241e00c1391a2030004000d411947e0324a40002e042c43c004034202c0d14100160000025241006a0f80c10240c2c020341012288080280c400b21101410b0401951100000c2800349482050060303050800c0d806030b030146105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 994837922 1250 994836672 994836697
    0x905090601090801061e080a0515041505070804051e0a0b18122808040f0c08010c050318060403020a0b130206040303020105040302072c09010b12150702030a0e0105 72
    0x56940711011039085d00c3e070b1504078010348800700d0002810445510003210081494101070443e00791039407240d5484140005402d80601c0038078000c641000b00c6104c0050b00000c60b420b04000d60b0500520081c2850341c00d4500303403041e205400003d8401c40440e202245403820290042403c0a01640e44204901c002424002818008003003507826100078801c0c2007040400003501540c90001c8060017000903606815280c3c071b40c659080030556103030064034a07500a40c1280e03418480301d0103071508003840180740d002000c01e542041c10341242550894040d5000d81400b42c95840700700110b490356942c40404580241c0180d1240328140045054280f4080c0c200303204031420300341160540c001c00c200790320a0780100c005031354400c00c100501d030b41072140f04007604071041c0341d001103c1050640b0f00140064819050344801c000c001c14207013403003540021803012024100d94040da403603082254903101d080500030810b040f07080009030214404000c5440c16003240e01c031a6915003480c03004462030f40280d40c0030f000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 994839172 1250 994837922 994837937
    0x50a120e0a0309181505190816210201140703020a0b1008010e0606010504170304031b0f08030c030403030c0311010905060123090f0624120c0a0905090601 68
    0x4103980a21000180700d0082c0caa0001552130800d0f19411804000c40d0380c440a490442c408003070011511001c001c40b0401c40da44010381450196544820100d98080c0c1c2e0644038401103000000d6121551508980d2541da004c2c00c080002c12140c040c0b00c00f0240000c1c0040c0d018114210b8500c8040c000e810158042c0c811100514843d54604884d02020703130300000a070314481020401c82600340511508221204040d04480c1042000a455406140206c40c00c0b04e1003510300c0550281e040098500441d0030086d000d690503103504428a000701203000d01e00c4191142c400c081a40c0000004072415503000c0030083d8a01032440e1000c0f200c001050008504110b11040d5504c8440e90074000d4901860090021381402d5140220281f07806904115150081811b500e890a080d920b614000b64090100010328405a40314000a40610200e150f24031358520749900c3d44540c54400005460f1440b622152031000e61941c442c55034142c003480c00d691000410b0802c00b808142488142aa00641c06040151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 994840422 1250 994839172 994839191
    0x9040509121204111804140c0604092301030b011202010c080c1c090f090e1c03060f050108090c120309040c1106010e070f030504020f120a0c090c050a12 67
    0x31069440251078000781000d45050200380702c218840007050320401c17541c0140001e109506540f10782c0d0014005004a0b804100c0d04070280002c2c0050600c56500800d066502c50711020018028500100011004e0440c01c040c82d40c818011161181602d8020080b081181e2070714025280d02c40f90440200e04004ea420350303880000f030050b0090b210200c49400a03040041c515a016078001c0d04d580020001c0000b0031408210700b2038000d1f00b607029201007a81c04a10f61000b040c9403454105100c04689820b220729600141e416895440030069800a0030340640d0f5580d900700454500b0b00a0703d143d189030304881d0585009182c2a07000300e01d1058000184c90508240350002000c44210100e80000304030000c10f074400c10700080c0300352400340c04448040a002c3c10189002454608054202d0341415650030224095640b10581152035a5004008114035000420314945500d002c00003240d020304000c002246001180c0100ca6000a240c2d90303c1d030420883c01011110314039000402c088040da90582c0c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 994841672 1250 994840422 994840453
    0x60109140d150902090c0a0f08060a03050a03020604050705032b0201140a0608071e0e0403090302060304210e06030718120b0f07020127060f1b0e0405060609040509 72
    0x402d00851072580024a101c81d07005200307040c080100110b1800c0810480703150305581020304001030385640c1c40c000460303039107071000324188020740e400c06422445a0b051800415500060b018800d521500c181d84030b00b030342d4000b85a6100410b070b4100c4110040011140b070441b80700508411022400d10001c84c5013198030a8020404909448145480317071507000501070410f0402c06100103004602000321403460054014180b4000c0740582c149107103080c00801c3c00d040c4906440070185400504603952404c140c42d10011226070311401002d40d083c40b41c0d80c41e58841c0211310150244a001c1d254500d19691910300311090015020b05c10103030080032101003a45a03029101c9c2542510800c1c844006003002e18429100d03100007041036045a050842d5030826400c40008100f40b45507002421803036440900c0c21501602c400e1044800c5189800281c0075240300d804640c80b9900056102d0000c000c00080c28081522030840d142500b0010802000c4020b0904e6400503a0045901c2c0654064040c00e00b0303107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 994842922 1250 994841672 994841693
    0x203120c120a0b0f030a0c0e04050307120810140112050612010207050303010f051f0e0d0f0b0714070c0e0c040b0c0a0314070506040b0432060f060109140d 68
    0x101c9041c60766820050201e0600803130209090342d0440040c80d4040a81d601d070440e49a0900807501d000140402140402000f002503a41240c0e020b20703080c229400b030724001030250008031010001e0381f130703480342c00500703540d40044c12050004180c1d581d01032a20341051941c05080c001e0142c50300001c0044800c000d50f01c0a1000d040d00911400145550754903140301991207442c150403082c85405011030b2002c04881903083c000103501c0070706000c2244d450b110000b40400541c6a8054041e40154007000100081c0c0e040c0c56108240c29210400f00344d0900e06403003107600902500030311956035200140305460a00034400d600c840044981c0346403c2d00e840b013014440d04400c01080c0c50307078405900c0c40105500b00300090414980d03542d165080104540342ea035500c45c8080d2010703042103040c034081001c0c41100c13420100c034542c204003210a4040c103000340c85041801e40d40142194040c000c08240c032220f5008041d4000c10b0f051350f980e600c0b0b5040c1215034105000180a8a0b07010280f10701002c000340d101f04d403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 994844172 1250 994842922 994842931
    0x71e0801051e1f0c06060609150f020a06021612081504050408040b0f0315061e09010306080304150314060919060306140a1404080f0c0309030724030c0203120c12 71
    0x2100710002c4c0c0b0301d2412400b43c030460342020f000d01000c100c0c10300071240c6c20003800a001401d031504c0201490b5034541641803c0e1100005800a400010100212811003420031a0903218540202c141280380c1c804840380903054900f003078424662607480c00180b03040c0d0406c48c3c00501406603103240036529903003000240d2208800c0d202582c1e011003004442040040720341903a039000d03a015403034128031000040c00c507940395003599200b11001c149100c543c1d00c06d501090140110000310381c2d81b43d8544019120b02c00c00901c041c40000d060048142038500b0140c800c501071540070b0440103090301d4048000810441840c1a47c00c0c1c1f65a6030b1002001c00c8241c003c42a05011100030318041341040a602c205a49012a000e841d1441030303130034000040da6107030803282c56000b00d20b52186c560045071415403c501c50700c0e82413945481008000704660514503400182400800c0c022502c81c881ea4009030b00360f8004460100c05600240014099135010100d003135072001030203081600c1c01d12140441d044e9414141d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 994845422 1250 994844172 994844177
    0x305060909070303020304061110060b0d06061409060f070807030806120f0d03110d020d1a0a060212090a0e07020c030d14070f0f0803071e0801051e1f 66
    0x50102504000d0219500301500c00c0152044604540b406541e1b07114521480d0100880c80100c1c002249042c81051103084140340c0c01c0c0034255554050310340c1500a0680c94103800d140074000074030075000d20302d2480c450780403420b10340c145040b204c01c204040d0010030000e03c61a40801000001880b20001070031124482d840e01c80f540d0070f10600b0b000948040d08042e04481d44078060044401e03000242d40c080c008103a14010450054542815229004940305500d00b9400802e0b85070002e100760b0884c2c0d0300e0051419110301001c07102410011209054492103015070080940a5a91030194000340130706040a000500510398882e40b001441070103c4482e401a0000700c060302542c030301800b01201400309442c14555400c4000e407119164400c00b00c0040212139544521400c000000e0038846003ea0084401512032403c6038000c0c0c00b00d40c40b1403900c0300c14001052101c1c4901d012382c50b91410380d54090081c400107154025488098504880420380c8030143c3d0a03203244c01001c0362001c915040c13059 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 994846672 1250 994845422 994845431
    0x7200a06020d0917280c1209050d0b01051f0c030e0a0b030a020304050105060603100506090a0915140d0308010306050a0e071d0919080d0e0d0309020306071713081903 73
    0x1040440d06008504424841ca144180400114141c3c8020440c82c840e802200746070092410541c1941c4223403a550040f42c000340c103080c105d02440500845541282c105070341b041580308181203031407994036240c0012004202808810004203100301c00e82100440301a0081008035103c801c82c034140c0d04229500340d101c94000042104000c020701800e82c002c141a03416608500f81900b0011000e0b16500401d07001c0c43c004200300c5941c4d916049044005d213104041049141035102c0070f1140007600d80031300071101c440020340d094103080680b030003c030a0780c1641d200c00083e425a82d5000180601610361804192074007598078011600340481c8000b418a2002103043c018045510307039082c68014010496500007001c01c0e0b011440340103c914510340e005007060760320190b402c101c8004001807c04040c0920900101110554160340046003150017281290521790312080e04684800201d005070106e449124046160140c220f000062010300c6044000e084c1a146000b04c603901540d440c00c240046d0b00c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 994847922 1250 994846672 994846687
    0x40e070807031512111921080309012c030d050a090506090c0a240e01091a040e24060d11030a0f06061d191205010507200a06020d0917 59
    0x41202e4444840e400b0b499000e5010580720080d5000a00da01c01e004400344488100202c80c503074000d1f0445080e501101c40c44d01d030b007800094a070007880003103905803d09400f4650042104400c034540d440c0100c2c444021444c1140d28951100a0140035040c40760280d1030b0060000080c2c42409054820090000241040381032601080b0b40382c805076100030116581102c00364100d0743c0002142d55500d0890400504d2984000c00403244415180c1c02040c0d040c50585414850352000801001150808512142251104211000031402c1c00d4880e405040080d0050480e609145002e403074009410b03180025013104842400d00e5603402103e110614036a186418002000544104030140c0240d01c4d1900c0d8042078040f2903003401d090f83c11124480c07864040c1086007125403030b42c500050074444084071083d00316840c20364042c0005840a001088848403020301c4807034002d520803030034900d41e4001c2c09040a251a01c00080d40200104a9040d4449201001088120710701e010140d0581c07542c160b90b02d42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 994849172 1250 994847922 994847933
    0x305041211090a141303051201080a060f020406271a040504061403030a0503131406100509060604061101020405040c091e061421071211040e070807031512 68
    0x707004000f09107061910091006009041003c50350025a05e104191520f40a003803d0f07419000c1c0d01903410321542488004a1716600220300080d0300c40c41803201b4440046c540720388000340e004074010140011403040071aa55559024410402c0c01740b80c50507035882070780721034051a0500300c400d005607018038002010881414144104401001c0342c100e00c00c2c4141441001135164403a41010707000b00000071000c00c91101c40118421801a031040c4501c840340007001c055501c40c00c0469800820a09041d0001780b2030400507401841000d0042402d1728190510f5000d0350402c840c0482099699400c0c0300c0452a500d03584150040d0064513115204050b140c40e200c0181d00311101003404281c081140300b0000140c01030581f141e91a80c8200090301d42c10149110800c070192404c2a03480c0c07050b090f05104c240c903044025000700019240043c0403081c05044847c01c148540d2240b1001140090000b40342e0394030826049800c4841842c0110700a442c0180c5122075504941200c0044c82d0151002d170200722 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 994850422 1250 994849172 994849189
    0x30402062a1e1218060a121e15060210020c01090f0309030c1d06060c0a020a06030605130e1005060a1203091401230c030f03011202010206060d1e0305041211 69
    0x900b150340c210700d8014911440d085070008103481c1402898046100c03010f580c05000c1203c4940da8011f0200812400c650301640d801007200c110040f440e150080303030480c0300a985800c2c0144d0302c1c960000e203500c686115400000f980008160b003082c2d5038803043ca10020740e4220240711101c0c02a543c245400c1d095080592143c1e0700380d80904401410030510b41001200c071403066911040807a0500c1d212000d9000036814018503400c000c1d40148040d40116449415a00480a803282039a031450342c141031101c400103c03003080741da500c01079002d1040703120543c08903080683e1102c0068411900c5698400e2080806035000300f08034040350711380c0c20500034190707802d24908001809107410b41221054000e400342854000501000e404400038010f45401c6042080703034000038a04100c1540e80d81c0d04d4000c12400c00d11800228014001e1401049036460058503510607542c0080000c1e00000f4603550551036822921b00440034004107000000e0b5011456900c4036280d401510343c8891311072224100328490 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 994851672 1250 994850422 994850443
    0x4060615170105010509040908030a0e070503010c02060a0f020f030103110f040501031113270c060507080d0b0409080304050a02010f05042709120203040303080606030402062a1e 78
    0xd2002018240c1451407589541102c2c0c00b82402a51414504045000b030500c0480c041c05d012400410f2212407080b80e8800441482800e0580358000c1d240c000300340c281c1c4c0e4043c0405d00107034490800314080520b25480500b020a20350401841d20302c54501e1442c00d80c1003680203858611100c0090b08440c1810f4002c0104000102d50801c031a604640d258184500c0140c0b20300d00030076241c0c0b00c0c200350683c2580980c6076101d8a4120f00f51800c002c0d00c00c15810f00300128102c07407026003007000103103041c09482900d094550200c801400e0920032000100242a0202d43c140d21079100d141110104502c18001c5004038001c1c0090031002ca02400090019080c88000348c0400000b04800c1003100c2d810b00c00b829942106200e89000794860000383c01c00740065240240629050440d1120074540006c0140101e901c6074032051030541e1580c080091500003180c1c060b410980030014400340901c080c0030105000319490b800b54888a94402c3c9500d1b10302080c1240280307464000040d15074140402004550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 994852922 1250 994851672 994851677
    0x9241e01060807120915050711070b0903011104080d052b14060a1a0c070b0a0201020301080601061b0809040f0e010204180902032d0d0210050c070308160905030604060615 75
    0x45d450182e503201450780c2c02c01c00039240d582ea500007080c042c51140810601c2181d08208444029848941d9a50340341d0101540300d10962900300b44085c0b011101040d542143c03030308006000071a50078039054510341d12901004280d5a41e0405200440902001d10003101e2500b00c0e0008200356180c40081a404003c3c2c0081d108950780101005200c0c28948003000a018410303502e0303110a07007844824038004c055085401c20240118251016560560245041b600c501e07048944d9a603031400c0070b98660380410917100601c504510100c0114141800400c24040043c0c00050200141110310b4121080081d9002e01650001800c101002d0301243d1a003d05003098130412402e540c135030010b561814155100100c00c000703501e030242040e51007009903070340d9201ca40641f00060391840c4001d4aa0440c4003200203002d1524000c6421a100d45099802417030303158440c8403ca40b242d0b4000361003101465181000c019000d007005c50686c8060000a008034840e51010480314203148441540d440750324410000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 994854172 1250 994852922 994852931
    0x3041101080609041113051602160b2a0a110a0609050d0b0a090b1003120f0f1d130915110a0f0509040614010809241e0106080712 57
    0x455583e883c0d02c082c2c02a07400003010a26803940d03000321302c41054584a007003503180303084100300001301c410b44500c04002c8143c0c00e80d4200141d030220004520f0241c020740e50b0a081c103100c0e070000000c00c07442c0252030500e1a0400c0440094540c221841d01e03041080c01c0720078804c0000d05101500f405280e81010704901e040250099003048040744150461110141c02d0300d10440120341c1803010759019007802508551000307c14604441c64210001c064417040ba04080580136401e0024800d00381c0c49042c008503555102c102c1d0314207404070307003080110080340c4006000d00711000142e6180c04035104140c08400010a8448140c1040d14941d0702c40c44c4031a421070700300040700c80c10300c41400880b1401e0449007421410001404c20850300e42c01492001d0340c026140680100740340d1048440400301c0c010980c0d40f03070103e9a03459141511000d01e0407121450182459107c0302a0010b110043e90045034900b500c00708071005400401a100207a100b0302c049540c0100348846181d100e20030315041c2e50a42010f00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 994855422 1250 994854172 994854181
    0x12051305100b010e0d02040b09041b0602120a1d0303031f0803210c09060315040e0c011209050a0506070f020d0f0c020d03170a24050a051012020f0304110108 69
    0x30001e0714440700140c45005c2d000706900440d90ba43d889130a02007005442c1070722074941340c50b0010402406450288095082d02c2c00021141d00c00904000040050410207051000e070a000b694882a05110350024011940c0021001c0e20200055480785e6450399503d142d44601500b05400d07295203030410700d110740080103961088107603091a40c45040504140001c540d07141e4800320414014685000d034400c00020600011007120700b803082605034103c400f00070420548100d19501c80c08148035a001c90b58201c86203a1000e00c550140300d000d4003e00c161905100156522402c2440481e00d0401044511070000c5003158100304003c1801c583d4103060016485903440501481030b410300003032103201c15145c0d5000301485070942483d90300c00c14013030815a05010b8108009808503031540d20400e0064030038032014031403141d03140701102c0c0043e1440c00c01c07a00305010305c02683c0c884c46070340090190003009000d40550354030040030044d1003442c180c0d48900701446e1070002e1030007911280c2d04001c403c00510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 994856672 1250 994855422 994855427
    0x318180925080d050318010e010c0914010c06020a020a0203150708180304140609130b01020c0d02240f0d1a0109060203030a2703090e0603011503060b0112051305100b01 74
    0x22418443d42c2d0400b5a180c1d03881840071004038200700e1150903c0d50800fa80ca1070306280540010007015220b0720740d06e042a80365030380f4401c01c03894218203034000390141174000e000c50110350041058000320702c140e842c00306203a00481e01d8075040410703000c07e0f1194007040081c01c542c41548142c020503040d411400c2050070000e2140c0d240114000c44100c802e00214940c0251307150021248440c1307020b04003450250720900c00e6002081d51110007409402000903614031440c0100c0259040c0354001c0c0b103a03146002c1403d50050074240070120f8100c440c0100051001d03503888002030901e41c034a03031030046091004084501c8102210219075414400741020901400f074022060700e0340086940400182d12a119201c4003150849500c68070166100b6004141403652010052090300c026100380303465500c1d44002c0c1422500603e400801e2110510003d00010b0304540010400d010305140c40c0c640212008031100480e1800e0360a2580448410982810882d081c80b240e5050300600c036041010011200c0003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 994857922 1250 994856672 994856683
    0x90111071b0315050901050c0406020a0303150519090b06090a1707180b0127060507030509090711010c11060105010e01090e13051509031818092508 65
    0x40c000d168002070784807203000303441801e8020b5400040b42c1501028024041c4000c2c2802c1e40e6615455080800140d10a00d808044408540790ba03802007459080d00d0f18114010002100c0c10856084400c400045907910350303201c076503100e90b80100d0201c0903182c0031002045a481142940c0a10024081440303e035450081240482d0030381991000c001110040036030406035190040a2a20304040c90500c038825035031702580c1d649174281c0390300c071812131407600c0340341c1e028603c10300c0c40e0320112410b60600441d44208003030701004c0d1003030a01360f00301545c000004076070714012500800021031302000c046840909000e6820751700e10b0740c2810f0502003806c140998071071205000f42ca0500184440c070441e9644200000e07001010041151006800d100ea0b03002d180c02019281035a60303103e511000269510a10100350003405404d004614004900482c040380352522095140c0c4106000c0d2004001e074010b04525201c0d82d0588040c0505000300c126444c11007807010045000118412418009460001074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 994859172 1250 994857922 994857937
    0x6070509060901030e060c04150504080706051c0204030302060714160201081b0d1a010809030301050d0f020d0f0215040e01260d0903020102060106080601080403030b04020c120d05090111 82
    0x2901560b40c2c100e040140c01a118030020f80c1118480c81003000300300c500fa40c01504c1640d050002503c918503c0c0482111513020b0350141244940203a0000c0140c42e004038000c00b403021041da000004c800080000f0b1041b600140d0081c1c025030420780c10040125480740700803185c0c03404181503c0c200b0805102c4040c10614001b0300905010580000c100c2040601c0d2003040c1e001303c2d2a001da83d983c410141c104c000380c1050310190400321030111102500b5030184031903603c00c01da075200441c1140c0c43c01c030400401c000030500568005403100002c2d00540c4801000c030404501503a401280c485040c030510540c058500300fa030300c1540d001c0c0000e2009401e0154140d0464030711002135120b0220701c94121020003441e000102192158038030a00c0700c035820a40c102e040f00e000342c0913a4096070341e0700401d407444034044460500154032a000500000d001e6400074041140207400141003081c1071502929016201100c000d041e807002ca0100c05e1000d4070300840c0d0344504008004d00c0804518051510180074006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 994860422 1250 994859172 994859179
    0x506060a03110d0206090d11030c090403122004091d01230c13080703030f03051e040c03050607021b0a08190f02040515010f09060e040e1002031503060906070509 71
    0x3d140f841135555560a0341c80c02da00c000c00948400e12640340022400701c0c0c0c001168020b00a41e0000c840070320b800080e0318400d0b9019140d05c00034031030030034140d0000c02c44007400030031040a00c00a0f02644001e02e02420203404205000620224401c04880c3c2c550101025404907030304054004031840b00d1072132420300700c0244a12401c80c40c0c4803040c11642c1400b0b0f040d01585080c3c61880002100303200001c04d0411240681c40305800c1501d0014100c1c04e60740d0487d802c0f2a9942c1101c0c025000e11103408406600c10301400d03030508960b80b05c1c1d55041c00d14000f40c1c2c0c0c5400603445801e0441d0802e40c48032100740c12000031110710110070310381903589413138840346070650020001c0c104944090118405039620500d500400030407452601613265203041303c03140c94003400181200280c41070540240612405e8034101d03294081030554140c10040039145c92000808c41e0b018400d90748152100b903001842c018103d0400030003003c14020300341441c18400410340200c56200034144904a80c01034200c0c5c0c41900c060703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 994861672 1250 994860422 994860439
    0x20606090910021b1516090302150c24070905031b010c0201021e0102030103060f090203060406150320180c031909020303030a060302041b02370f0506060a0311 70
    0xa0900f82c0744e240080d41c40c0f116008807032810310f00103514440644a2410802d6481900c100e010044070560f4030340c0402508844158120940719040d54050007044100608403045192006000081148244945030140740040b060240c015044690070003c1c060580090810304403851011442c88100300783e050500103104100c2095902c2409448003580910b03c2c260a446402c800c464002e500900c01621001d240c4030200001c00010b014100221750014010201612141c4840740181b403d070486014035440c03513a001000034104900d059102c0b0080a01c0c0420004560601c01d5981071251241459040c00d020031a07901d9050342507a03081040b00070200504407100036200c00030b140b009000f0354103200200410001800d6074010200360791003985c06101192501c200c46144010102d01c61780580c00c0403c20405c6102c030010b4140030980c2c000c0030880000001d00640303100030280b080c25252203007100110400c0c407404009503a004003094628440315451500c40f0b00140e1b006031100f502c5400038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 994862922 1250 994861672 994861687
    0x9190b0c070f1208070c05030d0507030219020303010e070c0218090a0606092a050f07020a0e0c071a1005040203100803030106090302040b1e06160609080a02060609091002 75
    0x100d40548100c41d91100781201e40c15910f003040d03258000c088101c640019061000074a2041c80b805020f5401070340440110b082040c511700d84c0000d0f00008040d036040641c00d1168100c11585035108004840c003940166a895040c09044814284001d0810040c42040044500140c50b003049420246401c04d40308070340c1e80c0795030014504068651a028203018142803000c82d210110364404188602c40c0180c04080c10310b8038800c0f50701c42c246402c108010610a01080000c01000700003482514070003404105442d071146a03c0100440554000750300600200b903030400c03c079500d45c131300700404c007100c20001c940d151000e8400e441d01000d005941c0955000b10106034500d10007400034014100e104203482c0c5179a101d09d03004045590a11091307200c0c03030a003522207085050186500172048008803440742041540b00500070a6481320008c6010306000c0101e54002c0b83c5113100700c0010340c0c8a00c1c0341603500d8401030402840d00d04003504581c841e014400510004c9040050160000d40000700003689402c407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 994864172 1250 994862922 994862941
    0x11a030705180d03090602060f0103081b0c03060c0901110714011d090c03091006050a06030c020a063902061602071206020a11030304050a0206030408040b0d0b0909190b 74
    0x14800854225880c011840f04041e0030164480580304250300710381e030960318404c11400002003840081d1410b1802c022304c0c003003917200280708031010500b0011144802080e50200c4c2c548501100ea216004034046840040340d0303840030032600c5600d02000204015814110001c61141d81c0381803060510140e001e014a003414041c4141c5442640203100e03981e54a0a8503403d03050b80d00498940007075004e80400c50507600d00c68824031003a9000a808a0f0040382004003d500400b18101044291711415109000059541c0107818803507402c0c1594182a6115011044440203a1441380c0c50408410b0030b16921170b640000c0032588a000b6440070f14100c030401d4820390030044150000300048000d07840013414001103800629203181643c0e03031038400c40c04003107141d9124042510000c24035000f01c00c609000d8030348030340a150040d00800b2600d1030305980b8030034080c19500c020303221030380f613503c0307140808071031901e4121140e104511034068076484031300842d1030101802c20b640c010407009012020800030301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 994865422 1250 994864172 994864207
    0x6280e100909050c04050a02070f02190816051f0c0f0c05060a051c050c1603120911030f0c061b070302043e0a03050901090821011a030705 61
    0x1403084000c001c2c0d1421410859203440c0c0c50341303c041c05142040040f85c0c1e1360b043e0b40708071491036030020400000d0041039820041803a01160108085088195000c1001c050611003001c02c0c4080488045045103404140002ca035803c00d8081010560010b800c1c2c003080e08051110342c202d078482009955890b40e0300c3d060400340d4980e0002c50700480d02055202810760058000d1034403600994000b09a000300701d038480c05442007180c0c820a61a000d0140042131000c040b0040d100c0740c03003421710280e901c100006100407201141802e941c200d542c412002c4a82c10140308854000891101400d1300d1400131022171450700c100c0d60103c0038509480c0c1d040c100c01c2000d1002e0320295170300074400d03c45035841d160800382e08000990611b40501d0044489840c0721442c040b20b25102c030f0700c00a024100340d202c15041c3c0c01014001c0007201d0315504c1d60b001c00e00040410009103440344000c100800000c80400041604100c141c100304156504001024a100a001d00303980d40443c20b403030501c0d90307045c4001800f0500d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 994866672 1250 994865422 994865429
    0x7020a030b010b0a030b0d050d110102040909240606090b09130c0305100905130b060103150e09070b0403020618010c0c0306050a0f0b0f3606280e10 65
    0x45201200104800f294100241003122950b501403100c1c0010300d003002103054030744100500799801040514401e42c0224202904d100140c00018207140d950b02c1c002d0141d40307440000b05c508440090303e40403440d440021074048168225000c00225080c1240684048614010100f01240100b07000403150784820380080320001c504410f000700010000050050401551340018031010004042100c6085126507803180c2c00f50f1000d03100200617901e943c0805c601c00707850039042540301d1210745110755112140c0002080400845401403901002c4941070040d560031a1201400411042015a03607241c196901540da0310000f180100c80500103039a0540c010400a00b1030b0060701c070000030300c0015413000c4e104405004042c401c1c00d050107005000c076195000181d9000700c0d640ca10030f859090840e205020b95208045080c0720f2140d02d40c60b0590400b5052000d51200740701c10402407a810144c400103810407180b020447c00b004526030050380405240a48090070380303880000340c41d0503180b0b0a0300004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 994867922 1250 994866672 994866683
    0x60915060715051e0f07120608061303020c030c03070b0310081e06101d090124030204060b0301120305090a0302060a0809010606081021050118031b0c0b07020a03 71
    0x1003902c1c01e902038040c2c502140d000034101d48080510242c88001407100380b04101c0d45082c8a203640d80d1031800d450040030065000001659070740046080c00c4100065030107030b60340404c0100c0006841c50000c8c9828091540c0381d000f504108007400c070a8400261140540302c45c661441d40380d80c2d8111740020204c0d002e82c000d01e414424008a1000b402c001e81c04510016441415940c190f5234491880c0c0240b0068030074101c1c410385001d07040c03902c1c0080005060b04a03070104008a6100a1544403414000041d00194540a0242d00c10000c40c80d25200300c500a018903100141150f240405105d40c510f004c2c88084c041c007c000410040584d5401007110107154010302c074a0b15500034000051040b2422241c0401562810f080480e031240240d02451250b4803206c0482d801c03600b04581d41e61000b54180c0c40b5102d0344074200003640042d10030b01a0015005c80f52804100c1031029050040040400911080591491802c440085803160585c42c09461074501c1080e078880300b510210340300c80603940c400b400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 994869172 1250 994867922 994867943
    0x111c0e060403110706081501050a03090b180105010f0b071514240409020f131509020304030207091401050f060d090506070905040e030301091d030706140901050609150607 75
    0x30190008500c00e00f5002241c1243c040e59226074003907502c07010030307120417101240d00900c1e003415603c100010022028030b03250201d41e0fa401946e840e82078060a44207000908080803030011108c0302449064010705c0603020300c070f120318500341c0300001d9403080c40c02c05004001510000b03c01c4040176042001148585800f0f02d400e40b401c2100411035421081c0700c8602002d2502c8020350710701c0c250123400d2031183c000340008844113002040000c02c082518810f1802030302c0f0140074802d00000c92149006140d99040942d80c1c0c94545402400c00403103030401c1e4042c80c9480d000700c140528444c0700d0342c1514019921102484014800961540245600c1c01d90031810080c1c07101c100200401d1050040c030840e00d80c0270a940d04c1d10204030a03107801c81c4038408242e006200402c4000f259410070041c00c108140c003211081e180e412403d08541c00903a0585107682c0f030f14881220701d280c110890303901c0401c100c0200302e0341c10180002084101c000d040e030300d190b452100c40e0a2155458030120764110b80d02c40301114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 994870422 1250 994869172 994869181
    0x5210c040e09031207032c0c1210021b1903082d04050a021918020d020c100515090103020d060e0309060d0608120a0906081504140415111c0e06 63
    0x40140c090302004082d47c000101c400c020b6825600d10006812501c040544501e50100040c451488a081c4500415104032000b1380d80c1404588020580080c01d81700207800c0c1e00702c0000051034180650103c51202e082c1701c031039102095000110a8000070a03080581c011075400140411412042214610000c40d0505102c1000400544240003510a4a400703a11212046589489070650f01c14040310141200c031103514241b003a0b0040880f030511113030050602000305000352400011028000e16103527580d003030010940f89010a0190200100c485402c15030541e4041800102c20050040c0159100c20203140b0141c0f062080d00e04200340500340765110341000d4072140242825110302403030f5000d06100c9041c0d620710030007216030709a9661035011310359161080484180e4801030090201c0650b8003010091540c2c0c50140c4004403c030210f5850f15802e140c2418103902002c0310350070310801d2409602e00e401c0c0b8070802c01d23280100f8005041542404038082e004000d0080d03511240400d009000800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 994871672 1250 994870422 994870427
    0x1b06270102192102030105060f030a1401120515130f02010e0415030b0603030708072604060e0915031b150409060e090706080402090a1b05210c040e09031207 69
    0x340040800340c3e4982d010280d401c2c0301008a100030300585400101c20403500028508800c02190884000030000401070040b030401004032400b0f800450b070039080d1b8089102805000c110181c101d030301d54000d207800d50620013134000700401000401090885000c4c2194190380c00344240b1a410703034003d0700900000711400d000305480001c5000c220b481c00440801300302241400402d8034125a80040e40c145130a076552101000c400100400d0362038441d8907070b1017150000c0e0a00c09080141410f44070aa80090b108040020765000204440c49000680440350141c3c0d600241240d041d204c8812829060554800844c14801d50b0041c0c02e25000000500020b403103095501084c201c80003250030310040e884d403281e110b071901414071030b00c0f001611100126001d480c064100c540c218512110004850844000810102c0c98055100d070105002054901d604120510420000d03007038041d60b2040c501d006039800380580590302034250141750000004140050401c2122000b18007008600301d54a00310500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 994872922 1250 994871672 994871687
    0x70e100e010914060d021303050a0b341206032003120313060f140f0106080c040e180102040506030c0d061a2b111b0627010219 56
    0x10070700040c0001c40020b01098610710b2a210b101c2c2c020000f600e010311441078403010750892074800b080d0200d001e000100048042000104052064000d4030851030407038040e43d424003500c1c8680035200c4441100c4800c815003901c500d80c44840c6070070188071806010207090b00030803480c2c00080284203090385611810306005551085040110103c0e200c0100c002440440c5010548000c010681e88082001c0094101e42150441c0d200e51080003034010244d50000380100400d903226022003d8000c01400074076400820940e1081c25082124509440c04003080808a0020300282c0001c0c2c0d0040348036a60030082d01280c2c0101401854280c03030b030402e136601e03100c03541c0704215082020f4640280041e0a100403817004008050300c04400e410500c0107142ca924101d42c41d00030500741c00c1c09828040303000d862446002a040b0450b550b10791202e070142a101e119005402c1c5450b801e80c407070000c00c104203100400b03100c00d500c16000c1c2c10107050300c64074020740640101c0c0c0412803005070503c502880c3c0ca922590 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 994874172 1250 994872922 994872947
    0x110f16090606031514031633020703020f0d0c0b18010c020109090b0a08060c09130935042309010312110f030c062517070e10 55
    0xd0801c041a030341c14082d01103030360110140d10540e1500c08100a920100005040c00c008064142c070800701d124010218120510703040561842c0c0710301e0100b0107090303d00c801e924034565800c80f50030841120082c040c4daa0202032100a100b56401002e1100546480000e0541c1507408036044602d079132a68080c11003038200800d40101ea002d8000c080d1001d41c441c10b040b07541540c043c0c407144601424407003101c0c060601009942d80003503009000141104040202c3c9100300c042134002c03606d880000d01001070101004195580c554202007141003c68207004c1510010b40602c0281607a00062126142c83c641700d4540740c0e0302115001c0340024503003060001081c06485288041101030b91000c04002040200303000281034000f0603003940d021940529480b4660304980c1048074460710300d18071805c1c03840e441141041d00c16080303101440303030003c8821402019024021017022883c00d00c40f800434401d0038100a2a8812040400443d1042d40103c0706070283c0000600345c4c0d40c681d01c1c1240d01800c0c4105588 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 994875422 1250 994874172 994874189
    0xe1302060319110f340b0606090a060905040f020c060f06010c0c1d06030f0d031e0911010e03030708191209030f020607020705030a020f01051303030305100b040506030601110f16 78
    0x10701001000c601240d411700709038018490850208000e07254403869000082505400032402c1190550940e1000d060000030700060b42d0326000141441d051009a03002d1848400c070050050058443d19600411076580c8124003104940c0d080d95104012194138604d031001620b03814203a0f40c0484d660991b6140c00200c1441a80c00d650107031a170710281360703542008802800705500410203196080784690841c00d00a442210303141800c9030805c0d0041c1c212041031340100e03000440c1710840695560803601c100b041d023a04034051400c0075143e403500070b03a51003070f0804025124410f4020b05107040c000c041c4400d48940c107007030800a6452900c1d000d025000809196005407041000040d80d07144005000383c16500040e0103404818420703400d008482a00980032814020709021000190401e991040000d42c000d0381c0200d0b8078100f1007640ca40d10035468210941c500000c10040c0306a8036460204c0750010402e00e000100600310710314941c18120144400d0010b40074031510009080800000d990a548021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 994876672 1250 994875422 994875457
    0x3080d090b040c330809100e1e0a0b040605041a0a020714160b03040804081c0f08010b0304030804020d060f0b0108090c010807050c250e1302060319110f 67
    0x25400f0a080c0ba0440a040c59102032201c01c001e00786108440c42a006110703141100c48847c00e441c8130350103641e5092016082580b050b09600c2495405900300941072807100c02911803c942d0783c0b2144172507540140060441d0303448a007c20100700003200e840000c20400c034403441c85410008468800780d40a090280c501d1080f001480c000c004000c90310544202022005d12491860b007892241c05400040061360485030034000043c1071b1000f80b140300e294208201c0341411940c050140580003680864130a0304101c80c4030018816040c1000880e500550103060074078065407580b000401400b08984000c261506000380d0600322402c41e0003585105100342c0f25018155200040207a4a1800005d03560000e0f40d20000315071040e002d84000c101421084060b40d80300c041105403500d8425581c0421418081154002c0056100c020070a030340000469103c00610041c80e0001502d03400007601d584a01030010b1480881c041c096408150150804020756403282d09064910034a41c04c29040c00c994031108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 994877922 1250 994876672 994876709
    0x807030903200f0d02040920011205040b0621070b03060414040503030103081c0c0905130c020607030c180b031503120304060c1403090709061a0403080d090b040c 71
    0x102c100165881006882000302600c020200098141c80380001d90f00150364078031010109076544210840d0b0030346814924200c40048000500d0790850b40f403455042c510b0300d800e20001941c054049904600300720341328244d125030782205034100111340840c100288114840015604d001d80040e51141c80700320b800300900f00010800041c1001c0440d4000d009400400040c00001c84c804003404030308000074085104040c06aa420049500411031000801c0e0098801c0102d890b01e001402041e400800342409103964103100070f9236840c0040c0102d001d160f202c0b10604141442412613400e0f0207580c0702c030301120a507215802081c0742d0056a802c800785005d22a601c000e8203001a80084950011106524655507a2503c1d802080301c9401c87c0104080704800741d003098891009140500d031580b01070b02d502032400034640200e6040340c0c000c8048166403016140c20307003070ba001030390116504840d405a0300d140c02a0300d400104031840c402071110b20890b00f0700c03060211620f61101950701111050149122 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 994879172 1250 994877922 994877963
    0x230a20030f030f07140a030506090a0b1f030e0714040e0115120503120405160501080709050103050c0c070b040f08060c1c06090f15120f0314070807030903 68
    0x92800700c1c500100c040000c0f03010401a2400710703034000007616040f0100e40c0c1207002c100140c1d000c04410000240c4900500803140f62400c001508003248102c200304e0701030002c1c04940c000c0d00200d04080c20001003504040e0f054040d8000b01104d00400741a51540d0382c0324000c220b12039051003045800f0300d00d05071403c000100148a00c4000c410032801001100345000b141002500d401d4400700e4142c0414000c91400f00707500c00e10140203a1103040a4840d5581d4031482c0300c00d001d001d9021300d04220b07100b018000e001d03400c20007003c00d40d5000e01c5c0100f025a6440b014070300b944610880400c652042d18400614190f8400c06071064030f80e10602e010381560346401d2180e40d042c0c140c0c0c4602d078860080200545c01071604115500700152154042241c42e038030f01d840790440d8540800001c140f500c44805c10700c8698131401c60000345c91600d03e41c0c07070444d885440d0000c01110000b401014042c240a45490f04103c0d601a00c0d1099400300203980d0b50740861900400100d41032000f100c001800140340a82c0d543c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 994880422 1250 994879172 994879177
    0x7050405041a090307060f020a11010908030c091c050a020909070f051c170306130e150718061d0306060f01081e090102030f0601020d02030901230a2003 67
    0x54004016224003045110a011581006801c44005100c10000f140003c5c3c07450180506e10304087c0c10040e11140c5003900a884c0b000d003258240e405074501103a4100207030116007969000415070310b00640f0b0301c8411002c100110700d0f00310400d0b003203000902298100100010006443c41c42980d0008840e110003520740e60318442409407038802c440c000341c24407580c10604000b641008030305820f071180300c40d9521103000140050307c1e07805040c4000020401c4a04000c00b0000301c0d00c0074600204103c080013101e05484485800c0320492004042d030101c0c102501c00c2c10f51041134800c00201d0000b03a07a4a42001d000c002207a03e00c1a60031f5025520070f40a0316001c20424410800507000080024190300110340c81390b0014003032840701c00c044d45000440f2080c0d1554a03c10b100001c001a41c0e400c0201800d0407140004040d241150f00901b0f0711a0202c1d400702c10ba8007094403c2c28480402000102440404050482f443c0ea040301c022030511021035010f510010030100c408650040286880941a20fa1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 994881672 1250 994880422 994880431
    0x5040b032113080c1206091507120c0906090f06080a092108060102011b020c280801020408061b070f0c0b070303021308031603050912010e030a121e050601110d0201090507050405 78
    0x641001a50303003464aa444a01944031502c0d1508040108180070710ae0b00700e48000e4568000a10500d4090003900e40044e544400f83c100c8a1300c01c3c001310b160040061202c03c00400340210162114101010804000f140319044241180364a00e4881c040300005c00030b0074101c501b01e0056003420f20111190080301150f94444104c0d50280112501d007034284400c80341e601e5103080c0410004242d0f60302c5141c9088110b0042d000320800965502d00e0448040c0c644000034210000311143c2030b801004200c031140c111084294407014400c0940400d00340006c2c2a0515801140180b9000440408040d4581c1c000c10310414a1306070b21204540f545201a628090400c0020070403889241c0d035008a800341029107071000380149030007031040340d2050305403c2d5119040868030035400412038145540d0003910b00c018118502004010b00204251001c0c0b00b40032000800e12880e503902c02203401c80e4410f00345e070503645079110b046403080c072203d000090007010380761003e98150250f0311000c58589410300816018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 994882922 1250 994881672 994881691
    0xe0315040b0a14071e0c05330f010618030b070804050607021f020c0c0307171005090a031224090c03020708040e10080604080d050105040b032113080c1206 68
    0x841d400c03248005171000c2c0380010310902418032408030014a08000c0c281904081c0141c440841c10b44a042d03800220381c81c1c0c464044040e085080021070b280d0340e01d07a54119201850001c19440c0110801410750704140c101500540c846000c00041541182015020b030303119508440c2e0710366620804a0b1200100504100c541744604d041c10440d18036600501010304410040ea0510426000000c3c03a000455009400c0c0300d410040c1d84ca00041c00748a40c062401c04904144000d1504281058544c28020002001c2c4900c11381d0354010116190f005c4040440d403424581400b083c5144c021480312349078400d11075950308040e142c03074246100e130007600d00182e07008020508041c2030250104012400a10070341528818040000710345004000c12402140034440b0140d85442404a000039600160462801176081c0b48141909490001d00501502440b03490b1106d415544e20360480316200d1028544502d86203510086988400880d070802070040031100f04100c02d0907030350400e1311880102c40c2d02c0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 994884172 1250 994882922 994882937
    0x30a0201080c04090e1c080403080a091a07170a020a050418090f14010606080c070b19060603020d06090504150c03090c031113020f0a0e0315040b0a1407 67
    0x1035000703601c07090b00040c0000ca0319082c6502c07801150f04640b4625004e6041d9403010340d11440e80e03441c2c5190f07484041ca80780b40030f002030f1400e03807005055003001034111040e8998421028007440846886045c441d13021800705403850800344402004091074400a0001d0b0b0032100109610410502c00c0340d050310000d4913150308040c60611403488042c0d011444041c070640300c14042000803110b0164040c054403c400380c116004482181c02d003100e003250032500c184544070b0b0034407071002400380568205903842245600c2590328248201c8600080c0c00b1010022820150041038aa8068014050030b050b00f420812206640d06c402c5d40c01e44500740c070064411018480000c20a5146410680402c2002c1c1008500100c0e03d40e500300c0492003076401604c05114444801d4030300e1400c0b90f00c6442c1c04c104e1032030075030410502401806e041e116000e04407080c410034080e1a40c1d42e4409010441604404109540b650300e000d040601d41d4260031160017a02504e031650300007442c41204d8450303016002940c1c6410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 994885422 1250 994884172 994884193
    0x40609030620030c0301140a061d010e03030a0302070303110f0412030e130204091b0e1216030b011e060203181c030203180f1008060a0b030a020403021e03 68
    0x10000c091011001a1030890403680310140d24042c1c00031802440c2200c1e0a40e42c9616110400395140111409903106e010803000c02c10203580d10586400c800aa038410b00f00760441c0c0800140c1d80d504c042d50a1541601010400c0d11010340c0580c0907040d41d0340651800d210003d400444888039200380504030002203000d11003070181584040b2401021b501c2070414600030007400780000c5504018141c541215900040c0500c145d000034001c00c4d00d241702410001658060010014011072520140140251501420301d0310600c000c01c851110030b4030001c0b014070a03907100d0a0801c40307110240620400c0006c003101450200c51560700b204100d85880e8055801c2520b00c082c010041200d034104642d015613004102032003810307081c500140c020b00c05e0300259a034080d81e000540e05072500b0080e00740315040030603000034152070f070207080d0424804501d0802c1075640c403440050391658154210b6500240084104000032165900400990380200c0b10441c80c0d2664440b800d441d0344203010b080b9050340207030a204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 994886672 1250 994885422 994885433
    0x4060203090f0f031905030402010903060c09030816140724031e06061206050d0b090a0c12030e040e1005040303060b0705071d0405120d02041d040308070504060903 72
    0x1160806070300070598040c0c51000c00031928010410640c40019000007411240003500c40a50032164800c5050003411803800c0d80000e03042941074131010300755039240c05420700747c01d20581c1140c1c00b81d6170010803980c46005003011000340b2a01ca12086071080000011410b007030300c00080c200200c1d148002000c01107840702606c00c0301d541d03000300750b081070545455110104e00356050b495403d51142d002e0000d1010303e0a900101111400814601080c2c600300d02480305403a01541c1031202d940000c4c4402240d140c1510143c9010b00c00180a004205d0511010901c2e078800b88020302c1581c042d940304180726014004101c00c032000c02c0c44081460b8044050b501c82c0360a613400007580240a8100003034240d55524100002c4d50080b070003100c1c00d8000e00030a000842841c00c40700580ca4083c19400200e1600750341e142e48e20f12200035110203552000c55500e89054a40d012603003d409208003200018181003800f002d0400d065408401250150002413440f500c100309072401c0300c401c0d603110407900d469038880 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 994887922 1250 994886672 994886677
    0x609140f03032d090d09060801050f09090309060c0610051806040504020d0203010218011107060e010507061535120a093b15012d0206061c050303040602 67
    0x50307030b082e646840c0114040b0781c0c0c030752030300b07104d014284080c16800b14035020041400601e03401032000d00c80342000501158039458101c0000000c10346003c50f01c1e84645078128a10702403000455800f61002565071144680070440368003030b1020820030103126032035008010002030780c0309103600c11448040004801e80b525400ca01e4003d4005009100c928941c0d0300403d0999010040400a552412044c030344156400380e42d812402040202074070045041141c000c2c201c0005600d250f04005010510300d06000c559800380750800b141d20448010344d80e4034101c42c81003200d08841480500c502e040c0401140e80e2480c842d40a413030100e809048000c61004a59035240c0040503060200f0031010b10108070070000c40c400324010204003040c010b1204913501c1402c04004040046911800000c0034001e2500503c140b50020090034208a00b004101100c0e1901180500c011050701c00c0c41c02e0007218074140c001c903c403030042506480180e0100320325242c0000c8628045c00040056200700001004076155a01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 994889172 1250 994887922 994887961
    0x1b0b0408091206070305180a0c1412030d09060c0503090a080a02240105150a12020d020c011a04050c13030b040305070507030b0906070807021f0b0d0609140f0303 71
    0x20708030000c407400c1c40324605882202c0400c0802c1d030b144140004001302ea0845d65403044040d002300301d040c41a90720352407100818071900d1113801200ca0601400e03529000205001c0700c8002c100c80e102c0d04040d10036000707002c6800068450301e02e00055a41e40358030074401c59104441e168003c0040c0c808666a2803010b0b03100e55140307001c5020300c030465030504400c05542c5100d003941c043c1e000301c2d1f0f5041c03008009588a035551200c41c81c4104208203007506400510b5030b0013203a010758005072180c804080c024042e11a00c800722425500e007a4005d0f04461004400d4415048180c4040100d5903400c0001c0045100b402082e000e54001e66000b0030010f056407070300e02c3e441442131418905015060351403d20f004c41d503410455611821504110000a0070001554800c6103440c00c81c18138100f141e40a0348402c280700201c000c00841c1e891040d00c00d8400e41180260103000340450b0442c1d042c9041040c0100700800044a45c01044445581c980c03000041d201c2c444281d060203540b4544450030b0703c201c3e140e035220 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 994890422 1250 994889172 994889179
    0x11070201051c020f0f1c0b1e0d0204050c0d050117030412080706110c06060f1f210b030106170d1206050603160314012103020708031305011b0b040809 66
    0x4454403130207048502409503003254080c00342d1614004d109401d01c0b401e250060480b400d2801b001c0d160a50395040c007078070062050746500c0380c101c0e00c1d400104007500c034500b01c00f9421a0038001400b6005036988010b111501d2641c40030042e90740c0b1513a1144452a09507001000c0303500c280310600440781e82c2c15986c20303118400d201c902d01d40b00003580d584065800c10344101b81000c4011070440551182400180d41c480c000712455043c000b021400078408003042007000c84001c0d94808200b44540c06808554010001400302c0407030b04983c9507102010b0070104030410300039400c00c0000121911140c54110070040c19501404d683c0c0b1001c40222081c1501c03140e000c0b000d80c0c95003000203a603100d000c0107501640d52424200e51500714180050165241c5482c2c014208540c80010012140004c458800c00e001940340da501c10b0b8183e0030201d02e4480740c0d410185850100050742841c042101c178451084810a80fa25191060251104815442e0319400549030036540400a000581c030304006100840009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 994891672 1250 994890422 994890427
    0x7060b0102070b04090e2506091202150306190806061009030b0f0426121f030312150b030f090304060903030e18130b060607080906130302061c11070201051c02 70
    0x543e00350419182e940d41e0003207a600e9850083c4a80d9900c5002c00c80a803400152012032b0311080d50118040c224403c1810011490210200d030300741e82c82d1100709501c0302e40c500344001091380f1243c4e69920740c0c01c1921542e00c80c4100c1d10a40007582d0080c00003404898000720720030540e6694001a813545c480c02081100c00c030b080c5035906001d10140800b1070b03e040184416880e19030081e40c5030b41001c0c0c1405413540c4040e081c8a12850110b521100250042c3c4e0341c50f240a40b04020140014001307000f818400d194040308146c4017081e101d0b00c100c051881600c803608200c000d501c91041c1d00f610b80c80346000788400035120003010303c0440c3c00380e4519000210058000c01c0e000300003240d03000d00034130150f90b00c0a001c1100c124806c01e10042507000d80d00710004440217440d00700f40b1341c0c2c1c001c882d00c02c44030254040d050206144050341c86040d0700e20010341d0041c01e00355a8000f07447c8500020f82c50b0340c041541592402003409a800066419244299030603180c0f54680352606820700c0f80d0406001840b202ca5408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 994892922 1250 994891672 994891693
    0x73209030d02010524030a02010c031101021206040f0204051e012102070210020303060d060b03030c06131a130b04050c040e01020a0e0303031e190c0507060b0102070b04090e 76
    0x4100c009528501c1d030b400080c0d5420488000408500390b00313a40d0743c1116540c0038401c0d041d500481d020641c00da090a1000c0300004d6441d060381d6454074046580d92952000c110300c4804a480e05a0714800c01301140c1c00c000450704804000102c1c062401025003145844a5100c0e581c200d80300c01c1121000141000c0c1d00c5030450a000c643c1031070303049800e540c00b181c0208541c421800c10407440034842e9124009103046107084c04c00f01d06030409005011300015215410580f1540303060040381c40c2d214848054910034030f08450f684155498103103040301e41da0b10700c030b80c0340c6802c1c3d500803400b40c0a01c02c1d40f0181e9104d16803686460946036000352040c3c4090051084201d030782c0d80c80c0c0c8504201d4800a07400503807901c401e0038001e040d0307075001c3c2c844034003d400402c10825101e2015004c0403408000f14240003003610780c0040003113180585141c0c0e070085403901c91403000041d00903002e440740c14810201070040300d1040d0b00480e103e6400c0e10955111300000d100a00c0302c0d00c007a40101c0c0c1c0c202101d0703046501e4202c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 994894172 1250 994892922 994892929
    0x5011a0d0e06070c05150c16031803030906080907080a1101260a0e0102030f06060a1110050414010c170615120106030510030f0318050405100e073209 66
    0xb041e209080070a22240b80c1c4802c1000511950104240d10003e1041a01e81030585000b94819104550441a80c1000907802c05000329100c507140c4503000364130483e094036480c1c080c220300110700900001c00d0414000401c2d214000032414144e9034940b0240c00103842d0703079941c45030f58000d40c40f0f01c0d8103010118000341e18646038507001481080d2160120546410010038501c1100e07402c0c401091140d0040040005142641900341d0300020240c641958400041108071030079140000e003100b0a0040506401d03810256412050186015682c0302d40101640c460b02401c852441b007070300020074405000d44040c8054448440c1c5c5c0154050250840d40e440d081601e0340551000318011203c078040700049c80440e92500c620f40e0b000301001e03032441300e00c0c0c190b46070b0828020000c0c03401010424a4a0f2603000c001d80309140900802c40903000384140e0400484502c041d580e00d015104100400d00001485a8400c122015411b02d080384441050030000641c0a1140b8085c0100720000d4010040d60171185ca = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 994895422 1250 994894172 994894183
    0x906080f0c0616021002060f061014160b0c090f060403030c1b081203042d0b0907171c030203100b0c010b03030a02210403020120100c020d02070905011a0d0e 69
    0x2001707903010306101d1038801041b691208001c2d0069000c1c14070108461005600088042c054003503214000c0d07210034180700c404c0000004404d00400306100c14080c0302000240b44090289903404440480c1081020707800c0c0000382c0164400a4002002281400d0105180b6252051300500043d142e2000e2625410807038030349141d290f200c0c114290000200418041e1203019814600b125030700c0c840905449684416488000e03000290a80382d00101269421000304100c10080c0050242c0c1a4403074042c9680c15107400720784440c0c071090607480c00399584413072003403003101c0c0704586c111446007400d820310003040d0440e00040d54004440d96079002102c411307035081003d4212500c0381d0380148030340f4600300ea030b9a040c903445000758075034a1418401440180e8102c1030401150125050b1000300c140a0401140b401d806000c02c400080d20b411a420841907001c03c040700b15079040d03000c446400daa90006641100d00901c19081410b169200840390205a44000d103440c181880b8041100107106c42c0840c14407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 994896672 1250 994895422 994895449
    0x60a1b2102191e0203120a0e0a1a07020127020312040b0301050a080304050f09091504050120070c050906060d1a040f1e0e160f0906080f0c061602 64
    0x500b55420b240325964411110781d0300c1c1c901010608048022007501941da400381d900070701c01d00707940f82c40028011942944502010200101111b204403410f0501b5000306400d80c042122481d100d00004048a005010b004454541c0c0e4041c4060b104050351400300c40b00f48524126454020320000a100c140318801520242c000260074a940394500b008201113030800d80d11007203850f00140020004d03030341c404903002004501611821302c070f80e6465032520300300b02500071411008150b4405210603c0415407100810203400f90914011001c00c0703541c03828038020b010000f081d4007001e04042c0240d040034401940c0000002c2c24150a01c0014010401034444000c202c034400746900c01740854038502402591314104107400200449600b10648140345501010044d58081c0c0f03d2081c140300300c0d0308001d0034004441c56007240802d60744440051410400c2031151030304c41410048007040c4481d0108900d40c0c2150f0030002801d4041c81603080c0107283c0c02005445c2407101003401e000002d40c9400503c07440701d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 994897922 1250 994896672 994896697
    0x20f01020301080d02070f0f0504090c08030a0f030c0306080601120c08120a0e0a03031707050d0e0309090c03060904030e01021006150f03022704020f1b060a1b2102 72
    0x13602c4c2d0080020310301035442d4401306000010301000c1140011000411059070800d44000c681c214403070034001044220703503000d080b0622002410404541c0c1c00000100b00590702d40e401c0c024903081800407800d0360403038050303510345420480040140780000c031034094100d4031841181c80043c0da107458a034100b42c1c4018214000310000218000c1403584803070600c45810303040302c0c0c0d55582c0741561002854680c20052104070545c03041c01042d6418000d4068803400c5039244400d10407800344001a82d12904600090303400f8059020106030b070000ca003c140c0744a60130142041c800c079a9191400c0343d401200c1d07603a05040d400b0300f06484c0032140190007820050103900041c00d40c2001c03117050042082b000d441e0150101481801103a08054419a810080d002014100f2950382e08100010300203100700248000c1c0e2500c00580205002081d0b1002c0d440bd02211090319032941e544d801050544241035820b140d48140100c1c0c0c10b0206008413545180c0c40000b1a8854400d003080ca00c0d4000c1303911400f400c020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 994899172 1250 994897922 994897933
    0xb06120a0b10020f0d031a120a06050c07060b1c080d23010311042c0304090f09140a08030604090302150c090f0f0604260607050d0f090210080601020f0102030108 71
    0xc0118100301900c1703140c55900d410099907424181d51601c2420031000140301e00d40c09092179140c58000c112810300c0710381002d010406428100c20b83c1c0c46950049404172541400c01e0f5111445d8609824803512003030a0410004940669030b81da46025480320800114241e980c6103d04102130540741950074840710425858030703550450038042c059101c02c6045a204a0a0400965000101046a24070591603045092030150800135050940c06903401c08102c0500d0314048450b21051034018280c4a070003411140d1b1010003e14206071101da1901c0b0107800c07498104089809402d0551003810141c1c00f0b44195040001c15400035070786408207481c0b180301c551003c500c4650a01e410f001d0024690022140c0c4035180c400140410010301540c81070541e0154171411545215004c02d994105950015043e10364620340943c01410340d401022000c59010b140482c0c1018002032489007809083d001800d50001c0603500c001120300c4140106094114000c0000400071620240051800380504c01c01420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 994900422 1250 994899172 994899193
    0x30307080d2a083108032205010903170c070b06060c2a06131701020702030d0305070905010c0510321b190c02060906030906040204050a0b06120a0b1002 67
    0x806441d00e048007490321402291502c9038412240c8042c03100c95601c00d02c0b194481c1c0e100d2038401900000d12007c240c10701c182070640410040194007200c8101e1080e00c50300e0740801d80540c80303034034602c04503008489003c0030444100405d45401402d0352150005081504e0b0906d900311803800e040c0010610f410848402000300c01a13040103d40140b100000d0307420904004d070458194824524a110f40e2011398080307900d220001031300390116441c3d2a005800c8a200c0c0503a000000c00524040b25400700040c001600483c456218100f0100103035080720040041c900624402c2c1c0040031351040002000542a10220f600d50045003007050180c0c2c06226001d807440c082901180d4400c1c81d640380b41d01a8400c000141c00f0079030301491520030200d54540180008114800b01391140b14082501d0f5200c2d00201c200300c41c103000001c4041c0b08a2096030240020741750225030703106485110101070360200b000d0160500c141000b1601031341c0400308110106044821a01050005151840c40d0300142c00c0001c200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 994901672 1250 994900422 994900441
    0x18050609090607020a08070f170a0305090a0206190c1704050f09101505091509040c031a0409020f041a1f0905013c030b030307080d2a08 60
    0x150760000c00c4001610080c503100c10005d4984942081c01442214081240010f0219059003501c8195100d10007804900c203041e0708a0940e040030841d5030009081100144481d040401c541c1151940580403071f052002082c01e81c9a6a8015401d4a04010486400d08081526400030741c0b0074800050b01a0b03501ca00b060148500c902861800c0b902803d80782e03043c403108420030303520070084881510201da6030701000c100846440c854903419941c0b00000c0840209402d410078010710f0300c01001c440800c50034441f141705405441040001540507000c60030b000d19142000d070440100540300070000b005585071413000400f11581c0c3c150208407280d59040380c1c14981040107950f100169078120b4641c801912000c0200545050b00407141001008503184811013010090010110003c0006483c00c8241c00c2003010b00b41500080c20b80040d003030180b212041c0c1404001c03520815042084607184c8121500008050a0346c1003003600182000c09a19011441243c45890f85854a0ba02d46aa509000c8141e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 994902922 1250 994901672 994901689
    0x30e09100914041104020901110a03020714031501090c120f020426061504020f0d09020a05180f06030a0b04051f0b0f011101020d09050c040f020913020c0304180506 72
    0x308001c0c0b01d0039081c8004588490a8030030f021000321005070b603c0040c040101c80d003240e0f51800e15014441c41c4c1041e4200b54011070480c0603034804a5800704039803203d000b0556108400340c90000c045c060300c1c0041c04409402e2f085501c1c9024181003018501040c00315820441b0300141d901a0715940c0030800388401e01486000e0952000c545121030781e43d0400d40640781c1c03100c802400d5000e04090b900740c0c1d46c6650321650150340441c003d054401d6128004183e00d10701408180c0d07070481c0328502c4000089114900103400c0b0b0080d003822482c50b06d0307a42c1c41c0181038030340381e90140c08542e15108001d14800062240201135108030b02c81c50240908422240b0041e6012038000c0c141442c09043c0b01c2a4901c1d621584001c210100007460482220004510312038020320514041803184c40c1083c00b1f01050000000343e260a48c0d1040d04d0400148500401e02812405411a41c4ea0b02c400c0c03000e12010361454940103010101c000341c080d00c0c0b40544e6846220003151080c2204c109190b1101d040041c5841c06021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 994904172 1250 994902922 994902941
    0x6180e060601181e05040f1409060c04031e0c0b1308010b0907050304111c0201140702150a050d0f0506040f110904020d0212010602030c070f03050606010c030e091009 73
    0x200780d8084801007807032411191040c000e500349004c1c041000c2400c4c03115030008400901002e0030800a607012100c8150103000845540041d150054002c07a5501500040080c0f082d4604880d25041070700350341c0c8407036a0800d0040e00d03001d01002d0f104268080380b110040140142a8500002c0c2ea456286e00900400d00c1a94880308081e40340102651050312118400d40d4000c0e01c6140140e0762350760740c1c903000e8031141e00c14124540244642103481c600b101c1c031002443c921b034000d07250402c0e580a04104140140314211009401040e001d0803490010403500240241c901942020360400010080c600100e401d00c0401c0740d0380640311000e010050034144160862009102401d1290107440f6421421038400e10b06410701a690024615108030f01d1369054a0541406000485695944220007540c940101405034110b014550340083c01880d540e1803501160740c45400307006680d8582c070064a030501141d00550a0040b2504140c005130703035201c0001c0c032a584000300740d8401c3d401c0509100c12118078a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 994905422 1250 994904172 994904177
    0x15021b0d03020123041a0105030a1424010602011503080a1119050d0f0201090c210b100603061e06031e15090c050c030d0b03030c060a1b05041206090606180e060601 72
    0x1030043c0110340b0081010400ca5410840c0385132440f503510915030cd001081c1e50405103d00c01c07000007030760b01e000f1840a141221410303030092203118110b485a4911001e6480024200c060401c21a50350900607090190940010700594018601c4000205d5000e40b50f84022209900702d2980c5052094005150349075020740c0c0e1000b040180240c0d82c0d001000301c554011072454050094202005010110b46441010b901403000e0800e4140300300060f1b01d0100c14007980c4042814910040f5048200e1500d0b00d0b1240354030301c915031440c0d2400c07405500801104280c0704806600e21002060a9081d0040d91007031040e01c05405411864401200d080b01d5044284000f007000421890305007984c000150b5220031648030700000c200e0303080c40c006491449080710290b00707409200700308845d000c03461b800b002d140c0c1102e48900354003000c040c8080350b0620850040324881c0701070b0100d100118010340d10404075140b040310005a101e03110304a8a000b06400f04554540c0da89800080559290900409410031002e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 994906672 1250 994905422 994905473
    0x906031a04050c04091b030503031503030f030403030f0603141e0d0212031801050c04140105040630110a030b04150e0c190915021b0d0302012304 64
    0x142d44250b110207100304030764030070354440403a1000d103c1241281ca007000c2c00314080041080d82c070300d400c1d500c9400c02c60340d0014042c04450105c0c0726003804011140c4a4940c10030840c1b035603a0f2643c05030b00404591050b41d0071a0b41c2d0707520100005080600006550307010400405840c940400c059101c1041500c1c0751106420041c0340d00840c1d5000039141d101c604000030025103d40e01c400948002c40d242e0010310500b90b0030001441058a12032001300141c903064100c060505040f00e0041d28184113a10900c0006402d803804020b003481c13102104c02840300094081e0300c07111f11001400003601c1c048222403600702400144004506c3c0c1601c07070f4080c0d61005613400d00c85904170186000400c0424410003090300362100000b50480a10011940c804844540021401e420f040c40203000070014003030b00c005203007000d0040196038000210f04145100494101d602c01c031000d01440940d4a401030300324107664956001035400b40003044200160100002407000600e40390405414101c0700303040c407100e4003082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 994907922 1250 994906672 994906681
    0x32a03050d0e041e050f1e01150e031618060e010e0402030a050601060c030306270f0b0d0b090706080405060403080414031c0b10091701150906031a 65
    0xc100c01d10400c0080c289001d00a400c070010401401c00c1300800c4807000c8105078061254a00c550006000b008030003031102131551010042113485014036400b00750150382c1c03801003103800031a6140d4a5900f202d4a00358ac86182e000380841d140c0800000c1e4005140308504050040410880d601c40c18501d9081c024405945850700303440f1503401c180900351410703046130009429928200b01041d25035034030130b04582042d0380d01c0c00b005065040c00d000440000781041d80004d2100f206003c0300c83c100100000d580d13a8510b100000c00e0040001c0308c0703c01445625001440426500c4c125891912800340c2c980c0501403801c00a0030f402d02c0c00e00e421001c1408551818000481c0c0300148040d8003da140c14030800310344450400b4021003c0305404038440303200003c1d1114415001c0c00d200369401c42c41e80001d0065150f5a8204000c00b130300f0800c2c1200203800003408004144400400c000d04030b40c0316000013101040d10903240c1000ba05904003c120340d484003820001c001006502d00d0014064001100c0503040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 994909172 1250 994907922 994907933
    0xa121206030b0a020a050408030304030e100822020a270606020706050711030106210201120c0212030c090409030221250311010203070e0307140114160c032a03 70
    0x40034005a031031a034007268607172000b0300450855019084903c200c1e0780b6480c0c80d20b001071649610303610460107403112800e481d10281c081d400003030050119051021451880c05101c3d48900300e0003406980c048416a00000c0c3c01c1603003401c90407402d000e40d00301c0000c101c10a40c2030060707a105502c54021980100420401d0540c00b5080c0c03040c0da90b0184220008140c000c0c00207002d07142d107400c1070315502c00030804032a081c3d407509608000c5510030b03241c58400c0100d180240741250300001710900560030004560300240d000700c00030750b0312200c1c9030744103410540104080707011940341c9031040300941d100294000c550408080140090280198943d00d401c50365960721030700e4a0000d500b6001c1102d10341401c020540100204850198108001c6480c1c0c03030000002411444040001d038003e026100f00499030103100c2485880801c01a1195420b030b4003000c941d50401e034421444000070011502d00d010018044450000017140a0651410b80c000e80030419214500308101c0c604020952400c00c000084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 994910422 1250 994909172 994909193
    0xd03020a1e0b0c19080a060e010f051f0f050901030e0f0c09011a0403170c0a08090406050123130f03120e010305090d030e010204050d0c0e062d010507050a12120603 72
    0x90803417138100d003283c940ca0fa004014020300d8101071fa14540480002c20208080f41c9410304883d4101c40d500941d9204d11a1480d01d0742c4040000800503548108032106640942d008200001c0107160008002e5000803802d800e107415422002c00e5600205600e10251501a038500d026026500c8050150601c5031804e006522462000034001d1100100e001c0950403000f0940c0e035a28103180031ba8605c03410a252a07147c960040f00310b0761040307241c038101041d203520540c51082701a86203030b21a082402d14500c00728590b00b12609051984201144c040f50901014800800031445070b10002695031001d074018100070101e4404504062501082001a15001035151582d010f5400c0002d508040495514068440c98020301c1d0031a41d203034103003410004802000c01c211469a02582c59913101c541c00c0004030000c4208840000041d070411102442d0018002c06040138141002c0b46007190582c0c8643c180040182c0945035070000030902c8140035084201146001c00824040003e5401e6903903a21251 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 994911672 1250 994910422 994910467
    0x405150906220609150b0a06030212042616030e011707120b040e0c03010605030a0f140316050a02100f09062003040e1b090a050d03020a1e0b0c 63
    0x6007180b4031070600b4489950701924000b5040450081030b5180d0700c170031a000d03040c1c250000e03000d0100f0301000900c0d580703e4801d4403c0c0c540d00b2071503014035403165114070101c0606564a2200d020006103003e0002c114580200083d1103000703040503079080c0900b03015064803c01c1058906000e404e074100600b5101c00c607100c5034050003d0400c0704011600c01e000f80c0040c22140d03d4650400e04d031034411601218001071400c03200b6030860081c020103440e40e0070b06461f507040002c000c0c4480d11b031065503000110104812810128004101c908184202020200d04030b8010340c29502030f0020310000041d400c100c0041648410b460500001c00161444002c03c115150b11506c420007404415800114409401184204031f0f010300702c0e6125a120906000000c00503902c4000049100c00d50301c003103600000658400210040c107040045140c0028006004281d140440c1107010317000c61400001c100d20100b80d8ae00c48e21141a031203001842c5004000f401019204180d4403805001c5c40d2001e041c441c810301c1c1c21 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 994912922 1250 994911672 994911721
    0x10212070302030a1413052116060e1204140f060307050a090305060702030a020f160e040618080315090c0313210e0a0b130603051e0405150906 63
    0x120744d00c40f149800100301c0e14140382c45039110b4000b844445552010007580c0c0f28003610a40e46400d62a422410002d003020304005200d04050001c103020210444541d41454080d0348082011206480840d083c404827416030f2208110100f004c0c03220710002c00c4c2c01407050f4000d132a6900840001d40020318140401842039080140000740c0381034182c0308000540085a00500312600760030030b60030280d12900101c4074540144112402e0580800c0001f500c02d500124400186101a00303126103c100b0b44001030054a0791500c1d00c990b02c24503002403240800c49802107004c00c1d101c0c1045035008213400041c070011032103840707041e042c00702c07200d110400c1320f8000071075941c0e50b054800103140094440108200b03603501681300040c0044141c0d00507140141c66041164086e0510361038000d0701c0400c7c001e10300081941811035200b48900c90007684002c0e00710302000c607500006c9024201e000280002250101e420b50085481c160143d5024100c0c644c1040050000d8034051512181d0390400e1050364010009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 994914172 1250 994912922 994912927
    0x32060a0f1203112113081222060c0b0c1204110901050a06090e090a080a030c02070b0304330f0b03160e0f04241a04020c0d030b0316080604030908010212070302 70
    0x40008800601800505080c001d48640e1074800740c1f050348540007006503800700c6052000002001003040700f1b82c416140e81381c86124500b2503a4036411602c0c04020f200c0c1ca0840000c10621028030142985544503d03c0b406158040d041170005020312510b0683c01180102d011600a10880b40c10032400b1080d6100219209401d81d2645001450400c0d00180505140c000103071108050ba07046d00148840c1ca42c17502200c900903030754003817402e02d48002c50380038050100b036000c1c0d103454200ac0c85450001c10030081a1040280344113607032204807020b00c40c100070555560054409181401d00514410719081d10144074210700d015110121140300500e018004034140340050304004614100350303032601c0a000340e40703100d59010802100808250701074205030b15010310310484610b03090080750025005003001c0c10a207092584160068804079010941c14050903800c000100b4a0b182100001c050f184001d048500301820090301003d0f003a040f110b4107074010480c61109019034881c03140c020f11140b40c0103a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 994915422 1250 994914172 994914187
    0x80c03030f0d0605100503040c120f060b2803060501090207030507022211180405040201020709110c01140613020903030306010c0812040c080132060a0f12031121 71
    0x5000780f4490300069801709982100c402c0d20359101001c1e6201d81d216070219510b4540b02c000c0003140340040c07403004026020b039100d0f0100058203500101c4070f000e40513000c80d2508134051202d10b05441b07610030340082c00304120802c105014603409a14010080345204514045940e00c0042a80c030450a019004040022124a400307010101e44400c203034007540204a030001d0220907084079030004002c1d4480c4000780e02c1e082311610b001d1041c2d90007258144c0040c40030614100601c00070b4103112540a0320b4036014080c803080c041c000e0107080b065402d442c004540a2030511b08010400d4030203071a911446206016040c226100002140d810081c2400d201004542510300f00d00d8520582c2002c00d580f0420b0010b21041010119010055655984c001d2140340b40241d0340d90042e0070030195580c0b080902d40d00e081000d005401c0119004040079103907926550300d85a50030109074441d4800700081d000d40700c03088181540100c0075884e406502001d001c4600140c4201602c42840b40d44250131f1181c00141c11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 994916672 1250 994915422 994915447
    0x70209310c051909050901020d3206060408060c2d041e050607110324040f0807020603040c0e0a1b0806030c270105030718020a031d030d06080c03030f 66
    0x10f4000c00c054031080c08546131040845020350015a03a102040f4180444045103011204442c040303c1e01c08480303001c43e91034012000141c1c0001401d5190825010030001c1044041804950f1043d5018000559141200c00b1071140c180c1009500e01000103e07199a00700070010001158220f600501146400902d841e8140c5600c14180e07003e954044000070380001003019840946040c0c460403002e4485014140c284803580410080740040504002d0300000c00085405e11400050350045016600701610396000c41c14030b5000344c500340d0741050010030800080749418007150b801014403900340103844003402d6040320049003d845000303104c00100010f1403901c0421850ed803848008124680701010003010301c0403410403201818a2504041c00030415080000d41142101c0d4800e0b210f085201080700c41c90020f40101e0300d118109511007120032014140005842142e100281c007855640c0c0e5134418440071510f103580200000e41210040c48031075a00801036548060780d0250344c564429509448 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 994917922 1250 994916672 994916719
    0x5011b030315060f03060512030f0c0a1a0a0e0a1109071e030e06010506160b0408090907030203070806041a0f0a090c020c10020102031b0f070209310c05 67
    0x300152240c2000c8001007540e4004c3c00c8140d20f445a403000c004464403030090042441248000c040190300401000c942454040001d0200c114000702b5224070404580c2c91403180078000c0b074600d42d942d8468060149801320340c890010301519260081c180310002c0d907102403458007c2c0c00c065100b12201d4000801c00c41c00b0f4094540d240c0d0044140e4505180700c014090300030840a00e68040c58405c450000c00c40782001c90840781950300300b41595182d900555224141940002c0045400071002d115032803494039000150b41c002c01ca151009030b12490001e900414030440104264482da042610400340c10b0b10309540c24003100c00a07070303114480001c030230b01159041000b6032015880c2c501c1e00d040c071803140e9404a143c4c4d422201c01c403892030319201d803503d04138282c0c0025108400c90b01e04040303014044240d441c00a05103100607031010341c1410041c1c0c000448644040350800c40080da0600b11400c000205076080181600030002c481e1120065203070f2041d00345843c0180c5000d2400c0718503052029107024070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 994919172 1250 994917922 994917941
    0x9090906071707031e02031008300d09050703060b040516081e010306061d070219060603060f05010e0108070b031603060302030607270e0a0b010306050d080903120405011b0303 77
    0x5c116103140c40701d8400c00a510480780b9801d03900e291000482d2807900032076114070030740341c020038182c00788541c011031640011008901c0305c03844410031481c170706020180504002c5600036005006c1c214510300b00901610300c046011442646020308200b0070382180903003290f03009171502d031407501a41c40002300a020003014200301c4110300034500000070040983c0000090781c018000c1580700e54034601051100d020b003034500c8405a00001c00d200b81d6201213440200540e4000c8401240300c550b65140d1004442c1e405c0011800c1c55101e900500c90405518040d0f40141400030082c1015403801040b18900d00001e02165142281c02c030540305414400e4101002454004081d84d6081c280382d5005041d08007440100390094602d500324040c0c0c140360010360021516042d80710304060b61040030f040c00170203005c605241850369448000c2070030380b80d49284001852154450340e030340b80e201c0402c061906010076a01c00c0d0180c0100710034041c50b42c0c00389403010300d01100302207090313614003604d8150302515050300c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 994920422 1250 994919172 994919201
    0xc03070b0304261b1f0b180705030f220b0906010609080a02060f040b04060507120801120b040201030915090215090a0b1305220c0e030c01051b120909090607170703 72
    0xc0c4a03000040855026401b0500c0442d00501c440103051b26060398204111003a602050741400010029021415083e5101318026085065188020b0780020011011101034030354440300e070108800104100052809003805081c0540410714142005544002d40e4100034021040841c00b4150f951a103425200a006000111525152540402003880d0071074001540c82c103d61903d1900c85e680203620f494182e80c0700d884c15840c07502464842045001c0f020300124100f43d83c1e440c9110100d000040c00c03015034044010040b55540990040040c2032031380883c2e517041c50b90204a14149940c072032100d08216494010100c1e03e4503410380002002e078200340d011036009800100310a240c1100717080144440c0f1441c1d10f00b000703900700c1020304071040540e059205801d5440350b0701117040b5602400280000500440700c10a1070888013050f503060603214814011241c1004c140c01c2e29615145016543c0400881c0c000c08840c035000384001c00750b00c981008001c03038118217004181303424840c1d00301e0300c2c0006900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 994921672 1250 994920422 994920463
    0x7141504060e0307060503060d031b020d06061401110709050c0f03041b14240922050f0f04110103180c030c080c010e04020c0c03070b0304261b 63
    0x7510050724111070101c9062181c0100c84002c21800d010328140e80c007841002d0952260740c041c542c0c040c1c803101c01002420f10710201d64900080165074440303151040502c9044c02044003440c00c0100d8403500718000380c550520038000f0340c68046135400039804040300ca2881e0f010034940c840f01101043c41c400c11404040e2070900004220611060308640a89428003100302d01800e50b41c1d00d085042c004d200f096040e40305028043d904020081d44800c182c4d494103070700f00c4c18034000c09540010301d00701c82005a80050603600f000010109041d1217426400900c1d119940300921f40b0480c480c56814000f0001003134001103c228860a922a43c0b001004024200041007003d0382800e00a140f11454803048542c3c0d203521002159110f0003092080c0109030685600409038401c4041201a41100002e81450312605100b201141d808018000051140348038043d500d0074541042903601c840203178810341042c0d000e40200c4501c03100004440184892031380e1030803017410142c4010700781100d800d4402c01e4060b41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 994922922 1250 994921672 994921679
    0x15081f03120302120106091824081e061e0703020d14090d020c06070201081e0f10080c01051b1c0306230d02090a0e0d080601030b01080907141504 64
    0x542e00411030070501c800e55070b49907aa9980c04887d4281c0c03a01400c040125140c0403400782c0103ca810102010100d41a010a03a940c141303c40000300050ba4806209684229401040ba581980c103c100c1507804001806452420b0300c000e00c031010683c02d4010400d280301c00002d0007148668141c6410309402042401140702c882407620604c242520342d00c95078003659020250544c00043c00328802d400c0680726034280301c3d8540054503078440007424042d107804140c01003407803018a801d80c40d05c12000382a45c4038003070504500303000c1c0d042881d030000e000710392004100c3c1e003141e038001040e01d0f201451109102c1d0b1343c86142603030b01c2c00c0150702204024802610f1a001024a8060b00101d00343c5110b6010002d04003207000502500b00c10241050b0303042703542a01c0c1d00001d0709140034040d502484540700030403103c0500c1c040750b282c49001048407001800c1102032050541c0e0501034100f03140e0003481d01c02d4550074625006a161113152103030850b54011000c06d1112621a14031300000c4058060b01c071600c9903136 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 994924172 1250 994922922 994922927
    0x5100b1605010b0d20030607020c040b0f0a08070e0901060815041e03120f02090f15070503070c0f14030c0f0a0e0a0f0b0d050a03080a020909041101030615081f0312 72
    0x601081c4120158221885d00c0b81e00700000c07103512400700c030307030080140401a100b400300404588000681100d1501019603d0f61120034a031002440b80000074982903141c000046510f145c007030603640c01139061140412002c000007503080b05106410408404d980c9561034074003603a0a0030900d0b07501c0c5070054100c0806064000182c0d220f4450503400c240301c07203010a40f10500b28800c0e4030903207034402881e50b180d42031814002141a03600f050355007000e160a0454941e00e01d19005990101c8220002040503c0444110342d0000c0042000701c0700c0d11224014000042c1d201c03150030f41e41c00c1c050070040c00200c2c00c99031012840c0f070081c0306054280101d424842c40c210301900280500c401c4490400303c0da01c80d5410014510400c864004003d40780510040d42c08554191001d050141c000c0d0b021f0249a81715030341e65509a0180e80320340c0008210000b404005000e4640700d07400310b44080080003a00034051b4210b400c0aa005140e00f100c86442c00300c04040303081240c0c05030806441c40c00c030036928075526074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 994925422 1250 994924172 994924193
    0x409060603140a0506012603031501021204050d0323040306091208060a0e0c190e0901290d3305222d0b010305100b1605010b0d 56
    0x240191141400b41210200640c0d0b03daa00490040181d0310002c010000d5038079000f03140e035039010030f100329020704400c0d0300c0550324540042c0c50741080760b0803200d0707000c0b880d6030104141c081c040c02d0b1200031420f180c40c00e00010602d000c940c40117400c0c450f03440b02801044d180000d0301002208500602520b03151681001710080000c48030032a0400000300c2e0300803e050092940790322810b80101140e048030f044c01f81100c092880a0502d06c42000c040c0300076030081d48002c01107081140340d9a07031034030b01e072520f03000304003001030180c0c802081d060841c00c4208820104080c800c41c806840320000790344640040d03098004000b98102c20070038140079400004003101d590072032042e1800d14100040d80c503803114104403039011301541801490200d089500c0c082100c0341c02a0b404c0c110280314480c03a01c1101c20300c010324041e038039102a0503951b441040340300c42e41e0944141c41c1c009080541e2003030391504212100903c0c0c8507403081a02c07103d111070000f50130400c003500800c0320a040600b000050a1082c5401740801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 994926672 1250 994925422 994925429
    0x906300509010606120209030a03180317070506100e0c071a10170c01080a230f190b060a030b032e0c050a0c120c05071e0b0403030c0209070e04090606 66
    0x1001645a1900f505c4580281c6001c0c81e00280503007500301007075400b51040142ca124901c1d180100820020100350313007200c040c02d88103a00c1c966982d102c0a900d070103030620720010182494809004030034040d0202080d1004e40c000d200301c64481e615080350411034071068180e500009d900400c5010059142403030901002141e608121000d410000350900984a1940d031450500060800c0c00040320f400c1c20307400081a4080154a40d504d0284000440c240404200d59000d00e00595405202d150340143c21094a44418a001003003826000f0001440c544503041c813440030151150703402002581e0501c001c0601400c501c2c100142d884414240480d84102c6032460b030b003607078a041c0c040c2e801d090250048901e5642e203992200808002c55072a602000c1883c00e81204005484035040300061b410090000a880000060301c1c0c0400c0d03584082c0c0350700302542c106c41304420041c0401c02c000b0b60061600002150b0454104241cad5036a40c0040b01c910348402041540300f81806080800d21a8660045064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 994927922 1250 994926672 994926677
    0xb1b07090b1c080307140702040e0c0918070308071e05010b0102010b0108040f020909071505030402030d0908060403080703150306020a02060121081c020a09080c010906300509010606 80
    0x144101c5200003180d40a03400b6000d086807004200142c011445440c411145907000a00d190405185401240403502c040748000c4c1c3c0f9900c26140503465103080004654002c0d14240070404207004030525540b10303400b902c0001c003601800714090741001540d0b80d0b01214000c894851071030034401810054064012418424055403a01e042c4a0f902c0d48039040442c4920741000203622041100c1d400d00005620080c5a0b4031640503111012401c000005031800d0898003582c0c946480b82003500415041800314040c00060110000080205400126020354015010708043c1c48650746c030b20b81a006000c0307115040710b2802802d40e0100400981c3c1e409814640041ea003101c480e681c903054401c8612100c1d90440c20003411050802000a054000030a0314801520000403c8021007180e0001d07a0445408170000ca41070030401c1c0064282048050000d4509182400819107031200c00740618200e03c10100c4246c500b0600c0c014100fa8800d10a02000c100320002c010728688907480780d00030034140c044d1000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 994929172 1250 994927922 994927939
    0x1509050f041a06010e010e0a1a07110405062b0b010f060f0f05190507020909070503102a05070b0103060c0306050d021513081c0e18010b1b07090b 64
    0x2c03440b4241100761080d601a1100030000e0b104000568011198000b03080c2c1c4150a00d0004c15034a41c0555903010328108900581c0e2102958900182008002c0600f0b5005929110400c2400d980310810300d89840e0507143e81d60000001c940c107845c070f003100128010b4070254000e0000a562981d020001d011240c00d555500218034030414101d9000c0c03207850b0340000081c3d0600c8207525800420420010040c064203005103418850b0b80480c070800b508543d411025001050b08100d181414428040005507501007004200821a81154281c900e034981f08021240426910003d600860496242a40051a030507003903035039252031300150040034030201c0042d052100008250070040c90704004a60700070b04020441c481c2c1e02c10300b802c68110203070583c4006610840000d8409041c00107134064968899107014191780d000e03000d000ea540c0c95004601440303424104500900d0040c0030581580c441c000c2842d0b56294001c0030900d001140c240c145440d010303105000a2565007a0700a0414002c161081070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 994930422 1250 994929172 994929203
    0x1e060d03080a110c01050903090406061b0b0403090521070609030209011401200d020706050304150f021b1506030304030b0c0904180b15060415031509050f04 69
    0x1a0900018001004141d590001c00d030326242a8120303a240102400209041c1102c0303d11302820b51381b0035916101c81d500002040e04250900b8020000900401c0c14981c0180c0a02008080300511004000d8184d108403400f08040611a6014100030940107280d080341070700c1c105c00c039802d00040c1340100d07000784180c0c20002841c901481c03100045a80080c441b6030396a00c3c0518001c540420101c400c3d04000c0c2103401d00c07440e00c1075054038200740c8003200028a40c0891f4100064542006500f09009002c414010040024000140b1100d41d040c02200855206490124000640903440c1541c04c0f2500c1c4815640090f2400540759509841e60540c045090711844107164a0b440b03940409041429280b00050440006800404070f003000540006000491010010f8011034440d0040318402040400d020803c80361102d00842200f080303c400c0d00c1c1c40e00e0110b404503100c401d0310071071040c1501c4c2c0317542c1024203c103002c0303407001040711984c207020901d80313943d40c2e803a4203000715011120092003070101c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 994931672 1250 994930422 994930429
    0x3080306040c0e010c02270f01171204060e01020a02040608011a1002030a0c030c020d080a0206060316231e030d110a020f1f020c131503030302030912031e06 69
    0x10768000f04180c60300c0200a11a03002d06c40206440040c0c5510902640d00d4019020105000a84a4038102600709078550601120035204010020f42c0c0c2c0d0107500604142c40d8a0301c0503011542181c406052085089003a400181d08081107044080e501500d0044009003840f4103401503247e1020b0300310703d10206c0850740d0801159004000c003610040e84280071003190140601614070129009003060b2401c0b1800e030b40005e0345c0c2c4002800c105c4803458003090312441c40350104500d03500108224041c0c600b000203c46220404c104038481c50f200000d444070300307020014080e81020300050002d040700481d4507580508440030f01d51000198020b1050200030810103214841c000c4440c080354000c2c0003140e500e5000c00440d4151b4240c0c0075413003989104043d00c099000c1c0300540c1c00e4000f030b402400e071100c040810030460780350070300c0800c403468100103494800c1c000c10f01d0a8800c2d654176040042c1c4986444200e01d01d045402c213849081d1150000c24811480290000460601444020402c1503616032081c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 994932922 1250 994931672 994931687
    0x22b0b10080f0c07030c05060a060608091c0e040b0409200d080910030f1814030a1b03030204080615090a0c120b0f0d0c050a06080702030d230103080306040c 69
    0xa0924000b801c0020030191480a0001c0034514001d140100c4400f03a17039141c4c507041c424242ca04e10102540c4241c10462142c0141026034842c18090203802d42190800702102140741080c201d80800840da4940202d40c0d640350320201c03040601a1003000422040c0c908054054023420340e0040e0b044222005002d0752600c115040c48943c2d110540c02e007002e00410a101005240381c08a8080c5034444813669440b542c40d00c03900b4903401c00701d8481d102501e424103041e021202c201a0206441d0010020303040c6842c3c001342c4180c0c0300020051041490034560070304030000d00407600881002e0003000c1c00e2003000001841910076000c1c0072036084115403201c4640c4001c0302d00c1c810203030010038039550320070b520320b19250301580359240041e1001c0403d03610304002a204030300c00d44044170110890041804607044c000c10000151005040403c41401c20510280d9680a00f0724101d1900d03885a020007901c0c24000500700c40c00140501c913400c1c0d56140c0c580781c403942e0421203c45006a18040b00715520521800d40b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 994934172 1250 994932922 994932931
    0x60f0608100e01270f0e0309090a15050f03031b030c0607182112050d05090c0a0b030a020705070f0503012f07080702030303040f1a0c0904022b0b1008 66
    0x210b40410030729581842c28041e003204c0900120303030390310b00000409405900500c51900202c0c0041c42e9a14078a008003d03089a0262010070602e140c0b001c4a00c4006407000700c0802e5803021100780d200c80d5a00f4002038594400c070000384085101d00401c04a4140d00000500992210b240580d410b80c2d6402c20116100c0c09a0203020402c0c4110031030401c00300290494011007070060300398110b51104c01d6102c0b41c000c8801010420300241c2c00160300c0721010300903c203141d0803642c20005805021049000103210f82c02600806044010020108515070350650460f10741980c400d06403020710382e4400310f107003100320144501e902039400c00540d00601c0c54140001c400281718100e515000c4004c140c052009504450ac0480d8044d0041054001694040014500c2288121029048282240b030035202c4908a40500d5595203410740510030702d8442442543c200300c106483c0182c50f0038040e02100c0560385111100b40c44e009102054504040c0103410440120009072000800030200c0722046a82120848 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 994935422 1250 994934172 994934189
    0x212070819020102190203132102040b130c03090308090a0314090406030c0e10080601150503060a0509040308040516050a050d060b0a0b04080118150f060f0608100e01 73
    0x40d140703980c0340d64041040407003128400142020074500104113052198000400960300c0860b00702c403100300c00c190b900c016295800302d2440c840d01204480312020380c55030f0020b2141c0e8a56941c085542c0341e01807480e2000740e0382c03401804a0f49401201a008181c01c200030740010703101200250600b10001040d06d25603074150764205042a00a007014400d0308400342a070381c015200c07100040428040c5944501801117400c0a01480c00c00a061b036030022000d174400c88842d04030030010480a00d910790010030700395a50600d15903e50702e09000510410160b046594408151400c0c04181a1301515061241c1e109104840d004d040050ba03054030301c0d4080c403800e44c0c0515144014001c3e400c1001c0001c42d0548104008a60103001400040400d00140c002c0541184040380400802c0b0090240c4007071404150203605058800e5210a040c02c8405901c8500c055210400d20307400c81c240b83e205100030b03c0103c850034401912450000d1850405032000400c4481600011580100c0301c2c1e81d4504841c20b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 994936672 1250 994935422 994935427
    0x19060212030628050307080102040905100302010503070f03020d0c03020a030b0118140301110a0807021b0a050d050a080a030902090a0501050a03170f03040309030311010b1c0501021e070302120708 86
    0x41904a1612820000c4401070f0001c1c540e001905860802030b40c80504412800540c54a08205040b412118010204254000c89440400150340c100c401c81e13411814a00d004180c01301c4000b8143c0c00b80c41007600ea050300b5072402c810084002d6042c1e01500041b24a550f0034044801c0e80302c011120072010805540703802d016030400300030030000c142802d6a41100980003003451901c0b84440d04013900075007640404078154030200001c00d80e041c019003108041000079188640000400f00d20722280600a260166140440800038080d04000300a00264032690207640c411121034003c014003100d041c01ca0046a44102044107400030b4001c2605982014200101c082c0c03644d261000d07105008062150060b404110728102c500b105801035226074040d40322400003618528000f00801d010845403e40c50745056500c03041c503519091200f20402d110317052a045590746041c403c3c020f2080500a9015003112582d07842c540350b281d00034180044c001e07001d880303c8101c41001d10005101e400c200074140d2104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 994937922 1250 994936672 994936699
    0x902030105151003020a030e06040b06030601080609070e1f0803090a09021809072607080702030a090314100915060506070302030708071e0318050d030207050402030c09190602120306 80
    0x20703602508640748286030116404c5180300c2301c1c508024064805440c0401d0746030820240741401c10005004002e0080105001e2414281d05502c1c0d8100d030090703903507420084000c5202c010203540c605202080000c1c50907645959610415669441820f9007401102556000554025180300795444400c3d488280c441140083e010059a418020694030a100360310854041904d00741c00103030800c40c41d0b9945003c081c1800c0d21301410860b0002c082c02d0031580100440f84801d80e01c00d43c00ea0842e030f80143e01408040030384110314103005c02040001403092420300e1070400c4c050303107980c0c05000321140c9208001c91611241440040d00c280301020300940d000f00303c14000540e001c40140f01d01800703101c0030080c0d907100400c603046034040c420058001030101c0041035860650010702d100203200484e14003008800c95a000f0f074561407640702c0d00d807190f9404000101c80c0744000084030040c4074002c0480910940c034041c1052030702628001d6038014403844610500b007070300c10001c1382c2c080c0900404180c2036108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 994939172 1250 994937922 994937927
    0x1b10050d05070507150e120301080a0b070203040810050109064e12111902040905031308030a021c14031e100503010b0f010807052b09020301051510 65
    0x7019010600700501008403030007103190340b00542080042850040fa152080d4204a490180510310400314a8000c10040000c18400074110044030707440126032500b40e545a005034210301840c1e00c102e055004016401c48000358542c0028161141403204003c0380d80c07208950300c9181c00b540000c8049204039941d840001d038481e9080e001d604d101620102000c040c0c04800203070309603124021076011013418004500c0700e8102032051503038400304000700000080c600c10f0780112039020f9000f071b0013951b459504005110090003100c000c010f550000424031559141c0380c03951781d400001d0ba50014014411001f15050000d550b80021020740d41c2c0d19500c000304501029a2540090700c0f421031840d100c042d42c1f82c03001040c12814070403141b15620900d664a800107040c02c2d500190b11a520840034083c04100d240c0c0c0155040d50020344505d00309889002d0007006c2d008410321030403003102403006284505c0240b400c81c0c00008120344240d000380002c0e03d560102c4121403440715003050748000d912118000551 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 994940422 1250 994939172 994939181
    0xb0c030901180b24011d0a050405090a0c0902120a181203020418090506160c050a0528020d060f061a04050907050309030406030b1f021b10050d 63
    0x80c100004840040011020440304440350072121440c2050800c102d8108421083d00d50001e100c042c0e0078150500000240011a0340d80d100c202c8012038226030241e626064501409000b010b48108028204840035581e50403801c1000c44901c0700704040403c50580038025180041001400c500480e1950018071018004007a84030003004a0307941c01001203038a03003070704c007030076030f25940380140d0310707401c0c0510f18008001d042d0703001080f42d0814020500207440090910f81c0103040c5408500005602d01049075070b08407180c4042c0180c07180c4e107a003505100e40850740b00f40301c86440c503250400708001044c0400e0910800c030041d501c41c24003107101000c40c1c99600b04800038104e00c44000b810f2501d03680140050104641042ca040e8404038060001307040544800741c102c122030521074150710b8a1405990b480c4a5030144a0400d626140459190f07207800e00342c0444080c41c044404400342c0c015030002e655409040d41036000241c08515174400d42051508502400415030f1040d16248200c00f41c20b0160 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 994941672 1250 994940422 994940431
    0x6090319050a0c023d1d010903151506030b0112050702150411040c0909050c07080304060c0306120501020a020111090612060d0c0e07031104051f0e03160f0807030b0c03 74
    0x15a12400c4000d440d4450035a295041c009840440b403554405c10b0b004184d841c0b121100e001080c0c400c0440842a81c1180c4c2440803281d000444c0d20b441d1800c1c28201c070203040c0d5602c034000545800080030800c23030b40640054200c01801c0c0e131040504010424068191542952608090303000300f00659207180c440d8a50075403250203114050110f1081b103010a00b25284202000001000540107125400c0d4901685d90010104030809040004946a00c500392002900080a90343d45501d445000c43c080d8004000a11071b0f20a14440c9640b07038140300c4c0c041d40c0505120310055191441a481d1194000140d40c40103102810032803d1241034205118a250090850360307220b50bc41e20000001200c989814000c0d2a03039018905e0700f8240b204018043e5001c4091246a520090100780100d481340b00b0803500000e101e03210b503070030160404ca00b070b518452001c9510380c05001d00a51280055288445070044410800880b00780030759034044551074a42c1c502005101800c980046550f000b00c12003d907400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 994942922 1250 994941672 994941709
    0xa0801120303060e090f3c010b0310050108060711103303050d09050319030302070204050103120e03151303021905060601030b241b06090319050a0c02 66
    0xf82500c1e6006000c00c1c0104580800b030030341c0801c9050b055900280002c600e100700007049040c407140e9086034420b4201e54003030003205035444601c0e0510210025040001d0751840501030f5010500c001045c0005042c090140c1034241c41a0000300f40b103207114460107194440da000180c06408130ac4c00040c409040300f0b00384041000c050f40c08110150500380682003090120112541089186160250500c007441d072009060041880080102c0e031000308002e05120b1520800520248a620b401d800a004100000c0c0d000b80c070b020004003c10007041d210f0601094a03445014041680000701603980442e41d456004075014031303001ca0b5104491035503882400d03209006441c05024010000b88034030b880010309861a60005040c02502d5825215034040601d0030b40d80f05800003049000b16003083c00c0c04000d62a4014001010b410320a044a91181706a10003002e65259041496400da40c81d00b052240c01c02c100c0f040341010074614010401c0798503c41c542d469a0640c0c1c003140c4c0070032808000040ca580c48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 994944172 1250 994942922 994942931
    0x1f0e10080607090e0c071502211620030a0e010801080c010c02100201020708070b01050907111e0c1c230d0e0607080309010e070603050c160c090c1d060a0801120303 72
    0x2411f10202403580070a40400180c5035034280041c0f0203420b0b0701814102c030007510301040c0b0980c2e0740d070482c2d422031092581c140960200700765003003d800301203000d07540001e50102262201101e40d0010f401407003180240c2e18080c603a620303800310b1912849030800c03050214441c1c418034001420051002ca4034200640001814030f00c0b1b94442c00f02d15803060104030760103000300005204c03d00d80081c2081e08480d0b689852010142c00303145603941c4078105440e42c400d0009240e00411816000c01010203064005005078512480c14540b44d085444070389400c95400701c00142c400b0b50404510b0041c2c010100d55001040c0a01e0003c00c01d44400e04481e03405500041d080002d0301c0810344000003140a01032210001074000300711a80141026041d80020040600304010701a41801750000e59440061550586500180b07030701c1c02101428041d400145298140795a540c502e90f04141e00d03211920000c503141142c000303d00c2c100511440303190041d4010609190060040d103a55450707805a40d80700c1d040006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 994945422 1250 994944172 994944187
    0x30d030606090501110304091409150c220519030309091a1002070f0e070e030a03080703110921100c0c1509050610060f020309030d081f0e10080607090e0c 68
    0x342036941506100c60039208100600000e08420005000c28028032f01d4002d01c581441d0021900600c59422000e21a40740c0e80a013104000da110044001044008c2181034a03055103403a81c0f61140507031005801040355a0000a00a01c403805182d084c400001103004a14084070108141038202c0b00300c1404503c940c440105000c001010700502800cad817034840418514113070800400d0003131f40b005400c0c040c1d0085662940042e42140c0302e6034020382c2504001c140c0100825117144d850041c1036040307504c504072a000741c4860205203c2c0904240112050368540002049040c040c1c503c88102900041d2a41c150f807004204080c0540d00319140101c0b020442c400e42e62290380c07800030262540e803c00301c104001005a144c11a80c40b0b0b00380101400170758203000300200000e4462141419074020b1242a1b03001a0700d030344040780403800e92080d44031001105034540c041c20000f2201100d01a26620036548041203407180010824480d0016649000c580341c00c1c0024820307066000f61003413001c14424041c05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 994946672 1250 994945422 994945439
    0x907050402130e040609140d0c060506030a0203190b2512110a0315170309040207112112030f0a0b040e01140f0606030f0a2414030d030606090501110304 67
    0xf00e02580c0200404249032140d8101181e166024000c4500980d000d00c500100c0281c028021080b4550088000211039480e500481e0030881b050000a5040c0207030400d41d58050040980c40040b0b03030040c140d58080350355001401d50f0b0605c0b600300030440c050550190041003842200b0103035028020103c01b00b07681d00e4004a0300e0094101c0c011460110b5141e40b0b90181800740009d922004224090b0180c62a40c3d42ea118551280701d0100c03140d0082e90000754030418002d42e006483d2100b08040e245064078107481c946401090303540124205580a4540c0b1403000621480c160f81c000c402088912405407a0035034880010000c0c00c10041c1c000352a0100c102034030000384500b10300360452080000c12807030f060b41d07103407940c4030f000704198130881003441440460031041d03101c81d91000240c240001c101c02ca1009a0700710380c000c0340810403415800d24000c20810741613010a050080207a080f42d1301002c001c5425020307500c0c0c5005040000302585400c002c20f61041020002e01060b50050f00d01c1c0c2030f10784400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 994947922 1250 994946672 994946699
    0xc02060f0304050c15180f0105091c0c0e070f0e0f0910050303040609050102010f06030506040b0717012303010c020606102f10051012080c0a061a09090705040213 71
    0x840032005e003c500c04c1c45520801c0444c15851908542e000038000d01100080c00a00540c1520303405090840403483c070b65004600f102d0140da0304001400d02103a541e004205526000301d8030180064020401c401809026200070135004000400e10080007907984180300032504024144032986188020004454901b40010009024180d564a143c2401c010000e03080d600982407055005240c04000c0002c40c402243c1d0316009a8409840120b42e12110011520740a2807500e40b000f180010000181a032500030800c42d591007000c1d0415201c08907442007508a914104c042009600083d0014885250041c4100001707922810310511894680e66448201902d0b070b040b2480ca140c2c1c00506102e0050100409107422000a00c144074030314020500c82c0e49028a449030341c6140d503013040c0c0f89007040309c00300a43d840c201100c402c41d4459690390030b0510207030074544810011120a14408071359418a03c0219104040c114010201c0314170304014080290700010078102c03100d000020100d180001e0101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 994949172 1250 994947922 994947949
    0x60d09050a170d150b0d2c0105010302040b0904050703030e2706031c2f06041112010614100203070506040302060604060e0105210c0a0603020310060c02060f0304050c 73
    0x220302d81c0307407401041e040048034024046900d0300c45695404102c0031111000f100c4010943c00c10119100030288001013491009101517508070f11401c07001d60003a14154002070480f8001c8406014400e11030013806060302043c0e80140041d040809e003480824080c621101000e10040c0041a601c8d21614400d2010140001d911003c240d010f414000329180c100b03c155100142c0c81d440142c4108500c0020703004d00701038504940c00d450b6802d41e0490062000804800d02d40030041507034280e01d46858400555100071041620660b1510f2141c40d90520510480d801c1e0b440c0240422500f0501c036007040550350341c007000401103200401c100000510140501030007503210780c00030002c0d82456070400003555000c3c4c22078001c8400041c01000305545d14595044102d402d04842c49159025226550404500500c00c41e00003282c8400002c4142d45940254422441100e569802a842e80740c21900e004203c080130758446801d0244000007540d0000440e0080d1044088860043d8010049050001d205a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 994950422 1250 994949172 994949213
    0x70e281a040905010b0903030a030e0c0402220f0b07060906110c0d020c1c0f06060f060c05010b04020304053a11060601080403020628051513020306060d09050a 70
    0x107010495010503006850142180d40d403180d0601d46c040c80403d03070740e00940c0d21580c1015107401c5c0007021200c0c01c0c8401794607618043c1082d5502d0f600b2003207059124903a41c4030b031610054044800a4070f0300e01e601d200300a0302c180340e0b5102d10307240b095101c060191203e010140d404d103a072000041c00314990719005110b00000c03100a44030796101c40c1e00c0642007a150810340c601410004000a0f00c1031482030411840700c0d4040013048009990341007900081609820180703442270481c0e00881c003290088208450b041c030450007030012960050600040e40029a801086640520040503130801c4c110202c1198440d00382d0300c07841c00c03000d0070681e004101d403001c02c4101094240310b40c1c2c1c3d104c0301c080c09110790044003801d10b80a103040a0303800039514a0010280c04030305524140300030b807050759401d00b030041f184040814001c0c1c0c2011640e08107071884010159200700c41e454110b880100f01c6000b0f80c0c0c45880c1c003e200c64109280d1144c0703030000d0054030504403a68055243c0390300014030503030024400400040d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 994951672 1250 994950422 994950427
    0x120c14070c0608010f0b04030308090f0a03020f0c01030e10021c050a02090a050d11040e0a140606100206010b03072a0b040b090307020d1202010b1c0b070e281a 70
    0x95001d841500c0c180c100c0701c00d0f96014002841ba884500d0200c4046030b6040c03820884036035030260b2440c18042598808085801020088000d055001070599141200d10003591921500b8030015012214200080495900007046c0215075503216400350842900c0c049c180200201d031480c148088070021102c440c04154007007000c0316035040070381e0400041c000c180c502d851400710503103030300d2214113095507407600c00d03501c500c42140100307000d21085000d10750048034840c84907030b07004440703031285001c458070b80c0206040c40642d200584000303102c5041f941e0303c004141c910b845007041203901c550b44c0c4001161400c0000c0c21f00e03030025403819078120418000c04442556003003516100b00801d0020305180110b9006110640240e6640c21074118483c1d07100c04c25a105413034000007030f0b0141510f88501c0f548a9000102c03200c0c0c035500b1142d41824980f00d030356a034240d80d54160701900c00d040c500b40c015030448600300c212203186031210002002248000c802c80075565a0310401003881010104400e18820007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 994952922 1250 994951672 994951679
    0x120106031a0607020105090f040f061823151909020a0f0212040e0402030703020411070c06031109060310090c051308010c08040f0c1806150e01120c14070c 68
    0x48400c610328880c1c2280c840b490060f07150002000d90180b5280d041c0b14406a043e0102d8aa607558002ca510049501e4244103095070343c100c41c1d000c2150701c0c00c0d518842d030510305070000740e10425031300005040001400b00d02a803032b03103810104420f81d6441800e820100c0e85034400180080c185408c80201307080000541e4441150038000c1400048101003000d540c0075545226100c040b8500f5074003030700d03101c0100785455034a50001074a45030340c0e607102039003091410500504404040c002002030310b019800d210402a0f503000200c0845c4d007000401d07840c0030400c0c450038a052508800554101100404444c00301c0c0d01c4000d05001c8485000b084008560700041c51b2034041c400c421410002d00250300208a14000d40310094041d20b00140018021000511000304101c0410150000f03820801c3c18198050022202c410043c0b1260040a900001444c0c0c158035480c866408000c0030541a5100c1d000d00741400050f9000d44107400a001c1032103503148981d01c4200d20f181c05020a5405040523000561a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 994954172 1250 994952922 994952951
    0x3210201240303111b010c0c170607080c0c060606070609241d060a02070807050307110a080606010c0b0615030c0d0506032808120405060601030e0d02060109090812010603 75
    0xc41c18488130380760002c041c8019070514070302003081a48420f0a180f240c0f603480345000151119960442822001c41c19075420505000040b101e100e0825621a2492500e6000088205000c1c0c6031a69416902c660009000340c100380c409422039602c94000451071801c00c0e40c692240002c401108000c80001c0410030030382000c507008007095440c00708000d0009920210843e6242c540040c1200c03541030f0005071402c1005240001c07541c0300c94008056a440360294545000704240da401514801c0d1510352004c1140c0b1004038009000302e005031243c103510110741c1e4401e0700342c150043c40168003484d103401030609101242c00030740c4241c0510360131310760b80d03000c0e05d45040c100e2700d020708a01d009a104500b1a002594024400300c0b6130480e4000c3c20900a9917450b108829100381101d48800c028000240400c1140001e0b025000360400d032030034804100c04084450391448595150001030707100780010041c0c90020381c841d000b401d0281d203440b4504101c608910005280070703407100e00066912086c14800e500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 994955422 1250 994954172 994954187
    0x303090c0415030f080708121008152815090b18010f1a0d0608010e010c05211302030115090c020d0519020109021f090f03210201240303 60
    0x700c0303840b2102026007182c850302101c401208008107444000151101070192841c2515812a00c100c643c03092860203504841c111542403082d46c001d88600c408054020008003d500d215170314075501c02800030080b4a45824015840b0510b00807681d803404c00c0d8090000d0818494040c01c1d000310003180c1c1c1c0000106102c2e00c0c80030340c0c1704210a10405401070141001d202e4820b0219a4580c4942c845600c0998111b0395520131441810301c00c910700040065082010f400c40fa0910b01070400800242d4820b4205440920940e414042d020341414038065810f1107104000b40c01110420b4019003003621035011a0845194100792488000b03c02c40c01c203c0010b05010703801c1500ba02d840505020950104050154014001249080e40103001d06098142c802d61000e60001d40007468803480d9a207900c200ca10b14075184101100041441f000460008100050141200e6004801a50400b500001103000e007d0b512041802c40d521007550041d04a084902e01311400c80f0700703950340f040a245107005031486 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 994956672 1250 994955422 994955441
    0xf06081b120c0901060c031206030b0403030f0615180503071d0c0f03070e030c18070e010801081b0604090504051605031506040e1203010b040f1205030304150e0303090c04 75
    0x782c0c402180b030021529052143d03811120203082800a034502440d081d16074881400c0b560b61160b24044000003032043c0f0044c4580501d000c3d0f00c04002521840c002003040c8c1e841801180141400e00140d1016a4400d03c520802d4200400d2101d021a440d00d0000e820328000e58081d0030001c441401102081c3c85031031290344c00c01d4092107100c0c0783c10a010310644d03250000821a00c01d1108609552000d0389050040b21404c2030020b026a240c04601041100100003e0314800000351440c034031052654041c4004c1740c165003e074001880c0040341d1510506088203402407042c1c100c0414040014a038445000c0c80d1f004078071640c00380041e4000e010840e105103440c0d502c103c0c481d80c0b000700c00421096640d40c540b50810415a0080303240c0005098441c03410400c0c19070014511000800081c5482c1c0b02800351094404074680e46c88141c1d0368451078207e20811000181803a0010004200003468550059600005400b0b000c21a100144420341c1950030481b42c0c501e41d41c0202213003a0040c98544144002c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 994957922 1250 994956672 994956709
    0xf0b010f08040201050912011d07060309020d021302091f0f030b09040b0907150512011401020622200f06190c050c1026190f06081b 58
    0x4003480c9003801001590050300203814850005070108040d22100c00080c0d146040d07078002d02100070703411500c0040080041c9058818029110081501e40c0309000d13103034605400500700c0040c50000d4007000321503401c42220030110360342005a031b034658440e8046041e50941d001e04402da0900c03e000081c2038100a01819020540350804942c01a03640306510740e003003600284001440d83c2d544403400e1804480707400501c51040d100d4034a03120160301200030100c2001600b241c24059076514090303141c98035071100c802c0c00340c1c02800015031003090314140c544000d0116040e003095214140c40d0341c1c2c6880d207100c0160650420b80001c0c2801d504000f02031070707000c0c0f1068800c10301d403d1741c2e00e010941c610403e4122070b042040342340214003400700030400c600401500402003142022100d1000d402500d4621084000c2524808061145122040240c0c40f0707004103035008102858903604007008044145407505000c2d5207450100d0304010070070a01c0720020144103440700420500f41040308401f00a402d0317000c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 994959172 1250 994957922 994957937
    0x8070605070c3201021f02181509010507060902090726160e040b1206070809010509070e04150c0207082104061404030b0708162d0c05010f0f0b01 64
    0xa80c0b03260303480e500d03d01d0036020307031040c00704100d00102d0501490403041110500200003060702d911181d07000701406144201e00d000c0d1103407890f00b80455440480d0700d172030b5070600500038480e40e54060802450742500c941c1001500c42035660000b0009981600c0e100001040c01c0d840c401d01c0343c0e500c94000c41c14615801005054941280e5450a889200190804203e5100701200786078955400c00000084018801f02d9034002c0c2100ca0341d51004116402c800103103008009c00c50480040c464075003d80040e02c00b415810782040040380030310f140544215015481598842031500d40307445078020303008060303002d00308079480c0800403880c040c0c02e03001c000200e000e40c024003103441402d10100c0d4112055403e1960007200f0b104840c2402740129400038040e04481e0040000442d801011288518000010391041d00e0201102b15074190440c12000f03010030340c46102c1000d800d10002c40f170407802d0851400e410f0140650b0b407420b0940310723683c144e031854079100c84480d80c0c2c030b07401c9000d07004181a080c83d02c00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 994960422 1250 994959172 994959209
    0x1a0a0c0c0203070614270114120105040c170a090201020606030718180203070b0a090b04080d0c14010e0c12030f030c0c160608060f040605150d0608070605070c 70
    0xb5200c070214441c071018011005844824002003201b034410106c0551114110182c0d12003d2441c01031081c0d150500050038041c00c6044188078100307440d0005014003980c40241e007003400f03100040c4110003002050055100c0e07150750420400084d40e00c10604d480022491030001c3c4006458644041d0416200e0b8010480500c080c00d080c814840105031498004240c012072040881f05103005808041d4060142040200e191030703482000346200711603541d84200f0595075504448d414000d41c002c0000f079400105507003c0c1240f20f803007070107041030013000403114000d80e1880c60303401c6075950312040c810b940080380d03080b1161030f14a413201d24502085000d5480e0420801840d0b06030300c0010210245035038007080d03110b010304080044058904041c07101207240c507181c0c4c0c0f02804001c2d0031101d071882010301204500b03060801e40160380403202d0181050140320310000385c0c40041d03000500c400c0b0320b0320b540b10030014804004010600080080c0e03200e4540d074102900f0414414012500a0034880c0158041e01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 994961672 1250 994960422 994960429
    0x1f1b110d03020f3c040608070e0a06030b010e0a12060b12030a1b080711040e150109020f1303060615080f27150105030f0f0d1b1a0a0c0c02 61
    0x2c80d0020749640c1020f002c13020094442d54a2454054001206684800d20107410608500100140d43d881d0301d032000f0350390700c034902100c10740580d10300e250b0040b0240c1070400110b402508010000001411b1030491818203070003146c0d8600650380309400c80c0d0118482503061010700d106030f01000d0410365606080b080440080c3d82e9038894825418104441440070503131200c404160701d050a1b5012088030f5a030502070400384601c2c1c001c240410300c03661800d10a81c00311180000c031078000c5442c1074901d41a981c40c10071400025008440400d034007880c2000141040c42d0f1001068000d54428400019a80e0400c00e842d554060300f4004002400701c41c40502000d1070b0107410056002e0010a1117000740c0500481042810b400d49000c42d926100d0385419403108c81d0700d408894180d03002034085808180211000c25a508401a0980b10326080609046d03a21403140e4410060132200148400d0510302c0e5603150300340c11000400d008880362002040c449c144a090141917450051450000e04101c03054001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 994962922 1250 994961672 994961677
    0x30a0f090b0405090903040e0901150e13080a021e1005060904080d0c110d0f0f14091c080711010915050d0b0a090c0801030c06030e1f1b110d03020f 65
    0x401d8403caa800000170280b40b0104100e8000d000c1c0c903000c0003040c5c10120f600b240641501402c20300c0c1130040c800040342c04030300d154400b8441e072000d040c4c3c400c0241158451a03582c1d84103000e04000c501402615018080810440e032807a5054080144482100240110b0890340090002441034485c1400e0102180c40217040d82d010308541c00b0001034401c00c5034025105803001c0211110240125841c00c0010380d0000d08451400e0072035100c1103041c0029041c105d580b0180001c01003c0e004043c041e0f1505810440d1102515812030040e1803580705050b01c0b04680c54100c07003801c4a26030f0322003203da04a542e101c040500100401124901d518110317240113800d901404056a186a940d2404441d007513071908000c3c00180f00400e000c0000c5029208000c007050000d01069601c0066207000090440c03083c45008040501c4074058061a001151150600c1d040d0b00c10321a1540e40399190f949000c954071034800c40d039807840d4076030b12500348582d15a98203002c0b02d419808149032052003200a0007480701704 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 994964028 1106 994962922 994962929
    0xc121d0d0f020a061a03030304140c18190906110703140a080601120603080f0901120e10020f0c0609030901110c01022e0c02030a0f090b04 61
    0x3099805009115904005901a5a00d0800302d00d8541c840e0300394035040c42a103000711614500007840c541007a01d0944904454107140990b6813410003802239a4502a07070703415080c50341c52040d090000402030081c2e504d044403204405119515902040d1055170240c020030150035510030a98032500400e50131000b00f224000c05036001c40d882c00c00e07510041802d07034454a10341e903103800440d40a44041081d048a41d2144404000500c07d075000d401c20102140440d5116490b03c40010205182500011003240c504031000d62501c0e40440c04141c40c500055026a841503a054800050300c10b054004106008810600000314004001010f8012090741c5075020a49600900380c1c03200c204104490160340070040190310b41c0e0404400c2903800c1e241c0304d8030001500150841006842d016005040140c00016a41c40c5a41e00180010298461843d001c14120b040c60b02c8224184903600 = true := by decide +kernel

theorem cover : BRFrame.Cov 994784172 994964028 := by
  have h0 := BRFrame.cov_init 994784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 994784172 ≤ n) (h2 : n < 994964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
