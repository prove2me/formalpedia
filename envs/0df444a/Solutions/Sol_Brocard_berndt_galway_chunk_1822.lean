-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1822
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:48:17.256979+00:00
-- url     : https://prove2.me/submissions/3423a3bb-728d-4518-9596-4ce363f2df32

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 327517985 ≤ n < 327697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 327519235 1250 327517985 327517997
    0x60e0418081614060606071202010209060a0507120905060301140a0503060903090307060c030228060c050c01060b070206090d030c0f0b160203071109070e0303220e0408030c0307 78
    0x2036568024064110010051841d80b06448600034001e5004000f40d9291400b00904031038982100010414004c07440c01511040c500ca00c9000c2d024000d6046689000005026079103c01b8642c40041c03403617200b61801c56011b03d005c9104100f143c002e001d08403d641d0b000b0b2050b03043d41e00f4800c5c011002140c4c1011940d0224944000143c15181403140c5801000c0042c0a0341e80c1701404070070716140120316070040e010466420000c0003c6070b804900505803104102c1c986204035044080740c0c1c0708000c0703060b020304600d20340100d554807140c00c800207088901c0d103180240210b5658158031249801480806508103104002074640307441c1c150400c150680c400e041000049041c0d80301c0c40900c080c0c100040310070407000420b110030039412006664940005100070361500c0300e140e4880e4290011481424000c040c601e021421084c001d014180c4031100c0901101d4590103030100c08081c0340191183e0321032448954002142d031800624100c0d21541e00296550b03e036440384800803456620041c0b01004002d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 327520485 1250 327519235 327519281
    0xf02070605010306020304020f011407060c090806090f01050121020f06130e07090509042001090915050a08010612080a051303110f09060a05090606221a04060e04 71
    0x140901c689400f80d07014107401a103e24003803040c480c0035800d0000c0300d414031034100784031140d0714a6902100c1c007061303103d000400c6400c0c91300419a0480140d40100000e80a800c0411842000c00100c0c0c10000d003801c4020710840c0d984103401c01a04a80b00f001c038103588000c040b1480076007014044a5084070703014003c0e41c6030901c0c0c940031180f516055040030411440110500c000c2c80d60103840d42005e81000c5840a5084c00d1654840407060000442e80349603805036404d84c95540e010b01c215400510f0403400501002421080762100070056000e81442410b08410104201c6014480e41050b60b504240d0006100d40a880e510002d4000a944004000c405c0081803c0c402d20040440010352149000b99918180d5504000d02c4411414003e0302950b0750004015842c0d407110a1001203c1e019920b8614903110310000c111180704440e0203071180c003880c24601d488080c500c0c0c03c00084030507510789004108600207030310a00e44264828500010503d107200840780c0340a43c42101113403111034811140d02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 327521735 1250 327520485 327520493
    0xc030d0504030203040303020105060f090a1508010f090c0b03040c0b1b0102360303031501030f050421030515040b0102010b090412200a0f0f2a0e060d060f0207 70
    0x50080741c0c00c50041c0c0010404004144d0240105074010000300c40e0180c0900c02074002c61a2284010302007180c0c0c50311007800a40e041e5568903d58081e2030b40d40d000344443c014006081c0094290304504440750b402d00324000545c18078170740c1900e002d40da0010580e0806840c228803500150420009400c04410b0b004809c90700d210244010600c0340034558882028280b103010160031150083d40035210b8110b1036602440c669001f1041329484244240000001142c2c400101c0003480416100c4150070318000510090060f80c000c2800c0381a000560740030180002d420480645a040d942045c00d003042c400c1c490b0340c902d407030b801c8543e1282062000046180c00748000403045841520199540d2103505180010543d21140580543d640c000d1243c84400e1925880f560390041050702800d0303125041400030402a03281d0989030100d030000c2406944010a11800c2c0b4509945801d400041c5000740d00051a5034860f2440386c420700008008181d003804a855207000b814541105a4100d80c1c2048100c1c001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 327522985 1250 327521735 327521741
    0x30302031e070c141605011803200f010c0308040f290108070b040503060105040513050a0804080610030b0f04050f0d0305180601050904171b0f071401020d03020c030d 73
    0x9041c6a56a000f22070034903080c01d0845101c030103960b4645421031040704801c412a0400c84044510070f1070407480612020040014000080d0801020340d120b03411a40c00120341307a1240500007004551070704640603031800664408004d21401404a002d000015000c82d080044140040f40074854030794008050280e06482d44010340481c410204c81d4600500441340d0810201c00038018440c0c22a01e03290030000000c3d03403994148240e078071894448000035443c106103c0c0807502950b05c981101c500c10340d6482d00d041c00740c00078050200c4512413040000c4206803080742c42c0b800c4a410284d107820584403882d4114000c000200162340a20070b81c41c0d02c400c0c800040010038211f40d000c0e9400102810405880c110498144c25624195030003a401031026a940d494103c0e00300c2e0b4003007402c501203000281d0016803406950441c200203022000002c40c02d060200d442440e0700300f8079058403e84c80d1590740c903020f62240c0080303050050307118160107000d050082c0c3c003d010743d4072840100c0e4100034103150a2025 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 327524235 1250 327522985 327522991
    0x3040b030405060912030603070e0a0608010c050403330e120307020f0c03030c12160c090203041a0115030e0703060606020a0201080c040e060402070201170a200301050d030302031e 79
    0x402e50000c1c080200135007040c45083e2201d43d84031555461414840006a80c0304020301488514103d4031010842d0204c4952141b0003d01204c0000d1100034807040c40601550004c2c8415905101c0341020301482403090204800f1007002c00004502045240c3d8078180204038240c00d0f13040b94490100440d1003800750002841c0704030090750050100c1d41c0c59003138031801c0206400e40580268403e014840c29868081303180700750040703004100c544a10100c0019002080300c0b040203003012000110214403940341c2d800452003240510145660030398911a40c02d02201c0900c1404424900c00f80e001a402d07119130014079060240100322503100da12910380d5070407561b660b4090009603100740d070200110758000e01c003660b10100f110f50381402c02d07141105046030844c0040c1924032035680020808216030007044c00c0c00c080280070110b0503c0c0d203441c035a83c000805100e000c0c200c00c43c1002854203d0f80a0603c00c4030b060f030750041c00305030080c0803650f07040d07010703410242004c1a01504501d03803030b02c020841030f19684 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 327525485 1250 327524235 327524243
    0x10903060f0b18160201020c0c10050409021305010f0c030210050c040e0c031b070b0c16050303070c03020705040b03030d0f09150c03050a0902030d0c050f030c0304090506030105190e03040b0304 85
    0x601802c1c0450303a00c1c5441d5413480d4420540e4014041101501c80c0807071081d085c10000c0c0c0b425601201000012241d40c032a541040346071500c0440e5103000122050302400980d00700382c807821643e1144030b40940788680d83d03200c0100140e0064901c0c0941d1030311780e041940c11401880b509401c2a441e1008501c000c10129004c0a18041c00700c100513400c2c075800c0300e421160298001c01e5107411b095484944180c00020982c450304007001881410309402c01031580c1c90550080113490300ca0504a00040140400d1070050b4010b01c50301c0c1010841c0e00c3d00c0e210b00328911000030020740c54040c11480c3c00c0050540c014003400e4469a0b0f07955800802c4008030341104850072a140090380c3d814130b1a0140440e100035000d810f13454500040ca00040e100040c0302001d880090401d001258140d2400e68070303051540b44202c0741d40c000456034544542000026006494a4501c140001c0d03650300b05050890701308940d8440800100c803d44151690b80b6802110340c000c02e582580c1c03174651120900110f0780d1084c1c41c111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 327526735 1250 327525485 327525529
    0x18090c0503041a190905150702160801020a051e07080c1609060509060603191820061603050f040e18010504020105190917010c110c010903060f0b 64
    0xb0801c0300500469011101c280024121802c054054180540a07006140d141c10368865000741400303420000545032000050600600c0d15103404008d441e00751810711040040b459000118030310506009940e50601c55680d02c505240c141c015185c14130081100184104200304110004651041c000344000324982c8000c00714006a450410201c07034080e4041140c4030b2900c501802281d4801a0480c1c10590884032581c81e41c45a44c0b00c500c0ca46000c41d4400ca1891800b01c0a2124a02a04e00100f0070760043c3c281e69180710413200390b4030402c0414000c85900c14400c22255a400c211100c40490740d0380245031850801c0c41845460410b0b9005800c8540c10141c96010000c00409030412850059a80802800182402c2d4006042c41c05980c03810b030402590301c084082c0140c407816820004001e008040c0700d070300b800c1000550091405450b40d400003180380700a245154800250009800c00680d981c4c5601480c544600004241d11203c242603961182e0741c9070015600c4202050092030000c040c0c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 327527985 1250 327526735 327526741
    0x60d02011806030c0f020c102a03080901140f0403081305012d0209100311130e06010206060307060801090207140105190b0a050a030b04020a080d030603060c091518090c0503 76
    0x45c0401084048500c119848943c0c4c0580302d4850002040e480350740340c2040c2140307100c0d01003910700018040048464005442146500303041c2d01086960091000400801642c8032411038a0f0714610b040b83e80b4a000380188006c00c000a1041082560140c001541c40d003400d8020350324a802d60f013040d00720050031000311000580041112944207001c2c1c200380001c41c03400c00e8000203e103418102001e60700074903660342c80700c020001400c0c04885404680018400c03941d030b02c030a00301d01d81e42000e40e030032030040c49140c0000b101d0341400260001a40c0300358644021aa10b040803150280d400210100c0c0d0400d02c116411031208424090705001c0c410b0181700c5021700d0007a01d100c0088840f014001846114041d40c1000107468440081f41a6038104c0c0340140070f40d9550011481a80469009280c00d124407403c004616030f0541c003103002c0c0e0740b0a510038404441d0003042240c642000b4090a90302c621603003203090400d0f02940145401042d80403811085a50300d160240840300c0c16031007000807410000030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 327529235 1250 327527985 327527987
    0x100506090a0c210609060902130b030c0d020d06050d0f0201110c060702010e0d020603010308120c04030221010b0a060309170a020c120106030206030c070524060d02011806030c 77
    0xc85030340711400300c508104031803044500502c07682041003a62941d12007003051540220707503070b00310101130301c10901c0500030f40d56a2603050009501001d22080d40c5108810f0114103c04120203d900441400440030701342603507006030000075407161242c1d5000700c1da9920001106d40b50082002c0c071039401198800c40300d0486000161041040c1c044844450f0010750a09804c0e0b501e00065403859074080c41e021000300e420340049462402c800b8006503014802000000410111741c0040c510140b141038048a1525200038000150055000080d80000c02002c5808c2e00303061300700150703641000c02d00085206540c401c0483e2501401e5041040025240d10040007800040b814081c3c12407000b020007450310400e030500030b403548100c4540e03a11680c04010401c5c0044001d41090300659001056155642400c00070107000d54421501201c890041c180d891201d540b40c3c81c19412021380142201c04641d030707410200041c6110800d4124107101d00d000d020000029044841c00c068910758900150741b188003d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 327530485 1250 327529235 327529249
    0x1606030e06040519080c012f0c070333020318071505130902221202150d060b0c0604171908060a0506070b01180908030103081b100506 59
    0x94040c001d9100006020014200180b4001466800107014001c24010b14000c4114403416000c40013560802e40c0d0740150304a64041d01c05141c0c0f901580b101240c020a01c8140381e4014170030103000541010008001040d0740020480082800c2081241c07496010440c0d00e0385460500c14810040e40d0100400401d19144841034242143ca00000d02e8060700c0c040d619032007180f5080c030310741c100400030070f0b400004003c0024080180924090564485110101070781405c00ca2200c030115544601a0024101c400c54021999442c2c003d82851010500d1051112080c2e008c0c1081003442644d940000800d03000441c0901079100c82a0040c000b02e0034581040c194005043e41d14030501d49007082034560005040e0110f021582c040d04225001e07548400c00241d4511555201a40004001078150700b0000c103010014140c0b0740144640007280301c8900341108031451100004e11100e0300704010300100b001c44014000303900094007a00342c15203041c0c1e00c1c039003050341e50884a4104c1d40c4600503c030042c0b070814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 327531735 1250 327530485 327530501
    0xe090c190e210304030809030102090a080a0506151e0a0b0d0f050601020d0f08070201060b030106120c08060d02060c07051c0c06050a0912031e0203040801050606090603061908160603 80
    0x2440403100c009030b814102c1e0301d0341301e5031100a1000e1000150f150891700d013901955030303d400c0141030210660f03880030803d4a038000090111a503009000008001d0070b40441c030b040c2c02a40150214141507103040055565500b43c216144e8000d0106000103505245030000305030510407640d002c039040d8000e441c64010b03144058286415500054455034189034001080076022030b80b454082c402e521841d40503070040c8500d030046400490008000b00c0c82c1a080b050b511141c0e60700e02c034100155a201e8a08a0f00e40c1010380d5120b5201c0e0080640070007600d00200500215000c0d01c1c00c0c0d5080e11f90b42c400140181c03ca031103500090158a8515400340a051076488001b4407440c00e01c1460144803460040000d050340c06128461900d039a284030525104441c01d1100310f4554016455444091001a40d203821a2017000700d0740d82032500292081c1440e2058444040002c5d04840c25a241c2008121038a100300d0210400300c1c2840703c0000f8901020050003a00000c0d01074200001810070100400360380100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 327532985 1250 327531735 327531769
    0x50109140c1f0e0603040f060f0507020d03110f280e031005040804170c040504210903080a05032802090a060309020f04020c0c03061608010806070e090c190e 69
    0x900b000440054006540100b20b407001c0f602e0513501d03500c1d45000c1c10804090744002d0921031074040d030314200c08056032103c0e000b050983c00b140d00c8010742d820100c0aa0354070a1000c2003081d07083c404c00c01040008009899040078500b020705507a03100103d4904100c50000d2028001546400103904038101071010340e05c030302103500c0300703000700e1509803168a854031543c8200d2207480c3c0d0030744200c142c44c001808007180d10800108144501d003000d0503c403400f03078129514102008418610180c41600441003031044030740c4042c0071410008030903000d4139290402401c000d520707607281445885416100e11990034240e926070b00140c440c0c07090303018440a244140c010038103161504a0f10800359407a001d881540042c03c841c09030b9150200e6006a00f802070080c840b603010300c211410302910b00e02c6002102260b001c1c90751480a103a0361100080e42c0e40c407042e41ca001c0443d1a0106000d61410801c41556004220b008440d2914800111882a403090034401c0c0c400502c440c5c03412456483d03c541d14000c0b0101d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 327534235 1250 327532985 327533029
    0x290108030301150c080c0d09030b0601020102040e0a05040c030c03080d050f010803090f240301050306060f010c0615030804030305120106021c030216050609060a0b0409110d050109140c 81
    0x4103090507030303a41030f1404a58244481840c0700d1003080400c10866410840040a83d82c04d00c2c0c8503400603000c041203000803510310480100003001548140b007071702c0c01c0754a0482402c029448100000005100c0540140c4141070a07080103c081860f05251800842c4a90b0fa5141d681c48411403200071110040c0c180910041450010812150004141c2c2c02c4001c0441e080290300103107200180050061740d0b002013901a5034108404e011100300041e40c121001503003555003e0762400708000381e8402605483c0d01140c81056598045440340c0e02040ea080c48440000b60403580f04d07114140990465030003100000c4e03000955050401c0d044003002d00504460000b030982000d403442c05e4480e510030140840c1050b5002c502c0d00018000354179412811a000000d642032802e0a54140361915009c40d00c0b00c2d600ea05000b80f851071414180308403a65160800d2a88107400044000c0201116181c0010f40356903480d801b01a011540c080e8002010014040c000c00c0025102e109110008140c2c0480d00c1b9803060b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 327535485 1250 327534235 327534239
    0x9070f0b0a120e0609010c0201150e0f0907050d0c090c1e0e0103090210030c0917070b0a030b0306100501090e0c040902030415090b01090501050306090c040c020a290108030301 77
    0x8001010748845800d01d0030120400041040800000d024155082030030384075410070f0000082040d4080d5001c4059507000f070107a0018030424142e03130240c52068900300107903003000454ac006a1034107241c2004417142a00c0710395a8840000c1c15030070124030150f0f0444e180903400c00040450b44143d804894040c141f4007110f80e242c404881d43c1065202c0c43e8418004044280d030881d80c8030b94004c05200350700800303510581c1210301c0c2c000e0003880701d01c16000103c0c0220300040741103252016007038007414200008140b0320781409070700e022a8215408100c14036407107100d80340340d0341c0c1c00b40f0840380300d00c07a084140e100c81d52810000506540841d400805012548824014180e004030100e600350b81c5c541c0c00240c0e0f00e0700e07070b40b034003865014040c00f4001440b4075209106040003180320310715040318a42e60f014007c0381d0700c9004145d191081034809070500d40c054101030380c5608007500f1010320b108035801960040049a110310b44ea4070650314102c445051013481907420044000314081c01741c030348030700114110341c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 327536735 1250 327535485 327535499
    0x1a040e0c091c05280503031905010b030907180f02031303030c110a021e06030403050316030b030303070f0302040b040f231e030313080c040f020a020c0d0606030c080609070f 76
    0x22696681007481d0740f034600304e841e0318034541d00a4103003603809001c80b1b40e00d14000010501031010b0034031130030f040341c20000001101d00044065034020300a220207040054039003d59204045030403040060300c60340352540000e0000d03941c80079610031300107c0712070b2a4402c9245001001c40c0e01c10041780341403150b5403a0b08481c41100142c11515039034192192032048810f04212070244105010544d8044400410001003543c000051406890b50303680928005a0114094041d640220344a540641c000e0000850240c1f08446840401003182001441e0039110160145180e0240c0c101180300301c1551401c02035405495034440c514040d032011080c02c2d982d2280000c00608a4500e0721440d140c202d0042480c13550b081c001c4421310a03408650307048403543c031841c194030381c0380c80ca014900c40d41c5041000d070000c0784107000f124600d03119a4041d1800c140124104021224800c03420ba940c20b40d22800440003d200e01d580f40040c0031100010540c51034180c0e8020300d4028203030480d00214054020401c508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 327537985 1250 327536735 327536743
    0x2f0604031527081e07030f110d0c060b0a05030d050928030b0705120708010612050c03070302070f080409020306121b010e04090c0b0a11161a040e0c091c05 68
    0x1050f4010507a42d625124030095010101803441c0103420804009045030405d600000240b51a10064840940c85c00415248540382c000620280740442d40147e84030b000601325503c20451504014944c0c400c40c0d4807100840d241950003002c40780402d2002402c41d210780791110b4825201481901d150a03000c107113100b881244801c510005000e02a4240031a50660151007521482549000424003910702020300800c0b4960a10480c00854085025031406140304e01403984500510701003640f6546030200d080300227500000040c0d5074a00c1040c2c000c8006039040d0020001040701e000c0160326400c00034200b10b1a18045052200ea503030140500c82a140a202040a9186000d090030f4603591008000b00307000c0c00c428140100103d054013000310711580d100300034110711012962030b075844c507120044150780c0d11034410b500c1903141003d943c200003000740c50012154070210034034140e00741942c907113029040c2001550350b882c402c40c0c04103880c0d86c01e090601d11703103030b070052142d1400c484082e00345c80386912 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 327539235 1250 327537985 327538061
    0xa1a060406050c030d05090a0614040302070e27010509072c180102030a141609170f0f0a0203011107020f040f11070624032f06040315 59
    0x5000d0007045000f80c2d4181882a00e40e6500d14110034030841c5840c80e407458880c40151f0003150098581030b030520640d03251800481c82183d040d00285642e07410610503500c039100040c10340c489103c8880c450654001c201c4507264604081d20004034090400e02481401e001c0150400d031030060f00f105444040d126034200043c02000c0c420300450b02a21080040444c2050044805c0e01070340c0004148040c104596101c0c0010182c0c02c02d009030b03141c0702e5030807518014007503002c584009817144206000c03941c41c1c0607000d020704691804403031003c50707440f4040d420f152142d0002c1c1029007202e000c50095003800e000300c42554044680c0c85140080c641c0c00102000c0a881305d890169a4030782d00f41c03003503000d00d500160030b403503040420948440f1a4134141c3c000d80b4082c40c00514100c080940304116104c03485a0100307490380801c0c1401e0340c08142c44010013444200b00c0e0303440c6801994110301e00030b483e02c3c002040558050302822041c10741c00d049a2007a200801c402200022b400c2804050007030310882c0e0014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 327540485 1250 327539235 327539237
    0x12050607030b040908160c0b0f0409110c070602160905010b030c0c0a1e02010e03010504020603130f02040504030f0323070507050a020a0609290708090315040501050a1a060406 77
    0x50b051001c440402c0040400c603200130402200040c42240004410085042d02ca00c0f130342a0700020340e2a00318084540c0503000d403030952003005100501c000700564001008076a034000442d170170024028205441c1406660049001da080400c940560003030a51480025188089090026502d0f14034168a184002000501503e4011a0f20044c052051000d082403607005021000c401140181000700c0d44208201207000c20718420305c244242c01c06006580c41650002c00e02d900395603644400c0c00c180b004004003280c0c18856581d5080041c2e60301d00c030791401140030360754004d0104200304000d800c0f80d4808960804225003e010b40e00f641860031202c0360301c074040d8941107440310854945180b404c032417590000d6000010710804155180d1010203480bc1b04d43c858a41030003502e00d20400b81030050300c8080125030440c104012008141c0342d800601d090040135040721015400f220241040361019641155565111814041e0030006030242c1d00840303800108102e0141210030014031940308030310484c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 327541735 1250 327540485 327540491
    0x80709020a05041208090a0b3103030309031205010902030f0c090904030f0201060b0c010e071707090213050d05060412090b160c0515091e0d02093d1205060703 70
    0x16017081150380549041c0075020b890103200540f0352095010540092032011502c0040800b4400042444620f0081403050045d1442d0010304584045010344203000c802d5090000b0000003002104280c0302d018001e0a10840c010b840342047c0952146000000c2c00c202002d840a000700c0f07955643d100501900641e2600f01000d030482c80d14826405003c040c1d00c101d13070090011500b80d56510040d00300d900341c441c40200780d40302d0b02d413210b2400c02440091040e02800b40c1c030030b00080c800201d242c1d006050720b080f488402e2410701d645d1b82c00149001700d000803c032901e40014040c001082400d44114030b40b5410f609000d240710741400c141060601400207200c1e05200d10080c0358060040f0080404050440544822a640a840f5480708554007010445010b0305601d60221903c2000d001021850480101007000c0c1185a800304140240050107200e800c2040448040482500024160341107100005006a03030700e428241d1400485264051b9040c2898200748100040010500c1c60f80200f05003400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 327542985 1250 327541735 327541769
    0x30b01051e090619030507031205030f16020a060203070c03031505011b06020c011d060c1c0902030f011e0e010203070804150605030610080d020a020120030d15080709020a0504 77
    0x40c00c03c0f8001141c06080e50036813040401404008100c0710243e038050b540d00141d900d039140302242c81d440111120140080010045250301c6820303c201d0b00c0340c04d9140704403240d01a06446d507200b2680280c9001000ca99021810400c15415001e00442501d10171034139a442071030040043c2c0000841038684205101d294511003c000059042d924010408002005800744003e88460700d0108403150f000c9520942002550004060084a2072018103102c4c1e080d40090000d40600501002d40c01242d16004100700d00800306400d2240c101c032908208904001c80045050142c2240c07084400781140b83d004204202000d600582480d420962021001d001c1c403440003485030062840b81c00c40382c0d03d4001c0d0700c01e00000801041744442a500b8000030b070307601c1a81c0000180d039602c0701d80c0b00c000d01103460500181202c0080b103800e1140b101440040d2440e1249141c10003089615440d1400d1010070761602c10b2112900402000b07010306940c0c2021442c240740358201070320700d024a210b0310114040e2040c039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 327544235 1250 327542985 327542989
    0x1020c0901060333030308180c090a020d050703060f0906050d0f0804090606030209040f0533060412120207060e0405060a05031b011b170f07050f07030b01051e0906 72
    0x600741074908002619902d44143c00380c04004c0100f1448154002007404012516580700080030401d8000c0c5103000f04980d01e0b0002c01e10100b182c008041444942d4280415414840c1c140a0240700e00d9550390000340580c1040410310801c40103401806410303180004c00d0081e030b09c03001d640015048d0005908000d81c1c4803072400a01030300c1650041040c80c1d080442c0020f5968142e0054000500d00321006d0155000d100340403822900201d9040b603c48030543c010304140740046002200803c002c0401c89068003020021031000d13840760f44041a2814021614814800140c40d12072000000d88041c2503c9403910b4030041034064201d2000e8412951000810301680c1d51303540300c60080c100503043e40c9a000c0741841c0e10606070f0f42e407603405022a82c080c600c960007a040d100440078003640450300084103034920341005809d070066803403506102410402080070480c1000350282d903c03803180081602c1411883c200c210028103903c46801a0107204c050605015a0310985800c842c040d21120340e42c0d501c3c000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 327545485 1250 327544235 327544271
    0x30a021002090f060d1e0507050706050901060807030f05060117070605090f10050304110913031d06040f030c0509040f03052a010b040b0612010501081e0a0605040b01020c09010603 79
    0xc0380640c4040d0004040000ca01543c0000100b01c0c3c51b003154001c100d840c520040300b036a9003168000000b400400c08800084c0312540895001000200009140c980311304690749848201d0300161120650084844208a400c000c00b5014100e4290b054514500202030603903902d13158002d10003031100c003181889140e294651450341c0e1990041441150305100540a42580c4c010764064512541851145038282003101d081c0b4022440c46024180e0b00541e52001c481003070100d00041504014241c1289182e80c032200588068003d00056501240c510300c0c00d200c1078001a40300d02c1c06a034104041002181c098003a00906a80608015640e03804092b80d4820382c558081080b003d81c50340490100c2040780560102d1040306040c0d0301004011032400410113503010703981600220340d12140c0140a9940305440840d0418401080b00440110b9521141c00c14942200c0720700c150740d550349080010b072078a03005445400744280084c0444049003c042121080140902001e0540f1010350b0380003154900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 327546735 1250 327545485 327545509
    0x50d0501140c03060f010906021902030709050f1f05010804020d050c0a060302190206011827060911010809250305070b0a02010605061c0c0e120c0909030a02100209 72
    0xd41540c07207107000705040200390400d441c69809440355010305003065005071090402d585072500200500040302c48864100e00716410101e03098000c07241c0010b24503045008550040d00380400b05560751a103650905036850b0500201900160303403510801190360001c01c29600190140c41310701a500781420131034034016101401680003807001030000382495042c1e020f0070681e172403100c114402e0062401d0480e650b643c02c0c00303841003004110340c4007074082103640d21002c075000e4917120401c2d5a0702c500c0752a582040c8048801c2ea82203031280e64180800c120b04038000c88580c070074240109241030034041c0030345c5d68a60586d05a01c0158a81c1d40780410940031098400442d40718080f900c100c0c2e00c3c0c11062196130001c83c3c108001d5820082c0c08207003840c0c000159002a0741c462a03442454030f00340d001c40090150f00070a4002e005000c000090706480d080b00010b61000320720010714810701880107020401800030078620300d6420a1040b03400f842d5001c0743c0c80c2d0755900b458001507220300c1e44000182c0344100c08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 327547985 1250 327546735 327546761
    0x6010b0901081315020706060e1f0602010e1b0d0b0a0501080607030528060b0c0f010f02030405030a050306010504090236030d08060f040606021615080a0911040606030b032401050d0501 81
    0x2010400140070760b107640458612b807907401014400d41d41c1301802d03401c0e512460320400710354100410f0071401e2904450a06a1602d0083c0b008800e2070446e1036a142850060740e40b02d0b06545c4403001484424000c10440380c110741907203800c104c3c40c500103011001807000c00e0082c04200c01900844001e43d034560f004403010344404140660317508803103580c59640d148542030f11780255003080c000c4180c0f160307a0f01c01e6a118940106c0607519001c0e02070070894140e4001000303d4180700c004d000110340f6042a1000d80307040380340341c91a0158104140d03039090115990120420304114038400304c113050340b0041a1088804481e080072003041e1079500005010354500c400150f041460300d14009840e03540000d006010600954012185a4540c4114002c0c02c50031078451000c01c0490000c1341079070380c181d0311900b050341c0950050080950140d00190517610726a01c1040040e440d4000c0340790601d0140706040c00c0d10480d0840004211001c0101e010300c61051040318403921013085030b0405d100007074004030030820781 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 327549235 1250 327547985 327548009
    0x30a0b0315130b090f030301050105030a02040819051b011209020a0510020304210201170901150312020114040b070c03050c030d1d030a080604020c07050306010b090108131502070606 80
    0x21070406000e02c0700103104103590516244002c81c500040100350b0008220029000d949036070300b4400190346c568805000c0400f203513800c101c0000d503001700b4000d500e40320a402c0041800101582085468044030170b0107000b4444001d261108941e070003002070513881401c10306c086480c4040780001100100e450b03102c16009107451840d413031007a601100620503202545003681c8840c205032020441d4000500d4001c1c0482d00d40540e040c0c0182654003003980c0110072100125906046001425078021154030840d1000b808aa0301e07516241c086c010110b86c0004000001a280f5240e261310b01e841c03c1c0030346040140208050800c0501d03204804443c0d1000001d000c4035a6401c650740030300001c01c0c400341880d01584100040342c0b03007254040100c0e603e54449950b0b80384181c881c0401c000c0254042509106a88613151002409440178061a402480304a80f140d440700c10030000544000c50080554404102944901000491502400105142c0c0410050321681c0702c2c903291004064540020700360b502c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 327550485 1250 327549235 327549241
    0x9101107290411151602100807050d0510030f03080928060504020d20040f0e0a060b030c03010c03140c130311040b0924010e03070b03060d14030a090f050105030a0b0315 74
    0x100400c5424010b1310940b11402c01d0800c00c7c004607540360095407032400003a002c20800240b15070b540c000d650001d084a0381ca0910135a2640d40d100980900601140416095810804070b12000e002100e000c071882c11401c2e5007503010445040c1c10000041005007030540d280041415525400c00411440368000d01a021807040c06501d2114225902551807087e42085440380c220f40890003543d075800d200038024041d00182d582c410f00641007d050403501413040100803c0c59603001d024018581d0081d4400048040301e030b103552030782c0b10002002e0b41c41101040041a50491500170040101c82e002011400421020f50024000d0230310610910ba00c118048184003901140f00c3d404402d002004100e03034003241030383d4015154141c002d8049541a0804101008944403c800035540408014084180c100150380c0c0c1d03030f0940c4482c18960810340d1020455504442c1c001d4200c801905103500c40303105603890940020640e200041292040b00e4a400c81e6031303003d0300c0c1000648484440c03034412580b00d03d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 327551735 1250 327550485 327550507
    0x30507150e070e0604111606090602160c0515040308030703020408100e06070305090c011d1201050915010b0306150903010609051f0e01030b0910110729041115 70
    0x90450050700024400f80003c1095440d00d8803c0d650020088420141408560740b58845510500e20040c0c680343d8070f40440200059840c0700918005c5003050440030b81d03000c0d6003890015080141c003c180102e6a94074030132981c030504c4003590100c0340d020140e266250b80e840c0f02200a4003456010813098400c54600b140340c140700340c02141110100d101205e00c0f598035004202d0580e101900d60b1a1140c01c418041b104a5100300180320950501c09003e0010864940214400041d142000304881c0d40d075000b4844e445805100a261428494032048815414800344100d01d01c0090700380751240310300303190703c003501100700c0b040e180103480c010f000f0080702d5520a40c94014140480b41000c01030002d03c26103071082a07617082e220580301d4224202d0701d40da00310340d14420003030405458010144036201c640300140340c07140144001242d241c43c0c1c00d0788894907840c1c00da214400c50b00c150690010150301080c0d02d1860201c0c81c0341d00035000f500c129692002c19010074184440b1200c41054050001031311f4120f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 327552985 1250 327551735 327551743
    0x51f0219030c200d1b030803040c08060f0907090504111003060602070503030403080702091f06020312060906011e0302190206060a0503070e01063c120501080a030507150e 75
    0x70710701074107149242c0440c0140f2500c041c0b2a51100310303071201d06003611401241c0380340340c0c41440411030800d0380f20064881e120201e507600100c0d030455030fa2a40b04001d100c0321600b4888590003600018480000d41441c005203078a03030003980981d5641136039680004040c0310b0b0001001c0454500a40b12044030894010003d01a10f0b003802554050b120701d00000440d030400004580440c2c0e085207030981019201d608210700301c4006810404880b0122110428841c074854002c030050078260020b540c0c0d440300401c510071802d001043c541c880c0c0948000c005859820820152180000040840300601680d606500034020041c54560040007217801b07501c02500040c5c00e0780981d504403a00d02d5041d690340700700341c2d0340d5880b406056418018940100402030240380700414002d040d00d40c488002c002d05100d40c80403031008120000c0200441c622807880c50b00000e070300280d040040c0c4244003540c10b164600d0b40d1070f0b101d018000c0411400280080601038036060103216000d18440c1803000c0000f04014941d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 327554235 1250 327552985 327553007
    0x181203110915030c071e050c040b1c051002031503070506041410091a04170d02211b0312070203030708130f150f060f051f021903 57
    0x800d14004412000c4000441550900240140720401c6210384560710052900050480743c00f581c000e0080c0b00016100003400081010404040a0824081e0a03d545800400d5200d28003035498601d030382c811625905004141c044010f03940c07026007485442c065141003040d410b000d4040384003000340881010807180b4200142003c4080703a0f5441e0729481041090b21451140004c00c0d410014200300750b0800c4480e02c0d09c0588641081c09086642e84040c449040c030719903880c03004480009050002d16a08203d260084040d5002061406c04c070510103980c0e81c1000e8001c1c00300219108140321610740450440c0d0245107541520041d041218080e5980d07600450324a604036540c039030000e105544000196031041c0203541d142012031f2074012049c4080c0f28215401d607040019a448540410359665041848080145001815248a030110012140c2541043d201019511000c10842d510100c4101c105200f0080d01c0402c0d44042d1810303480d14202e200f5003840d2042e2043d0348420325400c010741c01c2d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 327555485 1250 327554235 327554237
    0x302031c0b0f0603101403030c07090c1d01140915040b03250816140327071805091e0a05010b090f0a0903050c1609151a030a1812 57
    0x201e4118102c100211030004585256403031200340c07804c00c240c000304e0980c1820341d24003409403450101b0590701d907400c103000344c0c202c0d11019440b021924121030b4400d9030302008412001120701400b031140f0000b030400c1203804451204080106200c12155076180051041e80406500183c0e00c0b6901c0c91504040c4c2c00c221903484100200248807091144141e02041a200c100d649540d07581d920350340124011003010036100100b003080e06901c008000110f000b1401000d000040741c4010380701010791810007613101c080d41d070143c00040c0100804094181104890740f0810408a010366a10003254509910a40300c02281504400709030030130b0101080d070680c018018030007801a40070110612101c5502520418000d9058100088083c401640b040080364803030316017685404484070030f49184c4200d030407820244104070101000070050f1441802500f20760518560700300b070700d0074841480480080c00b00710304c860b0001000500c0ca0341c0d50703840500b282080c82030035289480c06003040705c1e40300800031410b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 327556735 1250 327555485 327555499
    0x10e060105040204030c0b0d020d1d0708011125020603040c0303030e0c01410408070e0c090613080303011205010c081504020a020a0206040308120a06031e0302031c0b 73
    0x85071505090089400b41c1e604000ca4103602441c04500c03805580c040a0345140440e401d01144034100010b0203818405050511a150702c000c020a04900f006500d910000c0030343e140440c10558480c4010035107400d042c0c1d040087c80080701200e03180d9405090000020b6104100004100c00c026001032888240c0e030281c0c2e420041c02419103a0103690720405140280825400c048086c02c220b4801607001c00c4060240c01c4145100c0703044228540c0e40115080c240030007401003801d00007010200011002403120400d010001c1c00c00308000c800601c070301d0040d40e00420000883c95503001d0038441c9480100507010841e940d0350f80d9401c60030280390344220203d525500701051603600ca031183c40541e014a4030380002c030f0380320701c0300404200c003d42c400158401940244112180540c4e11040900010360003407070001c1e40c40400c1180d14501e544003d1415030614500314040c4081905050324234034032900090507030400d00541c281039145006032001c20541006ca010981b8403c80e00b500124803898043c1e500c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 327557985 1250 327556735 327556739
    0x71203050715021c09030203030c071a0405011d031314120d080103020a140306010e0a060302040e0610060215160e06180108060d110409080903060703150501080c0307030507031d010e0601 82
    0x6139082e20150000680181d01c01d101040e84401c4460081403018802d07210072003600c6002c080d012007480300f00c5080d03034203942d210700c4152500d0002d041e00741d407203048a010798a40110006458200d80b40350003460a0022169100001600d07512601042e420a1504491124150000050000c40240800c0b40035500030b03440001c20b403d903032501075044800240600001da0034981ca0098882000301903820058403084000050380b11845515800384c0b071740000d801c407880c200e44400c00d20001e542c4480115808100d00003003118000301c410b031300030792240581c02c50030640005c100d80c0400c0d404103140d4007501c009884281104450380364042d2007800c0c0c980400d02e40c0d9020400c0030340c0e81078800103081ca501c04079105000d85025401a9030701032080500034103022090f804a0320b03001040b107103040425500c2d023000d8084003a0034210402482c0900c0d01d07000c0303840d000c100c0c400725001c0645070400b0f05481e40c02003207a4500942120f5001c2e04242141082c10020941582c0078110b0540009200e02600c400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 327559235 1250 327557985 327558037
    0x18070e0a03050a051522020301110a0513270203060d060501080c03010c0f0203070602091813061104050f04020309340503120708070f020a0b0903010506100207120305071502 76
    0x3d15442400020146e1142202290403140b4a107400c3c40c003240d055580b80102d40701c4500900280c1001e000c030740e0321140c5900e030b6140c861509080a4102a801443d8080d406540041320700e199030080ca80c6210150b125101ea0001c102005905031000380414101000451040c9000513000d0120714203c0092100c01801541a203200b040041c581005810800c00351300414600c2c1c00070103113030798051312000f4000307030b07111701c0c100c40650958990840c1409490110203106250269111210b0040510344c641450600000e0700d080b8810741c2c40b40980e4012001130444402480800b9a0500b0141000c0380c2040102d001940003051410480140111540102d464200092641401c0002d0b4a40c0c62404080303440e525815000050115401e00d040c6072031000507190b00000a00404490030020789a040d0300781014296440180340b94041c0e003054001c039240c10790002e200c50840d209061110f034044003e041c119000d1042420250100f01c001900141b15149076000300203402c03103020075804188504071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 327560485 1250 327559235 327559273
    0x12062103120b1e0d1502030709140303030601110114010603150812040e180304060c0308010e07080408030703090614010303090f080307110109210c1418070e0a03050a05 74
    0x803140e00302c0c00f01d403200180d91151400d048003903440103010700a0001641d54804111078031170031852540c0d402100740a5074603045005040901f03000e9030018900942c11021955034040241058100802c01d160030301e031804294400d130340301c00204070300d400c0c5580c4402000c2c000e0180c4046e404103503c1e022000040c0100f000c28040d10345446a12130601d003902d404040003407081c002c0c2401c200002d052400c5003030302e40108011308c0100340940320301a14440344c0c200a068600142d114040c96183c1d003027000b4445501840c5254403d07400140192207844902c2c0c100d0061140000007001503192901616204d60066003050480e031081e40d1340b0040036211480143d10b80079038403d5950907801130003410f00180b03041900c564980410714000300c90564440c213848824008421404000810141181c1441182e24502000c0d01c000248105462201c2020800011207140c0640d0307404011404204c1c0c4910948130503030f10140c01001c1c0c6140d50b8403810525100c516000e42112644034480f10603484501c100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 327561735 1250 327560485 327560501
    0x601030b060d03090b090414090c040f0b030303192306030609070501051606110708030a0b010f0909090516031a0604090209061002070801052a0405030304061206210312 74
    0x940d9090034070345013100c02030300c50300b050740d0356a03025071200042650440c070322140780d118009c3d500003050b0441c40b050078070046908110141030ba85040801c0d83c0f8041c0c80001c21240c0007502000c84070300140a541c41d29000b48400b8991428101c01310701c80c1401c850f8094801e0380112401c400740c031500d403500d00d5810f0355400e082c031541e40411414031031083ca00f48080044101d03d805407130045070b0760104003503080761a480742070100c0f0204004820b00010041ca441041c0042c0700c20308080035000002c1402034554108cd100c1c0002c00da48078401542040002e01c400040b16070901d9200003c1a00c0c1e18000c900c25110300180b10074407155100080603443c003400b0744c44989401414a8456840f01c806000041d10118285010340c455040c0018081109106851003a2112080f015400c1105280d404690101441610f00b41c231051100303002c00d6031b010045500b25a40d9042102203004860075403130281c480d9900c9118510b4040300c2262603c50040d8402c50041d109035900c0c54065114071134802102c02a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 327562985 1250 327561735 327561737
    0x607050d0b0d031b0f02040c0804060b0f13020703030b060c030408120a080c1b0a080c010e060405070b131802040608010501030e0a0b06030111030a0903080906010305032203050d020601030b060d03 86
    0x260545a1000781c3d210890013402e0055401c1c008080054020a0a85d0507560700c0b440050700304410032052241601c00c0100d03602080b02c026110000d0640062014070a1403081d221705540061001e04260099000c2c10340484040d00e501d44410010011b03d480c0d80162085e055035008100750f44165504032400c450070005c1c0d03500c0c1d5008503140c520b44000c417900078040c8040c0c542e0f00c01481c0c0600c1c240401020407018890004980e42d081061300090a40e038001d10303501d203640e008100748030000e40045082c006840580d03007003c0e01c0314044000318000c0f00c0da65000d10461540000440d00200341a00100141d48140c0c944100c10390f03a4a0045040718012511110b26410816040000031401c0c017041d50082401070000c681c213810001740c80102e50044d00d5583c900c90360780b000d401c20550000f4000d0b9211828501400302985952107141d1079200c1d040340256900c0d00341c00300300c3c0608002c1c140e103005150441c080ba820a80920360280d80d554087c0016210aa0b003a0005500751a01c020091480303681 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 327564235 1250 327562985 327562997
    0x13020108010e0115050f04030206030a050a1d03070b040f0206120702060f131502041a1306030e06070c0f0f03180b0a05090906060d021c050a09021c03030e0607050d0b0d03 75
    0x3454421034054001c8080d03203408506c00c11000016035240d60141d801f94072500c0e0001104d0402c5a9280b046031305200130311590a141f0070b4001100e4501100b6685c1d87c582160760301c14140d50350320f00f9284101c0b076044000d601040203c2d1419204040e0a006842076505400712100c40c0c485504107040035004641d03111001462110030b1001403c1c0c400200c499142e0780b903016061680b034814807100300c600c16951004c4114046540c0101440d485409002448941410442e0410a000d11074440c0801403c94051140c01c294460822844079011004242c000e0500303548070489250003810200c03d01e040ca9181001080d0204414074401c0c203d44a00030941c40705864410380e0000d100310703144c006020550004050002189200c0c0c640010000840c528240c05260307400c04104104540340a0401c0151629040980d8010780f224280b501e40c0c908000440c1001c1c076101d1074220050100f0042c00c40150042c903080c40049504400a007282d0148140240a046520800d11170303040c491100240010700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 327565485 1250 327564235 327564269
    0xc0a0e04110a12060f060309150606140a090e04110420181f0201021309140406020d09020a080f0c0105030f0601110a060e0a06060819030e030c03010513020108010e01 73
    0x300a04820601c0c3d9010324000c21020b45c1c41d000c040d24020264081c0c40030075154003210301040301c441041c0550308204d040c100030740b900b4502d0040c548a40111203d0188000041040c111030141d002c000040c600c1001c81040ea141c175113809001c414003603080e240120305000583c0e400741c60a55001c070480c0809980d4030305006034035521150400c04644400d0f040003150419074808041c2c45940c0b14020728940000d6524050304640040041e1582e0146118910b084810111458000304030f58105403c82405038403054080c455000070410301c030000758003000001d0000758003040450b920051543c2e03a0255016584100700544041c4001c032811104040280000740d420f6000b8030b80100840f820307008965801a0b1a9107040c1210070f42548940030b58400c1c80f422041100c62700403000035005080251001014101000601000d003a40003010300000c001c00781d4017601c2c00c200140400800500074402407c042c0b1951156245da0314061b40001c61180001c210100c503010710b58100c800200007011092 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 327566735 1250 327565485 327565487
    0x14060f10030605030a06090507060c050c04051b0c0606030708030a0c12022a0a0f211b0306050115020a0201090605130f0b09040e120406030e070e0c0a0e04110a 70
    0x1a544080c40c0e014540d44401c0494152002c003c1c200300141300703040c001503031401d03424460316000c0d2070303801a002c01000041d402c1c0050000b003208000e815041c1e501142c0d0f600d50345c1c400343e5a8480642e490408c000003003405400030b0000265a0b0150382d040e800e076440f01c0d48403a0425168899002d95078040340300401c81500146600030f07044c00d000c0c0244107441c4001c070564058640500d2070040019000c0500d800c00c1d4451400c122003400816040c0d101c0c51205160882402c0010440d0b4041615541ea05504a0900c80c4081c0d501c00540342090722805100d4503480c007400280428003c65240130004644041894000600e081d10705805854000300039180c500300b111181d1042e280780528010300030000960009a4061101510000011607242c0f0242003e1004a84140400f40b120780d2020b041e0000039090002140c003500d103603150101c0c5003c213140006183c41600c0d070002480041c0c403400c2141c40c6003040068142c003610b541d1203151201604017003000340c0303015144610780074400b00242c2d03c1903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 327567985 1250 327566735 327566749
    0x61a1b0316142107030305090a0b0406020c0717010911330702040507201f020a0903020603040c0e0f091f0b1206010f0b131203111207020414060f 64
    0x1d0003102c00c9036190101110410a03c0c1c4000071801c0082c0c0012501c5001c054060040c142c0c8144410f00802c130036007494441824455001d0400b52007150300103241c000a0b5024090034015022040303501b908003262061040c000d1102d880255006020070481c19020f00d03101c003d50200070b071204000100194070300d680e00e404107010005032030040820005030300162218045e45115001948a0760b12010101900401580c110308800040e41c100c03940510f801d41140e0403c5105940c4a5170040c3c891b610f02100355000440b84e000607610035004010031040111150640c81a9018900c06c603403151148903e4100b0310000359000f4890340c000d400780390301140c1e000030030044400c40064081070881c01c0070f008c902100302c4c2c032040201c1f60b00480010b00000074038204040c010002c00c00e03150b150540ca0b98a8030750044080c024044000c11003440e01017458410a00d0312643e295000986d100b214003000e070303030f801b9030300c400c50490249003820031078003405001d603d2040c803d00d4064820505d04035024104910 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 327569235 1250 327567985 327568013
    0x2193924030c021e01021306030903021c0504050a140301060f061707140304030305070f0e010c0f0c0f14010e01090501120f020d0207033212040501061a1b0316 70
    0x8504c643c03504160b2680c40c00014201030b90100d4001a9501382ca02c1c1c00091400480e0080d400f0b00d410449444006503001a820b4410052012160788003440090200c91520407648119807241c85600c02091200c1001d1400600764022002040b000340e03216400d800c006600e10600f0040707100c3e100303501c1100340904505640704000e407030004c610828062030803445400c10384040e000039580750108665160032100c1120702031840c2c2042c0a0340155003000802142e00d490008100c0041d04550b001000b8190310b082003c0e0038141481202d240c3c50351943d260100107244c4403800220341846400300c03940100314581c02d075041a914900b5039014a0180c8010b04807100070188946c1d42004030081000c4103201409a8620075502d9140e181039441d00d59030f40c00f45100038018413000d000c4d0240c48090980048035401c084c0c10310991002e5813581421401008a40d110021031000d114074403050a104200034640240c18008080c0b03a0070300211a2544c031f0250250507103202c070410013540c020648070810144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 327570485 1250 327569235 327569237
    0xa03080c040f140114040b0414040f06061119170315060d0209181e07050c0a0f061b0203040501032a08010e130302193924030c 56
    0x7252582e40c048044890755036a128540e881031001c507071403040da0b0004070b0b00445101130300c0030380c100b80c00d0104010700ca101c1c900c5860350f149007000c40d140e165192900583c1d110754015204218a95031981c02a0260140c0c2e50300715400d020302d00d00769180681c02c5050401c0d00e13800c07072508003150082d1350000c2c240358009098a40090310b036000d000d899541d40d400801e80d03080800c1e00580c503003c0c91000e2002041e0802064100c4090318002c200521403c0c002e542c414021581100355603440b625416199445036100d502003d0140031911002e110000c0000368034244070340801c0050b941c0e40d40e0320300c2602d040061002e0058104020070000e0350310130f400510000b180c031034210722010350343c115020f441050f1031081e10100e074070742004110303180c84a580664840c8052003003400380c20107641c0c0251514084640c0c4600f20340400201018011500c002340c489070032501c030802800c0c1d608c3d0b40c4400a00b0401c880c540f80410366078008903d10041d000d6401400320380b000c405c3d100c054a600140c014045040d0354034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 327571735 1250 327570485 327570487
    0x6010807020c10090602070504020c0309010507080708130e090c0a140301060f080f0c0a030302070315140901090605130b0a0f02090310020c070902040b070f0501180507081b030a03080c 81
    0x8a0243d6078081d4400916120361500480646000d002038180030040e40001d214a2051041e240040d03008812070f80015001d00e0076642c2c0e040c551030203075a00d000d544000303400c412002c943d60f0f24845110465200785c400940e0201920b55038401d404c0e83c1d481c0c07e003402c242c0015641c1810000040b2140c250408960001d00110303039661541c489228880180c1e016030324560010403900f2403a54140401601800d050350b0800c0034505549000e555640640302c000d24401e20300980c000c1c42c1782160b2180c500d522850a242481d414079003c40742c00b80c01720300390649156160a0116100c01e540341e800e004815400a0050129070f240d2100400038101710105182c0e05800304102d645580c3c1c18041e211144a51800051b11400300200061a1000350740100340201c0c410003007484008815002d6031306480e4015050142824249000c0c0d014060035400c10700a03d00804a420801001041040a84e121601241c0e01c540e800600c603007841000d51100c85d015000100c848020034401c19503d6848410f640d021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 327572985 1250 327571735 327571753
    0x140f0a03020f0d080d0c020604301211030a090c0f080a172218060b2d0409021b12031303020c101e020606061c0b060d020a020d170601080702 62
    0x17660a031400c642c1e40800680106080004000c00d821307070014400c104e000083d034442d01c001d552210050072200618280142c885019202840f25001003204103403200406469051440c50b0402811410300304562120905030701044c04240700401c2800c50304600c00421900c24281c451117044104002580441401089011007485c040d11080c500381d08084420f01c0558a00143c1022070420410b003682942c4c2490310030011040707003a0585001c00e190710760102042104101040000174182800c07840d0030400702c2d00061320ba99650150003030648a1540703000701d0f040440066150211146180e0a00304240045101c40c9a425100601988240111500f4041d83c4002811821204501c07100040c8242e610705c1c06004d180c0c5400440d824240010940c0b4105480091028003d0b40e8209140048040e00039040840ba0340025001d040058138142d035801a11640078040d52000c40180058400d00d0b0011807402e100e1081c000e44c0541d817000e01e0000d0703140c4000440d8030207006800c1404511901200f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 327574235 1250 327572985 327573007
    0x32f04030212150c1326011a040b042c0f030301091d0c10032c03040306050105031f051305190302012003180a0c140f0a03020f0d08 58
    0x15442c1d03076a0400061244010800107034040c000000c0c0402c1e2001e0060151208101005134010165400804440380c048a40301000e1130300c40820b5059261582001288072032480244000d000c80e007401c0e1018005030744640140000d88821030b4440d403c042200e5210140307000049014501c00e6044420b44c1d9075901d00b5050549181c000fa0041c1e003805550380f007a8012000c1c2e400ca00c3c41034003414000303000500c450300c0002c0c0201c3e48050358041495210340f2109155011440780c2c108520589180300d40700401541e42030f50b60381250108652452400c000426107140c0028070032113640e8912003e0b44d031280304603501e81c050003010308141d10600f0824800300c0003801c10300031000180300280b1513401020030350030000d00751a0f0b90800070702c0b00d01c620b41c00074800d4107c0804880d8031401039094405101000c03a5564036100c49050007414a6070300080c041484084c00d41107280408044880c0960404200100a5070741040d00c002580441321a074000954203200b0301983d041030082100500304654021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 327575485 1250 327574235 327574249
    0x90c0914010e0a030b061e0f090a150303020703060507110d050c0304030206030f0f06060a0203071b03080f030a0f110d09050703020402191715090408070c140907032f040302 76
    0x80740e01011400410582e0704054135944c1000401c11f03410000540c561011070750b81007164232000d0040c001500050040d00046c0c001084403112618651000390352070800030b41b20b01160004981c96030500c008a58202c3c031500d00d05446040d90405003015404800b030a5615500000f20400140014030000000d030f61284041d5110f041103010710401d80c0f40548070384400b04030041440c2c1c42000c041c0302e0051420383c0041559002a44050700780d90154140c8034001c3e00c594185d01c001d0040b1130000d440f03d80284424040d50003600d01c207605100c0c10708513400c0072050304c070013850450200c80f051000d01c00c0c01f0000e17002129510f0048064600c01526038000c2802c2e84c0c440c06030907451044140751190402d6100c0542a01840c900d444035000e401c20621480c0c0c106039404400d0301c51050310000c1018005c94004446615070701043c2451500d0782c03880d048001e03254210040d8400c500003c0020a041d01034058088400e078503840e503d014804442c07001c0d00388140400c041020000c00e01c004001616051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 327576735 1250 327575485 327575489
    0x70f05010516021009030f0509030c0a03050124030206030601030c18060e0f0405040803040f1a090c0f180f07020106030203010f0b03012901081914060109090c0914010e0a 75
    0x16880420140b126401900c0c040c0b404a5204055150200c01c9001c01d40c0003885c64903569051410907920303e11100064684031200969561101d2007180004c01c115055201c0002d4180340c642a0321a4001b150000005412501c4041d4020408100240140d80700e03511110005510f81040149901e034961a4100204c3c540c1200b400300d000e80580428607d000800d00750b04a00c111401d20151038681c2e030364441404081e00003440c0710461090340c4204010038030309248032003001d544c03c1c1003842c10401c01541d46c1141c071940da002d804085000a03c40c104070542c460491445004203040340c030381c070000c0c2c40c0f800b0b8010801d104656840c0e601200599081c050000201103000001c1282c0040104050860704841090175050411a004040ca94810980300c1c19a03070090800084e1a035801e140044505001c060308603401d071411034485901d1600e82c2d1814092030083e40d4044401e52030700030714402c40740c0178220398000c03503042541004004070000c42c141c004c1e00107140c40b1a0410030303000462864407840d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 327577985 1250 327576735 327576751
    0x30302030a092109090c052205030a060b040f09050c13061a0409241202010905120d08010602030a021515150d0b040204061d0a03021c0302240705070f050105 69
    0x10f1140d40d001e041d030005510015201c03484040002001d5840090441c0c4202d00c400c9440d68408480004440080e1000d84002c004c003030203950000059280c500700230f000e850304091043c1d150420441c9a0589442040c0d2050b5000c4014007050800d13004001c070b24507907825000340140c0c4500d40800c0d00141160000400d07203030030307151507250f60a200100d81560032a42c0d00e02800d01007405031782c9804502101002c102d80c034225075402000450300040312843d88a401c804d4001c50366421fa21a076440001c0d6801c070707003403840d60f0304103080c0d0301c51000700d0f01c0384944071181d001071340f00810f590b0004928102c0315030021812903242002c194500c01103083e08298043c6040b0f290b0740460180c540c00b000c1c0c052100401c000700d44c11031400c0d0034400080c01070011100114010000000c4045064603844c00400c091034009003241525841d0411000d140c4400035011001400b4091030b49408290b00c03c2c155090741d620a124510a13903400c10100d401c0e421842060303803000346811b48440070842c01c0c80361a005000b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 327579235 1250 327577985 327578033
    0x20f04111c0b040504020a0e070509040204060c12090311060f120408191412060d0f050706030b0f0d08210f0411100215060f0411030106090506070c03030302030a09 72
    0x30a840c424101d030800c1442d81d004608140803c4010b03130301c524005003654100c508096003621007040845050003192402034000c1c0c8002030100c5c8064110205240301c9204005215008141f51001c4480344a2448014004000e16070480304034603080d0050504400c403000a41d040801141c4d2804c0f1512013620300b511514400070b0f00a003095255080c8a64401c01418000c0103002103503142156031082c0d0301e01521401082d004544607588024100c1a00c603000155040d400c04542450b944640f01d911615010900c0e000c104400c506103184060100e4100601d0705070480300701e444502c401c2d4810030400d8510000b01101c1f400c0a80c14005003800f0303c0d1300651511442c81c00345005010584050900c034418450706d0071810b610340e800201603c0100c0004604841c43d150503002c103a04000d40e5182583c01800d040040300004102005035040390b130310740c4e1070680d107135510410701c12184034451001d0000c1042c0c0d03030180080390181d001541c02c810b000f030002840030300c25102e0184410f481c00c1802080c4a07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 327580485 1250 327579235 327579277
    0x20d0f0f020d0e0d05070b07261f0609090f090b040b0a050a0b030303150a1505180a05010203030a18061103060f0604150c05071a0c070e0403050403020f0411 69
    0x200034490412503c14440080c0011802080058020300506600401c50140f00d0001100f0900c50402207020001c907800c1c2c0707864a4826800030011000c112200301c440140c2c025051100c4404881d01c404690345522024000780c18512040050301c1e500e1954022a0348600041340007600350000c05100314080c01011969041035002113041d120007420300113a860800001146540d40441101c0e0842004243c0c0c0078100c0d003041c045510303000345900c144462002080b0100740c01da00040248074840c48402102c840c4400c5008001e141c278203500850780140c0c01400014801c40299001001001e05044000481c807031550301c45068a4072202060301c15032022060080300c0c1400101044103040c201c0b1a03078241400c0101010386000a503d062040048208041c42406402e0100d40060149080c0a40c4a11610f441d0042030758000c50017802035100d8801c0018052800a0302c00b07025030342c59640d0300c0c039040c9180c08009500e03a1030104141d1081d620070104400300c0600b002048405151084549020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 327581735 1250 327580485 327580507
    0xe0117090c03030319150e0112060f0f090201030e03130303050d0b0a0f061706090a0906020705010f0e0708010903020c012007080d111605010309140a03050417160306020d0f0f02 78
    0x1111001c9400038642c606c80309200510700003501d103040d5030000600304508500ca0415001401c10043d501e000145491160300b0039074580d800c0808064000c0c0c0702402421541044981c1da48162074240607004601e08090000a11420080034040743e00c04004c24490b0306000050030240103540503080400b00e4034020080503400c001c420342902031800305c0c150113140c086c0101d44511802070004408a548841d10f8040000d07a41c16030b2500ca030003038000c00510709ca06094400604a4001400440c46803031000a4622014003420b01e549a05901030210000f1540064030190141c5204190021040914188415082206100400303140c03009180d10340d074404000d0003040000d40c2441040d007203e0304516111400d4910801118000c1c40c0000d1007401d00d00381600c56081500b42c5030950300038413182d002456442000b1f041901c61044168840010002c6580d0740d07030b440b01c029a0ba0034140080100041031550340544a95400d84c40c000c1000d0200712031450840e88101f0007804070b26030228105101c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 327582985 1250 327581735 327581741
    0x507080304180507050a020c0f040f050a020904060b0c19020a0302100906140c03031609030f0b07021006030f0f0201140c1e01050108060408090609060f03160e0117090c03030319 78
    0x200d1309092091a006820300c0003501d468018000b94014180174441c00307030b07549a80e8405e5034004d60445041110341000005040070358880f4a11512580c14810041101c0c5c11010407180d145100c58001c0040c4801c00c034001240703010211060b83d105c3c56100c0d00001503110802909410240c80d5100c6414504000d0082d2005041100399003900e08240809054014000100ea030400d44071401c4880c80c80c803041046400d264183c000402048001c5c14000c03c002070341c080c00c2d026424940968440100603100002154003d21020f01580900341c070100c040342c00010a05407090040c5040d00e4004220345c0c200000f0760001c18400215031012544403035141c5100da0200d440c100b8000240b20b00d51400c2c0c1600c0e83c450001d80041e0162800180104060382c56500f120702d4103c0c0601102c1d21240d803e2003101c000d0308126002c40e0250846417200d11014400c4000c444100e4050b11050401c500341e00400081030001050320807a8070802d40c1d10720f0070780d0301040918803440c901c07003070302091901c8002c0600139 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 327584235 1250 327582985 327582991
    0x50d080c1903020c0c0d050d02070b1c02030415150315090b0f0a1e02070201080a09051b04090b01030b040c0e0105011d010507240b0105030f0601030905070803041805 73
    0x12403182448a44044680640540c40950441c900540c0b43e58a40d9201d60800c40a00e01e072581c01000307000c0d104100f04010851002c0020540c081d40c01407665962100c2c00e500c180038101c2584010168110b41d004010303801386400900070207101c00384a14000701d01c402c598101e403080d1580d00069004204012404410100d100b464010511840e1b01e07607500e0008110014183c240034804410002d04a0000e0303600031194403000380b6140f00030030f00600e4041c5c0254480b80c0d0030790000e181c0500152208250340283c0320f0b159404030003040504020b541d9507003856200c0307410503402511182c2d014041560310250074041c60140c4401c00e03442c101031400d141c4903080baa018110a001d080010402c580c0c01c5458078000561000d44809040c4c0094012281403207400c07070052614030098851034105103881c245c80d00400041e00c0400c40d51804100544840c0412240c5a140c107032100c0025881d54407a402c0807000c0c911070021101c101e0784911045041d5006a0001040300054900f200a158424040c1c2030f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 327585485 1250 327584235 327584251
    0x2120c0414032b050c10020a110a020f0118080303040c051f0815060415020105071d06030402040e01060302030316150e0a0303051009020705071d010501170703090609050d08 76
    0x820021001d09000403802403450f103100841412045004841c003400450382c081c4401e0040d51160081c92041400035000540740100045201001b00c0c1038020005142c035409400074008032500040b600112040c101400c06d5a2140c003400000051104081019501030b40c4145009600d4034200b00901c0407083c024501c031f07108101c5e00480149400e0300100c0154003c4510b40c0c0d030081d215040400304a151007903070701000b10780d958a44218001641940540d0182c1c0d255500c481401c03101034442208901c10545c142d5100e40d0803c08600140340c25800817114641800011421650b250002400d6400801541030611000e00c5001c04002c60142c0031581d01300032000400c5200101025140d0b01d90000b84000d060541d940d0105103500710b1200741e48014840000e0655443c0500c0c03504a40b108020f200d110030308500210782c00c1d101045005103505035001030b91540c64a07110f800c0b01c1c4250500c003415a006055071840404003040c9603000e0800d10030b0003000103006045c0f080388010074400d40140011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 327586735 1250 327585485 327585493
    0xf05150613050402010c081909060311090121021614030301060509060d090c08030a1205010e06150405092401092303070b0d060e180304060507030302120c041403 71
    0x8103a6518940000401048007000407180d07140d2006807030a400d10f030009800c400b00410410684955030b40e04100100c00ca0f510b0208280c1c0d16070b4103500340c5e01c0d075140108940c3d105000d0780740c00b035118218620b0040740070192030042008a0100500f00da10a00448030440002241c00c2d00b0b110000e8080341204410070011403540d0b1506400500d0303405120740c494031500f40081c80c015924141d40240303a030b07990001c4e82c4a02095407100015030701c1d440020103501240480060403064001846454100c3c1d140c03804600171070307641100b0000601c0f820b5898091005080c0b0021a441c1c44140419100304c0c8060343d00003146144079950804100c0c240c1c0c1e23140c104400a80c051000c00c40000518000c078240c07864521805425000007410031440d40c110190b1070201103403565217818660484000c5a50405141080d9101c0c1d003a461001d00303c4201d400f101c0e6104000c00c0154520500040130306900a16005041000e00501d4007601c00c0e054500143c00b00020406101041c1d00139124240c04030214010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 327587985 1250 327586735 327586741
    0x50409050316111e0f060306120f010f0b04061508090307140d0e04150e10180504020f010801080d18051c02120c010e100302121602160e0f06060f070f0515 68
    0x181c0003040f0b100094003406c00030021500c0c549500c25800c101d034040800b512102240c0101e414000c0c6084504400c4080c101812401607051510819055601c0003042e0070038424110310684d043d00000d041c03864035110800c0f1030400302e080c49098255040104014000203564401d008040600000d1060712841c41c10b00450b101c0c0400490090132038005d14225401540d0b41c64002884180c140c0c00030f560602804a603850031101903121902c0f891003101e5400300c40c98040c004407020b072400d008903407640d03011001d901d903d640107601c112418044043c0c154111a182d8002c0792802030414168451280d41100c96421440c0c900c0c61040640300c07020082c4411117022000a080801c1c4800240c000d82060ad10350194500c00d4040360481100042c0031245420449460440f684248845a0050159049000c0d202140304001821220034006550050b160b002800149100283c880355006104100c070000036055400940300389030041c05c80e00c0ca0304243d41441420301c0341c103442c41010360b152a410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 327589235 1250 327587985 327587989
    0x15040e010e01060504140d0201051e0403060f06030c1202032d010e160311060c120c070801060b0703081008061008061303021c0513030602180301050c04050409050316111e 75
    0x486540f0b14000c1f15414015071103400180c0700e40c03003440c600c0c10440d0268101e101c003040c402002482107131f1240104003c0c0c003100c8400030044618a0000901070021840204000030701c0c02d40068019000505840b90f116540880244110048041000752017140d1030300200d0120a204440e021042980a0f041908072401c070100c1c00300300e0b404010302c0101c070030f0120000358031010190b4650303522000450f00b940500c4481d80c3c0e403a401515801001e8400e642c00803c5960f4103010380320860b81080d45890401e00ca56505072800034000741114a00f0055200c0040d2204003004003a001c0e210f02c0300325521190500025508006000b0280c00d80c1c00015811a0000fa5001521010040074480460502d100c042c2c0210341034420304a44841200a086001c400c0c06041d80c01001c0168401c040b90141000100600d4243e510480e04088281010312081006081503044580c3d4103104600f075914100020030104400074100c10f0503100c1210781e2100c0c03680c5045c12400c203c030030f01c2c070030444c0c0000d0008500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 327590485 1250 327589235 327589259
    0xa03030f120f020a0c0c0b0403150b0409020307090b01020d0309020913140303160306080a15020327010b0301060503060c0a050a090902071b060512060d0215040e010e01060504 77
    0x219108014905400400700c01c034542c0800c1110104190a55440c0707043e160040c000c145058041c0e84a01095100142042552003220100e07903115140802c4c1866010f49980140f0303901c4100e98100d41c940740d0100041c1ea060100c1406400e84010000e01280c2c1d40000900c0c0404114886050500d00416500540d5039141e020f80c1c003404803c941d10780b0404030300d070200b42d032580c2a05161080c8004024002408072044a4110701ca0003a941045150b0340c030101243ea40200380c00250030a42c107000301888818541c0c0095500076030324031511070800c50b040403a0103018108100c07203405956407503c5032417a2070280544030007030104074000c01841c2440d2640c0f0842e842a130259805011000440d07024150080e1104001049442c404649075035803030824409030503240782d02c21081e003480321002c0f0750903010710309880d807041034402100c280e59101824444d10000503182a0b03840103a45940b00c11411202d4010000350403443c00002440d450100c04540c242c00603003001c420b20001340000e20400700c80003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 327591735 1250 327590485 327590507
    0xa060611011e050901180c03020315160c0503090d060204050405010b0910031a06070b040515070203040306022217150f040b060f04150f140f01050a03180b06010e0a0303 74
    0x80000100b5440c0d150600f1700401006c011280b1524030003441c202407007450000302d01140e0081d01a50503240202815450302001102d1500046074030580700501144945c0000751658481c4046903c1c0a0000c0c00050a0b50005001100c109130001024815401c040c01010300501030418180d091440100001385988d040b0034000017003650b00c0c03507011084100340310b44840845001d40250341c0ca00f11820228121a0126416209881280040e190000c0030046041c841d0110b54040d41c20242141e403a000030313501520042100302d100c00c43c4400a10600c0c041071009000c0302c00e828a03400a1034025506160f2140004540c1c15115400c0200000c81e06640a42c42a0300051a000c0350b52254002105016065070340c030713001032901300d1413201e1080d4000100306035030426102001c072540c2d4640418403504100e5206410a2801150705420750040015009000c15800c02080e540d11825045100c1400303044291070b100400350500c2440c1d608458010507115099580c4502c06065440240541c0074607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 327592985 1250 327591735 327591791
    0x303090d030f020c0622020901030f060c08040c0504022b02130e060105090f12010905030a0e0d0c0e09100c020709060e0f010605030901110c06060a0b070c060507021201050a06061101 80
    0x25009039001b6502402c85404e03902da004200c8032065850f401e0640d00400880d40c1102c1c52032400210003412401100c0e2030b4411a4481030000f42d4a003014140000394212031034620b0b100302034541e4616603036034129524142c07200c0102c0050700c801d01240c1d450441130203540000706007103070038080c4001070b41e01c24211064044181c031000c0c0d681e4080c07004600c8504030907510312000d51030020504208107000c0010075490380c2c2a44d075100c006103e1003c21003011390300d020043c034507035aa420420001303090707010556206114070b0550301001e1a0360000826a00183e0440700140c21100342407002804510480b00502400d080c048180d01d40701c07110200c00001070060501384500480050314500c803d400c01c028040c80f07640c001e40ca5100c540c3c003040c1c4d11182070f034015100b1078010002090f26114502502e1029412003c03088032031745481e03802c0d43d01e41c0c031003102079800850050400345488824064540180c208400000e05da81c5400c134010070071102d01d00032800380e034103004124401c00d0105224070110754074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 327594235 1250 327592985 327593011
    0x40f1d0c0a090b1303080d050105030f010b01020a0f03020f070f081504050a030e19090b090c090901031410020a02060601030f1a04020d1503030f030f06150807110303090d030f020c06 80
    0x207400b0300d80c4840c0d89940c0014040b04001581d00c0c0c268447d41c0243d41200c00503030440c2d040c01540c010050a8500614081d401a4070100c0c1d0000401c0700322850800040c0a4010369104e400c1d1410100e0030610180c012034a02c08415100700018232040000f8498540941c11103882400d041c0c0c1c62a840b12103030030001d41000070040c08240f20f6900c01c0780b01104c802c442c6203c81c3c041642c44503624041c0000301c10451041b1100130018080e000208121040080001c299107901ea00710f40e213034000440c0340604403000303210b607020300820400e2a2004200c0c0032aa90000c04541c9019000101629811000307031000f903050030114900c1d011660401283e1b2070040702c0c00741e11004080d07030030300041c0b898078010031540160400020500d90440b0444041d4031070740e6018003004000d00020010f5500900c03601c40351050042c101c89030079200c0c1100303d41121051400c00c0300000c1034400031340b964000b55030304015608040407030300c00d088d098032a44200860342881981007a8185058a0b104c48008007920100c2c44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 327595485 1250 327594235 327594247
    0x5030d08010302100905040c0c0614040305040302270a0506120a02010801060509031f06030521071103010209040608010c0e0102120a08130b070c3e06040f1d0c0a090b 73
    0x80105c410801521004d8020031440e884000000d009503528802070303648a25250708010550406428140700356003640300d03d40703058510386c24005443c0c0d1440e00a00c03001050303840c1e42d0044002040c958000e8110740008100d500342001004007841486c00f2100d0550300204240c00140d80010341c040c1141d109080103034407400c964010904000e412140d184880d0300001c91040524030039030041c42924011001c540081c0c0c1003280504803c1000c000d0012021720034020080000d082060b51030203d00003800241c10715803000045001d44100e0707048045165121041030550a900c5040003034144402d100500c0d000c1c5155643c01c480d4490b110b104010002801c000564800c0c54002a88105500c8029200d1714540510010040200100111860049610102301c03000800f0303a0075407000d2100b4140c1903002200910850101d985555007900034a003444009082403002441c0390040c03002a02c0180c50882e02417140a110f41c0081003411190b009201d511001548804140e0550b07000d0700050340c2e1a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 327596735 1250 327595485 327595487
    0xd11070b180a0507120512030c0715020714010c080601140315121615050a050a03050709170c0f0102010203010f0e0604060312030b040606020705030a031b0f030c0c05030d0801030210 80
    0x442800000342c220f204080313000520001c1040203a80b40340c01075050702d440c04003443c1703800d00b10300c03050340d18281603c4140001800301e01c01840341521039024160062030480d0983d00c0c84034540c0b040d0949011785e50b64508990155410901d00e90340148240307040b00400551104400c2140405000e0703000404180d8015103054461505200a1000a4040300c00c030030085074180f15481c0140c016407210504400c8220507050084081c0c034442806511410705240401c030342203008200061036401040303c61040080c260305802c9281039400b8601000d080c08a10803024801c145a04074203403230443e03104100401101c0702c115185401d0320208007070101c01d03843c0ea40c00500506200d40010780356008128280d800e1b950140c0c84890892001d403024405180c1d50300050f40c84895034458030360590400c000200000c2e100d40702c40d0121100c103200c0001d01c01d601c0c4d241d4051022202504502007000340395450140b05c015410000104004c40c002c0c50307440c082d403000900c500c5040c48001d001d19000b10041c1105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 327597985 1250 327596735 327596743
    0x1103032a070f0803040309060905060406030506130213060813080304120215150f0409050c0d0f050d051e030402100f030906091b060302130b0a05041a0d11070b18 71
    0x9207820202d0300001000c50308000056074000c1c0c1e01140030030106480003c1e41c500981c0c0c043d013183c0b802400c150a0502c0c1801c01c2c0d0113000300829556010041c0045046910102d201401030032090150a1002c0c2d030410b1405003c44101500c01e450079896000202c00240c0c5030000c69a01c190b102c090f06428086038001a864040c084140d00302c1c40071804104151580c07030440765140c0120440b04080f5201d019800c3c00226450b500b4054201d80281c580500c032420680510300d0946c0c402d817038090a910007a15034908000c51000400005030001a0b04a406c10801c4a030006880c800b081051171400c2a038000381c41a03510929100510024040070300b0980c1c02640400031460b00031209100031030051030003100b451002178810f840400603540c003142d054031a1007070b50a021101c45400a0071818181c0403421904080c040c1c400704a810800403503c0d00240f200d440f030491901c40110344484031003640d402902c540c1c00d5100700800c0d0620124000c20040d1a1041d00800000b40c0c116040d00f07055081828 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 327599235 1250 327597985 327597997
    0x100b0109031410050a02031501110a020307090e06010503070609180212090106090c050406091809050f01020a1704150b150f0304020907020625022109011103032a 71
    0x2c5503400c000c01c82d406032804603602940a081803010041e990343e980e0648101c0c002950a245000c0d800340016145500030100182c04d01d296504888183c034080c0c0c0000d1900c00c2c3e5420110a031500c5003210501c80004200365800f50000b2009048488c0c1803100003000001207100e02a501e0345210307603150685049904132150360b108503070011142d1500e003840a01818a52194000141c5012041540c40b0303c100140c4055600702c1c0c1d10f034101e081c54400045050708085098110a940d58041000015400c10009034241c00210001d0384440440e440584001e004405102160b140c030342c200b04c00900300c1050701c0268840d102d40000c05826500200710075000c0e02080740300310100001c00c84c00384008003015601c03540c0300720783da070b1410b961f11766040361981000d485402e03820020030040291007901003d90098201d180c411241c0111603600e51201e024070605201d200040000303a450f12075640404241c5418004600551540c1803291a02401442d00c11103040b40f0402620101e01c0c0d294030b0022104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 327600485 1250 327599235 327599243
    0x30a021606020f181e01030e030f12040317070e09100506030a090c050609060403120e04060e0108060f0c160303090602121006030608030315030a023f100b010903 71
    0x1403036000a00f0b82c0e5202d0382c42002c02d04204068000707407541138a00f14003e28407400341125403210035204e031030040d005888281e00042240c0018030202860324059405002510b1480c0030f507000b6800c003424041c1c11501401d00f07000300307103019204103d52389410400c2951001e9041e180d041c0c85503207800c0040101141604200e0f444907000040c4046968107401c143c103214000c140d580e222a80e6041084180c0c85111509034102d82c0500003000415a40c4044680342d0340d01c1e003040e03c03104030346034000b40803551590401c1e99244900c0c40107001d808001c004c80c90780b000d014800c1001034202071280100501410a0300c01d0304515145114041511070f812940f8a240c1c0890f041d502c4203000d9500c810859000c44290600645050340040c00620900030082110621005140345807612000c0022070b00f4111350080d0581b003003c5007072005031148202c11394000c100d10f100082405240d901c60b1000e4181413180c140084254000006a86000c40c51502c400451076002803142603440043c2c0d0052500e0340301074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 327601735 1250 327600485 327600487
    0x3020a031d03010e030405151914120a021213201908070302120a0809010e0f0d05010b030c010905010806040e1e010e0111070b2a18091308030a02160602 67
    0x5906504c0000190080d070308100d811050000c02030307070f003900240a0f050540c0d0712500d242c04182107003800740d600018444c80c83c1d14007900d45144203504002400042c0c401d01c1e00d240d4001335421114600000e107540020038410742d405520410b4440201c0320100c41400d403588134a4517075094060744c0b41d030020100300c4030740c07888421200d9840c04007a072908258842603005000c0724002c89482ca030013142d22040203602c00d80c0746051041c1c80d40111810915030703035050381003540c04101801c1076540f00d03140000036125070700200340310f0600b406042c1410522a1928180086104148131681e0006082940088207a5000900d40c011202c0589080e5110640101807181c030007201d0a041d10641100185655260007401000c2490002d400e01d03214021003e455502d6603004103000c25219800d11041c2c82c00c140a8008007482e4920b4400303140e104800355040c5448080c1074075101d00740740000c6540a41501c20200c030200c5140c55030388092000400e0080d51913030001d242d0341248a82ea441000d0a078002e5411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 327602985 1250 327601735 327601751
    0xa0b0a0f090507080c010f05030a050c070b010909030306090506180a090b1f06080c0a050901110303010b070c08061326070b0a0b0a0609090b06070f210c03020a031d0301 74
    0x5a8442ca1a40139120b550302406000d100254041d80a10f800e03451140d8505107141e0b2400034803001440b0240042c00071080420807813020030080e03150b0034040c1030f282d10006602e801c00d26018046501e10382c0002d000c5420840ac0007071503650020b50540ca50300921201d4050b0f500c01d0100b1004094441004100340c0300481030004641d030b56400355500203c550704401409469140503140e8290441c0e034081000020460710504501c6034001e81180c040605011484098110f030960464000760000c00200001103400818000c42002080062003844083c000324200002d5080e440820a0300242c00404481800710001d5180b884ca00b1468460a0840303880715210f18002c41c000500307840c2c030100d00c2d08100c00032520303103001c42840c0300721b5041e91500c0451516210404028000c0e0040f003da000354241b0903003001c1f80400c404c9104280c442d91244803965050800b92180d0114039602c0010061041b0060b40000d0300018944c4140c1d0f01403c00802c45000603100c0745d40610030300e8080360554208501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 327604235 1250 327602985 327602993
    0x5100609181d1f0212010b0f120f060a0e09070501081306061d0a0c080601110102040b18040c020d0804152706180804030605060301061706010e070503090a0b0a0f09 72
    0xc45550045503525884071403480011002c10f0740280d01310b217124507084600410a2080ca480107105900c40c04058a007048880340710791031f490500300d82101c2190813190800001d460101c4900700500206d0001d00414100303402c40d81d546460030f0054506002002001c10642e01015803d40358043c0d0181d014804d880c0c4501c2d010880d210001e06401d500e01010021800444190103440c00b40312241c1c1c3c60902594a800c01110940701141505805560030031000c94525895001000100c5240307400e298010b14500500c0200c1e61200180421504106c40301c003201c907400340002d904103411948030801c0703001c9541c190000b040c40024030344103a07003040e481007229950a420300f12180d00500007080400d2142c501915a070313410082c02484034100700000d00000780564011a0402c0010f000000d8070340e00c400119140d0440000c045059a1000004100050445841640c0269246401400d605101002030380c1c0c0d10070345038000d01c141041800603960021a6001d49020f501d046ca003030007030803c5814 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 327605485 1250 327604235 327604243
    0x100912030c020a05100806040c180e01030210030605090c071703010e0a11090112021b06010608100819080702010e06040f0317030c070b0c0702060301150305100609181d 74
    0x607040703000e0b4600300000652440d05064000d014141c544403080c055030760101700001020740e007814005109545d0703110b040710280441d01d1000742c0b500440d175a02c1c65040d8010013503504044a034840c20903003812400c0c0a01e4944515003500581c250b99820b46648035441e11207900011703182c0c1000d551001100010712100c500c01018010001705108000d01441014020310902c188081140441c80300c1820380035514a079030090902403905001d119246641e0400b6500300002a407040c400074080400b40b00190141000ca50004c200c42c90040184045202e101040490600809002c00c00b01080500640e40182c4452640b2480103000341c0d034445d10341c451070b400054035002c1512030103160005a801c0c80040000c4034010700240e0011421f10b03030356645416910400804940039000d0a000c0c1c500141c942d20007460192103110014a816502414010105c0348010700d901c10b12080902d041001503000100041555036455041c1d9950311403030a000c000d050a21104580c0041c10004000112400b203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 327606735 1250 327605485 327605507
    0x6080703021e1b07150e040f0c21060e0a02030c0c0d090602010f050402130509030409020d0606030c0e150a260108012d18020301090c030b0115050910091203 69
    0xc040c1e40b1603040d43c07805566078070700c9000d5844415008a000702d00079001e1042d901c00d428004101040301d084041d0310009552000095402040c0c0d8038841c10818030581c8840081030035040ea0030401b680c070300704035001c0082e8051300380100e055001020905c0481d40d48221024403203050100d030303415500708000031b005081e6031145400651805900101041c0c0b00d000b0b090089070014a000c1080200707400030001024080c0015085100c10000001c00f52498005031985010111000070070620300380003d000d030b4086030034450411164480c040d032296151000c1e0002544106e4002e0740f82e00c2e0582041e58042c09144081c5000700d6007108108095025480d80c9051f40d40000090003960408102d0461044100c0100c401d62141d0040044030319440f5800b4410700000740c40c0a030220007103600030a08641101c0400e46140c841c0c68001c2c81403110300e01d44240100404c2400404600140c41c0003003280c02100300342c0d84a0052250b104030003c0c4140551009409108020a1552410f20340074040308605 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 327607985 1250 327606735 327606757
    0x50f0702210607170402280603050a1a01052205060403060509070801020705070b07060603080f07020f03030a051b0307020603091b030a0c1203030e10060806090303090706080703021e 80
    0x35000961803500c5900740c107a00e4200d410551301ea5031070b59400c1285080c41d207412980010305102e207c3c0700d2441c20728103a8000b46a507440000d1581848461300d82985d003d2070905403c1480814194600d0740e0000440702902310510788040c9000505440b4814200f031584aa42d1010005c0b07000b005009086d40618001d00b40041114140d0fa5101d0b041820b030b01070002d02a2040c1c0004070300300601c0304100001c0807120702c1001c0015926840341d88555440d00040500176802e00045840310450500091419001c0c40440c0110700785565540000c00c28403402e04205100d001c1003e40f200c21031010002d50304100c1d0f000303100d03c0e20780c90044c404981d901074a90b94a42c07041818030007900641804a02400c1081d008100303030141c0f60400c07610301d8208200d04012002c16580310340c59850040240b008000075041c0040c0400c100d4034200d41c03203141100c06001c070b05090300100b05011404d80001403400c111403180c02c16039921f07980c01105400902451003c0780007036418a641800b2740000e0030060880d1080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 327609235 1250 327607985 327607993
    0x70212060c0c10090f03051305030a060207050d0903200109030b250503040201090614130303020c03070b09060306090603120403120801080a051b030309151218030703050f070221 78
    0x9005801c10f444c0e20490150100a04111080200744600000e000e9035845c13260700c0d00c1855448000c64503086940d4000d07145c1940c045080380c2002828402c01d81d5609443c036007480c0352401c58135500e5038903889171008480c0032549420301c82540d008420b01002180c208aa1800503d842c2c0a21507150390f40e801001450603603801c1c0d500b166400380040d01c4c021501a542d03052120f003083c800340c4566030680381c010440d590038000c2009030021000201d0195203e5405006010300350003d0600e03000c0035401c02c15101c0c0c0c0500401000d5100c400036282d009504a0b080003e41d115840840d00300400c4600801ca40c640006021003840500b0444409543c05039a600860380c3e61036032515112440060010050b4000601071030b090b440c011142d0f4400c80004007500d01e0880e001000414600c1c0b102e581c11420781e0040350007125901c81c00300042d800700300411005500034030798014a480e88035951005050110101740d9040d03610a0100b0ba50f0781550180c0942003071003600740400181c0302c001401c0321003842 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 327610485 1250 327609235 327609253
    0x1030b15070b010515123d05040e0a061a060c010c080a05070f030c091e05130c020303010603090f0c0b070b06040c020a0f05010222080d0c1106070212060c0c 69
    0x74142460b04002c040d0f0017026042055a41500e042080b010340328001d440020f9080705507107410305140c49802080e141950000000354004041e650039070781e00c00b0344580d1400c8034195480d000454840b542682c40300000030000903100c0c5905044010240e00f54001c0000702c0d0744042d0b0141540892024a0a80c81d415a20794606d820542a03401c101c03030010000c0c860301050b8400c140240c0044903a00c481b4103161190640744c580c00d251f180d00205506070756411160082065081c4150a0341034100529420302285000800195803440188211404c0503900d05840b810f00c240d1031480c81c40240d0040c01151101d50f111001c0011380c220300130594804292802150310b500d818450b0b00b0719405950080d200100c440c1c1c03a5030f00c1101c203101c0b080d1000d54080060f01c0082e5001c014141c481d040700d02121920904000c00d81c5e15100c0303c40e0501c03042c84000b40003003000c034580c00c1e06001c003004101c481c00d070384280c0e074404102008640d00681d0355502c1024148400380340300201070120b407010002203c00c400e07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 327611735 1250 327610485 327610489
    0x304120515011208090a03120509090108030a0906050307120603030c05010b010e150901050c0607030507020d0801080312130507081b0307050d020103180f0b0105040e0d120b01030b15070b0105 84
    0x144080c440d45110311141d0f000e550000f1190000780c1142c80004200d00b452658a480340150b0640c1c3ca82c0c02c0e00011340007d1400303c103240407030006001d8040702c0029410200c85d01c074041c100c521240a003205001c000f10014800c64468404184ad40100c0c8009007c65aa40d280117080604003640032580765092224084195100e80e941c1409144010b010400105170701e801c0d0302c8698400801d460402234204070b0343c0a41d4104022840c010380d11030742d00050b640717401c51000342054034103030948007003080110040052000000950754007003003001c102e80d12a01c58000b40200c045503000010300c03500600303400140501c40420038503200c4d01c0300300c45c91048202d994101900c81f8141d014041d800510000d5280241d4400d40c8950301d03c1d0000300340b000c18103485888080b10060842030484841c00468018059410140100c01d40d14500b80300420b000c110000018000c00103a6030b28460180e079070001d00820360f02c2900103070303030705030000e0f180d00441751901e040700e41140c2c07210409461030301c84000000350303034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 327612985 1250 327611735 327611773
    0x20c070f0518181c0f1107061b0605040f0b061512061309060c02060106090b0d05040f051009030f110a1403211503070302060403031b08030c090f030c030c0103150803041205 76
    0x4a0071b41c40241c0f82c6182013240c1134a0000035011130b0040c00072211b030340f80001074840c40341c03078000c50041a07005c6116130030349420300d400b15000b00020b01401100d041503d0a800900541e02440b4900301851402ea80b1a4041541061403996444413181001c0345181441096070040b4604441c50782614020b82e210306098610341028400c0350140fa0040041078010041680410381092007a20700244100454075840e25004801500c02c401350364441c0045c0805400074201c003404049410038024042c1e82c21b0140340c4070344204a0240405180318540d08968805104848840140d0000040f0004541c00e14903074214044400440c5840d20a40c0e00c2c942c0d18000a0500807a607000f4000c074645821a9000c883c01000c150307164202200410850000400d54000786100380c5005030425121101d41c0e007008920860f4a000368040d8104281584480d2400301340041050800e080c04118184c1204190004001d154001d40c6180808a408075030360074000c28400c5001e004404694400d04800020542 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 327614235 1250 327612985 327613007
    0x1205041b0f0b18060408030c15060f1c032106050f06030c0a0f051306030b0414010b040b0c0f190209070201020c06010302100302120703020c070f0518181c0f 69
    0x100d00240000c020800f4a10100b44055002401e030605150383d03221a1442c582028000342180d80124940c2d00142c0003c0c0c05055000200310380b20303601059030f8400300d401d01000c9034101d54041612000c43c014140102c0b2075503e00804241190854413009466000a02c0c050042034030401091044101c1494020203881c06a108440c40c146004890107081d00d40c0701d28010114188031003445800745200d990481500240302c66140414400d40590410040f6021410300260090340c15005201c0a05c001c01590165840c1560342c9a503010250045843c026800074907544030b1094508400d4810003070701401000c10706c02d8404540c1c40e01c1c1d014040e401c4c0d0040c072006600c81c0d400780c00100050300e07102c400c035400b400281c14018600040a000c040060130112081c50100f600021074054255042028800a015901600e0b81140c2080000b07410004141003502d00b005141c0c000c0350000307110300624400f5403d0307201110690041001a14581e80c5840b0f0341c040882d41d4a1203400e9294010284801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 327615485 1250 327614235 327614249
    0xe150301060c030c06020f0d110c100507030603020405090c090702030c15060103060905090a030e0a030809090c0c100b0f220507090801020c0309031002090d060c1205041b0f 76
    0x2095a00308102191019038241c0e090f4200070201041102081c0c0a20040c003000007248151980c541c1c8951a000c180c50380c100d00303c07010307441c2040038000f207440205051800760703841e0703002060549840c6000c0780608040d810181d4800d1500d42400050360340020741090341e48080e0381209241c0d4640c1401da0f20b03030090018500703040d00100700c120182c2c5c0300500c5440c0d105605060005445864600344012103804807084842e0307500c103610b580240f50304102030600110040310441c41003421079848010500401585034010000c260101701c100300c540c025100c003131100b4000c9812003040c00b0010000b900700070802d140902e0f903134400c0c0485414039481c16401d40ca503402c008034a4442c8401c01c0d000401c4010002401c0104004010485141c2800200310544400300215290f0807040c04140c20003601b43c148550751441000340003419111070f1b50032046560000800640414801c0050301e400d003895901c0100603143c03108010400c44c05401aa640d03003442e03c00460f1040d00c4556001800129000e060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 327616735 1250 327615485 327615487
    0x1002040b04122102060906090d0f141b070306050c0423040b1c210e100905091e091f0b150f1b1b04050705070b04050304060e15 56
    0x100072514808030300c1401a22444444100038158490441c0440f01c69640d0310041c4c1100c014130400c04010051140c000034400c000d4410304503209009010090003260764000d2101076403000181010b06800d6030200600070820b080541d05a01d0b0407a107e40150104459091034400411350301141d0009440a4810200450b00d0201200c004e2000038480c8071000e59000307488400d00c1d00503440b03180e0321411081100041ca001100b6034501201c0c052081148141038805000c3c2e201d407107980c4034132110300c00c0d00c0558580041030a01030b0115521a81c0360841070b0440b01a8090080c0c0301e100d6240e1622902042ca00020300361609007155848407684910900000d04013480007500790b03000c2c1d00038101e4501c01088041001100a00f620f81c60704031481103800c0b00b0002c900035180c15001480009091960809000c60f440d41c80050448020031444440c026683d510000c1d4201e80114100c03161250400c980d06841d2038280b42682d52a4020302901d40000c1c0c000c051000142000e070718108064003114566 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 327617985 1250 327616735 327616739
    0x412030311070c0902030a0c030509120a021203010612230703111e0a0305072a110607060b04061d0a05070318050723091f23031002040b04 61
    0x4501401102440c5540807604000c008000b4030600d2400c001030001d60300268592506175807010407107411180780800d05003000100041e030000031038242d0506036031400464aa161010080b841c0c20001840e28581400001c00443c0b00d40d004a0080d89622100b807042c404220ba031541c00c800c0344000203010300400c0040b4041190030340281c0204240e003851032149428000c1891910030690108120303040325040024060201130313458054146c1c04030031414840122221107181071000002c00b108909001460360881b401c12041c4c0c1c1404484000050516841b000707181001c81c000c0070042d40440c880c514203c0001041280030b40350303880c4c120180004000b50360700c0101060240100910080c00c0640c0c403d4243c02e0710302c000c500d540da200d004100412105003011003414443c054044a0384007010b02e81e10901066580700700d4998406401e59901019988050400c00316841981204040000503001480d41110000400c4c0c5400411003c4404405000c100c4c082280704602580036035040400c41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 327619235 1250 327617985 327617987
    0x3060e070b0403030e130f1401030b0a051312050d05010b0d1d07060c0809090f011d1510030e06160306050a050102150c130f081b012307080403050304150302041203 72
    0x524990121014000c1100940c7e0303280c58003213450140701c5841d403074030b000010b200703010305a04550307402141603400700010b050541f00d501c034403095000c00609554101c006807511038031450a80d5045c8602c03100c28041561a0325043d5213503000b00e540005060b14103040c0389281c0c00290000795518080c407021304031003030400030115000301d441e200035141c20074104120140c41e02c4888030184036203d844010150765042120001d000e120030200c0c0715590704010140020520029060121a442100c014404111a14081e00905040102c90a860040c4810014825800f045e05540d040e07156034100940c580b1042048121a224000c460040e40505080360b807920180303401e0303500500120b804904142d0074807008149c80e42d05420081242070905400c00c203d40c6c0c204441002030448030a01e03520011121700092010070301d02d105812018119030540200b5046008580c01c41c0e4001d140140d56507103134241036540c5e43c03040c400c4001d0800e06201d010440b612a00c281d4040e034105190b43c2c0d0340b080203030f20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 327620485 1250 327619235 327619249
    0x90606091f050a11010b10030504050c040615030b0307030f0308220f0c120b060f011115040c0503060f0703050c09040c02070510090803090d06140103060e070b0403030e 74
    0x821034100c50300c0103550010018101c280e080442250b60307030582e501982d10005100e0103140e105600c10340e05160445045640d00210710764608807510f400191507031a42042850b003000544540e81181c9403250120300b9165000490001407850744003804140c200300140b40e0f490301144000790a91030071103610f00010b48a0300f44e4030303006001d200b034110182d00420b105a440c01c011040c11141c1e0760040c2c80e074000b00095030451030020542240043e03c07100268031203a101c1d041c010205403040000001c0814035a004010b4140c01203038940845641400c046c00402e580d1000303a03010f40f21858220030002ea50f02e8009880f900c81c112407001c031540c984071090260050b00000e0a2104076420034801c0c0d10700d42d11648a00c03550801141d00908489160a052052500307003820302104015990a042c010850300204a0346c6812050b44c04050174015820700c0c0000f49821380784c00003098008000001403203040d800ca00080840700c81034030b1585603100101c1341c40344a01d11008012426071040d07244e051500c0b42d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 327621735 1250 327620485 327620497
    0x7020306130f0c060c02041b0203030a0c03060803040b0301090f020901050d0209040902090c030f0705030c090f030309040e0703150b0a050f01110609010c09050a0b03010308210103060b030f0606090606 88
    0x4004000540b556441c0e00028036290088000982c0100307075001945024015040d00d800d004040450020310041c00079140d201c0141070106140e11400201101d034031a500c92401807030340c44140c0b85c80300d0f2191064400e544c400e1060340b2151342000058040e10740745101b1a6004401615950b103486000c0d402180603410400400e81d2041d61014184056244e9141503407055001416495803843d203200c6500c03800d07002615500812000b4810801c01442210803074903809002c540d022650304510000030304e5845034015071504103040040489841100183c04010340b44079210b0f20441d05c800c2002c9004603654107000c20781c0076245060403c260300306925026a002018584400d801c46220340c95031a0070401e840303141450399918042c007103155121600c0d5010300411144070035428074003c19902c2a01040c0000b44c1040c10016500c400c452a0443c1080c5ca40e80d80303202c000c00396039613081840080c0b40d480001c40c068001c00c40005005200030900078403903200105042d21540301c8601303212240d0405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 327622985 1250 327621735 327621743
    0x10e01063605010b0304031e051b0106090608010b18070e0609030a02221409031e0c0a030210061409010b0901021014070927020a031b080103170702030613 68
    0x1011841d807a4548034012a4041c0203501e52035a628202842d0044c038400c031000d48101c009050845240d0400e81c003004a66018502030044004a01c88000f41e6004020a0380141e640030f2510900007009901900310f440b584208444110003440c0000ad4400f59142c12a01400040d0310000c0101061030079501818070800090102e40095129078042026502d0030841102226004100003031074a0b01400b0705c240b000000000b481c0b003410304201c0320b50760b4016102600c0548030101c4404000c0400b40040c0c1c1c00a2800e40110307240c410540c00d02a4031902c2c2580240707111780c10310602042c801041001c030880114041c00215580c0c0c0f9258903641c094000840c0c131070441c06000c41914401d2024015103040503004802d6104606003100301501c403105984c0030315080405c0301551200c1e540340c081d07540210320345002c0250381c3d0f000c1004210300a00c18684420782c0c495820201545075039004a071641600d2154091a440d101040b2602d10103008002d03009500d030740a6800911800c0c00c0b103103914401441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 327624235 1250 327622985 327623069
    0x40c0806070813291306060b160f14030703080718180b031f05150d05100b0d02040905010b2b0f0c030206271903110307090c0207050102010e0106 64
    0x30704210300c2c480c81020765160a940565170300c000c052040030f01c20003005140c2c2c0b0103154a401010360040d03c44200c032000103014609101c054030107202103200411101c011513001d0f03a54400c070500e8041c180c104140c85c25070005120251a44035940c0110404007a10b06441606107812042210304000e441000400d07038160103100c1c51031310005000c181200d0000804000071915140040050a015101221661190301c1401101e804118049548851040c44a2012449940401c041a001c008485000b9005071500f422101480f50640c0036054000d42103441c803d001c919400f551480c0355131030b86440305902d50180e11000103844004080101c5225501302c0c40c0d116030780d070001865a0001c0400d5112002040e85000312420360303190300d007000e15003282d0741411844482c07251104203a45000003800700390100803502007542e04000d0b0000a1989000a000d03249402000a450f114584121b0303000d0343c24070141e04094101801448255407071802070074070418840c00c0182c0701c090a0f40c0a2002048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 327625485 1250 327624235 327624293
    0x503070b09041d0106060302040303110a0218150d0803010905090d080c090d02130504020109092c01021b1606020106210f200a05040203100504020f0c0105040c0806070813 75
    0x1801703025030070080c070740c680340182c9071880c50502a06c12200354001001c4c1341c00c03078400440160346800c40e08e202803213002180d18a42e81e802c4a0790485146008055510000382440b000070030807100000c50607203c8840052006440f08a4101e95404800ba403050214000750300088011050f10003501300c0060040241c2c004020940201c0c241c40034000020800a413903070204420b651b003094854005010a181c20403404a02c01d03403141d103d1808503034813500c4540e00075100c0640b101c03d40541c4c484a02461101e1001340360314810341e6644240705140414064040e000045250040c4141c20844501007205144d109001103e8200960b0a00d421100704640c1400140401c103a9481c0d5841716469040403002e80c4040020404210032542c010780c8a00d0040003001070128242c0c8020702110820350b03000d61036841d850310048650142116040b00f9628150401c018440d04480300000c40e001c001c2540c81680f070b80c01d021104084200e51a10b450415010b294002a400340c4820045108401d203082590b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 327626735 1250 327625485 327625541
    0x60105132402010c020d0906030504062403020102060a0e0705040b0303040b040b0301050f100e210a08030f061801030b090111180a090e190c03080a0f0305010503070b0904 75
    0x1000c40c0098107500c04100c0c80c40c92190240300b501c0c01850340c1d0004140310082580000c0914005004044c00c054440d0042010080e45800517421922403082c0d421040344000113008100c0301d06d200584c018461980482c810031740c103105004011744c0d1680035080e094140028800646030441c90160144820030001803001d0013034011303001601a15000715525490701080090040c2c0c1a4005445009109010f1281d03e801c030f20310a00800c4191070520900180e2100c110038035070a03040124a41c0600c04d8040704220380040154420110f80e42100305d5600c0c0c250a200d145141c00d12010382c3c80311a4001480420901c0c0c0c01a0743c8032680c1e00002c0303080010102c44060310340102c110004043c441d4502807409241200b1120041c1080c01401c100455080c00880d83d52441618130014203040031001c40300380520108800051604100210b41c0c500b282c200061850101007252400a46083c1c0040340915002c40d0041c202c0300b2502e003083c1001304601c200b0000380107044607041d17210104040c290300c070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 327627985 1250 327626735 327626759
    0xd170309030c0f07181823070923192a022a01020c03010614090919060203070e0a060806122b0c05010f051b0a0806010513 54
    0x500103a40103551510342c02c21140745000910074a600e00b039001624140a0402e8050485662185510000ca02d901510b00000481000024043d045a2020030300034401d82c2c9209001c00009a0303801155100e079a252011000c5401052200b0800841007138540c031001d4100d0000f68000407100500b502461018082e041100d00c00301c0416001e40184a010542c04d11580700c5400c1c8040500203807600320103050071440b0204c000300803108420f451580c0e4560907442044540c699000c081d000b04504e540b52a040e021411011b48220b201c3c40c1c603080001c81000002c101e4200b0208243c80c82d001184082d590600a074100411680812465407100b042550300c42e4034413401000d4946502d00d80f4180030b0180301407540b0002660f500b40e40800d001c8052807440140c1000918a1b400104100f68564a001c6036101c0000340040c100c1c0d0300785404125041120780c8000d00516808041d504400e2107000c04102e02d01560a1f1500800c0103000042c2555000324000e01182070303a0a4887d48158444041c4015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 327629235 1250 327627985 327627991
    0x71b0e040506040204060603020309060402090c0403050102070606080d09080d03090303020706090f020405090109170f040803270915010c0c170a050d02072714040305180108150d1703 80
    0x41c5611210601c07040d400c0610420000e8002440c0661039454484600781d6942c1000d08000e005082c44030001e0010b40d0180c080d90041c2d42d02000075941d07001c0c14280600500050302507120940641c00400e010715020345004030840e0300d0358000d03109696020105074014086040e0640615400700003803070000705d5511440c41c10350305c1051000100303150340c01400200d40380180a50503d07071425202c440800d03407a0000d40202015060201d81e1080c400c0a0f64880740142d0b44180194070000c1082441c400c1c0030000c4080310050100c0214140101c0010001c4d4104c0c01c1d1030b00c050003d507012480e0b1907948211581c81110b805040c1c400c1046a59240d0301001c664017060801c070395000f2400403010814284101076031840b051005045242c100300c58100c04550f002500b09000e03040218074128006c1d1900004402c0e040c1d211294071b90300e02410013418550101d84501d00610304c0200c4040d5660180704081d0081c2c40aa15000b045884e64051207100350785400151410700f10040600c4245d1001402144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 327630485 1250 327629235 327629243
    0xc02120c010e0c060c0307020d021c0f140601030b01090525170c070201080601050c070f030308090d02071526040f1509020108151c06020a23071b0e04 66
    0x440b60840b041c0301d401c000703101d4030340c6110b21820017001e101c294001050f1a0340540440324400d601d2490710010381d14541642c02c110011641c1c0403082c05105840c9032803807850380241100e0403030252020059899140074000200a264180014043c0d01e180f0b43c403550f44110303038030300c031003035030050002031020a109148000700003604924050700c00115842c15990031800c0084414141081940040c02d2104018590340c10000c000c24082781c044d07030402c001c100070441521005601512814024050f03541116402c6032881807020b40d07000644001032a400716090f0040c02c0d01820f84440048aa451440fa401c030183c0c0b9074485000800c8680ca45118010303072007000b007034031801028074100c480b01004031840c443c1140b0380041080540d0b001003107980d001c50003441d1754041200300c03400981444901e01804d07000e07088003650a400c01101d60700038110720041d5141d040a000b0b404043c1c0c01040d065002429803402c007030000100161032440c1500303e001e50340700742b6440c040d1141070303103840d05000f218191 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 327631735 1250 327630485 327630491
    0x507051e03100801090b040204090201121e0b0108070206010311060c1b03070b030c0a050d0608010c0c02031606140a021e0304060e0d03170405030c0f010203060307050604050904060c02120c01 84
    0xb1a015030340410b15001018428020f200104580d1510f2034204001480a4050368840440074110382c8280d01898010003109801c100d03078184051039007004154940d218480700c2c0352036410040c1b58007541c1380f0b62090505600074001c503825951501451850130705043d401c07010130703c161009000c050102125880b240c5035003c600407558000c041c50300d01150700c80c0319410010003c0c840c0d0b40224504680155215040ca0f42c0d564803490608070084c08660311008403940707080c1003c00460352240008101d94001ca08498000c8264501d8840c00007a6118080100c1c00e00c84641018805c00400342a0b14080c038010380310003402005420301100d20703520a9180540000400344915a00b01400d052200b4040d40c10341c0c205405070760702030010341d00480c400030100040341c00103040060070012180105100029540c5010b00c540405000c0d4000351500307442801204c0001c141c0c0e003400c40c2034504031071008240303030781503110350f20b0b03100c014001c07948a4402c5019280204002000380b80007080c400000c1d034000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 327632985 1250 327631735 327631741
    0x60e010911030d091a130e0a020a1205060f0d1e0b0103030210060f120c050a060e0a08010203040302030a0c050c03060f0a140907051918051e0c040303030507051e03 72
    0xb5042c55072507480482441002441130282020300c1c180300034901c1d06528007507079a580d252550800700d54640c1c4903600c106030050400c03101442913005003800c01800c0d21a204181a400c0c003800965008890454110f040008900480c0c031700f07600c034031003000c0c090800c0c0041c01b00c0454072000c1e6001580402d6403055000c100400c201a8104140c2c50500700303143c000c000590805280d000c03066024850100d03001e1000d40c50304240320349541904001e01c40140039000e4944c0c1d0b05c06c007604880320a003600d0301c1628004400280c89206000312403043d5455805035240850320302c0107036450140364000f503516114052644020b17880800440c1e0007440342d015500014034090038500c0aa230081000701042601035000d12040b2240050103000340c035801c4440d20000751290848100d110700d10740c00740c5000051388414081900703155005501a03180740e0741001c00f880d0307141c00351002410f0036102200000740810040010a1190f4400c60304240189000c9180003408081110f48112001706c0b052080800024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 327634235 1250 327632985 327632989
    0x70606120314120114031e0f01180c0b0309030c0706120c030e0a030836061f0b0d02190f0807020a20040b0604090f0606140d09060e010911 61
    0x4400601100a0a020b01d0910108003500f203404040c854400405042c00c1070018999086c44034111984d42168410802501307101645d5888154910090307441d460640b07264203803401c202a20707030241d4100c103648101c64902440981c3c02ea2005001c00804d0106008080803004240030000c0145060796130300e000b03400e00580320f0301241c00300d4618409061404c0c20381d80c414400882c5c2e0780c00302ca4041c28108595503402d01e9a650b02d14500c42c0c10740980240e11840c00d80c0c20080c690b400c600314901011185603a6170b076400c035106981015000342800b410301204001d519030034001072001c140030000150800741408c501e120f03042d21070b200c1d000c0419003401c11440d000b40d220071003503132003500ba1005019090650319903441140020b031010040e02d00503041c80901e40c4a542258454031000340035181d4969641039007070b000741114078420303080c2401c0c10400101c036485405000001d0201401d65450100140c41040080090030300444001c3c1c0c03600454885c000302803080da904a0b01a0603010142040442 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 327635485 1250 327634235 327634247
    0x2060406050406080a0212150307092c0c031b030a0b04150f06060c0303020d090f03020f0705090606090105030a060b040b3105010819020a030b030606011d0402090103020706061203 79
    0x410018070b541b042c0104031001c06d5200c040e41d08500300300300540c4c85a5000000c0303414102503402410300e0b0341c142101511101148110744024842d6001c0c42c0340680781d0500050780340c084240325154190310498000f030448502c1202c0b00b8403981c008003103640c80283d80d5241000940110f030241e80c1c0300f400b508049281c20321801101c0c030103e01c0c40d40030000f43c5e0410002801c004a0110b0103400c141c0e0210300f182c0780030940d5000d10055030300032840030f0500c01c00c1e2400954400c03040060034814020900c1c00502ca0910103110350040000404442c00c0c01c1c1e141d130046485401c001d02955005886050000710f40a0041c010405401c0c2c0604440c0d6030540c40c1e0a02c00c10381740104000e5800071032080c10709040400e4029801c2611800d00e4801055110340e00b42d405a09402f086591015100280c0130580719055841110161400d6065803850b558280055440e410311407001800e6503c448407448031441c040c0d008048102c070505005042507071589a5800f22002ca4000038911000d40d1203c00a0640181c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 327636735 1250 327635485 327635491
    0x21b15131a2d030106050708070606030b060a06030905030304081c0c0f02010606020a0804052e0203070218040b0a021e041205190809130e031801120c0518010c0206040605040608 78
    0xc646051481c0e050001460b600c014030400c4100880864443c040042c01c10840300040e410620034480d9035100e050841c01041d0030b6440c54800c00f8a80400074105000c3d024801d143c0d07030048040c60450361680ca07024080d5201070108142500301d0440c003200845a44686615180c056403600240081c1c404e005e821200990482001d56002d4140c1d903000441d030318111000d40c0d0007600c214600311030940d98001803c0c003985441a69030982e1040c070a11950000203001000c2c021248010780d51801c1c846141c0c210f4058034003134890011000001c185009540090180b099403011000760314400220343c03821a003203034010380d8020300035201c54800c0c42000c1202e2104003074400c2000214040356074030590644210603e0f107000310301d030804030321030813000e0b5100d00f682054400c00c0d00c3c1e45402660b0100014818030b4200c60110311191010004000e6911404882440d1034541900e80702e0700e500f640e8000d01c0454100341c10030540c040040010b03141d06c0068802441191603c40d255418000c000c2d080e40801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 327637985 1250 327636735 327636787
    0x1c1a180a150e1506040908131202040b040c080a0c0e03030d150f0605160305090a03060c110d0c110a050d03230a0503151206011401021b15131a 63
    0xc41e05a2507040441e000161304250f0407580000c014044e841c0c17205460040c00c03240c40da85401d0280c005800501501c0340ca049030b200710b5040188048003800c01c0111820300c040703c1d000650420024801ca48503520409070b51002d0b00300078051501d550300091641c0d00c000141c44405440741c41c840c15181c01010b10b10080e104407000300c1281418500d00600c580035807030a6000a0352121924018140114221000e0301d03805403040d540135440f8108900a4895001c4000000d01d80300010b0115541c00700d440035040d0525074421039000207030f440b51010320405011880d448082048006619a17a50340c28150240c46916040c4021001d01855006aa142651076078246000c104a48200b0383c0700d0100ca078003440c1400b0401070240800046451062081d106144511034100085402c02d0007014551004009908450440b114901010122414103c945800c540b0800d60304404046160107003c608095403001414507a6800c03082180540080c0794603c02d100c0010180c44c0500480c0808c3e502c5410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 327639235 1250 327637985 327637993
    0xf100f15121203020903031303050c01020c06030105040903051b0609061f09051807060203041a0f030106030e190609020f0d120e27061c1a180a150e 65
    0x181c220038500da061007000040c5103115000d950540d0a000c1c1c0d05582c80e42d04041c04403500c1d101c002004880030401c90005640c1441001c80440303541d0700c000b41001810382c0182c8918156480e110510000e841401400c90901809001e041c1c40020420f030205072401d02c50006021900300000b00500b01b038406003d00d00a48100e07880048c10729402c0c0141c07030880d100386a001560380c2c1c9160105009005074451017155010720400000c206a0000240050340c00780c455008840c0340c0d45e400d9a110740b203104810b110700c11090004103c440c0c065804210048103820075505945040040c00c0b25510804000300d45d1503590f04901410b40c1003009154170b035004180c8428400c6c0d8003a480d1004d1045140c0c030404104940313000304031029100c00e5542c0d14200351010241c540040102c8d005144d200341186c0307050040303103550050910100031048800d805504110005242440188080d1081c0001032003584411b94100400c0b160400c10024148058094001d0303042120095170140c0076504030f5001c80510fa48 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 327640485 1250 327639235 327639239
    0xb1b011113060807170411060703030f06150e040e0a020901030b0a05010b070b04230d08090c01230a05040e010b1b0d140c0a080f04060f080403050703080402030f100f15 74
    0x900700382428580e0380b083c07070b00485980e41c0c1d00d024601d060000c0191f84d00103d010a0500800d074050700040c008450464041c07246517182da00c6040b143d90b040c42c000000480440f410852030a00b9805202644041020385111402c15004684002000c0e4004c5031584109020001c0c9881d5074070500380948040c0c1a0181751503410340b02d001205d200030300050441d0990202419004004d02102091500d510f000e9039903030b1041c82c0000c1c00c1080f08481c034900c41e00030b13820640c40c20b41c0f048214840e04d04410412400d030580a11500050b42c0000e42d070761040c0101008082409010781c10110300800c0d0380c00074141e445c0305154166051a003100b5010310075900852954003002d4010741800e0010020800c081d0b110302c04e402070b403440d0080300c8501519038000020200c07030503101c0c900240151082c036150010300d85840c40c0c00729200003084801500080f0203000748800a449140d081d03030420f0005040321b01c44014000b82d0340c14010f480400c02055955811a000c6c0c0203003d006895030103da004055080034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 327641735 1250 327640485 327640487
    0xf02070b091e130c090e06060309120a021002040f1404050c0a0f0c0602071a090f031e0d1104060e030f070506032a03040204240b1b011113060807 64
    0x405040c4400c0b00244140c020252640326042c07082c003008a007200c00e0001c1c00c810070740039180c40340c18061161664003d00000f4002d04044003224004c40383c3d48014121068010102c40158200982042c114022950101c1491006001600140504580040c4a6490509480c4401e90382a84c00e50050342094100030b1204c10100c255410f5441e2410180c01010059404850171f03401c240c00204a80e10102d03484040c00010280c407031680203031820b0268941c4401e00d800381d440c00c03100307000c0c00c49500802010303a400c500c4d003508c1090601411011410004800610000e0b07501b01c4203800482c0308040750400890707900c120417011600e4160041c1c03100d0044144601e494a0441c0039007801001c00002081d1080001017800049000d690162004000b4603d048070b42a882580c060f88603c0c01c01300160012301c0d2200038000c20b8001c040b801d0704003600d000244141904000711408680d0815100306103501003e0180c0b002e18103401a01d103644400e0060f41d00007414203070300014100407581040000903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 327642985 1250 327641735 327641749
    0x15070305090d080910090c030303061707050f0a09020a021c0311070b041e0602070b060a141228060f020306012001090c0303410d0b0a03030f02070b09 66
    0x502c41c50b0100c2d150340d900b01c107075180402d543e40342c02c0b18614041017503040c810310a00311410b680c0719980611031507070b58040410041128040d00c0c80c4680264500708228078003050b006003c281c02070800c00c1c4c91a40d4040a034100d800081c21000581c00074028201c005014850721009821103040c20041c0c0c00716100101081c2c001d0080003807604003000302050034443d0821900201e150400d50045c4444030320302c2d21001075041000c003103c0c2c261902011818901c3e040758040e0a80e040c070342d10713500b480a0040400c40c907900840a00042c1d8020b080d0790ac1041010710000e0707850300100008410f000d05442c0303401011507001000c00d030307462031042c000e010490b82d1207810050594842200c103510f000700521800e004211012008054400d6030900204068019101c0da0255031800700f00c000fa8001010000491070681c84030481000c104480054410442805403101c00142070b000103900110f480850405410f94100b0ba010842c009096420300e1780c10020440500100500d90f403c010340035000c1544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 327644235 1250 327642985 327643003
    0xd0b031e1e010f02070f1a1b1605070f140d080a0c080c030307120e0105280b040c050c0708011103011401030213030b01050f04050105060d0525021507030509 69
    0x401d071042400814150940068100010700b01003159030304c009140603c20400714040c216117020100c070700c420900c603e03082d80d203200c2e140301201c201c210b1444111054082d8052500c41c80d01311000031111b000311700104800700103019508125494a800c00e0a200303520f02d07001486501c0b07800b000070508001640f201c155002c00c0f00a0500010718a0b6a10301540d1a0283c580180041d20002c8100241e5960000c0c03000b00b008260f500c10406085114a0310b0309861040b20184a031920080318212281800c0c0c40d62000034018020003d10000ca10000509035414035050703000041740840e1030004c0203400d103c10b0004011000c02044002428140464180014410440c5085a00a40d0035080c0d010350101c403502180021948801c613100d1a2065034007400703006160040030b03080700303448580c1098411141a0303000240441c0c1007000b000c2080c00603210040c00220106003908008102d1442803a080301c14503100e03009480400011484018580740c01403a080030107081c5401d00c14408404658041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 327645485 1250 327644235 327644263
    0x1020f0702040e33072606060904050903030103031103040f030807060905031204140a110f12070608041505010308030a1116080c0f01090803011403010902060d0b031e 73
    0xa50218101065410b056044407000018a034880c41d00d0396001c500c0400f4240100d007544d00e4007098498160482c0c12100c80700600c402c1021980c040d01c1400005500180c1c040c0c1c00070a02442c05500c200407e09441e02034030012805e50011005108041c3c009882e441a03d030310b00b00850500d441c0c1404940258078900c4040d00305100041d60005010443c0c2004002c0d030380000460760759102c1a45018038442040790140c5140d640742002071103810300410f0b448503454010b01c00e0440d082c014400c000c410343c06803807100d61120002d000d101c00c6c481705200c00001800e03203888003043d42c40d10303040a0031000ce01189603101103103003c00510000d59803005982c1c00840d084400642501e28944e441101c1c8103038500c00c1d1542e901400f454080000410007030840e841d010046e15421003d544001e800e1b500c6954004240c4401171005009800f40fa0340d42c90078240004001251004c0d003034000c60b00c5a4000085000d10b0307600d802c1c1090f4541030800448880343c24400e0200e90024440e4803032034a96075078507a0a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 327646735 1250 327645485 327645491
    0x61212050309031207020615041b050c01091406070311070305030a090501061e061103040e04142103090c0f091303030b0a2c01150503060102031204051e01020f070204 73
    0x424010b0108141d075024410f003e600031007410a141d000e596107808a03001f000b12080307200f5a442e242028000c11144007004203000d03811024841c4182c445822030b0841c00090b44d607070000480410900007041b09070307100d03e074046c1500d03090141c401000d481e540d0380c400089000030801c04002a9100040b03ea00030002c090000c2e2540c10741c0b6080340034103034540c06481c400c41d039143c0c3c03001c01003402e060310400c0f1030044c0c49011103402034901140c0c80c1c2c003407407244519040b44c00c0300040c0403540c00070404507005a098169010503071a60760b000d611504406030408512004000c00011140400030000d0751081100e880c1030f400401c100107400c2070001098000303210301150001c0304242c000e030899031410b02d000701848411900c0303994600c01c8003484a403103040343c89071390345c807540d100c0c00800500d06a0326050186001d42d00d04500a80d1103a001a000e03030b045100810040b581260315680b1140aa4130541c05040546618440301400d10071014085020381d20400112030511281e41c11250040d82c151004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 327647985 1250 327646735 327646741
    0x80f030408190305150a030c0302061612050301051c050c1504120b060f010f0203040509041103030318010e03090a1e030807050a0209070906020604061d0712060612120503 75
    0x104149020b1010420341c0b803500c5a0784000d0305901130300014442e0342200300c40d02003164040104500501c20f8030014000d4601c0720011310150400d0001090020410395144824024503540c141595010b00083d02c0040c40220040c0054a400b1301c01c03448001010860442207020380e21413a03240d03800e4407000c5200b9441b02c0c100d00e1820348403501359001002d20220600c0c141c002400c20305d4034070400b15241c1d40b0800401d204c51500d0f41c042d043c0203140d2a5158001e50800303040c00c050280241015109543c000401096085190780810003103115800c01102c050240b04c010303032490300b0f45011000008480d0402e001220301d40d210b13141ca4200302c400186d40e1100f0301c801c03522424401c0a00da000641403210000d640c00500c5000201003004a100341c0e142c0e2030075501e001c0c084a030039000d409a900141c10200104000c00c0864026800b6062110081c0e410444a00c070824500441640310608802403c0c80002c01d11507503104100081c403d191102042c008565103480042812504010901c40c004c808 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 327649235 1250 327647985 327647993
    0x7060b2713060e0d170f16030e100518011119050d02090301050414061303080601080702011103011707050607020a051203090409060204090506010f09050409030215011409090703080f0304 82
    0x204040451800342036071945002640e0051283c952480003140140605002c5401581c0356103066103e03403040c0c012605031044040d4108c1c0507000303042240f003861086810341c0e80108000d1040c1c82c041c40d200d110307200c0d10340084001035003034440c018842d05c1c0b8003001780114400741c2003060484000c1b41d0540b40c0315030f982400d540240002e004410b4901c0d010340c0b81100304001c00000c3c182d41d40b1400c407440100c40d25992100303c400c09081c680c0d280200000c1001011580c1c550040168076000f00c010300003c10004601d0450b04c203190000d038050000264402520003503120140140300240c0000d94802d0315040d041e80115100c0c143c240710320380c0030300510881110516014030a40d803400b44011300910080206041c281d0294000e8064420304520380b9000c134049600600c111400d10300542c0703c6403911403901c000c2000928582c2400da0541c09400c0341051501c5031065518007030164001c0d007a05c14070f581800d000c4540d10061038260f45034030a030401c3c80804c06000c107039503440f500201441d94036581c42c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 327650485 1250 327649235 327649241
    0x7111e0f0d080a02030306031b01050901030221190c110a0b0c1b010204090f0c0903020609060705010f020d0509070f0e27060402090c0403020901121707060b271306 72
    0x2070040d2800502103520702102d5030200040d13028040480440340307401d40425072551000101c40c207140c0072400030801000594000c0d00548980421004418106920262143c1c040b15040740c80c2000d001e018541d80081c0c0341c803881001d061100318139020800343c2400d01c84941e507201600010b0806401c80303002507803142c089030846400381004071020b00c0ea1910207003040d010390014010000390508010222036030b00300510502c1d00c503100c103503a01030301c25245800f40003250f4030070410726420040801108011a0007400346810018070703a4030041c0d840400c0c414140c100ca40181c07004d01580c0250300e0800081ca030075000c0506440e08a400d241b080d03103030b14517000c400f882d004403d00342c500640090030b0101400803c10a2244e4000d460b4402d580e500c240a0a016100b6400020b5000400074010b0001c528880b98020641e4441d00d02c4c0d6010804941c0c40c042290802c00c0101e40345600c62048035020f041c0508000000c3ca554480d01c00035008440041c5002000144450501003074541014140140c44e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 327651735 1250 327650485 327650509
    0x30307020a0b0403120e0609010e1906080a0507020d05180a030f060207150501060504031e0b0f0a0f0b010f031a10050d060b070b040b131707111e0f 65
    0x80c540541207a46802660240d0000e00c0151750001c80f0100681d5200e0064051015040700202a20300c0c10360818019508945c5028615401c040b01c0c0041d451440c652034a0a0080e181c16100c400c0203240c00810700d030944400902e00c004540114072000d02080d0048107540b104103041200740d840207003841c0401d03a002405d40c009841190219810b80900421703500510460740624020414003140100e41c00940e202031013440f000541c100420000707d150913402d00d07082c1c1e40001400000c800d0a45640c100b010301511680a052600c000388502c0501c1e9104a414840b620362050146001520018180350485451a014107807a8010042c0000c2025280002000028088018082d29a1008060350054411080351603d0042d01045045c4010143e030040e640c460389030441d95865503240340c04010040c00c0004420319402c1d1140001785040401c280c01e91081c001d0b03a8807044513050040c680d03650815042c3c041d4144801a0705150300c0c4a00d2584e0b85e060a98000040c200404c0126664089079 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 327652985 1250 327651735 327651739
    0x140a03020d050c0a0308300a0e03090a08010b010f02060403140705010f0f0510060212041e08070b0706110c0a020f030c09040506010501090f060e1509130f050a2903030702 75
    0x410700200c10400c0660103000784c08240104044207002d120034000c94034090003804030310b40d1f42c5200001c041070916003281480e60900340c140d0b4200984800450b100030036541007040301c1e94454034410301c0da59100b42d6000301c2c072940707100900c92030400d41c0300600020102011051505000034184040c44000d40184c43c906100c00300800424040c0b0007000c00621040c0d07981a241424601d0006285200281c80540008041c030740740e1070549408005034685103800000c51007441d1031000000c020780d05222000c0103044030001590303910aa842c2180460395000c01758221079000f440340d0f1035440000a2a8200154152039105c03125125a001030300d800c810305200d680c1b080010742004204140410158120740003a0bc1d40d14680b91031b119260910b40581c002c4030005030440c40300444a03c0c00c840b034003925400002c080743ca81030301c040118000a55220500301e0003621016041e401c0540c45c81007039442190140100444032203036840e121a040c9100c4010b812600d40395440410381d405104403207600d1340c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 327654235 1250 327652985 327652999
    0x714090f1c1401050603010209091609050a08030a09060507051c020c21010e030309030315010504030807321902060f040e0a0b040203040201090618090f06050a140a03020d050c 77
    0x26140082a50070b5107690031909500f4440824040d00b0b050081e15203074600100540d44943e2030394400054403144075800c1040109400e400240d83d101c060800000d4a00e05001c1c0d6500c6011082c05010045c0c0741d0701174400c006040042001050000c80e1325800180c0150102840001d03400c1e04901d08640030901c2a070081055010408202c10b0a04159154580f203000b84240070480141588a000c2180c107604550070030400240c2a490000c0b0441c421003050400c5801c26403a0384540ea401d4209407400c54560201e01031400d82c0c41c1c05a400a0b20350031a031080c0c909038440401c180c940720340150040444600c0e0100100c01150703a40015102003940b6055003070b072615941c1d09002c1c12250250b40865100385003c00451080c01c00d8000c40c0d20494040c0c54408210389800c0007166142c2c9403107080c3c480d04042136800f0510a1990250340b0203042c820402240480c20b110400c954a07010b680725842c050300541035028241c4030424030308101d079012544541000101c0c00c4c40360402c0050010036070320000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 327655485 1250 327654235 327654289
    0x605040f060603050a09170c07180b1c0302030f090625031d100f17180705091605090a0e010b0301030c0b180603070309050a0c0e0714090f 61
    0x300301e50200c021180340f682c0a100c5900c6102c04902140e28802001d00a011f03020403a204540e1071000410f00f02414004443c0c407142c1d02c90440a51801c00c0820421039501c0f2003040510b4a00784400c20040c200e0303016800d18001c00d0350740281d542d00c109400c0f003040113404114080d07155151400e903215400c200d041c1e50041d00302c50039118084001072400b2008616441c1d10100712954003440880c8418002d08600d01050032800142c0340c409181e0950010402c901950350100911861428000c17142c07290203040451664050b07030b06114143d000240108002403c12808440041e00c050303600341c503820019903460b461000300303900d05540d030415005c04061100010705120340b84021030490b40240f112005103511100c512001d44200e544541c4403001108403181c0f60b00e0502c00458120b001820f0014800e00b0766a40d00382801007010f0180e8501e940528100540302034985815801000780c506801e441420904c40d030668081c10507014050320500720f914040f900c030302c3c2041e0000e005000300c89807021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 327656735 1250 327655485 327655511
    0x506040917030403170103120315180e0c0105210903040b0307090f171506131a1903050a08030403031103130201020c030f070605071115070507080d0e0105030a060504 73
    0x25106450460000d8090400c2c5034405c44900d80c4136040e00e9108960080104030f46e40d0032406131400c3d40701031004400080300000d05005c507694488000c0000580407031480c01036041a824404030b0340403541485000c0228508140344000c80411440c81d0030880c03000b6858520300c0e00d19500458100c014590400000d0060842c3c202095038100e440d1003030340c80140c9844290f078a1504100d8288440e6640c000030107500048208603000d580301402520381341e09100000c0c004021f5450b5000d0003240120318a46182e29420840d11420750980b84a035502810707448c568949944204580b4041c250407004004541050f1007034010b0580c1500040c800c6444e4108480c0d5200c2c182d01c0c80100701d0140c40390600121007410041102e80d94884190040c203806860040d0a4485a201d007000700c0c4c4110183c1a600345035514158000c5009400301d000c2c0ba201d02c1c061400c00c0c5010f0b01e40d00820201e5218048000500e50300c4100070304e04034400c2c80c100e5100e844440b0350794081c0440b904003d80c01801c03c0146a502 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 327657985 1250 327656735 327656737
    0x3080f03010807061806050c0f10150f08031e071a090c1002030301121104021303031407080304172107030c0311040902070201090f0f030b010501021f0506040917 71
    0x82c5000500f40c8503003564825055890002180094060180e05542005458040c00140c01214108002e460103003035007500107420418400380740d002095803000703054403114000d40a400500706140050560508142181e41c0ea80110f94440d43e00001d10b103000058080c151013a40d5907282d005c0d000c2e840c000006003040c1108070040f1484041442180303604007082c904140c16a403480c545401031403450b420704903003a1482030081419511003004107050710aa403640d10003480c804844070040400356043d881d0003000040511102941a8028070000c808a04940226500694050101c1700443c9001c00f0144c00d5004506010034011300102143d040d403403c800361103110b07800d140d170200030030420442d003a000c84a00e05c0c4445600c0f1030034002840686c8042c0c2c001e00c007450050610b106034a50360120807076022056009040c100c404401c1c1041004078a480181c050322007400540742c0f0000b8100d0035003403150002c604030906503c0303202040729600e49511816099402540304680c11112600c02101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 327659235 1250 327657985 327657989
    0x30c030807172106030c0d0308070903020303040806010614190e0a030f06050106030c09031a040507030c0906060e040b01020a150e01090302030705060f060901151701080a0605060604050f1903080f0301 88
    0x12054240d0f0008850349400b29000c419103100030b011207403800103501d007265040d0000342070380c050010318100400560740c1000030b4001080703904000d2800f50b04229000b0104105d41141c180d50b45424087c018400d03a10081c4803c041102e0700d4110010005500061000c1105500140c0340c008158a06010b215aa400080c140c81c0d064030248007140e69880202c0b08443c4034031021741043d2180d100c2d07588480c5040d81e01c40c0c220b4010801c80d00d1030fa03181c3c1c070f8100bc64802d03980300000300c581d5070f402000f0258101003007002c0703a00110b03000c21400b1081030000c0e4640c110040000c220000710211404100d6060307001c9074410709414000c12039415180742c0a036490344240b0342070391207100307240c0081c03864804010618072580e4068540b6081d030346041003082c50300c071482e048031060150a0f0f907030b504041d203072076405802000114001c00405072541080801c031000507101500807107081009201c1920f074402e440c80134983c180c44034030084e01200c0303c51054070110b400040200c5000209060594422405141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 327660485 1250 327659235 327659287
    0x60a0e06011203141c200c19020f030f0d0909020418050a09050609150a06060903080304050c030d12050a05090c1009030501140915070f0c1b060203030106020d0801030c03080717 78
    0x143c04c00406486c1d00c80b401058900c07035507984090040d01ca400314400302482010701c081c2c41c0c0e072070b0394440300b0000b400c015510406c062980c0c030001d005203800758013400c11402800007210452a013030070070a800200340301846030b10342d542d6283c101240c07420860340d010708103440e084001e40e4004d0502c41c800a07100c6410358002055100d5640100e02d0007081c40c800d40d42243d04949982801c0d074516912414283c20082081d2124012020705c16010703141070160f80308a245a544081004410080217000c4410250000d0105490041000501000025a01b80942c01240d0260f06110900c00c202e56440746a0001040355090507840d0000c2c100c1609168002c940c17420554410904948a0350b008070707011140b94000604c0800c0100180c0d014601121541c0d005180040d404880d2010a07180044241d000030016440040100400e503410701030b1030400c400c1c62420003219450b41d01d44002505032400043c2407000c000071030800b0002200ba1042c0340111724a006512140c02c140f002d500c0341c11003100e01c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 327661735 1250 327660485 327660521
    0x303110c040b09011e0312020c01082a1c1a01030b060a020a0215040308070b060a060f0203041701020c06011701050a02042102041d060a0e06011203141c 67
    0x389440c01d8018100d405002800b008480c1e0b1800c9080c050b00e181008004000289030b12010021071815041340100502d103030010504851030100060403000010280341542d103c81101c0030b04450343c5a01207103c0c4401e103d84a4071800780310a01180815010b080e01d00c2246046032102503841515965090282c0c240c070308200c040306038410301106118951204c00160007000010780107181c0009201200022111080c2c1007035200d5648502c584d00c82681951419505c800708107492800e14502e03c0a441640380c10346003039170f00c8800030b55a805180034040f10f8031070303f510700d01c00320f10309605980e0058510409c031481035960f50144445444041012041c550905001030380c292010b000305c8007103c1d0141c141d03242480d03484003228202c10741030030200c1c0d00c5516001d42c00d00c441c0b00014611420fa207050042c00542c102290200d0131240d86180c0e1200b560080c0004104001d03521010aa00d141c150901c2c0d0500600301e2050007045c802d0148001c2581d0404194500c00c0401740e00015031010540701078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 327662985 1250 327661735 327661753
    0x13050f010807020d121e1d12070803090a0618050d02060114060a0c0203061005040b04060b070807051c0503011707080730050d020601090e060103060911040501030311 73
    0x11140e542040b035502d0701503400f90282c80700da03510450a9940751a8240300000b801440514032080003c2803000300d0104584401d880e0030b9046d1103e840b8840d4034514001000c00c020404268406c9016400c0040c05400303021002a000300c02c00e200503c2c2895220700e04110303c142507114012005a0450181c0c1e4606c41d401800302028000144141640c07a0200c50514003495201088900c0d031180c0c8043d010031000040030001a10300f0455140980306494000707040c14140b009201c01c42d640211200d1203182000700400034040c0500031a181c4a80050000c2d9036054542081ca02e13040440205c1e1440907146000300c1840c66000001d141070318001c90b8841c4402d140d9140c4156a580c2c2c03070240a965030400181041200b03468043c2201d241004144400030788117002c1940040a0030f0502a43d40b600650300341200e5950600c074803809006040420884c05003190306940d528501400010003da81c1d030080c000070721001c500f0960762084010000e12147da1039144c01000700036900c260201602c07a858003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 327664235 1250 327662985 327662987
    0x512030a120c0801140402130602060a0b01020712030809120c030a2d03050907050a0f08060108150a0504020619020a020f0d0b04080f07050316020307060e030a0308060103020c010213050f01 83
    0x42d100c5014040c1c3c0c0e041c5090b401c2840210322a540c1c0784245501c90b03400c12802c49444400f068400040160350043e010307524180e4500d80a540c83c1ca41d44074110340080009010014049840c04600764051400b424140eaa484c036062801e04402d010f0402401d01045003031554800200074202c292550755111340102e41b0744070800d200000500d00c00c51803d040000da2005a200f0f030301c110b62120503a01101d000030354074000320704410f016422000403071401c07480c00c6c0500b590401c210f0740100780c010001c014002000302d5880c42c202d4040c3c1442d22203a25600400c0135990340c2c00035121001d400d1500c140c1802e10014000e59031b40600c0b04100d0083c5541c507a0342e00c130303071511400ea03029854008400c00c03465a03403a500c40000764810400038950940c107100c6000800c2c010000f61102002c0300040080301d00c8103004241c6400c03040c1d4848410000321051400407518042016003400303506003040e001945031240164003901071071610301003942c80810300c00782130f400400740710381120b50603212a0303e55a60140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 327665485 1250 327664235 327664241
    0x305100501210201050d090303150602070302030d110607120207120806040510061704020a0b071a010b0a1209020a050405160908120301061409041d0f0f21040512030a12 74
    0x2c1c081e01084051101c000808447c0d04178848035440703490000340e50000b80694805030b400e00e80025005170f11061080c0300f142010032003d40e070040305007411035500c0e04000c0c1e0250745500040c4001c1c01c0024401d400e010124403a0141c40e03086500282c01e00e070355850343c8001400d0f8542216068803450400d400300382040380620206040d9000d0b990f0341130b482100e800701c4210948002d001281c02040c41300d000038600e5145409006013620810094144150107650076000c020181c106a0f414034007040130921064120b03000048031801d541d004a400c0c1c02e1400010b6401d14103a101c6500315040008006234151040020340c00e107907140e140c0b0507101e9200c051a82d500e07400b0142c084100c0000300014020103001c0ca510148400ba208030302413400c1105804101600e61607121200465044800107e034200c0600004e070050150307000a090014a954080d50340c0c9030031102d03903048110030f03044100740c180110b800c9a000d0036003c1d04513011072201017601a5030f42d02c10304100e40095900322031850080d4041c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 327666735 1250 327665485 327665549
    0x70e010c15110c06040b040c0806010f03141e030a14340f150b03030c10021305041a101b02041107150605030f150f07090305100501 58
    0x301580314900104907598000c010107a4249076400381888810300c411410045203104d00d02c541d11803806810f251034a080750140e1030708484019040100140302142c0c60440d031100301d9800800154450036030200103420090b0000106181000d03551041420b114004010005400355554000004044115514a078001c541204440000840e01100c1d854020300220b80d082142400c003960740815581d41082030400c0003021154100b02c403024104407000340c031500554000c140c014600e000e030068030003a154a00b18040c80c4c80503a0100b403070440c50708000c011401030300e070143c400c00560540e100c2c04088070040c40340f4588292140602055494800d00310b6003c0d0300d941400c28103c800d80d0350700700005406410026403010f201030040c240401d01181640140b1102c110001507410f01300030a040c1070590032542c0d41c00540c030000e19a0860103941da5680d52089038000c1103003050f110640101c54003110781c1d00180541c41000140e00c038100a541c0b045d81203d12402103080710310f600c4400380083c41b80017 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 327667985 1250 327666735 327666743
    0xd0207060914031002071406040f0215070b0604091b08030705010b0d020d060f02120a02180102010213050d11300c010c11010e10090e060303030615070305190503070e010c 75
    0x3a4040304071403031341074005d060171030704c00c82425086d40f20340e800c0b042c9001000c0b80c040d202c009e03c0d081c011042d42003241c440380c06282c5400c1e4661030918581c0318007000c40030103040749024070303686ca216105001000302c6124944089907040c01021340d417a9800303681c81d044070340d098810794a0841000900e181041c10b0b00d1999078081c01080110240c0d40303600780144604100b4040d820380030041c24030828000c2c01400d01c500c1016500581303070b226280c903030301e2065000c01116055a01c100030102201d401c84024000301c8108a40079400000c243c680202c410140481140c0c101601020958202140c1014241c001d441941d400203a8064900c980f03641d08103412095000c2602a504078000c41c41c000e031868134200043c10501b442150300300102c0d00701843c003800b80c00040d0b60100c040c09000400c0381140d4110000310300030f50840c14040001130b4040d00300242c14002610008441c01014001e0003681c40745c0c01d8514200001c9003110002420680c030842d8990001951044003000f00d60040b03010320601904 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 327669235 1250 327667985 327667993
    0x10b06040b12130b0601051e1605060a09230a0212060105030d0509060f090d050a0308060a06140f070215030403020a11010804050c04021804060902070303060b0c0d120e0d020706091403 81
    0x40e00d4019122035200403070507a076094191100c0a880e2023620010440b1800c0c414049180b0107450070000e0404401074120030800341031561000120740010380305680501d0580c08601001e405103d41443c1030004c01c4001e410100c41d00460312004408507915048501c2541074078285031343da440468292240c4042594400818000304024982d400098100d0090292680e0100a0b4a0711114640f003450320007100040c20781c8017000702c0b509140410000800880c20400c0341c0303030901c020440c011b0045100f007060402002c42c4801c1076655098072401c031640f0303403a030303041c0d8030300300303420001c0d201c40d401807054072203507550900c074007055110f8a20300780302c0c07500131014000102e10941088081c0d40202c0c45002955104c01c40c240c0d26507118816580140340506005035261490300e0094103940305a1300230160040c05126007015101e01140d1036200d0540c034a00441d0480b01c800849005101002440c189441812504081680c001031413100b41c421540b0758031200c2d5608e41a8961002c00c500c212905a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 327670485 1250 327669235 327669241
    0xf010f020a12030e15010609050103090201350c0a0215060906280902090306011413052d0601120204080a033504210804080c010b06040b12130b 63
    0xc02d840e90015001c5091401003810100d40d003145280141224215048603104001081680e400403c030030000c01003802c1c1800305807581e4001034524541e0a040b1400d0348004044426921410303000c45940025074204070989040c840000011504500400c6000d0302c1500481d40902e103d02d0351b01c03032080d60021305200740e40e41c0d42000d0182099040c2c3c1040040c801c09070544400220504070500605100c420041c0c8841110782014031b00501070344900034903803145e4018a8651101c41505411290034000400c2c96102e288070940003040d1182c000d00c00d090b0014216550280da0121180200826601d81c0701c5680d0091455040b44103501c15104540d0200e000003001a01134450030700742e000002c01d00300580c40a602c803560136241e10403004108180309410401000320030400d842c944d65141e041c61415480c8150050003550000d000502404404101024005025040b0601180b40a070070940c6403551990125032a400480c10310000c4500c5c5d400146000042c8140c11003140d400c4040001591 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 327671735 1250 327670485 327670493
    0x606020c0a1e0305010c050a0305101a0307051606060303200618030910091a04030510050a1b03050a1103150907020f1c0314070f050a030207050a0f020f010f020a 71
    0x840007500030b00e410000c481000000c91300a210b841170008254980c0359542c0d000480040440300003c0c21542c2c140c10081003440090fa01c40604414803281082e8155240c480d0071040e1500e000765040d84c542d01c0c198030780c8101004040e801900c1164401d03180d40f41403810414104c1c01c00000f5140359625a17008d45c00065440181c55040d40003081400141e0f460148800007048094840e1420b410204000300e00801048100144a103444891101c031141880d041d507070707826161101c4204800c210383d00c0340c0224040901e242d01043c2204451001e0003200c1c00395800280161004407000340c062407900d58603400d0020100c0450384101c3d2442030302240e030721903041046981e82c405002c00301140314180042400040800541e900101000c00f48000c0c0c40a41c5802029a980d85c1c4000c0c45984c0e000040c010440d8020100130fa4000700c40c2092520750780c2d010021030003809110300142c0390740714100c0520203002c250b00c59848050700a030350101c0c9030221040152690880d00d610000103a001e5083d030004a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 327672985 1250 327671735 327671759
    0xc0c0c03060603150b1e0d02090103050a11030318090c1207030c0e0f010806040c03060f120210030e0c01080603031c06090c03050f071b0812070e04060501090e040c08060c0406030606020c0a 83
    0x210900504d007c4c041074290f00480d003041426003086500b030340050b608109000385102c9800514804030000c524040d4824003004902189506003800f4000304400324502d84803080565882e0f2040d1400700a8a141105004020b04443c0d001d04020800c5800fa04201c0d0501c402400c003440b0301a1102c06040d2104c0c000c0c0300080c00c10228080802d682c1c7d180208008850080030b20041c00d003844400b6009042d4010042841c19000d058030503d85030041202c0c0c0804041a46070000e80e003420000480e0f60360001080c118400c0c800181c24041c48090000f10741c05040c2d004c1d41c2a0b88002500b00180382110f03006504071803041c0d9a80060710210b0000800d00c511a00d90341800410f0703600701c6130b64000c0710780d502003044e0005020355426010101c100040b079984030a40918440085400384440c515040001c0c12040850013458050312082002030b0030300036010004c000401c00013084403000d140c44a52142a900580030f03000000b0f003410b00001d0703181c0c80007c060f02da46000a01e84030925203050032020003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 327674235 1250 327672985 327673039
    0x1050903071404020f21010504050f04080702120124150e0904060b06030106080a0506030d0801060f02030702090108030408060f150d03022d070b03040b07030c0c0c03060603150b 78
    0x485030302000740c09117210f100c001402c0604001d41040004a941110318540300340141c00c0140036034501000c004171000c3c00c0308510742040c1c0040707030b181c0d4403001070000c208050030111a0812a40c00c29403804014031000040d0b00c40700007034149908910746c855003e083c1d01001040c650b000209101e040309c00d0342c6031907012a900a4400d16001034134110407008507410307400903030003100481d07016020019106101d01406070721017011000740c0001201800c02400040040c000c2c501088420b0400c0302c0d04900030000c940c5000e40042ca08152907039074000090350b030303401406141e00300d00a104c080b03200000890883e0f070042500041980e2030300300c0507050290300c0c0460b04098045200e2110701c503e00301044074041d503440c0201030560361003001055441c0d1419019501c010340c001003c02c108400704100d4540c0941040b40381c64041081000f040301158011861080606070487e40100007003081800e40c840811a84280c1c9400d040030f460b21901002c680c4041e4a09402101490082482029460f81900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 327675485 1250 327674235 327674239
    0x909020904111306031b17071e0504020f18010c260d0e061b040b04090e010902030f0303090715050a3204081203010f0909020411180f010509030714 65
    0x28421114201140503640617a20682d0b80f0514042c04c84042809042d544000d80708140c0183d8030741c41502c54403581c402c5188205501c20030b101107134166407040b10103048028840140b05541b1488800c1c00c44aa0b548203444525801e8001e03a120007065004801400036140c11004c607141181d9644510002c0400c1201d10f001d0303101040240c181310000d1441641c541e580c40c10000c0c0b02601e0b1520410300110680200001100001d00040060141010448081e0b031003980c0046903c0d540c50014601421146030300940c036000c0e0f040b407030801c8100000030b180b20b541d240b01207400f01950b42e58120120300f034840e4a94005034013001105442130003a461f0140b21440c15004141030340071882004c07541081c1c61002d1146000000d420804404100b0003840254203110300e07545903515100d0304840d014094403070b06000a45560b110000c0d076855030f1001d800096400c80c4141d444400c05501c101c0c1859a010b1f4510175000c0f0440705448d540f091069030786984000c0c0c01441c1c0365040c1404c90145641440f4015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 327676735 1250 327675485 327675499
    0xa0f0e01092f251527020604090e062d0c03090a06050709030c080d230c010203040f060507030608030d020c0a15020a020709020c0c0f0103090215090a090902090411 72
    0x101456041e1002480003012450100b4040d001c618110401010340d1100c42d01803130400c008428203005161052014800c1075544880d081551b20114103035004039801140000c2c9410403030540540c004c10000d10503c80005628070000e00c0780b15007081c1c00b82c1141842d108112420020340c0918070305004603000094407046920712011650b800080d100c04582c3e0000180032420304004014268409902810001026107101c60382c170f0720024020b1070701c1e03145540c0000c03103c402c40c0d201e45052001c6450701d041503802036540c0d10b0941000c000c2e0070720201048444901d4000001c10503403003807285800b60ba450380051843c010030068103001075006020146410301817011030b100051280380103102c000501841c09a1a08900e450290804070b66901c482d101600400440d205aa00030419290100d0100c51100d00c41c50315100480080120440003900312006100d6001d02e41501000303025107002c00c592100c4102d8444150101b44d80030742900941040c0010003086c002500e20018025405024100f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 327677985 1250 327676735 327676747
    0x4090618060b040c02010209100f094113050603120d05070e09130204020706020c060a060e0601051c1a1e0102011a130b0f0a0f0e01092f 60
    0x8800061141001c80304240d0303030303032911a0a0038107005101100665000850130708000e8030100d1082008507101504004000a208507401d000d2482000980366080c4010003201100d141d854110680c40740f12139588518450414a000c1d8029a0025001d80980001e0740c2c85500e12090000c0c6c0009482541e160242503c03100f450410400a800400c020701400318841c24050f03005444001800c1c03603580903d2400d0b0810281400c0d81c282c51204560695005903150740da070410390000c0c011015180703032600680092014500007030300300109a0701000b00004103511008010740301c80c4600c685410810081c01021024151141d0000040011072220b6100080400c00010400113064400d260b420307216581c59011560709101c0e16019062031801c2c41114401000000c0c000350030301d01072004d41d984840da951141e8440005060038420083e1040c900d4030388483d14680d0b02c40060241381800701062000085500081c060700b000d892500800320715030501c0303500c3c0c0d0b1424041e5800303102c1001030070409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 327679235 1250 327677985 327678011
    0x20a0803070f0c09020403080f090f0409051f150603150f03030512010b03040b0606030709080f010f1a01210902090a0c1b020102190302070308030f09100905060402040906 75
    0x10806180310302d070014249401442d00d0340040040d6004450420710500040c80041d40250880e141080e20b0300342d194881d071622000800d0513040c40395554005042c188407008008000a19485001c0e002c4070103501542c00c0c58600d41241d800c1e280321005a12440010000039010f503000d100200041d14800003035503180c0c0d60008650400b5032040740090b6002902c0144d4005103841d1a014010465a113861410280c9030004034080280c149441140300101103070341d1901401040d0010034100c01507680070084502881d00915008011031445030900c1c603504901e0482c0c0028100002050316038006105440314141000741220b50304461650313440081d040560364521b11a44650614030000c2903558038444000c000448203040ca0301c1e05c194407400300740141e80110380031848004e014610a1005554101207241c5500c070380c009010342800005014180c450003150901c03e80e0342c01c04803007440b120365040300111080d080c40134103660080d5004c180146425005907840380d0180c10041418251905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 327680485 1250 327679235 327679237
    0x1060e0103110a0917010905030d180506091e060105180916120309061b060c20070f1d0c030a060504020c01050603100e0c0607020d082b0203150904020a0803 69
    0x3e5030720041440540b01700700c5054103103c1005a054041c00070300c0642d48640d1041c0e640e0080441000c030317207a103c2406144d008200d1000c2006103410500700d4000b4102910f01c1078840c3d01d000c48402e000304002000c0e80b10801c000410038100d92000d00341411030199480c0d1503100300006041101e0074000c080362804202c7c8101a03900141041602d40c800d06401807a02a18541301075016809004170958800251624080889149604070002140f0b075540050112020281e42a0342e00c01640c3d03003900164062070000344041501c0801140f10540c94a48008101c000c4028800c1e14000000700002003803918048091600f20f0132a00b401f11ba69a02e0b500041c040c1e0704540354a482c580c1d554410091350345410090303039443c1001108100141140c580e80c40b41c542d505158064000d6074006130103c02c40d21000741400803281c001032801c0d11110050a00503900d011403152805074501004035900e070100b01e2084038040d03180d100f42da44a00c00c0c2c4c81e040c02810000108117980c0134468030300000350050184 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 327681735 1250 327680485 327680497
    0xe03070b0c030603070608010b030a0b0118120209010f12030e030c0d05010516030e030a14040f0b030106030e010203190e10151a1206060d020c0706080906090a0b01060e010311 77
    0x1c00c25622403804a0a05141042c00da2110741046103000c010800c800c00b82c0200c0b6000784040d180490012040301c0162540b04c035440e0310010109142c40300103080c50000c9850001c00384200c8544103640d80c3c4404490040405002d45800e490002492200090081d004110654000340980d00354900d600001003410840d024141e4580c2d4680b030400c02c1c6403003608020140c801407410700300a400d00118200e42d482c01280340003070078441c0401180d88645017500680c1e00801da440302498840b511180311032084d41080c0f1a00007c00e08041d41201c1c2c8004c18025244a0f8086d0516609010310000404000c0e1040490780503903402841c446100c0d00045008026808410760a440c013070034500380340c1602c1c0c4c00c83c001001a29034028055000e48c000c0e4884416007080e403c4500c15103440e04c0c0c0d01c00b40000d115000295406200f413010010b00142c100201c50310446510042d03079129610200003540303c0c0038a4600810060403040140490b90191802c0ca04488040c90b0010b004200ba0020940b2a0f00074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 327682985 1250 327681735 327681751
    0x3091203040b061309050d0507050705030303010b07140d0e0603040807060c091a0f040603021309180b06061e0c150108070f05011d100c12030f050c040e01090e03070b 73
    0x740b070401c072039410083d81e000d0458600c050f0800c88100d06441c0c854a42c0c4813000203808011000a101040c8181041400c001d081e004050b02e54170b5030f60341081901944804130446810440518110044c0804542c10304869450b07100c005048000500300b080301e03880204111603400f0107000c12800300300f00303204400c40e061440d11100c503105e05000002c04881c0d0501401a100c0c0001c01203103603500c94240945044440307a080160b00d178070700380c0400702d80300390305d600030840c030031314109c80603103074111000c55614132034080c1d00103114603100d0406200040c0f24802d0040c25102c2c0001c2d860060718600c000400803004520180c400a143d00f00728009403c8080c0d0100e00164002c1006100c070146a804e00402400700342000c16500070400310002e0020070080d452440f518605607180140350185950074480c80e0312400c222448a01c9002c0a030040c074028218501103864100000c00d9005048120f0b0181ca28620341c4522036840c081c806405800c8044141c401804244004000500d9021081e0700407481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 327684235 1250 327682985 327683003
    0xc0a0606080105060402090d0b06041e05070e1f08040c120503030f2217040302040f020a030c030c142107020303041b0f030b10030506010b0702040b0409020a0b0309120304 75
    0xe00341c181d82c25103c001d44228411841000480311a58400d0140103e150b80441300c2c0318a40e540000140082803848402c90342ca580c01201107030320018541c0018400d081d03e417255110201c920381404160110101700f4845400c04002d8401101d0080c02c5880d40700b81f00c0e04403a10b4aa848407112840080d10390012a078940c00032007441584c07000c01d08569030080344014555501c0e0100e07110640c00000c001c20141c1a8406440c2c210080b903c5081180c001e1031300500180022031a81110000030b51181c0034220001c2d01d000a4045581d2207400780980000c1c0035902c0c1c007800803058000d22043c1c1c1c055002559000018407121001034514010f10784030f007019030003a54480c5000d003095203190502020008040c0d04950301440368000a140c0351040d01c3d0443d40c3c01010340e032152100482507400da08050194882d03071000103000751801e4010702e101c41c42a141441a0001201408280c6035801030080d4440010007007440200e42000c080d640c0091003108031111541c0c1201c0100282e44217030350136a0440d41c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 327685485 1250 327684235 327684239
    0x18090e0d030b030309011b15090b010905060d050601060f03200a020d11070b0304050124051003090b1807030c0603050609090307020a090f0e01110901020601080d080105150c0a0606 79
    0x141500c5002d00716102600510701e01106500001c21400b035080041c414007d407240b0850a200160504140743e003450442000990b00905000e507919109200d4102e034903042100080302401e1000c51031011550080080045074281074007034a9495403008130b0002c15940300318040242c000448501d9446401840c42680d0310303080d060003810540780f010000b0a10201c22000802010001888001c9415400c843c1d80c0320b071180e16100c0d014000024280d4440e0108104191000a10807011011200e00b11400045180d4640707082c0d058030300c85600a0202c4004000203012114200c09070b40c4981c030040c0a82d0b841607140d80d034042c2c1c485c443c4e801200c00299030701308110203800c0000201d904181002c008604286e41d40e40050490f010b80c0c024020306076203a1004414040da0ba030042d2011040d001d0090118084961100410707400c4020403500510890000068010020039892856006d41c7c2d60783c0c0e500d0f82858240901200301700c401000300e1604000700800040140288503040780b01d1540070130168 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 327686735 1250 327685485 327685487
    0x180613050601060f0207050d060920030d0e012c03030d0f0507050c030910051308030903010f051e040305042411060621030f030f10060c030f18090e0d 66
    0xc81d05030000b00078010042c0080314410b4000643d40100c64080320302164410042c07030403201502280c84000e1a60303c1c943c5400c496403078030590a02d2000001e60480b215030103081d0080b540950484003690106142d600800c0b8001004440b1000391103c5044c405420004540401d1031503110000d1884210b07960001c1190110b410701078541c214480e803400904100c0c4ca641810b4481c0b2610310b00c0d601c0b0701c4076250b2201116000340143d0300410241036031049010396070800c10740ca940c17048180905c03075482d04040c070064014034402c89010b0120541d60345800c08891402c13410042c0701170001d60600405001c00507049540c500c03222111000045440014400180050000d48410f94515980d401000401445441b031400c2480c00d0f0b00c50160550f0044102e81e0301134118803440c210410034a42c00410080c4458040c644075010b60b40071031000c0c00d025561a4100c502e29014040100018418107461661600c1035000040e0400f450101c0d0315400e9441440341d0485101401c0c82c0c401e0b400c4040a04510317 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 327687985 1250 327686735 327686743
    0x19060501050303120a18020a060f02060a02030c03010501110a05030445090c120602040303110d02070e04020613060e100e060403140f01020304110906010f020604020918061305 77
    0x14102640110f040c18241c05030459851300090a001c105995140b00e103070002c00e01940701c0c1c4d049401810a00c01692034240c020842420090b001026102d11400308660301341605c04c0300c4c8114800f0070754a04590a00740115128102d0000b04442d0384182198840850b5080c4001d20007000c501d802607030364513204680d400300149007030300040d001c9a1a184002500154203181d14101d030702128006204c0350b00e032601805a0845030404003002c030020380d10200308125507009206990207620381d00c0305074070b140c0c101720740c3d45044443c0d140058004190820400c0c51404040303030054401802e40d4144130343c41e8000203400d0410392080c40050500b8040c82020300f002085400d50b03c040d490310400c01e0b141c1d00007148a500c0356200091003104900c201200b0240240040500315110a000b9586e03801c1a04000124400400c000c0e80b14803903d2000c2071641d03018061142c01103480350041c180d5507446800300505004010070400c017400845000552111050090500c141ca803140310700d09004079414018a8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 327689235 1250 327687985 327687989
    0xc042f07020109090504350301171c0e010f0309060e07050f270a060f080318060301051008090705030d030912020607020601171207110907031112040602090319060501 73
    0x1984d4988010300021a54262888070303d1310148492010003061000c40d0081003440035070300d040c504404030010840d108448801031500e850780c1d04031844030740d00d5080200c14003003c481d5000400d603410b580500650240d80c0340c01071881a130070001895016074907031005440e4060f0401d00990007101040c0540d280905da00ba420700000c3e44c0401090245404101046111035804050714407184005010f5890344d40050001d400c2a90001d40c2c65541d4800d02542c03500019801000001c8142e502c4080307041c1b41042d40d040b56001012200f151040c420300303540d41d15010300955194001e0f90300110303003074800b00003140ca60030482e80c1c000340160880c1080304941d81942400c50464001c04180201c0e294006805415540d82600085050300304103105460000d03030f24032400d044900464540c040c030403200604106624287c07001d0f0b00a030b4403040101c0440d581004500e41c03588040c424800f0040d41d81070b42551161040d01d0040c6406081000603140150a00d0480a01322800070004100007081c090703240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 327690485 1250 327689235 327689249
    0xb0c070e060d08030405250806010621020a020727110306060708030910060e0703050f060319030909020f190c08250b09101802030c042f07020109 64
    0x295070411000041142d284a20040d02500020020806006d002e1044482040e12203074101507809602d810554409000d00c1840b03030b00c2c000d0500028070303903000301009005402c050904100100c00d080032980250480d43c2d02d042140309a02c0041403420350101c82c045d010407080b80854100c0400b8410000b520002d029020640401307205100b816111001a26030f5150f2200ba491b451b81c0d200700350b007481c1c08280a111030020b4100400098107103010500b0798050b00c40c0d6541480582e46000d0b440480340402d03a1010f0f003507880080c02c800da0103000721030303000d61602c68541812100c5e550700000d0140d80140c1e00208041c60f0008032611002d00d0408041200259800c001000e4003082e1103c003901d0007100b002c40d4401c0b01c440780c0d204a0460720250a035400e584407040c1007a80c1080c1c1541a515401224050f090b185072039120080400351196410079640e006004100079180d003420b00000d03080c4248151506600c9940b14100c0704e1010703d2401e08d0f030380d030313072103641c1d1520041d00004000c0c128540c4140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 327691735 1250 327690485 327690509
    0xe150102030f0a050a050f0f0405010e010804111212040e0702010b0306010311060711040903030b0301060f080c1512070c02010219110f1f0503180f03071b0b040b0c07 73
    0xb0340c0391901000d4410381010b6040094440c02c0880095800d80b003001a14000d0788030004e0b60b15000102c0c0300160041c0d030300c00e07070309c07409414503000056035610360039140580007206102801c50b15141c1b446c0810441c5001d48140c8514095250503024170f81c009030007401401d45032808000010303034248035800d0720f10400c80091402c4c2d40365880740b45002c80018441802441d0016684051024072502c0508500340504100500304050800400410f1040704084c440c2d424604001000601a0841c07001d4542e20405080d0201d0701c181040311051545018a40c06042404000e508402c11102148280700d03540b2071107140010352000a0500356440c4440c0610b15052a41c0d801146080d00c2801c0030030313800c1d81c04111040100001a50b007095281d076446c4c0c07401c0200300f00e45810754054051801003500c030303401c0c04d40081c0309108544c80304402c2c6222910341d88140056030106425030078928482c2d506000c0e0b46070b05030319800480d14540c40343d08440c0824000041040e1b01100422401c0c000f451900c40f09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 327692985 1250 327691735 327691747
    0x30506160c17030406150902030f011a04090b031006080a0b0702010606050d09020d05010c050702131b081807091e0506130c18090903081602070e040503130e15010203 73
    0xc440b000000d040024103115002c00003804110383e0b0b0340041d0754a81c03040e05000440303a466204001030352049400c05080842d1000001d51302c071070300c05110700410030042c5080c10541040550802006802001541441619000d5041083c03e22450028060b654080c2c900750000f401d00c4a40c07036401410900c11a031403c0d01c10003405078004250340420380c0c040d6000c2000c0e41e260001814581080c0d4001c2d00c554a020218102c164100c2c0040c140b4a1086e21a01a548404100d0604580c109090011000c0071741103003d001070321800760298030542014511294294441200303180c8443c3d40c2207010701c51b68440d0b506001d07100d482d00c0600703022802101030102e843d00e80e010804068420340d21450a07600d4201001030b0500601c11624a02d800207039007445213555480b0840507100010b0290040f580e0280482d0058040c2400c0059103078660300144001c070319041d4203103201c0303400810542d82800103202c83d1401c070aa0303612a8006000c1c203500b2a480e4142079a0b04a29a4948414241035510800407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 327694235 1250 327692985 327692993
    0x120a02100908060402010e0112140106090522090f0c0927020a091a040912030e0601030b0c070312090605060f0d02092a0412050c01050711091b04030506160c 69
    0x2140e4000c0d03083c60220903100c3d2800062764501c038082c02d0100c80a0420a203030035003001100b005d6040b9409961000300c200c0e904c400f4410341d03d29083c100310700c5210301604160030741c00343d8003c055101d1080c00d10030703805a220385651070405a260480c0012589503a188c0400f030300d5094100c201c68400e40d0300442e084601d0703070000e003c004070b500c1048503850b25040c0540001d058031250202410000e4020b10a1481c1440c10714907040100079110042440c007d0b030044d001038002441e5040e607501c40c0200c000d81d10b580e500b2403125003001c2c4045081001c0100260800c85140c050118594403804005c1910700305001000008a000704d2007600030451407110741c0250359400310854102c20780441046000200401c00041000009401c2d098101c00040c00640303c1115100c520140340103000786c031a000d68182c011103c82c41540e0010740001000803003081c10f03181141000d6000510002c04010092082c03008a115170415481601c907600240100301c2c46100c5400014070301041361a0000650385203940e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 327695485 1250 327694235 327694243
    0x1903030905120a0b090102040f0314010501080d02030f070602090a0b0c07080c01350403020d03050a0218010e041d030a02120c0d081009050103080c0d020d0503061c02120a02100908 79
    0x3c09491002c0e4907000c2600800294110390140490745000c00c00f050f100c2c11304644070341d00420010425881c0c04000940c103500845d02c0c10070030740c2a5029501d0300b0124140c0c0c00690b000001c0c2507400990030810205960340d00000301c070041029510440d12188001119410b001c25940880b0b9641c0000c2d0081c1c42d540ea00c11100300482030004116030603404041403a510900c9404111180310b42640180020701d50002000325090f00c2d01e550a11090381d03280781100983c02912194860b1440014a4065075070240c01088005440588005111300c111008480380740140d251711045600002451290b1a5060124441c2001605004d611302218040340a50321201c051081c010000404049204a851070f000c12000f805502d00900c4256120700707140100d54440d064a0071a4031808500091050011032548180b40441e25080c2c21a03682106214508810004030b0a902603840340200060780c45030380034048001600d0091a81c80202d1041c04600140d112192040c403221020030000844009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 327696735 1250 327695485 327695503
    0x1a0303030a09060f060605070b13030e010302031503100c0f0201060323150703151e27020d050601030b0d050c10110f0109050c0a0b0d02090f190303090512 68
    0x40060001410f0405034010800090a81c064905111000800d1030b803090103400c8a80c0078071a4000d050b183e1884400f04516a2030000380400c0082e03403290220740c081d6016691141d5200356141aa0314000002802c101e0788525038801c1c0c5a5450010000d0366208a101091801c0c500003005804c0c11030b20b84076415121011b114900240308080008102e0003844900440d000851040c00d003810010006805004c440c05a15580c5000000000c0c654581040402c030800700c40c06051a080e050807036000184c040341c440100300d10300800d10486040c00318070080160040903400001ca1b402c012000400380e40f2484c0c5501d220300e90071000800450004a07801ca00c0c00e104882e0400310714040301341507580d81d030000d100030028042d512044500b90819001a4120f80c07150050703400400d0107204010410800e80120507100c0400d1000801c00c41580d0700030002c11300010913203420f02c4414000204204031a016403c0f20540001e410420036070000d180c031001c0d040484000494018041e1039070b07a0740c4060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 327697841 1106 327696735 327696751
    0x3140a300309120e0406081002030907050a1503090f08042727110910060201050106021b0105030703090501060b070311030403020901030b0403050408011a041a030303 73
    0x70b1042c000701c50391001203024451070381c01d0100c0300c00203101d0501e03800503681d20000c16148000c124207030303281094400c003580d28079101801d113003010b01030740c0300e540144440c40b0f06001160364942d407072840c5d41c4186070006080704103003020440e40c489103070041d1240c08000303000300d10780e002007194001422044100b010142d1500030b01208071404240e82c654a07280080014014290401010384e103640a00420882500400c0c00075680340002d0342d5542007907032000310421035190203024003030060159001404c4d142a51458501c0c40c0d580c1c92050b541003020000010790284d0003644407140054219000f000f0132500d40004c0e0140d503102400507004618000c4120401c41e42c00012030302030f241d010708500c1d0140d00c0c503070f1000c1c11140080e0085090000502c00460103507009d104402e10b22451000d42c075125100c840c207010458004004c0c13120700505600580d0803a89001040f40d81000705 = true := by decide +kernel

theorem cover : BRFrame.Cov 327517985 327697841 := by
  have h0 := BRFrame.cov_init 327517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 327517985 ≤ n) (h2 : n < 327697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
