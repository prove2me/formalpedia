-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2397
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:51.872243+00:00
-- url     : https://prove2.me/submissions/6da9b8ff-5912-4315-9beb-531de1fd0529

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 430935251 ≤ n < 431115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 430936501 1250 430935251 430935289
    0x6080105071b08030c1306020a0b06040b100f1404030f02030d0801080d05091c0312050132060d051003030201060801060506031522060e010506070506040305071a070c11030606 77
    0x456154902d64003115600003102c4007004006647e0040030f074072a03e000d01d0036140c5198100c002005c50503c1d0240c1200c410001f4401e0007007240d1800107a030800c40c05d0349184100a80201c00700b18500c1060010300103140904140241421948101843c00d4040700c0c5400400150030010040d100000590400003421402d02d680c581402c0c00c08a04c100d54100003d06080361030f209240705154103d40301341002c01c1150020700c2240e8880c1074104814102a04051501500d401003290601810318641e880c1d0718010041881c0c2040c0354440c00a50384196805041600c04040400402d03409105001c01048000001e220640c0f0380350000d4240d010052410325102c581c00e080c0d411558564200d00082900d0084021003d40e0500d80324000b00210300451303028002510001c1950715114003581c109035840002000302e80d80320340d0101c0b03064000ea00101c0350082036034080e12491441c0300f10300d44541400d582d100040c0604e4204010000110070900d8000c2c2c00100c1030285545500c8040350404043c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 430937751 1250 430936501 430936507
    0xf010209091b07080703050306011d0105040519051905090907030201020c151b1f02041404021b0d020616030504020a03061d031b0f19060504170d06080105071b08 71
    0xaa0b040d04103104407180103110620018504c1d04054119015502860080e80d0359a01008e90400c01d00482c2c4100494a000c150180020070152900c40c1600030b00d10246035031034264943d15804252000c1039210100c020b400314400c28072150030000340780d60f403102d942030003450b0b520f1460700042d444076000c0c0000c2d4054240603030400c00c60081e91085070140d011030504204e21000009160f03032103202a4619040015000010980f02c03034090080d6401d80d442071851034003600c10002044002c0d403040c42c44650b0b00c400464002d17000759040c054107001102e1a0090711083c0b33000c10b001106d95444800790001c0c90714001c107001c05600d40780c25000980741e0000d0300048510301f91003287d12131868a0b20160799440300107203000005403145d0031001c007400080c1c126405020119420394841e4440e88400c0d580070301450240c0042106034005c1a0841c0c02103c8507607680e03082d03800c03c50295000980400019460300c804001801091060b568480b90030720300400c00164000b69034411170203500300908014004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 430939001 1250 430937751 430937791
    0x903151902161505040b09030705031803150a140a090b07030b03010f2d0e0303150f04020f07150b10030506030f07080f07062a06060513020c0f01020909 67
    0x2842d82c400381c064100d00141a09024405404050501120203d65102c056000b02e036606c9070020650702001d81c40b03800b46003007000103400215503056040d04107905100310050702d20384512040c851801752140c40e6000c40c0620030006450340005000d0243c0307441c1454046002d001c075014950301d5800c980d140ca8013040e414100780000c0d001d0280b00369000360b160314104245505400e443c0300307404c804001110316203410b00d150000c0000c40e11141c4420070942c00402c001034841c41c0307102c0d909040c560010010b02c0c02c414000007240413600304c91410090010000f0380306050000b401003000d58102ca030f0400740325100c07d40012501003052030034035000b8140c030380e40451810340d420320020207480b0b810000c0300d19442ea504e031101d0f95a502a50328452a0040190218445100c0c00510601c0b8580950001d149641441243c41d900862481940c1c026030382c0002050aa880160014030744d5852900941c44840b044240b5090820b4150030107440c0e03104102c0200c154a48195040e801140110007482c0c041d08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 430940251 1250 430939001 430939027
    0x160b0a210b01080f0106020703260a0c050f060601021002070203030d050a0504021f140a03240f050a050a0909021c0b01140f090406050603030405150903151902 70
    0xe120300344608801140c54000c601055100c0c1007032000999440c1040e031519116024038100c02e014100058000d8001400811411928660f10250baa102c00542d099556048444d80d004802500000784810700c03074100303111040080d4118502c4a034082c081600340000043d50703440045081c00c40316900031401105565052047d65106c18010b00148140d00c1c1070107a0303000808040314228803545d449090915100e01220035458050415102c04c030601000846400868202180da502050340381c01418041024174110682a0786010718803041250502d00650f4490b040f40e0001070141214090402959441003181421500d6a00c40003072903919500101380584034951501e00482e50a0010000700200911507a0484402c3c08104100d400400d040024202420480301d91000c4000702150102d40d195104541205000b000c0b0b902d0070340c2d2680410070903201594440014200498800c55a041c11f105e40741c2d40ea4844d01e0b10301b5031480c00084000c0040b165441d0000c00650100d2440032141d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 430941501 1250 430940251 430940267
    0x1509090f01050a02090114040303020309130b19150509030619060e04030c0b01060507080a11072706120201050f07170d200a0903030c0c0909050303090c03160b0a 71
    0x3600d0002840385251880c0300c44069888288464000354a140d152495084003005070350941c1c1d4036901951400c2665801c00456820748480000103a596101c06a0b9a42d201200d250618004501c0030803094a413580c0c0c45401c941702c00100041c44010007416001d0303640458032030340c02000038808240003440c1c000315400030042600020070180795103040c00705160304031a01d8064a4840c040c510900ea0725440215424014000e00410b485030502081c0c91460084610360b011b009001c0448804564a440031040d600e05645003521941641300302d00000400d90181501800e428480010404441e60000f080c601c42c1c0074032500440400724800081103440700d01e06005c02d0b854001182c85500c462940c80c014000c21038400b9180703c80002c407611000040c0180d42811020344c4404880c80d1558805403903401c2500b42c22070f004c0762a44030116200249104441100340030784000c6459107401c0f40600e150141154049110758405103c0350070f80c403a032182040076115001b5641d52964401c400a41c0c1e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 430942751 1250 430941501 430941523
    0x30b10090e1009060e0415020a0e062101090b12010b0108040201052b0606020f0a08180303040810150f0e010603020f0d0e03032e03030e3f06150909 65
    0xa4100400085c5070611801090f02643c020f00c585c10300403400c0e103806800c071321500c0124408114249410f4160f8034241018188d40c0785405603900560b041440209410712090700a040030301d545035020420350800d450000c00104050000300001080a000a003e401e00184028100000066052003200040100500201000800050f84105005420050003041c015000144520000740f011880002202482590070020032494444181040204003094010060301032008100010306001e0402c509003c080c8035400000e0038030401c0300054141c000581c40360103240708903039051103001d5540d106141102e01c1070900613520303040e0701d5403503906026504030a4595440c02e0f0045074202e201200952180442d110400c0892003020800030384d000e10041d0303801c0d451044001c14000640a08580700b00300000402403840d55119003044078111a006045841100381003d43c0c401d021000103a1010320368103403002d40282c1c9401d00761417070300c0d200e0212910710510010b008680e640302e0a10202d1040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 430944001 1250 430942751 430942769
    0x60c16030203070f05030307030e0312060114040302090a02041706071704020406120609030219050a0206090109120804060305060d030c02100504090207051b06041d0406180303050601030b10090e10 86
    0x800003500b08292171f81c10865100d07010902b4207452914580001c811180d280180714510003842d1111801154030003408690361100040c10440400035954501015214540180300940c1c0c0c4d0f400c040000d8540d02d0114101d11180d840078060140103038210240c22040d045251442060b56a2030000034042d003040e902c020b400b0301b1076200440c24400182c1000d282c05029400f2107074489030721641c00c2c3c0401c110713a00242c8180c206403090001460301000404051005240c1600c0598940c4c421450320b01c44618100c0b58144005420400b494040c040c1980c803140c00c84440c00c80100380e40b4080c241c10919040244038070503510852184038040c2090320701900b07a201085407514402e2400643e40d400804048000341d00310140c070440c9180c400211800e450048101c400007210480080b80b280b100904103c8000e52546080b40c0c1d40f803004002e42c442e40c0e01950303001c07607141004400541140e149404050003422a2174502c0c04040e0000340ca01c5c00c03901030b150240703116030718003c0d0110f101c0b016400030102e0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 430945251 1250 430944001 430944023
    0x920121f0905070f08070509010c050c09070f0f0302091f0c080d0c0215162d0512180c0d0501110309071707150e010509040606030501090e060c1603020307 68
    0x8110301980564071440582d15031301803002c2d20034000d403000c0c0c1c0c0403100301c00080c00400c040307400341d4801c0e07468803003c9105104607440c0508140c0090340c0d07400205d03030080010381c2140c851a056540061444001081401c08514180341000800c0d003064a12003007604c0720816000b0500c0c400e2245401c074102c203802420151b101c00b848012035024101d102c84a40c0144643d403140d10b203c01d4840340050240d080661403500740c4010045c16214200a910100508035003102800150b000202441000c00034a03070f6415950006214078120312000036041111899084500842c0c4940c00184c0300841c0e0b004940007188646a407a016024060103400c1c0e07580c1e00008810302454010015071081511181d20142d0b03104002c079052507981c0c0c4102c1c40380050395502c80983d03450145c0200e00c0d85000041c10714045103805101004078064400c00e5020b40c1c00070b41e441c401001143c0d0b55102c0c4041c2d8a01d0007000d48200e040c900780207070b8103004100880607091604402c100c1014001c0040b600234a911084480d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 430946501 1250 430945251 430945259
    0x12050622030c020f03072723060d050a03030c030501090216061806150303030509150f15181902040f030206090a0e0a020a0e010c1a0402121002040920121f 68
    0x4810300100d0491b0700c00c010682e44e0381f0700c582d60b0150403a8080110080010465401142802180d000d0451a000031003039046030040f510500c400c84006000717490102e00503d10b50402400c44105a0066409a20500050326100780140b00d000650740c002c540440d04040009252100400100c001030580d80f9000c00070006031101c082c0c3c0700031240291000c11a0b9038503800c0c000d88440c0888481d06030703107070200c0c00624007030107000166800c400080000341180e154400403411040d94a00441d00d60040c00c002c010f2003440383d40d890803640120074000c1d030030135160030088117510300d0502000b481480045101034007515408044070050500c2441c0302458104200070200950002d03000d48001140c00d481d000c11940500011541c4540c0603c0c100d04025600030130301c0801c60701510880c1d000401c0e04150070904810441c4005200005030016522031402c00e00c1411a080144e407440100c0c41d040611482c0700b025001d85000c4000080d860f07038260746e80001c507000341450325407480c08400d400c98046 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 430947751 1250 430946501 430946519
    0x30f0e040617011112011707030f0f06060501110a03050d090507120501050f0f01030b090a02060a030c0806041b11010207060f0501050112060f17031312050622030c020f0307 76
    0xd8a845181c0c00204071045502103c1c1020b44503903503000109000042c010403015000c51402010309a51f1401e44a0090716680e921003021480d080a0724024446180042480042e1203100000c0009091418250000c0104186c0f0350042c494058244003001c50003540750070503a006885401c1d805400d44640c45c0d168070384140d10b05115a010340d419031030240010080700e00700c11091f0041861102c1c00403560300e10b0362690318010004004101900800e50380340010380b1518084e00f0044d101e80c4000c6000d1341e43e000010034541c002069544182d05004401400c80d41586003210314040390715051040480303e00215000e4402d2880050480d481c0000781c00102d40310743e01c40c41c16280240d0b1010032100120001da42610102c2c014102000e00000c0204401c40b4501d000b18040030f680b00c2641d0402d0140354461a0681c1c890317200c00c03034100c6041c0308401001001d102e51580040c20303e14041010701c1c4480c014122000205008080c0300390701001c0800c0d9521998040217000c0000c0c21100141d44400e404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 430949001 1250 430947751 430947779
    0xd03020c060d150e0402061e0904140108150c070b04030c08030108100c11120a11010501030f17040602070618031e060b040b030a02090a020f0d020a080f04020d030f0e0406 75
    0x81e07401d460f41a1400310308180745000c01070155400a11440c00c00c04000c519401440c0d903031101090003042000b0051850312103010715401c02800d026100c6c0c10398901140396091005000c410700d680d0f08078200304003400d96400d017a00d02d00354000f0705803036840e070b00ca1a06891701980103001610b100790100000030540f000140c265500303861071106001d00618080251000d500c849200302c5941c016801840485807084040c00c0c0c810180c0c07402c00a82540d410502d400c5070000e0300242c94800880c810078050202d0403103110000340320541c3c1c40b0701e480d1900800a494241c203018460401c100641d0b0b450117104000100c50181d500201c1c1e41452030800002e142c1680e840a204484c01403c1c040c003032010713182903c03400d030400c6400b401a12181105908101251400400344030906900740903042d850140003002e040c851540e8400142d841c0040c00024001d2107000f000a0f013498005000c00005072a0b065403060100d5042c02c00e00c0e01c0070203540c0207591440c20f40001d150014600740303000445081445407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 430950251 1250 430949001 430949021
    0x60414180706170406050a0b0a030605010906050627010507140a1101030510170304120c030b0901060f03020d020406170304030c17030702130e03070f020909010504110d03020c060d 79
    0x3140d80090703031100140d44503020f14182c006030806030000100440c0440d00401e90010044034001031510046c2c0000d582d0300300c070f07070070a691043e903440062204003814440c400180034201c4415081803034101d084a0802410b54046c88018a5580100c0007640598150340081c0d901500c0c1010b0414206003143d652802e40744192990304540c0c1c01008107501a00c1498020390000e50003503031035402d0120150325190040034856403031004120000b4045001a16001958030440e020b002e201d00c5c6007800c40d01100302030300c008441e9150003000c0103401c03103000e0300c0401c07031758180e401c210359050900001340200400d601c040250b0408114101702d0070000301c0200180d0b8450040c150301e4035150100060a00e00042c000181903000304984400340c50075003507200b00000031107400b04a0200ca4448542103800050040750a2030a141400e000c520f0070880080c1c4c00310300d1000130030035890603407180881c200741c44c24100c5c001c6c50080e42100c2030600c280520002d0310700143c0710aa032009032440e203000407d0b801c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 430951501 1250 430950251 430950253
    0xd051602090a05150d260403050102190f020c090a1a100305070f02151b13060e12151b070506091617070303050a050d1521030c0b06041418 61
    0x13041118a4246507649049400001050b00c407205803042180420420b001941c9001c800d00000000801c02d0004007010007018541c66076694103250040c007100781010010b8103540000260356419203980c007485a20403003aa1f8042000503030552403a8108006801e0b05400c0240c0c02803901495030140c120342d0048805507141032400c114504200d8481c0c003070b00038101102030b180c40400d11000401004500002e084101d481c03820395211490b50454215600000c04035100f0034481490f4a0810580c0750384408000250540c0e1402403e0a10032001c000c0007501e28002c0f03a1664182d590300d41e015943c200350311500322001d0381868048103a81e1060f100300ca40d41001c00450224003001c0310400c00c541004000b009200c994150b9606a0702c6420800b0901c2c100241800611148017042c000c851181283c0300894080c1d50826038104e440340c000104940e0b10600d10040b03100000d40c424034070081c0640040341d116050300c1c7c54ac00500a130118031a0412050340c0c0505004e94200210344291044c1d078048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 430952751 1250 430951501 430951531
    0x2907080a02060603060a090503030c0d0231090203090c12030408010c1709030702030318030109061b11070503032502030601061d0a180c0306030b1815090d051602090a05 74
    0x98102650b1f07011000405907001070001c00c00316101040130703143c011910f078809400c00745c00a00d40c4c1700c49800e5141320180d110b01021288111040301c2c01500c00b52002c01800c4d403070b501e02803400725a202200b056160043c075a900c462142c0540900546001d8040301009004112144c5001412100d41621013801c1e29020f06c0402c403c060004116030419034003801035400d105941c1c00c90b401914400da5000e8155480382c1400d40011701c030f8401c0d0b610f98010000040310303d06840034010b21100c0c200c40040c03001c0d4043ca01c20300065070300105440641c1c0807a101080401c07110785050003544001c07135009416110b10000854410b4001c4400280c1e41c1d040c11401c0080001c0b8810840d0b600590f100b46007500d0b10050080d000bc4082d40c0000c081c40507941008940300350780740ea80c040040c00c11110842d03003107000001042035003801d2042501d80720644120901504020364501d0b11451441c016005002002510340038072010035400e100b01d150014520042458a0315060018010441700300e88581814 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 430954001 1250 430952751 430952761
    0xa0e1b0d020a11030415050703121b080f010303090b0a030e030a020d0212030402011718070602011a01090f06111905011b0315090e0106170a0308102907080a0206060306 74
    0x11745040b0b41c2e6201501e2642e40c100741d03094409500c45c03d0146d0030080b01c4002c00c592191540110800d00b0006021099022011400203254810203000500c0c0100300e003004201281d0701080800c00d0780e079a42d401940e50f02c2641004e034014600030901c01094007012a001e444250041480b0320501040c0e02500d2480c82d604240d2501c80c0302c200c50081c0401c803c0c118072814541651521940400391030314851040d00f11022180c1744ca50306601050060303464541809111219440103810b004080c24828880360401d0b803111000401406124100010740e07004108800041105d0044a01080e080c1c0d040c003111410218083c0041094810240300c0402c210038805100b44505152201d54200300c80780030381800b8054000c5c15100907a1303001c0c1e640324500030400d00d009503007003080904210001e1840c203890b440c018003442d10041000d600c1c4522900204000500421810782c403042d480d22400f820102d0360b00008184c01086000b9101490116047c072110350005001802040304604580541d41c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 430955251 1250 430954001 430954003
    0x601111209040f15211b050f060301270e160512070e04060903030213120b0f01121103030c01110304021206090a0f02012a140303090703060203130b04050a0c0909020a0e1b0d020a11 79
    0x82071280b906428014103100c00100400000d900030951600003705822920421040ca0000000148204450003400c20015464480c0004045450315409451403501d010544284154000c2020b401644c481c03418004141c0301c3c0c4e040302d43e0925450b000191668070303159503106107408918101c6400000c2004100c0c078100c5c0d041c001d4120f50402c3e0701c0b103400f543c1d1640c4a007207842c11500016058031080c022844004428081c24010141c04404241c4925140c01000301d14803c070310400045400940a1050040000c2921081a604104880c4140c10b8500c0100c915209044541c030008402c9490500001e0040009915040c055418031006440e12486245c0780d00c400c1e155000140d1101008200169568000d107910040e8070b0502e0b800345420b600c03440c9031801d0440d400c1742e16812659070fa03010030403100110001340c5207118082040342079070350104040d610b1501503c01544903503400580354840600100800020030800243c1390300c2c0d00386c4200040c0d0420301c00384d804982d140001c2281013070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 430956501 1250 430955251 430955257
    0xa06050c0610030b07050a030608031b1603030f050f09060301090525081b0f0d0606021b0d150b0d050d02071403070e0601111209040f15211b050f06 65
    0xf41000300da031031303d0302d074040c0c1030344c20b1350002003d002810b44412000922000074400340181c0308030304640a0700c0400b50450300c0d041c01400203005040f031101400500c0403a600031906802d40c146400c1c0b10341c0e180d81804020200b8040c080c4010b502031000800424441c4080c2c0100d40a88101c40710780c000041c000b140341842c60482c0c1c203008000ba4520340041c41b0084d41c0802c42c540031040175a42890003580c603151b0324590740f08206403140943c8643c000c00910b13a04000d880342c286502d043c0303004080101c0002172442c544c00b40e07015061009000cbc0c080e00d000c10f542d0102056080080041030250350616045445250700d03211100035001c0c80c4000624010350b80c80c103990f2400d000700a8240c0031300308110a1740c100f001409841c108a02e14801c0450110100308075940e080040030700540f031319082c500700015036950405003071080b401d0a21403044032605c07002030750983d0900c0b21400603d03031441800315008070746020083c02003030307010280c000e82200858191080d40c0c0240c42c1100c00b45030003010300403a44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 430957751 1250 430956501 430956503
    0x604050a030e040c0c03030b0604030c260718110f0310080c0d1509060b03030f131a070f0305091801030605060315010314070e010b09010810120615050a06050c061003 73
    0x11780b009501d400020b02c640c3c4051002e220050955003040e449440385564217007280c020100c42d8800d10503480904042045840c0c900000382c0003456610705026600d0b5007000c61400d0310100c1c0d42c0320400c540600c030404e000e90f04040030039000940c49e86040755200301040010310602c0542e0250901051880c05e0000d131080b90382c3d8002041540050703510301d840b0010101c4e100c042c0c0d013540d601c0d256650956006e10081c0500310304290541d49418241c02d28483e035104580c00940310b00901c0c05100011282e00084d1525240c00c100c03002201d40d00c5040580301c91252154480e400308500000c1e506943c040c1072400e060700c0c02100c0412941e030b2514181030769180e607440498101d10307004004000164103405d5680324202c1003019500130560b46c600181b00d9400070381120b038484401059000307041d40c0c440d0150742c0c003503c1c41d810a0740c030790700e480f080d000342540c02540504000c0c0c46002102e900113040f00f405c2c0013404003814003005280d84900c014203a030002040410980581004100e401402120311000c0c1c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 430959001 1250 430957751 430957757
    0x180f0b0f0a1a0c010203040b091912080717240d1e1a13060b311d0609070611070e150a080d12060f06200604050a030e040c 54
    0x50800d440c40600e150251069034290b64100b2410018203030a002560080344103003009180b81c01c111004c0c074206039501b0044200904090300c0c1601040000c501c0200b5001541040c103030036280c09004461501c984110702055005810030712407886c0180c04071203030079101c07220948082445081004150682d01c413003d00000c10604007209403403c01601c80e605580b18411650240300c080f840d10a84007021100411441c94a0f145102071014a00441c40e5801c0300301c4440307c40c921040d40d450004c1042162104103520400c01071001174406500c1400c0c0035501e2040342038540d109411039541c1d03240c02c41d141041402118130010381e0314058588030a80360b4020000c2e041d11800d11007110081c0720020f1041c840150700d6544d220712500d82c0240c1c000070700310000c0030b4030180c00f1240028041201d0b405030200c04903e8a0410480c9100900a001c2600c1ca24602220101d10742c20481055500b1481c00c0001401500140802c11000290319040c0b60301c03a486414242c1c02c110100002c40c1c0c02e140e000004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 430960251 1250 430959001 430959019
    0xb0910050105060f090a031203060e090c01080403050306030f0f1c02160608070302090910090b010e062d0a0201050604051501020a0308060a0906060804050c06070f0b070306180f0b0f 80
    0x100c00100d130240c4000d100141c018070030103a0b00c2d20303403200b190007501d01c40010079581c1e01c0a0242c0303034002071216480202000200a02c00000000800303600c001480034080003404000310f0b020f55418804d09002c0380c416001c0300c0c8000401403005445031081e2460703500000d16819480440ca0021521070345400c00b0001c11000d1614281040d144050000c165504141c0e0800070b140e8a42c0d01c06804900a0300d0341e969070804641822106402c0f61741d4400c0150621040c900059110b540b90300444480e0700c0160540040c0001203003c8201e001002c0c1d82d9000100381c04a101403035194158001845800c08076014421621030341c03501e280d503850b01c11080340181c000f444040003003402401a1500b2201c003800c00740b02d6980e170b210754104441c015006000000e005805110130b0040402c13606805600880b080380c9004255550301252007010100100b821019000080c5a18065480003004220303c7c0d0905400b2071480120300001c2c40c2c4050844909407500181e1013803424050403940b083d0350007034040301e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 430961501 1250 430960251 430960267
    0x30e030d02011104061416030c05060c031311030c030604080a030c050403020105040905070e060a0207031704080a12050706050a050105011806120f0207060e2b02030412110901030b091005010506 85
    0x1c410400106d055070034039080082c04415040140740d1041309001c2e0b41ca403641e9401c9407400a0402c6005880306184100030700501c146410740460005a1540c00481c0c0303101d00e0f03040380210f8200781120304480c2d03040c081e140c100414007950742c00400c60080a6901000824035540301928580985d000280c0007a00c184418400c60310706510494114200b41060707a4203c0b42400041c00ca640005440b80068011103000c004205440c103101442c504800202e0382410306124a25a84407800003020344a035400301541505117001c0c01c110743c080d60300040140214a00241c41c14040c1c0000e12859001428424651740320840b85070b035030000e41d1000c3d40c90054445411414601400440d010f080f0000c0d42005100d001664610070a40c2200c180f60107840038038910340900704482c0800d083c500351104600307000e0300e20981c04001c40c1c0980701e40d608900b004035110704141d00c1190750204c1d485d40000045001100740410308250510444206c0c0c11159000382048480c025200e00388035840d0070103000d2003111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 430962751 1250 430961501 430961507
    0x206040809011106091b040504080f0f0f0c030a0905063108010501031101090f06020c0415050402030a0e060a1515020307150b01120605060a0e031603030e030d0201110406 75
    0xc030075003005141c01800600c860540c0f0b07003010b0050310007003603540c40a007a400b1aa0400c00c007510095804880800242c6440c0d01c48803031500c18032a00e02c40201d0300240d90a2840140816a1240c1d15921543c5485005151000d0b41d40c2e4801d00300140851044030700020703103140c0041161010422101d2816241640d07605c84d290070007088c2550200c0c0340c60042c0114018a003442014001c0d80140e2650300c0c24222580007501c03003000c5412806d06091140707024010a500010000740c0311000780c80c0000c403882d10140c207900308502c580090350707c10b00000601c00e0003507031a0400c08081030120140d81746900c5001c204030803200841581e906800c5190001c018009899242001f401c07200c0c015a1314061850360703801e011b680142183c000c0942c2d900500d42c0556407080702d54513480300040040000b075003810005841030160308400380c10444140d80400198505103c40c1c1c51900c592170259450300d860b0725025048200f0220303100e00a1040b8940303104c0080c4140034070220f002c3e052980780d241c02d00b481011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 430964001 1250 430962751 430962757
    0x2d1f1406040606121104090908031609030222061a09040f060f050121020a0906080610080105060a12020c070e1b031807030f1406070f020715090e130b010b03040302060408 75
    0xb82510360030306c00011402000d000702103116108015040d83d0389442c00801c403540c03001e40303150310800588100c24030040c0c85001c020f2a07200d6550101100303001c0c0442c410006800c058010034006442500000701c600f550501400410404690a000580381070b441c100c100c54040c4192490100d6401040115501982000303c41c0311480c1940e40c1010341c3c130150403041c3d07032144c030081d070015290030f0702001115800314109400c04c804540740c0702e46038130080c0300400d241c806010341d0b8452480000c0d1f0f0700e00c042c0104040000c0c0590080c0c15901c6408218816454902d1485501080004800041d0001c01900f0b001c0c0c4101040d0030314241140c807046002c1c202280702a001194510035040302201152084506410a9100b40c0e8512502075608140d40e00b0044040c14401c01d0040411300301141e00d402280c114161141e03058070340b01c40803c0000440360005990305c070800d807103109818010035500881c41044064007030303114200c0740d9903910002e000f28841191f000d001600100007142c0042c1c244030003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 430965251 1250 430964001 430964021
    0x11070302150d050708190f0225200102060a0c050c0703120e0d05030f090a351902010e01020709021602040c020f060c031305010518010e2d1f140604060612 68
    0x41c14100304990246279682004102d0a29034281210101001b1403641103151030f5000700f00d400104180c00c00082d42ea500007134411484161a0203011000d18440c5041d1090124120f084803c13003581da0500f5400590600c0503074001038021a40c5032440c0c02e04003502c101b03c9511031700940c82c04040d11044a91a0802448207501c00307507001c0000307403042d400d200301100c000414040c60a000720750344206903211148213801d4982d40061031101641d403403810b0070403100340d028288034848044910040341002d1941e08656200c600c003056410001c6250181c03280024429281005621401102660703528000c6481c08003a80c064000612407900d080091900184680030b44040550180e41380390035103004a54042e0400070703107013400c80c010100340640510602900050102940000244004002e0100c0d0030040081e454688131009001004210324004403001d10010424486c040307940602a44101c0c0b100415080c000700341d0300d203400d201d02000c1b00e0894442d8024000490b0302040a411400c00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 430966501 1250 430965251 430965281
    0x2160303020a14160b09040b12030319020903160302130608070b0f040b120a0605040204080c0103090c0801111308010626070302130905070902071211070302150d05070819 75
    0x3014040480c4d801401801900088405580ba4100a4240003c030b0b6400c103259441186100512807203505c0200407260009074002005c035186451110841c081c0c0305007003410b0340500c26541c080d00c1a148124a03042901e00c00c80e442c40520300c6d8820003400342c0c0e002d030003a51031a8215640c200500e03005800141040c00260a58900342a030352310380b4041c3c40c2c02980107054003407001410060b80400b90b11400c006001c00320750440c10b09003800c010642e00ca03009030849052550310f540407418040550f4400e0018941c3d0402031041c03101030aaa9410f5030006030b0f007403038243c482e200c0c0861405010301818081e0307038042c03419403084e0128242c42901c040e064203c0380d0460084150101c056100c20890300c103442c0560801103200c41e41450901e2506046138050306059106010140c005030f1941d4004032072026915001c89a0452449842d0400510754030095010310f580030795906403c4400b0142483c0300701e0034400c001c55a01c1850a07260002c0440b45580007001c840b1681c045ea88a69005600e0309103601 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 430967751 1250 430966501 430966513
    0x5090912070b060f190909020111010e150c09030d050d090b07020c011808060103020f0a0f061d120705060c01020405060d0f0507140304060504080f0703030c02160303020a14 76
    0x662000455803090710705aa0200c910410000c2c14101002c00c100ca0300010381c1d5200c03481034107820030310030301e9414003804841580341c055010039607101d10504034506120000030407030343d01214a416515503242c0c240a040c680210300084417680d0b10410b960088401402a003c0881040411600c030392003081c450601a40c0c400d2024080b0f4080c8111920410b4242c0040c003040c0300201c000340c05103000d125100b44403e80782d0020b209172a80400c1032070460f54181e0716200464400400101c01a0310b9070815034502c4114440054480d0f4004080c0302010041c80300c0fa449094030005100c02420420040749441d44031403403c10031030034401b0080845030200e40005007070a0b241c00000343c0c282c0c00404c20512064859480341c2c100161403081d2604120030341081404800031741c1c11028603000080c00a4100d0b0340da28006000d0000748001c0301c0304203000d644a941c1e5a00c407454060300404201e050100180715103e80910380504010014007600d400d0b800401d60b1035055990f94114a080a04d46030042c0209 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 430969001 1250 430967751 430967773
    0x70315090812011809170306010519020d030f0507051b16060c05120313030c1109011d100503030909061f23211b0f0c011a060301050909 60
    0x12001030a0070002c0021850042d5251850304e6450f9600c0c0c142c83c0350b8061402e1254000222100d140242c03080e0b21200540d101d43e54100140d4160048200e10261f414042c14021700d025030102d11111b05201a44003003018031004584001201c0b0200c6840c0003140080210040112060480f01000d91031041216020f0f1100c032541c3c40c14841075400000810054a0f240080180911200180d010007045003411807a088a4228501098030750140c01d20640c0000d8800344000000b04e802e004d20081c01080781569a411409132400f4024641c0f60742011540c089112080c0214282003110001001182402d90800070482400400b501e959488035000107191034240382d0841d5005091007503200d101e00c1624000300c1030108100140000e2500104201044074598601040301071003001242e140c41590351100705071461141100310f084030780c002040842019161400824028210300000d008801520040508514859141c25480300d014001441503040441609510143e801c08503600c4000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 430970251 1250 430969001 430969013
    0xf0c060b060a050c1e252103030e0703020901210b0103030c0212120d020319051f080a0b0a0209281502060609070f020102130f0f0e010807031509 64
    0x84940103034040b43c008502000101018082c600c40c40d85501078150140c40ea4040a61b00d5030729100c400030084000000000307072003103c45501e80c060301420064020000340742020b01091986901d00701c0000781045980d07200098003041d0a0300316503014010354034a0b42041d40351402d2600140100d075040c16000361030400f15200788803060085000e41c071103040948041c0140102040c400d4840289580000c2c04400c00800a02c01c42c1d8000c3d11503d401601c0740c42c1e1100c0e00c035030f034900c0384004a000e030b04000c14461000300040300070303048a0500d200c0601041e51601c0c0143c60704089000a0840c1c0c40031800a800850190028200c0000080005076003060306010b00c0c40c00d5494601c40e08031491450001d00100d0f0382c0383e152841c031500e1400100010b251030030000b40202401480c05041010600501c1c074100e0007501514414040c1642d2003240a817079813105044d400c07075813041d4000189d04d9540003603408441d54a00c8e068034804400740c8002403c0d611500c0c02490300d6610030303200b16a52500b203804140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 430971501 1250 430970251 430970257
    0xb0a02061603091a04170f031605040306140703060f08060c0906130e090105070e0904030e0a0b0d050f010603020405060d0c051e091e0f0d02031504300f0c060b06 71
    0x2035a0f61003070030300c1e00b81401e002403030399490f918a58204004007c40b030300b44c01c41c034410f484e406014000c060900039800c000417031740d80c0156400140107070f04041c0d1000500494041c00c902c2040541d4042040560b00c044030b0a540d44548502050781d0424404181a811810000c010f401c0300038015616000f00c1152881205509602c184c10700c492610a000891030280240c42e0000058600889003501030f10024035002006080141070105551083c9c083ea128406c400c0010110003038000c0e20364120b007038502d0103414100d40015032089a00000306070a4083e01c02e8900b59000541814103003001c0c03603092001015490200070a200e001e0004078040e62401d07001d940e0035048244001d850b51220024013a00045010900e000d26440c00c2c403510302c640340d0810340344400604895102030b80c1100d001082c2413a0200440303042c050510002c02090001c001c0150840300c10f2440c1040342442c224290090f000f00d02105800080c41c20300e0802c1806d4441c0007042c0500b801040b00080e500c6880000808a43c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 430972751 1250 430971501 430971533
    0x3010f0b070807050f0d030f05061012060e070e09010806090606060f0f040b04081c121a030307050c090916140301180b070e090907060f1404060c0c0b0a0206160309 72
    0xc0e0091b00890b0840c2c3e41030199500050f03424030140045d0a05200043c0300d5441d80e05013070104034507031125209aa00e00d420007001040c1669250b592400d06581c001c00715402c2e694103074001c41c2c18900005c0e0542e00083c425124074500340183c1542c1d1110b604100d140c0d0b0200c64144510b8506101000000300b200c0b00800082180c0c44001c3e83d21460509080c1c14034031000010f40c1d0162640005c00c801a410030300300150f05500900c00142903240104841442c0d0b00408540c1d050300c40820744100b04a40010f0309907408008903444045130380d40c10b4000f507075047d484980c520b6401c07010108012000c0101d600005a20340240007140b400300001d20034501010f107981c10307604544040f09020a2a030800217a503540202076440402c43e01e002c801c0282c2d25026480f07440200a8442078200c01039100b040220310003050016002d644a07034408000701419225102900c0b0361b182c030603000413000c100d541203900368080358001d043c03d66585004441c601b0345895102d014152103100700c00c0055096503160b060300c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 430974001 1250 430972751 430972753
    0xf100c1407090c030b0102071406041d0603060f070512060114070f0c080a03350108011505011110050403021608031207050a020a0b1506040803030a05090303010f0b070807050f 77
    0x4610b041c180341c0c01ea031600c60424080c1407600300b45002c13590380403603080142c0720b003400030004103001e20000c034881c0d100350391009016101039285d00f00c0751200e04801038080c604c22400c450300c5498032080e0091285058494602081b010032080c54010300714000c00b41d02c0300301410440850f540810003803403558840e4500721051154002c8030700812807000c3c1a0005001854024006082c03955406012101c103849410304010035480000c049169a20000d40c2c215400000a0107559582d020503018040e882c202540f0802142c2021409503c0b8200c642c05500669004152601c244095440101001b83c02a0114043c04150b465000c881900100c01004840b000316960060541801d07240c081c060546000c01030304002d0843c000c0c0c0c4c0050354a4240b500300b440c1d5801c40d12080001e0202000009a036030308114082000124800080b01641c42040003020602c0284c2c2c0c0e503401c0c03030f840c4d1000340180021300c3d01d080e00c240010801e4201030001c161080b40202d2406425858803454400102c003178000b2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 430975251 1250 430974001 430974013
    0x417030705010e0c0a1205012a03060506120402090703110a09060e06130b03090304030f0309081009080d020706020904060f030c06031a010e061603030b0a080c0f100c14 74
    0x100070007441040c800010140c080d00e104038492001641904d00c6104d40b116100036550003500f400340039885090303030410081d510702c2000e2240405985a144c0712041002081c0390040026650812030210340040000407107296580d95150708001d85500c1c094094401c041e5618001d0a81c2580f8030b0003040c82003003170307190b4140f844d290640003000300741d80c009120b0003120148000e401901c15001814165103405959940360358448407140d165029550016111107010080003091541110f180008d0703070307840c405480814031503c038080300791000303084002d11041c010030807011086410390251101038071489016203841101c3d400a41528040d80045500c003041c09000c00c1005100f4003540014000c0e4101417010540002814140c01c02c034030390b241d05100700e04c1c8010100b55202000c56100d40030790440c182c98003a0a00b001002480e0010000740284031444002c1845600001c501d83c1d0a07000403d94041414903d060252482d900d420390000c0c00b64003400000001c4a508402410380011001450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 430976501 1250 430975251 430975253
    0x80702070620150a0f0b0301060e041202150705070b0903031017011103040c08211905040e0a0c030b030708060a110412140c120c010809070801020a11010f0216031404170307 76
    0xc07200c40d240e1b464440d80c0740850801c000c2152200c8141d02c00d41001e0090b8035140210000d03410200401c0380b1151880c10b01c0c0c2000000ca400030040d011141c001e02c1010110795528011941e80e12054629421b0041800700400c400c110040720041c20320b540e0400032808000c0c02c034004005400c00c5e9401ca5040c01050420b0040c04020480400504940320307214800139849481c040e502d1080b01c12904910382450490a107a5018000b210003c2941031102092441c000a8100c024205000070a0000381009a004203915000841d40f0560307c2600251000d91288042c43c4010640000032003540c2c9814440000c0c1070802441d07011841780210b80400b00c425410302100e040c403440700007151103600360b5015000d1200c800107640c00a20740030b0030611515240e003a80c1c036142c4242507008800640c0002802050300e584803859031060382070f83c0c000b4426100c880201c1026030160221500515076004c030084082445481305d9480003182072042ca184c40d44034182480b60000d00c21001809a100142c2d8030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 430977751 1250 430976501 430976531
    0x71b3c03030b1008010b1204050106030b0a020705060105150d150302101101050705030c090f01020f01020c16121e060207050706030c1d030c0607030e1906080702070620150a 76
    0x1003d510701d10b861240c079810210f10520034060102900b43c0c0c0e480210000d030400c01c1c02d40c41000550f80015845615151030b581c0c410195101e4030080320b40b0b00a61000090700d00f080b900590159001d250940e003405c40071303500c1d00b00130852602805140d04411200001586440c6541d1180406544d01d07801c070103808240b00d50951f400500300c802040420010054062940c2080d10014441100d4400320f6901e2000100d1400c052000e03403c1c0e540d40b001600d02848100001c00c405139410701d421900308282c0e10010000310550348200501484001c0d030492556002c004d0550341042d101e158010f0a040c001d0701c0300b628000058000303601080e56001c104000a404c03d641150358803c00300081400c0c041d00012a4a480c015140d1901503840030800320109030140392110801d1034080c108500b04480c400c00341c817000e0803d20502010034042400b25460070700c00300e40b01c8155030381030311410501650f201030481e000c0c20000100d5002e00420784000001d0511070302090046a541001141c2d030a02c00c8080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 430979001 1250 430977751 430977769
    0x702010201150b0a021c0e040207020613091505031501090b03100608010b0103060902090f011d06130e0612070e1305011401060311070302060c071a040b071b3c03030b 73
    0x16030360500d5446c110554540d0700206e0046940c00545000d03840c1c00b114404900e19001d0b01c490180c900c102100085850440c644c8098451238184418104541d56901810b840d181b4000c441c001c04118070006100810054010082904015044843e090513802c80207044070f03204d411031000c41e51500f015500300e6030705004002c00f030b113030811045140c40c0c000d40c0001d80418504800f1410f104804082c600000d00c980071101031070342c01030211903a8031030141940c44003540a000384800c500350a4049041824400b8090007410550070050210a04005a03200e103a00008c0c441e03110f8200c3d0500020000d8000e0140c40c2c0051104040c0b81202d504000c8042d00b541d0b40b040195000c100d0900c01000425800206240c2068001c0d07402a640c40050070103405d406030709000d513550540e02d08188410407500802c22489050a82d40304c40b510b10a81c4810b1800d14416080601109000400002030341c030783c1038111080030302040344c45c0c205500d601d04161a41c0c000c00e400380c01203075030f41b6031002140c244480d203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 430980251 1250 430979001 430979023
    0x30604081908071e02070b0c06011d0c040306020c100c020105092505010804021c0302030a260403030209030a140c09010b04060c030c0503130314010b030a03140702010201150b0a02 79
    0x84001c0e0383c540240d0041856440041c00074094040490940c2118000d2180a0107401c1c2d92034225030301c040c6c580d40305540b01e900b0303c280501c20840384000d0310100a0620014010110b042106207420702d0754035001c004c1c4d006800320910324041c1e941014004500e034820780040d024035800206040c603002d803409041501400464242c203001900e20000c54140d0030b000f2080e11400d003007040181d200c50021030324451024030801c20704c0040441d81d80034960008054a0700704940e40e03607481d17419031060868030300d0303001403103200c40021585000c030340080d000c3c0d006401e0b2098068200c0703504214907201d050b4261003000300415260807402e24500340f8184508040e001d0005446032504e06031810300b000b0b1602c04407402c0642007207010300d03a103410800103004461400790512680300c0b15584a00303022803074040100b8140d015618000f040c0740542408100d080b4a15090b860322001408981c521640b20340c4400c508078115541d90011283c240c1e00c9800c0720002d4904010400c0d00c540c00707a04040e28290218030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 430981501 1250 430980251 430980257
    0xa0b0402390304090e0a050f01020c0613020307050f281505130b03180d050318010b0307030213060503011803020606150702100e060c0a02011202211003020306040819 73
    0x5880d140000085070115200310b000058180d0540810501b818000302000f070480c050300c0ca607104109015000380c0764282c00c03681682c2d100d817031f51582c1e03410544d281e900094158008040811041c505105584c01c1d01102501005504008180c0d000300b43d4080701c0d03910588c170303c000401d201c1205004e40840550101d030403c030b0b14000000e800d640900e004c034881c4890700c92000000501605038401150502101c60301100c15805c0180b00250581c1c00c1210803448848421070203885140050180008852001d0060040755085400b4808000003c1340300041e03850700d0703441c0000ea40d1024400e6a41042003e000f1550b00001881c00904101c2d01070400c0d446003030700c400d83c5201d5100440440e080070740d0440742100c2c40d007413985054418040c080a01030b401000031a040d40403040c0400c40307485141c403da0340c8558041c08408000c00b01d000d4101514080d2076150560900301d1545242d980e003056441c00004c00a517580e6001030301c3c201040310b00300c0f4200400710305c0c551a261604039002e03a041c180e007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 430982751 1250 430981501 430981597
    0x924061918050d0f080307140301060e0f040c1d03011808040302041107051c0e09040524160309110303130e010b120c130305190b090a11090a0b0402 65
    0x901c4d100740701c07030f0b0300d0758003030104d680000200b62418001c01e001541ca034400d1000503220340c0d4503200a418150a500464024064100191a5441c05100d10030304081252651007281040c50a02c83d04080f0030340000e0b0b0590b60310031030282050050031402d03040a2207561126901c074254070520050341c000080702d1044400c1400900700044002c42c5282c0038a2440070303403240c5810300540803640c242d000d202480c1c0111688007130005108010450761810160340040d00c040c3c001101d903511140c46d08030740003400d2910742c10440501f10720a4005041d10b9024074260004130144200090965200c45292040714801103000c01401c40c48005250041884c0c0e0007071820518070f86044c0d50441001810340c03030303070903000541e007488503271160f40500c06160803200700c0c0c0802c0807002c0b00180002803028241c030381001c020001210801d0028841400720790004003200040f03e280103000e03055201519164165440c1c00300002c1c1c0d91150700c0641219036045140f07580d00c0d40414041d02004d8041c41130445000694 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 430984001 1250 430982751 430982753
    0x190f0c1409030723040c0f020f060114100c08030901020306010906090503070902070623150f0d0f080c06090c04050903120610120e010608010b0924061918050d 70
    0x2041440440d98904a08a0130860080c545242c070402d40c000c1c40d07803007454100c601703d08640c00009460381e150346030200c0d00165480b42c1c003140d540a091040130070102929540c0040742c00e000c1c040381c40c8410303107051040018406a40300680c0307810440d00e103011a036000c01003000d15070b400303001d2000400d22401c000400c1414440840d8842d0201e0041d00f000c6034001850340104041640311801078034400806451040d12510760140f1800e06030740552483c44188068041d40c5050482500d10702c1c0d00a0104c089c003030303850762803408a514602c07041da841403040c0001c0c401c500043c014140724110301d0b0040c01d010500c1c00700704001c6610290060301150310038020724908100c0302e0817003a003041003240e540207411720508080300d103400d24440d28201c0e9410045c4101c1a90815007147c0156910340d002030101ca9070003c144025040125940d800342d591406c0592141054417001c084007250160a6914102049600c0f0309007441d40118000000c909205003203011164103014805042d0446150b080c40441d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 430985251 1250 430984001 430984003
    0x9110a030507090515040e010f05060f06190c050a08130e060904021e0a0b04050901060c020d0305160b0106050a08010801051003140c041112010e100e190f0c140903 72
    0x8036000d0f00c3e007520b5130b03040403070003c1040d40c49000c0d404000420074071414400c0280c00e800707801c006090000c02801d1a010a6041c07425442a44120002905080c105403070a4801e809107100d030064107092041400c0b964010480500129040030301403804075a891464540f60191400c0032782c054003c00030b501e0180b103a5a600d0042058001d074048410f4a040891800450000c1d2180c09000f51300c10035403e00003d4210240e4041d000702c030350403112160280c2e80c40e0300942c2d46600a1380000c1d40302c8098942c0c040000d001d000607140e154103c07203501c070340c9030a195100c8261140a0304944003140c03020401c00c82042d4051022409042018000d1046040090a9650307820460000411241c205420640500c1c4104055103004400810612050b1840c2071600c0d10f5034481840240410005400800c4090062002601800c0b2210f0b040e40c04600e0003058144460f0040c00380e0158003401d401c940225003550140c2000056400c00005510300340404c040c00d042c102d0600030300f20317500c203020040d4903580c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 430986501 1250 430985251 430985263
    0xe100804120306080303090f070504050c120c0d0207060f1b0203160302030903100b1509010e130207170315190e0907120f1a15010e030c0409050109110a0305 69
    0x180c05484900c14607026102900035200e1900214481d2002008201c1c01c2c3d4070026681d07903240403810035100900d031a1010b000689200325102c0389c00400c10400135801c440c81c0309095900440250040f414040e80c003100c1400d99001e090240c50031754544042008164040c490f04c440040d200702c0d861000808100065101d004402075045800d5040c3c5080c030500d80203204480740c0350b00c0101658020603c0c8900e03007001740250f2400c0c038000c1030319646281c0d0301144142214242d0b14140c6030000303000404410480070b600784120007500350307400f8080700000802403104a40200e4102448070740f80e1500144410920300b81e144c1075817182d40b01d04094a020315106800505031041000c02016540e0340c41c00c11880e05520b5803203861a00c110300003180c180700141c190314540d18403075102130b003104d45407208092480c082600e08113021206084000410742c007450240b000c85c800a030a503030a0050041c005022038ad803400055429944458020040100d032403100d903458841120181d09641c10f640359217036644 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 430987751 1250 430986501 430986503
    0xa051b030610210b101a250c0b070b010e060a031e02010c05030c0714151b120c01061511100507050733110f16080f07030e100804 57
    0x80c6401d14000342805030204140f06401100c2100c0d02d01702401c02c03110b012124412000e00e01241000c2c040361a9450045602400314900c500000340c1d00c4000c8080d003503001500407202c01e008031a0000d030842400002c0c1200601800c84030260750300d084488842e000000300713100c2c0f040e66124030900c0060903d684480c041d00380b070607051584841174130041e03404c407c3c0040c0c060705500c400f01b02070400120014000d000d480c0b542202071107016404007800041c02c02654407044072101400348181120808284c4080e00086c4002c44024503085d400c1060143c1c01904000280e9460361003d000e00445441d5040f56441549030042047c8260742000d034442881030b10708400c050311540895962031162094400036904080400c4035098418500e2003002041c402510b80700380f01c3e41082d500e0042900c500d00108003158039540c504003c40303444a5681d8040c451a800c007403405000200426001005006818152560540c0e950742c0703030802524404507580c0302c902c980c10348203004031103d0313010344116045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 430989001 1250 430987751 430987769
    0x21051602070f03140c030a0b0403030c020712020402030907151205060a0608040803091f05071709070b0f0417060f0a0509030901030507020109050f010b13200702030a050a051b030610 80
    0x100500d5603203080188099010b070b1b0600c6413a5400080c4800724090501803482074908210a0003140001d0780c46080502c03820482c5080513030308401508081d001103500014440039503018544803c1150100500c100300e480000d105e8002941c42c00400b44617598109004407140b4040500e88400108002c500600007820034001001090f0f028004000d82150358046502461402844400030001410100d9102000904d52849550181c1c10304030a2401800c0c1d4001800301d080c289070004d030352035008001180d03a424041000051004c656442d10040744e0040c000340a10341010031494002c0b04011340300c00c480d0352518081c0f0023400000021600800c0342820701240c0c0c0e6940d418264014415040050090300403810308082c110f4042d070050900240455010140d204420001c804640801103030041040780700b4015800360b02190007601410340b0060403034820201030340d50b060034510010b03400c89040d4072150030f100540300a48107041001c2000d40003480f00703141c6144221245500c0784142144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 430990251 1250 430989001 430989023
    0x10c0512012c0c0910211503050307060c0e03030f0a0c1514060a06023417060f0c0a0c02010c15020a02031c150e060121051602070f03 59
    0x40d8030b8400c2c501a21540c8242444249854425403010059000c5207446205410007641c18600d41e002c0c0c1e030700b402c071052002d483c8000030103841180002440c0c250b41120114042030400800120100010041948159030205400c100c0400280c41e00c0e04400c0503502c00c1d041404042c8510107114184c0d5000b504624201d4010189030402c4c012210340c250b090426076091680d116080c1c0000c86001d401108140c8034216074a41e6460101c1e191001001e40300c9408a9407800d18052130700609000461030010540024502e40d1000103544514040e160243e081d0811420442404105006568020b0700800c13002e00c1e00c80d05500040c08a82074841c02410b01c50384030702c0392060043c4c2081d08203005801d00c1c0110b645400c144c1010f5620b0700103150450105852900c0901074080301d018080b9a140c0010a00704518201141e8051203000280164100001001d010328000c4500c01c418030340e1404514000381a00f4483c3c0c095030600310701c005040a662003000e04109070f41040341e1200c00c498010108000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 430991501 1250 430990251 430990289
    0x4030503090a0609082a0405090a1518080f0c06070c0c0803030601122a120609020918090313030f0201081308031506040801020c01060e100b030a270803060102010c051201 75
    0x240d6445040031b256005860f0004000c05500c001030803c21143c010a080189d03819070118038800c1c0c400b10403204e51601c1071180c41100041428003c0c203510a0b800307800e1401c00760305c0007181d840c0c400222541d10008180c0d00c0507034140445c095580c4081e00305000513514500d050760028181c5005e049a400d44941d86100341c0c403400564150046180401003800a00c0c0310038907400801c003502860282e0462441d0110008100065100301d400340140601645007440750107811442d181030040205080d40800c1113502c00426102c548440a107101d8084240c4e04c2c091400014040c8800901e490031902880754848046101a4103072607014105102c40380010000e0004922107000c1e83c4e0000b4055800842c00840114040d00428240c5001c5c440103003496a4007504071303021029034400c100a0201c01c00214190038500d03082550040548901e03448800c0580380d00f00003a03484010709860030107011003484810340e428007072070050305002d1170060700309031104425060904040c424030941e469004011a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 430992751 1250 430991501 430991563
    0x2030402101b05070608071107031109061309050d0e03190b150d0602040504052d07090806070906020c01020c090f06040914030304111804060506040608010204030503090a060908 78
    0x414410351203000d403944c0c9643c80303901420800703040d241c00700130500941242c0c0071081c00003140001c5030742018049003801061003d0041c1200301030440c0e0f03004011149000c035884101d0045030010b51042004280019030302030b00038142c24140c062144250849040b00100980c600e88048101d038100740700c440d054882405020300e6108421032141c108a065400b40107001065006d03004886081d00c0a01a5560300398404088070038583d05882d090070380850b0a04400121401141d0003112410213040e0503450700e03809450a14125210301c006030316400e05002c00c0c1c0d4180711030601080d0a00007001402029000217282900041400c071500004000240301d40e55581c0245919507042120100300b034504600040e00c03030303008850580b214036200c51911094205a40d619081f192030f004003075840c3d22240c1d1107034040c10002c1d000590007603c42c080070982d403e003803009100643c42940110780e5600c000c0c0920a0192040d403008040c040708403410071921101054180e0500f22141074481c440624203090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 430994001 1250 430992751 430992797
    0xd0305190c0b010f0605031512010e061f0e0a050601031509090210030b100323010f030c050303030403121d0610030317040305040e0a150303051b06060f270403030506090a0203040210 80
    0x80000d4bc00c141c0011080741c408112a4004e01c2e900350b100100c40700c01e501001010130903210b510f4884807007500152021030360b035010542141d41450080b0b84c844c4004503003800300b200d90304001302c01070b6038455000445c6044c1c007440c41207800e01d08081c4000081c13040012555609081480240340d1107145680f8410040709951844860304c008501441d61956942d52074407010380002c80b9a001d060300041090315001080c1d0f0b1103143d040e6104500d0b8400c881d4184080c0c551480313112000800410b206819500a200d60751085429000c20503500d891400d00a12407100c030f80c1c10f040140440700c103003c0803a5000c4100c4003581c0d511540078820761a5a0348034401402c00b03d40c01d00743c2d001590008000c05a2180c018590b100b03000f03510b1108112104401c54480c034098603061307440341100e106003159040201059000d00059135503c00c1034407c9050743c80c91410112000c60000b59600e080200c00c2c50b0201c0750503044042c0aa0840c250700e03040e4003090382054150000424031140501c100f1031100d00306c0c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 430995251 1250 430994001 430994029
    0xd200301110712080a1104261b0a060c051504150903091404051006080c2208120a0c02011206090e1b01030b030a020d0305190c0b010f06050315 63
    0xa0302c0c1d07120003904020103000c20410f400f0b00080d007100046407081c42a80100da421400f40c0000b03504e41880e00e50f000314201006514044252035000580407002d2040c009080c403441000003d801c83c02301442004503001c0c45800043c180140440e10030040744000910f42410591003403a0500c0e40c41e1800c184010b4014142c455075071909101c3d08104140e8031203c0030b000c5520203c0d1445480360001c0800060b910115030500131025200801c102c000d103d00704030ba40024120010501d0300402c40405003466802c50300c20030030f50145800811003083c0c1000049030341140c0c0f001803810800d1000d4004c24080e4003c0029041018007085549118150b0f4480760041c248000100100210500b040f610350640000000041008074074403800c5502900a41108050040c0036100702c115940c00c06c810100d00e07030030039010004180070445828400103422031380450700d0703102c4450344041490306000c8860141c100310880740400c101001a541c025007500c0e08401d868046240d03441602c8003040c01c1c3d400c4030003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 430996501 1250 430995251 430995281
    0x617090a020a0311040f0212060f1c050a020f090907151b03030903030f020405030304031401020d050403020f06010f0b04031212020409090c05041119170408180d200301 74
    0x10407010a0904c00c07a802c065409001d01d00c0580b5114007207000d42000010181120400110540b0b448003c0c030b001140000c0c8003d003641c140d5503a680f2007000002d0201d0780b9034001010601175182150401024460403520320586242c0501c00c1500c0e14024030800004181843c20303102c0c1030340102e000e6220318800c5200301d64041181d040090141610160a6011900d881d1940719821468003c0324251a00036005503d810310b1035450a0a0040407000c40c0e005546c01d001c85498030851340600e9006070300a034001c000c884035444009080c03100603800300700c0c0f98000e840b0400682e070800b801d84080341d070401d952121103540000141d8920604843e800c850300d200140110300d80d1565030200b141c90b4083c845084031113450710140030890302c440c1c40c8214443c07800d01070190024802c00c45101423404a01d00100040d003040ca015495400680b02181c21007008650300505600311a0035501c144000c54401d0307125012500c0701940000e503810a00003a0300d02e0b81c0c0d1044152002d411a1408200c0c1310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 430997751 1250 430996501 430996519
    0xc08011a19260a20180109081002031f08071202030f060108030a03060602010212150607080a030c08130317100e011502070503030f0921030d060501030b0a0617090a02 73
    0x40300c41225080403603004046900c4c014413407009000c400325001540f500c40c0422841c2032041a6900d280c200c4141003281041001400440da0080610100321180310000000d0b0304e908203c08098641c1d00092192070000c001d40d182040602e40003d03840b0b04440b1b020f80948a241c000e800840c2c201010403890f02071754072540d0000582c140c000001007a412050f035a0402840362916012400e07031245800a504440001c400b00d43c010b00c0c01c0e01c81c0c1c152103100174906442d081040c0d89280c00ea8002040401c00720340c2d5407a507000c206030045000c40d403140c11022010981030701a500034144aa030703186041454440b90000580c1c0305110100c00002e040000c020f00440d40e03590001d500721080d40d1143c0c400500480c00d002995081c00000d4408010b41440000c0c21716641d00103100c007100d8014091448185c51424004040344203000038480e0004941000c203c00e403e05002500355411405058094490008200002588500d600303504406504044a0b0360b100c50030f00342e18100014501940c402e4280c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 430999001 1250 430997751 430997807
    0x90f020708120609011d0a0e0114040b01050a0b0301030b161b08090a08191b0902030a050603010e030903030904091103060c0a09060503040317090106030804090c08011a19 75
    0x11200502c40c0004440000650386ca410740c910410343d60305a12106443c2500103d045d014098106c000c00700c104000015158201c6124a49050400e0310103644080e071180040c00b150810400c5c0e078000c0c059130b01c5010b01d95491070351881c2a80d50b0080c100d0381000f0106000d8a94288160041e0070542d10000441e0181002070403c641180d0021050351f2085e01500c01c006411600072481c0348022035485880c0350082c540751581541d0b070a414408076030765070090f81c02248003035061003d5030049031000e0001902d0301d000414036084841320350220109a0060000c5007090794000100d40100e8015200413030300a40c1380c40c1c048d40080e441d06c100e5605000c0ea108001c4500c00301009010181003035510602c8050791900c09030385520081d10b0140c00a1144c0a9694500c1c0e10031484039003000b200c1000003803281e82c1e51220501d40d00250404d0f403105460b42007009505030702c0a0a1409403410701503915455480101c1c048884c4555241c84022002510401e04500e000d280901010000700d0900c40a508032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 431000251 1250 430999001 430999027
    0x12040303110d021b0601050d0b0a140f09010f050118021c020a050a020601060f09030609050c12010204050f010503130605040c030f030e09070513140d0804121e0804090f020708 77
    0x2501d1544c0400001e01d66001030010009107260482e03202415040107910107407a50010414000c1c00e00b88615107441200789d4800d0400007580c400e00d490720851019003004240d20b420b590258030a4008903003070000602c843e0703800b00c001c45c0016007080001030392008008804040c401940749a0500c20f4408030b1401101e5400000402640d245e590035220960b0300c1c2d600c01da503504080c10030f02c000102824010300009000368008000303140070707000f20780040042c10001901d00c19144400700e40350750082000c01c0700b810402003c803400380b02400c182d07065182103004410248021013000d4881e40d1030700f010a042c85000103900c00510b4000301c04014040090070301420f031041c03c0c03600501a480d60341c0040c40c403500c29025500a00411441038030300b103140081a84210812403c080d44c0007070003c078503200040500703005000400810381c0b5a56068002c0c280760490f000d281c440c0385042030719044030500183d500d400316004d5803440c0e039000588540e07140704a402801580c030300510003000010382c40c2c22101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 431001501 1250 431000251 431000257
    0xe04050105150d050c010c060e1c11010b06030402210d090f1202030a0f170403050709060e06030d08100b04122003100504080d090b0907060c0812040303110d02 70
    0x41005004182d062225041c403040040082d0041d01035080319412500662140241c561000e01030039010408040701400907040800e01411803007500010701300500c10b240c11200203c00801100000c0109200c020046825480300070402882000852090b1101091244020310001109030031500c2e445403125010700784086500501081a54883d8002944500c154100740c040e9405000780448804030341c2d819000e5214010202d4000c4054442c03401319a0f0080c014000550050380140502c500c0c01c0499001c6a066811420f543c21440042041c0c540340092010880d04941c074210f68140d40d50a104e20500b00a50044040c030b1600040c0041c41e64092a207006c01d40340070fa014080c0c01c090351650b00392941070f42c0203403d405800c8890040c000f044c80fa17120030380c014002c207452881c041d5440b502c001202c1d084441102c052801209120200600700118009010241002030940d4941d49400400b07000e000800e40d0b56141207000541098440d400615540910464254840d001c11040304043c1d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 431002751 1250 431001501 431001511
    0x6050c0f06010b070605060d0204021c050a0501060504150201060519062714010c08160b01060806030a11010c06090b0901150b0f0304080c0a050a030809150a05100e04050105 76
    0x88148a4141003440e00400d0a42c101c44481c0c220900c1d11340c455031100090000141590391203021519900c0140e1968001801c0103c1341c54032410380300d151346a1410880d07001901182000b885c0800600c0180c1c3c000b0100c03401c1e01d042d49200f10b14501d10307020403400741c1007a401c69500a92400d0008004068490364002558038075251400c01d0408600141d0101004c03451048080000d0102006030750606503000b00c0304601807400d013070000700d10f442d682ca00f81d21410f4541e04420740c42d01d41c9020310003031500c85405840c40d85440e0b400340c2001c9000a9a4440c1c0000c050404c082c64024520207a000d509000e9600758804818031051102d420114103c00c400c8444425035400d0000761050740c102400c280040d54447c061030380c2081d1306500360000c1034100030804c40b5101ca0030032400e1103038101001080007484c410310040030184124034004060301c1d000780c42181a0752043ca48001c03900006950b03658000c505400000d440c1c2d0f54454900d01d1091107600020001c0030000510044c051306402c1507200d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 431004001 1250 431002751 431002753
    0xd090905090d0917010b030a080304050106080601080607030c0e09071d150706020a031e0605010e040203070507061122090b0307030c0b0d06090c020d020c030106050f0f1906050c 78
    0x80e615240c03542c0d22800000b80e04000203410040c1401441525603c041e000b800701800000e0030504100420700c0d00003002015500303040040100001c01c0404d004000280139400b0160415515000c5041c3d03a448003e8441014140c640c1074a02e05280f080506558886000300118910305040380c0181c108a2107030501004404403100000c190306005040c2c401081440000c90f280c02090b444620081d003010f6246000c241e141c00c0c1c040300d41030300380c401c500302c9035507000d4009076461502002409400b030126a550140d801401005903050300201a80d0040e0341001011603001d03072402d40b2280c03502c150780c0400c1c0070381442d5502c031104210110001003502c507150800c0144e500300904241d40c0c0d010504c002056a07208202c14401c2000140107880740d2121b0000210f50503886051003c1030701c0c600508400141e00101090504507810040075200300c40030b40003003003818100f40100300c03000d0f040c0d80c507580103008089040d10651208031700c20610b54420a02290116100c1070003c00300d0740040704078202 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 431005251 1250 431004001 431004011
    0x2041d0c0f240912160e0106082202030313030b0c09061903020903030d090506060d0b06220501030501060f090516080403020c10031512020f19080d0909 67
    0x6a03042140c96918808002072100c51500211a4034200b00041000c2090740c107281400000c101d9210306243c14844a031020240102d8086a2400492504150300c8090a801540010070085410440aa0b0005140d1000711364160302078600d200e070b250140d44020341520000458007400786480c103a601c2a248182c040c00c0940c1c8550601032803502441d030540798010410000c0305031503a060740084241080a0401505182151340000d046800007140c440015845207101c80800070144241d90b400401190310310034000040d02d031003800d004010000b900903802d1050b0107207400c0d941d4042d96020a0441020300c629130f100c0c078046010f440c2512580820889114020500044600607a44101f101e00180c41d0450302c0c40c1412245400003420a405500540b0342050007511411444d01c405100b5807404259400784ca004040308461640c46640c8560321180c0503001a55021220801c80e18102e421b80f521100e030b40c14510f426035207680000380c01c3c41000c810452058100310104111900308908001d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 431006501 1250 431005251 431005273
    0x206070504090b0612040305033306250302010203040b2d060a05090103060204050405010b0f030604090c1d010e010602010902060306060a030605130e06070302040509040b0c0409020406110c040207080406140702041d 94
    0x200c01e029001c004030000314403100000c2410b103070015246140c011a0083320010f42c1950744140420580d1056006035000001c00051040103420720760040303140d00022a40e204071840301103d1908141803880d44016027408104141c1d20f00c09004050000101280c0c06941d60b0b1910b10300950062007003a0166052900006840a0f000c0645d001381510040e82c1b8550b58515040000401000e0310881d007141d00351801241d20b286401c070f003000c200040c407450b494550400668000300e010507440304046a046c0691400103803900401c0c1e80d00807500742c0d200b035100d007440b0200f9406480315420658001e644080c1003000524581c100d00d0705030800500380d0700c160704c1d03061b800c400b44c1c072a0380102d48c0c0140701c1202060020711141c410302e500c0b20b4250400c0d424242c8501a50050340d2142c0e1015000404821251040c210140b003c42c0c200700c0c04a42c114900f801541e9462030500a43c0f1580050148005420b819910080700315423100b0750040003001040c58844c0128001ca41c1225036400901c117921400f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 431007751 1250 431006501 431006551
    0x40f0e01151b020310020313031e020a030e0f03031201060e060712050319020406260403090506070f06021c050603010507120905030c0d0c0506070206070504090b061204030503 77
    0x1000d4401e030380d40b0075410000003107146415206082e0120b8040c8a85542c40c0484200780c40618061b941d0800d20b187c0344501c40c10010413001501030075810f5640c0c15469040340d940c0008a40310850b5040c140401d0b1040303d440002c1c03881c4202403407135405000000d0355243c100b043c065140d040c0c407141d840d108203400c4064103224032030041e40c1c00104016400302d01c00000ca40035030301640d071080c0089407110f2085007003603800e8280c2c0c1003540020b01007810341e421090001c40c00f106290500007034468000c12446c06840007444090a0300c0381074010340300080d1010a10808145581845400180030340da912900480c2c5104860032100321030445203040c011420a00e03040c040e0501400d030665580a02c210300301c6c2002c0080039007150848151004226851107110184030720004007035a9218003c801013103050584c24640c00402c45011500803a040041c203a0700503050f035040d9225450006013440380c890206a90740f180075000e140f410300e100304000406502100a612403030340c1c0000144034003511002c0e9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 431009001 1250 431007751 431007779
    0x20a15020705191b0b090a0902070506070305060a0306060b0a03060501031e0c121e0c08040f030804080f030f0105030d030207230307020616030810150c0c050303040f0e01 75
    0xc2858203c2c404060b051484083c0500a69009184400114030a250400c400c003400c0da1040c0c020600200c1d050036a480c041314140700429a006095203848004c1d501c0688907140248840c043c90f568901141d05500c61903000f0740910f40c07004c4100140d540751240e40006070080d440d14800682043c40c049100d52090050804440d030700001c695104c0310a0b00c50320041c0810000c0f000c00c020400381c1e06c3e0883ca100703001e10590900044220301d03103108040403460588408034000790500995600b84000903910007a00c0341c0300c6405140200a90b2220724100429102d00c21007242c24000110500c0100103101d03000c20304950040f001c58030402c10b1480194103a00600341d0151919009c840110358041e10f1071100c54036908040c0503685003c58a83c00a001d40c0c0101e0a0051941000d0000008064100007099001016a620b40d403001d468042022100e07101c14001c1c004000d0074880781c0d0104018042c66901038800201625101c54440450700003d100314405c200040100d44000a2003a90140c03035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 431010251 1250 431009001 431009003
    0x510050c1606050a0b040f0f20040918201002120a030b0307050306012304060f1401020106080f03090310020408032a1b0906010833030a03020a150207 66
    0x1841e0440403054480c88001c242c024000110541c54032200c1440381c0d901d202d20784000301d94460006110680c200319a0840d60421003402040f03a503500b80425042d042c4040d28211440c007240801e0f034500603100d40d03010050001c4c00801e121003c2c0300300c2c5c0c400e00d4001c40710801940250781b0703001803080c0c0b0076040f6540e030b03025000030005c00c10412980c00f661f440307a00003686800014007250300859a85001c42e29000007640282a522030200c8400c040800b03040880e0300802c070442d410310040e42004428060601188903003802d8040074142c004240c0d0003034100700000d00024040d17902207481d141c481c64480d07022b5142523102c0d0050340c140c54404412882a02c046d590050011802d201c1d914540d8006010242d0103109121343d040d404c02e1060b030382002040915403520185101c48400101403007040c03500030b450141401030060070094000c040500600d443e0001c21409a030f546c030004001071481c1c4c0c10b80442505030060340e15440501d600001d55601581c402c03920040010140d84c10802240a4014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 431011501 1250 431010251 431010277
    0x10212130f17040f321c020d02060d050108070b391b010f030228050f0a030c030b0f0d020918070b2d0703051321140307150e190510050c 60
    0x14490000891b04146d40415170700c00b80c4002c3d0900110f80000311150402c0702020804c2c3d40b01d03401840400f805000710f070020022041d0140c2040158a00c050303407049002074984101643c042d010380f03903841001c0081890b2014600b034030000e000c40ca0003140c902c0c40840c400c07808a80c0c000b03030303040782c0380d10034030884174203040e400c40e60400010004110594800419514000c000301031224040307040140009028020040e100040d0642806401030151100c3c00b0243d0310510302080c00ca603c0c0d85480e024800510383c119012112a0344040d00341003142c420202d044020301c210f200110302000d050740100700340061a03160302a0b4107141e030780b44040c07070b0b892180191840344203000e1400024011000382c801584860303c142d007160780342d00c00d410001004042040d400d41000c00c00f9418403250544200b01c030050000070f1071900710651a911901c3c0d000111032140c80b42c0d5480002c031200c0707041c0003030301c00d03640d290a83c8140c490943c00d0241d5103001c00306456041c940303050302080d6260350341c0c0d08650340000c4200d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 431012751 1250 431011501 431011519
    0x603021f0212071a0a1e0605010e010309050c040e01180309030c0807150e030712050309090c03100501050f0f1308010e0606090a1a0909010212130f17040f32 69
    0x100d6040b001001e868248001d4840700d2410000001c194150540c42d240c1000047d042d00d04070005254a02c42c10384281454541440000072a0011a80c800000e07030948001c100c40d041600c4803170050041d00070901a00b030700c0621000030958001c0094040700d00030101d07840090f03295403181c1d4a03a03007548183c3c00b100c08403181c0c0d0f1040b24040c0b45440e0f0038040040c00c1e955140e0703941220ba0030104041d90122541d82000511022500d000c540742500043c40c0800315041d4034007100d211038556180d01070103050010120300404ca10798803c1c1190403458102003120b844100d02c03101c00300340700803034002d0f4081542442e01c00700101400082c0300b407080b04000d08010b40c68685a06040c010241c000c0315402031184049003101c0d540710300302007a00580a201c001030303441c003031040c00c8101d10340c0140020303000c2417001c10980d000c40c19060701407100301d400000c9002305001c208482c100600c03070f641c0603403041c00200c100081c50245810040d0f11424000c080060b0600c8900c880c1c1c00e00c51a9a01200d50040c1c0c80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 431014001 1250 431012751 431012783
    0x10608190f060501020d110d0c1b06080405070b070b041118070509030f010504020907140c0a08041406070c0e09010e060901060f0609061e030603021f021207 69
    0x1084159045149400403110200c000003050040e245960180719800380c44910400055904028030565082c05150080090004c000d00c5a120110040396200b08904000c0c008180708011840b035403030480e070320b00c81d0045964510307010b414502c00301e9094405000c3c10000040c0120104d049503045c0e0390107884007000b0fa84954a0700c1003c8072002c682c0d41c00c00c01d074036050030510034034001c0140184e98a0300e40b207443e14090700406103040700b842050001d03a41003100384001038440c8070116410509905081d03000e2030381c5081104c440d0203403a080c00f046100b03199555041c40340490090003645e0070f440d800595050541c05011851003041c80042c5610641c400400202402c408159082030708080013051a14581425a01e092030035985c3d003040e42d6548904002d10612045080010003080c10050700c80d51402401816100034004d01d102280566008001d0702d6120f5400388015542c000c0c00000d00c02010000d490346d904041070107002510030320301c080354000a100142c502c496441882001e110201d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 431015251 1250 431014001 431014007
    0x60c01091703012d030605091608010209090417070f0b0106140306011b151e0f0618051506270a080a020d080f12040302010501090227010c0c0801021b150106 69
    0x8200c840701c6100b44441300032002480c14040c140c00346080340010710b94880702003400800c003000e0358006d20040e881080390040c907440e18001d0310350141d0032071480c50102800c0300d0f40080030700c04d142008283d0f00c00c4180d54410401001700082c181e841c1e44c1d40b0190ba01c1c415900d07140c2144001d40d0090b0104542642060000c0032416001007814030030b00302504404a41e41c04141500c202c81d132000c0f0360300803000c02c0301c403100311500c50100c00703c10383c58050180700d24003040d5458004c0201010403000d5111000500c00040c041034015184102500c0c05035109071030450b40c100c4207030034855100c100d03c107178140603683c2c54900344100507219220054810070810380d007002040c40301900101d0b0000c009102c691490601540a0720088000020a1000b4605882c000342104c005811200300c4030705c144031402081c01e40100801c85a20062005080d1440383c8005940303100305028020044815100c02003080041074004c1c0c4100815404020a09485043c8040cdc41d0301e02d041d825505064107400402407148 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 431016501 1250 431015251 431015309
    0xa140f04080d110408011a0d11190302030d0503061f050405060c07050303031305210f030403030f0f020d0c050301080d031107060612032604110f060c0109170301 71
    0x10040c002000301c6078a0703c0b106160040d500054299544100b022800350304010740841201040f01c04d0b0a81e68200c1d540c440303140c41c16101d46c502981c0c0d04113409a1010b25000441c000d181c0090807903080207000b410003001d581c021a01c0500030800c010f15902020740d00d02d2074090b00c8400c0e440390380c2094202414001c0d940c21540c01180b0364880d40800040540302840214001c00c2c0400d032002c010006070522900e400c040c960540344120a4107811409a0058820396039941009070080d943c0751070b142401c0300507110003001c143c0e8242c0782010a02c440034040d4014070500107100703420322124580b041e0a40c3c07280400d2062004940000c1c1c00c0c0a8000e1080c0d0000383c8a8a0034045141071001c1900c9800131100399421455140c03001e150308030305240d084200d0181200c140002c8003040320010501e50708680c00034100501c88840020101410340c0c81208423942603001400c0d884d1a400030814140c00307042420010b03552810721021000c1502c50090880e030607207069964606150050511450202c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 431017751 1250 431016501 431016517
    0x90210030c02160b07020414070f0e0109030501141501050408060f0907030c0b0a0318030c030e210106030c08010b091305160608090c0f0a0902031003020312030a140f0408 75
    0x801120700b4520141007007141d02004e444c5180c4440d469008a10600c41154642100c40454401000802110590081015034101c200e0303c0e001041d42e040300016158504517410040c074950038001d00789020414421010712500e41203003446842852000151203500c541d004070700c4a80c004400080300c03861540c030144c0d00403215100300c4516554948a0b02505102c0b41c000c091003960004108070480c2d41809003440f81030018005201e9680907a130040c003000510a4001d041c08001e810b560031316601c1607210350a03d24075502c0089810ba4046a2034024005400121303030030364041c1e20200c1d03640e0051045130040d14000d01080700f0758848204e0307040344100100045800d0b02c1039500308011401000100c4c0000d00e16511006521b040071104a4180490031503480d000b592a00340400305982c0f0113a0020840745503200042e03903521120000c0d02c41c40a50340010b5014440c0a9942404c580c030400110301c00c45c01c00e03800304003200e800794581078503030380c25100705004501a1020802141e0704900500004d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 431019001 1250 431017751 431017753
    0x50a0b041a0702040e1506030601050a090e070902040f05040e010606090b0c0a050a060506010809060403020706030f0b0607080301051302130927050c03191509082502010e04090210030c02 82
    0xb2181c0d8000340a0b11140c40401d1220b0700f0950b46594442080c150407a00140124040d00603581041d01051202406205940c242512041500d8081e0384c10b201d81c17000b80c0404007041d5038071500c852003440ca502c0184a143c0c00386240100c5600100d4040c070174041038451075940c042c140c0d85044c034008500e40005000c0da2503802140007180004004020088000d4864180400c01e481e10070000340c81c3d91f90080240004e42c2040d42040002030b404605081034500c64200001c034102214010002040c0900340140c0105c0002841000d0014210103503040f5041242d1138100500c40c2031408060303001c1c5265440c00b00311040700c1800440016004040b10310a6101400d00c24400780d40c000002018108003551f00d50401e00c010f2000c0e0800707010755505038188a100001c3c410f1142c0c0c80c2c1424500030110080070f241e80705182001c005003081103c503000302c0c0460030884108000490001c00c0d02c00f0a0481c00714210f01d003403100c40c0c1094003d1003410b41d001401030040d01d6a81c1030640c06030038816041821 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 431020251 1250 431019001 431019007
    0xe01170304090c030605041d121e0301030f1106040311040902011202070f0501060b070203071a13150201060611060a05060f0612011802030105030712062013050a0b041a 74
    0xc079070210b02ca4216404541d81e4003040f17561078581031008841c20b1603002c402101c6256010346024400003003e400804e01380452036a12251440b04518111035a02c0f080d58029001000000380000c5c0a404082c3d18003070003000d9508010341042240034411840f005049000344000080380d454143e03c42c5c20145c2c0107040604010105019040c126400325001300c0f08440c10f0416101400424407880d005414468031007803925031241c001039690708051190030a10301c1e8001c19130451603c684140d0701c0790b22580941c8513180ba15414000c80551000310180015880d0500c0000c056204921903065414141301034200c036100c640200c005428001c0009400c01e1400c5007880c496203d00c00207100ea0000d0104040e065410310030055015071b81456290810350043c0300510450350041140c5045032003000d02c46c8400c0c0c0a80c54a00040c00c1d030020f10001e4030010001c0d1204c480310361401040128080c0036100100740d01c40040000c000c215005190143c5414441071204c2a56813000b0940c0c50612224641 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 431021501 1250 431020251 431020259
    0x807110102191809050c1b0c040e03071b03080a1d030d030603030e0a0b3007030e060604090503040501030c050d1b091a1e09040e1c03060e01170304 65
    0x7003500c0042480ca00001c25000e030300c9048548a00c0b244014002c000d1041c005c81c00c0802c021811030003540319004101500c2144009003450410030903030144400b03403091220f546401886512034104050540d02546681a00801580808003810589038404001070500030500c00498050010506010b03d040780b00310030071200d981c10007409030950090369012078820306629000300419410200315008012405c01884500c03040800d585410188014500d058031083c89104001e038090b5000c24440c1813000c040c01b40c800d40c150030035420140303100200d4000f615200d06000850780c14003000341098106100a210640c07003a00038058008491034101d0820354402381c0e1404565400041c2005090f0040d166036000d078000038440c004100c441c4411079900d500700e120488501c1032124000080681c0400f8640d40d40c074600994240c1480504100152112500c0700307580c07800c00000d4070700c03c20030004820801d42c4c400e004401c140c0d40b401c040c50707400e03074a0b020110807802d000280791140c4c2d00041c0301c041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 431022751 1250 431021501 431021527
    0xb040f080a210c0209100807080a0206070f0206120406051e061f020f030d0212010611060a09021203031602120a1d0105041d011401050c0c0108090f070e0a18030807110102 75
    0x1d40150051040071b800c4d01e2078005403510b0641c0c6540100700680260015030056603808054690307540d0480d901c12001e0490f40700243c40d900c258804901030072141c078244400d001d041e40c0542e12802442140e4640220642c5090444c04411503035250302915002c02014000c40214a881d80261540111240c21540710501c41c00c50700450040c500081d408a4980c0181c04205170f12401064241003141580200c94100350f101c620082030304a020351603603280011502d03100c80c8407007074030904e009690320390910310700e1715051300c41d00d0070742c100180f14006c40161504249011907040b101070f03480340c014090020b0560b456605240030f060b810b003c0103010006e400c044d0055070030503840006055120079030600544405180c280382c4e4480c10010103214010b811200003d590280d1300003401e02c0c42c00c980d14800d01e03c0c0703080d805851050450103a41000076150284100039805145880d400f44502d20011000301d048065000000c1c002036800c01c042528030f4060340c0c07002ca6803604440003520301500c0c21984 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 431024001 1250 431022751 431022769
    0x1060b07050a0b2203030509160b0a090b03010f12061404050d110d12050604060305010e01090c0e0c120a020403050d05040504050906060303030a0e0a0204060b040f080a210c02 77
    0x50707807150060b010321801c00031000c0a041d446205004981e000c1d50380039103a000c83c2c1142c1c0350000c050654450201e83d030a50100030312009007401510305400e0603104c10007284240c10a03003c0901103446600c1c0859200100810b49041c1d41040006481080c07070401611001c1d480400c09856465603820714040d20094044c0d090721075809080103245000e10312000800c20402c0d0181c00e0b0582c1c20800042410ba58030428038a02a035181402103169118500050300030b050310380c001001c541c41c1011651030b03800f0641240620900481500f1340040e61a40103030400e042c00c54141101c80e8040040001034144004e045410146103603005003019107030380d1410324201030000c030600469404642041185428040c3d1030340240b0b820040e1403242000b10100340c0c0c81c04040c1403070300103d44500243c1d0441208002d0020030303540040062050540c1c5905880455001d401a600803001e800d801080c0c0701d8000407030002c4981d21101000d000700c0700b03065140b0103107003800541d8204400c20f2106400b5990300c01c0c036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 431025251 1250 431024001 431024003
    0x1090302130207060f2f1204020d0317090d030b0a050d02060304240b091e070e270a0e061504050a0b060a022b05040509180a06090c12080d0e01060b07 66
    0x81250700c06c1010460502800c0c00d0325034040c4608010702d101c0c900202e001540c2180d03041e10840100070b8a03103420340781581d4003402d40300d0400300c050400c94010300026070618410b40c140c900b0485500178106020600000e4003c3e9500000c80b0b404040c0107040020056034854001c4800c413481c0703041510354408503050080c00120b06502c406510700207240595145420180340c112041405000c0c0343d02e8117010a004003c82c0c2405800c000c40400b546484a60070741d48030440c05840411200c45106100b441000d0b00c032001d40c1480d003100c103096001c0002d00c980c0120718000d02e600403500c80b081040080c0000900d0b0301046501c0d079003604900c1c0c541030007502420225401410030140c030f18082600c40d02c1444e203003040b4100e86541e008100c41d085411101038960507140c0010982d1480c02e542043d9a40c1742006d03000e0310035410314000340180c0358002d41006100b5a910890941e40b40c0d0f005110340d0344010094202c0c40104046a000c2889921580c0107a039010700100d0707955a60110110030343c0003950 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 431026501 1250 431025251 431025281
    0xc081218030c15060904020d0f060b060a11060106020622060b06030705091e060703030e1501030f12090b0f0a210f0e0607080c0a0219030306060e01090302130207060f 73
    0x1540310400d0003c0d004140d0b0101c01500da20f4040e1030f007500043e44482003030101a141c43d10955400c024040c5a0f0031000610360050306690f903c2c0c2403c08014a10140f0020310507031030103044004034a241c0b01041c814002c43c3c0181d8000310f000250304101c0d20035407081404440c450f82c1c40c40e010703820352900c90181d48541c04544684d0b45a010711414402a00fa1440c098130310f0324420034901460741e0718041038860b11a0186000551349501ca059289005084081880d80300881d00000042043c28010003505038818160005501900c00d019100c91020780120f0a5210045c083d01003c007080700054003580c05146058001000070403000280d40302c11111490a40d5112140f408410b10301c0c0c082d928000044000a00c0d1601d07160340c0003441d440d0301a00111404000003040c001d1280f00f0400103410303400040065000500e40e18000e0004e0605110321004102c005205202c1d96016411840440b80c018003008040c1e000c041400d4000d506c0031408803015599a0342028080f82d46201306600b041c1881 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 431027751 1250 431026501 431026513
    0xf1508060c0f04170f060c03011410051e070606080f0d051602010503040201021509030307092c100e1303080115020a1203020d09080903010e0307031e0309082205010c081218030c 78
    0xc0001e1581081c10140ae809110110520320686500404503440c00703907003900307580181e60f8a4010304400d00c100350029140720f0500c0e40c08244140040b9481e44214a0f02d000c503000a84000000e54641c00351070031800540d080f490301c0801650080313005503805403051055410400b071690030905840e10a42c2c2c04401b950020007004540303600701030742d070024003101402450290a884060120400343c02c0c0d10040414804000c0b0310482104241480646403410840241e850902034080750118610710940014016000008002000102c504048066035018003004001d5803030f910b80c095441c20090003055400c2051a00c0080d00384506002c1c144035507069070307403004000200b5082d50034010b0075001542041115500081d0419031a9050b000101710300d0402e81030420094008010120019000c01400542080040e10740300d946c1e90110081418224000d403034000464200c5201c500007011060101302245a41c11500301d040d902c610702001030650300e1701d402a22811500b0034542c00380c81364450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 431029001 1250 431027751 431027759
    0x20f010c02090720070b09040e12030406090b18060402010e0102030c0d0e0a081c0c030203090d081201060306080a03180f170c060906090f03010f1508060c0f04170f060c0301 76
    0x82004c140c4500034440013041080d040c65103500203440791081051003559102c40c0c1103500c00050082810b07010005c83d44030f40300c0ca0a03080c00800340104d4081141c04545000028032198420f582508030780203814010301a0380d64035801034030540064240a4194031041c486100c59505c10481d214141540e960350300d0814003044284498600e4070740001a00341c1100481d4941119500381490700400c0d2864104801d21040c2000d90130351040300d1480750000014840a0180700400f401082e00c100844400f9030300341c4c0c0c0d6400c101d086840f14043c2641c0341d0011885480400d12610006003100490000e10b0030850343c0750140c1034412960343c811206200b070407504c5043d00c0020301c0441d4244d20300b902c08a14145244000810a1240c280c0750f038402c0780103002d0011991400d502015841080340c10800440740c0e4810707401160103c074403985145224080004106d002404203941c208005040d5090801c0d04200c4100201140791004103c184a51042201810820440c1030f000c1c00324a1070f1140d0b03170b5042c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 431030251 1250 431029001 431029037
    0x150b030117011b021c09080105010905010302130504050c060d0f14070801061404060f020c090a021306020106030206030f1905070e090f070c0605100f03060605010305130f020f010c020907 82
    0xc070890080807400c0354500c3c01c1040d80110340070500150169121110320310100341030380c010244e0b4018100c1c0d903290400108841c20507920290690340225040c500031400700c84e001081e282c044034018020382205043c0703890750805c0d801802000200c803801088034010400400b00320341901104c64020b5071014280030b0300a4002561a01401c441d01c1e122071105c005180e4100203106604c50102000070104008030780c58400d10a01481d0380c0c00504800701c50030700d041910080d401c607e00d02d4818001046001512034014480e1004803a4081c042c00d045954803075004401543c010030000c0c072080512001600780d030346441040e103d42c90644038266510310800610440c641c0007001440505401c00c01e0042041d00041c04e030820702e41c0040c02241036555812801102c044541c815110a07200c001c02008006154200034103482007a0390412881d03442d600c0b203101689607820040c0c10115030010a00150814813000c1e801c201041c1803004401e01c0035800309118030011503000700041c481c0c1c8048040e20030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 431031501 1250 431030251 431030261
    0x141305041a181b04060905061b15010f090b0d02040209010c051608010b0402070f150b060424021c0e0301111204030806010201050928020301062d030b0a150b03011701 73
    0xf4422092a06183c200603001c2c01071106e5000d400d110307400100d40030916082e40c5820300315540b030b40c0d002d9450030f891042074003142540038015900d461811040100d540700b158855240b0145005101c01602966a02030000950061940c9410400c0c1c1c1c200304070100b03c04101903c10120030210010a4a140a80c1c2d2421119000307900b0b403160f40100b10550200d484100c171012950303005100e01500350703605407588000380780f02541a500000c2c00b080010307080da0603511411944103019001c40c00048080300807a22240c00003500844200140503a4180c14450100c9016020000c3d0001a440d60001c914041e80d410416403142c152012804010030194400003c0c0d8101000307000038003441c2000e00706181c42d01c0c54001040c0000c00711040d01602486201c1d845a0010b4014000f041000d450f20350006004c0070150803100b107442d441c4807011441026101d2401100e81001040342962507450b680f1015018403112142c0c143c148501c0411043c40e800000d50081900761b022509103411001c0050a41e2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 431032751 1250 431031501 431031541
    0x40305151501080c04090b030c0901090b040513020d170f0d1b0206010e1801180c030b090a0804090c02100c0210150f060509010203071202060403141305041a18 70
    0x20040c407082c04c0d0860700351420b0360708524000c1104518070011030325000003416500d074040c0b240070000821083c0e5501c823040b40306095506200580d25000c0b00500d00d00c020f10000e400ca0f0000541d1404607941d245c05200a8084003089490140380d001600d03450342020580c6184540d1703442c9401c10100e40c0c00100340180c403450000d0a00ea6141285c0c003480b50600900aa42010307007070068221711a002e50001a10320b14400006d0600c10050410b20240350060004171402000c1e400411555080020228403d5a004000754a010309003012000903003007905d0040c0c10b6200d101c151101c2d000c1c1034002c140c0e19401d10b0b4000c0c400d02622440c014141ca041e030031918070326a80c149090251810008200044e01c3c25400c0c444d54034900500101d2851050362006030089207040441440d2640c0843c100d80a1030107580d40c0d489031504090740e140c880c45030680c10303d0164040002000380f800d1a4201c40c1e0840315041c101320448094001080c0d0b0203081e403034401c5660214200f00a52000d401059507840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 431034001 1250 431032751 431032757
    0x13090203040219030804180c0f050a05091c02090903071509020f09160e0607030905040c0c140303010303020c150a03200a0e0301050a0209090a09021903240b0a031403040305151501 79
    0xd0040230b0000d0050080c6202c05c408200740040c2941d04140a1400c554003c0d10240c0801d20890104002001e0001d109004906c02c0d41914042545104000160b820141e00f003180a54034462a400c00001080e002108a030440401003542d42c036540d0340d4665910444500d20007002401090000038611990450b0182c8223000901c001c80100303505c0b0044c002524419a40058141d09244050302c1c4544020002051140c2c1403a44400b80c0c600030001e98100c9107e41c0031104100c01c0d0204001172104541403200d4840300c144056182180700f0780044000f070f4098060034420102401418141c1d0f030010f038180740070442d80c0c0b60160700da040c00d1140d0741d40403a80c45c0045052100c04400035413482c201070032000c1100c0d1105401010b41d65115080c50340c0d0552542c0c8144800d0b40c0307183c11400d0441c544220951100c11340e40c00e0390014824080c2070a00303400100b103859841c2c01c0d555a070b4540000b19a40392000c2c4414040440080c04c10450101d0302c0c26003100e417200d07500c0d0500d4400e0401481d00101810 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 431035251 1250 431034001 431034011
    0xf02130e0c040614090a02040b0304030c050f03040b190324050102062505030a0e1006050f01090b0a03020c241009061422050411040b061309020304021903080418 71
    0x13031800944500c1001820440c2c440701c02c3e49806407000007a000d9500101c0404d400001404200750b003241d24248001d05c01d006030b50311000c03035490094a07802030340b0586a28090801c5840031210700e0700f100000e4075095007400070f11012560200d01c0b2140380c10344446540c03001c001c0103012941e0100700d40380d48500c07440b4000f00c10a10346420074074038144031708030b00c4240040803010400c900c00c40c5d0400807480c200300c01142c2440e03200d400c0103005440144147e500500d458030328414203500c03420801c000d40d43c95840c201e15002c5c4080c0100d000754002104001d090281038200800a8801004900c2d004100703040528923040c4070442d40d840b21703040e5100b10a0241340c0740080000328060210070714071141c21180c036501210b0340d00302c4401a16911010340d0071a4a49030030002040020b40086054250a690170040483b0000902c01d4521825003440c0c1d203040e801c007040001c001a030b0001c59002340301900e180310005120144d41507010b09504101e80c122404102408500000c2c0c00404030104111000e101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 431036501 1250 431035251 431035259
    0x1e08060603100b151606050601021b01110a1a0604050112050d080601050f070c08060c070201090b031302130f0515011d03011509020301080d03110a0c0f02130e0c0406 73
    0x203a91070100074210001d40d240c03c20410b0030f956881a4051382c45035602c00680d12205948030079100c604184040f070707803070b4903003004642c046d440040d212040b0400744445160303400494006680308006180c3c40754151141010310300006000442d40203041601c0502034078542040c104002c141c03201604502c0c4020008007441c804580300054459492246003011103046d21104012a03481c4600c1070701820040d400a400e10400041c90444c03000c503880d0000b650642e851b02c0303c6280e11031180050181c0042d00340d0b0703018009010072000840d000315440d04038510350241c607804110b04d1b0b000c0e5201c205080d03990781c0590140b0700603030050719800545810141d50040794480042e003441d03800440f0070341e030541d44030024102d0340b02540004c074003a03029200704907030176a0356544601070340c000d01621a80740a03010441d0806400f9014001c8803511941c1c40b1030403d0303154041100d42c855000b000791007105a04a0704005600c403000000c1c01d2580480001c25401c0d0b00329900340c54594241003942c0240e1078403030104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 431037751 1250 431036501 431036503
    0x1050108010c14070f0b07050a02150618090a0c060203040e010f0b070b04140601090b0f0d0804050d05010b15210f0703090303090b10030209010b16020607080c071e08060603 76
    0x1d150340c0003c0d080151643d900341400212141000740043c030030103018051241c034540001c003420700400781d9402c07240d00b0911152050201c50341511125081202448603580180400300c0c01e541c4070307540a00301c4009100c50f41361055010a158007000142c0c00c00901070040c60105002d0724050720184981036941c0d8901218004548120342d0064200d0402002003010440c005204c11a13000d024400c4442d80d50b110300461000f000001d50007803051102030300000d40c43c200b0307c007450040758020305550f081c2442c1906000701428450300440307082d541c40b50044110b41e03680c0c10250032061213501d129118200951804444811000380c0359054600c0c008208019282c40c0046500001c18a030101d071003e00c510742035001e40740c042d4000b00715102c07070410001101e0b0035a5024044178004c583c1c2c045a640d07100c013a400b00b44640480e240300000d982c094803025003091070041050345d08c20441c00c2d26103582c5483d400e09014031900040b00d1031040c1e032280710448060703030826409888014003604103810400c0010f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 431039001 1250 431037751 431037767
    0x9091109060a1b0503094f02040906090b01032901090b18090f090705012102130302100f020601050d060603020307060509011805030a0b18010603050102090301050108010c 75
    0x914880c940004002c0b102c544629240b03c08503001c2c029031840c18030245880741e180d0700483e2089020f00601c075095900040e0007482e040c8409900003c503a0f1039481c0c00c1b070201f00040e065034101a210220200f90000c10480c2c17000b04020300580000082c1141000c010f0020748100b0311340d6504060030146000d20b00645035250701d150414004107000d40d2880b03800180c450500682c8090300201c1d01054801070001e01903982c2801c1c3c04100c5000381d641d9600000345e00b09080542d4640c0c1180d0104005001c00d50203003a180c1e1110301d1010154245034440203084099070b026a50019401500060030802c42c1071010a41480750000d0601d040000d42c48407000b50707104e20510071248100c0e21601c192007171144a40c0004082c40e0041e003070341e4030b05807180d002a04540c000451240026020701c100c140c003030b944250110680f04018041d01900005850724902280c015081da0700c82c00261034070940c50902485004000c1d4801c0d400961120540002c0500b110416481404a64100103440300415070200075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 431040251 1250 431039001 431039017
    0x6031e0601092303013b0319020a12020303221703010609030b0609060604091a041d0f03040e2a0a0e1e060f0d1b0f090911 54
    0x24808a94828004840c4a07080794440703610019180400e01d640b070710352034600e020000164028044114040700058800004000f414408284000b040382e01400c01e0f03588081010009088034242150710364075030400e000c40480203026a1141b044903081040b0031240d102002c210b40080c50071464400f8903803c031104400001d013040b50918051000f000091a070001c40380c00200c0f5596220341e100c45019080c42c1440c0000c1e107040c522480011520b01c0c1c403e800510655026080368141840c00072000e0103002104400f8078800070000440c099034680307101d66492620035a03c01e542c20054601c42c1414200000d42a025031b07001041300380503000411605c036811562010342096200400008101030080481d80c000c00303082c0c0020300f02502030f07000070052004c45007150b410107a400791000c14094041c00040e65034015805019011540803140082c1010b481090808543e0b1100a5084c200c5a0b8a40c030711000841d18145280c03804c540e100b5000800380c261410304021164440302c01801d40c1c061011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 431041501 1250 431040251 431040301
    0x9050f130206031f090e0c1302040302010c0b0411030a0606171c111032070c060509010212010e0403030c090f1206020d0e150a11071b1205030406030b0603 68
    0x20003403d0136105130100f03d00901030351504000e02926055456111241520040c0c4160030880120343d1320000b42c42182d0450703505031190303480c10f00c0c00c0d40d40c5000c51000030020764440081070384665403030301d05100ba0084103100d801e0002e81d007420303c03095083c864800240b01c101740d400ba0300030303003048800e25201444000140c18441c010794000c050035440c101112a01583d003a0800d400780454070740e03503802c0e900300358a003010010b07404914144440010f40202d4640b00041d10b150240004502c00f079010310b420dc2c120100251400000318021024000203910510300107217402c082000b410350502c034095946e003072464940340d214036000703120070210000d02880d800c8815911a0404110165044440032010100c06014400d2410002910303002d145540942494000c000104904542d125010300f5081c0341c0180ca040503034a0301e403910300c420305804502c964803c1840114004e001521075240489c410001140c0e80c900301007000b400e43d0450711119001c0d030018401d20406016944e04d050340d141c4802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 431042751 1250 431041501 431041531
    0x60209042304020a0605251e0305040905130c06050f040e010305060406050a0b2b05030708210411040b0a03020909030c0606100f080c07060609050f13020603 69
    0x1802030901c0804422046010180512000c50880100e84100c3c000c807100980103558031419241e40c0700e0743c10010f00c02c00ea262019124101001a02408640030f44400045400b40c00002d4481d0364178200250045500440c0400144405006596110314100c40c86040341301960b41311594004a802000144040425160079950f90001900d004003a1221b2214455070360f424482c1d180c3c0c006a40541e50702c3c1c2010300240110030a405480c12280028001c61241018600843d0190701d50700d0101204040602401c00070560400c05800c080e0302039000c02d41e4640341402c00109a0a4962801c5585041c0000300400f0800842454440c28810707100451002030700000241c450006400080d84610b4003014807852060001c0901401e01e20b013000c640044d03c824040000500581e000740300041c00d40807c00006510401c83d181d003055084a2640c2440c80355621501a00c86a4001c407211a0740c50b8100250300343c010488a800078000c01040c7e0841c01aa00416098880108281800101d034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 431044001 1250 431042751 431042767
    0x1110f0d120f2d0e06160e010c0c060c0819090602071a030f04020409050d110d110303131a0c0d0b061c0b1809030711010f02060f0c1c0c030f06030b040602 68
    0x29041400340500c4d0a081e80c64074070b4055004104003020006180c001061100e45070043e5006044250f81c6603001209120564a8020100e07525440d01d20b08949081c0c0900c032003c02c0c3d0b0220000c0c003041e8085911080d04207410148000e1408105a01801c1c603200b4110400310781d0f6040008881d081480601640d145940d1400420040c16000e00d00520510a405141a040e0b500c48425052060140191030f0b516041e0b0fa01190068a80d40300b40c80a50807c00200d8584040601ca000c0f02500c50b8a218101155a000c000181ea8040380c00301181c200014150a005d01035214001592a08580050a113082d00801d04c507090104581011001e590300440c00469030385420124507948a03815803c0c8a152031507141c2e03101d4100520880746880584040d51866001d081d1542c0460526801850b2940c3c40424171610894068010203d4000400c03689030f10074141e00714540e04048c2c407040810a02e840010013401c40f001c4801803030840d85040800e0000400610040d904a5044000582c845401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 431045251 1250 431044001 431044091
    0x150504080412030e15090916030e0d08100b0307020c130b10030e0f030c030a05070303090209010602150105040615030e1e1605010807050301030201110f0d120f 70
    0x581c1c218481008030390b4065410598040d80f5125020070554070050242c4001404050900851601c158007200e60000283c0022240c0c040d0706101002d0303e00403481038211030116003402c42000c1c055000500303000420140031154a6103200a02d00a02c0451941c0b5010300000e44445003501094424803010380503801082c00b0f40c221000c400402007007042c0081200c2d001030010300e682084901540a81451030408000c00300988480c4034483d40554030788000807204072000c0d03000007000c5040c03540d650b0304a80541c03926811070340600041e400603c000815100482c03882141684100c0c8a141004800d10481c0801d05900103495107600700850310850102020341004c0c00c18500500701554403124107501100005c400c99010041000c82d240340f600c4900448551104403101070108004000420041d4400c4050141007194441a1811912078903044c50401d50300345081c000040c4800f17540c42541800344600f403080700800b0350800c007400c030100080b0b1003482d8042041140e44d00d00981d020701902 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 431046501 1250 431045251 431045257
    0x807050a2f0610050102010614090720070b090306090a03050f0a051b070303111603020904060f3615020a02030d36020a0b030a090501050a2715050408 66
    0x150902510307918038212120b1083c1e80e5052040e0b500540c05d1640c00140c81c403240303a0304000500040d145101c0c60740c41120540b400002441c07140d0b407070143c04008881c2c802c2d0a10112000e0801c01210035501c290440030035107002c0d405010340301103820031401d4400090304041101d0b540d0071500e04540e05c035144898151402c0c091410300703232002002050341d017010540c007099240560b403203a220801040841500d0b960703540903021640422059414083c0054a040c03c10306034000e120726401307c0c0980034480300c9001c3d140428294001520120034030600641081c8001c072569428184112841f2411b49580940404000320b01300403d500181e0504030310300c20f01c00c8800c041440340041c02481c8494241c0c40090041a10110700b80c2240d200c2d07200313880315009a0b0001c00d41c0040111321500c0c00d08011081c1e40d803015103100c034915a035115100c00602c0c2800703028400c0881540010703012807643c2100010425460406640c2500060b0400024038400304203020130b0b00340038001400307688600d40385140f84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 431047751 1250 431046501 431046587
    0x41505030609030304050706020622080c0d030902120c0d1401180f030e0913030809071e0f0909080313030210020d020306040f06140f0f0402070c060807050a 69
    0x401581c0400282e407400000450085102c1d90444043c50f070303100341c101e0301ca21059454081e000d0946041244007082c005644201a00a11002c2c8c90700d00c4400641d407400c0e215441420100751124040030951034850018a0f09450b03101c0504100d446078000184002c800c404001e08000f43c2002288402000350301c4152200904d6850304150001810300000305000e400b0100d0014151203480307001410100a06401000c0308800125441c082c0c0e9020340d6101001080071040f4402c1c680c0004a1030903400200d6400b44044140d4045e090400a501c00c8282c941d41203810100c0c108203100000440e10b00c205c83e80800302074000c01d400e030035a10381241041d140d00c800c2c0394600d0001c2107002c2005515070045014560032541088220a0041c10b6400c0d124144108002c04110b002c200141e81402030583c9070404c00103144a2003103a1300000030301260400c91054804600c03030b810030310020380c0000c02180c0000b01c0b814180d081940c8403500030225140521104e10317036800e101d515041061010400a0710b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 431049001 1250 431047751 431047753
    0x2090604030305030f0604060b0403080318060a02040f0e01030b060d050c130e150601080a1a040905030913050f011203020309030604032303041218030602040f03150e0a0204150503 79
    0x1641c0e01e050090154106403161100000a180411010f1516210341c100f1a042c0c0418241014903640304c54120b60002403418840c080011500d42d19400203000181c4108842500140c80390701300310b90a01031000c550400c0c00c146031004014000304d18000e20640e88000111489460314405240003030074080c2c0740082d96003240055030007030450035184d000610315640380c0040b00c0c10340c0050110b12003001001e68116012440b002c0115091025a4101c003003d401603c2030700d05040c0080c2d010408481c0046020b603156080820b00c022a440c111028103980303d240f0f2010302c010304220501140184040c4194281c1040d0311284008250090060311002213004041c2d55840c605400c2c003038080d011104079125a2503450a40418a0801805681c0500d41040920655440040003a2201d4084c00c141400001c20182c0000000b0050300081c80948200e444848805255240c040d4101c48031810000206040a0b29030200b0000019200310a0b60126004100141c0aa4800442c800290002505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 431050251 1250 431049001 431049007
    0x50a0909170d050a110a0f0509040b030f03070c0b1903090c031b050405012709020d0c140f0f010c20040204060507020f01030b030a11041506030b030f190b0a020906 72
    0x750000980c0581e1084503094400e0010302090781030300740b41c0c0c45005c00394000b04440304403007942c1034441c00127050f4076400500001129105800003a01d840c8024400e1940c1e5030002424000f0040520303914002090807200d0310303043c0f00d41d441100c3d9101180c00d940c1c03010140c1d10380a81c018410002d050400858105110000c0c1201c0d07160007010810b031a001d402c0c0580d092000000780d00c03901408030481d110303242100603010b0214140d43d00161040b0b25003680c0c820381c000c001380d0106040d40c0d003c1c1c1c01804c490041020100c141020f104038600304c507642034031507090304d09245020398010200c000041d600c08148403000e6102c00240c001d007a417510751107802904c0400e0214004c3c1c0c1000003400b21a000701c0c1c4600404030410011010748000c544100c2e0150000c0b170007000040e0180d0302e0300311081c0005001140310106554101041d400647c4000006511070007640b1040c01c01744408a17582001034050052100710324140340580c00501e00003001c643e03c01002884119460b0b0580d58800c00041266036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 431051501 1250 431050251 431050267
    0xa121202220509060a1202030109020301020c060a180308150406080111040513020403050a170c0318130507020d0c06060e010603060e1509010306090f05070e0a060b04050a090917 78
    0x105090380c02645040e040119400802c191801d40415486940001c0c80c5100540c203201c082c204004054500700e030150349490200005035020b00141189003000b030020a802c0c0740240c8000142c07a03890f00c04120090b0754074454001b1990200d000d0350b0007140e00305900005042240407400401c1650b0001c4501d51902c0307088458184d01c40c000f0b01c2200c10895252241c141d01c80c003000103e1080d071100900036030050200000290108088000c14000c507000c5038140410f403e1000d0841c1d0100b104070441d0031122240700c0842c03a000c400c6000d40414900200a02e1400c0c3d003020f542d9a11000c0b980f0240030360720307038107404004403508001d010300b0618501d409156503c400c003070003030402030145144145000f8002081544d820070b04c2400850001c003503202d10703465615100300800d1091b000b0380d07481c1c80710a02035000c10010006000244000706c01d0b004a4501003a500084034900c6c3c02c80400e22108200c1085039598840c444004e07207090b4000010a4030003858074001120400c5103000e100400450004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 431052751 1250 431051501 431051527
    0x6150a202119080112020103090312151d070e0114090d060e1207081801120c080a05070207120b1f080a060c030203010815040602041205280201020a121202 68
    0x102d580c0c0945403888a074606600c405407042070090140c2d421000d403074a80c210242d0711079040440d1450090070660161010610250103a503007038040d00f201c0040c24139040020440d00c035111140a00c1501d103040f214104104c008000d81950101281008214440400924042000c640780f407030f0001c02c0c10392407841d2454410060843c4000c000c0071401400101c80c2c0b101c000100b225889603102480c04d25201c0c95503a103060b60714034416154104a000c455038098025103105003041d40f41503454003a1286403e4050000741c86004050f4411904458410032240c482d8062042c0740c0d81d030094100d074007070340c440c1509005079103c0a500071004031080340000c1c9080b40400c040300b425025000c10b1100c07070300b0080281c06a103c20b10504d01c0c1540409a0a48620000310714190064403440c4054941503540d41d0380c10840710641342c2526a80c0108115180d80e00380c4024006070110544496a0041c545400107501d54000c808040c020000400c0404a03c074070411003032401004d019821903d0342d8840d1154 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 431054001 1250 431052751 431052757
    0xa08030a0801031407080a0b1b160605071d0405060d1e0308010510080711010608010204060504051c0b010e0c0717040312020c060901031e06030b06150a2021 69
    0x44e60764138004004540c90070004544207080d94210001060550ba03903075a00c91f10050300501a84003075400d4041c1c141119140740052014100c5e048206a01c8800b9040480440c3c001600d0202401001d0103884155503041c112a00c4500040f200011180d40310030101d1100118140300420a1108864941414194075500c416249c002d58450032281e88410502c00090f030000c281001082180d0000f4041c1440381031101c0182c009e910000c25039699461946003039811541152011a002140900c61418081c2c421510341c2502c4140600b4400e0030703101c10680c03900c1800350101044204000920850081c01201d0171f49500c0388900c0107452000c1b01d1000c81d9001800111020440000e101c4450342c400511070340725840090040e4a450400001500203140000391030b4000307084090702c940d00107081e00c1100002c601039503d00c0c10a103002c0c0c0421a0350540c00210380c00c07024050201449007640451500303100f4552174032415400c026214118540400c1a000e24034405410882c3d180801080c005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 431055251 1250 431054001 431054003
    0xa05061c152103050909090a0c081e120904090206040f060207060e0102011401170a05010f0f0e120a0e0f09040f1b21061407020703051902010509040b0a08030a080103 73
    0x42d0540d0302c0c1d0b51100d141c1d0055820002c3d00050050018040600d819100c481d003007081c0d601102c1100c0e61541d960f0030802e03034651241010303420903440340c0c4441d02c20f5607a444901d09644040d01061184241005403406401c4040b4090b41c1c1c2d48201710b0464550108071009440360001080340140c0d90903009540d11554001e40d0001030b00e8410480c11540140074141c8101b40680322090182e080c030302c41044051a08511440c03034441c900003000071034002e00c038270014014006004241c141e83c0c240183c2c25103140c42101d40f030790f90143d40c403c07959808000940e043c1030180d01d03101000d41610000a40343c1c80f9510100d50384aa00c90080c48204002c1c40c0c44000c2d001c3c8240c004007214101641c1c9400304402e248a188030b030b14407814a41d4002240c1121b1400824821040019820880c82c3d80d00603000084420303a002d0381c0041001d0090000421144140000005d101e040140c0300f076000170030b603002e003a00e16800745840d000581c1903a0b44814601c405800b030001107030b4a45401301c40040c04e00d8820b01c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 431056501 1250 431055251 431055269
    0x2a07180c030612050303150301181103070512070b03040204020706050106030203060901090203060a03030806031903080a05091b060d0603080d0f15080619090203030d0603060f0b0a05061c15 83
    0x1400054080c0f04a0464a038143c104001e181113988801124149800b1080c01540c15569158060004c0090601c0c41940e01c1c082c101118180c40f40713206040c0740007a01e400080c490f10b80c049106d01e005c000004d403802540c01e039640507038482d00c4910100e00030b402481c40013080703903040c8000419800c2d4154040c40c0f04540445820311542d0b038814881c822403200b40c416907003240c0083c000b03002203801041c032544c0040025044592a0150b0540b9842081c81e1040850018440405109241c1268010320382c20403484409071003407981a84100d40c10100c108140b500401d40401c2031095034590303a1115001356081088aa80d90782c3e00c03a40d0030020400090b000c804070b850044100040525402002c9c00e40ea405001059681ca03111149451200c880c004c64401c252a103291000584051014025400e0302040224100c6c0c150310f80b41d0259640200700740000f5190001c00000ba903918540c10b0308462080d21002d50b2050950140d03a12401c1080207010a41d060000c1510307244402d80d801e00031610140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 431057751 1250 431056501 431056511
    0xe060714041829030607050f0c1005061306122a080c1c020a030b1308070f140c0108040209090c060403050c0f010f050304080f04032004112a07180c03 66
    0x7203d04001d80da0040491509a8001030000e20700d14081c400402143c24208000350034114910f4480b464070f0944021080381544840174010356041500e801c600804440d070052181038100080c000c1c401500881c090652000c410301032040c89041000c004061400c58080e0310700513100d98140341d4881480b1041070269440440c0d412160001e04503c120443e4007d005c0c0c400d1a185848414810002408448001c1104840361001522050017042c0301481144071a0b155032030b0703003000b048038200e01441320200c1e080707140d1b1440c49030313880f01c01f80b07500c5581142e580f88143c0780c980781240b4145200882c19000b0f1310000700032013440000181d505d8100c04c1192180ca10890703c0c801116644000040003001c0f450510202c1c000030744100140c030501036004001418203a4070f4a942c905481ca04031350072982410030b400603200d0f0905020b01e11845118107403140c902400f0a4221460700444451040d01012160030719a40c081305004840080040d0004d41c050b506455054000408644c81f000d40403070710340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 431059001 1250 431057751 431057801
    0x405061503070602070e0903040f081b1c020405041407030c090c1b0305090102160608040507080303070516022412010801050c090904030c0b0a06030b0a0e0607140418 73
    0x30b9050955a80354050070445142948205401002609180040c04288004903804110402d140c00420425000b00a90440c4042d0741d03050100c3e1200e500d006000c618000458502c442e54074a40c0030380e055a00049580e2107003410a002004d006c041107450195150010511980070701000548840c90010403408020142c00c0e662011525110191f2049842c04e40001c02d0254000e040341c0141030054402c1816107c04410311801160044801b08401c0e4050100388075003000140701038001040114610b003840c42c40030304980107031005032048003107d40f074400842d100c000f0b208444620400c0c0c1034460784907a0000400c039400080d2030000041d020400051410700c140902d0b8081c012a000c0700d0310302020302d828051031480091081c1c06020300c0500c072030000350681d40340c24451400c0700f200251982c11441d001c0f04402d0041d00310500d0a040415111547d0700101d5500d03008042c40c20f090701c4023800c900c5e043c5001e019561180d41090302540545200c4aa19007180c58410041c0602504150780 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 431060251 1250 431059001 431059003
    0x131b0e0613031407090203190b04060302060405060904090501021902161404020a1b05100b01050711040e0a0818011707082701180620070206031e0405061503 69
    0x5001581c54a00c41058010070106079400740944120030210141c460303a90b19a41c40c181643d00a981075103030180c610752049a00401ea1280e00700c4c034101190103220141c91030b0005102e81c011400b5291103030100103003541940d0b6482e840b42262951100095423078004400103130100100000c0424058041c0500c3c04014034030841059098459040d050301e280815041800004e4000c811503506118a52400001905035000d90344d150300e10400c010030760700310ba03070b80c840c1c007038072a2502c59070f06020081c8160340c00516180e84240c0409030541c1c000903003844075010145004504c03140a080160001100d25101d40f003c80c20031540c40003078803081551405141410000e100c00c4130b01000044522011950b4941c40700c136001f0020503071a00001d4600e20f0340d2a00c50855015540340c40c000e1940e200c1305410081580103094078104000302e0411281c0d1100281d12040c82070140c0244514000800516640c1c0301480003144000d010f90703200403e24161600c03503031307a000c2521380035126005000002c0044c030f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 431061501 1250 431060251 431060257
    0xf020a051c0e03060112060c090e04050d120c0801050f030c0603041b0e01030f060e120a08150105040302010212032208130b03060d110a0314031306022a131b0e06 71
    0x92846e0502810005a22200010240c00d00e08030100b14110800182c10403100195074000c81c00703000640007640ea10900138082d544001c881207205802c2c42100410650000c10745411079a0a85990550f006a80002420071040f082c0e030540c02100481844180280c071f480001c0440051510003000b83d484d0780104202d060240f200501c1e420340519000000b13929a0000e000100c4184126060416515107021054208226000c001141d59042205d40c10b0040e02c100c0e6071003c2824014902030540d00000d4071104103400003400d0b0b09001001c50818941d06140e454071040e07043c640210b207100c42ca00079103550300a44031003078185e118000118403080008112802103000404180e510031103640ca5229001902c00003590103604800000040b4441101c0b1010060805000d180e48a0086051400203046604514110341c048200c003040c403840d401c100c0800c03005130b0080c03c194980c1381000a0414010100302005907044c40c0601652001360701740d03036600c41a182c40f1424040d5141d014003203680 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 431062751 1250 431061501 431061509
    0xa0f05031005041d0607120b0a030209010b071b030f0203010515010e04090510051501080c0304050601230414100608190506130510260d0f020a051c0e030601 69
    0x11503080104128078044d8801c0341c04486510786a2207a0b0340110341c19007058800c0b01d940b00400c0c10540049a4400b0381d11030a41094000c80d99171017442d0460f000f0407042641401901410480054403409204584000c003012054003584c5040c955146d1400160f0b20000410803800b81d0b003003501103030b401401c0319216100038106a43e207580a0f030750a41000050020702e030041e2014024032864908a44241c029580702d2507124945207591098140018a80d41c4010300031174109100340140000100c6c0070400c54110340a00d40b24616802c10325207c05100d040c84403450b6480f520380313404408407006841c1070a00c1201c1013059852156035400d03040da00003800321801c0f42605031050802403038003920b90142d0340191004d0321000d200e04044d88100308440040e41c1008030044004001c00035444500c08207a00400d40e1120400c805500c401d40c0740d9280711602025050007441082c5944840c0300f000100f80e540d03005000c980d102c0b560030b01d10000402d20a03210600048040d1350a5070703141000280507040b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 431064001 1250 431062751 431062771
    0x100c0807020d0f0e03010515120a030e0f041b08040c0510021002031f0f14040b01170402030f01141006030903050301090b0a03080a0809060921030a1b050a0f0503 71
    0x31503440c8000c0b10f8085110107420288006214051100e0702c0900c80d0904c145001e07144049880c03061030412100042013140d00c0c02c10b03802a0500c20000750b00143c0721000f42425507068584403402000078001d00450484003170907200c0d1001541d801a4003065841c02140a14111072401e030300d07a81442044102d9103142400742c0d100b102c1d0564011000e5004541c84040701d60804422003141c03c15031100401588048880d400c51507051201512400c9d0841c0124012181001542c40c541d00282108881001e50117480e40c03002c0005056441c01d01000c05c01c030108074020400030741c074050031000b006010740d000003520001c0706021609902912038100044c0d01078030f50500b5680b80941c249c01070070021240300c0d00711850410000007d18610050507601e625500c2d1900c041c6854240180b0744a001040800298442c1c295080d181c4201e145810302e82da418144166207070348861030030000d4001440403031014020300c1e01e8014520b82c400c0c09000505116034906620f0001840b08846070b010a40c2c1032449 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 431065251 1250 431064001 431064013
    0x3070b10050a03141501030c06020601050105130918080a23090306040b10030c03030305010501080f06100507080903030c060105030610150c1506090c0e240306031c02100c080702 78
    0x102d00c84c14910131001311924115a600d4418052289a0801c01e034021542c18080b4902031103026014441240035100c20700e041d41c1001c500d1015081d04404034841c0765012983d6450941001c010030070040303840c0b9081080c203603588042c81c80043c04140d140540c281c0000c209841c0c0340309c0e500f0360411112094001401031106c0d40300d54a444000c1003004c1d00c100340d014846800080006c4913105500300560003038500066940c50320b8002b51911400410a40c5003204c3c41d01040070b2550740d5a00480c1030b200e01d00e041500c03040d0f1441c10301c020b40b08203119558188008078254084000c0055018180c070f0341541580c200c3d445002c44c00b80280e02c5400fa148456001c1c0100010991145440e1001c490103001d0915041c10b0b644c510030200c8820360040110b80342c03100b40d001900d41e0480d81c40003404106031820201c4030708065030031741080f440c0700d418500800c0000200d41d030303503130200170032019089005008002c00010340c0e0b01950314003410340e580c1c410030305103455601102d00a072450b51140a40c5d8002d486 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 431066501 1250 431065251 431065253
    0x301090f14220b0f0a050f06030709020a030209040509160605032505070b090606041a0312030403050403080c01051906050108070e04021b1b0a050604060804150e03070b10050a03 78
    0x4142c5004811402c0c0036034020254000c540b100000b603025003101c0f4060320a90815501602c15248001d00c16408646020300740300c4141c500081810841707030745510040c0c6a59040c06c08801038400c2c3c0800380d80c86420031060127a215004100b104058801c6403080f19101e5a82e01c06903080d000455240070a003504415040d0b400004d00c40a51203502c0350314260303140c030754281d548081aa009580580850f440407080100a04091285c1e4100a2105284100c01c00103440040d94824601103a000004404000300d4100360141066070301459000c200907807101d81c590802030090004541811115078042100e483c1c13002144504d80c1a00e00c180e40707034000750755000829a44003049040c1150855401c1012901c549803580c0ca01a4100c1100080c0507002c04c043c0c82140b04003542040c99100350b06a41003040640d0340d51044400301c030140e0a20a015584038144085d01031030381e80440c004541450015581c10070080010104079210b440050345c3d82e00c0c2c0461140d4682150701a641d0000031400043c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 431067751 1250 431066501 431066521
    0x14271f061728020d1a0405120f040b0c0705040903050304120e06032406030915010b0c061902190c1506061407020f12031c0c0903030507020301090204110301090f14 72
    0x5110303001602000e40c3d80005e640302000c440c040c4149640e07228000041c402003010034030a50300080d188003020781c1030000036800180b0b644694410400341880000e8440718a060a1200c80001e050050081043c00c8180c100a41981c2c0222004c0300c0c0b0289100b6a08507045c02075998808032071000d4121130131a600e0460a03203403c0a445ca110f810075201340040d040340d80c3c1d900021403040c080000904048540c0c1c8000d20034286040c1c0100412aa0522507110208400030381241d003c2c1c0c403241510207603026005144024858400340c24071210382d41c450385c03016a401030b403c0c280c083c0c4211703086481420310790b0f5410202c030030340c2c0610f9000404003401031134182403802c054a0154002081005030303841c0d003000282020100303403a002c0180c1001c030303404034010034441c048500c03500046401c1c4108446100024034001c400d000041c04d00401141d4002551030950101c0d24840e4040c0c010803103030301c140003180c3c0c41384c01c244502112182480d44024000fa070901070199421214103203500c00b41c036000e80d40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 431069001 1250 431067751 431067823
    0x80708240c090907050702040905011505010c02030d08071107061e170a02030a02041805060102010b180609041a10170703051b1203070807020414271f0617 68
    0xe80100b00702800346c40056540c611030b22503294810742c000205460b904c40354160f00c8107507601c0749050219440c010030151702c011a000420000a1038013000079590a5002c3c0c072140c121011340861440342500c00f1600d950480502c0b04403661000401d01c014050308011075080300c20203054695642280080381070304006401454002c0600c1d0405401c2c00e448860081c080404d80007043c3e40b940d240d4080c0035031542c080c4106120407100740c504080b0620303045140c000130f400150100c1d000300c0341000020148000d01d4408044445c1c5040c01c9081818000c0048100325443c0c020003414844d0701c90300e90301c900d0000a101084942c4240506a000010f00307440c0034604031015425080600300140580f070100074002015010700c5400e500d83c441c2440c0c01404102c604040091054400170f5040c09009100c406502c0c900c03d60106d841c0b0580744183e05a541800c50041141d5650103690a0b050012501504030b48103850b00c10400d0f02144190089072580d4040c864030130340c1c124001d001c00703081c3c1c1c8450a0f15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 431070251 1250 431069001 431069011
    0x306130b06160303060f060c1a1f030b0601022e02090607050a0b1f0506120711010501260102040b0a0c030509152706090f0406080708240c0909 63
    0x811420a28004502c400c020302c0c070601180040c0c0d603248180106880744809202400084ca866208540195500300410100c2d210405178a18944001940d40c402249510b0030105400030f0800d1190352440c0401d04803c080d0f8516000d4058041c802c1c2c2c01c8000c255a6001d40050001d100007071120440f1038000951207100041d82100d0104101c0d00851420400348000b1882a03000e0710b62843d00304060000d03118070031001108041780c01010401980c4520656038a201884079088041e210080103a4541075200071100895013050000585140148003940d507009010035654034114250f8100c41c200c0c0b10754000c91100fa40140090b000c080e118110388100a48a818050b16040d5480001080c3d01031200c0c807000340c0d040014844003440c641c000c4100d542c007501150700c61108400e0001800a010749103409014001d03040d58801e483e665074010388014400c40b001c2d50312650321040001d44468400b00740d28018480305540030109030041c0000381c4640c2c4400b010034140180d130300410001e428041d003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 431071501 1250 431070251 431070259
    0x1120b030a0206030103420b040b03010e010c030c051303140a0c0e0103140a030e0622030501021b1c03050a1e0608100c090b030403140c0102030a050c0306130b 70
    0x80d40c0001038540000840c040c0d1f00031004a19021000c40d4180820308a100000c42d4030f01004141d500c1000481c000400301851001010416142c4034010400809010846035415030801041614000303041d40300070f650001540d400d12508841000654491250b000ac441c10311000380f13810004110f80001115600035590280c1d00044c0b007644500c01e629071160071000903411520010003c0114207030100b00e00c954480040d00746948951800360165500c0c090080c050302001410041308030410400e031400542c005200940252a0304240d0700035045806103400c011084030740708406002c0080c14224208489100c600030415800d001c602034900a4000f25600d5203544492182c010401c015080404c2407090001d071a80c41c209a940c079110f01d44800c4000d040c542100200410351001c00c610588405022103542ca07112480e0071074201c92007070b402c1e070301d10400481c680220500c107400850052200c09414050f50320b621030044024403065a00c15849031060038001c00e21a0150407400c51050020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 431072751 1250 431071501 431071513
    0x6040b060c0c04092a180e1c0201020f0a05030f060a03050d0c0204090c1205060115050403110a120b0103050c1c1e08041217030115120b06070b0f070e01120b03 70
    0x90410501c9405c58802e05c0c5007035074107105104601c1c2d01040045a07103100c2c1c400f4084020310403505611480d001d2044e0130742441c09040301700814001d4049440e1241e44a482682c0c1d500c83c80d4008045400070364016400d90504000f1a400d45000003000d0160707900000506024010000140c5410500c180100c0c0c20a45032401d0034040b449921807040100000c866840c10748030a0301d0454100f01c0140c01c001d100700400012003419590200549094a500861a410000c8a500003070100562540691004455242d070741c0f003004600c8071080d0407039126004903100c0300d085104010102c90490407000303141107087c034520003142d0390f0b88807641d03041c030000350030511041d585c4c407101d4196005410494810f213040125004100d1302e6800f0909103150105506e0039541021000f854441712411000204001c1c0f04041c80705a5256001c1c3e841560014030042d640e0240e840c003008880811100f40b1060a5504001074072207008100c60020301e20305945000740908150300280007801012240e6415106603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 431074001 1250 431072751 431072783
    0x1b19170703030612030e03060f270703150b01020f0d020c2b03030e0709050103020904060222080d0e01030c090512030906130f060f050a0806042306040b060c0c0409 72
    0x1000048034114003e585804104d1b040c1402d146c0307040b801519202d0100c2c03031102000000301c6444020300c8510b40060b06594101000e84050385030803940d03000500600700120180c0546205a842021051400c0c1c0a0f40c401c0d1a16004245e220300d450070351040541c00c1000d10301c8403468100c20032110300110204030301c2c220780c02613508014035012420481c08284c0e210244e08903018100b00c5600100341001041c4150340c110741c0820484240034000a20706030b004200f1038504449000000054000f640401c0341d01035451549699902c0c1c0d1821003008a02c160141010b2948039004000800210ba15082d031018905400d20810034050701a1412500091051003060760b01e110041007111203005c0b03040130060030300c401c49202554a61003402070101d03c0146d2403559400c413041d2080000300c0d013040302d000d507150404100036007001154000c04403141280013454440000d5a18001c120541d003c000c054001c0c020f2280600c2901181a840da00161000019182c40d4011002003441040c2d9403d4019003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 431075251 1250 431074001 431074019
    0x160f27050a0504031803051b0303160305071b1202101b080301050901052e020a0c09240b12040503041205070e09120306010e01020708031b191707030306 67
    0x160707240c80c03103103407900d0500c4245a032241034100300c0003a07805010665480c50356081d03900e4240d58a844403160401803124031b04c2c0d4040c010380f5442e00c0903808250f2004c2c1c1e9460000c0c003a80c0500011104103640b0281000c416040e1054482030300c100090000150105408000408812024403030400c0400c40000d4a00c04081010188551041001715180e50404003049040302058000034007aa00401c4840200030708034021111039800381c10026443c071201d4100f281403400b101d00c058018050030400084200c0103070f011001e503904050102c01e0741080b0707414921a07003465101e03010b01020b0a110440c40529411034142c0c102e4400c40489180907580c20f10320031042d60002c0281c0340c50300a4001007043c1584140c040d03074080c1800c009000340c461001d031114801e000190110b41007101c3c00c0300c2800140d000300014409001c180003182c0c0c43d8490304a01c03010a429a00b184012400f035170071860b28952012032407002c0036500c00708a0119400300203649806400c505410b408150301ca007000075400700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 431076501 1250 431075251 431075261
    0x50f0c07050708010204090c3e0109020a0b0a170106021c050c0d0207031e1703150d0c170309030307030f02160f06260a0c020a02090f09160f27 63
    0x1240002c40c81c2d207240c060140034200d04481ca000000c81c8187d041000c0e000404070b427015a640c103014400c0c4c0e101d40d50360b1180144180740000790080490a8003254082c08a009001c0c0c83e030711680c406900b00446500c50174003c800384181070140e07104d070060060896103107101d0002d080304d134a052810058903512051a0084650080e000341e04804001e20a12459081c500d032001040030002c00302c069141d81c2c0c0c059000b00900c211100702030201c0840e409000355203030084e80c040001c00004890b4601d0600710445401e500c5001e035042c3c05841e200062100220030360b030002d00d004010b141418203546003a50901000e0150b0000c41c05880c1c1c0c0c62641c100644c039880c024003c5d0321302c44500c15040040c0500000500c220100da0703044076854001d00d007994a01e24903440000300c4000720f40c0c4100920142d1070f0a0092900962009000040010b00300d104021075124603040e00840780309035405100605a810355000f8600c4012a022050bc17652006880c141c0d000810361610a48800000501c40e085403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 431077751 1250 431076501 431076509
    0x5060c07021915030902060904230a06050d1b180606231c0b06070813090504020a030b070c080715290405100e090703050d0201050f0c07050708010204 66
    0x20402151400c190305102800c00c0c004500b42c1d10034242281410801015071042288580030140c541420404548032203007034410f880e0303000c2d00911154a064540d83e502d0a00e5100007140d030142d0308000b842c80d0703945001c0d203021038a02404404600f00301da26515100c41900c00e8186242c104c00c0c42c0002c51858805e0144c0c818900804001012801c19500030035030000c842d480c000c0003900098040ca0020044102d458101d50003001802981080b2070a401034400e200c0c011758400004a241c2c4140700814000781640e00034801c031040091b40783c0c0600b01c01c44800f6500039410840041080c40060349199501790060300c94248508154031ba51341d0b1000a62048400310341400c1e1600c14003071058443d000701c0c8070070483c0504000c1002d070a0038a041000c22000d4900d44503c0d1982d01190800b0220080d000141080c4034200b1054502051041d030759207002c0c802200c40d0312548043c3c08401d4818440c40b4000c020b9195a5061515000b10020880e00318040a56481c001c01a00180f201d400344000d000078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 431079001 1250 431077751 431077771
    0x61503030807021b01090512010e071814040c1203050f0a0908010b101d0a080a1b09020c030406050a0509090103030809150f0c250f0c0b0a1205070c0506 67
    0x151410402c024200707801407416044c3c00b4081c4d07108021076038100c490b103019500165001d0303c03010720394940640174107040c0c11444c481d0b000382080841d0000580b0040702c130a007402482407003c03c5481000b880380c640d04440290200d80008004c1c4607803120310303640e50400c0b03002e0f14010782841240659401698005240200450784203042080b100d4000e010300c8010680481700500090064807024180c2001071640f49240312001144003890303691003400c10007502c0c078402200c05001c01c5160548500d01e4011012100e24080c140c0029002c4c01802298151081100510300b09072800b44165510313040038998100b0f105040c41a0492130325a91480c41c004c502035500c004027418003440b05401c1040c05c3c00c0c3c451f90300c0d003a00304000c0804400305040313030082e541003001981c0718203c800e0482d440e020780a62024031484070b0305082c184007041d07440c2d520260044c180101a1a0b84204002091042619440208110820100c0b804240c3d900c0341e0703406a0582003403205a103080d62250b0811008942041d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 431080251 1250 431079001 431079017
    0x80a05030411060c0c0f030f03070f110a080304050103110f1c2414060417010f0c091d040606080f0102040914100b0c1203091c0f1b06150303 62
    0x2e00460801820301280182c442615028042c0b01d00c3d521a0f07003050b00a800b512800d031981215413400c1058840c0c011030301c03050720385812440ca0101c104003030740c0006452240c10f20352200520324183ca94407044402050045d03240038a007034015000b030800c0010700b900b420014840d840c42c8100100050240d4502005101c00079a86c24120354200c400003100314185000c9020109404400c69801406440144080304103080040000038854480c542040c0080301d282d003000f0032150302c1500b24010303400307100000740f1955000290031520312500e8803801101f1000380048031203602c00542c0940e0000e001d0039002c42e4041c1c07944142464038284c25041c02050f9400181000100118803980014a0a240342c00701301341400000701c112100140a5003102e1880090ac04004500070401200e284a000c0e80058907890f08020031034071620142c0746032038001807503a200d00c0c1280c0304d0384105145c8280303500d49107040c40207100070092000d510201200c8407a40c6200408a402d0700c4020f4a0096200e0342d0b5540b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 431081501 1250 431080251 431080253
    0x1603020a12050a0903110a030501021201032108070e0d06110405131a0919060303090608090f0d050d0e060903220e010306020d2003090723060c0a080a050304 69
    0x1a400c1c01508240c2089070500540000650104034032007101c1d0044903480301d900d08280003451142c20359100800c0d0b03600c000b50f001d03000750070f10785080c0c1200d0091240d0007880221150301410280388003005000183d07500c001500050260020301044c0d0806010103240c1d080c583e480c001191095050740e0440d41001c5004c2000c0e16044601c1c05038403200c01c07000c0c0f1140c01d00a20030105030120501c0184901035010015035526201c00e040f00d02001c00e40b074203010311030352403c000e090729005010700f0000682d40c00000f2140310000882840c0220144000c1510070562201220181c00002c040b80046451b070b034044410103010800640191042c20145035504240c8090031101c0560488511925081d041c00304090159081100d04481d0022000359941c43c11b0108800144458100c0c0480c00c1e10300001800103002d400c002d18442c4c0200422075041c0c5898590001c0320f8042d07442c5002e01046890003d0035141800000f0f08403461030382c0d084405801c4507594801c3c0980001c4034a5000903c0882040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 431082751 1250 431081501 431081513
    0x20a06021c0518060c1501090c030c0c052e020304060204060206090a0302061b0c1507030f141306020403170a09090203040b0f06030f0708010b0f0a080d03111603020a 73
    0x21a0501d0500700702d40781c084001d41402c0740d0340320b24000754807442000ca04080301000031b2000282065500d44084040d42c0c452800400500b15503400d1000a46800c1400d8402406100701e002c0a940183c002d00200881e6050301d906414600e65031408480704450081c003d030040e0002d180194850b000250b2140e0034540d00a240140050030303140325501410b0090701098001c501141c00c040860201510f4030482c11544409104450721507545100d4038000711094229000390303c0c003c485542c2c2c00c0c00b00121031080755080da41c5002034014004000408510000340300c40031080124403810300036080940e40c2e2030b00e220140340d242c1d08044100d80040c0d941001c0d1791100c000c0c1c001c0c0a1105e8210b0450401c0e0311240121382000703000030101101d90001c941035560030403501c61074031080000c03108015207913941140038203015203181d80242210058110ae0b8071781000701170305551848000341000600b88800310701805070701405030690003081094040c5038445064102c1a02c2c0680c00401c03401e100c9280030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 431084001 1250 431082751 431082793
    0x20c0d03051f06050a030e0a02060705060717190b13050f181b010c1104060b1e03010806060d030309052e06080d030c11030301060c0c0b1c0216020a0602 67
    0x78142d41d122901d8207001241c0c00000f40c44500c5040e1a0014054040c20101894040d04040180d441100490750304100700c2c0000e422441038407190b0311000d802d04450480030100710183e4110540300304801800c20444421380c42650030030802042c00c03421818804a44046039410350b8408000307c1c840c0108035400820a49909000b9064001029450007080c1c00d281c82988034084c4a0400210903200400e112a8400118034800c2c014000c04c04140c0e10b64003c0c603164000c00d0107011a50b00c000c40c0c696800801416a412511908003070011036a4800c02c000b40da49007044201d06241e9288506004120100060b640011014888010003401c0000140c1070f164150100c016440c240b030401c3c1700300017000c00d01c803801c09070505011030b020241f04401d480014001030309500c0d0340700100000805a9000780c1c84043c041c0659a56403c45032504142030081c0301703900c0d03581d10041c000e2040c4041040c980e4000c112503008004654441c1405600182140280364003440040c1d100e8a08075049601c1d034240c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 431085251 1250 431084001 431084041
    0xf0c15040503030615030702071a090a06050405101107151101090c031109090c01140f0f0d06210201080a091505100914041412040312090b0a0c0b0a020c0d0305 70
    0x1c6e00354540303003000a50340d80f4a8002c2c84030070600b02400240c140a0802503a5142c440100b0180780152600b000500ea80c12910410f4400e144050000880b280240344a0400c0c0c60b040001d4812681010710060000b07085101d0142045085500100300700c00c28451141a94404c40408003241d00d1030810110f081d045090b0750744181d904005000e0402400030f0542c10f45802820961000c0940c1100c1c03c0060007000e0204038120400500c99400040000060002c0e01d1100740420101d0b8403183c0c0b0b8101000030301d0702c115000403000ca00002542c052903040b54007401e54803011811400b1983e40819422111b866042c00544600900541d820881440f8015010303508040200261050404e011614042c2000e40040e505a40703540790300ca0180805140c12403100041e594855a034506101069112a07020300040c94140000c540b1103000741c2142c0461220f581c1e01f000490480e1605943d070600070b04a040d28035400c0200900b000410310102aa4072410f4500040920784480da1000345112046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 431086501 1250 431085251 431085289
    0xe070503010b07032d0e09010905040b180709090b0712020a050405150405100f0206070207180b120709020c060105030a03050f0c01090c0e0411010804080f0c150405030306 75
    0x14081d11042c0c1055450b5142c140c948010310b07040001401c0001e5240041003038102201004e01000c1c240c01180c401001035040e0340401ca80c0c0c0e6100c1146089400071782e00142004e01c1c4e58085445a0110200c00c604442e48030203880a140d66140c805040341e00103027003258407440d90410005402e4010518500c901450fa40030351901c0020f920061140c8194040e1710304c110b05620398140000d1000094802030b0802030104840780151840c080d120407920700c0380c5401403040c0710002d2206880805d01500b2508880128500c414171456035402a10340001d50f6600241c1e0b00b43c00000c0303c8410418a03004042c4180c005035240d44101c0c0301d0707003030100c1600164041d9115280410010390301030101d644000160740d4151b1901c07611402180500031071203010700300d1100010080de4820901c40f265005a03c01c440c0200440c551100666001a040b04c1c0504410014000848420100b40c01030181169103429207081d103400e208200c210440070f031400d079456440401000340340c0c2490100c18250280440b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 431087751 1250 431086501 431086507
    0xf1005060405060a0e1c050f0d020c090703020c0114010603060b09030312040507090f0f0609050f0711010f050c0a080c03010e060d020f0612091902130b0d02060706060e0705 76
    0x140200c0d5841c031072807084a0042c400050f500c041079200c0d0b1840e00070442c0040c503070310456912035860029030800e0034041d01e03140175000b00c4003c803103c0016584000e11542d00a04440c003404010800c2d81c0c0e200070240700c1816000c10140801410a01c5013801c00c070703803134a844826541824802000c440294000c0c015181042003122407541d0000107a03800d21420181041d510f544070719000d41803006680c408103055051031100d0145030f1a03034201a00b01030070201c0030455190345451440c2030352800c2d42c1d000501d580603004035401c5841030b02d10560005140c40007007582081743c400902100c80840d2000c10074000414446122903100150b00d402100094569083d5410406c50484840c405005c861040a12020701c2c000c64503802d00c6800d081d03800078003840c0c4800d013407404509103440803034094800b405545030b22804503a810442c03100c925009021000182a64440b100080c0f1032030201d1580300070a032501e44010395a510003080500c5c4110400f140e10361030b25010703545418000d000001404001c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 431089001 1250 431087751 431087759
    0x6031106040f05040c020f0a06023a0e0309150912010b030616140f12070906050a12060e07170609010b0a1b060614031504080a200d080f10 61
    0xe80d030003e40303d003158002104004108240c0c0b41c180b1008170340b0028011841c05805101c0c0d01e5000e8a1407140c5441100000640305420880351030203600b0b00600106441d005007007c003456401200800c000c08101c03071600481d90000356404000e10f4024006170300005040c403036410856841c04501b01c03100000e00c140d0325110700007030711a10300405840070700c5030303440e84581c0d15407184040a09000c20102941e5890109084000da01e5112195a089500c08400412a8103203c0d004500440c0d0382550b815040c51510041211060904005c1900e055103412011a18004040071980200940d4035800ca00842d005040c0d101c80000030100b80c42000f4440040100380d10140c22141e28011600e020798145201021032003040805003000380050f840c210b40410001400503003002241c0e011000c482206003004651180d080c8210703401400c06c41c0900241d90124015410316511039040f0a1a0403030300300c95084149008a19095180003a501101b40700350402c5240f00785410004489100b2521414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 431090251 1250 431089001 431089019
    0x31b050a02010f030f0501061e0f050a1412130507120309030210020f060408040503070902070c05061c11090a080d0f0e0102010b0607050304050102060609240409150603110604 77
    0x29032000a414000c5051000c03580c54441c1e0301c040603030080c0a40030007865846641c0185a65680d0b0818048141d080d106007018034010501039040760700565030341d850000000c4c030480382994480c030b81c080c03824801e0000d100410001c1045511419040044549941c0310341001d43c41c01299a0101c00f0403404443d820001c00c2d441001071f401c1c0da40544680f1b912001c40c1408916086550490003494014402400200b0040000400c2103813000c60441c1c0c0002c0d00d42406070101d100d201401043c3c4a8120010005411f000300582030528008440604003e1041040c40958920651040030154002070b0000c0c1490481d2803180a002210000c00580e489041c0181c20f03143c410600340d00b40026540e0398112072b8800d4000005403440034003070f161150654508940d903a0001e0090f280940140c0001620074203056000c684240780c0407100c14800110358503600100c00703e80d0072568000781c5a24041d80858060004612041011180021918510704120f0005040f20781e1207442101e0402c010885010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 431091501 1250 431090251 431090263
    0x30f240c04031b03020315190e0309040c03090f14010f0b3d02031c020c1209030c040e03030f06120c0103180b0708011509030803070e0a0503010216031b05 68
    0xc0e205800402d824034800c0e440f4442119a40029030503c40c5401c040b194a0f00a4503441c000e01200c1348603002600032144034010b40740c80740ca0701200c580c801e02516200c0d14094204c140801c420b42000902091540c441d211507544410065468010002500700070b100248034103040500d20300000c100b042011000034096011043c2a805c812a2003007840f254801c03403100c1410203003070351005819030ba001c450010f51241c00951046012003103500910066180038021100e09500d013901070580041d403001c001155802042c8065014810601c02a4803502c40b4802c000440718000c004640303c1c0351507012802040b4008028038081d90a45c00d00b442d20b0b4200050300700c01d02c1400d00f008112000c40380244910000e1541303014105904e448140681c01e0740020649040e1001c03292030000f242d41020007601c001007a0702c4018010b80080002a0303070548035400e803060300031005152101c8107035200002426a04200d07040021444200500d20406420405201002c0422a002c0309420b040f9114207449803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 431092751 1250 431091501 431091503
    0xd020f0a11121203100f15080901150824010f03030815040609140601030908030a0e12030403030b0a1d0c03090109060905010519051003060507110d0843050405030f240c0403 76
    0x60f42c0230124081d400700390403100d17103c1d100e050100303c0141d803011100d644029100089007080441500c0400a1010b2145203050b90008a0001801c519544d8110b51030300c6d004101c1c00300b80c545042000104d5480e4000c94008084400c40410341100b10740482104600c068080b9043c5403601d814440001d611106030380e409004040d00007890304c40c17402010b0a00300340219151000f40000100020503405a0285120407402e0303840083e01030711401c030380e50811020864a41c4008080c0c00159030000b02400660780031240038000301d10700301a030b562003042d581c1d5080122400e075110381c20402c1c1050184502e0200c6050610240418180a180c1584001003800080d0030683c0303c0000440d0540940907100b8680c03041c5045400380d0503082e4000701816802c0d90141b200c0380040d01400c61030000e00c540b0910120b40501d2203592620f00360a102c00b15203520149806011083c0b00015040d54107009031600c1c41c09401c0a013080300900e803801035440c14418220080084801c0134080c1d03481100066606403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 431094001 1250 431092751 431092757
    0xe2706150a0902030f0f071704080a0905060304200402090a090209010315031a01051e0d030909060902040f050301270602040b0a0201020703020d020f0a11121203100f15 74
    0xc0040c1001281803140950489900540004180940300c04110040c5202e030424180100040d25144c50489440d043c543c2d1030146034010310f002c20042010000100745000303641c240000780c01d5903000070494580081b00c050310040b00c0d422050800c1c002e80345413100051811181145080c80340d40c0080ca0140040c0584000158040381c484200d0b4081c0c1c1c0001c11540c2c07200341e050820f50baa4600000048810301e401781707880d42c152000052a080052030843d42c2001042c404040791005018044c1e01524a1029010020300e00f100290303203d40c2d03201e85009059801000340e0b075a0305000c5110b000715046d0b40468000ea2400d0103a002d035014082d00504001400b00300025044998204200070f402240c020440141c000556404030784c0c4c05600400c6014401d809a4800c0c1919079400d80e203a1607d01b0944c0b00e83d4000c1c05c035040001e00c2d5452079044a8030020306110307025a01349400d6103010741e0685c2c000d0031514000280807950309400321000040c0900c20104080e181045103400c2e1a16140103c0428 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 431095251 1250 431094001 431094031
    0xb072d060e07090e100c052502011202180f03060103080f13030203010c0819200a0314010609080f01021c0e0a0609050303060a120503040510050c01060e2706 69
    0x41007090154500420400310144008582d52812070349a040045810510500d000a540c5005000e80155034a0f5280d000b15101d844e00c541400c80c0c9510758020080b07042002c816010500061548068900c0b0b0b11001840341030b864004e03003070020b0742c00a10382c0c6d107110b603000c1401007000a1120044800a00005400c1920b40b40910421140c0030401d410080d81542081580e5541c90740c0280d43d00d1003900381d105283d0390030820314288401c46070031a40a9180807126041c0e07100e06030031940140052446440c0009100070145951503042000b0381083d40044c0d0b00307517003c100110b0108038000d020000c2800031860300000d0201c81ca00780589203080c41241c1e8031401d2588010905100c910303c013580000c010704c074100380b92510503182d90044441a208400303510002ca003034500c071401260602c1d4000e00441c6810b040c103040140740012a01c10f02e04004041150300c01805c1c0038092000140a8144016524140030031011080c058009106601140811074403030000d5000a81503008001d115060388 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 431096501 1250 431095251 431095271
    0x309060a0c0c0c120b0112030f0305060f0a080705090106081e04030504090f0608120901091a0405061902240609060102121303110a050604030b0c04050a0b072d06 71
    0x4070b502102002601c2060840c0000a0b0000c04540b000101e51144040c4c1c90581e072600c420001000d000c0308054006200209110396440c0a90700007034000800a01046000141c0c00001ea82c2c680c003600000d80640020f8400c200e40e0410403038490261225061001c0c1750301d0303c0305440c440814030000740392080c40034201080c14540980102c4019040480051000100700399001c4041c00a51080031490301c200b008c064001b420750b0342542d100c0d881c140c0d01c58422074a0001d0305e0400800c0c8034009041804108000a41903481350010304075203001d6000c540c1d40c40f1240c00d01030304200800c103401c0e21100150040c0820702d1a06018144e0003001100c183c425a00c80c400102d00e001a4008120216038000485181702c4034520280da048a10a10b4120450f40b0302605210100c0700303074400c85400036001c0c4024800a42c0ca5403100741e10000700442c85080650324000100d000c210b546c040c8079800c03000039036034051240242a0f41030724802e83c072070b07070030b2400f004104001d400310030b01030107080b069989903c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 431097751 1250 431096501 431096507
    0x1207051c02180a0504110a0602030d1a040914060705390d0e151306050d0b060406171e0106030903020a061104240e130213030b0a0b01050309060a0c 65
    0x1407078950440d4100015403903c40c0c0345034010714007910b05585218200c1c0c0945258a4600c40301c0054030b15550203142000b981c00d07400360240c0318006403c0c1003050403076840380303460711548200c00340c450045080152036000d080d2202c0c141030000d00700ba000c10804214030382da201c000c4040340b001c64a10006034980310300513400210a844526451211a0040302d5203100381a60101e04201c0141089071202e282c0883c444a529562288102c140c80c0383c0c215941c00c00c0842e0140e009450741030514400400c1240c004000200540d0190f0070101c0440e400b030104a100001500c0103991182c5500d03240504000b41d90f0520f1800c0b2014402c140805891303208070400c0520a0081241580d031281c03007806680c541011050f4580c01c580100b079243d814190b5205680200380002d011424580d445188010840b6400d1162211000d882414145d070204428203050781d0b0311140c00f0041d805020241c0290a1407210223099545504485040000030710030f0102009001c0f80e4243c10180c40c0e20002030200c0e4409085e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 431099001 1250 431097751 431097769
    0x10050f01030923010c050715111306021006090207020a0509060a03080304140105090703170a0c141b060901090b13050a080a0b0a09150504030e0406080c1207051c02 72
    0x4051400f030303200c001e0100541d0104038140b482c00300002c1c0403a604548040b42c05000d608006070034030b0301b0514040f9611b895540000c40b03624440200030301d0200124404408600f880d80b0883c0140d010f1180070b0040b00040c4110005011100d0013585040025000210041041d0051034858450680804c01c0c503910170340903900442d400600151a45440c3c06e102c0e004880501c003903201542000d0000e80003000c0402d05c1ca01b80c035844000f00b2007101c4c100081110701e0300401012410b0085104001d00854000040031a032070451034028881850840c0a040c44403490b280a103005920601100ca000c1ea045080801640c88040c00e0304d031640000326900c09001500d62005411040800e40440c00c2c110114211411301d0180c08248100c0d160107044000311502c030600500743c0380b064841d01c07103403001e02c0d04500e4110380280342445294041c20000317421600943c1c090a00387c0d00c2181c00c6451418003404021f07503501c106000e442e0582c544408200c0780582d5003095800190300e0b0318101d007150355003409 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 431100251 1250 431099001 431099003
    0xf0305060906030319051b0a0b1812070501020d022b0203010605093604061401030c1401110d09060809030c0c0114040e1503010b0307080c12010908070605041a10050f010309 76
    0x10244085801304401c54440002408c01e80d1b00c21820400980d468041c0000b15030302c0c284140041128000c4421503903400d8221200407030b4155000c01c2811940f400c40c0c00a84240c0f4108a16100700c0030703010f4ac0e52050303000e11b0321504180742c3c0184010081c5036001411f99008007010344558080041d00c2c0038040c0491210000040880c2452001c01e0b01030850728405031003607100c2c55042040c40100310035942c141c40244001085130701e40100c107020a0300ba00407180104001818149000d104048090f400c1501c007000d00340004d04041c1e81000740c02c1e80080da03a5001000c0300040c614004849a209868901c0c20603103e0522000c041c09441e1098410b007190020842d01c04030020905010455004124548840728820f600b49903203000c140c5070100344d240849030128001c02000e9281000d0082c452442c04130800c065690340b05510100e251070b00140a00c0d44520000100340c542440e021454413040c000c0c09448856020411282e0601c078031030107080e180708440700500400c444004034060031003030f50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 431101501 1250 431100251 431100277
    0x60b04091b05160320031308070b0f0904090506010605031f0f060e03031905090f011e030513020901090b01080106020d09290c0c011101090b04080c0309100f030506090603031905 78
    0x5d04a1090001c40500180c941402084c2c008a50b180c0c0780590710f100500030000002001c108112140d00801d0081142c1c010142002c103800c00107441e6203081060903030003a40486c800000f0014002000d1002e84984024021140902401d0140c103007010017940c060101400740d01c0c8001a15507070204241e03a0f940c522500c5e200403002440c100100ba03500f107204580d010b040d4210829540f9805100718030240042070090580340c003503620084020b404007401c11000038039100f8442e80981c880e0002c4d00e001e0180ea80c008a017403e1154001031202c0d00590108045403c15240c1c0c840465100084400700ca840c8540f14804d8404503400101c00040081c412400400001e83c2a180c070001080042c00364600742c80d190b540003c2c2d0500c560a0301d0511a0040040101100140014100101910b06180318000700d80c1800440808140074600d508151008140700124447c002d6505000d00d0340c1c00300042d60300341502d04180300401c0da03a004061510b80010a00d040440b6514805c009455940c01c1c084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 431102751 1250 431101501 431101547
    0x110f1903080a111e0607030c080a0507030213030f0b010b0c0a03050a36090e0c28060c1e02062505120a030e060705040b0c0c04060b04091b051603 64
    0x2a070a50054440030180d18071a000701e000141586000344101d0a40748d802c0d403101c0445507102e01c001c8000f014002c0800090660070305c9160f1000303200c50300300300145110b114040079821030390900d0012004160f100142d246800c02180315114004100e00081540c1402c001d074464031240b00a8840d0056407440d150610000b01c402d01c94110811521201c0c10b032400031481c030460b203c24080065030f402c045446030036030141b0006826410080700120250300b035102c0e445100c40c10814407007904d150f541c0c407450029005003803c409129900718099650450040d501c0004030030780d4041000e80c054882d19071100a2200d00115040c030b07580c5248524a9404015130b0288003107080b00c1d01c40b84d08441c1c0d1450021b440c12031200085000001c3c1d4500590a41c0ca84c13038141440c4c03041d5038900303601006500c07103540510164407680c0d0b1210300448000c0c2038441741113a1500c1c2040030301c10845042d0551005421800c040480907203030001c1c1103500780365040340b40090540d031905050b500080c204661000c0801c4d14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 431104001 1250 431102751 431102773
    0x30a030509130507090b0901051213170702030606040b1c120e090411040903050c0708030912160b09010918020a03050c0408070e1909110f1903080a11 66
    0x88010111140c040781c484960050814070a0110343e4116910401306030715480621110105a01030034241d00705150961900723003000314143c0904c40644041c4030b03540384c2d9820102004401e0002c002c2d81e4040071403990826078140c0009544e03c40260845010b203907108203590050300e410044c0500c24460440c01d00401c149403404000c541d0f02d200c8040b00044100c11310710403500d04086001e001d6900700c1102c0e100c201c40181048010540d410b8101c1c1800303020230003405161000c0c0301c108018103416002d11b440345070240901c40300c0c00864903002015008044600d40d034074810400c0b00c2c1a951050100703038451035000c0c0141c1e040c1d14150880c03110410903844895124141c2c1d001000c40002d155024080350712143e50383c580364082e0b0f004d50003072074020761070602640000025131075016900070184120b2590f0100e12904440c0c40e0708041c2c030042814014203045080002080004903001d0f1601c010035079403980c6c1c403420300d0854040106620710005001e16160b1240d0340c02080b24441200783d03440c001c0d40b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 431105251 1250 431104001 431104007
    0xb0f0703020c160f050f010210050c04081b01080c090306040f0204150b07060b01020105010e0a1a060304150501060801050a272a1b0308130b0108010605011b0503040b0d060302030a03 80
    0x183d0f114042c00c0a00003400416030703080070000a500c103c01178000303144607052002500c025200c010100e4500316001c0c080040c950104220a281c0401d0038000c0d00c54003580c520004003200c5c0010050100454104040d413515100054a1548503405c5031040c070b88141c26100140140200d0300030303917050b03265108000c95081c5030301005103100340c403542e000c0003192540001a82682c400344111041e60f4901000941c11005c1a00102103044501940e084035a80803000100d0355002038805880705540318420503841200c52003124050b00c00f50902428541c035060002c2e86407441401034803110108200f00b51204820141d482071440340c903800510940400c42c3c101c0c180242042080c911404124802038a02c500a0700c08503000008046c0d034020010312510103568401c4082e01c0100581c030500342070300208060080b0540070780401c41c0045801c5213024001071001440ea50828180c800342d0102000080c03001003180c044404003d030098075090288442d40051003560300c0650580200701c0750804040d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 431106501 1250 431105251 431105293
    0x13050a020a020709090209071b0b04060209030609010b06041214010906140c030c0301050d032706021203010b0406180801230112020a0b1c0e160501020a0b0f0703020c 73
    0xd155400c0ba048140c0da00082000d40306003c2000e900720003018041040c540c030803100c00e0304001282c50f030380355218055590724807500303030440d014cc0f541c50b40851481c04510303007480f40307542103121700c070092000e030b1204000070380c3c240300718845d060348640a85510820001d1500e414809141d560313000b081890307954140a00905411400d400215140c10300045012800d40c0503203001d000c1d9801441d00b940e0800051203074043c030281c415005d0140c058003080b403000c00c00c41d170908602e03e0751000b0701c00140f9020003e4075050290070701d95034a4030140b005000d08410035041d24121000c91825460408940b000c0e103400c0f28064001200e01e5080400b4040c503c2d01121030204510800d014005050383d965848200c80059500000d6010724081310400c080210398001c1e000d1003203440611780c1b9000e40640004c04461962494402d04e40000c603201c42c0e0204644e51107401000c0a00182000800c04d980307013104032b14000e051a11885041000c110b1040c0310b0f070f060303c2188011078112407202a4070b40020060300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 431107751 1250 431106501 431106517
    0x806040e0f060f0f07050a0e0a08100f0b0f010c0f1e060504033504032703021c0803040303051b1206100f09090504020f030106062a020901030b040213050a02 69
    0xf9264001190400901a030700602c40d10703095542c141403182445045a003030b02003480b0350307511002a41d80810424410f1242807003983c1207113400590505002d050005540c1031a900364440d83e034200050700c1990b00316440d80c9046910054a10303040c5507070f10713001c1c100d196250030888207401111940380400449074096800b5034000e440c0c082d03150b0318503d48202c140440c03000300032058015000c60758500501c0d0058a030040d04c00d09060030700095045e0151030880c0c88544624a085822000b00190b080c0081100522085005008400c4001d500da83c03c5900c400380008017015550000952101e00d40305c0e050000c003840414242d5141804c0020000c00744081e14010f01c07070b0054002020b00c040c02a01807440b5035841c3c1e100e05018601e041640b02c01060004c10983c0c0010b0600000540d569080c440d4102400050b16038a12400240d030f0540082c4002c0400d4030100c800f01086c16002d66070b0a80c1305411a50300030455640c4d66541e102051085d00071003105200c10b030805050003290000c40d00600022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 431109001 1250 431107751 431107771
    0x51302071509121b021807021e0a030915140c1f0207030315150e010c05030a0807020d260601200607020c0105040e010b07030512090c0909010b100806040e0f06 70
    0x4410f013078a400e50012510a4001d500c0841c0740c180549184003d1a01030f4488070500680d084054440000341c4440c1f54035076002196000b0062000406821401c810301800340b100c074400804400d00005014a002602d11003440c500100b568803000d1410040e640500c4118452130508211f44c80b00100a900181c90807070110341415580107500c00b465056600300c0320600342c42074000681900a4070410503041920b410000103040c454081407080004281200c1c03541d40340c60303451500100c02420140508540000c2104104080d407001284514610104040701c0161690351600da0041c3d034180c22034030100501d00824a41804072039004500288114056029141582c2480004551500c030750b00a03442c0301d062800060084840020252210500c81c0c2803080c40c0000314101031515610480e11840c090744034408440701400c11016280d0030200f040001d02c9401c404500040b0000900d0044004200901000500c240d0f1340b49c001e008060311210580c0e62141000c10704640340c40c0c08a5400440d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 431110251 1250 431109001 431109017
    0x406151806090b090603120c25030c080d0909020310120b010608280905030c0703050601090c1d0411090406090509010c020303070813241505010201050105130207150912 74
    0x541c14500c4c0001c1c441c03140140580070704548000c00d1001a0044822070f4054441e03a143e441d080d036581c444e030640d609081002c00b80918034514050004800c00d8209071000e42110302240487c540100c4c0702000d5604100c405616a558001c042522b49030340d6128140c8680c40441680c04e1055007440141070b02c8613941c403a0000d940c1c100c02207040c0c0001d894805024061003200b1020215550b004203451481070341620700e448045c490092826109270020f0320f554010b540100142c46682c440c01c1e14642d150700309007088000c00c0c4941070603684004001c80c000c43d110f04e89260007558001c125005500024400c0001c9031311751801e00004c20040701c84a40d1503280c00881e01c45a0300000076203100b403070159512100f42e9299105400d071607128000841da0508144901d2181c904018860840404011000038074100140c0c882c68019807142d000c2419641750900500031034541a580c41e662102203400075a03154194546124207042c60880100d00b00d241c13007410340801108651000490f840c40d0ba8202c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 431111501 1250 431110251 431110271
    0x60212011421070e0712270b15030d11010b1c170d0504030f020c010807021e0f15010609091406040b0102030d1401050111030c06040615180609 63
    0x1990204490042c1c0c0040251010000700306004084000d03401c2c54415112070903510354009141d100180d1700503000c40c0c5110454400204140300f049a80a0040900c044680010701030b02c01c0031030040c80150500d451b132000030710a4040d902d450440e071040501214600008104010b0003981e9811050182d5401c04064100902c1c0500e100c0c540764280d5490401c000b4907a940d07a146a41c9510100703401d010003845032003482a203c0c81040c2c401c034040d464032500c0d00c580704030003030801a1194015046c089440300340b00d0b00070380c00502c0d452410011091010240b05141d003081c0b0b40320740303c1c0c4446c1e841d100e92600c0060036a06151218102c40013601c8510115442d00800d030107584541410b001d0600da00700004d2078038541030b000b00040c00b5040c0144d0b441d02025038400400d0390345400320803402c2c03003104004000959106502c07403981c074041c101450412500c440100d8a510028002a00c0b1300d0b126805145800d060071002001000401c400c40044a14106040043d02040c42800b480514122244c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 431112751 1250 431111501 431111519
    0x6012318190b071a0903030402100c0c1e0b0315032b05090432060406060c080a090e090f010f020702030d030e01060b0711040b0d0b0403080c090603010306021201 71
    0xc1140c0380c001001d40c081c42c01d05807030a41c95003110006503011000c103254400d1602411000e03038052880e00340691b0f503d2070607006218041040580040c00c2281c000520404541e41011040c1138071080141c200c04894a18030001c1e44281a07080890100b600200344400c00e4512003e941c1f20180690507a0040802c0c0711415005600480800c41c60b0001603040f06d0102d031080d07004224514000b00009000b1680350002c140c1d200b06004407621180b00041035000c01c021010003594403c4045030180603207800c0c070100403c7c86620f40c82c01050f81d40c000c1030a0030b9060241d87c581c40580685100c0d0034951a044074031035950142a10038104075407030401a60041001d6000b120fa103e81c01600500e2056880c213001c0307006109200c04c0b803c155607240307804560b02c1001300c0102074007802003031841811484007007004200e07004184102e2189049400c0100001e40c481401984143c041c00c2c8075020341c0e104048542e1900c601c643d80342c0d01110010010041000340ea019200340400c10030051482d03a01d03402070b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 431114001 1250 431112751 431112769
    0xb060c15010608160f05040f03050609210f070809280914070e010306090c020115081c26010e010305061602120702130606031b02070e060906012318 65
    0x304d54200c210140426028010004060411000d2034464906651860062242c0c0b20341d4008a8140e0001028000e40c004204240c4108941c000c04844902c1c0d4146c1c200da03035034803800b811900c0d10003001c01c4110a201c0040c0540c2c40b09440038201c4810f035101c4040740d20141c01c000740c01c0914500c05400c0818804181e114580c404101007130303c200b00b0344443c0c5050b515046e5420300175042648641e4081b60010301c0c0d01070460b41c654550004218184d0304428500b022a031600300b80120ba0094180030070070304140c02d040240c82100c1c280126001c2680182c0703c994942e00010a440301d034810000140d92061600c114122406602554200e440f0340039240c140701010840a001030f4070120900c1c00c2c40d140da40041c41c1052000782111240e4000d6600c12040d2032084e03003e60701003070f92106000320302c60501c624050320402c40d2001c0c0144c9800d110f10484150340c05040c55015001d0400091a940d005410000c4402c0100f052039100e00c44126409030107912a01c0031242914100c611420b5034104002e10b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 431115107 1106 431114001 431114011
    0x1f0504050c12030c0c040e0703060c090f030309060e100206060603060111011407140c120702180a0b040606090305060f04170f0408060c0a0c060c02010b060c15010608 73
    0xf1405d040d0722107030290082e82044d034442a02000464075000b983d0b40940002541c2c1030b005000c4403125810b070070150741210b0f07a142c08000d154210b08030358104c445981e9802ca885c4c2340a01480b40050420842c0300c0540c0c4040041178051a001c0061540854103151800c3c0c902050100f40c2d0a4400c00354161103401c00040c00d214805034407054054415100313890302494039108101480d03859224200b4410f8080c0c01203500011550340034140254245039203994425401c2070300c41d138030007080c451a0040c4070307501d000c000140f494055003201c03080325049000360000d41d8540748410b2481030000d200700e820700c54915012111101070006800a007803480391003521142014071103883c1200180007a00d03090800c0c803070b1050250340000060686a8001c05c041446030140100b68003408024510035400580814040707840040040d9407026000d6240c1340d41c0c15039aa0b10f00c25a1200f001b59a = true := by decide +kernel

theorem cover : BRFrame.Cov 430935251 431115107 := by
  have h0 := BRFrame.cov_init 430935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 430935251 ≤ n) (h2 : n < 431115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
