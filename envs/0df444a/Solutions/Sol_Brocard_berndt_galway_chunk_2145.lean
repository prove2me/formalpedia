-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:47:03.783992+00:00
-- url     : https://prove2.me/submissions/9ac6459b-58d0-455a-98cb-1dc951e79cad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 385611510 ≤ n < 385791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 385612760 1250 385611510 385611529
    0x2802071b0906052218050d09081b0108060303070b040c0e0604092111300a080105040b1f0e04050106020f0307110a050310020d1b12050c1b060610020d020d030b0d02 72
    0x1c1b030300c0c1d400010b00420421350040c0140010034004009241d180b02c883c08842540c00d510461381d0410004d00e0000310aa1410000c5801031b039408441882c20b0300c0c0a0070015486492401680d05410581002c07480e2032610f400b03654085504440150440c442004a146c452011140c000c010f01c84a05210445158203000c6001d042c041121481911000110042c4143da004200542112400c1c000380200d0741e41b00030710724107441c1e0948000a07804240c10005850010110b01d25002e0400948030fa80c0c01075001c10886104081643d040c000c0da600c4a41c26030f254042d61603600c18961045c80703e00007081359540e0403405c0f81e90182042e1103150712130700464140080926034001c000d030001049060340b100740c0700f50300034410000081d818421105c0e50003000210384488500341e194841011840444409040fa003860308400d0207120113000d509c070266240c2d04215088c0e40b1582e510404500914000f0403031603a40f0300e02c0ea000e030a5403642c0f00400d80040c10000005904042240c036a40c0042c0c0383c0c440007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 385614010 1250 385612760 385612763
    0x12070c02040b270901020c070b0306030307061b17060607020904080c010203070815010f050d02070302070503011e140c0301030b040c09020a0c1b0302092802071b0906052218 76
    0x42851072000280650450001410301c4c0b031503a1041000a036048400300d00070381540c80250101d5940e40382c480000b407840c0100b80020f42510300e440e02004076500c5803a10a07012079402c0d1192400b45100d0101100e0307150044070055044041000030324014900740155a50040c4600001402c01c1d071072540311400c80e0012101d00000c00c004206000900c5080c008028982809292500342c84040400040203400382c100b50b8410245c0100b440781c00c2500038004140034040180007001118050140143c0da1041c640f040d40f505071030318240c41d000c9141002079a114200b0340c80c2c81303480c42c0d1840c0d4a100b921800204192001485888042039021040c00100705a100130390b28a0b02c600050305002d0002034000800c25084201c01e042000141c41e0082d030701e80e105040030f4003140380d03001701d43d0a0004034050303248001c08944001541e104004010301d81d40020141c1e03c00701400c0c2522405140308680d903500031240d2100c0c001021080840c0f05490400034580103060109440307010014007100880a83d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 385615260 1250 385614010 385614049
    0x304060c0314090105070b18061009060608010f030f030212030c0904050c03190c350c041a0d092003060702011811031510091112070c02040b 62
    0x541001d041e840800c01c903401c44502d0a840c50071681c0c00000e08544203004009001c89180d000003240620390214135001103102d40141c98242c900390480700c201490078080c1c4640680307007100103c0e41c2072256441c14140c0388500c000e920000d046803926081d480081100324114845d40011802555007030018600480910100d02c1e199850101040143c650081000321002d80c14010040c3c03070300603242a214130011710500021003011503202294000309107806c030234071688000d502c00c004200020f00170300d25100031403c00e40591a281d010741c006200d07901c500d030b400904404500d0810565880201000b0302c0b42c03000003d06001d5695214a80390750f044000000b0304d101d41041b0f009007014480194010200e1008118a0780d491980d4141413081103400717030031020b1034000440c03503450800c90f078080c23156034003000070761881c00d50110000c98805005606682d8100262a1000e0040c50155200c554600c0c4e80102c0300d5492003001c6441d54200d43e801e03a407082d00c0c0c0d00801d103030307403201c84442800000558 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 385616510 1250 385615260 385615277
    0x140406150c061107020306071805030a03050c01051803030a0e160b12070f092106050f011502121c0f020c010903090b180d110907110c040606050307030b0a08030406 72
    0x142601210648000f007034081400b000503000598001c40e5031a0b02c5401f504041e0780224451840f001c0385152500400c0d01071003164000310505402c58050201c060583c0024005552032039083e90307401003620300c56000c42e481130020030105007894003c0c201c1070515074200c2d0060b0401c944095a0707401213500030390038045c0009030128502c0304180b01c0b9500c01201d0600d510b003903003200b038010141407151144401c404414008042c00203d0841000c40d066000303107060005050007810024120428400d400c810903c0c07044481c01c0e580045015507035400c0f040c1d80b90f42450101c02c03802244030748003030400c2c0800350742c0e51394414540030300e202520301e032483c1c4800051048014500075214400d1900408005032050207000a8031141d501c8a127030b049416114003a0700c42480c0340400100c1c418844c170541c040107000c03c02c04c0156022a5850707805400394210303000102001c06100498880c0e01400700092005c100042d01107000340c101d03c1c2e600e4400342400100a41d1840d03000d05540107608184009080003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 385617760 1250 385616510 385616513
    0x1b030905120606090a0f0b131407020d020d050c011803110705030705280306051e070c0f030f20060709081b1905102a020a140406150c 59
    0x2802262241c80c181c010907039410100b000441c02d80740104402a03481e1520b0400c4107038101e5401c60104040c0203441c450407401c100c02100d0107810300c2d0b52613802d0500e40c0c20001d41a14800074003840303440b07040d070094845000000f0701220190f003e00c1fa1214203640355019102d5070982c3e160b8071a0309502a503a141000300300c0140b054101489648030b00d2084c3e00c0318005001d02c0e981d038613007040c00701c201a5181c047c0c02d0004e070000400d800d1651020f000c49180c8410458501d0007141382c00c40610511032940010394480c0c42c01d030b0300403468000c0504003078444100140084e0240000c106110f540b402c12014000203003006080801c6401e03001c44144d0030036030601800d10780200551019050721000380c010065449401c16004500045070380c807421708800100072001341c152401e0007802025001c40400750142d68050410190f4100e403001c07031000d1640c43d07103881c0b021041c401d00d06540100030104807482e044002c02c2c4070075107480c03484e0701954801c000a01038002c42800034140078981c07220320200185 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 385619010 1250 385617760 385617769
    0x7030c090501090b04090c030e0604060906050105010f0c0212030f0f0d2d05070e0411180a12020f27010806010e010b090105030a1d01061404060b070308071b030905 72
    0x12640102d05102c00d80b80c1c240071640040003950142c0c0c100e8500040e22594641c001c1b000f500c030002006000c2d002c0c00b41408240b09042e08001d454a000343c00070b00c517690b40c6074011110082000280c2c40000c580f00112801460420801800d0218407003c0b41c1c00d10750b40e9540301005500250786c040403104001010000120107008041d00c00b80d40030b000107040d00303811540a64030300700015615035456480d0000740019024612400610b04003800070418800300380c1044e034031036100d86041e0310741c104038500840c400c1c5000e1040304252030b44d8560b03204080c070f502e50034448101040c44000c2d90081c180041020b60200b40642d029203891b003819001c2c119490f1444081c10a6010380203a003500c41c03500014000020781c401141e601003070a05c0c16903541d0303a0340002113008242c0103104081c510072940700856085415003001d13081d20080501115031014071720420044401600c01c41102c150184100c0012074010508154044c1c0a0b040035205012441d100442c541240d007022400700365912030900043c07c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 385620260 1250 385619010 385619027
    0xd05130b04030201051903150b040303020c030d090603020706060b0f090a08060903070f030527040c020109120507150f09060b09070c02090a1103090606120304030c03030c08040302030607030c 84
    0x16182080745030a0658000170413600ca140d2180e40180601c40e80002510700c280c0c0050344041100346409911500d070220071100d0b0703210340703c103800500c282961040c09145c0840c0c1d8003009007031602c81402c21490100190702a400100d003d8138600d6a071000010340c0c400000050410b00100741405a23110440401c02c9131508a0750050901070b401201040b11000d4000100d4074902c0e0090403994900388e4914085895200314000340c141c544100d05200c1c207030b121000c1100b040c1c801c01c03241884600c0c5442c0c81282203c40107a800751102504810355401c2c1e5000e01d0007021000d006602140410201c04111000e460400e0b00205805039540d001001344401c1b4800d071801c00c541250509075034149540020f285000101e4068480c0701c01c100400c0310340030940d204903210300034400056146d1a01032180f84e160702c400c0796110700072403002ca01038075190000f1044400b0789920074407100b409030964408031503042124804540d1154100030110141c1d400300141c911a10003a80d0100c0c1e0681c280200501c2c149 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 385621510 1250 385620260 385620269
    0x60c0206010609330305070e15030411041d0304080d0504030b070e01030f06080f1504080f0a091d0a15061b05010b220e0601060c140a02030d0513 64
    0x4004500500c1203d0b44002103508880c00c0b14400c200802107480303000b02a400850b803443c00340986044039101036805820003841021981ca44040021900703061240050a8292000e00640d08000040008000c40c02c01c060041c0701402c0007600705100340365007650401c0c8074004002c03a440880c0c10050a80b040164803588291460014100362030341d61080100040600141d0500004000c0030299910951000140c101844014003c03240c2c1d5021b440d1316888002390140480c010700701c81c0f00b011030081440764010360388481110710b4928074a242d50041e0b080307002a081085092000092030b40801481005049401c10440c040790420a0781e00003151022144851907080350401002920f4103c8044066011031151545c1010703402c2c908a030050081c810b01c50390154181d0149582407440001c2001d1040c015207081000c041c81e840c8090b0380c3d01007403240400048103070868400080c0742652031031304003e403581108c05000d01c6500213801c01c51039045290001d8004117001a18144441c0041c000b030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 385622760 1250 385621510 385621513
    0x9031502040b071202150c0c010b120723031b03010e21130306020304030903050f061012020619021c08011a03061219301101060504060909060c02 64
    0x40c0c9810240c0031140215000580605006641e44d01d00c11300a009440c0207004c440c2507882c6030701e41a4000301d41c0d81c10041ca2200759610303060105000f810f2030349901e103506001c0c10007445854a803400410140d1400e040202d8a601e4440e020b040680301040301c8600c07a800c16200f81c09040f40f10040c5803c5a840c1814071400754050082d000048085214483d00c8020140d00c080e80c1e001d44040c02d005982c41940b0040080303100000b044241030b4080c90410a170792003042658552081400d8041c0d4801e400d40d11b4120103d424001081340640713110b61703514941d101800c8507040c50001d441110740110040600703009600a2a5106480701542d100b002c0090424140042c1a506241c0b400ca00c21546101000c2c3c141e07400004100340c1c1d62100c04412190660308122130b555599221094042d082619080304c3e0383c1d5045500034103400a01d29a04130000031040303000382c402c20505085a200f40040050034880d540c480f80444d80703031607038041c0780b02400c0d11480102d4074186510301541200e00d0042c050341103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 385624010 1250 385622760 385622767
    0x40605011518060837060f1d130203060a09030e2202070f020907020d031a060904050402010306120803010e0a0b13150e01060309120e030a0b09010b030d09031502 71
    0x1020b03200b1042035401519128180b544c0712805001c40142d4081900b07030f0103603443d440c41e442c40140c42d850700340312420001c144003080d03803148420054809405081c0303440c10780402e507040d06803888111341e0b40840c0b503410060840710035801007810554107039a0750a0907a12205c030401416000b6100c01c59440302500c09403016440c03000da0100890b140c90107980010b0b00052210148408401552004c2d900108100164140706c00060b590346032206024000c2802c00c40c101903010012507820110f903c0c041d00c41d5107000b1032101008010700c002030040b410b0695443c004601c0480c0702d4020150365100d500003603034a50400342595000c09000780100032041c14070b010300710035481d202080c0505280c940c5012409182d10b40c00110a0021900144000449a4000110154075402c03e00646003c0c003601034080407162021601c0408400a01e900b50b4003214040c800102156042c90380007400300000140280000300090070302882d030721a840041c02c3c90b4400d00502403a40c502101190300e00804516 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 385625260 1250 385624010 385624037
    0x20d060315061a0d150302120715030c121806050702100b04020c420106030c172a040306020a1b0308040b0c0c0a0510200403020d03170406050115 64
    0x8151080c1d0b16030a1240b6126403480800c01580c0254202940e401070800c04040341055904c1c9e42c5031510b00c1912030520319a000100c07a68041d21031514407600c9691031021624109409801512644402e00102000c2d0061000811298881e19003d0740040c0d0180c9102c8444d40078520584d9901340c445803049104100054080c0f0001440307600d40010031402d46500c4c8000140c10113480e02104542c81d003040c444801401038662074000314141c074419181084107040d0244c04a40720008034090100c0c40d04158007042c090310411201801c800000c3e06445461401c58040c2070054016031f008076038040d008903042a0307540d000075805503d1514043c2c20244458103031402850403202030b10260289142d50b010a06c031025620480300f0f1080164112107c010980c07820036a1030f00e541036410481883c2501d10507100500d07100d05200301005c2144242880d0950b0200113120701d80341411000c0c03100e042d60340404090480c000724480d40c003500000a40d985041c06610703120b0b00c2282c0450400007413014004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 385626510 1250 385625260 385625309
    0x90a170d03140609190c0306180515040b0a0306060f090501081603110103060e0708011a0901050d0b04090b0f1b0403021003090201090519080f06010302030d1101020d06031506 77
    0x10f034084402c4440c4101521221030009284c0e500300901d5801508002c035401c00541c25410170310840764000741586070590790b80c03140c0301224010713180807003004800582411549002c1d0400681e0000040840c0c120340c0c0e595548004030b44191384901e4144009032005c100c0c16980344545da005081e041301404252102007143d2032101c0140c000280003240045505078280d00c00c0c0d100102403e03000b0403418181c2040840585143c40c01d02c285030305240d003030032440310410f080030548000107070603159241011014210b69010780100306080f5003241d85c1d0b41944c1d01141c00740341040c0c041c0d604500b00c3d000c01c1c1404849107030940c803007403109607414004000800c01a10350b0074601d41c260115150003e401c0741140300407250310642e036200b1a4010424211140800c044c0003921301112110030480761a02d920800c0b00c1e44a880134803001e98903810003607900c0d0700140110742d00c08010300700600052170465840d0b1b89508850362604141d64540700382241c0b0300b004010b4802d04d00903200d044944024040e40d1100d08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 385627760 1250 385626510 385626551
    0x212060312070b010b070c0b030a05090f01020a0f1b0c170c100c06021309020c0102091804110d06021204080d0b03070b161106031f0b0705061803090a170d03 69
    0x6100b0410000d086414032070300700034070400340400e000346076605c0c10094002d101800c2f040c3e500c1041400750640b83d0810b02e105200f10303800042d250721280c61030804180e059851444015012010840002c030440020341d0b035061510142c054024089401d0844240013840d02482c1c0140c0c900404006c0076104440da0002c04034000e2070740c48040560760305041c1e503074070a00c0071031940401c1581e8008650b004c0050419005070005843c1035039900c440c29140039080100000948010304407108160446d81c0d070f414888030703049100d805031a01602d414440121070400348402c45040d43c0404000c5402c0140c01c1c03141c005c07029981c034210010b209190a02821018510641d66004444c8500d0142c000800110081912424078000d01560701c0b450906141541d2a144070581c502c125040400031170081c0c0800240c6444a4000c4028041035542403004039100072a07031000703c2caa01c018400c5d807610380d841d074001c6c0c006480011b840001000800070712510b0300b25250b180c2c02c24507081500b615846900480c14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 385629010 1250 385627760 385627769
    0xc0312050403051902030d0b150708031003050d02070e09030a080105100210050f060306060904080d0b0a030803041407080106080a1205130b0703080106031107060c050d0212060312070b01 82
    0x1415454900d8107460601c22443c0d0610a001c04c040d507400042e4001c0040c1100803d03104041c4001c0030795908022008001110f51500c4400030720992022945d000301030760380401042c0361402010389a4888a10b440c586a130708200590101d907047c4800d80070842c1d52070b0003c121a00075401e11076111307806480903105021310f80c0a80f8a0b0a040e0303260034820454007509034079080d410825800e159518070b41505c3d044895601278400e00c804900181849000d1750b00c9a0b80000c0414203103d00c3c0a03862000d44112494640d01117044040440401c1c01c1100450145102c0c040e1603003158044101c1070300340006580241416403405004102218000c1080e240c610790102400414040c1c44030290394030301800c02c82452003d0a150040b80f10394505004261071402a00e030800d00f40e03030b100c4048065403420107540150040501000000807881d40055035052a1030030070a0500000d031413240d00b20303000b4101007070303111644e141841404d09050003456a01c00032640518a09945a2107000003450103101e13 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 385630260 1250 385629010 385629047
    0x61f06020d181a0711030a0c03150906020c0c03060a0e0c04200304050a0b060910140d0b1303080105030a0302030318010204050d03121a030d030b01020c03030d0e0d0c03 74
    0x80018100000401410140c00650792441c0c070a10b0512015940350090301e005c4405115407090a000b9140010340c200096038004c00c00401141150b03103151500c40b0009442c0882615920080000b44160004c0d0000501a4008011080c4c2b03500805142c0700c6c000d400b05410341d04d00200c880c80d080c0013041c5000000c10690f80800d18030b00f0740d148149900c1101c68400c051403404014002003010204840c00041d00800005459880300e0040020081050710f82c20036081c0b410310100003503840704d03000651a0328010710800080c099600d031301140764011200c8a18000d0015409000c0681064106014110580050a0182c0c0130f940180d628407002d850041c01455072a0840661842501280c0203400c002d0040c0c100b2920700d18001d030002900c010b01001c1e40c2d003030121030925002001d0b101da00354034000700100944000c02c0802c5d80184600d0b200281140120201048582c07000c0000b01510b000300e01001a50140c0c0c01c0080d0b0901094481c42010010380e548604080703548204a448040074654 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 385631510 1250 385630260 385630277
    0xd020102030d0e1c1713050a050105072007050d14070b0a0203070312020c100c17010b181f140705060f1b04050303030a0b0402070b09061f06020d 64
    0x141d25501a08080814680c20880602500e0202103070124060000003480e484c000b07154902a142c800340540444629514800054803000940c01c500d03a1045c0682e083c0c42a0301410380f0b40c1400c1d24400c880090108910748840384139100c1c1504100b212801c2c84019042c0360741824001100022500700107490410fa000c104181c295040c00a40014405100d1040d601c42c030394440a500c1e034000302c030160045892000050075454143c0215420b105105025108440c00495484010840304255000f0003012080170003004123925007880c041c141421340c10307440351417a152a0000105010b0321f070340070f03400b101e038101040c508000d42c0413640780b01030030203100c61509082d49803c1e6005035500644103209070003d1003008080c1008507030280d4000b601da200b0340c000c407041c00ca0113440b03a071103410b1300f6070303c108002480c0e49074aa200e00210303000200003610303040742900c401040ca1425500001039403c00424000c0180100416189400021003034012607440c3c94400b035250249040624103006103007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 385632760 1250 385631510 385631513
    0xc0c02060306031c030b0405060d050d11031c02040e012106110f1603020705220b1906090617040c060503060f060a0903020a09060b040b0c0f0709051f140d 68
    0x203208185900c0304c00602d880140c1600f8038028041c0c0450400075006629000205100d400c2070300b036055881e0307004001041c0c1085060000c231000070b07140c0314107103041c00240481410790402c84803101101c0e4003401c2c00344e181c07401d01446040d10074040e030050b24044a180d40c2e0140d2115000103c8007040c0c2c02000c00a42c1e0190122449140e11a05442c446040030000e0030035002001180d1045003640030303a0840d0403c90300d50052021108014a50460749441110031031004816500003513105040505811480181d0306880401304000350000c030302166140c4c406000050f0702a074403c405a40300e03415000103003082c1c2c81d81040c2264034041d640411100000148a5480751250300c581d1440c068a0b0b150b0320031403a00018222011400100e1150f4002c2b4000503540f04c05010312001d5650310388449281a150110b006d840b54011550030915008403072082024110500032000185443d8a02056515103040000084803003040c0b44041c0118444041c002e001500700041124402601c9801d54820903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 385634010 1250 385632760 385632763
    0x807050a110106030b0109050a061a0901030e0f0a140a0305041202030102210a0c0810050118030602070302030d111315031d0c0301050601051e07060212070e12010c0c0206030603 78
    0x800240c201d5800c04800000700400d01822904031444003500304190740392a41c05c101a00c442c0c0c0f0586100d0b1a00d00c50001c0000c103010300520200b401410000340440d204180c03207051071504100d034842500819840b01c03d001541c500489000301c5080500a02040d03640c01070b0081c0918007424007881c0c0111107000854509504407050070b003010903406481050035903000d01c4024110b58124080d820041441e8100e8010590031f4003c807066034070300d08624103010046a14070040b45042e040f000c0700103400004929503200410700b0034000e602a664900348445140d041c0c031140b144100d030948040002010303074014a190b030003c0da501c003c40c100c0703c640000c901f00d024020110107a0300c000303d001c0e4814841c40000402c0c60042005400078082ea80e20100190303614003c11103240d00c1c4000031401000d03211541802410f06a121f66001030400000740c036182c00d00c1608688820101e810541c4981c040d103008500f41440050b03100080c0300c1c02c0850040104074080000d4000c0c0205800310118040d03640 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 385635260 1250 385634010 385634027
    0x6230f0c0102070c051207050f04020705190c0915060815060c030c1614090711120705011547030f1905040b06090a1506020304030203070e070807050a 66
    0x3019030003035445512908080411400fa403041521450b0f038003401c10b01803d00452000c048500040441c0c1c1030348014020f02010354000201100d01307024195103030200420340503d48110b140164076040c041420710799030104540d4030740c0300ba0003016542070003004619400740351941e00c04001f56040b2201154030b008201079021300000070380103010100700b02404401c001540c12800441c48040640c0b00c4d900c01103000680c8440f0700068008040300009201c0030b00030054200480040c20886402010b00c02c030301c00710354010f10004c55450b5120030b102c00000c007000c05000042c1203c1f5202c0303141108428000307005110240d988805500421850000e01661049403001110009000030382d0b0380b03401015810b10090803034020141c1c000e0b10280c0701115000d8404c1c184610341c030040c500d40b00d031120000c020405400400100310513481d808003010800c07007101601d0085c01d00d40c0040d6212411481014240442c58000204c06048902008000e6034001a01c94004400d428015076415462400b00c82a0341d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 385636510 1250 385635260 385635277
    0xf061103011206150501090e07090e010b04260c010c02010e0301021803071a0901050702190306020a0f080f0c0309030d0e0318040b010e040b0301062103030606230f 72
    0x40200000510190b4868810344461050383c04200461003802e01481080c070b240580350000710903070028041c8034030448806410015a051207200540c0d9080c407201c045209800509003031340046410012020b0f0755030200484030790009074149481c0c058880540c2c44004800203070401002401c0c5009690042c519803042c1ca9026000355607902e5140f01050081c042c0803e814024851000006200d89003107589034046000380c5d4601c3c1c6406400001110300e134104400c01da80c4a0130014440ba419000c074507081c401140304040260700c441c0603c9002d8110012541d103030042c00566002c010382c5038205928250720216021709181c894456003284c03803450103084d2006a85500d00485502c003120000054100901d9013011110580b03e08001e002c25905850f080340d02107015050461858602908487c40740c0030007900004402c1d036206d640c1400c45802c400351255510400d1140303002d05a0500a10002d0005402e018600360101c51003e0201c404a00a1107103082c0081610030307030300000c2d000710703031460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385637760 1250 385636510 385636541
    0x5040b1819050f040b130803040318090e0706030c05070203031e0909090f120f0a1d0301090b0a1805030403060f060f03110a06020d1209050c060403030908070801090b040f06 76
    0x40c0f50441d00540d500000ba101038680c0a203520001d501384609132140708150b5030248403582161100c0d64181c85070300303103400c101c940b420041d400410070119621500d072a45206400070715541c1c0c81d1120203002c075100b4480140401100b04100809a00d000003180d10300003a810104044848001c9036521031f00031a032006510901990601c11009000220380840c2240320060b503004641e80c0541040c01e104640e000d6904043c18080c2818060088020402100c40c00b503140d00c1c0c810444002a0845200300c0c01144c911a8820070300c411031506101300e00700c2e07205801c2c046004005039101c0319600d0041d80320007810310781c07140e403003e0101210f03030450f030300500c070207203110716004e8603494a81c01900004082c2e9019614002000841c2440000c00021000d0036031201d102030324488500001528502200740c4440c4104559407130651940300040000b18042c4e640c040c800c40c2003d4038a4103006c4a0b0344106200c0e81400080c0c0041201200c0c5030307400683c440141c2c080c1e60101c0c0b60140203007004241244c0d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 385639010 1250 385637760 385637771
    0x501120206031f121106192001022115031c030905070612050604151401050708030f0601020f01060515030a090b01080c1009080a08070c0e1f05040b1819 67
    0xb002c007494130903100d0034840d0010400c50040c400c1809400d00403485030040a80c6410705402c40c03d13000d6a4546414420000c0b00c903208007074006024260f81c40401103508101082e203544030062440540c042c0c005401300044002600082e002039551140c503900c0140c801103a003e09007450340079a0101101ca0f5010080d01c5082e03590701c1001d44807610a007a500002c608150001d00b80e0320b441e108140d550f020b60b100121445041810290000e088000d070340b8107000b410070062011032500009103124000d07906501d101c2d40f5140c0c00080c109412050521401d81c10403009100580c0e40d12900a071065144400b151299526280300010b01101403014211000800002c18580000709000043d0300c0143c40039a80145c0c00310003154000c140e8030031103806400c404a8500041c14480007440060b01502501a10036100d440c00b200e61007040c1c4c0e0100e910301914101c09040c10104810200402c2c00f00d808000000c007120100d000d01d0006103103891885440070003e903a40c00144401040901524020840c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 385640260 1250 385639010 385639019
    0xf0606060e0904021f02010b04020409051608090c0d0606120b0403031104030b0c07032304083a090911120c0f0f0c190b0412030501120206031f 63
    0x1018580110350004501c103540311054207080c1c0710b0364000c0740e001d030880d10f03100c8415151106481c4d0500c00d00e0119501c45550340344030350381c60000d04068882404e0005490400c04010740620b049010808240b054200c200142c9240c04107014030010002da524a04403100b91400600070000b1ba00581c0040c1c9001c92241c040c032182041c40c43c401c034460345080005401d05200c05100d80584d10000384a0103080001469511100c0042c107400c1d0300c01c0c100716003000c1c213200140310304690305601080d10841c003103400c0204660030000c41c030001c1140c014000c00b141070903104141d28066060680d030f452002004050380c2c01c1c8074080c000001c2c52000c0b030401071414000300321161036103c4807000928038045000b040f0440403510446400c04503180689181407a540369101160b0000c01503d440303401100e064642c090040c09525120b1307403141d03121071007900d4980b074044108010b180d0650101440c080050151060b480f80088200703404441454680d40d820050400040031183c5004400241810016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 385641510 1250 385640260 385640273
    0x60d0509071e0b07150c0503091203070e0603130501020c030a0e040e03040522050c0d0e070609090e0102161214030f0c0c0c03010504080c0c010207050604060e0d0f 72
    0x240034400a20a8403201903030b818076901c044480342c00181d00a14104000c10401079884001e080180c0f1404c3c044a2281e0941c940008440307108401d00c0204000104201c02c082062016105030380095107400c0c110f00303020100400280e8002e0046014801c008040743c1000080400b840c80154010b00075503542c2188403016407aa04000c030728402150130001555041c0c076040c014810000c1d8500029420701c0c0c5410f08010b01c056040c48001005040d50300760b5085804540261031203805022400b0385c0d103402640d448821284a4401039085401011041c130803280e1140340c0e801204d0a001c40440e50820a130507190080c400c510410100401801151040014902d0780d402c6124031a03d403145105c8002030321481d00d200440d5007462048088002840c403c402c1c8001c3d2103c4410601203a0156942e03401003401c452045d603007600c48410100740e4040d0782c0e004000382031111300b00784003034000c0a1404005c2803050050740941014414401503403001d9440740a642043e46030800408616642241040d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 385642760 1250 385641510 385641521
    0x6040518010f1a0303042108070c060f08061206040b191802010807080106020c0402070303060306050f060f04060803070f06090b01060915090602032b0e0c04051e0109090f02060d 78
    0x78a0405905941d0402031401009480480e80c8107152003100102c0c2e0040403c0801b047c042c00c54040e00c00b0720424004c942c1d50310000e0003a0901d51036801200c00c0a42002d003800c03200900485c407031400035a0341d465551004c54121780056001c1c81421a82c1c81c0c42c0d00498102d07045000c00d14100d880c105100b0902070003035030035613078450003030722100d00545841d042107540ca9802d021b0200540d22030039450300c107414154010080b85000380780004840c2c1d200c0d510076080e502d00782c84100e00f8090000501c07200e840d02d0450050700c000121001c10180e454815426200d02400d60080c14602032003110009200d400e03002020b08070380c8150004007943c0c40e07000141a4002c0d600a017144c0b106400e42218580c0d004100000984110fa00110b0800612451080b4079a4110040740c5045e840c1d00d258503500215401603c01058001c0b000c1c140b400c0c0d0710024042200d40080841d801031105010a2604000c21500e00d03065480d001400f00b4400c0c02410110044446424000d41215001403040310341d9020b0340c000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 385644010 1250 385642760 385642781
    0x30504090b040b09010b091f08190b010e12011404080304120c02060405120106050a17010506030a0b01051302090d06020705210f0c010902060415080c040e06040518010f 74
    0x40100241c800103000c1140c1e071041c02c03950000c120700c0044c801001800e0190170103550013428030194243e5801c854208000c03040310a03011408042c203006c0d010104d22204040740341000c00c104211030301070700002c010155801286000b01d2070300308081150102904800f01400c016440e800b510f040034508002150b0044030b05841e8002004000c0742e01a00c81e8403100d1030150014085c90805082c4010000350801c400c00401c490f6580784000500d6880c0e80040d000100f03180c0c4c1902a240a05503129404e591008001d80d119810415414001684807605181034400940e5208680c01e4079940b118001d1159900e00c3d070703100c00a410280100507a580041c0711017071241e01500c4140c3c0794045200c901c0110300d680801c4000090050b02d661040d000003a02007050280c002044002071600071034115030107170704010380700c00300f102a1010140c1c0002520b500100c0428200346454030740380130070248841c058011441a07807101c001c6102c6c5610f8040410f00b8500e0b42000b04141c0b4454a400e90082030f1100c2c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 385645260 1250 385644010 385644029
    0x803040b041505090307020f040902280e092d060c040306060512060a020306030115090609060602031309020904060302130603030917150403020a080d0f0f0207050d0c03030b0d030504 80
    0x32a00d0b18809503003d02d034020041d80004505000c0607908100d40c0c0520051900c0c0c0140d07a52200b01c0140c0c0d120260319200e456040e5000803401d40d4180e8814034904e482d04185000c4142c9004c1c1b1056040003c0d144200c1011410360a43c16125402c818000b000200800140751181e41c0038007061002d0f01e0001e00c11203100d10000c000301541c440c14001c00b140300500040300c4c0e80007900024142c0c1a01d400555020b680200001482c1a50000303008804040b40c110740400d550703415091007500f080303200c1c00c8041d000f02c0c00150708044400300b00e41e0b0414140e0040d694a1a00410140515100c030381044010b15801840d1920266003034182000071320b840e200540015110301000505141d54007135082990301c502c4013502181d011920308403035890020740f045045104000032480820411000790440c65459000490441c00c820103d109170f842825207501540d01c10012500082d20003e014000350101e820038002040740d07800c050b4010010042500d4000003986c0307082d010076600c18014001e8503118038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 385646510 1250 385645260 385645283
    0x105060a060305090303180304170105041a040816051516022505060c0708011811030c060a0e040b0307060221070b22062c1501060e0d0803040b04 64
    0x300300302d00752402a00e207111190820404682022101d001410001d060311084a01d0a90740d80010b0700021400c4103080c03400e9550300103110070081074000030088401d8507400e420345801d00352030743c09891040002003114244441c6080003046420b000303104542c485602800e1043c0340506080c5900000402c2039001401103800320304400742d0142800510030540b0301140075103400c000c1400011303407000801e280d4910a040c800100ca0f04700f400313050840002c15604041c1482d1915000104543c1800310138070a070807030000e128035900c65000740c890060342031620007050344114001c01d0050041c0c0044582500940030040b03001c1d600051400c2c0c81380707100c94000c0031001001d000d05005001c0c200000740ec0354000c6000c600c15900310080c500d9015944855a0100466a9505800c441480d08551180260f40d8100c4d001c01c811264094175040c0541c01911a40b2001c80c400441c58405014050a000c0320854800c105d4170b1303d00031a04070746c1d4010450741c1c0c0c0303042c5410300d001b810310100c404803030058404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 385647760 1250 385646510 385646519
    0x306030d090e0604020a050d1d060114150d1b02010e07080c0f0f15070c060905010503040c06081506030108031b07060c021302070f0606050405060a051c03020f0d020105060a 76
    0x10700e0380d40102c030201000061540c64100420002c6e500010300d1100300720007030000d880211030fa44212600410b0451001804541244070f00b0b04040f0140e20020085070030920317800060716060020001d01c7d0400304c1c1c081d50b4100880f000d02c020604a0344403103400060800e510001501503022100d4440008220b0f61f9465945c50460303542c01032403c80f0341e0462411650f0790a0390604001e00642c50f0401080c2e580207000c4140720010301d80168009542401050f0707004c0180725040204203014040a280092442c54140c071000726551403032040c0c10801403801c00041c400d900c18062041d610100a15550792569030b040c8a40d81e0340c01c030700c4403e240c035034000881c0d00e8040c400150b0013003112102d860b08003d409658082183c00740034a074183d13159603000c105240c0005c10800e501000d60b4441c490005103981040d05010848100400740c03806212460740500c4181c1c0c940351812040204028a44031072045440d040f800c041ea8031201a180d0301c94280c0c040a1203806410040c800d40098810040c45580c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 385649010 1250 385647760 385647767
    0x80a03051f030305040e0709080a1a061c0b0414030d150501050406090b1e040611010b04021606110c030430080406030b010905090901020d0e060405031c090f03050306030d 75
    0x202d00c001800b08204020802c6403100030324045900c01000d09240003420369608010b414041c00c04004c0701c1170510150185040c080c0368681642003142a1516505e00700c107011a001d5500200320301130210380311100003500304400e03010424403264007001680d884092010152010b02a481e0101c4400c070400b042c0410706511035400c1e10304441ca0b9582d2120b10600d058012099a0b000903c46601442801c401c0d844c80c0115000810003400c141da604152012a212041e003103603440341d0554811401048048003146c9000d040d40301240c0c00500c0040c80d080300c0e9a5044541c450395541d5a00da000209001942c204145000c1d00507011900e00441800500100454100ca492400901c0791109110502c449131082c0e00c610440d94040c1040a980307600c9800164852204590300a01607400040c03014428041e07000d41c10305c115010008100c14100340d520f86441e8000c2c20401c441403001d040c100c000e500300a41082841c2c035000448540f09403514140207205034401c44e034041c040c1c413510140751409840b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 385650260 1250 385649010 385649071
    0x50a05030d08060603070212070804150309030518010c021305010e07050c0d080c07060e0714030a0c030206031b040902040e090c090c0a020307350412060506040603080a0305 76
    0x1e07502d241140e660141005159000900704030114420401c0203000072400c00018440240501e040329120752502e01c0140e03c0d6091402884100350a000f4190700194003c025184c01d03002c4074441d07041c1c04104000407036012114101c027a5000d2011007044850b0b001c2d035072240341624800403c030421962020000d80f80e900c1081c50103405540074000c02440715210706001c9400051585000e4501941510345401340c4010b4482d494650b00300070004c205c1c0c0006101080c0340080d068021b40400c914a0320b4894a034101848042d00030000000040c07420000c044850020080c013800c629142c40c0c4908042000b50014000c001a81c4a8400480c08030000010104d80b8690010031380001039a40c00c0d0410380a4212801800c15031006104620020b07424002c42071641d600c0502d4a9503035002c44502124005c060013910011010802060100e0541d00c0683c4403800d801450210709911080c02040003072151b0703400940000c0000c42e0394070f0055070541046001c2d04000092804003180c100f880f80070300a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 385651510 1250 385650260 385650283
    0xf030b0a090e070f031a06010e0405190501120b0a0c022a0a06110327060403030c0b0c0a0203160807020a06030b040506040203060102101a0a0b030a051e011206090210030204050a0503 80
    0x10000f204041b0b854006500340da500000603d0142c0498a0b10300104060358029220201c1480480940f9803a08010b4030519006010480341c0094100554941100e150800b40c0041030907903c45400410080c0200101d03601072070151424103c080622044105c58560503080070300c500340240c40003c4140c07187c01c00c101c1c0d1034030001c044d500e070501002040000c04c5801c03c2d840d80554034462001d19603550500508025400782d242c5064400b10b501d49803140000080460310040802d01620324100e500006480d00001110a000d443c1d4045082190f0240611130380290b018801402c08142c1c02ea2603040758006006c00e650503c0b00d13403101010001640412a549030041e4045821603000c03503d00e400500a0002020382101a40c03d1240403e086035050340140003c4030002007400380d000710303511919500110088081c5040c1d41f250000c000e80d00c00620908025105c4441d0700400d11402e5030043c00d600c0d5009000340d0a104240e00058003071342007441594410300032030a0000c0e0605021500d0204036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 385652760 1250 385651510 385651523
    0x10306260106030c090c020f0d022d0102030106110d0309200f030a050d020f0c10050703020f01140a0609050c0706020f070501180b0718060f030b0a090e070f03 70
    0x42100380c014081424544140c03801d6480c2c420000104a403d0b40040141c6000d8401080000105001914000c466507042595500881c0c0926460758003040588090003c59401c80d4459200401c0b41c040d00d20300500e071001c0f940300200000d0541c0d0071660141d034a10b90a025101d1103010401d003941224104440500100c0c20030300c040c042c0b2500051b6019041c8001082111901c2200010a01e0a007124004681c00c1c0e01c12040d149031540c0410415171840130b4007000b0318110342c8c07280c045611480c502403620203216020440408040c003d010001c54180100000c0120020b500c103001481c1e17401391891941a0321384000840c40c100c1500a0324890412048a507103060550b0303950304029032140c001980703280c5090004070005502800359224420840d07000c03a41c021805d0812150241c800390089041c0810613180015440c6808503010886e01c05051228008a0700034040d00900341304182036a22904078440170a22503103070750280b503940911f681200c240c03c0d00c0320300c454211002408080c011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 385654010 1250 385652760 385652789
    0x905120d14070804170c0d15111b0726121308060a050a110405030613081e070507090608100e07090207060515010f3507020703060506010306 62
    0x894080d00600d5095603011030356500e015242d80f83c400c503540050700500d504103440c03c407460350010200524500201d04480c2a401d1440035501d00d62900010b02c0304110942d100c1005403010076100055688640d80395000360891194503c2650300d60225010700003141c14003550b102c0090103000940360b20303060800e00034500900740d01c4041003d0342010028030070310403030800d010541207002d03c0860700825082401065500b00b0013100781c1aa412440007107414601407104100c25600000c40b99080002d40c0c107181d4001c3e031a030802ca041c6105d10100242100c5140c01380903614001500145480d81c0100259002c15031140c21103026503080d071003501030780e81c403805a041c0e5010180d408401c401951500b12890079036a04003080c1aa0088003096800036943c0c0e00300316034840518813900e01e551003440c02ea40000d283c9103000e0300284919621904283c8844019000d409005400e20000e10b01410707000903520301100c0c002d41d684920f01040f1844c40c140004510030b035000e801408103484120f15032034503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 385655260 1250 385654010 385654033
    0x40308090c0105070f080d14070e010f051215060a0905210715050705010c0e011707051e090901170f06060d03050d020d06090b040b01140f0a02120a020607090512 71
    0xa05410305c03001071343c15000400040547d400c1600c104803513880c2000100303003545030041000c4c1c8880d0a0113005070501905494a28a0a500c001214640b20350782c403006513107403500400170300055460303c150381d044480080d403d8100c540000038041280c808581d54a0f2400048001c159040c101c5922030695a000728000e0105101100c40300c400710312607141450402419032525800d541c501201940412074040c465100e650340030882186105d101c9491b01960704020100500900c5280500a116940884160340e1034000e2070848403071010040c102d80c0b5558541041c007a5000c0000196403840c419440306d00302c58000401e00318860f80000341200001c2049440c107680300e6204500c02c2e00074a500300038285600b1154401d6030007904c6141307000941e6000c1d42040c001241c02c450b0020303043c040b032107258004030303102c070b10841d034000890303c81c00c0351200354554040c2c1ca424448180c9200c00c17100491a2114940e00107950f074421070700d95481104e0990388200348907255040d40c1075800310760410fa1003540c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 385656510 1250 385655260 385655273
    0x7050f03061305030c070608010f09090506010b03060102030f0c06060a0f0609031506050409030c020102100b091302010905060f03100e0f0a0e0f072402121e040f080303040308090c010507 82
    0x10300c2c49020310103581ca00102c0c18003060a280b99a0085004902080014006120322080020241100c402d00b045060300c0d94640c0c95542c01c05120360784c0e02c00300c004001009640709109035644488604030443e203889820760800c0d190001140c4032405032a5080b000221520036440c00800c03942c1546408a00c5825500c46000f80211001e0081c80543c4130540000d09031114441d0040182c0a13aa0301840a5210f10009041521751110864840d040000c040b00550381c2c1443c5d59081013203800c10540c0f0700c0e824030041c0c6081c000d550103e90711010110340d0712100c4205d900118402d1000311400f48040b521030803031800c0018151035024208068200092444015900c0802881c4c281406c88401e012040380e00c91a1941c950030010b44c1c0349810840d907000007003101800c04044220300141c1210700300c00d9800c07141c2e4000d2513000c0300c8202145409028100302901101c02030708143c0420800300b80c80b40070f021390380d91042c0d80450000f084840002c1031310001107402c05444605949851074885551200c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 385657760 1250 385656510 385656541
    0xc021302130b0706050403080907140d050a0b09100b0604030c12051c030b0f0907021507212403080412020406150e100203070201020a17210907050f0306 67
    0x59160388440404030b000b681030000b5200c441e2060f0404500781c80c1c0351030014180400540f090b10140d02841d401d2108480c9541108144501a640c100c2d41030498205075180c0f80c041d01c00a007000d205c0e1024800c0b803c4011030000341d0106d50700020320184840806214507846240302c0030303090000d002c01c284000b210340c403000d9140d1750090088401c484d2440150070a95040403101c1e4011982e694100035050030304e01640740e4000c030300715400c09a501d0300c041c01a4071001840108521501781400207180325004142502501801c04502d03801e0080040d0070343c000b4814900341a0300e43d400000c2100c50002d800c00c1c02000d503076120f15903904181c54244c2c500d01c0c5d80e81d1401d0880c2e000d80c5501d0046000c410300d00022504000c0c55940344003462a041c18020324150b00440c203011500f0401040000d82d80000306424101d40c801000810b200c40b50004820a00510b44c090401410800c10014a44035806440d0300a110712820703104403650300e00800101c1c1c04a04441070301600040d0001c0c5000300c021820 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 385659010 1250 385657760 385657777
    0x103050f1c0806121f020409200d0902061e31090c0306032f031507080402040e340513050402060412120206010b210606190e09070c021302 61
    0x200c2d034021103d0085e03806800c05482226503200d6001c42e0401050031140600011510300d02162028206010071a40503481340038a43c4051507142c8071101d04545910086861590207120300011030300100c00c1c0c1e080164480800b90800849a0352134030741e4181181e800945401c81040201d650501c1c080200300030f06407600808080c03550321400000415000014042441d0111040703c01545888107490145240c456495000b9031200d15051044440d01c0b5030039802c1b221a0a2201141e0307120310000d0090010413038802d0303141c043c254924112140c50340040a56256000b40000000400c800c00311030070859114142d8007840a00b000c0305601c150703a0045070081d0014140e285006e0f26010120790b40104802e00b00c903100c0b0000703143c600070355040c071070301340940068007443e072624100105e040a500c603940000e0b11002c60010220f11035a07a00400c45101b003103a4201e0090300c030900040504020003205685000e1403e81d80010182c9100c1d031107810142d540140103000d0006c195000c640203401c1810f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 385660260 1250 385659010 385659013
    0x71218050d14030f0a030923101e02160204050a200d0f0c11011109090114300708070806010b0d0609110306030c010806101b0b0103050f1c080612 64
    0x284c1d2422805031002420400c0807071300c0100d49036100e441e20010741c13030300d0100256040c008000450f84080c0d0110b19002d1656175000d0100d03007503103001513866460a503000e00791070711480041d1b0030880b404043d0744134409500032601044a0340e01c44401c14103440c007041e003002c0040c41e219940914445100301404500a51400010f0001800c2c0b14030000c907600d40071004041500101c00149500b001d0203850103040c440c0120030706046201d808a0500c00d8103024510b070229001c854200c81d903c521611003200c0740148140212480401e00c002c07003890100b1071030f003924003410102041c0f0100009204003110b09c810020030032680f070314014000e02c0d000189452405d544030303030300001d41070b11502030340050b099901c02c069601d04201e004c06286c50143c00c07150f0306100f0104104095640e4006140002402c6070a180c541040c0345080c0302e6942c280e492008240f28202000402400f20004824030314091001c200d030140722150141c1102815003181a40010300110005401741c10303c0900281440060030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 385661510 1250 385660260 385660267
    0xf050a020304032907020c0303160809040f0209100512040b090f060703050f160e06090102070b040e10050319060903050904140a05070504050a0306110906071218050d1403 75
    0x90b0b51140ca03503182405000f449480d0400c13080c6242c000d51081d40c101143d40001d080404026010a440b8000c00d01c4003100751024038a0740b414003060004907040103100400c10816004c1084d04d4100035041240e11501500201c071040c03c540703014000f01c600030101c9213000d903202c1d500c5648602c401180246000070a006018020b102d95408000705402103001d0748004c110340c0740c40070b21b002da000c000070903220349010380c103909012140d0000130811321004188c81c3c16968403580b50050349049402c0d41303c9442d0550002d1b001405144640d1260300504510301c400890315968000c05584054030040e0300140380c0280c0c502000120103500c2140c3e440d1090a085003044001c10002c0d0032070703160140c0c80c070202050101b040100a028411603901c01c03d141019400c15003894045943d2508601006040710b80d101c0c600c1f002c491844c0140d071740c01200101050342ea114146416401c146c4208900f401280c556003002ca40440040044800e80d0701c040c08080c01c0d02c0316600c4403184284140c2d840d110b580002c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 385662760 1250 385661510 385661513
    0x140d02031513140d030f060509070c050f0307060f0f0605060316030b1c05010c0809030a0806030102040b13030620030f13060501060201091106190f0527010e030a02010f050a02030403 80
    0x2904100f001c03e0072600030b0640102c107a480a4241c2d0765002c03600d001d061030080240036503510a03022580001603440c180e455070302e1a01e480c80c40c0560092034404148004581c140400402d030300001c21300e800d4200305104003985102c0c81001e0380e4150241c258000024800555112088400300c0d021001e00d240205400c244034011903103a200c2c43d820300384034101e81c451400070b00900340a5103e50401e240f4001c102d500e0085020b41d201d010300c88031181007110f00d001040c03943d40c0035015940500b105809a17503884500d02d2804081040781d11089036058184100300c0180b681030310152424964000000b89950b8070400107071030400300201200f10f81d00020f40440040b41c0c075031060754041e0071035800020f4400d40604107580301c1490b11014034800e82c4104840300c00220801c0c01150710f6452420140745441b6058401c1e1420300401d10103904180b408440507444002e05002100c1810017a250b00301d4081148080c10b0300c50060a4001e404191600704040500d481040240340200f610720641e400c2079107a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 385664010 1250 385662760 385662773
    0xa2006011815060804060b03120906090a0305030a020a0309060e0a090b010c202d100c060f0f0e0d0c230102041706090a05070302061b06070207140d02031513 69
    0x190f80081001074000070402c400c10905100e400388001c07080f0000c0a0035805540000c0180c4109450f8034084c0d800412800a5511902c440c07901441d80201926182c3c1210318000b96220b56050341640007072980040000d0550103440d41541d003017000b03040b03001001e09261440c0090034201640e14100f200080040021482c0f10364a030710b0b001130081e803003180500d80c04204021080400341e08201c801c004403120401040d40c0c00b0030100c03800142d8140440070515203003942c0184048401401803030603c5040c12500c04582e100020601c40c0c07100c20409100e25043e443c0c2d5030f001940b0310001064504072540082a400308000c0300308101050194101840120710318207a0b007084d4001461068003a480c0040000248202a448060140105a01c1406454081d0764820520000e406400b0004603101210000c0000c00c03841d20041c01100c1c100d040c21000250303224103512403070300c13004600710702007540d80f401440c04010190010b00401c1010040c0c1000403d0f1000074200c9410108038080207000200b2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 385665260 1250 385664010 385664051
    0x5030307030c05121606050601110313050301110403050d080604060801060305030306100806130f021611090f160e04020904090c09140c030c0a110609030a20060118 72
    0x30039034030407944808503d001e03031400c0e00c21480008000800d100d03244c2c6100400180010fa80d42212000c141d68450000583d5042a1804082100d01000680407600d40c0e9040d842c00440b88260001c10401070a00c00c00003060085000040064000c0a00581c01c584907108158000300c0c001c1000650a42e50101282181d005074001c035859003020041140034038041c4041c6520014078104441e0b036142c007500281c40301e00e42000103090f4582e540981000302c8920f50641d042c01c5544d03091041c1c0e601d0927051000e840c00340100107070300c01c0e40c000c0002a510400080c0042c043c1701031030350007803244030300038007e8901d0082140c103113070419030034080fa240030380e0385014940246014001e60080241003014400c1901c8003000140808401b403001c3c404d50500350350441c0c0d80180444011074641d21380003000c81d407400081d40c19983e18031901050040c1420044010000070f40c0d1502c07540c00740101628203010020030b2429000b580d4000c04010400307001050072115415400c4140010303a8480980100080f00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 385666510 1250 385665260 385665263
    0x1406030a0e0d1809060f06140f0f0316030b09060d080d0501090605090a060e19090b24010305060f150415020705210a080c16080d020601150c03081005030307 69
    0x1c0745030700030152120000540d18050000c216083c030045d030a00c68810b24071000752151104001c03004200554204105081d035801c0007140130300b80c0d80c5660281e50007205420a850002e1450346070803440c18114000c0c4102c10456802a0a031001592041c0801034803600d0320905a03042d04080208030003608241c440c00d030103480306500005605060209000d24000f008007140c000300d28050341032241e20114010b8a61105052400c10203a25070200d9803c0541586100240700c81c5e031480034000c0130080300d030042e584c00740800c06007050820388800440a441e000c0d648907801c600da8101e040580c0c02d000c0760043e8500030890001d0b28003951030201c101e40610101c006401604006402e1029190800c1c10a44648600c841c040101202d9040b8540b944400d03000144920b1001520440300a0280850a4002e02000c18051a56501c01d031075500d03501d0705081c1400602810001040441203001000340c0704038203580342000006981d0b02602d0200010344490340c04840040c2c0090725135820002080b556 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 385667760 1250 385666510 385666517
    0x1021c021c05042d0f081e0c0a0506060103060f0e0901020715050405070501140d05100807030605060a050a0b030112210e03011d03180d08040605180103061406030a0e0d 74
    0x1d40c0400e400c1c912854040c441c04001c104092001000321703220030072000700c9581284002d07968201034902c441c00c00450444400306494081030306d042e01c0f000031404c0080a40680c080d90802c1da00c0ba0011000c40701c82d806401d000e13003582107007880881004200c07590f00404200c0014946600e035106c00a916010509100f480f50b2280e04000403c0414400c100c01000c007030030305c01c50310003040c051000c02d030250030100086981d0700c0c1d000850510145a07281c00a02c0d6607401d81e5401034403400c0440140000b15015409401f4080d00040c40d814005152001c4554a0346010f065908100029900319801141a00e8410351119139060001342c0119140b4a801d0a4840c2c45d40e03c6c480300141400e546c482514030303101902000f20400f1404020040f1599003120104120522981d08000703441e076681e07034002030300f490400700d804942a60420000c14103090b20207982d81121030120011400e440c170030b0043c82c1455002d024503403081d05100e03028680203280f80a01050300034042001511308000300d81700c81e001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 385669010 1250 385667760 385667783
    0x60b0a0e13030909020f0301060c0c1e230a0b0d09080d0b01080601090620150c040602150709033f11070302090103020105070804090c05040609060201021c021c0504 72
    0x8060f00700c5400c81c010603103140c040d030504003a110880124041481044248408074000030200140421700d42e0150846106054244030215030b01c0488004500500e0106201100e01d0503c1c80f4103100680d0380190300412840569040c0101d51250b80c11aa044403c40307511003040070001002d01020f80010607152800190040c1440001008000c002e02428140b049030082848980d43c458070352130251210a035a402e038160b10a00e02c80c42c01116100038082158100141310408892400400442c0e455500726228240c032020341200424003030701c140c4041800544200001204070070a07c11010703841c400d130010f484142c0c0d11620700400a0b14004000a0b861030180d004a41110784102c15034098801008094190307400300c1d150035410f01000c0c2c140000899442c040100310000c8401500014105014803280060040c103e40c10600601000c5021030f007000c24a1407052094500040e040c810b08002c00c007003094600000d41c498500602900c1007081814010032042c083c0502507481039000841 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 385670260 1250 385669010 385669013
    0x801060e06091e040b130f0609031709070509070306050405040b0609130221010b0a030b0a0f1103060f060c070605030a0b010f08040605062e021b030a060b0a0e13 71
    0x1c020307000746005407400e8110b0103000032480303d0421aa01030741c8141d42c0300c51911420701240790480c600034010946110078602100300005d5401907103030203219480e801c040742e485040040f401d5070200d601c10381640c8072040412807071074004130700c030b41101050600003000f58503200820182c4004440c01c2d180401d65000f440903134142500160380c1f000200070510701c111120341c00108417161120030240e1104031003d089100c0e070001e42c003005a4007001002e4111665882c50304a140003001c45005190a01d4411420420400e5005140c0c0e1100ca03161740c82d01d90b0b6980c2c000c002c00c1070f21030b03c1040e81214040c0709407283c00c2e130b04100400251070b064480d142c43c1d10701212948143c0d10366680342e41c10003951525407440c683c0c1141841e0380241d800000403401d0794444000c552a1a8000586041f540508445402421004d020020001103039807c3e100c8280784148048018a2402d60098042d40300c200240089800c6610500010100400d09a202665042d03106c0101e84195985c90703009402c15403160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 385671510 1250 385670260 385670269
    0xc23030c0c0a140105071b12060e0601030b041b03150902130207030e06030a110316020f070e010501110c060a020c0910030803040209070c0f06050a14040503030103080c070801060e06 80
    0x88451604454104050f030500c1103566011408000c142e051003404518402007210004840113500b003640d81c044c003c140da6851021012002c50000d0300c0451500d104464505c60100341581601c0d08080e048181d44c95541e0b41080c0000690390764010b5107007002c4040005034443c9983c244403801e500c00030800224030f00400a06560200103900454070402c01600040d4220754015803800086810302d880c2da03a80d50520001d841001c409141005000082100160480f445002c8804540d42101d0400c20050440b50f900c0b4258011043c0849040c001040302d984146e011074144070107001607400103681d6001148031034122990f2040540c100c24450304050410100c0550712180500310800d406141d5240d00d0200d10000c3d0002c0e00030ba949100081c0c0c2d0b14040c1100888081c1d000b0400300200315075081420040c003007030740c4100c800c0c0d04120742c002100e8400042903002d55040009135240d6469039960640d1988005000150380c010b01800003211402841a80c006042801c0610f04070304c0c206c420031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 385672760 1250 385671510 385671523
    0x10e01020307051209030319092d09020d15030b04020907050a05180d081303020906041e0c14070c0602060c0307020a0312021c0905070b09010f0c23030c 67
    0x450440d4001d2040c1e4022940000300401204a0146110703518075507500442e0851081c103003040c0c0c060034402c9a488500d40d1140d0001d0890f0b02c59003144101d80609035542519010050760b100300803903202e506004000d090350003071241030f50494002550a400c2240206800c0d060380c810740c2e0080d81c4004100a50614180e0356a0026080c6043d601c1c1c068007000140050052603101030303400e4549920344041d40c48194666081640103440d40c1c1e214000302840603210112030000f00d014107004008a6114140b40c0a480c4902c66420a40c41c01c804010400c0b000500300c0807105010007003e915840ea81d920359000030071440d8004c56180900074141480645032140140400140200400401500300d501296103480d45915140505903000080a040080d00500140c0001d0024100005d02e07910320039802a24950310600c25a00e8160b907809400070300c4d0194954540c00701e0048404034010f00c0c0700b180801000d510946400200680f6003080c2c100c1c042074811100207941c0005000c46c407001041082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 385674010 1250 385672760 385672787
    0x40e011d01050115050715020d0f0c020106050102031c11030711010c1404050d170307020d02010b060405010c17070807062309030409020a09090c030504120806030601051309060509060601 82
    0x9210b9549000e00e21407140d102d5151320000c001c0d001c18024204140e000c410102c521103004159140d500c1105024014078103150b0141600746000e004040701d50060007000c00b1601c050f0040c60500001e5050000d4003c2100080800b6541e21401110031560000c06580104081d030755520307001340141405070865400c4008c03c010702c01e0104261a82c0c0711100116002d40b202520811011040391a01010a030000040454001804010055501d60010b2481c03080c003000c0d802401f04074007203801e00c1250301c2540559800512440d90b1200415600e043c04910740038030310b000303d160035015190158035030440c039002c031100b40c1c691b001c1308501c0380f40c01055804800c1014001c10f180c10403240c0303240c2d644914482e50f00003940108a42d41c101e405200010024031041c0028002c040300140c1c028000e281c00c0346e048810000e12550886140c0c440e45c20680315140280041c1416402c100c00c200c2c03c0304031130301c0c020880c03919102060009082409120300540950000b801c1c3c9040c18800580314a400b40c0c1d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 385675260 1250 385674010 385674013
    0xa09031112030a0905030723070608090c0f0604030507030f0b0a0b01350f0703150602030706051b0d06030c0621050c040503030c060603011803050720040e011d 70
    0x40e001d0703681c101d6080300e40050605100040d13420752071900c41e04502130500c0181010031202c81d030102c0f048060b0307005154a03465405071440e41d91076400c2900c9000c419a2200310341e52110031a1900350414400a40040600030702e1705041c990390741c4e5010b20b00101508110780d646202d90440b01045120700e4025045507801c103050025814240000340340404080340c07204500310a07200e80c00440e00d41407a0402000d00d0b4034054119190042e04016030700c005668460010303207000c6041d264000c2640743e6100b614201e41c003842ca01307007103034440310094074000c1d012040c1c2c0b02d00c4840c00161106400000c0c60000c80e10305020a0303651841c188010000210342c04401072101c90040f400c40a052002400c001010039140041c2c0c030f840e42001d810140c016034000c0b680502c80000c0b4507403880300000c0d00d10b1042e04201c0c000d21a8000e85029208d4000050070001c01141050090100081d08034120f110320050010355044280b16040005080d00e08901c0400c903165980c1c0140100c00c4026070f000c0303286000050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 385676510 1250 385675260 385675273
    0x6030308040321110306030d0c051c020309040e0c0102011116061a10020714010509010c08160204060f0e180309014d1b010509060d050a090311 63
    0x4601810642004200400b0440080807141e07000d01c0102080032403500c0c21004111030700180d010414164800c0e02c8462180c4983c800c8000118884c0c1c00710800d4030b5206c400303041040e070001a4a416140d103040100103501090160311215141c80c4101c0c081040604010408010460006400c594070741d880100340c02c204024209040f150006400401039203c2000118820f068450614031301224204661020241000501141e030010300f08090307540440d01c03040c4400e2100b005403070a10410a0303040c0841c45200450f00403031500b80103041882c1003021184141100e960004085039120740019070f641d000f10b8020710488140e84012a807141d40410041401c500300e114803903590168002e100c0c10170141100701408000c6c01041d90765200c071460301ca2001c0703140404460043d00900d100b81c000581ca20946840c004c00d0002d800c84041031514000c0d000c0b00d00441c01140e1542c050040150840400c100105404400d44a03082c81004040c10001e41031600d4a00217002030300c01403191189a0103079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 385677760 1250 385676510 385676513
    0xb07091415040b041419060c110d0506040302010218030703080409051003080d060302131a091003020316060e150d0b04060b03090d0f020102120c07051f0e0d030603 72
    0x4480356062800701d035600190100310300c00490318807807900001d107010804500082d00c88410b010180f0001422608442400b400700381c0c0842009451141c3d8002a230b80402c2c0d040030840d1105c1204564102808a203850409502c0f480d1506600340e9045006079400560790102c03020254031501130180403000b41464500e15200c00005000c0c602440c410b141e524000700d0000e6128041c00310007150312006481d22051700c400c0480040c00c29210503402203504001e0b071481403174988200180d01074114080c1d060164020309028a07200014180400004902d40c00310159030f0030000250340c1401108200e01d0300e0b08002e402412400c25421090085026600703200c40100843e00351b4001c01806d81c0000741a600020028001e010294820304070b050740001400505103001c104400c1041d99070301c8441084d10800c204034201e1003000d00080c1e64104500c0422001405203009100d62805001100c04003070b044016403881402c1100e803548226950480640211014001400c1c0400541401c00056186 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 385679010 1250 385677760 385677779
    0x212060a05120c15192d0c0f051f0525120c0e0d0f020405060f060702060c03071a010807091406040507090e270607050a0507110411070b0709 62
    0x81001c0c0358421003000c0400c200d207400b503800b6100c01c4108818003160740303214000c002e0b0011b40c0c0500e111800d202d44840b016200c04400e10001604e000e0b5503182111718605407101d0900101000c011101070140d4110184014006c240000000188102c00181400c1ca03007211824601c0d402201001c042c44c80b000080c3d22500446540c86001c10b10f03a000c11065003c4c6400c41340b020080040b07903805900002007800703000c64032042070001c030301c2541c00308055181c0c1c1c010006d0342c0a41e0b0142075840682000b5800c014140f02020340100310040c0100d9003400065a01c40d0a00000c0c6650180003100100041142034003c00407980104a101400c00091810170303000702d0700030f600416441c0034548036004610424464404500202050059440d05091452504000503040c0642c0d0100f420243c451100d82c00011500700d010ba5256100d240c900403d172001504c040d000540183c4008558807094138550302c440c00f40842e98180f20341450768464040c604020090720145c11001040701d49031040c001140e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 385680260 1250 385679010 385679023
    0x10509041407030b0a090b0f01050a15090b07050609060a0b130c0e0d080901020708030f030a24091d010e0c01050c070918050708030a0c0b04020a090212060a0512 71
    0x104140901e0055190036401480c000495200400c031041550402c00900c0c0e259114000340e5120340a400c0c1c0e80d4032034442e4010000350a0140c240e1104441d0010070071103007042995502c40010781880e120f095500d0455801a4000b140c003580c0b80d80100c410410304846c21b00000f5880280b01400f00030003695180482c500380056074000c400b0b03a60740c1c025520168003980c030720b00984500812907862500d0f286000c43e400e8100440b4a170151180c00c10100c0c01a0011003901c00c00e18083c1122421551031880f2140a84403101c42e0203500320189120701c00303d80020031810302a0007103441c00300d0400065240d821103102c03900c18111040c0d24000c0404150300011610001e100024a0210b490700c072440000350402803940e0000240f075140556500f0901e555103404500300e80188103035001d42d50b441c04415264481c05d5003007000100c11204076000650f410304002e4010380042c082e2441e05031036184400882e842a9541c121640d202e0382003120074030706002c00388050310050390b07a074440110700f10107a80d8440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 385681510 1250 385680260 385680263
    0x140a06050f09041110030902030d0309110f09041203020405030f0d0f0306050607020d030e04020c0123010e0f0a0207140c1e011b210f02010c0815010507050106082a030601050904 78
    0x80c0c003801d0b0748200901c60b1f00020140d58004080e10a14800c480b009401000c2c2003508443d9141114408101c915140d069401e4400003c0c10170500c40d40d0301d03522243c5184181180700107150b401d20020800d510704104c1008021030000060022070515a40984074010141c0400d0805041c40070a00490304c0c2d10f01582c0d070640c1d041d07074444144812460180c4d084001180e105030418400b1840040e00041500304004962002034000d02031001560480340c4060309006002c1d00e0161540880c0840d01c2c120179043d800000044010304283c1150349001649881c01c0d01004294000210490036243c42001141c2556034018201607203490500080c1050401407200105520305444070000c4c400c08002845020f140310816039100180fa03c0050542c01c9542c0d40f090040d8600080703000c5050007484564012081001000c00c0d1045540044980740e01c1080308841c10f548500f00000c00035410400385101e40700304403140764541451820003030b500c034a00310102c2c400d501c030500420a0343c58505081d504517 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 385682760 1250 385681510 385681519
    0x80310170607200c131d0c0108130503090d0b01090b04090b01060513050307060305041e202709010b0604140111030f0a0512092b03140a06050f090411 66
    0x80300b83c12103604180b43c030004641c0040342400011101c1000b5844100d1646115103c0f00103e0108096a50744290b12281540403410000c040b03016410380030180030034207200760f0880345000141030100d8001d2400080454048603c44014041c200542c003505000d8201550200181400e03a00c50441e025010f00c04c15062102c0007031441135010003103500d40d001d400301800311840740f503448a00400804040b101944c3e85440d0f41048414494460060306415030440f0314891803020303074585088001d0300d10041e65400f402511020844900070b0b048548034054060b9108400c1c9800006142511080c82a89208040410040c40f03152002c0d01700c1e115080c420710346900010707200908036203180b140038520b084801010440800180c0d2200041c1035104402c1821484c41d140d182e5248e607502c00c0b001054501d640b20103105400b0b080091600341c0605418070300418040c4200000c4d25002c0815590f008106440d09030a00903403d08c41e01200c0252410340c0d20240c1c9141540303901c81d00c4011403941c42d218 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 385684010 1250 385682760 385682807
    0x3040320030d120f0e0703171207030b040207050f070f0b0a02100905010605031501030c1a0d0509100606110105250e061c05041208060612060d080310170607 69
    0x8849213030380070940442078000100025060380116503607411b0284002ca0f40c03082c020504c40000c0500c2e8041d15880030426540e80200c0d01d1b43d6100b6405010303c4409150480c0e402d01900c000300c2c100b0010904071050200192019a0600d0b0f4007440900b51a081640c443c4c1c4200203064090781d000410b624840030309680010501c001e407030040d014184a078032456040c495500000d08a000c1040514100c0e4410005415020b82d00c0c2070801d0305401051800080140a100c01642c410303240d001030794403200440540d4130014180380440c04803050b0f070308801d0015240f54010b5150150034403441d600400d03410401c0c25081080d09403201959117580094040000d1040b0107003c540f45e60056803190345498042103040d08086004100401e4210f4048d25800299004803011034082d18a4600910010b050107251070000f03400c808036040050607243d044125811200082083e9502550090b044160341c004003611340358812440e1661418405019000310b408d0080c00754203c048ca6070f03c2e14144404001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 385685260 1250 385684010 385684037
    0xc072c090f0304080d120b0a03020d0201030603050610050f0915010c0f0501050115030f09030e240d0b0901090b0d0b0a140103140d0305010533070503040320030d 71
    0x40c402096040c440754403000c0b81c00700d01d101000c10a114410102c1e60b407416001e0711281c1e20000d48509800c0b45800001c034500070320141c1400390100240e07074010304011403001c0d5070741e484500c0c0c80720480d0712107549040030764140558036108100311800d02c1c040b00c011500d07082c01e4140801e40c4440e50302c814180700c0c46003050b03000c0100d0411685d40098100300204055a034900c90350100f68061074901001a01d001e440541104041c070840d05d14540660704c6030f280031820004c1c040c503040c04509024101c0c96401140c10310b01883d40050221400d40709000c181c000724001845890901a0094100c49003402504441d0f030700e451080d00e0509402c08003160694545810400040464901e52042503561078000b02c141f1500004000b40f103442c042c1262814400c90f1f0041b81210020b00855605c180001c1c180510300c0681940c81c403005001c440710038104000107062007250390100341d044a00d50400300d010414001e2180c4000f440280c0c0300c10381c240e4004036600003034075205810041020300034002003946 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 385686510 1250 385685260 385685263
    0x3040b07032105040308010b130b0c011d011508060124120c0e01080934080307110406061b022107030302010f0e07030f03050c1002040b0c072c09 64
    0x40030b800c01405a20b1450065010039000341c0b504a8058020405010001a42c0510301e400c640f0300c0ca05034101e9075412400c109015845511a11110080791b48440c61603580d10703000030070601c1d001c20400c00060655030400c0e0000400d0342c1d0b90300600303d40d084200108a010100020030070007100304c41c450a4484040501038500e01907092110600500d0600440045500105075207584402604c840500e83d690307411240d43e6091604c402903e54901042600c11402c06c4420100b140e030b10000c0750088251148115803440e000704809888030048400c03c1c040d182850721610300501035900e0f20010540c51201e144000c1200250000d015400300000340002a1016121814801032002a00d00d050381e03c2c10000c0c0a808a4907020105529015542101c032800142c00422a0f13401018080c04074510740302501c0940051080000700e01032541141d0401845100a0015003031410101d900c030140101072501e4401240c10808140c02c89042201c8911a106c0642424107841101412150780d48202036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 385687760 1250 385686510 385686527
    0x607080712020a0c050f0309031e01110c030711010c02061605070314100605040b0a2304020a0507050c090105130e0a020904121403010b18030c100206010f05011103040b0703 76
    0x42000c2e101003008064543e1014851035500c0c003c03011644415209024551684031301c500f005d03031551100c810752160149582803003000008241c000a211044d050442c2c480d0392201a856030103820000740b1104004100700d00301c1040340c00780703000303800003405a020815a00c9034020039040100c400d100c81c1308108007040b5000155030b01241d021581465264150380d9489034240443c442c0d824444041002d0802d48244500c80d10001c1002203160321b05400e60303100752407180d14030a4100c10900c0408880e02c65000400c4011030595410707644605908100d414222002d21040c840e000000040000fa40e81045a242da0ba518020001d2501e800818462520781c0740800203400c500d02404001c00e04c810001418041606503e0f01c0602c2c2800c0014034800703100134016003109040602121400c41128234040301c8100e03020301141c44070311140300050360441d070345080400145e00c070000603c04c600908207028004c19080c20040303440c0c841c62900b240c40780030718018400700c2d00022a020081c540701c0d4409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 385689010 1250 385687760 385687787
    0x11502120a1b020409120f09091b1107080f15070e0102251814060d03080f07030618060f060203090315071412040c1a0306150d14090f0a0506070807 65
    0x1283c850081b821b006042010b143c4901804910841c0000400740c40e54040c10b0501031007034900200d90410440309480c01c4040d0340e01c0707182d64030a042000c40e459400304154880303161184000d1401d040b141416051b40180180344504020580c0c90200999030005900c0c0f10011614440140001d60400884025051030f0321000068404c42044171403045503034080e0320f0b03e60740c030000940b15a58840c1031000071119020010005201d000024003070100f141002d44e00800c15280200f41260790300302c043c110340015506007246581d1a00104001c01c0300a00c10b000800090010710305080c2c600d800203031640580c08000c200c04040c4d07400038071480e102c0e288180704415070089040d16000907040108240008980c2103c84014030b80b00401d00342a22400e0480070400c4104252440d074440b01800007082a0f0714406010304424050404e4030031071b50140d800700340810071000da140e1800d421824074000203c0a4107480d0f0700101000400300300c01007580d0703a0105407800e03c48125218501c1c12214404032409 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 385690260 1250 385689010 385689023
    0x90712110d050405010614060f070c030602030103060209040506041b05030a060b030112060506010504030c03082b0f1401050a0338151807030c05070506011502120a1b020409 76
    0x2001c0215458541c402800b680c007810081001548488907a000c14180000540e40b00d0b000f4013410301c42a05840040c010103108441014086580b503403150107130380081c0c00494855801203611a100d060030f104051740254101c5d018494100468800070607038481c0280c00c0f0802c20000f0014410f16800d402010090401405007a529079650020500da13042100c41100c03110300b003c011449135071161058030f0590f07821038801da04a07440c5a580503056070104500c0701205e41c6445071852810200f83c0c085400e52a00c0c1c0c404120301200c0c00e03c1d02c0441e1101c4d0174a00b201c12280c0f0061240d81ca4400c1402c0a695002101c2882101c0c203000240c1c0c11006032101c02400c500c103448804070001c075010410300403010104c0c0000c030b00079441c04000f0b600001000c0c508900c42030000041e410b40c4203400001821641c1c0c03c009103441c450b602c40c0c9050510903000b130351011200544801c040c40e07040003040040b403a030b40c1d0784600304041260010080700ea2004040309107a00e00c04420b00359902d80e0b2062200c69841700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 385691510 1250 385690260 385690267
    0x1207030f0302070815010510120501170f01050c090105070302070806040c030b0604051302190b03010f0f0509070e090403140c0c01030e03040f0504021e0c010902040b0f09071211 78
    0x14260014510080c01100140902e04001501d9500020065510745403d101c05046030700f0310080c085103030300b0102d012003081300700c901c1d014100c4094402d1601a0000d105280500e96000313280515081200104000e00ea00d40800c20a03651100d500b9618680e5091034050745c0c5600900b000c900d1700c81c00360130078901c03030003003005002c200101842d0700d4085030b2140d207103102243d41e50400c2000325103049483c080750f01004840c0c4030040c54082c120045500481150403150381e00c8004103212030b042600044040e892801e8140065000c9421510041c10200c44002062611440c001c2a4180e0050302900410409001ca010980901c2a80720360141445007103403103131007101d591651100c40045290200b441e1000c483c03980040881213070242da02d81901041ca01e403078501400004d5010b8007000909104815000200151080041203411919000031495030f6490042004071500d120100d44201e0481c8030b00c01c40394a481d25841e502c85801d092a07915602d9a04200f0054000f54001500449000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 385692760 1250 385691510 385691513
    0x409210e01020c040903020c040504060f020a09050a0b070f120507150203060907020c0a0605030903040503030a080406060e040f080d11030a0e10021312060e0d050a320702120703 78
    0x10400c400910340036401c43d030340c21010304103000840d031512802600580200341110710b9400c0580116400920580d80000c1a008000328034003203800a92910001481070041080340d4584004107c0290204103e2907140c010190f0340d07821081c040c1000106034149807407041c142d80e4092016600e01541000c45100c00412481202c0020f500840d8070a200b0b4101d940400e9140388001070b800e0540501901a03c0b0003800c000301910207410090002203240b00810004c140b035241400a450b81c81e88230384030b01a0a050030700d840000c2e2403072500a80d01e418692020007000c116104c0c140c0404a802a910640e2549003c860310040c0c280343c1c0d10600031910000522818039a50b44c400c01c1c007040424140d031101c52440714400709034819007995466018281030140a00700690800218140c4200b0000800740ca040a4040c1051640200e0801291002c01c80d403c9042e00002907001001e00c100c640141d0345580c0c0d52040c0d2040907100002803840340400c00b8000c540703d01040c0c42600240004440d41c040d034a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 385694010 1250 385692760 385692767
    0xc02040c03020d14010e0c160203070602010e07090c0e060c1501170f0a0c030605091603050303010918050a0b06040b0d0b0702011128120c0206011e0303050306040921 73
    0x200c440300f5121450b0083e84070344d04c000900072505a030401e042c00540c54607a0a89064160041083d100c6411144401180180c0d0208405801000030341c0012030050000454182071044507400142c5050030000e8448490340d00101054901d0400c49401d519040440007a628004224104541c01400c1100224820030581c50540c55207100c80122030400250422154545800d080d00418000c5d079240e061000412a030410f50744500c405003220030303c5800c0d540349052002c0c903500a403941d400c00030043c001020540035038003402e40c0141c1520790414107540e8096445034400740250159030124040b0706c0f41d41c1c0340d40041e40405801003d000d1891038900b0308140000040d21014059840c1800800791801004191094010081100c25030740c1e0511030414140389000504108000e611081510070015510803601248141d038000c0070b1560500d0720150744020000d460300c0011200b09401c00000c1d41c000101d035408038049d503004c14202e0b80c614004100d40e5542107089a80400c10024813041741e0f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 385695260 1250 385694010 385694017
    0x302060c0d0b030a0f1101090302060405040c0e18040203070b120a0e030c0a0503130906031a070e040513020f0604150315030203070e070e06030f1501020a05060711011a0d02100c02040c0302 83
    0xd051b41100321004900540301a00c6900c0003d41210050004202910f805e501484080c8031901304a50180480703c0007820065401400c00b4056603e041480258281080200081c01061100d60301d04200d44004404c000802050040c807151100c1e00e181c034002003403041d2000c407440340e42154415501882d00d15203d030004034507048c00126601c40014020940c0c01604210790304505031510902801da1903c4600000510840610035003054440703082d180d510500d03100f8228004078511250701441045858166280714a110708030500085c420030302c0741328200b05454641e04000416408601c403a0340071024592029505014010001800e205540a410700c0b0384403da91b140325500c0311a08110150000303890081c020008400041c0180c01400042c403000c1d141401140c40300c80d142d51300c0314a0311404488001c0014900c0b99040292842409452121030064084020601d200004900d2041c03910001030b1260380c424050940c1d050040011640883d005881405100074a66000e001f950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 385696510 1250 385695260 385695263
    0x40f050703021f0e191e18060302120114070c150c020106060212070510020d020c010504050330070c0f080c0a150207052109030a0501050a15030302060c0d0b030a0f 72
    0xa0070010a0030b142d160050146040c4402c0e6403400c10021b040c400c0080201c0d01c0284200e82c006c610b00408103050201721140103c0000ba00c1000c40c00b14214070505c80ca143d1004849040c1d03a040540340014072404070712007540252285403031365000f48982014207400904210100c0043c1c50448041a541ea041d0402004c0d90902c0c3c007141d150f8003602c5142001403144182c0501982c104c1c01c0c110150105076001440d0721740d05441c0241c1410300100c40c81d800c450f030544085402da4000500181c01c00c0e02d801d6864111505d21100d0445184454090f5004420081202d82044071500c10030042000442c22104a40c0d0030000315526104c0c1500d40aa84901481d0252521181c1040c818a0b024803402110400b030f030b1003409802c0d6028419640e01c010268007081d4030a200b01805001e13203d440410610784480d00406c00440d480c10040c40e41d10885a2008503030508030b4482d0030505c00f01e0303000203c654003e0304400b0704582c0e5200c00070308140140341c450341240d071602555070301c141070010790001c000d040ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 385697760 1250 385696510 385696517
    0x1403130501050403050d03110c1e0105060a0b0f0703050705030408060906160e01030903030e010c03050414030f0f0c15070e01030c0f021b06070b04240b010503040f050703021f 77
    0x29a15840156032074000d0344070007001c1d40e20010044079180d110340c00042402c0108100355092a881700300540c01c1620035410301921150600504403074400c02d00070381e504108240d404802c05820140301110510074603000304884280042e00748100341c400d0080302d44181d0010103480d244d5880f880001d8a03044141e1b406d21640c81210040f903485601a4220712442c503d83e01c1c0d8051900f4501c0064019044250098090655a1510000d0b915080c01051a400142d50f00000c29240500c1d0100410060b0610300d80d10303074000c2c00b42081c444020012204d000000f900300c1600c070540580d11611308242441001000c00414091102c6242c0018007050718150980341400310040c40b0350300702c0702d21070303a1814180141c0c040444400801d1f170058814041040241010745840041d448200d07440d9802c5c0c03422110030400c460a2000c0d0707000300490384a059450301052002e50001c1000800c64040900f010308803003034800f8074104000040017620015a80540240180040400b8955158805030b07140d0340403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 385699010 1250 385697760 385697797
    0x40b1308060f01030f020d02040c0f03060b07020303030f1503011503060f090506070c08040b04120c060504050315151815040b0d03050a0228063c091403 67
    0xd50021902a110b00400700640390342d80c0c03841d00c0700e07802c03485e0402090382c07ca5020f450010140c1c07038a02034404d2401442d150580c0f101c47c0c204d402070490302a64040344601200740017240043e40d0200c1100d40000c050111000c05440e0002421000461100a207030b2562801480306031121030901c400b400c413400b809041003810412150101130341e660f0f00c8000c0c40ea80003900040c0145000d41c07202030030030340035044031410036031a1003409296902c20f8011203e803103440b442200800044100420107400340d0b01d011400c00749040b020a95501070350400c8003141c000d080000d80314240011502031540c00041001010f020303014018158040d013500d01243c102e040a5058044e030a0500401070a2400940030407000c0d1103c0d14201c4181d004403043c41c1c00c40c042c42d030000003e081c403081880038404040100c1650800a0300d4660101c0b540040141180044140d00c0c1c04281c034202c100d4640d2901604007600c54510700c02d061802803000c01e500400040340541d02c41e41c15000000036042800901d403e10702e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 385700260 1250 385699010 385699019
    0x20f070f0501030b061c1113090b0a1a0d090305090436020114090d0f240b09180102040909060b0307090908180a0e07030203040507050a06090b090a0b040b13 69
    0x1846d100c1c9501145801401008034034030310101c1d52020413003950820f001800c0c0441c1e02240401000c41e0361003000303a40d460341c008c1c0a2a203801c0c0607400007071450342051004a04204c8003800705000c2c3e07c0032010110350f00c2c841c9400f418092421a40c03030407401081000a030340c48010003450490080031200400391b4140f402e2191a440312404800950140c60302d0042c1c5e040041e4407103041d0300c07001c00340b5000130f04014a08005181501200001c41c4500d20040225100c491200b0128955001e500e03803841c1411500d51098407440c2449410031503201c0c80800071039139240a140644074030760244404502e4002c09005200d0745500040c0c0c03601003107043d204900e94804000d01039905c646000780c907100c01044050100781640c0080c1d071108a000d07000c0503030955111000c2c0c0c1990300495440d000b1a8000007007104001d402d20140001d002e040b954000000d081042c02000c1082e10300403c03201800002e03c000c291b945802c00c24005113a903449041c0e07281c0e10b440c03015040390040c0520780040400c1d80400314 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 385701510 1250 385700260 385700269
    0x90c0206180c032d030703091706150904061b050405011106011508101809021c0503030106050c030c030a05070c2309060f040f06051002070321020f070f0501030b 71
    0x190074880100149109135141c00040340b007040302c0d1044a582c0c11665106101c00b001840540003250080d201d141e9890318061603400c54031140d0b001e0401c0740d002a41086012038102c0d0303d8603400002a15540c4032503660346403100040858400208124009213001d000481e4000300070010b541c030a98034510761843e0855000c0e43c1e000c00b0301605c0304004090700020180e502c1070000700d51000710541e08103800e0f1382d0b40640c000355180d60314a00c40c0242d00c0d65131402c294100500006100d01542441c1035086d00385859450301c03030206014400400c140010040c00030355003042504d040901c90020340350b440d003441c103024000d6801541d0850b00104803140000f4655031100c00c001c58107070342030401804020303003404002e60564020f00003580302c034880500c0c8490380c03598822101140880140040c00d02c2c1448204021401c03004241c01c2150f000c08030501c00104084010700d180d9103034401400e000d040900090b03040004400c1995140d1260540001e5501640091002250400c0c1c0f0b04000900e0b0740001d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 385702760 1250 385701510 385701523
    0x912160b04080c0405091009060209010813030e060c01060305070810060602190204020d020c0115051f020c06030403020a020603040507091503030c0b1f0305150601020c010c03030b0a090c020618 85
    0x1d644640004021110604191700445c2e8444500800d50700e5541a64201c1c3c1c049400181c426600d255000c11200c482d543c2020040380c0040045d1140c074035040541da00184802d03844000240281c0000c14900343d905003d40104010f15400b03019602c1c4144c030350b03002603031f9510709000307a1301c0d8107051400c00140c003800464000c1602c40d15903035441c0c8070f0086d074013404040d5000b146000306180c1d0800030708425003001e120306900003103503004540c03002c0c1c03400c000c10120f12003030a0443c001101503103080110075000940c86000800a40d02c150700d9a41d0781c2426402c00300c4044020303400403c00010081040710105007541541ca08582c00c00c4541d0344d40c9aa6285084503000090224015450700390220310000201e641c42010315102d62020b90303201100350a5400703968000c585c00d911003004039004a0850030040e034041c0c0c0c01c0c030090101d4600c0f00c0000b028151013040c00f9062640d240480c04a80d1100d9074204040c1039801c80c148000034005000940d690700885d014642103043c6402c1c016200c40100d1007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 385704010 1250 385702760 385702769
    0xe0c0a0e01030807031707080a0614060403020120030f0c070801050c0f0715060b0406112103090106030f030507062418020c0106090506091503120f0912160b04 70
    0x1a1181c0e0a642d07510300507038400d030710a5080c045a4050030394825142d0010340e1041e07085607500d20a50030209041000d41c1c1403a0800384135540c00e000c1070342043c0c5400042c0c400700ca8091800c40c600c008040d41108041046500d4070140b8040011803072403082c0100020040703a100c40c4215a01c1b80d51b104212403c8a00c16222a100300c0c900f045181c95000461024103981401104002454881200f100c4112941984110202000401c003007100541000e203001011407210050001a0005140c41c06103400c49003100c80200710210101d03503d04030941c002d5001e160f0008049610313002c9070802900c650003640040360354a007440407014540c8040105250940c8507160258074060800f030458091900c05c7d9030400c0d1583d807d120719020740d2024004c100041000c001c0c0040d031401c141d002d10640c041c00911052251045800c0c1c00c105490000f40d010365850700c655050b844840040000c40203110785442c043e400403c1601300291f01f0000314645609841c058144844036995483d900b01c0d43c003d40c841c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 385705260 1250 385704010 385704029
    0x809150a020c030d06080d0908011e1508010f02030a060b120c0c120313030f020303010803040e0a0914070510020f10090c05060409141302100f050f0d0e0c0a 69
    0x200d519054140c0251200355a200c0030359041440c4418140e049030102e500217599588101c02296686d90031044480c044d107001c100030b102001150302c00c0b07008510280caa4130a0307165500020b103d4464008048805400380c44020b10440c145003021310041d4000b074401d401d40c40c2ca4507400003260100036080700c1c0c40140340100000f82e940e81016000d140d800c002c41d484150302031102e40520000303918008501c40c035031010320400b00050604000301b652544554031800e547c0b040005100e034142c00001d68044482e01100b00300103964841805014001c14623008202c07482d030001c0106065800301b800c400b80e40b0280c0d80c1050300d4141e140d003203035200000d07100c5e81078a811506842d0703541301e1142c0007204a01d0242d1000d407869a550070208074240d0081d48000c551656540c0d072450f992030300d0310459800c40e203c0c60240c400c17500c2680001d000c803000e402295041c0184c3c440d00b80a09401141130390300c503140541d011070b100c441034a04d84000d020100d0010540e4000c0c1400030707200e4604103400d181551003145 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 385706510 1250 385705260 385705303
    0x609060e0918070b0a08150919020a090e010b09040f05072a0b0705130e0403080127020a02010e070b0309030913090606061d01020d0807050927070809 66
    0x888501c0000b0100d414a1401480400b150000020004119104680d40c40004519006000288264040305850722405980042c0070350001c64880b40c185003c1d500300011b07560450500c0a94203642c0652100d1000700410000051240254000c0e02d11001c0550301800782711807031821401150780480d4144003013003e81405107842480410f1907255581c016400302100180c40d202c4000c003010484180000810004240316000728410700c000003099121418034040c00c050303801034410b0740c0502441c0042c2d81400510f00300041044200b1010000e035200455403840c044030002d000e0048070394000703440d20490782d0014a21440c001128865a00a806141030406250170040401f00d911412030300b15468004010102d00e03d846408014041b0741c0b6540840c803601c0840c9a00301a19041032415500403058400030f958018554070390110661425543c0d5080c410000b8540e150014040360b40c18502c0e059442c17501184203006030244205850b109855501e0344403180d0388001a00e0b02200c0410f521 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 385707760 1250 385706510 385706521
    0x50a0b130213090908070c270b011b08034302160b0901110102031611031e030105150715050c04050910061d0a030b1305030a02070609060e09 62
    0x10350240c00344040340e101c00142c496441009500340e800c44c0b0010b85950300c001404030100110311a5010040040c0c2a8024280c050350f00c1e182012034122082c00c103c540c80b486128190382c40b0f40b02000e0301820a0300b406a041c80f0a0030059515081101c4098029600a49401109081c0c10292250001f01740c5132100d12014069441c85115034820b13140254402c0c98105071080344010980c001070005080700c1a01d802212000400240c0354001c9007006034410004e00c100141e1402a007072110400c1d080c80b0700d0f8820008005441c40c0702c5c10703480c00343c00310620b50000c014107041c0c2e00840c100c410468551203801029495614188604840202a01398200d120361400c1c0894101e0f5038003030307030800c141801d140e038400104907007950484954041d40111b040a100b21074000340c591800000b640c00081c0c0c0e140300304001c9040d2140702e003c0500000342d0100000c04c0000c828660451080d4048180c9899285103030000c3e545000b03c0c01503801241e07480c040441c0c2c080c468500011400070080003c045034071035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 385709010 1250 385707760 385707799
    0x12030b03010605091303110a110f01030c1211040b0f1810080a0b0f1e090a0218040e0f010615080610080c16240b040504032313150201050a0b 62
    0x101d60224107000c40c14561304180c487c2406481c522600032501080f16145030350410020110059001d030500d45400003401303449601c5120f1420b40c9100c0100040c01e0303400060303500020702640d031150b8982240010220a401c01c0c5002415040385142c4469000b00307104000c1040403280102881c0010f42c9102c0011150755860701b004c0d42ca1000501200443e00c481d20218540300d00b040b074058205602c1d0304684e1128101f146407030398030100c417040850415003030407000402c00148648103481139440782d038120f4840d01c06000b000c62103400764008000b1107588400c4c212040e10000403203000306612000080450810b4100c8920f07040c41a03989a0041c0e9402210350501d4000e103400c03016007807600c500b00d40000e0702408046a03241003401c02d440349008086a000c00d49801c030442e54011800c0070180000079811442c060050110589170301050755106440240c14050480c009000c40440000060880402c50518014a180368020301c0540d84a50540b025181a0380b01c07507801403804000d00084060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 385710260 1250 385709010 385709041
    0x1303080417281e170a0e03010606020c042004080f120a05040512030c060408030105240414010c1a07030c02010b0d0b0c070813090b090411150d0912030b0301060509 72
    0x20040c40551421100d4407101441a078180b92400c03801030000d11701103619006480100ca1400440082c85200d0810400a448036440c0c1b8146004540300c2c0c40e400c1040bd00b903040d01c481c8500703194115441d280c2d0380100175a01d10b80b002c0d00c640f45001c0c0c80c850360b058030b00d5201205c80448a50320f40b07510b440c2c41c1c4014030000c0402e0702680c3c40d190000344003482140c8020f21495000714000d450786900c0e54104010407214107002e035a4000c1c46454036100e91761808501042e50110742e00c10b00040049003026005031050701c80030030700421846402011b03600d403410415849001c1d192076a010046036844080c16402c84020082c0661b01003040814400026000b821240c0d000000c000c0031410001c0700e640304040c0303030025540d0745d100754858002405609040c0c40740c1c000c0780c0d100721a0140682404d45410314200800d200c4580640f1000b64400e4004c200744084a50b803001c0c00c2c0b8100440ca4241c2442d511a1030341031450030000c3c0c185075940f20340d440c050213840300b5582c00a0100c0030355201d0001d80341c1c060704d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 385711510 1250 385710260 385710293
    0x9031206060906121e0619170316080d0b0f09040f1121120f0a03050a0b0d030e04140c040501080603241902041406130308041728 57
    0x402c1882c1e10130500e840c0c03160040e41c407204020300e030321103403c1c201001010080c400c0d8040c4500851007906801d0342005079003119540d00c040500e01e0101e02c1c40d40d0442c031507520400707035840000c0510410050380350010f120002c1171804c10032209103071208001c1c20007261207010364080e42010100b8041355046202442e1580300302900202090200c001c95100c000c03030515416003940b03215420102d054144640d549140700180ca462612200c6080c4100a0180040284c101980c1e14002054481203900c40380404000401000041c44213180c000d004074a00309083d801541400c203a807494940801540c0d00840e03000e080c090800d4100001140c440c00003c0c2110750500c035800d00e03001c1031149400d030745146e103411501001035440c0c401c22800248071240c020710707070441c41007204021503c00c0f00d030314144500d8201d9150765644038a084182045540d6000601f09080000d000500404e00ca00905d50003a10002034500c0d048850380850700c080b9018134162030f00e503003090440000541110300d00150700c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 385712760 1250 385711510 385711519
    0x5030702072111060f160302070803040308030601031d0c061c02030a021e04080a110117090c010e09040209180f0307030c030e1009061d12010b09090312060609 70
    0x202d0342d0780500c2200400c048084a007480c02e2001d01400d214a61448541e00c0d0419a49240b40c6000c60840c00118442d100848450943d0300ca481020540700f40405030003400a0b0040f030f6200c9403641445070b80e50740151201400300b803500c00d107080d10140c0d00000d030305078103d8000504505240c003000e100c1a544084007210303950b0201c0c0f180d20881c0c032142c40a140100400345005803298100001c0d804441038508000c9001c800500c0f04200034440051880d030f005501000c100d1420039030382c00580d4514460030700490807642103420021111000103007403150360340c2641d0384400400c2d1142400079500040e10080d401031400c00000d800c000202100c03111220342141240c41c100c00d041851070964100304d9044000580c940c0c0200d043c15440b007581c02c5034000442d40203040c8291a02c016021009a2280e0010311400071801e40008a2a8421100021010304085c403400d004000e030ba40200680c0300c005128515100100b54a80c9000003601c61031a040c07001548651950410004103400041115500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 385714010 1250 385712760 385712773
    0x10f0302090607021201020c0601060507050714060705010e0115050a08031e04030803070306050414070f08070201061d0f01060e06070807050c060f070507081b060706061d01060f0302180105030702 86
    0x1a100d44088034298174180c0001a202d030b81400d440c0e0b0070000c048c1e2081c002c1000501c483d0003c9000460044110b80b603560301c00943c0150400819641d001740100540386510300b03155080f13003680c10b4002d0120700e094186a500c1c03094650040201c03100f1540140101948103003c00301c00d070341d40f4640c003204158080783c08030309141d075075a135000d0198404c41c3d105e00080d884610420090600f40242002c1410043d402c40a5140200b00201300d9940010240f04011544000c01e40c0031f07001303500540240ca03090000421888050310300a181d05d4058030b80315604044000000348040c03003941803810384240100300a00d803840700c3e114107540e90003248050b81c07a8014038403100016654040241044034141d205991103441c5800d2050500025911440d003d0b00401c2c41082c244004207a101c420140482c0c00e19110041814200b004103180d80102d880342c1411414102217200ca1841d07503040345c1c05965415101140403200310164000d1100c42600c51000c415200384d02c2d07018401846c1d0040151040b07032036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 385715260 1250 385714010 385714013
    0x50711070909081209150702010915090204060f0f061209050d0507060f02040603060501020f07030b13050c0d080306120a08030105010f3f021815040e070504061d010f0302090607 78
    0x1d0040503580340400380c0c0709411700240381d5001c1c103c55074041f805000801c000000c544800c05000c071000c40401c072150313598213500e0441da1070f40d01102c060400804e20410307032600d4100c4015501350b2401000c0204000d0388140001031382c0390043d00282c1d64808054100c45a805001742e509400c41003041702d919440d1a000f51035496144064402000341da42d01185403407405002908285400f40080d9003174000322010b1000c030b140212460707040b4000c040c5100130850365041550510940d08180b40d4004032044048050018bc040034602403001210040407600c1040800d0b50f640308403650040106100f48010030256008204007115400070342420300d0320f41003c81140050344060154091143d091460130341c0c40e0b1040509407520000c0e100e404500c1c200103506024611821200341e28813480e0040c106220780380d83c180645005042740d83c034102c0c0b50705207001d01521a8010f405a03d0024254040c0c0015411003041680424001a1a1301d0036140419801720069801384003002d400060401c030080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 385716510 1250 385715260 385715287
    0x5030d0c0507150c110a1a0a020702030303040b0f0907082e0e0d20070504020705070806010f032108040b1b070302011407020708030f0703120207060f05071107090908 73
    0x83d4200110710009122001c030440646410503141081100e41e200c51111070000c3c0d801e0001b07640682505e110081990f50b040a9400030f8450984003e42600010041c0410403103860201130041041c1c82d980c4125a980100d6195507841c40d21a0015a5000c0c0704440c1c55541c4418050514001c1d64905680d00c3d00c00c07003140400c1d0360168407031440c40e5101d0f10072107036002c0d0310445a0503130016100c0301c241c580303004000d03071f0382e03107442c940101e510465001078001c1c2084810418100140022000c0e10080c3d82e440d001c040b07107220a4482607840c40031070400310703042c0c0d90300c0b95030f80142c0480d0b0b0319629840d07180c988440d4400c4100a1041050200038114000036549000c00741c64014800d90000c00d001008038102400000f000e40304c1c006641c030a41040c003c00760b0100c161036610484038051911003145040403540002003004091142d80f0000e001824807071603400220b00203d0b1035a05214603102c400044821421002d014860382d0011031051058071744a07040307190114015620242403048070241b07030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 385717760 1250 385716510 385716533
    0x706060b07060e010507020a02090a14072001141f0807090e0f0706081602030d1118010e0105030c090109030602030f0106081012030f03150303050d0b040905030d0c0507 74
    0x680d900008200300302000024003030307000031001007002070105082c043d034080d50f03e00064031b0081c85000c0300000030700c40800301c1d0f0000d00b03001038981550219003840c0c04003078810b1001006154846516078020740010784140100004e042d902e102408039580c90140008111a1038a510000b01c0301c005c0c030001744100100115005400400d0740001c9044100c80000c0c60310080318001d21160304815810042103070443d009690109100d055060207120101080703013180708070040d0741c88803480d1085950303280788600d02501f0040e008202c00340c08505a100151184640c0307801d8540010010070010f580d9814801c05020301071410304003150300030b480741e03240c40c20303600115500140744d5210001008480d9008810f143c01c5044414001ca00e18141a20350f240042500000307810301c02700d55882610303c2e2013940300e42c180300c09215910341010b4803481c006009620280700c440c40d513401e02521414618092050141da140c0c040d00841c501000120355002074501e49485109015041c044000441e08547c0d80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 385719010 1250 385717760 385717769
    0x10170705041815030605061906020d0908031218010f11030402041413020d0c050612090f1f0504050c130522030518030319031406060a140a05070606 65
    0x18aa180c0c0d04080121001d4060b4682c03880500d400c1c0b81c2c07820408001c00100405882d001440850603541d0100811008143c04a00028251400c04002281c0d64080380303101e000845a0364020403141d94504440d624081d03001d00c40070300380000c1e0100e80e550038601da05134030301c006090000c50707000104c40781c03c1308442d414080940d6000001017004110729180c072501070038081d10700218a003030504100c02d5003a030302c0d0020000e00900d000d800b49010f00210b124000010070300205255554003240c6034500308004c080d208490103200700440b041d10210007059514201c2c0c0b5055512400036002d03600900a040c01a009503294011045007944540314041807101b40d00c081000802e260070081c0c18030614050300c1a0a64480140c200034500203035011007120800000c0344001e041029022002a085204000000183e2135002c21801e031855056005416103900480401c2804d42d030f440207214461041c0e20f171410004000002c0d5000c0700300108054020320900b0b140c442d007484040e980340303000c03161950003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 385720260 1250 385719010 385719017
    0x610091d0a0b010c030203030a021305040509030c010b030f0d12061e080d080708060915190905010816031407031a150a03230339150105101707 63
    0x1041000391a9000c0d5442e032800a28000320340c01c0d46a1002504c9001c06400d50488a40001d1447c440804803101e100191000401c10400d9080201c2810780d40d52120645020b5035090059006092901081100c41140d20001070a10b08984080032501680c13800c9060385002d603a49000300350001c523030004600d96000d10b69003802d2641401e212a00e4002100c03464030800155008200d4441d501140f007540046060311411910b481b07400001c40c0401611801d16000b07101302d4501c0c07183c041425069001c81380349100400c0f290b6240c5030340d0ba8594010304100001c5042040c0c041001450303071103604529800f4003096540007038690380d074102510110682d000d1000c5001040c032203044600b5040784422070044855495043c6140e03900018130440307080082c0003000c2c007081c0f2411a0300074002c0f0790702d81400402511001070304145604007242c660325000d402e10700e1b08070341001013140010352400902d0b40914841060f0718000c20045072407441c1002104101d4481000402c10001d00a5240116a0b40d00e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 385721510 1250 385720260 385720319
    0x1b0102220806090102161101050715051f0815040c181a030d0e01030f06120501050709060c0b0609190504210c0327050a06020606010314010608061009 66
    0x4000601d0003030050802c1415174130402c40384113204201000d0743e0003254000c118520044590005880e01e00421078050002490a0075220010559a018910441c20f044c52a01c5442c544401541c0c019403900540c0c0082e88040101ca801e040c0c000c104983c8079100300c150324421a1a081080407581201150000e07464030f03214a442c2c600c900510110000c101034004024010610500502c803080603080e40b814581c0c0ca07401c001c1d40c0703a11030f0088009400c2080704162002443e01d4098002c1408503a0b0500103404440041001c510030070f002c030310503904114010069107400d0100226010040c121144a03845482c150311300881c0c500a06100c0c5015880d4448080300984108280540c003640010400451030130000002742c001e5600c201c40e2140e8084644418049141e99500351459080268064440c000008006600054040c031a40081e45c0c1805001d040305100307880e813031080c010400401c0ea10800102c141c03e2481005d507000301a4681086102c2e5143c00000c003840070740006400b0302e0a00b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 385722760 1250 385721510 385721519
    0xf0807030206150904020405040302010b030307030c1218030b091c08060a0b0f040311040207020406231509060711060d240303080c16080d09060509121b010222 70
    0x50200e1544110f544000e203caa000390000581c0856008100074815981d030404a4107051003540500c0c030641015007213a645842d60309000d0070815800804551400e003c041c480041842203500380c42c14640182d15116a504560b02c0540642008000300641c0c40759012440c5060902440b91284100b0354171026420704104040c0941403020341c00031001c007481003200110b12078000c2c0454045a07040030a120780b200c00840010301034460f050002e07500c40e04284004c1518900c0142d031825400c1800210490b0b004010240138030100000a810020308040c400d8102c2410080010100305110710040c0714004035000c0050600d0700b003c140555201d54a14030f04070f4110441e40810f0880f141c02d604071a10901c0c6030703001040104000c180000704507010605100c7c2840c100f1100c4507190380159126100d542c0c0492000040059038402e5407940d040101241c0c1404001c9280c0004444c035541b01490411b8035140c1c1010b600200142e21070665007000103250020b4020400410500b24242d000003c5190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 385724010 1250 385722760 385722763
    0x90a0c0c120c0b1005040e0f0606101709010203190e070306050718140a0e04020321040905040803070323070e01090e04050c0f010207380d050108070906050307051504030f08070302 79
    0x1c1f0803041c0025400240d800c0081307030340003c40340c0e0700100c00c940c60305441004820848840d0300d2001c03008150b05a00081c0400200c040d000b0354480c1c0700c455045405665822a401d082e690b9200320048039411110045c808034102e9004564005110300384a118a40a204070041001c070a42c460381c0403412000403808030740361800e01407004001d01c000e40003030340c10240c00103500e400980048040001c402c01005003282e0701401543d00801180d1803c001614190402d00e104e40e000f03c2e0703007100080c82d10344682100380c40d03a6044036044880c588299400d6030380c00d009850b0355440e610080e0500c4405000003d841d03040c1e040161285100344060300f042c2d0011428800320800441d240341c103640000b041406400440dc0200d203292641e01c3c5030400001c0070641038005841711540415050500107400c0c0c10413441900098100c40784481200d0b44681d440c018102100c0341800b92640c15086081c04002d646401b14420740301c0c66070b09148614140c2da9542d00902000b0799101214203800104412060680 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 385725260 1250 385724010 385724021
    0xf030602030411121501292b2309100c0207150201141308030c222d0b0405061b030c15060d030c20100c02090a0c0c120c0b100504 57
    0x8030300441c047c1d642032000e03400006401400c0003010481001c1955042d1012969003220490201124546400580300b0b42c800581000100440c6480080c136680b0100441d240c070162042d19018054040c810310000f40c10091b01110303400710114401c800011455088804c2c030022030b0301c8660000030f600022200910801603008190700d5112500503442404128010200d90380b01c03580c1c400f1035580700b4007101015903090b00c654a80780c100c00c203034101194108400b0b00302205407900c00c580030f403011072056540d9040c2d40d05010b10746465005120812850601c1c40c05420109102c5e08281500001d18003041e10b5034101c41c0b82c1c615181d00c41c1c210b0300500c01904081c150810030603107981032006c4854601900c01c1a8a84c802042c40300708018a01009405000c00f0501c0d800052040001a50780d41c4001e1200000501c00c0c0c0c0b10391200c0780400c0801281d44144c2c95801590b03118604440744a480d0001c83c442900068018000780440f40c0000a00f140f00f0980314800041100f03406500f4941400700f20360 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 385726510 1250 385725260 385725269
    0xb090304120b04051516030f0b0f100c0203030a09060f030c170a0b100206010513020c250f0b070c0603020c100b06090d061a0a0f030602030411121501 66
    0x8204200910926211090340c559180d001100b418158880f0301d0114a0444221078012002199406100c1d0b2908207501001003030344203030f4041c04a2505ca00765041201c01c20030000b94040a003050590441c1030000c000311802209041c4400c1418081d00460b04543c04082680000740d032401046c03020710b40122800f02401240d02d420000a544100090550703200c103126910140c1e40030b00090b00c451351640150070520406060407a0541000e940a9071b07404080c021540b01d110340406510b0b0031030323080c400c0e50200d40429009000b1040003003691500d5000c095002c1c88a103411450100d803020000951100034407144264644c0c41e90103040c241c82600098019400705401001014507020001480d6240000764020000e07070701d446070002484c9441402d1245411569040100050004603030003035a4156035101900130907003500341000b40c2c0b200c441c003940d4243d43c620101800803504030390103983e00604c6541c0b12500c81c880c110018040c00880c1c1c1c2d541c00981d010506142240101542050040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 385727760 1250 385726510 385726513
    0x120414060c0c0307031805030a21050f0f1e0304050a26090910050a06050d060803031006050c03070f050303070f050a02030f0d0b0d0f061404080a0309030e15070b09 72
    0x42d14a9030300d031644075110740501000740558954101036425212880208001001c50342c0018040c64100340740114400405160410b5051030181c06001d0030441e518100030709642403401c019204070305219041980120800c8200700395058404100e400103600450081e802003140042c1c502c1d2582484080c401d07a40c0d031024500207840304061414054419451003201c07484480ea0310110100f40160441c0e0100d0b9101c198854001501504180105680350280400b4012a501c40c2c040303130366902c000e80b01c003030281e141c03403a08100c107a00c6000a0300b03143c401c28054178981806070f1102c04840b4034000c020341c1c8540001040c0b25266420031112600284241810f504219505a001e5128002e80700b080081c00300004070881c10b40700c0d40d40003064043c8020303c00740141d00a420101491440000101c440074078003940038045a400214a9100d1766001d200d1074945070b406141200a092448000c4007403000c40111840196102d00c01a441c41e0000e0703a0a13074070f03030005003000c0c140c281d0013a2255429 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 385729010 1250 385727760 385727767
    0x4170a121701050f150a0f030b0402040b09010c0602040801060303090512010501240903050708010b210705130b04050406020a03061202060703140c0303100f1d01051302120414060c 79
    0x1d01c8074066007411508101c40d1002c81c00110400710302c8105112003e0b89601c0000034024890b50381220b0005860581d590341000b10014a200b484120310a50080b105114001d000d1400c2c02d6100d4000030150610a440141c240341c5d568000c01d0039661540c100310049105803006204500b0721100b140c0d010300d00100280110f501d40032a52079540f0f02c007004080c8124021100c90400e07405400c03201c0007964004210350019079200b407040e00070f011540695114100210540408407001140d83c00000803120103070040c076190004000c002032481081c05030194542e14807840310b503200e20034503101e24003506004da90781c2040daa0040440349a900074840c5850090400c10158880400380d41c041a450304000740079003885071288150340250343c811030b4a4030000082100d49207010400c601201c2c00d0070f2000031081d4881c80b42c0300340000c1003281009150311a0703004004c5440c00710030001480c2c0d4182c100500e0049030000e03104000d04121010780b0020100c01d072440114030200300b42503100c0c0c00440810704 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 385730260 1250 385729010 385729037
    0x1005040b0f040b010504020a2f0c10050d0507030f050717091203011206020415090320030318010e210d08162604260901051c0204170a12 60
    0x3d69441c103004a1b4000ca90104041c0e242d03a000324210454071380220a001610078000010b01d500c8201410411707582e005015250000b07040c04c0d8203200444056031529401d00051450312001400c0040c015001c01d501d6140c1d02402d00303000d1242a00034901c40d512403102e103a85194180354000c002d020b403c0a9844028100c580c00d100000703030303410340b0380054150700c3c21880e904058002c1d01540d00614090741c41580a50107150700082100200c030f01c40c404800304040d80000408445000044640c1c15420803c003800340032940503258803203044141040380b1020802d0f00410071422803804400c3d581c0b103007000d038030442c014100b00c40c40b001c29151a0502d40d500d818401009103101c2441d07444140000c03008030580782c00246006014412203020b030400c50f0705d010705254601c0d030f20318016264510b0140d0f005001801c07012084580008061710780c1c1d841d10740c1c0400035020349011440311060741c0f0341c2072201280e45181c0322401081c1c8034101d00284032170038041c01c00d401b03140d080c0d01d02e4005114101c1110f07003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 385731510 1250 385730260 385730273
    0xc08090d05071b030614010e0a02040311010f111e070812090105031003060c08060f0d0206090d1e05010b030f03030f0105040c030e0a03091703070b0406021b1005040b0f04 75
    0x180c202d94030624040007040b24404414040c0590b4000911140c14000007489001c40394080174100c0d4242c1a601146881d0000e80d5422171040740405019002d051b008001554081d443c9a00c000310149401c9840800c07110865003080d00b20404156001c5102440c0310b49408108030b01806008940058101080303880e40a90143c46264580d905100d0003000080e441c401151440004581201c13081c005e03810030400c01083c854048a0041c400c01d50040c82104070b003000707000c0c44d130b840f6805451186086081810070104584c4010200c070340114290201e00c2101200d000305102501c40c200203d0b1091b1088105400e010b080d4503a40d8080d4010300c100007800c10490f070030504540e030903900010b0171712684000701c005e8024941e007444075200326007032001010362001c02c00782204c01c0d034140c410344201c00c0703920a82c99228000c00900024003031404a000311354964000d14821420050015070540a0041c40742040c803070366440480685c2e10070070001444511059290701107100000601c1c0d40ca01540c409 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 385732760 1250 385731510 385731517
    0xf0a0c05310b0303041d0403110a0308040206030c0d0e03030106021522030c06021b0f0d120209120d020609060a0207050d0e06040b07050a120e0109090c0c080307030c08090d05 77
    0xc07551551200410082a14103108480281645202031841c1407003070324800700ea15105070390480001e030b480c400954800e0b4010550a68443d450390311800700341c41d40c1e001c0101c00d40018000d103c1300103040003020318041c07a41c821407040c034801c0320246071650f1408d04080d00340142a8800d8401c00e00341c40400200f81d1a4544c1b01000e000082e02c0d805041c4c10301d00f000c90300040500d800401700e910004038000f480724000b985480b807840c61001c4910540c003000119480e07034250560381011440e942c200707042c2c2e01c3c11500034008000000c0c0a0f1801d01e8440001c0030703d0000c00441da000903800883c00d03c030042005110b40c6a01c000080e01c1036107003181980e1520b940d04060b000300010002400ba42d682c0b40d64503e0102c030004e08280c80001d444180c9030034981c4d10f9002150b0103e0704240d181d92070380004c50107103000c1910100161986120503240c03500302009000d803441c50301c04004503c400c6d8400601c124000d1802411280c0d03000603441c50a0310007901c8808040c00007442030740300c580c1c454071466101048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 385734010 1250 385732760 385732849
    0x304060908060a06210c030c080a060f15030212030d020301061d01080114042c15060d080912010204051f030b1203041404090203030a111212010b0702030f0a0c05 71
    0x305c04100d022400d200080741c445420050007582c0100001510040c00555941168001ca40800021412480ba0070481d01c0a005480c941e86800c0340400c0035140c00d03038041040f01041c40a0300c0c58408000c94042c1243e209800c050b0104503030031020328012076242209081031500707092108065050640000e52840101042071180342c64262002035103101d0b5008003003640c1c00c0c503181c2407803480030b01659489440d100158054080d08000160301d80c6172400c4c510a400303030800c58840c60885000c09020000780800c101603130b90340d02000300055039110590380d9000b51440000205107238034850402000c0e5903000c07031820f1203400340310784160140e43c0c0442114112010414440b01041602c00032902424010300081d501d808046004005e4035040b4407203907070084e20202501e00e007664503010107030103000740340b80d2110903944000144091455079000300602c81c0010201e0b41c3c8440d0004250380780140c044022590403144210402550401c144107c041e22100031080a0340300940080000c280d022284 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 385735260 1250 385734010 385734059
    0x6050d020f130303021c0305010f060f1715150c0c0405090a0213020a020d02030c0318012d030507110a0f0311030708091306050f010305180304060908060a06 69
    0x204040700d60191400c42d020b0019031081d02c100c0b1650b034100a0b417588881c550b455450070001010014440c400d1260301d040c6c5540c084183c2c00d0743d0510604503074440f8010300000c203128a00c50f000a401e4403000d01903115a0780a483c0064500d58071043c000c444039402d8040030100f000780705371101d003000403e00408840c3e0039500007801d56200c41c440b5140100e0f000003c1e401055409042103005c0083c0c00808002c5a25003c031221082e036200c0480e900d12030901012540c1d00144060760f00300c602074141c030300740d0301c5c0524050641c0c282001043d504101c540d4042c880c0041d42c5070114401d0390700340c0215940310700181401400d51035070850081e1520820a4014000f148440c0d0240c02c0500482d40107402d441c21200300e0744c58014034500f0200c070354403a0a0305c6106840d10070001d031608100b40942016510040c0c0f00784070014000300158040c1001400d50040d445002040306029403042010304010841d60740d907421258038008600d802c004000e4034961106c0c5c04c14005001d000c58070168044054980813 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 385736510 1250 385735260 385735267
    0xf0a0c1220040209060a050d0501080601061e021006090903020c061c09140a080d1b270b0c0705090f1e0411030a1a090105010e1803090603090607090f06050d02 70
    0x4000400030710501c218264084c5e0042100e1644a9110025000410182c1810415648c03992451941c42c0da007445172800141000d152072540c42032200500000805a004449098030300341004402d40309150052003040c9c0e61941c1200c1415410010010000e8040c0c071030902d1b044041c032030304102d00c80a90803541c0054480610000300300c01c40040c10344802504080c1d4201c1c00032840c0c5030b15240d20049144000504210345003000417560088000000e201c0d8544040c000c0940c2e007004040358049581e04022210083e0001d4640345510043c00c1c43e0f85004050110030782003000f0001c0d5044d000e080341604000e49001c20003031018065009181004401c2c1c2d42e00a0341c1d40317140c9000d5003407241201070740500502072207070708100c2d503090021034150a411925055945196449080324001d20031500030010250205903c00e80d030b03038110741c90a107204080c1c03442c1100c00300c042403143d44207980420855001e40b08000d5407a90002c1042c018046006952001600c2c1050040c440d01070160300c1455181d000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 385737760 1250 385736510 385736573
    0x706020d050708041a101e0806010b071202011a0918062a0408030906220807090e0307020a091802060c0708010b01050c06060f010306120609020114120f040303020c0f0a0c12 76
    0x4600c110024100c14040340c00b12b41c0c642000e518540c0203541d04444541012440501c154010700400100d40400e03500031001e44a071104100c0c00d00006450406284404000c3c4000c0301e20600103d40306500441000e015600d01411072151070106013200c02c0803010074013060101060100c115030005000700c4546071501c03042d0003c080050750ba800d603c6100f8458001c00195020041407140882c1e0070f49200700000078144096a44030711808000a620110551090004a03101d601201d504d0280058045c0c5041941e40452200d601c054903480c451fa203d036804001c4003200340a038880001e401c1c80c0c803d09140d0502c0580c2c0c0e5800021745610300c0b4095810440e5826440390b8080001060f0138210014151185d0a0040c020440c600099001652042c5446041e190040031610172418940e07001c60550380c7c201d0100b9202c100035104604141d02040404403000f4200315250280301702401402d941140d602d0403580c88201540001030309201c803801039004c02c01f1049010f0140b0103444d6800c0ba8104071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 385739010 1250 385737760 385737809
    0xb07110c180a150816060e090a1e02130f061106010e130804030327080c0103020c010216050607170408030c130905010b0a0314010e0402060706020d050708041a10 71
    0xa1050821940c840b20f0f40000c498030000b480e0010781c4101c0d000c02802c00c0d01c03200112202c074584121160020341c803c010075155500d55101e0a01d038080724191001c00241c9e20915030990f801a0546a0390500a09040c0b04203e255002500140543d0a00f551b43e0464000c625032038807014803904a11691450000710025008480e0f00310869100c00f1050760b407034581c503010b40500113541007d5408030315072204004030038803520168240d034808170051821030b404500440181d0b110303503000080e5540070301070700e1804100c109a07008107030301c11009040c00f813a01100041843d1100d0800f1207030365180100307000c086800101201d0b08242c1c20041c060307441d6612500418040a268040d01442d8a08000011107808542c054103240d039203503506000c040c0500070b030400f102c1d0013070041d852024591000726006260190003020070900c1880c0260401100480580884404407400d002023200581000304010301c0c584071407040c8010003e4503845052515003400310451034052920031800503000900c50a44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 385740260 1250 385739010 385739021
    0x30804030c0803070804030206061909020c1504060207050f0c0604030201030b010e220b0d1203021b060703092d1104020c031602040c020a0b0f040c030f0b07110c180a 73
    0x80020440c0d0f600c0c14000c0004145580440d0164010b00420010528502d001ca60072050303c2d10503458100c0c0b013400c161010000794000c403800003041c802e40c1600710300c0310350b42c5001e58403c6010b8880103072140c0c0c15050507401d0240d481c5424840780c00081420142e95035180c140c80650b6028a400038400703a40c080140e541503196014554040c250000380415111820001007030781d070003c00180000840e8009005064500000003000c1c3c40e910b01ca2511894840e6020b00038103005020206401c0720001c410a080c040c060b920035000948135180c040c01e100202d2580340b080910188001c40340000c0000b1481c01c141d08040081021a003210390020135076680c1c06035002541c2c03e00a880e500c03070b0200b101e1492500b60640032800f4070706000c40c5844007030000c038080c1481a040328074000e043d501d5071000e05e40c10300003c000f2100030700044004404200c086105d240220301c140b54904441c10100e0000d060519003003100c010940c010040070f040754a0f240c000d145901d010b207884000740d48600101c007000c0e10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 385741510 1250 385740260 385740263
    0x1009020304050f0115030203060c0a020c19030c0e040b0f270c0a050405010e0c0c011d03030a0f0b010e0d0204020424030e0c0604150306051017010f12030804030c 71
    0x2800402400140000458942102c000000080040c84140c0034540848402840060b40c141c000e4000142c14041000041400e000c03988140d9200e070701d40b800007811058180000c8040005044018030411814105000140c10420755054692501780d64075118400000c01c44030346042d00e6400300e03075090031000705115415035603070740c00e01070488164840e56100c9880b50b982c0e1080600120000e400e0400313202d2a416282506841036043c1e0714219940702a41c03000c20010000d40d40e0390740380950740d01015503c0d8001a50340002d07564034203041803078206803001010f010a0051400038484681ea0300100001c00302101650101d03100d0855000040090150ba031101c180406690036582c44600880002110035480d43c074100301c0034014040722560303580700e081403941102d0308100a00040c2010809036007820010718010a66a480d14042612000c80000660200d5210401c141441d400c00d40070b00d01500c54004517409041c6080000d4640d021424030182c24046600082002d2611401c4c1c0c144032039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 385742760 1250 385741510 385741529
    0x30f02011b141f050c091212040b09011d01050913020f03010311090a0e190f0615090f05060306060402090d0b040b06040501082b030e0a110f1c080310 66
    0x15940026015190f409041406000c8030840da41e003803c000c40c62061034015103010710040d05028000b0140b2a180c55007a41070751052042d60411601c0e044100000e2002d005240f81c4940c030390703020f04c0000d0200200d0413003242c1c182c0c010065190250341d01006441f00408200d07042c400580d070340c2d480c00c03000340708410142d000d40c2c0e0000000b006210b0190766003400c2d007000755402c01c5140e8400180c80304031401035800881d030b504060980b40122480c2080c8010f058040c0d030024660554941d26030b001c4032100030341e6010641d8402c0007004480a548111880560307109170902140ca045d20010381c44800042546110726400300b0041300e00d844100031121139a5100c00140030f1810705007802d4040c00b50488207140324a09180c0080344014000c503e4074084020300d4208d54907400500050003004100008440030541c0e5011030080450040103070740b00340387c081c0e0000354079020800c00303204400610100d418010fa01000441400c4012500319002d00781c0c210380c0c016141e0f200e202519900c1404c41d884031801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 385744010 1250 385742760 385742783
    0x161805030f010b0102120421080c0f0a02030d03230403030204030b0114130b0315060111121207020309100f05161b0807050f210703050a03090b04030f02011b 69
    0x991105500c0910fa410f0701743c0844008603041c0c00c011102d84110300a6055110550b050402c00ca59641d0449035014891040d4030b08000030880100d00d85800d440082200341d010000e800254201131058600900c07403868140305014003990054402142411840b10b1541c1c00d5000809241c1301e581914040c590100840d0461b50356201154020500c6250091082440076072040340d1041512462004003405800340c000f1900030307042119411002032045044c8100d00300c003511201424030409041c0070060031040d40755000e002c1000c2690318001d21040a40d07104124015090707403102c0039407040b500700c0d15000441e010500b004403100d01890320011031b6999007100030400c01a0b881003104080c1c0340e101000030640c0d9144400396842d407140c410b00b03801094081d1001280d00300102e46007002c50000986600302440000910b140041c290700690b120b41000400c04105a8040085002030074185891400c04d4110f03280c2003c004038804c0001c5c140140d0244110300218042d0b28038851a4201c020001e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 385745260 1250 385744010 385744033
    0x30303070203030a0509070e060607021306090905010b0603070905120106030b0c0301060e09160e0a0308040e06090106030e0c1011010c05250c0314030f0307030603140616180503 78
    0x50b40d41059480007001030402001407081c00000400c3d1048440070802c4001c1911901c0a105007684880c0d801d030380102c4d841048501100c601c0c000d04004101804000800492a0501500b10b500781c0f501c4030702c16042041408102e982c81100402034580448007542c2c051703946c802d0301713004019550006242e00112020403880c1801c600c05181281c0403500d4001e0b40403113aa04001d0510001c03a403100310300429074043c80d1494030644115200040c0030304140b4801e070316a1289059508654001d24010f484e54040200301d0070302c100b4507401404242802d201e00d00300740800d9629217170680c15080c0200c0c050030160000b2482003030780d0300034006000020010426a0383c80280164400e0740280f540c04035401c0403031812001c003503220540380e400c5601d400d40c040c2140e94041b8004080000102c0c684018845e0004021507100114010303023040d103002983d186580341c4512400305003007900350f4540203201005540c0c5070320141e20011384118a403195050501d440e0f4a84d500c080c035040700390940320701c544481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 385746510 1250 385745260 385745263
    0x703050a02090c070c0b03090a0f060506040b06070803010b030a09060c020c03070611120a18090b09062d01090f03060207110904030f08090c0d062003161d0303030702 73
    0x100c801e009070380b0040e41daa9035502440a034401c0c40001096a04890b10800c610005200510307000311042c5d0603500354910b1600ca205040c4500d200c20f41d880c4c0e55131024011186024440c0820740c082c1036504d10b0601c0f14030788481400780014415032012600000004031040c40d0307035201c004400c0d0300c09010400c000407840001e40e101c03400040c441c001e1055030f402251480c0a04d0658151010850052482480440c0c43ea000c0d50010f21100b8240251000f89000a803c03062206000d80ba100c500010001422410000424801340c003450007641a24a44804902520f03801c841041e0302c0346218440d111910012511080240d00c2607814069410000c02000001d800070200540507005550b0040101c1c800c008603000c054174000c0201c1c011031041c031500d078000c2c04150b41c080401c6066540b07040e0748101041010214140441f03515942d0f03808075101c50254015948041c00104a00303046203040c102c0b49908548459020041c0b0119045810dd500125010026031000140071b90361241070030034019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 385747760 1250 385746510 385746523
    0x1270f020d110c0d120905030f070507062a052a03060114010f121401060e181005060711180106020d0206040f0305030a182a05060406080711070305 65
    0x40c94540c14400303014010b95a00b8203072004031a40340068603054110200a450200000850070021174580107a100414428009405100d140c00358182d45e40b8101c1c503086081c00b2468208205000508841c28100728010f084c51444501c0421a10304021340c0d0b040040c82c004010380d0740141c075490b00c00403841d040032403500c5202e201e2003a000c80e10140d0721030307454000161001a8130703400103140c114404500d52040d460150740c00782c00040003c0740302d14014481e40c142ea0076042000420840c9000b9a8141000e118003803200740d40074202980c81c100555600b046241621401d44a80d03404a00718060008400c0240304034075005054240d0210000721203509244244140c001502582042e254014000b14019100d00d500229107041c1c11810ba400341d0389500060800003842d0750b02d41c0c0400c1400e298a45d42108107028a08041c0510340741d103860007088003c1c080c038400303203012008100080e841d00c205803416600f06003081400c555618000b207841c4030380301c0f80e0350704a03209501000081c44004a841c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 385749010 1250 385747760 385747777
    0x70306020d15080303070e180c071208070905061e161a040312020706090503220503010c0c060506190b0a031a030604110a150306080709060303050301270f02 69
    0x91041030090b114074803401d4040e20800c8025001000002c0d002881014560b00c5001c0c01069450350000c070740641400e01404640045d0102c10020340d01d014084511800580310341c2ca880c05400740e103002e007002464000f13203101d47c5000b8000440c0034130b11107280b580c2c1d00d4040000402e1a5407202c0b12940ea0250044e1412030070340c0d84502008001e40d074106540c00132481241c260311258980c1038410012402548a20f10940390b0303030b541d1440e4a0002c0d01c00e00052007040c0358456001035111101881e40c2e00c054003580b1045c840d80c903124030545400e03000028840030541208002500355241c00114064590b902c501c5042003629100104082041202506e20320042c5e9030204140035900c02ca0106001c00c05103070513030645c4100b0000b0001440403010442990700600005205035840f860700105500e054080004291140c40070301c82c1420411540c0c00501407107030107010311451914041e000b0f10060191050607010903412058241c054140c2d80c0c800d80264401304804c1d400c4000600007900704845 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 385750260 1250 385749010 385749037
    0x2011d0a1506031e060b040606020c0906120a020114040504180308090307030c0b091f0e010e0c0d0b1b1818090304050420040306061a03160309020f0307030602 70
    0x503150601c0ea01d03449a2000d4940c450140c40c4c071640c0301c03181079030045000f16045550303584800c005441c54845000e48001040503030000c2562000715820400c0126004000300e0143c071081c4e414800d4140004bc0c0000707041e40a00f003041b40b009107c00241c3c3c040c070850300826046400c2c1050403481200192140c9080c50003562558142d0300c808405c01c3c0c0f00c6c8100040600040c140d10507010100b1003009404e90000e4502007215421b102d1607421503c030083c14042229541e031760302c0003c00e5481c1c0a0103000f030422100c6014003c481c02d40301c00142d05100704075020388481d0000d0009034000d840c2b100c10300060030708901e4032503c40f041c440c41c202e0b203040410310084c025020b021041100004044c401c0d400380d07821902441c202030412042c0001003840c5e20b2440350b82c1110345981d00c0d004240c0c80080000e1401140c0101d65581072190340920310341d020400030241e0100b001081141840280b40224052181c6000701c1d16052600000d2071a4003142c0031a0340c180241c1100004010390b03a4010610b4122110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 385751510 1250 385750260 385750283
    0x3120307080a18171e0310060e18060109030f060c090b03060a03060b010e06030a091101050a020703030c0c0e1014061312060e030c030a0314010302180702011d0a 71
    0x116080b003034440060340d0115601d40410540b0001c0d046107500c5400140e148070250030403002d501d0114001c120703801e18403c40f94000080c4042c9080103100d86010304024240640405040c1001c100fa0401100303c26000114040100d40715078482d440b144003d54005e0004019800da40c00d0040c014138080079000081900400c0c006060141441682d115a0000745444883e520390303224103009e8284143c00341d041015a40207550b81d650390101950080101d00000100040755240c03041d9000140c2c0c1c0030074140001446400d88450b8001098000c0d254180390900281d000f0340342198100304940c000c207112400300300c100042c64402c20600b00c11241c0302c900409070015800706000081c414402c40301c02ca8625584240046252401440031161050900007046a00707001030358210f400540300b131a400e410000724520495418018030503000d02507041d110503945142d00007107012007140041d00d500c440b680001941a8002c4d0b1015a00d54400070001040c503000740c1500352556416402180da40000b030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 385752760 1250 385751510 385751521
    0x50a18240c0f080405030f041701050703060302060711031218090f0615090d0f030c060c0e18090c1c03021011091207081606030b040b0108060402180312030708 70
    0x280600011910035840b02c00030340054010440300107200900550f081e100c10024a89404100c000510003810307102d165400711485500050f080d9000505001d042505181040c00542d9411044402542e072229002851700c0e04070020034200741c446e440d280300300701d1f02082c2858020042c0050b039100c20030032501d54030f155460949140e03048a0a403001d580001503505131144005c4580c0040220300c400030300c5a000711016507101d45100f40c082c0412800500c0c604006410065540245402e40c1846d040070030040e004080481d6203001608045c40c0180f000c80040b50706980d0900c18829039020103040503440c20320591302c0b000322180301101103005100d0b8000c102c0c0602c07980d110785071060001ea100d5500e0205810b003005000300141d01030300018013074418005072a22040001c5400d0000601551668914150000d41164407000c5d4690080c1e003040e241840507a800700e0717030780d500c04400c0b02c3c01602c07a110b0162a940c0c40504200180d094407030100725950402040000d1446194244d440e0117103541d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 385754010 1250 385752760 385752833
    0xd1e09051603120f02010b0a060f08010b071709010c0f060204080c060316030506031006060f120b03060601050313020405010306090506130b0714071509050c01021b04050a18 76
    0x944030291108500d2400c801145100e44400034413000d843c400450101d2050001600c8010294800000704a56802070700c4440d81109107a030060410b9400da6040c901585c4400d544800740301c4c100c00040200142a682ca60f005078803404c2026040005200054510b01c0c1088c0254028043d41c400c46c071482d0000ba40528201044a20601050100c4100104014416030140030094155035050003803481003007001c110f501c6640000e040541d2188106c000d400c130041d040b5444d07091004405400c0c01c2c800300d400e45000480701c0d00910203203081030f680d645040928104074141c0c0002507003d400d040000041c01890740048500d14016026248180c41c1c4038000d14042e02c80312401000d84e00f02c000007408150141001810107080e00d50b07040e1a00545a40300b00f211064113040101c69559403071307080c05009081058080300e000a0000300302e05611120f180142c83c000544a038030940c1c4410002d01040c182c2d8020b5400721201c81c400481c4040c682c503103000305500c140091110189802058900d00c0328 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 385755260 1250 385754010 385754053
    0x21c0e070e100f0b0d0b1302030f0105010e09041506080d020a05101803080a110408150709062118050d032003010e07270513200d1e0905 60
    0x41c040c1c620743c805482c1c04a581d900ea007200d903840c0c040542d2030001000d16121614044e4000007039460041c2d0700d10b4000311000308464180c0183d81044100d5420007520346545000940042d00400c5440000511400d1000030f4440b07134002c80b0450045c407000c2d11a40b9000203602d000c6038440c0041c3c0d1070702c1c210301c841002256101c861007010040c49859600c0440c0c060318010750003004812010540540f66880d03440f2a60050b8030504e9140d0020001f181100c0b440c1180982000c642d1402014462410708010075800f03064400902c0c0c201c503000083c0d03030200c00b68045440400d041c0328000002d032807170900f25200e0740e0314105040800d04188007004030000046c071496801f0003080b4114207607424241101d0a0020051101d01401100401c8039a0151001300d80001528250f0030904006c2c18101804401c01d444600d51380d01c207042c452215901c20780318500304071044080e290345444905541626001e005008612442640b0390580000280000d030840030840c0c4c01101269071100ba2501402075088 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 385756510 1250 385755260 385755269
    0x1d030711030a050c100905152a061b0d050703020c1903050304120c0c1403120301030c050d0804091a041404020a091a060c030703020f070303050904021c0e070e10 71
    0x104428103854041c90078420f01210415141b1301440180d0b2074a010072140c0c04201002403031490046a0034652022011244510090760a8411108038041d44c046566001c080c2c084d5004d00303040c1c015040020200810b44094100012090080c3d041040010b030096000c090946840e004e43c20041c02c502e4616030804105560660f01c151940e0b03110b80f169000d00e0241c80f4400208440a01010702041e40c01c140400506901c3c401c00840540310010540f402448802400d4001c105000401c00f1894014918003202d0003039074894240141444e0815491180d5000424214588104000c41001052103034031070640c01d071020048144500b910912281045070000d60080042400380b00d1080f05401c0703c03008100c82400024000d0728000003441c0b40d0000b010341203040d8000300e20f50040c10b504000c9031850960340405014000e0550b140100907104480b1081d0040d40c00046039002040202a00000a203032982c003000700a100b030010b29181c41c80c40c80303503582c0410000c3c0070546803003800c502c000c1100d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 385757760 1250 385756510 385756513
    0x4050406020304140d090e100b07050c04150503070902090301110703020109021914010e011b061a22180f0506070f0807020c120c040221070906050306060d1d030711030a05 75
    0x52a1514514012600030708c280f24250740610000780000521019000700b902c21005480001d880c502031004440004541001e00342c0310304030030002500c010690100341c50001201507566420707440445d01401250200301042e510000305102071645c103511409840744200d415480c116510500700f000402c02d4080c4d0302c0c06a44229011071a58040c40070800d0000c418140005141c2e400c076180410003c11174420340b2450b44032140010400c41d80e00800300e545a0403141c0680741504083c804185803900340910074440d559900c101c1c11440364001c0b240e50946d00001c20390510017140b5200d52a03400c2684c804020036018404c11044c00d015010507031141d45e10354020404c02c035000040040d20002c03000c034400140070b90302c040c0040e40c4490000f032042c0c2c84902c000d1460396221008a000e0410020700d02010000603e00a10886501108913074120303070103c40c4a1b4564000402c000020042d03900f0000448900b4590810100c2010010f01403460081c2100c00d95015501d003403640301c2e50308000c000c1c6207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 385759010 1250 385757760 385757777
    0x40501061d07030b0f13020a080c1939030e0a03030206062103131805010308092b12090501020f0715020304080708010b0f04090f02090901020904050406020304140d 72
    0x1990f00c00e901800b11508024407210010142d14045490100542140d408158000034140401034111003816044400c0348089c500d441c00310300000101b131001d800e140c1c0400c4526041030411a801c20540445920310300f5824100800c0200308440b40ca85030b5004502050101c07900c4802171500728507020417607800d40c01400b030740d50f603d030100000304500030400f091034000c0d10303c44466660104040c2100902020312040842c2c1400000c0e19040e000e43ca0b441d540905000c010310010300c40d2400d8030860700c0300380c820914440b002140c01c440c00540e4001a040c201015802009000005014103d003100503100c030501c8a85400049840d2011005400907076403055074108a05c8108004000c198102441500e08082c0c640a44600300162030384051042c3c0e4450305148003070700e40340d50001c00d16a0102d40c02c102004095451486045c079030840680b01d004c4510000d071101800390111070f411a8024400c2209240c85c0c5803210080d0001e0b034064480700d0402d50084002d0000240000042a0136150480c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 385760260 1250 385759010 385759021
    0xb0105090d02240403060b0906190614070503030708010f090e06040215040e0408300402010c020406080106091e0203130807060b0603040638060f21040501061d 70
    0x240c4061880211041215809502d84000c07080142024500c106c00110310300001c90104030780b521000e80f08911802442c1d28001da0040e10b498000106d8440741004034800f01048802500e9024484001d410360000004000241d82e002c074145050398151111042a41d454200ca0b03421a140c41c2c0c004034440c0d000344c0124015190a0a4004003081c0421915141c41d0b1225080c1084507020340b000c4500c0356000c10648110b07408690728081550b00229407025040c0248082da11005001d0000303170501c4414107034402551180d07040f103000313043c411001b80809076071100d5000042014503404540600b11281403c071407180c0d40210380c084c0c02c50043c003c082c02160b41b64500c142e44030349401c40f02503583d1070107032000361160703800b45200c0d0b40030310300c00110320f41c010012500f201c20140c01880140484550003030790310b01c91a14503090301d4041c0c5100e40c031100b8204d8000c1d0300340300300c0c080001c0b120044040601d0003880360b0380040c401e0380310700001e111940d900c004e04125215514014800716000000141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 385761510 1250 385760260 385760269
    0xe030a03050d02070609030c11030a0f03050a02010608070609030302250b0c030702030607112407050c0f30040b1204050a0f03020d0215060306011a071506090b0105090d02 75
    0xa400c051a041c0145440c03460382d07500c5c00f00ca000840840205008070441c00074441c07290302151002c84103901400030450159618580300070341980080c20b00101050101e0781c20700c00d5200b41e01030103000d421642942e4550501409401c0c0d24807040380148180200b03522009400c105540c9000301005c01d030001541089922b6000741c1190140403d44e10040c45810090f03035080000d64082e004544502ca840c210201065083c83e034010741d110003c085017400c90300d03541701189410303034000d0080c03a10035203c0c00c0c030800107420310211241011583c40b5090300e10642004c16140d8420a050041480c0000403445040c100c80b4001c51003100810041400140d5001301c40800c440c4c1d005100704240e0f48900c4150340c03031030703a2191403150990050f840305009280d1346404104688990f030030444010340d00e250440000c0d40d1500d05001c1d541d080403c2d07601d404c45190250040d100c19a81c040258050142c84d292a00c000302928444d000d03103941807601d540500d502034022101c40c0500980040001c3d0782d41c3e020710 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 385762760 1250 385761510 385761517
    0x103050405030c0313090509010507020a0b0604020c1605010906140d1805060f090c01020f1b0d05030d020c060112020f040c120f0902030d0503070206130816060506100e030a0305 78
    0x607196808200030161415406100600100c3c00394520b641401d810710841c841101c800820141c40f40c1e24090510828540005010b0317802c1d0780c81140d0000c0c5903078020106002e4000c94101a4052186c81000441c0340400108101515030030380c1c800400c1651090200c075400143c410f0420f8821080080700403d00c0b0b9074100c903004500f0801e400034409000e9a8052400f4000c5602c10210385107039040c010540340c00e00c0481d410071024401450281c4203400b20540351164658040c1441c4003490802e0210784a1001c01412507800005417611501c40310068406941302c10500a85030042500203d80000c004012002e410340240840700680c00ca001400020800b004580e0103100c50580b401d02881a42d024490000302c49100201d01400c8910615152460407003940c0c0030711800b48100a0f200703500240141c0d2042a030450b040003c10382d414039102c02d1041007010400303400215003210910100e9080240120300640350349802c0b1282200490320b9138032041c0b8440d4103401010304c0602003445600034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 385764010 1250 385762760 385762763
    0x309031d0d150504110f0102031c060e01121401180813090c05070c1d060d03141b061605181c030e0a0608060a0b0a030902040c1116030503030601030504 67
    0xd6085108181c44802c54a80c0c409007211005840d401080f0070407039078041040d0074840580d4800c5401c5440c100103502c178003c5250b16144030065244040b00e0742c03240d401c014020881e0088148155858000604111403403540550300a91000e050408500c014403038084420152040310f0f09190303c99031014855880b0f48004910f0001e03074000825241007a12542d02c5074852600c49507506c40d201d11701101c424ac1d181d0300c060070301980340c4c0c8180b6241c20200031940d408070003116640b0110328140340548200100941e1608240c80c00f165001041a02d05280c0c4e203100c3c20b030011a40c0d04d90314488444200b08141007101c000810a010300784140e1007081240b00d04020042c81c405412000fa040d404c40c200055909a00254444030182a14100348c407900005d8070140c50075869520b400008a4503c811512460812a60028010402e00d00c6a481400a40d9004006010704410f90900822031080c1c864800003501842101494040b070043c4c0d5041121780c0400503605580e21a40150001d0400800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 385765260 1250 385764010 385764019
    0x30b0403020a0506010e01170c0d03050705120403030810150f080a060e0a0203010e010e01080d050a050d0203040f140127030c0f031d060a080a090c05040606030902030d0309031d 78
    0x10070b54001481801a54083c190050a00c291585030080010b1001c20708103483d115130700a0002540d2503151504418032454050400580d25a00762421030b01d000c5005210028030321002c038020040607400032400e401190705003500d010190f04c4d4000a511712000c01c4d10000819801c000c074144940c02031003069404041e160000500c0c613a1000c0340b0303107400b2003241d41c24221540000140102e48162038158050402c0c8951807040b981451500d981d01c0100301c003410280940406c01d000400e02c0b880803540d03078510514055440c1e0900d0f02d040010a0814282112800074100103014104030510074190800d100040307800400003040703580d40714400d03003010580130032140d011540003041142503d08402171180d610403500034540d0f02c140c106400f100480511030b0404102d070040b203982c004d01080e013001c0d00200018000c6202d1500c142d02003400e500c101d8000b07041c4080007c0542c0c141d84024107090007602500c805c20032100044044400c0001c005011580b0011031904a110014592160308005070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 385766510 1250 385765260 385765273
    0x50a140a0e151605010203040c0f03021005031f1701050c09130f090605090303070806010e06030a0b0102010f2d14011203050904050a05180a2102070b130e0903040f030b040302 77
    0x1448001000c0c002c0c40113468a0b9000810b1100700500030440100074500c0c07010340c0840f03074116400500c80d03030107940c2c0d0141040400301c003041410a402880c43d0200c1300c050b03041c0b02c841d030340c55000c500d1860034008202d900703510389400640c00200500c1184c0c40030320001c01d08100c080c4881c1303410000b0142d9940c0700314040d5070342ca1000009542e51013118080d01100700155120304e45188010188000200290304020303041d44010b4090700c0e400c01381ca8005080307900110300ca90f030540040f0b005125140c0d203421400c2c1400d2a00e80c80000c65601000540078a01d80190449a100320300c00a0310406481d140c550307480f03c2c0041244189006032080d0381072191422a1074070302c1440000b0306840040d103103100b0459803402800031f13881d0030f00d20740618160032401500c82c61805450390492614107820a104224489141070301c8a8424440b0f034000d040007540c80c54641015946003582044980504501d1994100110b00c44440000c15901207942250224555070708540d1030480b280c0300a4004c0701584200e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 385767760 1250 385766510 385766527
    0xc03010b0c1903031e14040f02190b030709060504120b07170103110a1403070e1503060a050a061d07050904110a02011b0c0209010308031b0a050a140a0e15 68
    0x403404115041c0213650200300401c010224445289401c014549064078000310b0301c44a000d40d24240798801d8020324114203244450000c5804050425000038031310b980340c0d8010542ca042d44010314040c0c0c149a807104900c0d91119001c3e0740611481c080c68502ca038000b510036000403201c403612036200719949012520f5052140000340210800e800482d042800c43d10780749080c1c140903100c0b04c0284141c00311a0f01c114502030110740c44003554021016121007100000e640d54028600c5440c0c60032010f012104546424042c0800410003501c0d0420f0b41400d0000016800700502c90241c0c24520781e11100903281c4414800f42c582c0d03031080200c141c0194403280705c1c10a0079040c038040d06075041160000b240004000b013107440000380d50b11001c001e00c404a04903201580f1500b40041c150b92340221603565035245e101c2d2403c500c0c4801000c254005000007042007a060340040500101805611014007818201c0440e84084c040e002c0080d0014140100c040312501e400144c541d07200410a08040c60203130744 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 385769010 1250 385767760 385767793
    0x709050a0b030a0e07151707080a050402030106170a06050c070503040621091b0603050c070809040b1002070f0f0e0a05060111010c0e0f0f10081504091202150c03010b0c 74
    0x10703076006d900800025051030308a6508080498130019170261016400d151410b0054441c0601401741c41a155491001604644095001d0ba003d00244052201045010a030144d0b0307641c0c254104654480c2841c000c11080c008500548440c1c1d0ba000007e10b0400b41000411910350725840d424507080b60303611102135030454451092401c5d06020319540407a030524460805000c20a0303a20030010545040b00700310401d006501520751003a40b210029a50728001c00004004d0100480d03610303030081c0c8101d80c072400290001843c4003251902c4c5207220881d540c480201d02030007010300c0b9402801030010009003a059450703101ca50b202105050070f1ba2821101000c0c1d9084401101201c80821003448040d06146822080a07440d030704c0455680701c4207482d01003c14114181001301e4014010142c01140c00c0394030801c0e120040c1803015004010102a9042201c0f503034071508103140241c0160302d180782c840300481f140d55201d006190541d510307603440e183c1210b5042c0c0c059040568a80200741d0414140c011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 385770260 1250 385769010 385769023
    0x7020c0d1106070311010c0804150207060209130b0a0e07050a081e010b09040e010e031602060c0109060207020f0f0f060a0c0501050a1b112107050d03050901050709050a0b030a0e 78
    0x6559000a10800c17141110f00b1a07070185a00c40500c50000c3c10400000c4103800801c9260748403c1000d600d414881c900000039001d10071807240d10030441400303071009507116400303a036514000300e680070b1f2200e81c1d41051011142c0140ca08130b0004400300001c00c40c142c0a14941600b044004440c11201e2440e030500803403c480c00e81041400240c00584030110345000d00501c141d00320701d00020800700b8241b10040c0d170b49110b00320300e110f55840d41c070420340c05545d60002a200d02e1981d0314020f11209510780b81400c0250b00c2107904034440c001440359810784d030a0549400b03942000c05007034807203803050480401c521078000300c081404000181840000241e020b0082c140074012030000800d14240d51803207044405201e0030b0740800c101070070080c00d50140e0300003200210301030a80595108103241124401c068070071204090300b0f038850051f0074804075a0642c0124410307083e0740001c015586899100f15021000c0d4452550300001048003070010030f00c408002c5400220700c020001d881ca039458145801c110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 385771510 1250 385770260 385770263
    0x1512151207083c03130b07020103050a110d09060b0406080f0613081b03040b0c06041115040b090f0904030c0501061a031339080607020c0d110607 64
    0x1044103804208a80040000e24030b104900c0220070800d03c82044011503031075003100302e410a24060100410024018412129207010660060300401e031079000d801010fa110354030480c002403529000401c02040752040402081c3c203266010301d058504003100018000000341611055682c1105210540d20740c81800006c0452801909040312800c103040c0c184a002030110319000301c1e201c0040e000800d40d0084a03c425050308001c0101c8a0300a03c0520354007494110742d810220000f010b02d0381c02c47c0040c500d44101e00c03d822043d402410003040c401118915841d12101d8401404240450404100035002201c03000e4410302102110000090142c0c1e0240c45c00d5000c5034031607038000c00380301e400c2c000e1101901300141c250010002140942d040b500c40100110171a03a42c2e03828100810090004083c691410307080c6031901c100e4049041c044140d0170003585040c1c41022040042c1c0140040345003441015107401030014440c888d011b018200039099400c0302c00d03504132a070000c81981d40c5406000c20380d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 385772760 1250 385771510 385771513
    0x220b0910030c050915010804050307050106030c0510030c0819112109060f070f021515040c0305011a0f0d02030f07091413020a020309130b01090515121512 68
    0x4601e1800e011484208940000740500d6615081014000c0d072400f00c070107021000c2c81c242c807076030f522420210b040d4090100700a1840d420000c0010a201099100c00d041e94002c441031164002880401d400300d940802003030000c1440000020f108010305400b1070741c10303200d11030701080c8442e144501d009654003c0c0094a601500300044800101001484661042c1c41c40020302e81ca00740442e06c4060a03100611001c1006040925516404d1003440b00090303140b240ca50b556503505041c00d02c101d0800710b042410740180e141c28640700c4024445c4c050181210381d80b003102c0038a6040d50781d084101d944a000c0c03d03c0ca030031040213440c881480c01d00c001c5202c0d6211512150107410000300c0140480c001e0b074407180d0000d10301c03032000d20f02d07648074520948541301c001001691190044026410b600648510304c0e0b00c01c190601c06004038110b504610280d0200340e8980069030303291420424414590300040043c04000c0c007542020118000c110740d0000c0f40c0c015440545001c0b400050801030b615078851486 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 385774010 1250 385772760 385772791
    0x62707030f0e070801051b030c030714070506180d05090f010903050a05030403020a0b04030201020c191e0806092806020f220f0b09010c0c030203190c0602010506220b09 74
    0x44c10b900b0700c2825008028070140c2c60204403004440c0c030a5010145c107c0c1c8074440c0001c0481e1200e405011562041e009032034415480c0d2280d810034039250307a011224540c1c82d004c4840c5e0b5000c604800f00c0c03c50b20583c5251101420b0450a034140644c514448e4141d50500c0048880803022132410450140858418070046548904601c184640b8504580c4950126101400305000503038006c03c00d01e0300e20070281c130301d00850702455142d96480a0300f60700050b042c9403040c2d03080c0c03c87d03111441d0400517107060300119411610b400e10059950016131043d02401c44100420901417440c070b0300380c0501c2600030f190160030502841a450926481491504070112014000507410f0f6080c0e24040000c001804003120114601451400c4510a0085c60390400541d24005410041000d014030040e54000d0101e50311070500c03020104180600303100035180000321030381c0007031050b00c1401802e20424001e4041e0a060340c0035400d10384042c0510005114140c1c503210051005e4a0700203040b8410103d10304420071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 385775260 1250 385774010 385774019
    0x310091a0405102d0504061b02030d11040f2606010b04061805130b04060b04030303091e03020d0f0219060c0e0d02060403020d030203070f060203010e062707030f0e07 73
    0xc5800650007200301c03001100d86a4030090342000c0c0078034261340603000400c00355030340c1c85d0a00040c000d01c014841c0800e410241000d22681c000302030310380031003000001c020b402c004500000b4076005911a10440316112002401010040c0304281c00b13407c1c10056050129005100450910009030444141c00b400071804101c500d600030801038a01c1010784d00e60b038055003004003260303501c03004500310902d1036212030351501c0c0f54689500000040050410b040d49031074a03072400a000d2701c03140e04203541380714440c05030b001c1040c0002017101180758940c0040040800d000805d41c0c0d420044640c1c00103500411000320010103039a06001c400ca4418500040e080c2c021190140c518090703c510702e0301807110710207034600507122101250256501150020b01941d6146400ca203584a036800c0188500826003160f000c01909030081c1d41a520f089251032520350b10f61707091002d10401c10b042a882e8a80c0c111041906000941115400080c0d615000c0b9030140f001c04c030303032099480340c010040b800d5201200800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 385776510 1250 385775260 385775293
    0xd0816030806090f160e0324090304080c01030504020d020d03090306231503030403020a0905011409070503150a0b04060519051c0b040b040504050607031a0310091a0405 74
    0xd42c40441180c030b106250030800c003200e181c410000c101d60a41c00c080e000c0050104c2c0110003140d541c2e4001070071225448071800311008201d0b81408074110010401d00820501c0d1000b106450646640d4401455503980010045000d4000540306a800c0b0045800d80805070302c607451422001c4d03010b40c0750f00c00068a50b1502404864040c500b400007400c610750740d805503c5045042ca500f00d468010b036151f55080709000281903200f2540029404a400c100000780b00c0301903004181265440d41d0404101c40d501d6051004245040340c3c540c0c006281000041c107015180c4000c0b1103011806042c1090701030b01d030032401c08980e101d81c0140000c110041100c00c105014104111030301c0400303203003103402c080240341c100c0d400704180311048070b2080d102c42c0040020740703650740640c0034140010000c0c4034900b010704003d6250300c016960500080d0500704120318480110030b0400503014007800800680112034129002821225004ca48489602c0201225841200e5155000301d018801610403880c120042d1b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 385777760 1250 385776510 385776527
    0xb1c0f0512030702120d0f0212010819021516060513020f0a0b070f1a0132061e0403050607020601060f0e030a2d080a030606080f060f0d081603 63
    0x1103110038070030420030400d903a002c100000884010040c0c2921140d8800031803001e040d00c0c040c54802140b0201e11409400019030041d4100c1e0501010749101010240301e50084542036100650004e60b000c86011200b1b00c4100241100c0200583e450b80440056881500340d80c1d0903142d10000503c4520407005510302000354060400c002ca03005a01d45240081500182c01a48001781524030000230340d0051294824140c0100c14880280041541e124a80010f908440304ca100c4000300d0140b0f91842c22031103d204440c00d001004007a20b0404220300120840c20401030645005807805100c0080058420040a40590401d40150184d903041c900003c0c00104003950a504001c4104100b0320340d034a000c50a207001035013190f000c4020301e00c403090612030581d140f04c0740b801d85860900042e040c421030318090400341a00d03035020300c94203030b480c041210390000903249240407950703040100d80300346801d1040351800d200140591499901a440d00c17042038004223001080301d1a0b04c0500c1c0201544401c1c1e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 385779010 1250 385777760 385777783
    0xa050d0804291b09090105010309030c0c1509090b0d02041802040f0e010c050f0304110f09040f0303050a0c050409051506040803030901050105150702040e030c0f0c030f0705130b1c0f05 81
    0x300e40c20401d503907000801d617940610540381030542d620320030070515102d0300003a80d02d01d4000c200102070075a10008c0c20349103860038001c000080c01102c0d01107034140c1d4a01604400701802002da0011a03225000c100040c01c03401c40e5480c0599110071400c005071154001c01c01d030b01d5990640040c02941c581c0e015402d6400d4404200c00300042000141040740c400015a0f82058100c040400700c4196440410b0740a60030b642010b6202c03410740100000c01000b800c0c0140c0c230301c3c40b03aa000d00c41900d4030782c90442074403c0b102700d00c000b10340b05000134480564a6480150b11007002c0d03585030484240400890203da0058011010f40c1d007000003003105803102406082d00500f001e4880344c20025020514105900a15900a105a85510b032118000c5010000e4403d42c0c1c0200f41070b6501d400035040703041c0c0c0e1404014400350280c029051a00310074a4041041401c86401402d031125060968010000400901d0240782d40903060800981c6154654001080201e01c12210321011113894100030340b6100b40701e81c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 385780260 1250 385779010 385779061
    0x240e071403010212010902090f090a021c060513090c05150a090b09091305120f070606080609030a0f180303030c1d03071701090206070f0b01080a050d080429 69
    0x104d9100e91018580a41107604050b0016201c000a4001408020500100603403064550060007103c404a50040c4036400c0d0907489038550080301c8402c4800e032540b0b842a65445403a100e913400000303109800418040c1d200740c0e048003015803500009400c1e00044a54444c0b02180442c0e1582842e4109001c14003820035040e030b440c14241002c00141402c1001001d0980340d407203d050080070044200000c24255604d40740d5240c50b00c1584000e15016048100140c4409081c072400042d01c00020840500032a401c0001d1071070801c01004c150b819492401d001e40c100a070742e015000d03001050070f00f9140507510a40c1d000c500d20719204401011607010a072100b401c404810709107011964006803401c100c40d80c088030050b4444200301c11a0040c004440007a400680000d07a5904001c0224000d20145104858815141e40ca403500199101c44440000f0702c103920500400c4036590003502c5140d80944039000514400040c0480f080750412161004140444044140940c920440409001c215503200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 385781510 1250 385780260 385780267
    0x1080d02010e030403030509033d1418070b03040503030106080c090a03030f0201060b0d321512030c010507020c01050702150703030603080304120e0907020a240e0714030102 76
    0x11100f5200c0c07080f48001000e1240004284030986c509202d4070054403070070301070081c0b0800c0400030344144602c04000400c82810b0014070360403d0103c3c0c41744400389183c0240f840e0160340c80d1325580d5604124001c1d035610a200d02c1000060070b040000045103c1d5201e10059510303949820009443c0d000301406c54100d1545c01e0202d0000c98481400b424100e0f5007600d00360500005610090740101829044100380e10400212a48106107640019640e8000c0c200820180c4200740e40e80001c10a541303100f030620070314071008260415140d00c1004032511008150a070350410300b4000300d286078446004506165107400401401070340620503400309034800c0c2816032500362a9400901c0c440341c1c9008901c00070801050715014144250305c003c0165078008880c0e662401d203810010300b2421081c60b1080001c1441e5044012828000701342801131440341c00a040d650403d070341d81c0e04072103807410640340b145201c440b42a01003c0d81d4046d070707400f100050020385115401c1103110f4494803e00440f59029a0041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 385782760 1250 385781510 385781531
    0x801060804030c0213020d0216020a1401121a1206151c0303050a06080307050708160f060f0e0a140112090308060909010906020a031d011a10020109120801080d0201 72
    0x649490103540d03041310b1201502d205c4094520080c00350100b80c200c26440800c2c0c0000702060541c10010380c078021186d2415076640c49090140481100843c140007600720811045018036503040307007566130300b0458142404071a080c041040d194290301e4040880e0300800600030002c3c107016603104c0240c02665031080c0104080b6241c401500401001001c140d9a00001941c440036540060060310744c40d403d072965000c89060040d912131403070003010038500441d414074201d0003d98a0780b130304462801000d00c1c26645003410564070a02a03000c40300a00c8081942d1003e181d46074101c1c00054042c06888422500742d40c1c0004041e0011030612240341c6161400d4800803d8110b40410703440f1208980110903507541100751409012010402032045001040d03007201a0341640003041d404c10710314080540190060984d40c2601c084030120845c0114002c21040d141c2003401001d60403008600000c501c2c0107a030398440c11181d0183c0340140001d145440148070940b418849820210300d281b000b03000c000c055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 385784010 1250 385782760 385782767
    0x312071103010e0d0c02190e01061d0307060c02030c120303010807050409020f10050f0c100f1b050904110301030503190906020706260a0507020c010302070b010e040f02060415080106080403 83
    0x910341d050505c002d02c1c410394115034442210951100601c903040004031f68904400d03800c2c480c20302820000c1035003c444100c0300301070b100070304510f44001401002c04500c1c00350305898420400400340d030540241484840ca507210325000496a2507444c00031941e03036140a110605004c5507812080c880ca0800a1010169031050007a1110720411074000102004400c415220392144c0b80184040c51030104004640b00d9004c1030304241c43d1120202400700010102e0080b00f01c07201c2405034036100c6c6100c034800320036920650103002c03007600c05000044e60500100014240390000da104440a130b1002039161984440740880c00d10301d4682d0305024005a050040c00707502c400c11400b581007000405031011481010389103c185a04485482d1036400e030600f411031001030304048481da000361191140003203079544070303208650015401141c0a440c0d6400c207481e04a80d450081c00507150701000841c607030701590325400140000d019080c040340e05010030700005880d0007016804034040c441014208404280c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 385785260 1250 385784010 385784023
    0x1505121011121821030103110108010803031612090809040c080f010e04021c050c01020607090b0a1b0501050f0a140402011e090306060803040521070b07050c0312071103010e 76
    0x1600d0301d1025102c0e0203943c50314030341598605440b0701c0082d980c555400725044940154140d0b8000d81028040d80c4004c00156554042032041d102caa900030000a05625104070388000380492501d03200181e01e903440b241205039280300ea02580c1000001a22015903d040d100341c1c920f446181c00d00061501c0c05120f602851700052284814000d40000050210340e0b076100c683c000b07400c0c0350081d02c4a4010b0350400c10799424601e42e41501522480010401d4907009800e00340c1240c0e20b04521030718000700b41c10226080404241c000ca2028a00da4610000480030302a5602c91808026aa1414500490080240d440450406030035020000520016036800010117441c5041864812108100300d84100c806801070362000e00014a041004a08950040014070403102c00701c03072590f01261403812a481903079503034004035030715480100b04010014818000d0500d2500131415520119400d9010905155280d1b07603c080100380003882c1d40030401e02c07030300400b04800c003a0000c11202d0143c0c0e480c0395a5a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 385786510 1250 385785260 385785271
    0x90b01180b1906081e010f050f0f060406030903090f090b01081005031b130e01020d0b030c0d020d05030403080f0703090806070207210203070329090a020103150512101112 75
    0x2000907591044d024185017034030300100d200300415a91021410450041406a01d01c43c072510035804a95203070482e82c000050038001c0000349414a0302100341c0042402e140c0c120b00f4458600e100040c45051388000900800c80c449002c20001d41c1580010a41c544c0200f00303400744954807005120b5500d00048207040381e40c11030608054540f40200107043c5a01c03840c00c0e41941410707c043ca98240034190060705901400034020301840c2401400c15407246200340070144c06c0400c031000da10140c6018245011014010f0058030324158032a01c812105a2146902444a8100245100415911051100003404510041c01044c200250003d40b5903140d881622803590002003035091140041d000300200d03d50081c1224000c903501c2c500385c07042d6a0000d0915801e01c500034070380c10350719224000980c0300b90740010280c80740e0030345a8015002810181740b00d0180c1e074041e07140414981c490700c01200d80e5401203c020309440c040f000742e003c00d4031010900c0c20b184c01400d00c51140c4600240f450950030030f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 385787760 1250 385786510 385786517
    0x14040302060a021b030a020a03030b040e030f0702040902060d0b01080f01060210110c0118060b0d02031005070201020712212c0a0f0c0e0129090301090b01180b1906 72
    0x80079042c81d24180c101c1000c1004c9150700002406c0289142c001490098045c030a440a00c014100702081000712641c3d002030201c9500100110260742c40341100a15072644020000a100030054000c9a03007508140c17500d0405da07a0300d0548455540e0040702c0d04c1e0740005446000e082a40c10094020346030081d400100c040d041d29004240542841d000694a1124055000f00089038074683c840341c40d40c80a4405460151070306071040f1081c10040d04201b4402e40141c0148410980381150b0030051078010407140c2195424040364000030320740250f54104060707681e902010300540b0404080820008a020464586003481ca020343d121100f10910044000149640910304450300d0b11303040c0b81403104018010103503040074a0411452404460595400055840b0540c0e01e4103245401c180401002141c400b08411002d6103100440c0700604900314050000329540200e41d42c0c0140203030081e003254503182000c044540780384180b4401c00040d4a4100ea4152241c44014102454503020380104c0d802c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 385789010 1250 385787760 385787767
    0x41406030408092e0306061e020c09131b1d10050d031e0903050d08070903060e030702040c021e06101712030a14010806060108010e1003050307120314040302060a02 72
    0x45420410b03104694800d082c07401c074006013441c001401030145000f2400428074040101a4110207451001060100d6030010000d1214050805c070071003100400c001c070b401906c860503d0000d204408000042d80d81c0c02c080c800c40d641400440c1c44041c1c80d004400d03081d01f41810411050303190740010302e0700f200c005480e94030020880742022203c0703944c121480022a8820bc000801d81540840d51004490052094070212041b00208130303001c0d01c040c0c0380c4000184001000b032001c59015031204075110407200c00c0301d1500c0304d80d0f03010409030b84c01200c903c40507820041d842404605480c140026070803e42000d0080c44c07902500c20380030a00c1c1802044201011000740344e881c03100030044c80050881c404e40c00c9031a440c004507010041c120f5003140c070130b002e103000000062030307100020000e00425050b142d23404a41c0c01c0988240702e16000600302e0705209201c810000110b00180001c0400c0b80c004c040b00710320340e060600050103031003008464003510040c003002c000100303038045209038002d100500056038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 385790260 1250 385789010 385789039
    0x1b090e071811130302011b05032215090302040621140102040f08070302030115120f110a0b070506010e0123030705060d1416050d0504020a1a04140603040809 69
    0x40c01c60002d0700594200c0000c01450703410240750604200c0c0e10036a07603082c00c85003c4030340d590615a4080001c21a91041c0490b20703201c0c4500e410409111400164074400b20707070b83e040c5030038171280000300240400c003801c00910070750a00703006800250643c82d81e154480140b64800103207100800002606240c2c035000e5100b0001000c1d01210000c000d00844100150744610009840380c1103440b089100b0b600e40481c1450341e00600c001402120410118190204a2510703403912829144070203c03507021405043e401c2580c0d0b20700c62000500040c620494481c20769242089c41d00c5810b0f0030107071a6078002d000400220103440c001c0d01305c4403104100d40746c0344248900402d14164040d0042603210b0700118250200080e20b9010f00424081a4540d100e2074840709008416045039110042c00140d0401070300d155121030790801c0750010b2000c1c21404a40c0d55442d424501074290070b0002a8450001808110200142c0188402c3d0402124100c0c507600b01a50f9031106071046c031500c2402080290305024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 385791366 1106 385790260 385790309
    0x40e01091407090b03041403041716052103070203060408191713140105010801060602060108070b0301180b130c11070e040b221b090e07 60
    0x81d03d0038109022403009500c000c0094034000c840d0640c1c44681c000800003007006048027012007105480000345d5030704109640b141140c0500641000340441c0c1d842c0303540c000c00e1200d4988600c0180c8000000b0720705601a061020754103002d50300030801448102801040f469000710003800030f00140500586003800705e400302000c612483c800080d203604000080c400050301580c1e0317413250501c411600f282528400d80281c6a00d0b51110410455150100852800350140e100a0715845048c4200c05d6007a020510403030b445100701084041483c030080c0e000412840000c2c0c07241c1c168043c4540304c0700140010110190005080c2145080d00302c01c00b007203010644403050600221a100c545070707107110040241008034054101d42d03150358070030403040021540c01d2080f901290800c08003231001e01024142e50100c032403141010f480c024500c6d03000c20502c0550f143e034010000310712701d03011410b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 385611510 385791366 := by
  have h0 := BRFrame.cov_init 385611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 385611510 ≤ n) (h2 : n < 385791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
