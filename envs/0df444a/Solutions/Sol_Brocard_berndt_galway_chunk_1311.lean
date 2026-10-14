-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1311
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:18:40.987314+00:00
-- url     : https://prove2.me/submissions/5d55b760-549c-4502-a023-cbf081e9918d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 235611510 ≤ n < 235791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 235612760 1250 235611510 235611527
    0x30b010503071e0e18010c0203340212010b0411030f18060408090a0302030a0605010551040b0c060f2202040b0402040803130e06010f0e030a14030a090501140901 71
    0x1007412014031a5021700d04c41c0070b014443d50b91709160f00a6880348080302842040004003500b80c0002c804400203a0000030b6a0b040c0201080d80440e003040c42e0003034040046015129410005a02c5450010a107002c2c0f26004040c50148003550320340803099584007003034000c83c54010320a14141d841540014005403001c001456108005490300511a070b4950100e45898207583c412112107464070014025410700c0c803000c8600c442c4400c4030170340059807a07040e29121441e1002101240c40b0808a0a5101030b84403200000c64018036501c0342e4840c1d444c0300d00120341e081940180490f024900c08500840c0d601205a801000c200b40100b403c0c10780c0e1001900d00003482002260081d8640503a0201a580d910280008000380000707180d0380c3d005240044910040d03900800340c052040e006210040c0d910030300d61084c05005060041c0d2494210000034600a80090024545403c00700c0c00750310b00c60f020014010341401c90b12035522080d00c1301c0056406c00c1d0003000f0718000d54000d21904001d5071155000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 235614010 1250 235612760 235612771
    0x1407090308070201020a080a0203090315010510030b0a0b0703081503010c050a030203280905240c130306050705270337060603050d0c02060405090406021201030b010503071e0e 77
    0x443d0a101007d9507007060315040b0518190160300042842c8105040a1007000818103640191004540c10030b00000c2d9000800b4072904101a0717134a480c803201d41c4468175090003800d5000050b50300c1e5030503868001e155140c01c507040c101204800050b02d8050405024055031411300da16454200000b0340c4080b8007d42000700940c60300d0243d0030f4000304454000c0c0c070b034100460001e43d001c1507a01250505c1460515104030030001c81c03170020400458918080c200c0c0350040141801d10f55a41803440300340320900b84a4202411162402c03060181803504000140b005c4c84012081c61002d09001e0001c0040120301c003d4150503030886040392008007040a0369a944910030b54900c200790380d43c40702000309644801c80403600c01c2d07070318581031042c0301c0d007040221018403007441d1407810000070760f0202e0664001d510401d8002e9801c08003003010462280c054801141039031842c0e007459a0b480c20800746000003071091030700a0040e00340201d90640c0c1e032820885105040e10049414610744603030360364010402402d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 235615260 1250 235614010 235614013
    0x30f01090b030a021504061116091e020a0909051302031513151a24030406060314060406050601020a020a05090405030c0d08060102100e0a030f050d0906050901140709030807020102 79
    0x1c80e440161707204148251058600504181c4650a00d900642400e1a801000616600c00d03016208070900c6100c0d03d0060728071500700407400c1410fa9038103104141ea6020f40c0c02c03055001051000200d544241010121102c4c10001d00c903d44503018000d1452100c0c2030040c2d059082481e0410b801c0d402c01644070380042c0d280180c821030041580f6510007082d40c0c501c80c0000151140e440e0282c8901e46c41c0700e000411350449220a00d040c00780d036852000002210700d180301d800040005070030f10071a940300900541e04078080d20080c44035400203036110101124110350403813174200810381c2c651000443c068070a82c05403100d4083c504000410003290070040c0f00310f0700741c40100040d0b4910041881203219000460700c40301e04900b0481c0c00a41800e00301700701c218101c0e00d041000c43d002680040c0e80c0c01c40e00e415081c0944c41580219049940340f06a00286c0e01841c100011001004190341c0300d2481034541070020407080007020100000803409584920005040103003c1c03001c511800010a00c1610500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 235616510 1250 235615260 235615273
    0x90708060609150903060f090303040611120109021b0c0a050f1201020a05130803070308040b0a0e01060f030c090b0315130629030a0302030d0f09050609061b030f01090b03 75
    0x3002800816081c040d0f6440800c0214454420f800c0c10001540c200e2200d1a0111144c90040300b8944e69010050000c2e110a441c0d00034090405001e408030f8070700c11009046102d42c1d40e10b8013a004003940c00700d021448014000b402e02a83d080c40443c28152942c0028860884946080c040044c0c2c410104541070388846103c00324200e00c0c400344004c140740c80d05520b8441d11030003101582d80060340c0b00d0f4811102c1c1e4004111840001f540501e0103039000340d200d00008400d807200d1030850000e000c1c020865909600c0c01101280805000b1070001c1268464280300c280241c40d0480e81c02540ca103055043d81503442400705a903002309042e4016400001c001100c01d494800340c680c5400d9600d1036504101101e9440071750001031003040640154840103038028036103018555802990307403050070151050280d40e0058039030704c1481a006200c034240c01034226209410100d0040d51641da05440e240c2c0c04600c0b007014940142c1003c4281da1082c2d54175210101a03071318002c4c203103018020082610b1345c58003c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 235617760 1250 235616510 235616527
    0x705040c171515040e04020127180b0303190e0d080d0203010f0e07080f33010807090303080a270302060106021204032003010608030c010b01021504020907080606 71
    0x1140082c42a07800c409400510581c140500229455800302d2824440d0208000e0140340c842d401a140c01c070358203190504a40140402c15804203010380b1b04071903002c40007507000402a030f612030120701c4960862010000400140d0415540c1d124001030509000303408010000005c3c01000007a000c218081c154551019865841d4401580316502c03191410703902100500401d0110720202000c0d090b441e40500080c02e2045007e1b00301d00000704140f01c426427071000584a200c1c0c0a039003040c03460140d05d20306642e0702e050400018400403000360900082d20f881c005035250b4841c002d00c0089a0b05620740342400c1c0c858540031030107807044003c8203070f064002a1a051400501000b050941f80c000d501901c2d01d94144207000303040440b0031a42c0e4a400070140020f00c0032030110801c00300e440e00d10281c0f075000d2025500100303000d44410303070001009000100302e0640010040d000f44a48203426820b50f1581090707480c6c1210b400100341ca01942001e503003030022310340b140101c561641100c002845d25007410081c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 235619010 1250 235617760 235617797
    0x3180807060e030c03040e0c0f030a1a0301110d11070b012919180506090906030a0506070224010e13050a080301060c0b0a020f0910121a0909010e0705040c 68
    0x2111301903400d0752000404000d55081c0407000c07908070300002c91003460400b6180c036094407408050003c03000c5a41d60b425404006504002c1500701e850040c00078010900982c0040304142c0210104211250804500140181c519400c440702568004080301c0700da42061460814a001c4103040c0d54608a0400c161102100301c0d400f0b0606480c0d40110071090201e512320081c580260302c2100c0b41c0b150624070042c001a40d5150680300800410340b224021640c030040024584940781070003401c21301400c801c1c81103107a400300d40f28501000c030340291907440c90682d480720840c5000748188041c0890880105296807801d04044070400e000313000b2605641e03a15101d0201390780c420f90140002c41e41c050781000402c101140c406030300414841007181000d8050f4140e030745c248a4007801c0b03446000c5030003607140d5a9000310411001c0d500d00d0441044580600c44206205405032004144204407100c000f50540c0303414020b8109041070b41019160a40c90b1405210103032000740011824050141a0038614444 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 235620260 1250 235619010 235619017
    0x80705130f23040c09180605060705280b06041a131b020a0b04110112060b0d0e0d021b0402121510020601060e01080a023703180807060e03 61
    0xd00c0800300024040d90030b10007294601d10150a40600d0424241014454003c00071404803084000140011410890404020f202d01e8002c141d01c1301000c207462080c03080c0040c420650130000552005800e030104201140c1000d0010020480322942c4002821410190840d280040525034041224001e00c0e000503818150640700311411640d0300501c0003546407680c12070f0b92a0f52a0b0016043c90562900c030050040d41c001c20140c0003810030b11a400040c3d104080c2e03c0000001070008100207516541c0607455540a072203034000282c20041c044024040200b40c5085042c241d400a0441c0d40001000202c2d4445008282e607100340d090041c0d821114400a0091164808115103804105180c0802560b401c4042c15070045600203401404225003090102e0700e2082c0c03d003086205556500780b04800f03407003030031500b095060f401148844c4054841c92680600122101c0d99506104503800440072103240c08421582c5500250180002c6041c40c0d000709403140c000d8030040384000412010fa443d550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 235621510 1250 235620260 235620269
    0x4110408060f040b150a0314070b04060c0302010c0519110c0d060e15010308030c030405070b0403030203030a0b272a040e0703050114011803020a14150901080705130f 73
    0x1c0064204801c01100c61913079684000c004d000348410621900210300182ca00e030000034007a2a00c1000f04914560820141e0018504924101d680b2510f508d001050000e855008402640c02d1582440c10310b4050020f0740d641041000c483c445454030358a080740ca4540d02c0408030402d0140f00d43d40c60190300d59203213841d550780c0038800102d90b0202d420340d403920f02124440c108400449002c01400040c04e0001181c1d0018a100c440903200d03115030402c18100481c50707110100c84040080c0002c101a004000303144110400c0c2002c00c035031018541402540440303403200b11100c100d0310b02c03009180006a1800f50b000b17a40e994240350140021380c021650010030140c50401450b000c14100801407600301074a034481d025180511995152071540344550746480011414003004689074400740c50600d64860086400428000e80542e0307404200d43c24203003083c45503001e00b146100c0c100240b131160049505299040e514040304d83d440d640101e43c181c00c01c25007299070080410002407019140342c0004042d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 235622760 1250 235621510 235621531
    0xf0c01050d0f1d070303140f070f1a040614070e03030307050706060305010e031b0a0209070f05190806101d220903030b040c03050601090312050408030304060c0311030c0301050411040806 82
    0x7410350501404042080c2140045a0020050b400c0740e88d45410644203410740c081500c1e440c4080328500b5003c18403249002c1d03840c1404420170881400401e0f0080b641900500020f00c000303848034201181c00310b1501c0d002503015441040402c1c0351500c16801804074034000d240020700551680d40d0741c0e003034407904030a07101d0a41c404900e00c81e4851801c02d040d801c60600350b004000503200d44d40460b00c41c1800600700420b002c04801c9103a0b03854040c2c000c841d4000b000010612030600901c1014190f400207580310f5003c0d928611240f20300501449005240007440d01c0c10400c040382d05801c01c04402003602121b000040300c5007105100784000c1c001d00030000d101c1d44002c81c90b05900c1c4144800c807080d03c0030500825040c44140603150346c115101c4030959400c0081c503160f4902d2804141c1c4d4501c00c5500100c0c151000004000500a696000022032005071381c0601c090b04485070021038034001554402501a001c04c0108658609680030240d00340311003001c941441d9032107500c107061aa0403034080c4940c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 235624010 1250 235622760 235622773
    0xb0a0e06030c010507050705010e01050f03041406091609050c0909010801050103150c4103090120031303030f02030703140705040b07230316050f0c01050d0f1d 70
    0x481c6018024280011002e103452801c00d000da49449030390b809980306081c113011b003203a55450a644900104d8049920000c1110354a0078545052080144200301d125290b001d10b40c0821110000468040100c0c0c500d0524408081d051111250052030301500407900c6130710800c454580d9444681845008037100d400000f00e940c95803c0049600f2654031013000d000c3d241820280392581c11581d0900000910b2a10b00080d20f80000c1003111060121003039032042a0f04910640c44070b501400561040c0f58006c020301588154421803500158100715884e0703001000d0000905401da52010714030b80038024900400d52909041d03100040780e03c1070342c81ea00007940300e1201c00c0080054000340754210710140f030881d02e01361804410007018010b0040c028811040205c000400d51040000240048144130a40360b66622810454101214400c000c5909005511400000b141c01044c40c14082c10181c4816241c0300007008003a00502c03114401c48602561a00c0d0300e102450f00100141801482000400383d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 235625260 1250 235624010 235624021
    0x150806040b2401050706090f05060c070615050a050d05030f03010e06210c060f28121e090615030c0611060c160203070e070302071110020d120b0a0e 65
    0x442e100281101949955240882c0566848821a2070300c41c0c000c600001d4079621460a00880803501202614500c00c0c0000c0c0442048144010900b00b84503090030481c0464850082030204064071a0b16441480b00c14104040c2c200000000c94443c07185098038502182c03582da202c0e4070b82080c0c0000e001e00440b102044414180650907030341e01050301403601401750781c4c055650b079142544007000d03001c1c0f0004181860040da450080e942500e454011880804d103100c1c850105600041101c10002402c81c09110a030882901c507410b20045464040d211040a6607255000341c1100c00048a040c0c0c0e8a0f41d0460b003180e25450400d01035442040c1500d14146072030710041000c400c072566046550400000e001c003902420048401a0a0840d41240905040e000190424039203611103104140ca801c100b02c40550305900030406648a000e004000c0107000050000c683c000c00305240240e031040c070004400d640030700401860316084401c0882c0142060b0007040035941c5560202201425650602c007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 235626510 1250 235625260 235625281
    0x30606060f051c0e070302030102030f070912050c06030c0d150609061b1e0213020d0f0207050d1805031e0f0a050a080702040603020901080f1e030706150806040b 71
    0x14001c00c0203250580c14018070200e6680e004080c4603100346916603c040c0c60f150013200384060001141c00030001c5460345007030910400c1c0b040040781d1200000d0b1140102040e03d8120748814000d00350054000e01c50103119105010055101504034101001c080c88052800d204e280511408801443c9050000918024000d00b028084c2e0300280c0070311419072a03103000d2010314001b0320f100320f40110809074410b40001d0481000070100002940102a840914010501a40081030605200c1004015040c1481a06012030013110002480c90300107022152a0368495841c414210a1207004280c900f031751640020705c0c0c4203507084c1540c6c2c81c2400300014440300c0340601c0b0300700c0c0d6411140c014100a41c21580c6e40b540715071401c0070052421901007440025900c4551100000d140d0243c404820f070350b154000d0554803840c09c108000244074010110002c01a03d1000ba519881070304019030400c1c006a07200009850101c0c00d040c0380e4003040300d0000b401841000b0f0325002d240507504e0175030a81004500355 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 235627760 1250 235626510 235626527
    0x12030e030f071a1303060204081b01090501080c13080f01140906041110050903030d0207021c02060912120a05190e01090612090f060f0b040608071a070b0103060606 72
    0x7001940250000704500c81103400c90040707840582034681e07900da0411100f81c4503105a038001500061002c2004507581d4030005c0c0a8150040c000d00c2d00c0603e50310100111000c460501525000940a20214403001ca403480504101426242c452415039200c0350401d02d48800b1030340400a9079103500b00f2030924019130181942211b05603024200c545072549444c880c0d00d8407451494007505503071030041011880380301551040380000342901e85c0c0d80b000420f070070041e400c42c0300160f2084800b440c01d4051451080090810194050403203401e00001d44200048080c8030491240c4c1406051400c0286801c0040100400001515025100c00d080302a03a182d00090440ca1410301c1b07103114494225a0300701007040111100ca2425144030407000200341e0107400d80350001400b80c1d5002c0e00c04810410303590010101601d03c0442003040150500410003030314001e03c0f54585a030441c00d41400904405002c22034540c00e44480140b40c460681c1d01d102c0c1d100c03002d80c41910107958411003032040c1c59006c0d141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 235629010 1250 235627760 235627783
    0xc02010609060f21080c060717150d1203020403020604032307080c060d18120201050705070314030903070b0f0703050a02250c0506040e0a0605040c09060503060a12030e03 75
    0xe4419460034003030301c282503c0c58111280741008522101130104483c5c54119010080000140c9400d4100402c018150040e02c80c42c403102e5044c0003001035842c820206945061040040007247c02d00d20a8644035619901801907a0800d03400b00800310140e207070000240002c521480000e051141c3c100c02501c1c803602701050203041500465001c0040c0354001400b910008011103a031035507007468000000081c504182c26406203100d0701d03410001c1c400043c0c1c02a45014140c1c00921071507407050b8049810748149403004001c0b84c0104213140c0c0b580d5a5401075a8004500000c4914000c10f541340c0320360511003122500c0548501004000b201c3c1e602d406890f0304885002829400e0541c40d009804103515004002255540d680080c038084c0100c2c84281c0c80202000f5128996035510380142000a12049809619540c10510002900d080620482c40aa007059a070404000d040c06001c550030b6001800e215405000150701103181c4540403040340c8514400e4480c007184100f04000d050406a91209 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 235630260 1250 235629010 235629029
    0x1609090b0c22080c04060515040e0c0f0714100504031e27140910151112180f090a0902030f0115060221040510020f010c0201060906 58
    0x1920000901559540c03038001d03200750714098840780070782c0180010080000c20030701501c90200b0009091880850320750b801443c140d41c140051034882003480301d44036a064400800d4401004100002c1c000320901d80c0e004005182958070b0300b480c0490320b43e0542c1003c17805a035440b03039985039000380c3e040070044002140d0300300c034090110345015113010f13000d40e0000c4500c4101c4c5070310003c9150400e119000210f0365080030507080000b5003503002040c5810305a405207082c0002e442d452060240f8186e1030040c420615003c06070b107040d060800c005008980038074038000b0f0008010029030103000620801c4160780741c44403d29280c0c0102c501e400240e504c0e404016024002d0103616404945991684540c010084100031070151b855102181c90440c040d04120025480d219525000c170054800c1d460454555508584030806a002c404002421510240700040010403003040a23041c0120302c041290401d005071020300c0c2128251a084d541d1805403280143d64507a401e00c00c5030154480c5c0f0019018a08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 235631510 1250 235630260 235630271
    0x3010921021203070c030e030a1103120304021011070b0705010c080a0c1205060310050a0204050f1203090904080f1206090109060b0f070c050d0b0603150402030a240e1609 75
    0x1591a01c240b00142c805410007515284617414140509030454039400090121982101d95040c0301e076486103418190b0380300e8010600354131021031a11007500d00454006041003103c25420034150b5410b0302002040040e4050b00c0317800925000303400050100d5030300800002c1011070380b01c0320082440c080104a1041149801c1c5194000c1d80d00a801c0c125801201c1400603594a5060000740740c83c407000710101c15141007604002540826402410403281c007a01c80300101200c420400041c0400303808001c00b240d00c14030103a07c403071615905403600a07008101c424500701c2072130b40c1c0c0441503116201d001e800d90080c0c0144141804d102c01628018000300104100c040e090800070b000794404c0001002d142c4c68045411818041001040001050010031a00c80b20a003440c21000481d011a03105209016400e90115403120303d08000b84910381c001c02601d0480220f03511469803d1000c9003080c00d009036800d00740e0988507640b280d2405002c142e030040480c403815071000c2d48401429006880c106003000e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 235632760 1250 235631510 235631533
    0x403090501210e0f070306061521090206090d0b0402010f08130b090313060809060a18120e0415030c17061b07020307030c03031e0e04020a09050301092102 68
    0xc00320300da1182c921601048401801607601c3ca45031803420314403080d000b21200001001243c2c3d0002c02103c20000d02010114101d0a0a4400310704165075200039069681041e1207406031580b0002e80144001d119504015103000490020900c14000f254050306450078081550382245030241441341a10302101140381c803280c581e0b00e00e0040440100008003000118901e41010b0080d6100d041c02114103040c590f17a109130007001e0303130421b0b1040320150017000c1c040741800000d4003c1c0311001c0d0700c1c4026001d0030081659614107070683d0014100802201b105c480013540c1d51405000c9803e0f042c20260115a41141448141014564012485004040d075555640c84010491a03400114601c59001034084483d400e0319501ca2180002c3d8540102074010041003524040b40b8207507406a511140305410401514500384481646807001c50646416440f0398039040e0001e00b6101401e150070300f200c5035200082400e50302050011240e01c1041110641c80d04540c0480501c000140e10060a0f0042c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 235634010 1250 235632760 235632797
    0xc0f0b0105042f0703020a0206070305120f01060c080d02070606090e0c01020c0306070309051e2a010c02060306010302120a0203010303110d1d010c08030a050109060f0f0905040f14060403090501 85
    0x300c110450f048501003102824903000f4080b60401c10340140c03580d0350710a8103150060080e8803002c9011301103c0184085610040315810072410b030b95080d100d80d6000c084686501d00ba5802c01f10300081c00603000c2041c40001030407801040f008207071522004c244028594600307410f00c2444507180b81154440381482c40780b035800080d9141c0080143c100004d200c035050500c00c3c204080410400884484050b550b03a455100185689001e0036880100c0145402d0b405080078160000c0000c0d030000347c400c40e0580240c9042d100454011005040040c903000e05282c0c102061034044030642d0381154040010000d0540142140c1145284100542040b20300300c42c001d84000d6a42c01601c0054041c120000584e90140c401135000c1c60f0040340c001d8a91a143c00f0b0000640000d005203410942416800100300b00f021880100f92080f5002104010b41000a00c0005100c002c0c01507c0030010603440002040004040e81a0340d504107001d084c8c00e291a06028008c0c55065005d641003001721241d00d02004038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 235635260 1250 235634010 235634081
    0x300114011b05031e04031205040b0d1a19090b01031814150405010915020f0418200414180609040c09051828020607030c0f0b010504 58
    0x54181c00700d02039816052051440c003402c1007401c19100c04488604100b04404041c008a03031240f81034008074038001c070086525000781e108040e0800e8060020802d07241ca0743d000b29424504900c64916034010060005403000000c5582d941041c034445010b001b0b080d203501030099084028201032041c145403643c1c0042841214801810705050600d8144801805000c030240c900c800030398550807810b00b42030150007040805c20032580300602006803c0d030b40c0c44900030743c3c510f281c0c01c640312801d0a24010a02200c03d0320b040c1c24551050b99105000c24404201d1000d422012128100a858504080d29490101c0744c0c0002c0600c03800502040451403108038006076405041612014210b407a0340c90030808a01c4950001d6503091b0900c41008401c1c2c440b804440e480702c0303e12003200c030018442d00703501100c40e90148141d40e44524084600000d81401d0005180042c03103464820041d24081d01da10010041e240380807510002000c004010500e02405110000c1404020340b0340c030065460100d421141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 235636510 1250 235635260 235635287
    0x4080717030405040218030d141801050d020a0f080a14070c02010513080d020c010c020a0308210106050304030f0f0e04110c0a080705010501080a0b0703020d0230011401 74
    0xe4400301103000c1050034000d840090001030402d64603010051403403600205140001802846481080d20316148240711080490fa48a02c56928001c20411214100c800c03036641141441b030104405600682da520060040340d00131b50300d2071720a05509400402945003d030045540c54240080514000580304140350400401d0400c0d0391145106c1c80141c1d1140030308001d5442036540c0c1200051010008035030340b02c050b003455082e01c0000c0000801960348807040c0c14042e400111030034080c0002080b07400140383e4010200040341e40031800082c4412046001d803c500c00040000c0300740003c042c0c101c0305080f0041a5420003800d41d1044031001090304c421000c01178425510f0710240040019803004403400c0003000e0099070340e400c0341d5042c100e810360b008142c1103d0f19032a0800018403243c0124114402c540e01504043e000c2d02c481000301e02942007041300d028180d0303081203014005c1003500040350380640b03d112500c01c1001c99610300030b400274050380020303908010040e4000090b80e101e030301c296121 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 235637760 1250 235636510 235636529
    0x180218150a0305100b1305030d03060b180301180521070b0a050a02040b040801050402210d050c150f06040507050a050a0c05010e0313150903020d06200a030f0b06040807 74
    0x703551303003803100c0070504641d0700c01d041940c000140340c204905442014010380e4402e80c129110344601c01c2c0f04408440c910b104000b00c05000707005011508400100c12559990001c0c00459401220340d00400d482042038000c940580c4003000e404800701c1701003003248175181d0610307a803428100c241d11076141da0071006040c000c8255850b0700003030700010164140c0300604071100e4415102d54407048424000c18003070310700342d1180015208812410049114045980d8003600203071100259a180a480641140703240381d505000711500d20020ac0c1002104621803141003c600001d400d026050004854010f401003040200402c41c13064525044130407120340a00c1442d10460090241c2040c0703004241180c880c06440c00006212413034402c65550400598406031000900001e00490945645006100080d040345085240d0001301d80141e114030141e001c42c01420402c2940c800010400346d005600540229aa40903175a20560080c480c02d40710140a0b1103251a007400d05100f141d071f0b00d80700d10850640 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 235639010 1250 235637760 235637771
    0xd020a060305130b0a0c110307030f0815040c030209040b011d0120070b041a041508090313080d0f1d041e0203040303020a08090d0c080a0306180218150a03 68
    0x10260103d415218940c00906509081c02d05407080006000c601002030b0000e03000c00010302465001104480405a16450390003150744080401c3d01c041c08010141080d00260f801100a945c66030700880019652a540040c1e484030ba10f020801246e4040e040e0604100c08245242c50000040c009641929000d081802d86a03100c4a00e10203240c1101c200e82100e40603641001a40210f034078040c0c001e44460b442d08a00d00100c0401d6038149006602c01d01d00fa11114260a0700c0c214000c2010325004503504041d0307485c144000305001340c0f0071040d5008040c1035009100fa07145881d40103001a40082203458403400a85003070882403400301001244078461692007800d0015080050301181405009040654503450582000b4000f500111000c0000c501c1e40000600c814401086018440c101c40c0c07180f0340240340c0c030f40b40c80402e5000001d1050506a032868003141d40c0a605070f2100000c0c45884001d692160040107407440d6040500c00c4a01403842840003185801c490801e0310f001d01c0aa150000f032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 235640260 1250 235639010 235639021
    0xc03020c0a031d0406150e1206060411160c030b01090209030a08030c0705070305070e0a0c0c060b03070b18100309200a030209010308030a0b0102120702060708091504030b060d020a060305 82
    0x1480f000c5488443e4411300c1d003000001c492062030041198608162185119110b0f0740d01403054020100c0c6104076582c102d4000500c42e4542a40301c2800e40d81e070032020350300340035440c1c8601811203980d640c1500c4103143c040c402c100704600510481e0141032420400d42c1091040004240c1d16019804000c21640008c000200840c0030740c0c06440e600d40e0400100c4c2c4950341e8a09259807240390300d000c1d400304409240c001801350a01030280c41440d044981c0c81c038011054945441008021600c44070b6410300580a000500304486006050004590000a418140071104100c0044940c203580c1060500301004c130b2001c12042a0400502c10941c461542a142c4081c000307007500c2003c0e00000d500400070400403040c0210f10b0040c51150018000070420259480c0042e42d4618070a500d1a0300540204046d00050070560040c20f000d85c4a4082e03103060508001c0042ca41c1d619043c0c240000c500c0201d401c100740f00841980980082050350000c0c00300e14a0307004034084043c40c0c01003100307040e02e4101141 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 235641510 1250 235640260 235640297
    0x81b101d060f0a09091b0807050307020a05030c010e0f010b010203091905030a12180806061003060f03030f0923060a0219030e04152904081b040c03020c0a03 69
    0x2200c42122055896480d45030b80f0303003d40400d619005000100b0b180a25542c1c040702e00450000c003080d682c0e02c4009a541d100da60486803035200030494401c60055048500c002202000034101104108001148035010b0703040c2d003850007409203070301041e9a0500700c8012907070b40c002c01124140581940c418401010100c00300010440f242d10042e0180300e28080e1905118a01d11414010052a80e0740030864080c2200c002d00b6082c0c078002c0c0d40c91608207402150051601d0000c411401205040100744540c0d60804010056a554800c0d0041084524855000d1750321019160180501da2080101140e8407c010b034460115402c2075409103600007100c015080c020000b5000c14500c5090304c100c5519039160007801050103081c84e90246091030901c1d01242c000076000b10696601c0d88181c0b400c1c00c0c040120010400d046100446445010040801c07059401e101d0300e4800d032000e9480d464004800780c00e03c001c0344c54900c1c04200b01741c4144242c0c2d0080c030001c41c4000805805203081d400c61152001d026 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 235642760 1250 235641510 235641517
    0x41a0403170108010b0103112107230403020301050c12010b0702010c080d0e06060102010c02100504030c0c06090315060308070f061811030d030903020a030305190204081b101d06 78
    0x400441d03000e00008032000705401210401d903003030b42c1c107018080090300c01044a00030011407411000c9d400001241c0030a8005640d82d1100c06490f010007003003078161140e1282078050244000d48000080c060046d41400d0058036089107107010036034a80421214080c03042d44041c0a6036281c02d000148101c156032195812124198014101994441d1103030503000061641c20328040e041c1c050000018015801882004403151054000e001100c0c1c0e110341c220000c1000510880610000c4180d0314041641541a10007808894540b0441c1d981541451206da19520001c4e14590342000300500000f004401a070b1881c0ba071000401900543c689007420240079071140d5800c031001e019428100b070050984150803145829400d039600c1e078044400c01c41c19180c8a90340507025a10091202c00064440e074420f5910599852102c5520310040b8200c105a03400f551009485a0243e20200006071140c01c4400d0158011540c401c01e01140481c054045085070303984c000440c3c0703494581d09031a144d000c100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 235644010 1250 235642760 235642787
    0x3030c1e070b1c0e01021e2101080d02070905060a06120b0619080c0f03060d0503040302040515010314190c110a03023706050c09030109030e010e09041a0403 69
    0xc1c29101c0d03045010010380e2660100c00d211040781131540031a03a051040c400c0720003d00c1d55140740414004030950000f444e80c4011800d080c0304500c080b2581396081c110b58114060f015010241003402101c2500a02e80069908008407680c03502090000b0b40da200b8044004483e89800c00e1401e41c3d0b41c0302c03511401000e1134070007143c001d600002e1090b841201c207100781c0056102c0d501ca600f0f194540320187c0c0314602032000c440d1b41070b69040001c070340545805c04a02c10700380d1298045902d810307120f80c003141c107841d41a11348804100f081500d0804c15a01806800d01146410004800d1485d20901000c01c00020608000004e80c0d54441d08254610444c00780d8200081ca200701c48410030f59180081d503032511440303c0b00725110f0f91450212001407005200341b008a12200300380d0307400d0094854100034040501110010081045650000e403028042c03915110b019840d101c0d500d41a480000d8208400e02403110b225039904000c00002030190720000c11420106204890310350355914081d141c0c511003980 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 235645260 1250 235644010 235644029
    0x90507020a050f16060e0303030402040e07080d080a05010e07140d060b04030c0f060203161b050d05010c02060601031e0902011106010b03070905010e09131b08030c060603030c1e07 79
    0x10f01220318000198140440c16450081001c59603943c00445062000c00d000701e42c0b54008201207000740c07070660031140c0034042c0102594189596522428a40f0260500c0800424000c07000c00401c004184181401450681504045031034402c0000300103184282c203500b00b1890101d55645502400e42c07040c0c018200f42164199515101c0c1402c1000c0000380c8515098081d4090012641700c1c40441901c610304045d001104203000c9a40d00c6038030030b110108100c04c41c001c0212001545a4138441c0340c0000078000d200004041d982d80d80c2c000d0614078000d00c2c0506040c1000c102501030030031014003840040040c000000c0410351840125070641d10340400c00d20903c5910008103a094891000318018511a03c800744919a00e50040da244c509000089502840003000240002d002e0001c003101c0e40d02c1011203800d9074103c80c60b190900c41c8142c00c003841c55807000c40e105242810800c2050340203007084005504042c480481e00340d84e180019840034140d148184074003507529040100c88090160180c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 235646510 1250 235645260 235645273
    0x31815030b030f1609090303020f040909020405012117070f0c08061b041404092306010b04080a170c0a030c0b06010801030c0902090310051e150a090507020a05 70
    0x88006010740510744140d03209015100c1d004150407000a01203011400002090714420b1801c2245001025200c10640605400b00821012000c0d02c9005001030030b203402d80000e50a44500500c41150303c140c02078481e0305d206602c1c00d500004000d244a170100d03405101c410140c200f9070b047c103102d805032400003044003000c00210f20800c581c05000c042603071540c030101c4074170f43d80740d0381030704495a011100a0007807a42040103011090306602e1600404101800114408103581d9030b0728a03102e030080c414203c40c2c42504102c07441c800c0900c103450050481c4418681482d0808800545420a2020017081c4008a41c45100600d581d00700303584c1c03800c8092041d200340795861301300600800040b8504a92030a00140003910030742c0038184040c1681d400074601c5030024200a41d803002903200c2110719030315208014241d0000100c07030040e2407040206482c802010410381c1860a00994007800707210629148903407092958541c550000c0468060050200e2a525003110590900c103408002030020b01444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 235647760 1250 235646510 235646549
    0x32502040504030e1801050108041101110703061d070807060e0109030b09010c09050405070e011107080f07140102070e06060306281511150403030e071401091203020a0318 75
    0x70540b40444007518400140f017130307017540445808024040c1c3d0b400301da0f0040100e40071603404500c1050590341030402d851002c0e010006603290865035801114076a8881e2030640070703c50382c1501d030811003a4020041c10098207000059840381c1359409610108002e1424000301d40c4e2080c1e1143c0011500701d0401c0300700d800e000d01e4403030203801d10007a20b0303001c121103200000e0607040c98450603104503003541d2041220410100119120b29001c00c032107070130340324a10340411003820038003c1c2c80d440503040c1d0003441c00f61b140c0a03103480125203104881e415908680e4003005032080e003080c0b16511480445601d5034036529203001441c0a02001507111200500301200f032800f0301c0c0501d02d48159081d01d411008441291101218007031036498404403282c00c1b9404490002440e10300c8540c02900c03c0c1004205e4844c0f02c401a86494070a9001214020074851015a1540c1150110340070301014596484012900d0300c0295a55482d14801401c101400f00a103a8421080c82d11030040c01196a00b0070003014007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 235649010 1250 235647760 235647767
    0x1110a0c030306051804110103110a02070f06091a03061c0b151c020d060e061006110129011403010603090204060f0303021c1205040803090d080903250204050403 71
    0x280c001c03070100c0d140501c08210303460001004041800512184002e036a200d65540c100c001404003828141904c44c003088100101d144007400d2031491550007031000034504545d40080c1e0701c8603400311041c40100f5405004c0782c2000760301d42020243c410405036598235036501158500310f94440c443c540762683c1c07034030754100f00c0c56480306400741c04071900c03184012b41050108010901104c04104c00f25241561711801820071034a5840d07a0f5004060000714440c1044000f801c03c0c41c110342035241e41241c4817042c04859004170f4504a0205404000c00c0300804007100c420205c440c241401403802d4031040e42e004581c1c4904586817219a80c45036070780e200d59480c1c40c060003910300050100c0c85542442c40c04141c8420f22414101100d800da401800d5041e0450003481c020305103051490104030310080d02105100042c00b900c0d019500c201100c0d50303a1b1900c50f00c96424000001000130030094000d050003000d5000200796480c2070460001c90b1a4041e4410100c8075500c000800207400c5170505040000b850780 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 235650260 1250 235649010 235649027
    0x19021c030614010305060f011d04050f19020c03091e04110315030a02030a0224070b0f0f070f0810090f020403050d09080304060c080412120f020d0c1401110a 69
    0x81448440002d203224038015015900c084403141c2d04049051038408056125080004d40703284000454036a000030a0702182c190f0310116115820f01d4907000501481c032412a914800c0d103134910780114240300e00744c5140d0741c80e03100d03103d411841402c0c840702d5080b50140f90741740c070741010070000c2040040e4900c0f0040160907810442e021340d000e001e44955150031381808101d80038202d0303004019210028550f030810000222121880c0340382034041941c02008410880140100c0340919a806074524020142c1040d031074000b0b0141014207917000a0015030350f002242056100503a003081c1145682d000f4030081d0315000382d40141855400d00501d00c1e6480019030080007504d0142003030300e00c0b2601c01c003c03c0c1d032002c000e0710034610705510030041080f426215086500165203d043c0540c90181d031002e804850b122038140c00d0340d00c0032000b54010f900b5900100b0f14403c10000380081c01009048100c007801417030580d8000b5001c240e4122240c0d0f06a60298003144440d9005140303541c0741c07040b00000a03e183e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 235651510 1250 235650260 235650269
    0xe0d020f1c05011803050f030c0c0f15010603110d110c070e01170703031209020d02060426010b0d03141b0601060f081006030c022a03010f060b19021c0306 68
    0x501e407045203404c403492000c00803283d5400d41c0390300e4601962a2082025580000c0c400d00b0000000c0c050012211424028a0f85400007540200344c0c0800d07030038601400010681c002c806040c6802003084d00d400314001590102040c2900025142d06408038189151160580814607409550030120346442200038482c180c40707007000b100003289150203851369150981d00001e00030942000100306480c039036412001180d80f0140080d0784200880c2d0102d60b4940040c1c1004141e00640c1c0f803404071881c0c404000010b10010f120003805100a884041a00490080e1024041115a101d03914040c80d0180445410412070110960315285a52a00c0c1c3c41c0c410a021f06030002d4036018050900622642c825405450003090310410f042c50188150001d000c00b0407107005502440700c2c403507180e180018010b800041c28000d22101d840c500d00805003116000581c4140c80c501e0194203011b01407140c0c3c207684001111218050201030303083c0050b45455100482c0c0c03002d1580c40c1800030704581e816005581100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 235652760 1250 235651510 235651513
    0x309010f021804051f23030c030a0b041e060506040b180106180e040303020a17061c050a05120c12070b01030f020a0e042102010c141308100207120203030103030e0d020f1c05 76
    0x141c0ca00c4201f41d228402c0080186c4d02d503118101040c08281c0c2810900d07049886198540d001c1c00244484186007102000d040d103900340c1da001040700b2806c0501610038440012101c41c442c0c1d43c10103410070303907000040c0122010010361660078141e81400210300000780040366001c2500b4a407901c0c0c028007035440340e485140010710501d0035442c4106441700041c0280401081c55004a076544200e1001030410038094545100b5402082e0103e0020700c072a00056018843d816601d040d254111450801842d00502441c20208505c00c00704031078405490549502281c1c1d0040410340c0e00000d078001c54207400105030b00658209100411404480100203030441c1c0c001c607212146103035000d90032506603000401c04681e840d10341c6840c4490b0000144410f021400c2c0150100c0e442e010341340c1c9402e0000305401140f6a0021395041844160540702c6038101300c0d0f1004510b50340c1165802044843c085c00c1c172034000d00f0b064401300110b50342d5100c02c2d600020042c00b0313800354518142c07128000441040064445 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 235654010 1250 235652760 235652819
    0x2031e071b080715141303020906030d12200406030b0906090601050d0b010908010c02071a03010f090216080313060605060f07020d0203010b0d080309010f021804051f 73
    0x4648061070110445503124050700045207495140c44480038600c000b081044800c040303150034030b003806000d058075a242012a8020a0461041c00350401c0040c2c046803080e40200d007003100e029070250419040c4940580080740d43c00c038020b10f04080302e001c6600c0b2200007a000c1004901903078035902c42d0191210480b4a50910b88444007444804041503a1150004004210080110320140c010744506041803500840030b655410030182115015515000141c0001c0810081c20000b901445e01d081a103580139403444d4900341d00c481c5440054894200502d401158200f000c64194001c0c0c001e40e50401055540c91404581d500c80105080d00e0072580740f0318040000c102814641c0035030f0402a10001c3c2c0701d14010043c0c081100301d04041108991564035040c810910381c075034503e0b020320b20380715012168490920050580c00e640704010350311001403062044e200c0400e601e00c1c80200309a019039002480d900c1e000020801c0c0700c1d803180c001090781c00741c207400070745500c1061000740c41016403100d4000c0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 235655260 1250 235654010 235654043
    0xd0c050307081006120c0302061309020a091701021327020f0c011a010e040b0d14010b0a0611030d020a03140711010e0712060c110607020304030c080c090f060102031e07 74
    0x58070015150003521b2036410b0034060005040c1080103044908100740a84041039507400034100340ea02c200007510001e040004100f0001c2c820361241642106041d0003507082c901d04002400d00c0507a103104607040a031000900e01c0080c207a600f14003400640b03c003001e40d60b4488640305091a6801403507043c045600c4c2084440140c011369600e80c03082d02059688020b0358bc961810407010f41412503480d940b00c01d071070fa4290001581c1c1d803110a854a0504000315010168030100004081c2c41e900c69401e101c200842c8014004002c411628a58482100180c5480d00920118010841c480c1801901034a50060055482d0850a060210900303400280303d20351192044540707500c0f25104d4000b25055031100400011859080080d08111a01c3e00c01c500e504000410b80c42c000741941e001c0e0160300001030500c140402180f900c4003900c02075008284480c03141c1c0c08075070114001807494050080c01400b24500d40e20920440c0c2c215003210000002c0f520809450402d035a00c130401c21101c0c03041941c86401e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 235656510 1250 235655260 235655279
    0x20d0812060108070804050d050906090301141e0702030d1a19031401020a0e040b190605070b070e09060f01030b06040602072108070b060301060b0c0f060106050c0c0d0c050307081006 80
    0x10700c03d1f41d00030040c00c2c400110180581c0c45070404042c05070b204505004500440d10240705841e0610341180f42461103040200c206020490341a201c2c6544d4145c2d842000006900001100c1040d1085040012211183c4403000000f0312076000c070740d500018502c84034008903101558402034901651041c0e031000f40e810700385c900300c1c4120040c50010501c0050801401d02c0c00740e1003001490fa0180441002d0406694a0755011190f500b003c1c0109201042d2a403e100551707002c282c1c84049810244c1640300d51b500003900c04103000b00164807854001c000300c0d2250344680c10005805a014150548864881c80007940b503003105e00034080e000510540011000d54071548a40c242a00190413a180c09401d444424003000001e040580540d2104800100440403400500200b0f0b04440540500040540c9440c02c0c41c906a02c0f80003004000c1c01352500c800004588036801f40f81c11202d260700e0a2241c41c1c06014a00c090b8401540740c024590006001b07040821120382401c500352041101c151940b5462 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 235657760 1250 235656510 235656527
    0x71401050603011b180902161a07080123060307260f3d081506010504180605090f06181b0a020a0c0305030405011b0f0b04020d081206010807 62
    0xc8181d40c8040c2c1d64148134901541075200c461401c0105c101c0b2160310f410144044e0380c01031a00384107213009900154180310307012024101c041903103030fa811550308180740000c10000307060084402c00d00c40410b10030351007081c513528102446405804143c403890110f1000e4115800340c07100e0161608180c2209880250519103548a0510280010401d4841c1e490310640710b4210340c3c001004104a8102c00100100d00342287e40c85081640c84403c50b030305002846003041080650b280c02100c00e601484940d07a000000e550642304640c0342c0e091180800018540a026103900280c0c21102620030320200d40d199880c014800e07003040c3c0b001000c3d44010080303004a050304840c0c0b200c5900900c945c2d0400040c1f040000d001d400c241c1e02c12200c00c0815615060070b4103441c1c1c2e01c111019072000804114558105440b0005411b00c00e0329440156079a884031080a11032104c005c200b07000840c001021951503444c03031074020703400c40f6441e80c8840c502e400720180c1c2d4500b41c4140703000c61070000025900f144212000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 235659010 1250 235657760 235657781
    0xd0b01060306062304210c030f060c050315041112012409080c090a0b03060907030615032a0308030a090c120201051605030d0f0609110c06130305070807140105060301 73
    0x300b524251a00384007100a100801c6e1001d0b201861004040200c6c900c4812400a1400f82c0f040806040b42c0e80f87c401d0072900310008050030301205000304a01079003200780c44c10b01d843c2e0036200800c4404001c11074120610a1001d02558100581c00100b030311901c05491091030307003801c031045e850100a06001e9031030024520980c1c960340e104c40101907507803d1070100f0540113036a004002c00c4000102d00040d061030303811110b044050380f0070340302001401458012841c549150740002810642180c0728940c2449040381c80c040d19041c120342190702219285150002181c0044803180c49041c070414950203403045410035601208883c2000c04c0d0381c91404586015554140c407414500600c59141d84004c400241060703803240001d115800c21403d072030080b0080d145020000003843ea0801403420111444c078034007001c0c00d03001402840e4494800051107500058400707a0a0400c01c0c0f0752401b00e8440c07107101001801c4c0c1c00c0104044003080264141e4002480200000307100e142e0b40c20042c54200e882440741f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 235660260 1250 235659010 235659077
    0x9030c0504110d15170c0f04060807122109090509030f22030204020309010209120309030d0809190f020f1206011203020f07080a05060a090804060503060d0b0106030606 74
    0x842503d0040c0c0d83d01000b4011a020791481020344d4980c03201100c000801d402e6950f6030806c03140c6c11114074014030340c00b052510480d42000240d040c400860380c2c802090103100514a5944112000d01403000b140c125070301d0182c0340c568034038445500004d00c80304161145074005800d04002c500c110710007106032010304c0044640e850030180c040421142032903d00b0710924032214030420100150700c50b80011032040c1680c0c2e00160751004480d00740180d0001500a117003e03501f0070f10140c80f042d64040b0b81c4030040d9821b4a00b280c520b03100c1c0643c1034100b0101005424040380c18904110401015011451100e80201c424001050040051005854441c12031900c3d0303411420041c07041c03045000d20031049901910446000308480c0d0785007454940180c0041405500031072140041000c2084010b0384031400c1d5109220030203090391480c0082c0243c0c065031041c1300e004000108140c542c5029488016040b1100d4200c035695080081c008081e2130084500140d004040401c1480d8400c0421264401034030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 235661510 1250 235660260 235660267
    0x52e0209010f030c11011d070501020f0a03030b1f18060519030c20010605030d1107061b0501140906090a110607020a0f0b0904051e060f0301020f0a09030c050411 71
    0xb00200c00416183c00108148450060b000c000a40d00f481020300301c0c48a00b111150304050116030a140050300da200904640c030520305c100d5415000700301810b419a060034041581900c541c00552101600c40704003215040886c804829580d02121410b462003404210391801382c0c483d203080b02c9a100307070a140703000c01600460b81d44e40300348694450040031019203417002d590034268a04031151f040c0700c0d6241c500ca80d101c100520251905000000038040107082904045c0864000c007a140d64a5106007418419802d406481f040c600701901c010341e41e40f16008005060f480288406000c105540d5502c1c18840c800000b030641c480021403012994000d094034412164074410000a54000c08040380c0107084490005040d044080050700a060b100058640310802c400901c41241c0000300081c0c05240d405ca1000504545450b0b9a60007d00030f0720807a800015101c0460701912401d442c3c441801c0740011a82c0c8020b0b484052107040d28410004200c2a964440412054030101401d00c2000c078000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 235662760 1250 235661510 235661537
    0x201080610050d06030804090516080414010b0d03120506192304060803030103050c010c02090a02070609021f02061605121b16110a060e04020c010207052e020901 71
    0x94072040c4440407032922500d4603004442581c02c0c1c0b0001e510441d035001000c0350074040b264850141c2c6071f000c0c40d05249242c046000314001090b058010780090200d41c21880d50f100456402c1d004440e00c0e550203085183c1600d180e02e40186000403074a00392041343d2600c1c0c045203051034804807480745013004150b51143d0a0034a10b0090072110400300101642c910305500c0c145c07988860003000c000344012000782d6143e41c514184603080010012400741008000d01e00351005940750281580c00020842c0c0040e101c1e035846c80d011005190141d0b01a5000555201011284501c1a19840d0b480f626900341c07100e94403842d850b0402c10500c40c14000c04258140301240101400c4021242e1180c8042d81d03c801da55074281909510398010584921040d4020050006001c0d001c2e44010840000307440c220a41440c11030000e00015210b0b803824400c41d00010491114402501034803903d80d0004151203108200ca00c02144186140041585028094079140e03072650442c403d03034051401c10f850f40c00360b0080c03a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 235664010 1250 235662760 235662769
    0x108060c09031606090815070f0c0201180306020912060c0d0903022a040b030a02090f06040b0a080105220b0f0604061e06120c0909020c07080a08090a0501030902010806 74
    0x141005034040c403071540e4040d55009540f40b030000500301511036040d25170500c1c50031400e01d2084840207100f2030140041c4a4465845490326046521701c0c509421001c00510040b208101c0780c81c6c4c047c8400365920400b10a103e1a03a00034004078408450900c001c590031800c0c0d9440310f60803906120348e60b8041c841d0000c6444950404a801d034468416551107400f03940712170362003280c19002491500703501e0350f901c1c000d070500340300301007a51008600415071215181d0004010002c02455540038030a040c0101342c86440c1e80d01700403805c000c000d008285058907203010034000c000c200c03000385021900301c1358611000902c0c0c6a006026400502d085c1c495584c15526102c50040135100079009642c440c80001d0142d414a411030519491103000301d00689070000c01400500b0141070345040c189490303100030449800075446011070758803403805a1516070240d07846042c04219031003045c503806502c402c0c00400401c4402040c00b11400c03140000c1141d1548011000c440c1c0051009001c00c1c1c003040441c0340c5150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 235665260 1250 235664010 235664017
    0x9030209130c0b120702010b0901081e010b040c11120f070b07050706091101020c010302041d04050a12020d0809060601081807210204050c0a0c1202240a0509060108060c 74
    0x24500c4209065a6285503c0d1990201d08482e410b56041e10512401c01d0f4280180381071844200c80c121159410501e4654070340d00f00f20b551f21740c61021410750300c801c1c090030b40002c2900c0300010000c12072511b490101500b21858001404554010518603121103582201034070410700c00f6425170341c1004081d64400300c0e07000703014060a017808030a1222400140302c038026003403020305c03590a00c011242011300181c40c0c41800320009060600501c8240101050380300d044029008060a4025130386942c100300d8103040041e9800782c1455416201c24111540000c0c0e907070466a580e6844038001c2d60b40c5141c03039882d00000d840301400118404081400c80c85811100380b84d13525008150340c0169551562204100c6541ca010004501a100c00c481503142034807a66601c07080c4061501e00d024190307030004241314410900240156141c40014502c284200190041104040d51226481040c14800036800c14211801c00850741402c00003407544501051450482c0d1005000f4046521010300002c0c8a40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 235666510 1250 235665260 235665263
    0x110a0311010f0c02090a0608010b01080f0610090509010e090610061b1a010312020c0d1a07090305030d02090a0602210c0f0318030c0d030203030c0d2a0305070903020913 74
    0x215201d0f0050390307814000b81d0085002480000360b8030b161401c290700391401c04a0413814001c5400401144101d007504641c1d10410071108044a02002c103c180c62040c0950030007504002c4460002c15401e5910000034001ca410700708440c41613039900287c000d044010f004150002c0c00c1c60040c01045242000e031410124492803a15469450090303038411070b0f0609074010784016903800c1d40b00b02801c0e0103001401c240c110680e8400b0066002c3e0321014101748809d0703c2004004080800290618412401d84014607030050a90b50344000c0d010300400650003200e249485600e80410000f006070000400943c20301100ca02c01400300603079111000e20740c106080c200c0050044000220403100184010701c503100a2030140040090044280f52500c043c070340020340108401c00c00e44c0e0200c1e40020641ba844403400c40070581d55402c04071306070090000380104508030001c129030700f450185880c030484c00181d6655010442a80c1c0c1e10b900716104a401e11019400c00c240401081c0300c2c40803c6c0c429129103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 235667760 1250 235666510 235666517
    0x90a0f11010504050d0c06090605071e080c0307050609070506041d0a0e19150908070b04020f0406080312100f1701060506040f0305011503231e0307110a0311010f 71
    0x84d680c4011403ca5540301104070380081e4a128103010090304801080c02920251030305c41c2c280314080e59080400003d4855a2840312001c02060080011040c102c40c07040c0c041205603a21140c0701c1ca8466a2072070150b0b030b500d000703000702a0301203954240b100aa0b01252000178016005080c20340710900c203440080d141040c071175101e61008410702002c000320880581c19006085101c68a0304203107048212555006190509007542040402c503000103403074a0710340110007a14540c6071440001c41603000c0e06030740ea4000d030424000145014003c0701800340100c00c1c00035480c05950b021449950484940a191105402d400c400d20009540b07070660300d400c905a1000107000703a02ca40028180f908254400c4840c1c41000e9810f100f007100c20b0180244a540001035540d1050840c3c0c0c440010b840304404000300e800012940452940d800c00c0340500c18441c04030401201d07101003240980300d40c0030804c1582c0c803510940140c032090402e50900320482e60407400716800207a00d04011201139880382000c0003013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 235669010 1250 235667760 235667767
    0x8030d0b0303250f14100f0b0d1502210108150603060115030603320109170306030c10120b2403040305040e100e15091f0902070c03020108090a0f110105 67
    0x72032803019514078289545c010504090381c1d100c41d0042c0c5103008001c126403820802c51504584a5480d542c0d11154001041d4220400341d20640d0b0003401076910100e80c41d914803148000500b00261880e0680e030f143d10545d00c0d00d0404850240c07010100b560070b5071309540254010455811880b45100c090f4540340b40100342150380340c842042c2114130183c0307003414081500b04080d86480400c071700d14544c60240000c0c400c02c1000e44030b45440e0100d200b484482803000000003903031340e030b0140a0083c40840c010001e01f42c0020921005048046042c00c0e1149a49046034050042c6000c42e40c1e002411181000381094604030321000341d403500081e03c11828403030280008114140b9900b04140300303940c6071030310b14002da181c00c00218091a000d801c070003400321403080800c3c075030301d0f040c41083c1d1045c0c01011480f0003c148420084880c2c166510580d000351020800320204000903007190308a80c002da0722040703640c0710310100c40d441d40080d10f0004c101b95112541140011901407180d4034201050408030309 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 235670260 1250 235669010 235669013
    0x90d02120a0b0f0108070e150603060a050d0b06150421080412051c0f020c010e010e0310051b0c06041b15050703110c01170c0f0408030d0b0303250f 65
    0x1c2145054a900d00c10074083e500511841d0070412000004161103d00240541000780c6445140d01d4204803903401010700000040d4103440e01c2907175200410000c0c0c1075412082c51824225010282543d5881c0b24551482003e1068101e01d4152020b966040148807002024050110b0198180b103000301d90340e145c1803200290791050040384041690184015048050504081c108150b41040500c403d12181110f042c00c0070782d001684910f04d42080c200311005904800041e14040340410041ea894891105c1c102c0700a01c83c0d400003030140111000209544a45a110b00d4446c01003040308141c0e5400000010f022480320440840009060403c1c001a41c2d210301c06440c2e49191540b56901054002400c1c03c1015842228004046816405000b0300450400000e110807800c042008a615440e00800d44450318107080320001540c4005595589a41704516a01c0b0b80002c42d08420091400c560681c1c2400c0220071514020090740c43d1266601d41002e18801d080c086200c15a800e0780c406140c0d07070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 235671510 1250 235670260 235670273
    0x110a02030a0503040c030c180b010c110f240c1203040b0f041703280506012f0d030c1101090b160c02150d1a1005280909060b090d02120a 60
    0xd450300a10000c01c110101041c1c8c410383c1c82078452141007003007045507000498030520000c00004c808403070b00b40d000a849030000c6c90f10389058821610140301010014520748140c0000c061056103201034413810300398241c00b00044d0000320740140c12176058800003166081c404081e039038800d05c150000700c5003580801c1d405460781c104440746814901400359041c00d1a401a464040700000030500740315a141280c0020040e075603e010740c1d00350743e071210407480c0d8082d5410700c1440030f041d441c012161a4590f00d0401406020076001c0c02d80403640b008400403034040c040c05150036640d0403800d210007070348895623003a1060300080d003103d0030400626200c0c40143d960211320085c4003d0080d6031520b6040c080070441c00c44034203620f00c1c40c0310b289001c0000321a40f11075a03e02204101405c02e0ba0b00d038a408000c911b0000c0c0c2c8400501c112500414890304a15044184401916800c0c1d0040103041e4481450111500c50302d82d03016032050503003200900500e44030a07030b0317020000c4203030507a015401c1075138400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 235672760 1250 235671510 235671533
    0x30212030c030123010e090a021612030e030c0714040f15030516031a06010c050a0302030d0b090105130b1c1401050c03060a030308070e061804110a02030a0503040c03 73
    0x80040741c0300000104254a1528089080440340040c203407003186000001801003250b4181d43c80c003c0b90100001400c46105906035110701718900300001a00c20f181c03034442c0720185144a100d000c00d1070702d507201a011790000180d0321549001c2d001440054103242500c0d1306510f0012030281e1054481881c5800743c0140c0c010006903086140c0b203640658103606d085802c2c5450030407141d40500344503000b000400d103285c41c0c1060003101c0c0c1106a000340c4411004884031030b030005010303046e4800c0316040c000300f40d0f00000810404040b8001001443e20041c108103400c0d00a20175581e104040c840d050710800b503190b1102081600c0242110b03003a117a100900c1140c031b111844c080e1f0b0400c6c504011011510030030300410394041c0d08a00c0492440c03402800140d1041c0e45800054108104500082c0381c25000e01e1442c02e501c0d90082c81c8986454081140c846011030791094640110304004100000b10320301704c1070b641c42d829160080d6082a4200c1d0b02250340760001002600c0c1d6a462840010118090740b414 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 235674010 1250 235672760 235672771
    0x21b012f1306030203060f0103200d06031e150504030c06020a020c0907170a05070804080d0608100c0f08070504180609060e0601140c060604020a0e28060305010e01060c03021203 78
    0x15840c2d1034a1b40c204084035824400140c18142481c440380151494000141030f446030398082561103c40b444d51402c01000107070802014541e01c1c00804403c0304100c0550b580d140d20510591540141030010901035502c203440040c085807070525010300059880d0040c00c200b81480c030480c0d42c554182c40004000c2c11007964000c02044103941145030700310b45c0503801940101809000d2001f0305040c00c00601d22a00100080d00c9103c000c0b8108402c40c0a5800580c0101007074001c17140202c06d000c680c640113000003e458030106104144080089000e0f45d480c51042002e80c480a080c1480d00391380404084d00010b00400f0303a5901c110206041d07165101e40c0010b001030701c281455a242c00000034013680120041c461030b08500380f22040c600500000c1207544548150740141c5c40f40c074030902c00e444207502442404d602002e04035103000c55103210700c82e03960305a80041c001c11600d41d941c0400e40c1100c1007809641c14124270600144100e5000d0b02034170108a1203441151210440c400c11543c550704251203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 235675260 1250 235674010 235674017
    0x705090d150f1509090201090f060e0a050102010513020f0a05060403050703050c01180504200705100b101215030203031206010f090e0a0c0e040f021b012f1306 70
    0x4500c0030741012445808a4111a40c0003000a0000ca03800c24100211621441900c42d40740c0c1500320071a40304e40c002000400100c440301402988881d005002075001c00440e50042c0740000300004c496105000b0300d8001d51100d0000000d0314490780034050305040202000c0e03045031850000040315103594000300b0045000e200a85881e0342149000c038105419001c7e0f00781048200e9000c4007180d4069004071049036070440300001c140ca284804800480300b40c041e045000000440c0c02c038140b28002c50191115000741c1d0007000215001710070407034100c1081e681200001c04038009484602c0080d40040200009069115001130f44da50000f8a568007542e082400090000f06014065801c000300482860580c14001c40300c0e401e0443c200e684110051500c00780079201c0c4010f0003110b00039010704550307110160052000e00e03170400151020398010500e0144c0c0040d0140c103d0080340c410702c2002001500410180c600e06c0a10480400795404d4202c40858030380700b0022800c06005055011b40113094646 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 235676510 1250 235675260 235675283
    0x70308060f03060601080a0504150914060105031f050603120c0d0314070c110a0801150602070504090c0e041106030a060312021f021602040f061e08030a080705090d 72
    0x2041c0100754900c203403414042d0b0f01010500c9074a0380c004411640c052001c0100003560350f103a041008000701c001070f903002050300d022000401e00c505040c80c040b00d601c4031012035400303903600c0060564071500918149035611420018900000d003c4d080145c00420041c01c4071503c41040d070568090f0f5010140b100740e658800e0030102c1e6102d4044c09140080a0015044400c0c3d07d0b02680c083e040c1d00030244020310000d405079950b800c50fa01c040c00c60010b0940d0034000c0000f0465041c1c0c0180040701405441d01622030300350f0005e640c0c40c15001d07208400f0b07848408485901c3c6021240c00706483c0150044414643c6845003410548403000654402c031000d54020908910b035040180760702c5041c00465085401000703400c1900010411180c011100714000180da5410440c1000d81c10703c3e800d00000d60050802d6504444100b02c0d40085003039822005405060080740700401c1d000302028480d084054000303001050480e801000015801403040c01d02030314041c1d00400003801d88140307210481d100310515 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 235677760 1250 235676510 235676521
    0x50f07020306180f0109030f030e2e0e01060302060403120507140a03081e010515040e09060603071517060a030506191104031713030c0b0309120a080426070308 70
    0x42003d40813a003c2072000704400540ca840082450700700010344d03410703da129440144224420080081199940c1032909480d1412102c010003111030008020f002605105c0301a000300c07018800c01c000c07254010451454945140e84001440c0c82d07105005061000038454080440c810a05900d01511180d0107031070044203901c0e01616658001e412301103001d43c03e40c03141801c060f550700e245041d500101c0d006241e20705800580d000707501c21134001d40c2010f414003050100046000404ca401000200c05444860391a40b00b0a070241c8585111440090a8005407502c500141c94965070480406081c101c040758503515041e24000080e5036010050107101c3da295031460051281d0400d1880340c821040c9031038034507119400c1c0c4411380c1750280c0001900080c000050005418030300000d40d440b0510a035210354170a420129508101c4400640740a136110040c0d001b109031048402e42c10f0681c0394408a070702d0326250326040c440b03201c9030310300495a201d43c0c40e581e07812108090401207101c0d40d01c001c02c610301b5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 235679010 1250 235677760 235677763
    0x3140c1c05042111100221070b0415020d0c0c020a0f050f0103020309010219020604110303122d0a0b010e030c0607030809030706060303110618030406050f0702030618 73
    0x103400300c0003000030034003050090f10380010f00007940c08482c00300454a004241054048002082070480c0e010b0322900303410700f91580104094100c000c400900881c0c20450fa0812201882408801000d0700e49103400100090030003100442802c0808900608095541a0703c0044980101511012456200b151b50441c41c2004045020b400c1d4545101c4072a0310b44000300c0c0454190b02c03141418940c0110000e803503507100354103450079040b0300005801c4100149102a4070303000e050301c0c140c60700396900c0c0312829541000021075100c1c1c100030708040038943d6081c10907004044202500010402204040b1120410200c0d0150154240c410000784d04440c040c005000400913071000390084d04034402a29856071500182c0b02d080d40c0500b40301c0c000307a5504660718150320610000030001894004080285540318060780c0842400708111000c2e502d450340ca1100305002d12210714290350040205000c15446500644081650040c0107810700b001540001c0c2080c0301103501030f055400d04003c10300403480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 235680260 1250 235679010 235679053
    0x2208030103030c20010504090908090d0c030c0e040b01090905190b090d1403060d020a0f080c0111010b10110a05151518010e10030b0406150f12020d03140c 68
    0x10036401c50784d1040341c0500040c015000e00e02c91040b40700ea0755040f040502c8842012262119801008202507094034074100780411418081902d4103040c0348000300d80c1101882416025035044481d072012a171030444540e02030001c40c1c00c1242c0502619a042e89455507462060190502c80c000143c15440d0240d02caa2419407000702c2c590400c8402c610310a003080304202102e41055007a622140880c2d06800499480a0705030700500f080401c0d24400a1400740c003181c0206010b4090342d40841c101e10f0144214240d0390210b00381507000701c030780c01c2d60420180260703448103440003014155668040592130340c03814600c0250003881c200811004000c205a449071180c180424102c42c00d0090541c40d542c40d000815050003902c80d0000401c1c04900e0000b07486168000440e8880b5240e601072074a881c004001d014050922089002d13054070208100036000211030640c2d0011298418515040d000c104820103108400e41c2031003010141d03c043c4c5180d410041007441110b0000301200b21b000c00c01c0c003d0051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 235681510 1250 235680260 235680293
    0x60306040216050a052e0b010507020d050604030201050606030402060306041e18020a05010f020607030f0f0507020d1e0509130e2407030213030213110d06050a0b030702062208030103030c 82
    0xb01c820400780150180800c40b0714605007014000441f407400c080161054440c110001c0d60080d1074645032010003200080e29889917203e50700034007680c1c40c1c910034081d0780e01041e140203602ca6024800200c041c2059800f40c440050a5040b500100ba218010070301110100e0581c5c6510070700300c1e03155000350b081200c41c9500800083ca0020044c49400c8070007500c81700c01038842c208068480d06c8854201010740c02030709401007540c108104d9030808080107582d5420540c181000b2481c840d02070750762040c4000501407c07000075100c05180140003000c00842c100b00c8540308210b141c0e1420b0b545481348042001d08101015101b1510000c50300c070358503440213040100000304250040003040c4100e214150100101da40c10340d4000c2c00341044500a81c042d107194000c2d440308140c0880c4002c08096260062001c441003520340241c1c07103468500305201c0784001c031180740140c2d00c20b00114680c0362641c0d418102002c4800320341c41518110359280c51712980b0a03401035000444c010120b50900060041240c0c054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 235682760 1250 235681510 235681543
    0x30207080307020604060c1103030a0e130e250806070f110f0a030804260a12050103052104122d120f0311040b040314031602060306040216050a05 64
    0x2542d281d0004005108a0240c0c00030442010505410001010081c0d03c900d4001010b42c0e84803124081d004010040c24600144201b5a41c2c01ca8990805a4894502000760003000f6101c15964200d85007800303c00c98400e03002c1d250141300e0003e0840d00501045000b40f217560354041c040b40d40350b0700c000c041400e60305c0019010b80040440c8004442c3c002240e102c00c90b170505024181e503482e41030100c1220301c0281d40480041040c00c5601c0109503080c020012155661200114101183c074041c0c2182c41c00d0100421682c003001c0da003000c5103d4030350860600c1c590100c0c840c0c909a11031180c2d85007400c1078030741152044155081484443c1e01034030358542070409401c0c25441020141ca07105031540008400b1018029045002c2c91000e1190b01f007088124000900c0582d0740e940c440044030300c1d501900c800c1c0c40c404031440e003106030315001004682c46007145042d030700e06600440e02002142e9202034900c1e42d200b5402c115100031495542e0341c003d02d80d4003640c00b0340070417101da041003070414800d04140c1709031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 235684010 1250 235682760 235682767
    0xb03010b190e10030905070618050607080f0712030614101103130f05030709060503060a0c0201140c030a0f020306060a0509120303010b031008010603020a0501080405070504050a02070302070803 85
    0x440c8042420785420981d146003900400415010969500c0c0d100c000ca5034100120607885040c030b6800d0b03004001503c0c4550101c50341c1c944d0b00c2c070b81101c1491420000b40380d084080e40b01041649040340103000c1c51409540460b290004405c0e01c010160710442048400340110598082d500382c140c400e5400401445015140e00000440060007044080a008044c004c01c0d00c0300c480c40440c20000d842c0c52003180c4a40d802c1003034486007480c01d640f0b060310a4521a11403481c0100f0000c0b058041c2104940001c0e0041545444030f807000c601a040b005681405c547d0b0310104400390040503c07031103000f121282c1e401c65980c14410780007025900c00400d003031035803801082480443d0f260b0301c049075180200e501d4007984402070140006c1000b0800c105081007071002000211703070051544020b5000300c0030480001b03007099a50035810300303032540c0b440b02a501c00b00c5108100185c1d4020390f90301d0f5103e880b4000ba5a40291650001001c82c0c001780c07582002d80345d002c0760950425070100020006013599a004504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 235685260 1250 235684010 235684019
    0x906090c010905010807090f0609140a1a07140105070504080c04050412120f11090108070f080a0e160f08070602150604020f040905040f210801091107021f02070b0301 73
    0x3202d1082c4111410840039200044200b44251030703140240400c5000d0103802903450400405042190044900c0603c4802039265149841583c8808651b2000c1040c0c05100c410003003d80650001c600c1610302061100c546465000203108562282d1102c0c3c81781922503080c000c015280c24480340407640200d281c0707414840421440c2c50070002c02e0350355281c042c4511030743e044d017000500107664580ca07545040c564060444494040505a001c1081c1e03906c2500d1758404000b107a00e44090550940410001d80c0890b00070280c0c0e0b0045040358213002c0c00c03560701741141c9000840b4810f840d4420090581640d5081c00828024051070001340130314030080030329a1440b1442c08040c880509094451903002651403002004901a40d00030516a9400c202c0e0745800d0401500e558800c00e400c030f82000842680101038014812044108411a9140d8216030f0031300e100c29009250407508400008030511110740113a03070b00c1c4012031600d0009100740001e444230001c0a880d19000b0341050703101e072105000622 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 235686510 1250 235685260 235685267
    0x6060f170702060612030c0f010b120a0b04110f030d0f0f03060b3a0b030114070e010c11130f06060c02010c060b0f060705060402031209030d110f03120906090c01 71
    0x5130010001c607082040302414400652642c852001040c400340203426000b51220380c190300814510505131407550031449406502a00d03070b2406c00d4000d100d00202e038007040100f401a00004000f00d00500070000e204441c01c0040d15045e429100440060f0b04025001030b400c3c1d10000111141006050a128181c1483e0741540b07180150030001c5c1c80d414030403900f150786d8030201c01d00f00c01ca88201c1c0e07840c00c541150300300c0c0a405080c03e8400d0502075800c00408a062001196035588143c0b55a611404164003c074011685280107202c01d80300c00ca141c600f1468079540f540580500c40803400e100080d000646e1a445080d112035a1003402403088904422000d80d8100c01d00c0200340e5481500090390400741c0001440580c42c00e04280d0308100c003c81c1003401c0010000b000c90003140224200c8604808100e003082d860300c640031009806030009010500b159000310000e04000108009641428548042480c55608078006140001e400b900074051000c100f03000745c81c1c100062101601071a0b41d0714002a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 235687760 1250 235686510 235686523
    0x10e0a172b0f3c0606020601150504061b02040603051e100b1c140105042a031104020a030f050708040c0b0403080a1215270501050a151206060f170702 66
    0x81a10b03c3c21014062a2205800e200310101c6a41840030001c60340c40d054020360b611801d0149141000178078001c0815a4058020b44089803155501d8165004604400c4080c80e5940c960407a0403903200c0c1c038080002401440000220804d81071590034800c2ca01c10030610301030040a4a95000e458120003445641702c080300d428005101480380c2e101c04a042c5404103101d04c0d4031081c643e2175407034003091000300045242c0080c88000e0352201001003215054048100380c50307501c0024143c007a003150598040c180f903000781c84040c01500b4009400e508072030860f02a20b800301c800e2800034149804201c104032821401d00058200c6040d420b0829066036103081f0035100311300455060000060754820858141d13000000c400000baa00c05203901d41d601c408088a40c3d9a50350b010301d55070048802425101c1038400c0504032800100b000703512900d000c404c2200845154a5141004140c80903090070f0070050003110014145aa5080c02402c501200200f41e8401c901000907100d54881c184000c856001484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 235689010 1250 235687760 235687811
    0xd06050a12020f0102150c07032a021002030c030403080d050108070e0a050414161802090f09060a03020a15120b01050d0b010504120602040503060603010e0a172b0f 72
    0x20b0b00f8204a003440184d1500c0d00f00e18116407040d842c4400c000040b818078001c0c1c62820300c00d4840c200582130f05120902006516091400c0d003591050100015140c0a44103104040c00f40c01904c3c9400c81a0b00c0d940d00b0740c2d22a0300305032a4410006a644103080c002d00c6410b004020790000741078518240009010300c5c00000e04910021030703c0b4004101030041c6144090240e55413141111104541d10000d5480c001c10741c403482000c00701090f43c00758489154001c65046907c002d04d2101401000801c100400c2c601600c2103400c2034a0300c601100603110400000090101240203400c194410500100030241c05403c640c4801d080000c3d0001070b98225059981d00c11440e0000301d400030400e00101d0b054007030340d44441030b0652980f4010703007842081d60040003590415000d0b542e80781e03681002e141c242d907008146140c0503400b280c07110340842e01020311941513103d0f42c05034501c0c20b0740b8035200c50b01ca0130618848904600e084690304c128108030b407103030742c4c0d0055256100340702800c1045080160011803c94 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 235690260 1250 235689010 235689019
    0xb0a030905030904060e1015020c040e10090309180207170307020c03010c030b12030309071502070b0703030e060f15010c05010207020a060309120c1e02041b03020d06050a1202 77
    0x500c000c1040038800e60700c2411014104000c5d5541d03d0411008502c01607403006080850044041091070001883c0b440c02603154004219401c5500c3c240001040340b02100d00160107449070f0492841c0d018007441860f04d00075074640000c00c0c1040c0042040030501035007101950300c10042c0130009882c804a859201e440704022680366590003105030300b8090700030841c6500d5464440304802c080d40690101c0d649010a60300541130840018403141e40c2d100907030320500e00c1c2d4000502001003440f61581d200030b455852040d600300320740e0781640050030781042c0c00807000701e41c07039150903c410a01042030542c0280e222065400750f0911500342d80e004006000079504000d064071204040c40025012034004540c003070321099090344d9400e00180141280e650803150742e000038421164151042a005c0d4889802880d45018414410740700035500705110002c036002520303101c1c2e4003447c80f90a80503083c50b5042d510b000d0381c0c1d66042c40341c4108503895600002d01c00c443e1180305002701001805465100c0d58181ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 235691510 1250 235690260 235690271
    0xe150915010c0c09060807050d050312070c05070b0d14131203270b06030604030509040b120604030e0a090212010509070309051603020108071b0f081309240b0a03 71
    0x4841100310b0781d4003c0c000301002c150001e80d07451030350b000b507080728441030a0750f0045444408000c25102d410501404541c0140080004078007240061a040092404c6c0141c500a42e0b40c0d442d400e004c4258010a1a1440440d2a9402c0c510307a0286411140c2c1d0070410303100a217044140e601c1d400c500c144000d003c03038000c80001e000c1c0b10300030307407081c0310910722510310701030190341c083d0044010a40c1c3c0c00c00b19210032601021031514100010170364042d1f603141d220ba50404d0103130b0040c01300404403180c405901071b0203040c4008500703201b4070540d80964000d0b41d0304824002417505100740c4120710381c0300c1c0403198410400003040c100702600e21815114200d481025980750090120b000c1c0281e4880600b0350f014103500c09404120000112003140e100380ca41c1d28465451030b401b03450400510030030803030100105e0340749000a100812001e408520032002e043c00c0c2420002110040318280e0428415035666040c408004401101c51906054180220782011410009003880d28080c41840c0400c2c03603101c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 235692760 1250 235691510 235691551
    0x1807030f0f060302060a0f02100207050a112202030c09060a0203030604140601091a04050402040e011409010e07050702030f1902120703110d08120c0d0e0d050406050a0c1703010e1509 80
    0x89c8000d00000552031015500c4203803d003491030720fa0011180c200c1e841421100e81d071406080c000313003079031104040e251908408041c12480310702940c00240045c02c5940308015034400c940e51030703014200441c0e40390300554480c0743c1007007404110761448003190403243c00c01c000c014a03130303900100060540f00d104000724090140c800c0422014040c0d9000030394032030b0000c41d0206161040f036140c90304881882d03810501e110101001c0c402c864000303008806110138068002081c19002d040202000b42c0702504881c5204d4062018a041000d6215100d484400c1d0064150a600d014180c0142c891454006030002a25680d55551207808620489001d070300b0320040202403180003419101e402100340c4800086180401d031648555000f4a01201894a0020401d083d1113001900110000e60750302d90514150515905444c10707003001e00c4000410425201e210001011200e0b410014200101e030755403294181921458a004001c110450781e503440720805640382c2e02c0c039035900d0304030f4101c000405240010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 235694010 1250 235692760 235692763
    0x50903090609010e0a0b190309080724110d0605030c0a14030a05010c080610030902030a1e022101051e040b0c0705030a0e01090b090102060f061807030f0f060302060a0f02 75
    0x40e14010b6100213070280c0001c4c141c5600008001f002c01c00032401c81060002c1e0380503001c5484c07884016100e00d8040c4244400240e01c0078841d406581e50036900d81011121440a000f81d40e11508032603402003021a180d0523400700b5026690107041c00310302900c3c1006070000411814217991140d0307404192206041c442c40d403018405080d0303041d040002802034043c0120090410002a100c650144048040d1410054401d200c1c81d002c4582c020050f014414150302c48124414810020040f030151010b4444d00580d11856102d62a500d404a0801c0b031041002138142100c0004142c0e6040c89842d885802566000b402c51907482903000312074403910344031100e0040b154064a1001050791200103509500070360403c04d201c94031745090744c600f0320796601ca000125040c01410b04050160b4400000700c1c5c1e000c00458404d50348003402804c03d00140300605120110388000340d4607036010a90310107035402c24030400d0280240f03400030850280701d294510350100d00d25101d0340c0203240401501080c5812007030710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 235695260 1250 235694010 235694027
    0x18050604060e07020d02060115170a020d02070b0f01050f10050c120315150a1d1311130504050705040306020a030e06070e040e0c0303040b1303060213030b06030105090309060901 78
    0x5110301d05104603d01540041d54881c4e81140ca00c0c0944120000041c0142034a200800c02c800d16568000c50408442132102d41e000001e0282a0460340074003e10400b80f5840c03002d08885070069411708480d00305000c01c07188040c01a04982e004145003c1202c3e2903403229641c40010041c0d81c605035076a504940d1915080c20008440100e071300500206100400540380c0112070038440807180c90011244c0c8201e981c840d0b1140a03441804070b040300400c80306c08171a17115400f24602c0c02501d01d8051014202c074400440f10340b800c6020300d442d00806d0310320f0600d038240042c0300a090251000c200f84e00701214003600c24003480c400103012980028400400902c2174201ca144202c1980031114107080a01c8058800c09183c0da000c0e000d540b51100d00349020710001846540043c000e80a58601800d0810911056005064030780c41c0106000340040002c8291000300300d40a081708401032042c1c294a4044000e00303000e03200764420b84c1400207101c40c20310040100c80c48503030202c5000e940c40052100584d150b11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 235696510 1250 235695260 235695269
    0x201020a0803070c08120106020f0a030210090c05090109141819030e1201020a12090b010b130f141008041716020406121a01030f03050706140405070302030709061805060406 76
    0x10710104007030080f004901b518074141d503031607000e03901e41004c010f1815545600000d0f002e40142c0c0700000c3c3d079074a01c1a9a01c00164540940c0c01c0c0081c407034449000c07610208080c2d100825460741c540704101866844062103030000d00104042035510001c0210907643c0c0c6081da0458614614042001c040501030403a44030104005406a42040d040035a414001d410a0070000040303281d40208a581054a1040700e03000c030340c04801c80d01d00c0d034284589054590002700c502c1502d41110800881e000c290b030382c4017070010070320940030002c03034084002070044500052440342c00b032000d648103100020704110b0385154884081c6440a8841d03600407240d01401d00350301c502039001440c01a0200e6901d00c03a0800c0711086004504505003070071511003a02d100c2100344009011a02d48003030342c02c0007070f118500a04070180501c502242d10559030605002884041d1402c0b00d00780c1c4008020001c604051044600420b5124010060329103403a18070014220390b044204c001980d108000740246d55207620080242 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 235697760 1250 235696510 235696523
    0xc08120c0d15050405070908030708090102010b09131b03050c010c05010b060a08041a04030503040b070e120a030311041211040906021c0f0b0d0f0c0305160303090e040201020a0803070c 81
    0x71035a0900702a40b08410702070640504d040c10b000400684c0640000d02c125560000158540b03841ca0b240c400e1107800800c00f8038115501c1e031034400d65079911045085d004504448520340001c46624003280403040ba81420300e401881020100081840030900030300e072620030b0034080c54600092801ca401024100400c590141010541d031003001d42c49840940300d01d00c140801803154042140e402d0b24502d0842d0000e0000d401000010b00240259601c10340026940c18840c2100d02c4190002c1c40c84510320042442c1035104e2000c810034980d00d13015040340c2d068000005440c00d0f0410700f100c82c07040c01044019000310001d0f203185101d51106e5026950064000b402151104541d2128140c1000c040b511502b515060000130301d101e500300c1c07280307440a0000618011100e407031903a42042c1006d052109458500065000002054060080911030b100a0716090111819481d01504d401d185822004004501e5010480141d1700000c0364408903400201706900c9990700340048803512007010008088 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 235699010 1250 235697760 235697771
    0xf10030b07050a0224010303140d09121205270f0d030b0a090203091009060e1005180a0b07110f011806050106030b1503070e0d0c03050d0c08120c0d 65
    0x10705600401030000342001e5800d50303130003c41904501003500020300000001c140c41d0801000002c2c0201c50307401d0b4034018aa403190a0a441c0100d040880d1090442a116a89402c0d076903600558400b40c0c208002101c80410000c1d821b101440c482851400008814a10300341c07222600002010410306c3c0b40440c00804540c03a490f4185002809071071030f05000c500501c607009020410381024000d9030f1044c10b00c82e0007040a601013007840405844d0b440c50650304103568503e003420450301440f02550190521601044a0411224207000340c403000c1c1c00890b481c0c1160740311b40300050004100b40e4000c1001c8c43c0c909801c8080c0a03a85050070445c561950746586450908094281410260f40000c0c0c0940310400c180e0780d17a914181c0c1a9110140740756845402c11460301607091001c80a10b80010305440d18030f02c160181c402044070303c80c02d50001c0d035804000e400c0400810100300000c1c8080c2c6581d18209424807506d584968590082d4040802e90a82030000518001d140c4411b0701c3d8603800301c0605005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 235700260 1250 235699010 235699021
    0x9090a0b030d11030d0903140a0e1203043c080a0c30061b0c02090108010209100e010e0d06050702010e0d0e040e030405040603121b0b0f10030b 63
    0x201504040d66000740100002c450000340151200382c03407040310002a610b00040c1c91910300c01440201e104070140241e060040d505074450201411280302036451b01050400c402c3c003040604003000541600c00d0b03000b0072003407000994118500c01c0070b20500e070300d170b40845084c51900d5070644041c0413a08070303030342c0e0144000805200c0000e06944035801403030b0040e1401d0b1903580c6040c0c1c1585c5481c0500b0303404842c0c82c841e1141d03050b40e04140c00b000d00820300060038484540c9401d08005d100000071000a040000030415803a050081c18014079100c4001c501d0a0f12582c08187c0c041d0b00b5217156000e101c031740809001c09900401400f14100c1c00144040004082e51400c44020401a504140150300e0403131010810600007480c82c1407400e00b42c075144200000d041c00c200c081c040c2103108411500046c080020b603503c440c05840095031082c0b180d80f20303c00c0301850042036140e00240c1c12184103e20100c000c0415461211703141c01422006082480c1c0d680c817480b030403105000398030003400710050301c08116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 235701510 1250 235700260 235700281
    0x62916050115032f011b080406021b03030c0c090c04090203011503140c04090c140a03091506120b040203031218251511030703020c010e22050c0909 65
    0x3503902c600c1d00300c24010008204041c482a04005004110f01e190110300381300d60050000c02e851800c02e414902c0186007554510b00a40c005502c0403025034403242c00c508054040043d00740c11680203170000c6060030f510740c202e04c1d5a03401d4101c289015a51030310100c0d0803a138409084402910307031404255a203507518a174043e5a0f13a41c0360198000030f40740241407046200e000310700b02d0242040400c041e08050401c001c0c00018489010b010092214210a40c900004118046d08140701e0a440c00208a0140d0130414540030300c01d0035006c586494110140700481c0c40c0034411041582201c2c0c0c0030070030781e43c7d440480d02d50300c56080000000403411040005850100c2c0200c004881910290352a802000e21246100c008800304581031446170030040c00303105860079002c42c0b6900310b8a071000305800c1d010300e902d09641c0041c5050740145c000038103503011075030400c10840081c401542d038030f001501c0000703825100354000003649038401d0703c0d940440d81c1103088406445203410018101401e905000354401c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 235702760 1250 235701510 235701551
    0x105040f0212010509060109181a0109110c0d030f02041815091802060703090302060a050c150103150e031b06010905071e0807120509030d0629160501 66
    0x100c2c49505012091440c51006000b41c6000e05c0088001708850b0b42801d03400000303071842c60f4a082418040074011004640301030020140d007030503900c0c0b213005541800d17500740a4502d41103100010710400c11118242c08000960b240c6245124500001c140e844810041c01a1180c0e42c404000d21031107401c05c51a55040398800044000ca031115812665503a1400c0e0003910700988604150090803880030000d42041c800500f4078500c40d142c01c1c0c6680d5101d5000503440c1c3c02c068007000000300e020400300700703949040000750f2111415150705c45e01d0350315607540e124a00b00407080090740c041c2c0b40e183c4101001820010780d002890403090900d4003003034818580707940303600910815501600300004078200502400e0050b1a400100000c0004811081800d5680000281ca1002007103504184ea9032001210b00c2401e008146100103581d98013902c9010300300b902d1054101030f00c0021002e01050740c5003000c0d540c6420400d0030750702550310769010b100406940c0e62034620280040d424940c10442d4121491500b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 235704010 1250 235702760 235702763
    0x609070509070e21030d0b0909030a03020903030c0a05060702060a0b060406050d110a110616140a050408030d050a1b09062010090308011208040e0c09040f0b0a06020303090309040203040804080105040f 88
    0x204905054002008070b030707048c2510030350259082080640100c40c8203030003c21000700c0140407a4642000c11040c030f443c0200d03090080e14075420074070a101e8010350602c21141c10a00d00c02050109420460000c1d55078032072441103906024000400401402142c0c1080840310b040854543d1500d9141038007410f0b8036a0050446414000d02c0c1c001103d074550380c881c0c6464141c0d07640e40c0c80741204c001011403e05500c148945402e20500f840b0000b1400d900304024202007102d2000405c6500308030042d103080e02c4200c0c0240c985804445040510700342d2045840c0101d038101e1901c5003818090384034158500c0004500c0d0b915500690079848460842c540204183d203200342c0d584031841e0fa95090001c0c02d061040350041c03410a080200304811031891102c26000040d00b443c043c07408a903100000c0c110384d1f51450200159440300150381d410310382030404100400e041c1c0090f5107140b030107030120346c5c60703104051500340f1450380400494240010081524060701c0c4a00c020031041c00c090500200080c2810b40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 235705260 1250 235704010 235704037
    0x10312021e06130305040807030c030c09050f0a02030709120b04050d0521040c09050906010603050a0e070512070503030c150a0207020904030c030e0409060e0609070509070e2103 78
    0x2030020781d00001c4485281004050015194a4546003030f4038103d001c4280c01501006010301002c6010390060100100641c841c0078a0b40702c40e4950318102104084513840814510b1405c020050000c1c60614034580c401d881d40401692030790381d442c00b59130705591074211401d041c11088141e402c0006801e540c03030107580900c04807403180c8030302241141c1910036481d00c4449044202c101e14041414a21016001486000110b1010b925082c00104440c0704444c20b148641c49071004100d110740510949400480c031180900c400214405001c3d5a480b5a1095900a003032018030612840300500104c00507060040942e603495924020f407a80e01c40e449142c0107090440000840c181a406208440103154050015909650360b524141c4040381c000700705906114078000b084029540342c0c0f00c6e0b89001c0b84500c5002864602c1801103910300307032000b450300b82294007004040c4200e40c0d407850340d503910200f10b00d82000060101004130718108280d002c0d10000401e21180c03408940030200c05403400861500c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 235706510 1250 235705260 235705273
    0x408130b2101030302030a030e03040509091014010f1a0909190509150f09101d0c0a140d0516060c110d080a110106080304090501061101021e1605010501031202 70
    0x500724158100a00c00100940d0013004000d034281c2c002c0d004008144120003e0341e0a00e076440d0046110341c403007101d080f00e10303412105400034000702070f00c01c4003280710250500020660400d10221104003c601484000c482d5103100c64200030300e040202e45041c10302800404442c1008002da1801190030800050000c4c1400f000070b60441c0000398601790402850001c50a0340c80e0f040b845143c018000d0014042401b8400a890f407100d0280108508000018844414142401c2c00141440c0006002600c600c0c00044100542c0494007c60518598100c56060800030103260841c606410400181150b00c092540018029006095403860a00500b944140200c4483c100005011041c20061201c14140042000d06110301c10440090310310380e0002845030b48540c0807030f2a540099000d03240d016280d40042c8041588960b40310b85000e61300d4020b40c01c004a09110b000d00c0701c010000a07460314004a0084c146038890303d000310f040d9401000800ca1541c690801001c1c42d040001d84402511801d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 235707760 1250 235706510 235706557
    0x170709181203050405030703050307031503080d0c030b0607080c030417160510230d091103010e03040b0405060315090f04110d03020601050f1908010204050a0e011401080408130b 78
    0x83c043c0511542e032103000785103003410a42c1c050b210780d00080c00150030103986150030200711440300480d0004e54082c05a25444444510713003c0180c8948007420070825060850060356a00c4000039560910b40c4002640c1e1180f1500d00d00c6861030299622888000010914004003540c003c140f80c2e01c80c481b0042030021068441040c07007150016440c14100103480062001d00c0040c49002c101c000403070580e2110306d040c03260240f02054811003502581d5890100d60713450740341e107001d100b035001c008013503406036007080c0c0f4040500850303005501ca402d00410000001840400081c4000124100c2c000c082810f02d00740b0042c1c040c080c400c1140c08860840c84403407911050315190320040034095141d401030076680e0901701401020310196250a80000d070124804807203800c280c84100c00381500344001610317a4641800c0150640301988403200e00313403c43d00103201134080c036070480c04003d0084c00c240d6903544640c90301e040305210316034080001c80b243c0c10001c50380010074001082000d1581800e420891000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 235709010 1250 235707760 235707767
    0x6120605010c0b0601031805010b18060102071e03060608030306030c1504120f080a1701060801061e2c0a080102030c16150501060f02060a060e011707091812 69
    0x55008041c00710300210b05000c000b071030a00b00654429410302d000702d40003081d0301c900040080e02500c01c884a0751a0242c042003800c5c0b41484004082001852448a04003000080e403903601d640611468000103414640224595161460080da4001c03c20402a40d680d00c1e00c1d5240d030010341d4258480d0140c840480c0045c580b102c60142c41c03010b91950545007601c0c00900603840c00c110030301103681d86040403030740011038980005040103e00c29101c4910030320082c44c04031105a4140c0014040c04018070040c4080380c0c0c8580700c0c8942030148160403208641041d41510707420440d03298011440041032aa08065070110000501040300f03580000120b03840303074501c03400d03408111500010120280000070050000c941c40319017940c0506c0c528a100c004411400041e604240c022902251034208480e2404c1e504100c2140e005641c0c0d40b081051a0a007000d90304150320600c1003c0c19040301220400a1742c0d414401040207100700c0e0f02c01c124032520110080c0c0d11845501040d00d03003910341d80300d0f070391107900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 235710260 1250 235709010 235709021
    0x2b0503193b0406050630040812090a020d0311011808030c070c0b0304050105060918151f1211030f0604030c080903031c0c170a0207061803090612 64
    0x1091403680c00e0115096030300c0362940d4940d00003a81c45619200f0020b411344441c2d00600c40040c0d070304892400440590004269451001d610751000c4d40f0500401010501c0001903a00901c1c074090001d9003501c41189541c0342800b2510065809080740407207004058000c019080c111440100078000d03c641e0120400a61481c8607024101010400000307009158150080004a114034040020f00340c407259907000c2c980040f501250719039568000e20540345080310029a00080d000b807000c8000440c949030a4807040da88041444443c401000300f1000c7c41a031030401010a10371100c00f1740c582c1d840920741261210000c00340d410020b402103c203240d040110f1001d02d5502d0744401001c607a10f403507a00f1500707030034041c400380c1d4011000d10505000d80c0d01800189101000f1605050204203242d100004907882c0712214070030300101c940a4100c0d5154481d580d6030020a0260050701ea440d18207119029041803100c000c072120700040c9010070150400302c3c2100b030707654030782e10b1010250811407818100c89 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 235711510 1250 235710260 235710317
    0xf0507050a0b070507080f0901030f02040b160302010b030d1d0604061d030102131d062b050703060c09060206010e0c0711030f01052e03022b050319 65
    0x700484000e201240c85801d08a4001c501850120300d0805140c0310800c107a005400c100041001c0000d80c041f0640e414000c0104958501d0000c6242074500f159242982c40f4040c10011803072100f08400003810f000798081c491800001e03040d21050011414001c00000e4402000f40f00e0f1201030315403c1250511100f41c0d82683c000b0345420707151400510607400d03080f5003044000e03071540d000c0001cbc00c84203a42552040041c2401c0303081180160448210100c3c50400078403103800b40025408081145400303500001603159000d00b43d490540392818513a090800581000d0055403c02504005040c2d004122104030740540d402c0c1c50f1203036241d22510800c11401d07a030743d1034414024000000407031441c1070141030203c0700070104c03402d44035290a55400d40b8000c9035840d042071070041c003001c00b854070700215210401015408207400c5003581e000078801c88842e841500a01071001d034000c0006e00c1d05907001402c13604101244c1e11080f58400884da03800066080d072000401101c0c02d009210030442981d001c50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 235712760 1250 235711510 235711513
    0x609181103132102071e080703080415030b0609190b07050c01020d17062112090112090507120c0b180f1807050a0318050102040603050105010f0504030213090203060a05070f050705 79
    0xa10f0600d0784111b00501103044090608074100010b44800200b001c24001c51080c440b46442d00d1a00d40d0b50705100c100080410700385410190031802556485003100c01d104811a0311034440700c903030f5858240c40c40841e00300d024100400910141801030005040580c5182607003124041c80c4c0310300b4200c81c500c03030700303940c0894000342c40c0e020800300d00c0c008a20101d19208020706010031652402640e2506032007500e01c05684c0400074403400256407000c1c4c41d0200108002080c0440110b50352503035680c10b401c0c400c030b1a26035050406401004100310025000302a040c2e02c55852742e003e10745164000d8400c5658034030503030003440500d1080c1454608250841040340d41c61140b541c0303a2509442036417000c1c068500b095a601e01500c00d0001d440c0014025034024400117031118140300d40902154410382103107041c002c010a800d02004e41c010219001e5030781c15100101d61461240600b000382c481d8150003985406450200700044c0c00e694006072180080b030350342030700d201d40502d01030307405118100000d4000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 235714010 1250 235712760 235712773
    0xf17060105240904090803040609020108060301020708040e0403030e0a080301180905030d0c110a050a0506091c12060f0315060611100203061f050c15010609181103132102 75
    0x2020703550b4019091402026001185d61401ca507140d00c641e0344100c41c21500141e45541c1e840a659121000507805402503008500c2d0521030744400d007090042e44984202542150f002400b098801c0d000841c1c02107505040b90010141842c00f280d15400034041d4484480c03084450301c4118215009440045401601840c589055061000068400c2c0d00c056001e01032000501d8607110403c0021003036140c01200900021529450600d0501401600c1400c0583c03004840119411140b406811030003a0750419a40380120000444081c107107a5001d11803602041c8070000621444000b0000c581c49901000c0006607103400069546245549141c511580032140103143e00d626903009503081a0b0091851080780c7c0c1145000d107100040c150f690f800030b003020920300c9611804105507200e8507598908145103605008004040760098403440036080901d1000f07424640d459809803000c868107142c7c842d6079142030b10100c3c842a400b0740e022100240b03020146d0441026040002c640c04d000e941c0507280c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 235715260 1250 235714010 235714069
    0x31b07021518130207030206060a030c050111011e1a1504090f020c07031211060903030f0a02091915030218060a05160c06030b010c0f1b0f17060105 65
    0x3116002400400102502c04440c918550341c0e5515068030200d04031009039a840d05480c000741000000751125000e980c08820074000143c42107100c000341c07182860714a03d001c0001c0c11590140400c800003030040112640410920303480f580010031880005010b203501c110305001401550b41101c8034620900d50301744024042c0b0580c03130f00110b050b1036260201505008000317082c2410401c8561040b1845030700009076100b0583c21600059040c88600041c180070320704207912580720310004101c1140e0014145c002040245242e0682d1403105029080c02c141d00944004451444c4040c01401e4144040720105048144680215030b00c044490303044142d501061014018a90004050f02c0144101800307034000b00801880090030312400b440d16444540d02d459009001c6841030602c6c40d041082c181501d1000c180100c000101c1958010700f0442348030000049501e1001030390700400740984100e48006482c1d914510114054110601074031441c7e41d03034404012600d40800d030000c401d01c0c2c01c182041c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 235716510 1250 235715260 235715299
    0xe130c0b030a0905010e0c0901120b0a09021f090503060907060c140a020622050a06020c0d020111030c01050a0b0102032104110402031f090c020309040b13060803031b0702 75
    0x182c000442d80320105401c4841c0c0d40b8035082d01c000c0341c0c6118043d8080c0301d810305903141c450300340390042c81c440c02403100e0180340d070711490b8514800418060801341c460b8010411519101d6000084507064803046a100011101c02040d000152044e2031107032103108041104188081040da0403a5041e490709810b0700010b5030f960304080c038040c1c02500da07409a801000013588448004120702262580e818280c10f0030b007540300704a0949604020300030002d248061212039000902c1000c0341900b1154104441c141e840103c84002015542540900021a1354140c0f4030341500b25602481903c41c09001c280c007280f00482e80c03800380420340c2001c03030700f00904d0142085400e183d02d50082d00a1056000140d24000881c007a6032055030508266400240383e18402c004000c520300290810010038054010000b100075035070301440310400d00c22942c44407000c1880c2d41c1d03920340c0314410314004420701c08680e07100440b64a039042290220071120f0085103405110000c1e8040303c0300a540200301c012070700701807030300700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 235717760 1250 235716510 235716517
    0x504111c2405010b030412020703150e01090203031615050f01170c03030403210804081e04030501151502030913020d0f09080d0f0603020f01080705120f010e130c0b 72
    0x4a0409038000a291000c001e07400b900f4060301c2d01d400440d0f607a06017460b164032440f0f582601c500445d0043c800910004902c07200c0006811001000455166004ca00c5103005040000c002540741c8400910b14400d1910001540002030013000007440100700003882c1380640d80212007184a0f042440c00501c41c6409002c0b50f030203000c03054011100c11282010100b86941e10a40090750180c8007001024003006e15801540360380d80700c40c03403ca406820706540d056000e00402d282d080d1f0410065080d034101949000a54000f540c0083c020300c103180111914040c250668002d0070510f007061514070340401e000004881c100c3c00064814040281050701400080d0015404107035115250b606244c80490240581c4100038003400d44a591040c0c21403180c0100e902c4042c940c0b48140c00c1c02c40c10409a9203200c95110b0201007030070100380d07642c0d03800c20403202485114102c2c10b0b029a44028030424210000041d4161442155105a15107401401c101020f40c100401002082801000d00407441c41c080135 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 235719010 1250 235717760 235717793
    0x2030d0c1211032703071407030212030a02060105010e0d08040909060c020718050402010c0b0f0114030c0303040513020717041d09100b1906080a051303080a02070f080d0504111c 78
    0x141e03070a080040d40c7e807002898514450580d2a40030050034000d520345490040004101031000b54030b0b01d81c00c201d0294030f41d84144505414072000740160086038070358501c08804581e0014841d070303480d40c444d81004000d10080c4000d83d24540b601150003060380c0001844400d0b2071400411110344008044681c014240061040741042a85042e1500080007404528003440b0003010240c502d40c100403040001c0d02c400c41526100b0f90080040e49030a44000c030403201a071b002a2441d0001c132035a000010003030700c500ca400404032410040f03111500f143e0b6802620966180f8501c1d9030511040d085001030051059407000416005100c070315130742500c5507102c505040710241203030798801e41122800100c80c0c010b038480c40c00300d0180010880e000c2814401d2a0340642a18800c43e407040d06620024840075004240070003060340010040c05008086141c1130b6030550101e840c076a55490120300d2405810256011200d094440c640c4070304518001d917482292403244100300f0481703030040d103680d800142441307103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 235720260 1250 235719010 235719013
    0x6051003080a08090606010305061c08040b040b04080c0f0603130c0e0a0b1807020a08030a0e010606170709230414010f060f052802030d0c12110327 65
    0x1400400580c0c01070142040340342079190302c6001e1400419070b42c20400011300c07081c101880c10301080015994110340c1e00800098600e0310038900201d1510300d000d4032a540000045070700c01b1070300040c41c624001c0148107492081c001c0d1100c204189042c4611034141e10390040e801702007400003600e42004a111130103210f015828140805913101c43c180ca40842c01d40c0c0584601e03131605114001130920400846200d81039802c084050301d0300540007910746080345070003807030103000001003000581940c024420344100d2000800c4070701e548450141500c2d5001c54035081008190f03000800041c02600d210003141c4003495490408250840d642a4200c03003030640700c0d4842d0740c3d18038815980060700c1cae44070b01821400c0803440d40320342040009041c000d044212501004000c001c2030361002d1000744aa8083c105904611981800a80d41a4218001c00003401c1d450b51030501c1100c581a44071000129450444004000b90010700000880d0752104035036201c290002c50134101c100003089541500040303c1c070300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 235721510 1250 235720260 235720291
    0x8030a021c0c20030d08060d0201030c11030301060306030b010b16030e0d200a0b031311010e060705010b010306052422031a13050c0d170a020619060e01030605 70
    0x10f580303003049400040d00300030160349041e0300f4140d4141003000003481c54090074507808034505a80011020680f0940003410103032984c1416003c00d0044180010520303d031001e81ea181e60b1150300c002c004219620064451b0145240001100d241000403104440c000c0c000348201c9c851286c03429504050100e41c13003604501400200d50220f0b2110300700f03564104e01c03000340001d42d0802204000083c074558204202d180c0042050101500800e502c10010743d900651809503400e5044c0103803515590074180c030390005000940e1200b00007042d0300201c4000c07000d890400055489009200c0300b080b0711198110081502c00c018221030b404400a000d91900d00c09100d0080c544411203042007080b503034000c8402990f54440604a81c4045070714590002c602462a5043d06d0140c564a40e1102d40d83c0700715006c1e05400c140d503000e01c280502e41d400307d06280c0400c25074405542038001d550b100700320b4480c091241050902d01104e00c15018850407100100d001101c0d69082d0b4070340ca0020720010f02036201105000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 235722760 1250 235721510 235721513
    0x7050d110c030403030e030c09070c0b09030f071209060e030a080d0b150403050706030b0904060e0a050f0a050c090126100c0509011e08071d0319050708030a021c0c 72
    0xb0001000550300c40d075140010a410242410b1402c1c1c9040c1440c0c1c8115581d20411480c150300410a400068111001c45003503208c2c100c4640c1548a4000e600c015600005112010b004841e000e01c03071004410b540b610240c03a03440d481128294103600985916412028035100400c400001520035907520090008413043d48200068800b400310555003103449010600b00305000041c8a80f000416007030506201041c2d41c0c400190f050b04d00240010f040c150303607141240b001441004180706281e0301c1811280c1403e082e0b401d2907070300c00d00000d040343c4510451602c1005401e060840c0c90481d050205d2003000c000c1740150700c1d06d000151401d00103a500c541e4010341c007407024074000c5d100c0c444016141d19990305061000101f00300390010306400d00b51044510b07201c40582c00682241e00030080e00e4410b65018004003c040c0b101c0d0340820440d03251180304440c5903030100802d401ca5404d0f1145003200d00c0326964180c1d1544a00031070484101581022801c0f40901da502d18494201902c10720b0480c5421406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 235724010 1250 235722760 235722763
    0x190215151503011205060c09030309060d180804050a050316091d010c18060323070302040e01080f06340908010e0607030b0402090d0f0c03050a050102030610030507050d110c 76
    0x264130a0558082c140a0602840000c0c0103203500007502248061234a824500401da6a05c94401c0050080000040507454100a40d001940161200048216403503e5080800b00e80d0414040c07184504810040003880d4540000d0804041000305446160945019944da00410b50b071244889400c1701448820030382c410a10038414180d10a0300d450301152114180d4005006c0142c00c400145440c0034000707028008003209012030814800c40c1d5441d5030795a45005c8000c2d018652100c91280001000407420103808964410101c80440c202e40503580c0c8c0c0703c0d0700221041c000146002c203150310f02d1580c0003d0880c208401e5030007178900f4400c088a540d20701e6282101c2d01184070308201d4006400340503581e0742c980103803a20150210750550034521140b000444481101c00005c0c50008054205410480003050180049d40c014064406252090030141d010350f0003113843c10701c668070b0420142251030103485164094401070341c07803900b4000243d2680c001044034059030403002805208401d00e4540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 235725260 1250 235724010 235724017
    0x2010207120b070f081e06040608030a110d140403080304170304050a110a0f0501030203092104180c0e06030601090f1d0a06120f08040e0403051902151515 68
    0x41405070400b030b80303440100200504454052403041000343c00a01c0140c95511604001417a200440b0090f0364950704009401031100303034000c1003980804140141603503000b030844408100345505458184050190032580288201555004200280300c1400402d00341400346900503c268842d048410080311a00c10903003040340c0031140c680c1304001071010409402c4d03051040768410b560703902c1c3d01400c240d1140d0020703405d03000300e904059000c00000c0440004000e000c80c00001200e03801c1140100101c4d4188589c41130048298255480300100348031601885212802c0105540e804203841907042004450341c4007034204ca0400c6074150000c100c0040c00302c0400000c0c000301d84000040090801e2480700003100501035038556242ca48100421001e2042c03010501d903006207100042501d80c94074403c280102c0c2c001d85850300312070040208064002c4020300ba4000400c001000d609030220049030f8500c10034042076501c40505000c1201d40c008a04a404600001409154038080c0d07540222640c5c1c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 235726510 1250 235725260 235725263
    0xe0a020906030411120a030f0f0e0904052505031507120e010203011809050a0311031e0406110a050a15060905040b0a0b0d0507051302040b16030f020c090a05040201020712 75
    0xd0450070002c02c2ca03c2d008017240c3e9a002c5013005031050b0103054401501070b86900c2403104c01c1c00380c10760128103a18469942006407880c010800104c60070729040841e616207400003440300406c0f142d49007113001d00c01d00e4082011107400030001c19400101c0000300c1c80a00002d08540c0074030078000e0500004039018001c1d40110000e0000044e1030b503140180607220040350149080c190782c40c00310400c01184000c95000300300c0313406081100c00c40181d4200f85203180301e80e40700d58650303070796520543d90101c01081c01042140c0c990fa9800258485003243d00c1c0d00c607040c845004180d50300c91640c000009032451525514084e05140001d002c0c0d82e5038080744141d410072241120708501d0a0100907800b1140c1c400d501003800c05480c023200c880c0040d07840942d120114060940702d80280c000c40c054000c05901118068400c241c100ba0301d58070301c2820307280c50106040048002c68050000f8040803440001e0300c0070390210041c48052283c403102002e0b4014a00684268114001c024001c034a081c4010204051303039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 235727760 1250 235726510 235726523
    0x3030c1b05010917120c0f13090e06011a030f18010608011515020304060c02030102070c08210306010909020d090206071a0a020702150306030703170d0e07030c0e0a0209060304 77
    0xa0f0711034500039050000c3e900e80303852660030900c40720030410501ca0720650b11000101e50103588101105d4124002c1c0540c00c0314426a000f40074012400c21f055030400c2800c003e40d0b80803100e083e41c0340c07100e80d007103070400d03598411a043e070074400031b10030f00032003c249a001400d08221118a02c81e41a0482c25115940c1003c481030f9101d407140c00040309252240001403107030380c0b603502c100c4218200c000c0d101c5c442c40c41a0810009292916419586d0a43c100d42c100c4e41e0110380c184c01c441c0c0d030f002c4107902d65000600c09005a44101000a0140700d2001168400e00c01607407021030780c90404002200075045421400c850969070801c00d401600e900d00101100307402034500d13100484e2400268031401c0001800fa014050040c40b418005840745c030201c40403140b820b044a074603942c81d0804a4900500c03640040c0081360340b801400758804e0503000a02000c108181e060005030001c540b00b80c1d480c4c2035440000d042940d004002c01110220b81c82181e049130300b1010242c81d1041c0b040018a071070700b00741c038180e450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 235729010 1250 235727760 235727771
    0x13150b0d1407050111120307180e10060e190b0d0e0601120c0807030f0f110a03061b08060307060c031107090f0f09020a0308091309080315060f040303030c1b0501 71
    0x2031341c1c200030a482540f00810040c801c10b001100e00b002640009131102090186540c040c022642035010020041d080312481c0e01014548901c032140303c3c214501c1101c2c08140c00c050482c0541c1031200d11401c00b103d500780c80e49942072a0500d841c80d16480030400b40500d56503022114040b4030140101402000c4e2400c402100d01c00340e080c0070400104541c4182d050741c0c8007800c1000042c0b503541172200c0054100c01c0c0d040035140981044000141a048030785d81c81010b00300007200700481a03000c18400300740c084d2800100c216185064a507440706894640d80f66102d50810040da034820010498540d21030300c0c10240d1410400300d0540741030b203260805001035441e0201081824224450400b2401039a01c00b444081e8030ba030007140340320302c10b0300000e4001c1000050841883d1215000030096030a524005c1201c8c545070304182c2c89a030002c0e203000d0035644a2a1200c4003e00d042d50558181222103054985018035503502070340141506402201888060030000040c12024016095918020b0001091 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 235730260 1250 235729010 235729019
    0x5240a06080a0b030a1b17060105100306031202161a0331080705120301150e030705060418060b09010f050904140703090302121303020906180903040e13150b0d1407 72
    0x400b42144e13000900c1042d541d5a62694110000508e54111241900d0540e51029140001c601814070b503080a0450060112040405030303002445c0583d40e03024011606185444802c0840070300c091a11741504a40d00740007080c0581010391700000030070480544010311900d2081c289a0290040505035030308000400c10105105060021080070755210b45420726540c14040414a12003584840608210b00044492865141044040c0c06400000d1200e07440c1c550b11050b800084030702100c424585810407030005030102d403190030350b000000141c60760b11102d014104104d41d9038002c1400c1a90103620fa4560414070707000c0520701c0380100c20503a004594180b090801030b10380032040051680d0044100010503841d80081e40316011707680d04440591003904c1b46000030316801103000c9440741c1541d5820520801c1d40c8004010801c841c02c078602c200c4180d9a940d10811100802316000d08038542e2500e0300340382c0003050703405800c0000e002405296458030544440d410000400d10a043c0355200d03590502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 235731510 1250 235730260 235730303
    0x80109140f070f030b0403170a0c03151a0c0325020907181502010608061305060a0603020d02150c060709091d030a0806011e0305240a06080a0b030a 65
    0x14103040009100051500f6580310a11409100260188061030046010544105440da02211042c6a602c4050502c7d2030030600905e148e45261000c20715082c000035040c840c4500020865000002c9104e0780003003620a001c0560001840405a010420021038071426141440c201c1d10314060014010728100c3c414480311090190181052000d04070f580340074840700c1f1500d40191002c011224006075000385082c0c1c094802038104044c20300440c0d0812884407441c0503910a010b0040c411550302e0740381c88510004948450001070b4204c41001c0900015040020f6001d00c2c8540401c0210b280131750b0740b004541402d0080e038500000031510101002603e0b800e016202c000100c09031003401c003104100510b1f950b440384400b80000d2005110000320300780e00442d050030351056103a00c2442c0304501140700900820b0120f41b1000c855244c844c040c10b000140740d101546105014080c80b00941c1460310075122150003c2c54940319a4070390300300c1c002c0c54509000c04d80059103d0040001000e11005420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 235732760 1250 235731510 235731523
    0x150a06050609030a032a08210118020a1e08010503010606110c0f041b05040f0b07080d0917070b060418030219020310060602060702061f090f020408010914 68
    0x81c070a603020b0002c10314030740e0003103000d5148070380c1401c3c148000d0302908040386800c03952211895500f1000e0448505010000c001801604140603000070511400802444003610030300071002190741d031350b0401441522a500411000c80c450904148941c80d0030b51a8860700d24071040f400000300c100e00100000d0509010794009403482d03003400c0505c40da141140795603070f00a0104151180182c3e0b10500826110360740300a408282d902240b942c004d904c1344015101354041d00c1030f58540c00103080c00040010040c03098402450740101402d251407880c1d0400b82c098101000251021082080140e040c400d040000380015480b0f00860b211600d0040108821140f0101410850320a0440fa003030000c3d901107900e1a24001002110b0b69050780d5001291800c1c4014903d0603403070346041030114065070001034a610a03455a400c135102c035030701c0f420308902c0f0f0903444e6042c0d00c605500300402e00c42d1812640240504440c1c01c40010300301640c60355000d082d520f0250054071140e002c1c0441d1360400c075091040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 235734010 1250 235732760 235732769
    0x608060d0b15030d0e0d1e06051806070f0503190b03070603060302040e01050402010e060309010f021c0e07062a0c0308071b0e0103020103021c05070810050301050c0d05060a08150a06 80
    0x3001c9517820010100b058460030080080850f8850001c65904028044402520341e8103d07200b0845403034940e5500d85e940d20000480c6500c0e1080134006038159200d40d1101451010039a2402d0030340d1100404442c072403403100391034403000340c4a50101c003060318100b01c1030000701000e5070085980e5140d401808101c0d105424055603a9060508100160340c12a07442c00d040d2000340c800c0e503a0b0ba560780c0310f1030340181807507024413191900000f2041546d460f52100d0700c1e014040c1d0202001034902070b8020a541d0a80c500c120f1021958100030140c455041e642d0804001c52410b2210366400991b82d03680303d01141c0740d00102c1d1515400306007001401548a8240c884900c0004100400313820b01a0742400d4402c1403100904050b00000d058004a002041d5122669000388003030103107040c0141c0180c024042280c58441c0c0c0c040c030400014403032505024a60266601040b101e203400302000812018010003003505421912102c80028182020032581c441b090400310b9110950816030032031400d64050780d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 235735260 1250 235734010 235734017
    0x12100e010b0f120f07031b0e1e15210c0d031403041e0c08010f020703081b0c0a0305030708100b0a032a0203310608060d0b15030d 57
    0x1031881042e102c1c030b6810454602c00302c0c1c1c1861811442c0807210702d4107a41031030200c80ca0207141c03400030411840780101542601c0e030000e220300c0d40d612241c8a0341410b00c101c07580654400850030b010302907a2403080342da4010146900c04110349020401161080300c01c68070031039020f91884600070300c00d00180080c0380500400c4440c000d070300080d0f0b02c00030802d82c03a091030180c1c800c2c0000040350804c20000142c3d80716000d03c0c8401d1103d20068180205131082c1445400c01035400c100e1030a800c01024421900965410f480351b10540e218810484c007406444290300c00c05840410201100d2401000110180c500c00d50300d15a891070031a030000c0020070044d088404da440458028000c940020068070407404291a0000b26040110010704c102284250f8003c101d910189103030b00e100c0d0703000c0010030074000b840c40d86034408403400d00c0c160014048000c42d010100c12003201446490f10802550303411034001080043c4955154a48400d1481c040c6d4000056101c0d1114480c1da9040a100b81c6418288504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 235736510 1250 235735260 235735271
    0x1506081806070210050a020d0905010e070f051305101e08070816030303020a020705120a02040b06120615090616030206060d051f0f02030103050d1b02130f02070212100e01 75
    0xb14080d6945241e83c1040f0140350b111340c0010490001581510711440486c007041c400035a290400b01c1c0240141c4607012101e02841201041200500343d0580c21100301a08011044560218210082002600324010301140c4800000c624004e0680000e800710311a40741d061481c6031007030f40340c50308423140c2c00b9940c43d4100d03c0400740308040c61403041080740c2e0141000f50351510b2003842281083c085401841e031003c200075035400d61080020395014160710a55080040900d0082004440c0c02452503503a8682c051400090940c180f43e003240044c0c070030b0001c10904180351000040c1090304854205c01c054003200041e0790926604015840d04090117840001490003a074076174503241c2034412904182007190304640c40c03400d0000c0d48414000c400faa9421922540c480c9082030b00c540d400704201e0005184402075031f034424005208208070a03402410310840303d4030880850085c1c850040e001107403680c01c0c4105805031316414146005101040098540410f120361038030203d400c141c80c00d0005a1404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 235737760 1250 235736510 235736521
    0x9030803250309050a0b090f06090102030121020a03020f010c151b0c1109070c080316180b090d0f05010504030906020127022112040609060e01020a0201030e011506081806 75
    0x42001c3e000c4582181c5060a180c1c0c581f4240740c508a81071184039030b01d1040b0003c000c2201010350155040c1c6030129000c5d442001840d070860f40d48404000065413001c03151004000529100300820400041030400410680142d1500b10352980c030059202c0699846103035a644150314144040c00c0b060316400c5c81d1a11909a448941000707400078a03990040c8556008600d11074041ca0700e0042240d80008980e40e03900d0710200d4244000000005500405c03000407410056641c00085081030319070882c103290074407101c2c00c200110441d20007001e03141007040014040100c0c40078042ca52141e80a515001841c5103440d00c000d003100d980118042d480010b803503070720007000ca0b00700c01c20310a42d0b011102c400001315042e080e50700488620103408283d118482c1c04041d4030203108040e00490b8940e482c0c1880440d170381c250503541c2c911a003c0050060308007251050056009174000c196180c01040006a901c40c00c0c0b011030002c40854100c080800c01030f5081140c1c00301c0d40c84c008040006100041c01290030306 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 235739010 1250 235737760 235737763
    0x90f0d03120c12020a02010b030f031c0b0406031202010209010905010801082109090f07231215130603060506030309030a03050c1c080105100809030d0207030903080325030905 77
    0xc450081c450561103007000703503002d8450804a09007558101c411544d85208040c068003c203080120607010f401001c210450a84020083d561300b9900010750103800445454a90020100007208a500c50b035a0000400401e8032a81c40960008082d000107a49000b810005809185075a0025040040140040c400a60007089008080180030041d4812104541d26016580142032a260300100582d080005c612035582c9428040c950984401c1403c081001c0c000b60340f4400f42e001d100452608102100d006440915402e0b801140110600c000c1282000041c881585110007001c030180c6600d802d0003446400e10a85030002d908600561406102c000482c1c0ca520a058020701448004a01410309010030f2140420348501d0004d40501080994800742c0801c1080c000d65020b40342c4800022100b6010b210454004c100440085090204400711000a0750000b2412400c100140b08000300250820b8099401850944104801000042035511030400111144001c150601ea029000b00700f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 235740260 1250 235739010 235739027
    0x180501030c05010e012d080c030402030712030c02090f18070e1b0c0105010602010911010203091f0302071b060215040305031f031a0f1803090d060b03070b090f0d03 72
    0x20b080000b44e2007242e40041e6050b00201e94200d0100c100c42625588884900c4061207442c2820b0711007001c240c44011240d003090204a40094040e804007074207018003c541141c0004c10b40c03003407415001d2000a17502241100a064074400c040340e034500140071045403038140030fa40c0d025030a00144007480c60030f00030700740c0c001000d8400c1d0303c86000003409006103251081111850341c01ca01c028040d41d603640704028001c00000409440d0400e8500751810550f1012080302c550725030050000e2500002040c801c42c2c4003005200034070505500b00314080c0006e844042d881006a0320704e0706941b5081c504000a42001c040f90301012100700b164040000180e00a01543d070001640c0001240407110b9000044110899420141604094007e00900ea00801029520801c09804100d0441c1c5441100590108c0c00042d0840590030510202485003003920100300854050b90011840d03c2303002c00400e0500003560003201c412440090307201c14900300030011030b8020805407003862082e003150300e00820011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 235741510 1250 235740260 235740269
    0x12040905070201060308040609140111030304060b0f040e0f15090615030c0d0605100b0a0c02061c1d0d1d3c03060f01060206060603071116180501030c 66
    0x1503803038001c01c03810392007544608013541c0e010340241d50b00d50301d5501c0542030014030700c40d001c0034209003a51310155510806100400e1038600d0021425034640b07581d10005003040c001500c0e002a4140400c10041e43d80e400384201c1c401810ac01341031402d80813154541445090580c0340c0908102500740301010b800001d03103c1e4880d0103145034a0114020300c00190400c1000c0702c1440d403104050318084240111a401603001c0d15a110403400c44555528000f4034a000390403088003c03424000c010700150801070000e0508034020301a038000c508011000700222014a208943d0900700300b94844030f8090100a84503c9400341c1c1000511501701f40345200d64a0300a20307000d4051110b90007002010000c1c074030580c0c850304485088205001004161411541e103a00d50304d8464030408002c507400c5000854458160382d400d0f030140940c2d0340c03000184441540054810010420b9040b1405101001844011b0401541440b65103e962405084400741c044140190f400e07d42f0f042c0040000515003550001100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 235742760 1250 235741510 235741529
    0x40c0203091908030d0230070c060b12060615030f220c0602010c091a0403030309022407030e040506090a05090c091f23061c090501060f05031204 64
    0x1031601da005140e51403942d900c000e15901c00800d005284041c5ca4000d46455041c250b0200300503011358401072002e04604520321010111100070501d907a104804c0d20f00c005002e00c0e0042800075030300022510003084410003c0180e00103400303118851910310f52148100c00f5404a86003182010243e44800c90700140c8242503845900c1820481a00301502070760704c2c40c0e001003080a42c01d598400c081d018083c811140310000b8001400807441c03e00310050f00756801e808000d1903051a0a5580940041c410048140da114015020381e20f03004a070051f020510300c61103410941c0b1000140707005044401900100c0c3c0c4542c1c00c1000300036003070700c0300c401d40c170362202a0380004141501e41d14035950400380038201e41c42c0c004402008114400e01041c9807261a84103070401c0702941599008509811140400ca02c040e180d00100805030724948030b8041c00c1d1b80302c00309440e504c0c03c022100045040702c20220003211907944510382044009030424114006050039406005000a003401d45c6446201d5402101c0e0329 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 235744010 1250 235742760 235742779
    0x7050304020117040501090c12030e061e030a060906050904021008040c08161701050906010902070501021213060c020304051005160507030b04110609060d0507210c020705040c020309 80
    0x9581c452503071115010b6840c00f50284a040604042d4041e0001c0c200c1030390f1000703440c40002103504151080d00c08564140d030314200007080717620400846a22461286010103030303000d4100000f84404d0015805040043d0000589503d0a00b0f5036007901ca85a111903c00c420202c10400540c44a0a040c0030b10b0f0807030710302070aa40c1d0716850601d2856605411080140c0b00e101c400082d031070011341c6d4101c03c0e15a05000281a40750741c2007168240e0780115503803045908140c00400c00102160007a03d02c5c0d03032081c4005820003020705042602007200304e99005500800ca1820b40a1250074450800403845502c00743d498503040c00041640101352114007400c1003000900c0c02603007000b0354190020307940e00500b038450180d41d0f800e0100c0d0010050b41d040d100080740c55108003241c60480300705d032951840900a28288142c02c10b0640003400d000380000f080c045084403681c005036540c0721004200c9000600092655806440240b07041505e1f0441030296252020316904a90004203440c8614801c65008a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 235745260 1250 235744010 235744013
    0x906030f20090a0b191107030c06080a140a05150f0f0d05010609110306010f111221091006060306030c0e100b0c060a0b06071a0702030708070f030305010b04030b07050304 75
    0x20b0a4106520115102c02e02245085176010241040c0c030b80b41d1200d41e034120485504c192950788a1405d0b100c0189030071042031080119900403c0740035804004103000040710401c03010603101c940070440307a400345a80e0b036000300403032101403120745000c0000a541c00201e403544200407525260100c4850f9119680004505082203c250000e0029203e003c0090004507034144800841d03404c16214203000c40c0308074030030035119841143c0c450b810555042c010203000b02100703a4855541e001d9047c4011490744010410b1004907008031690047c8100d10092020440815a98041b5042c50b0011810541800e4080010504010311041603a200100d511a0303502c401d40c04000c2c20040d0f0307000c2036090802241a03012140085903c52258180500500a03250381800304009442080d8005040101c1203480880e803c903009031036903011440d070044a203044980d4445880d9074106460483d0703501250001c0750308140d41070142030300521808400504042c01e41e44c1c0c0600c2c80070020490740410902100007070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 235746510 1250 235745260 235745269
    0x403080f092404060b030604030c03050304031704030905092413021e0c15070c030309020312120a060504020a02120a05120a0e010c0513210c060906030f2009 69
    0xc2d1020311142d03600c00c11080440c02d03410941c000f02c030143d6442d0300d1320032840d6250401007a9288501c1e03055641c040d000d0216501558581c00150080e000c00c030020f0135143c040040d1340802400369010780c581020642c944004c000d800800105000d04940c42800500c3c16400742100c1a001c0500c11a0001464003100038150000d005014030890451400029501419075175001040210303610f038291000b441806100b403544030403e5500c28000b0b03010013580b07400319200341c1c0071424662006042d034103400c0c15089070b40000e4010b10903000c07480100d03105001d00c942c010f100d10802028243c17415820075404c55006903c07502d03560320304402c00744002604070f24240700c0c5040f200c100c0c2e608408000541408a4030000500003e245608150f1030100300388030050103102980c2e1046c00b0528080407150070180807440e00c80e6010091074601e80c0d0546c1070400240e40685240c00ba08040d516000150b00d0f04000400383c841d109202040c091801c49100b00070100010030030403c1e00c801c0d510f95922107128020a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 235747760 1250 235746510 235746523
    0x80a051b061b09032e0c050403030f030c120f09060e0d0809010606020604020d030201021216080928080c0604030206040c06180303051c06090b0310050603150603150702070314060403080f09 83
    0x185c0142e480e20103051001d640100150094a00966074400c15a07007521b404c2e0111482400c449000c031394080203084100748a50070841c500c61400c0c1000c155a8603e55492050304c2021b045031802d504040d00c1108125400040554030a840c034009001c80d070324002000e5100c0d03d002d040680102c0a5044180600d4000d4049030000d02a6000b48100d81c0f903d6110070b2882d19a90707440c0d8002465080201e8001100000e03403006000c0a00f04007070360740080104c04620020303d840100e4000000b48104002e000050081500c1940031780c010703040745c1ca440e01d01030007001d071280c205105101e0031088201d401035980007028141c17035060a141b0f0361071750301c48203850f1100114108100c4079400c03c203021a0301d501c0e9070010240b0f0300d0150215801e0315500b01c0d00b142035138411200d840d015401007001c510f00d5003028841c81c1d0010b502409403074414000f0b18000c8002e40d000c8444a0143e030001e1001c00c1000706148441c030015191801030036840c140341d0742c0140305000c05800c8140040c10040800c401d02c200388441d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 235749010 1250 235747760 235747843
    0x40b07080c16080c0a140a0506090a08060a0506091e06040f0e060403210e030d02030601050f070605071218021e03070603050f06030d0c080a051b061b0903 68
    0x110081d0340e0314410f01d6512018111a940291840c0c0000207018206414614400310b0007808045140d04060a101d1107030000e00b01294080d01520b400543c070001402518010004400082a103142030000d0003000725024203d010109500301a804084085806003074020350100c402190122031070170801c0c0680010146d05400f80a0403090104040d0050400f04412040490b00d03a032003052070328135404941d0240000500740e00200b0801010107002e50085134001c0d014100207040141b05602c100c01c0e0b030049a41140c1e25035599007031007a40c42e00f0114080a44011a00c1032060b0825605602e80061120900a00500d818010b5110355981050041c11041c8050211859a643c2d00e1000740a01410343d01e0440340b158080100d40c4a08002c0b50010b95004640c0302e200d0f40410720383d241503071680607210044c2005014000320089504d01c2000300300642014000300000e040101d864508480c05014041e0502c100300509086900c01203102c0d0352042442e013442c60941c2c8003110100c068510500c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 235750260 1250 235749010 235749043
    0x3090109020a0801090210030506100507050102130b0705101a0603041106030a020414030a05060f070e030106090b090a05150609040207060e0109050d02031806030702160b1e040b07080c 81
    0x180400d50f07850542c08011500d00844500c9410103a20345c0a80803510700340c9140790048294211030f00b400340030340f00810515100702e00061805080c1031002c00060243d81040c40c401c90001469400e11104028507464040c03140000c00c41486050b00340402d0324400401140204000704c000703000c2c080940840c0e442003001070300040e0f4a01d846401d001c001e51040c01805081c209039044480309041c000b4060b480c0b80e62000082420362030752940c415034910001d01c1c500401054403010502030303d0030301840340101036084020076090280d5041101c10580100500c007668602410420103040d07044481c164444283d840d1a901e00f0b411001c02c2c081d1103202d40142c4628108840c4102000055000b03258290040741131701c140c0361010104a07268459207101c0080020190350704031061405030011038010506004a400d0742039044a1911401c10540c0b0007419210003040000e041410000c0b0411422a496a42460f2600386062100c2c98010000003801440c80130580c1e401c049400c200c0c0304640c55007041d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 235751510 1250 235750260 235750279
    0x7050604030306051915051303050a120e040e1c020c09040506070305010e04080301030201200f07060f020c06030f1503030c1b060301030203060609040512160210090b04030303020309010902 83
    0x1d01501a101c603104460090040500e1030100c00c038000e2141c8241d540000708611001220481141e90b500007004110309903100d4000000002d004002020b0224800e8240d8a80c0343c03180d44002c0d00254241c13004900a034140b203140c0503c440003107400d04541e14800e242500301032625400324540001d06156903000702401c2c0c00d1205200b000184107100e622595400d0007144c0e243c018103000b20f4000d5400070710140092005000660143c840e000c05050303040c5440d40141201e51643d403526152842c5540c840d000903405206c202e600402c0e0036201480ea000801e40c1d040030700d0100d202c520000301949403400001010902c2100e61592080311030070000c0c2141e0316044c040110702d0321403d0061a13101c0c0c03100e1b000c1210125040100c283d904aa400074041d040341da40380014441126001881107416024004d8220219030840e0050189100d4424405640c1290791060145803a490100b150a00182034810485290381000722400e90350b1501d405030301e07602c500c0c1144d4050103031070b01c00a60100902 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 235752760 1250 235751510 235751513
    0x60120010e0a05160605071707060903080604201213060e0f161d090c04051008070e010e071409060301141e0a12020f040504050a030f031404061107050604 68
    0x1102d0900e00d0060082e6441902c400c82c04600400b418071850000c18028000e16001c90302424641c22031082040c129840c0c000141d60340411039190482c11400300301c41c0414403416084c5481a52042000b11003441000e65045401e140140542074061220846010008030b40856403580c1d14402d076844141401050b41650b80152222010909035103a842404c41c0e1904c440d035640b071101c2c03c0f0343c22080c0c881401100d25460a481420040007440c0d5442800b023081c9480c3c40d10b2040521407090180011041c40c01e0810440c141241e961100510b15040c0005001a00348500c0c400d4201045050405221000d244004403501440c248140d2142010000281d4029034040d203400c0e80108454520715034a1813402d502610201302c2413070750000344020301841103103002d000107c0010b000906060220400b5030000d016105c04072000c488c1a00800400c0b820540c0100e0000d03002090350805108203e0070303840031000e80d000140060106500e81c0b03076540880c102402140c0003560000d05448040c03905 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 235754010 1250 235752760 235752763
    0x812092b03080708130b04020414040c0609170d081b030106030f060603020711150c0303100314030c0c010804030c060c03091412070b090c060c0d090f0806060120010e 73
    0x36800c1d408a8507040000740c100e8894407800c2e00ca07a01011880074101625150034488805c020b1080360055074551310510000c035090308107803295108407450242c1ca4140703040200b46c1c4c01d269204800c10a00281002c8400c04041a4440c1c54051890310800e03c0e5580301d94004000b050000070044114000004a00b0591680101440407020304080c4442c541c0e4030720450483c42180700c007a01c1059240390901241c030300251402c0802c62140751890401e407804c1d903070600319802514605030384202a442003041000300100e407420001c07081c0155040120851001351141ea84465150402101302c001400701801a0740c203e94543e0000c5d0200301c0e01103004d002600405249030300340c0d00b0300082030310032070b494600051008846140c000714030b050000c2c568801c0c0483c1400341c4440f038107002d03101e0b00b0302e41e80d22950003400054040000805c410003103100042c1c4020304940150000c1d036441c003001d020318140000c1843e08072400f031030101e0b107410307980c802d4506418206100300895403c00b5503510503c0390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 235755260 1250 235754010 235754089
    0x10b160f1406060f0618190801150609051f0318051b04050114011416150605060403030516150e030418050702060403230a030603060507030501081209 66
    0x606011154036031660020800b0000c030200c07429600c41c404202c030f4407800704904911b030b5250f00042c06400c02d844000c07018010455168000e10300030380d5101940b003192002e6a180070024451800c0c0f041c0b02030f04000205944e042c1105050300e1240042416070209842988078420350700003240101032a400d01d10300180c80c1c0d108079440c3d5503480d26560801826160900c83d10f4100c2e541400171940c000410401911050b200060100d42d002003400408241e101d011050381020303220300c1120f61010141d566110882d041604100e014100500091000940007070888101c1e503407001c1907000400941ca40b080c4094121305110030740070700703203840c0300d01840c4000040d1065a00071000e00c140c070030213500180101c500856003000142d00900104002c6802000d42c1c200707814017030103034500c801c940b050012140d51040220600190796901c040041c82403d10445401010610b0180f0541d4540f85c15583d542414400d4016540c00009034414640d807141244a100d4030b55007004503c40c548500070404080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 235756510 1250 235755260 235755293
    0x80409051b03060409030908011a1c0201081902090d03030b040f1503140a08180f0405040b01030818030613020f09040f1205160c06030c09050603010b160f 68
    0xa042601041c418058104510300500806550328119501c050812018040d031a9050307083c8094241c000c03448200070b0003003124245121880f2000100642c0c24016040c9401c181200006549403aa10040c1e91100a0941020310000340d81000703481c1401034402407084020f582d600008440034a81055015005071004100851b02002150000560803041c4c83c00d0550381c0312040c1cac1c20001840001c443d14407111001648a00b00c80e40c100995071281010f9010002480c01c00200e81c85118551078680b20340c12131204295418000c0340ac25584c0c401c42ca10043c00002c0403140003241840705220012640c09001000804448003800c007040300507101d00507034600341d01a01c516590141030303040818040e400307140e0040445a14240d640c44085501280756500300030090108050710301918410008484a801130040811032450008040d0448100d0300220b814041810001c2145035111000c0d40d04403560300c82c0b40391703541c0c002101c4400349041c00a40203041c60181e419075018080e5101803141c898 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 235757760 1250 235756510 235756529
    0xa080601031e060515071106280306180c120c030b0a090902090a0c020712050c09070f020d0207080d050c0309030a030504030c05061e09180a0c020c04050105150a090308070804 77
    0xc1d0070118405615211b65480079001d100c407540307a201503042ca01c0c020401580613000152107080c080d001212040e08104210000035102d41c4248003204d0034070540300036161308050810001e4401c040243c90706080c0c2d0620654295074050705000715009821070034000c80d008283c0000f8039100c400c0c4100405048030143d00a50081c000500300350001e00c291005070b03050fa0014030319140b50224038501140541012240b50060010844994480d5040d56000b9443c588845810f1100d01da030080c038100c0c1603504c050441d8842103007041040710200e400c1c1d02c0f03840a494100e81e10341010b0f0781d0350715620600b403519400d4030814070410141075010014000341c0e8411800c80341041d96401c10040b20303005458101d5010909141c1010f6019011002003154030f0000d44640440c1101e0011021100d404541210409032034460421701180d040c0040425208115000c0016504103000f00700e84040c800310500352a1400508028803a0065076039400551780300f14001d658918bd1310301525160090702c41d01284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 235759010 1250 235757760 235757779
    0x30e040e0f060a11040510110105011502060f06010e0d0819090f0602010213171c050307030e070311060a110709090b06012c040209060309010507020c0907050a080601031e0605 77
    0xf04140b40c0070342400d00c10040545030900c0d042c00c0400119101c1030a0346810321032610104001c9200a00405d802000010100c0082d808400c8000e410464000c250303259100c24941004410380c0c1240b04041160019600c803464440d1901d4083c000384103418034040054240c040c50302e02075502075400c2c819500c1c9400140e00c060341d640010303400c1c3d006520000c00c2c4e401c0116070502128250390210580011000100e07590306801341d00840c80c0b554983c02000000c3ea0002c20007000390303003500682401295038030081c85040e1460310358211009503a04928403a03800040c16241441c401c1e0101007142d240e20064460040d034442055000f004074940440c1c0324400d02000030031541c0070b800314903852095010102d42003541e1345400101c07540d981c00d41d507a01c16800e10148600d81c4402c0c0295119a29200002541e8248040c0c064a8a050412810710500000d01000b103003030340c003c059410000b0b15042032603454440e00c005030b0241c007125030303d800900c001b024458014142c40c1c00c4501103490503200c9009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 235760260 1250 235759010 235759021
    0x209180f100c1b03090603020702040906020712180806040b100f0605070528020f04020418090506010503010912260405151b0913090b040f110d02090f04030e040e0f06 73
    0x24002c40f0643c05004290340c0c04042002601a80060404500c024000910884166942000c0740c0100209440400152951810380ba4004101c2c04800311021a2403442515020b445a5900c030000c01c02410702d59204040340d2021110030810010b003030080d49407401c41d51540c90052460300b00351000d4480e031151007441a40400461078407040c41100c00305442d540442c0b6020701001403180c000260b00a0303800c100c0040c541521082810b4032075843c1130081200341c03c1b801d0281c40c081d01038000740e101c4d1b45081d485400041c0070140110700742800b0f0418000285510503a00d000109490740c000c207480201c01040304012000c20704104844080c44480b01c151550f142c2c0d03001070149070b041100700c03000800ca400614a00031340d01c050310101c0840c000c0f95080e1144e8810108460540d4121058a0111a900100b05503c044094015425910030002001c240c00050302610082e0412861041403004113040c940318040502d43d4640280007031124244c204240c50355410342c0c40c40c850550160401041e03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 235761510 1250 235760260 235760297
    0xf0c01020f07060c1e0809120a0e0102011103060612130803040f032007063c0f0f05030103020904020f0411090406060804080f090109090908030402090609040209180f100c 75
    0x950f9800680300702c030075404690041e41c0700040580317222030380d1181e030203506540c88108d8000c00011440355241c4001400080019007581c3c3c880b00d241380d1914091042055644407002550010f007201d40400f0460703168141d46a216452101016108810000411060042604410000ca0312a955034200c482e82414414211070070510b02c0303055908403003003c0013110702c101d814040705981c00030071402c40300c81204200d0300d510200151114101041c0b4101075103d82001c2071850320000c604000c1c0a0b440c1c0c0040080ca60711050200a105042a00215041d9120170b4290f02d44c0040c040e104110b008101d220300321f59600000140c503c554144140860614440c2412038043d1350b01034111418000720144001c2190008074a030341c1003000060f40054912550f0184031065030240c11050380c1e904082c0140140014010030a50082c800b41091100607100c1c0c003503c42e0302000505007500011000000c1c039041c08011202c903c4240b040e600c5040155115600150344012a61500f5580d514010b1050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 235762760 1250 235761510 235761527
    0x316110f090105060c03220504060605030112032006042001050702010806040c11030301060c0c0b04080d1101060b0c070906090b0d110f0a0902030a2f0f0c01020f07060c 74
    0x90750400720140040203a810300e000581660010181a40d00300148a241000001e0030418409417040c115607040000c0d041503c00c80c80503000700e2030a68a5581041c580d81c0031820744400040800050b0ba8040b1901540814243c1d248a0740805881450804e23061040e1021040c061014a540411031200e480750700500c00c80315015410313101c0c9203980d41c3e003a003080020000d1250300d0050004407580b60000c60b45c140020340c0038001320b4079052107081d000e007469850303c10590814549481c0802c02407050450000d031440149605190204001d0800035006024010582c000400d00c500271410040613040440e003441550b0b2076000802000d035591100d2400d0307649000d078142c1c02c400c20245460101e490051b03444c01400c000741840613420a014082919a4640c1e809a00030380c0e03012080c407542c04018000d99140491080514640c42c5e4002c000d45c60307280320341c0b5400c400945c000a44501c0642802c5c107980302e01e40d49800840d21051685008403480e8010001107504074030b00b09403d5011400740040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 235764010 1250 235762760 235762789
    0x615110c0a03080f070209090a0501060f0e06040c210605040b19030f030e09040305270102120c07050406030602041505070510020a0203070501240503121801050c031611 74
    0x35403480c0d142d40c480d4007241d48000c3c0000342c044400c10181d80903880c0e0009060080e80014000d10801155042c031508644941e00026100c1140c2d40040220040c100c50190b000300044500162006018005a42c921410035842880503ca0360040b1504549030b402030040321010f40d802d0044411240400c1981c1844004c403020540c11480148040342404d0403402100d8880d0800c010700300d2403000000d90124048a00b10300007000042c20724044010a000a004d0030341c1902120005007a00b00007070b40b100104c11001e002590b001c14100000b00d0f040021100070720000e0820043c5549a06001300a5400380c0501030444151011140c00540709030704942c8600c0c0c000c8094200840f10146040103503114100540442c8024003248000c20400e01c42c0720b10000601d00c1150f8205503005295004100c00d0f40000d11030b8104400c0300c40c030303100303000201c40c030300450f410042c4211040341006a880e0300031207400b101a444041307069400340c4041e000c80030103140511020350984018504021700150103650 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 235765260 1250 235764010 235764019
    0x80c040f14101703190c02011403100f061e030506150d090302010606050301080304090b0409140a02040b040c1704020102070305030301060f0e0f06090d060204080a111002061e0603010f0615110c 85
    0x10361003119841072202c80386c2c540c8140b4041d4102298881540d14036081a82c20400001c2c110302e0800120b2440c8038114010109401d2103a40c3c04d0600001e4008580c1b2064410f00b450b880310300090159880705400349290035000c1d021604c5180b5000b0701c0c00100040d101c21009986454808941107020b0001c0d60b04035011280154607050034a440b06001d00340d00d581850b0401e448403112800235464aa00c14606c83c105001803699501c580104001c0d04c07045090b25014528062504025a50007907201191100d80c01018859465520040340f600c09030340d2026010740400b000104900e80e1080300000566040e64514114007004000c000403a000900d000d81d0007001041250b00504011820b0b0500500940b001400d062703445841034244420141c0444104131030300042c800706e00d000d008401d424256071000f0011840d10394000c400d40781e12680310300803081900c00082c62650f003d40000031a0800303001c05100950390b80b10302d244403884000312200030540c4461004100380c4009007030132000341d0080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 235766510 1250 235765260 235765297
    0x1409010611031c02070b010b030709120c03081b12030c22050406060c1e0b04022e0c050c01110303190b040c200304080c040f14101703 59
    0x1901a01c245080a2040d04280400d0006618907810162a1100030740380880240c0c0d954190b2070440c0f00340b80140c10800e00f00341c0c02d005104c0106d5001103007a0035031307034500113a01d4041e40a090202c42d8900c2944002e007040b10010b0308415808078120b0051054010600301c070309407080040c940821380403c80780300715080303010b014020a02e040c1e8095803c43c44180710644c01000d4892001c54165071180d004140400c11902e000d4040042c602800122040082c004480d000c1052b0345100880c8006003010784203954803282c0c1604085502010304000400c8400c5680c0300008680141408040520990709401842c1c0030119039402071061804030340d0150091860759075070424907910000c2005100070b60560b10f10203e200750311203100e2f88070740318032584401c07011003001c00d08103d00743c0f071a8000c1303002c5410130321040012100029400c2c091079000c4502240310307a05c401c1c5103c001d04417141720440500100d01407040b000c50f61080b10703003982d400c50000780b412510b05200d0390740c03445100d17619220400d084 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 235767760 1250 235766510 235766519
    0x120708030f0904180b070e2205040314070b190207030e100e06040803030108010507020a120309030c02180a05070201022d19020f0c010c121101060807120c140901 71
    0x158018482c40000500000361000045803640041c01c0245003120039410b40f8007030081c0705030098842c151207501241c1c0b0301120603009411140d184010944038510544030004181010f00078050081a04001c07000e182c2c8031040c0e0300305004200c0060765001d8007813044101d00e6413060054021101c00c0c03071300340c4c03108040210514140f00700c025603270300c0301010010030354060b00340c0f40c0e100402400100200300042d03499504011200e800c40d040600f04601759030140c80f01c1c000180310494540d40407421402c000031070b181c8509003a00d071030b9a00c64000394172151410000d15442404164107010f9105c40000308103507608c1c444103038200d200b444401074402c1d00c050080505a10212603102901d2030b544222401c2205000300d040854607000800303809a040040800c42c0c4403410480f0032800c0700246092081d40f58252100420000c070f52103140700304090b0901034024020250003171402803000004517007500b965012041c4928442200454010200b01030005640f580688030708085040103001c00340a07441d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 235769010 1250 235767760 235767787
    0x13060b06090108060f063114100518060a0c03020d09050a092a08090607051804050907080f0c0109090c080c0307030b1905270a020906070203010204030309030212070803 74
    0xd00000b031b81d00c00400c104000c2135024103c40c12003101030060404000041030000e8018500d503580082000e084411000307001981d9400441c8200c1e01da0303060460b40c8400f0381c112a800c000002c80c1403a001940011007990103907002d1458002c2d64001c3d400da49510700707100d80485019030035115899010310115030501140308260700c11185400b944980c201c0b08a0551058220701c035110038004045440700d002c000c1200014015140d10404d40d282840ca0030316004028080c1c00b00c40c04100380116511400540c032584204805070280030641c04840c460700190014569030186a02240c1c0082d06c0501c0000300f000c510f01a00002200030348030000340b42c1d603054408440b500000c10540c20181c58100f00700441d09c1d008c2e0310b0a130a60824108880080c100828819405443c03050000c603100055065100e1740f0580d107095800c201e0342080540c0c0c40e00c0b0000010032502a4160280d0301d54070010780001050303002800081224425906c0400209880d030010380c86503054822030907540c01c10004c09910001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 235770260 1250 235769010 235769029
    0x3060c0f0e040f06031a060a17070e0c0d060b0c010b0a080303040609031803030807030e03130501120603060f09110a03201203030403030b040b030c030c100e030613060b0609010806 79
    0x400e0f5034009640c2c0d5a0f6269800242e0744185050000780d07061061101c14145104800041d0400302070304034034088404041c65490881e4032596031881c0b00d681c0402c0804668a04440c216400c01784140b109580f9001c0d80001740d840040108019840c0014586031401c0c111003010485000c0c0001c0c0d030859550751904406008048421000c00401c0c20b02100501c8034041c05c1e4010f1030190b654050a440c20050203030855051807001003070380e403051042c40604514a0100c0059030000e01c2c003a4130b4044540742810161266030402442d80c0e04200080c0790000d125804031000501811589820000000911100b0300150101502c007001c100b001014104a440c440c03003903150083d01840c011a921400305045800c180c404400107500d40541419901d041d00810b43c3c5403404034040c1040f005c80343c00181d560300e40640880e001e290000c008c0400715000721001500d0001c05010703a012850f143c0311070842428080403c44860345490280c1c0464181b00055400e040f05c1a183c00c40180c8500d010000000c0c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 235771510 1250 235770260 235770281
    0x411010905061207120506060910021002070501050609010b040810020f120a0b0103050f06130506030a05010912230301060c020f03010609020d180201050702120a0206120103060c0f0e04 81
    0xc0040c60014071525004010500c0b80d03c00e03542050709007045400104181161981c4200d030301d0400051040d00e660311011207847e818212980c5400c00540c1009a080c010b421400244803880443c0c1101403000c190007031445004102c803140220780c7c90f210103031038074081d500078501c49510034044c0301d01e13005035640201000c080c400495802c0001030008591a1003044400c1240031342c40d010130000b15605070150390382111580310044224070b08030011903d2541080907241200340c849001c94801d480c00c0c01040c082c3c6802c54020301240803103050100c43c3c8a0204081e10000b10b80044c10b402010380007020419240600141a295074a4004100e400c07055080050303900c04414070348064030765024403d0030010200070b0720142e01d034040c80c50014100c3d80c2c207004c40f04412015031500c400507a03102044601140e41200d01e0416401c0b170601c028030f0900c18020080d0005000940214114000d6507018101c80c440d90091012203a042c200319068400d000342103001c2581109480028030701500082c0214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 235772760 1250 235771510 235771517
    0x18011d030d05090907030c050906070f08190f02010903080402150d14190501030507030609140316060c0c020916020309030601030c05030609071206020d021218071508041101 76
    0x40240000241401e2241a042002c81c1c000605481107090000d000d590040d100c0c01c0401c40b0700c0005001070410301c120b1010340c0c450400020b00c8001c02410320b0f004a1401d80040803540c44888000400d00e030440c9a81e070b04400300c1c990544480b10144140546008154585e81c0c050761500e0b01d60034000700b100602030450083c3c40602c5041c225100600c2080f602d81c06811041d103881c200112007000100443d09210040d904080040c4041100010b03178400f00c1e42e0010000a5440050400300011402e030101c6400318080001c911520041854103418014010f40040102d262100070646006c901d01e4802500301c18120300182500c0c0340070108548850f0300b401a43e01e840065400a030410209800890b000c00342d40c1010300c82c0342410081c40744e00a110708002c011160400a0243c0d24a2503e070004142640000b03007441c201d0826019201c80c035071110000005410607a484032081c25000038440902d200321791000503860960a003a104140ca00d8039110515240c548030f86403900211583c681c140f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 235774010 1250 235772760 235772807
    0x2030f181002181f0e040c02120919060522120f05010b0d05031e030705040b0f1303110310061202090604090803010b030a0b0a0303090506070c030c090902010909021801 74
    0x80b40c64020920044e210040c404814400014001502c0b90b030800b0202c6000e20300d003c0e80f1604060b000076020b0000c52040c4e020f16216030380d600004055400124541c80c2c40d06221900040c4150400040d01c480300c98044812070840d0024503030540d681d41482070044010b12204400046111520b00078922805040003107134541c05035012a04601c2e17101e90440e00c0c1c1d8400180600d50500070000c004031120200d06840c91030400550007000c41c0203e0080031955100010134101c100014801c03581030805007070f020540d20303a40f41041003550b1103d02e0114002d01800d440e070000a04c4a1081d901540e40300d104856074070741e1a40a100018000411058119607180b1117140481c03518405580280305000150340d491812440000a40e10b240300c4940c01545180424800030790415082c400341c407001d89000f42c84200c40d040c40071000721541c0c405494000401404500819550040003a00d8000e89400005566851016080344070350551000000110800e81015601c5412140e0134150340390756802a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 235775260 1250 235774010 235774057
    0x308160818031c0206010608090106080706080a0e0105060114130e0901020a1b0c0e0408091905030c06070f02040b0d05010f05101512020a020f1002030f181002 70
    0x249a40500340c001544005040020341e20302d030800c00b00c0d46040e03a03004240800c0c0400071000e55226418010582804041c034002184035100354040710080511404031811a0b56404015001120940f00500302500303240c191884003a050194501885042c2e4482d41541c242c1c0608961941041c1c0ca5850304050707483c8001400c40e01501c1d070038020800c442c0016503c00d141d10003c1c01c090001100d402252058480100100b103103019001c044449441d1450099500c074548030319144100741c00c00e0ba1000e10708482203400c144009060003910b00503811150700e042004100501d5020300c0000070110b1210614031401400d00f03810180304d205001d400d00080405580d105429110b0740d01d2660680e90f031b07c0042099108031241c50720020309462000c5020900f808070f00034149044040034070461600003a030002e001c1d07c20480c0341078100d05101602d060011104650000e035000703688031802c08980b6004198864040c0d0001c00702d440800d001003036189200002d800113900482b1604105442c456003404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 235776510 1250 235775260 235775273
    0x5060c03060a0b1c0e0a0b0c0a090305010c090e07090819020102031204081e030103050a030e010e1005031005121902040b04180c0b0c190804030c0b0c010509010c050301030816 77
    0x1444520000d01314400d0829070b02d020100e8082c2c01183c0c003560f01030f0250b4004540c00403000b40d00800722460322a030724641280c00f6285065150303c014420b42ca810882e802c216401003030001503404070204201301d81c0350f0a43c110b4002010303008590309500f1402c3c040c40c00350400319104451510600699060969001c5186d201e00002c5909464007030002400c41915443c0042c084482c0c0e11020280b402c550464032200e40e604036120380181400b200192498040c0c0c043d45601071304200040028038003502100e801400c5402c1a10700c601d44c16000c08000c10b180c54266810302200340c10200a24544186501100a00100c488181d800603510354943d4215191400344003180503800704241030b042502d24204080324801e41c0104ca0000d010b002485803076001240e01e00b1941c0d460034091280c2c0303019040c100c40314402c0c0d51004021000c60039000400c80762000103425540d07000c2008100554411503403e090f640c450030400300103a0100700500000d007018010301003081c01ca40d84280400456074500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 235777760 1250 235776510 235776517
    0x11120306030a1406160c0b01050108040f0b0a1d070302220f0617100903090b070602120a0e3a0302090a03080301091109060405100c0b15010905090405060c03060a0b 72
    0x1e0740076004031040040a418941151741012243c0c40e100c0e08440b91a102d021400e44180680c0d4100012080400c0a00400c18640c03e0035a411643c1c2044c2030400081d003000034402620501500c10140c40c1c0c41140c01000b0914500b1690003400b10190790441d0115204051035003049155200d54a520006030ba000c1445910080c00ca0248010b08084880765803500c1d081c283c45603410080d080415003400654407060042c101d84101c4211500ca81003454142c01900820407822400d080c6102042404330598106030001c1154400380d80d20710003011038075424a48001d0071101d01c1d001e02e1010000b958900310f01d0300c0901c0480d00c0d0050070444c401c800a00c146840364015103040c00c0100c014030080c2103030f11030721000c05c0c1203001842c64540468003241c0e2900031842601d1003400e80d10354921a15000d421050180c50b4010b03071070381445ca4500340c041c400048100f4070a00040c83c0000201c3c8d9400d12040b103a0140d500200141156a241c4040d400e10354401011030f60030003c0400c00192003000c58015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 235779010 1250 235777760 235777793
    0x2030a050a08070b0c1c0c020102040308180f060705030307120e1e06010603090c17160f060e010c0213091106040e09061003020604350f010c11120306030a 68
    0x2407550f1106641801842035002400b42110840d00700102a07139102d20038401000c80313944140214625015142c16402401594005440f500000601c42d5001c0341c01525100301c404100e48071400c81c1400c6090003603034001d1920081c015441000810031035801168120724104038490042100350541e0451428240b0061001d040301d28500000104403e080c810359000d05182d243c10401903000e61a01450704101e0f10803001008180d511038020700d00d0a002c00100d03a801081c3d041800c680d1550000103110041c8607000014a280140341220341c451b01d40c1758003030b1360020500744920b07041241c8400107061a0104541503700c20803100c6144c0c4594000c3c000404c50401008420f2400c080100d041850080005100888403031041c00141d6980090310b054415070b001c0682c0e10302e2800c11700f04400400c0c00511040c02c0c2405d644c0281041c0009203141080c0744200244405c0e44800815100071200100c07515651300a001c1c404403001c4c900014681c03090005003100d02c400303d107884038204004510364 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 235780260 1250 235779010 235779023
    0x61c0302030306040f05090a080f160c030620030a15080d05040504060e1b0f0f070b04021311040614071a040b01170c0d030c0b090c0f15031302030a050a 67
    0x803c4620302d0203110f0041c4d131000160041c0303c5031800c07500680d1241c6114400602015011800c540c080010000782c90941d403411005450315811810800b03d035041a00c0200c40142c1024140240c1d820706070b00c2d03542000048400380d42592600c2c070194000d0301200c0c0c0250402207490308000703a852000c200414000c120381e02c1d03555540d403c010500003a00c590b50880c1444030320801c10701450746540940090804419081c40d034580304400800617032072180904500717804001090040074046441522402180300300d65040720f2000071525174003900d4038441c030140f110500f8002002694041c2181e2032444070103011040c601040c5540d1000d04c80b90310000300100c04080302c204010800c100e1761040c0900b1554207081c0c0c003501d940030346a40e682006000c250080d0b650702c121808060040121404450380407031400d92900d0f2580d40c0076514010300c1c00c40d03131044c94124071099540c1400f6200780f004010500c0094a999100e0015241001d0102c00403030305442800e007000e000c00c0091019406481c8103c9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 235781510 1250 235780260 235780267
    0x20102070f0c1401080c090103020306030a0f050d030b03010c0c0201050903070902070c06030b030a050604110a0306020d0b0f180a051305060f01090b09010806070c030201020d06061e02030406090b03061c030203 92
    0xb00000740c2402c01440f264180850b040a0143e541003500544103140e009183c0076030780340ea415001c281400003525000b8802c0e100d507030a080401030007141c00700b403050381981e0803c50740000b8070405080c1c3e0704120180d800324009034804400341d44940b000780002c0c5c4000d030484500700c1c0d071044d082c012640515002d03105000e08803004d001441c1e043c091540318001c11001441d100055850751a01c1d0306010300000d0682001d0140c0721036603150002c04c40011500a40d0441d111400d0803961409088001002d91156140111440b8285801e1030501c00080d5010500c044680c0c941d0850002424040e10404420319054649000124104500c42c484e0f6061700003108194500040507081d00c00640810780b20b15182001841050000210300364886030074a0310614030031850405a0080c418032040c81c0b903280c20110040b40c1c2da500000c1000855000503040924540105012078030390040780a2100042c0e09440100007588030403010710b82012000302700d1007100b0441c0300b260b9490b40c4200c004801507040071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 235782760 1250 235781510 235781519
    0x403030905120c1e06040812061527012105131b030b070509060d020a2708100905070e07050d0501090b01110c030c010302070303321b041203020102070f0c 68
    0x3840319113045001c180c02442d841c01e00d943c41c240311340680e40101d41a0003924000401507a40d8410a4100d00103802d01540c0c7c44042b190841d50890001680280010781c03124180c1d26540b00304401050103051881c034455240c21600c022001e420003419080145890401d214003040c002505210320804080807608004d00d58a400c900002c0000e1981c030900c08144489409511a50100c1d50700c6496807100503070b54910801c0c20b0b10050390f4800c2301d10009095401740d4240c1980140107505880c0d085003140d902104048004007031b2030030500001d0064000100401030151090401500000f59003811402c04100268070030031607109070700982941340c490310141c4581d6041452405e00c420750070054a40543e000010079500d00c03a0301141810143d000600009141c032a40c015001c1d80a0049800000c440c40910002911a281845e070541c4031a000881c07400241050101c01920130742a4a83c1030500d4480042084101d000066003555000c010410008944401c806e128521640c005401241407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 235784010 1250 235782760 235782793
    0xb0c1806120121030f1110090605190905191e0b01061b2103090b09030a030c0c0f0201050d020408031314040603030e0f030a0203070603051603060e0403030905120c 72
    0xf08078040d020600c00c5107280003c41d034450b450a50a1712542441004103002041e80362414080640d607400b010702d1701c0400d030100061354200702d00689014021481da1486000841c007203a2841da0010842e07442496401044444110300500c414002d540203104c2c200920054012001c4604c0c2c1140c041007040014400c4582208868404105039095085424042d40c0c1d04039240151411002400c01c66540c0e1921f06846a048508415070140e0b8614a6083c54a5890b56031707000785160001003030401151581c07a9219041707030781d10a60009000c2e00300302d07420380054407070f6801b000308410119004c00010400c0d050800c018800b400499810014803403402400c0c3c1c004000e5581b506100e2401d00c0e9080000c03c0d4084045144e243d400c40d02c0c5090200c10b440003d14140d11140c009406000d01d83c80021a41d07050ba00040c8904100c003c09021040c1c0c00004504440080c090660a03031031b0034000c90007085c0b01c0e60100003114421012140f030b034007681c00c2006043c0c0000040c8506a403080b5410308903400d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 235785260 1250 235784010 235784039
    0xc0e0d1202030c0303130215030403210609090c091d071517010e040218070918140c07110f010c0b090109050106120c0e06060405130b04090305030a05070c0b0c18061201 74
    0x232800d410754118201a6401410b1307268550142e1b048000c2c001089c886826180d0000c002005451020010810b20341b070013400d0a51b1521031581c2031890103aa10001100215110703d0300107402c0e001d800200d0400c040c2240414090b031055040000e1014946250389440c500180a03040c0307030134081c10303d01d0244104070344aa0b2881d4144201c0042c4400e011002d5003000025003076500c444840355960b102190b00c14010306a2000320401c0c400208140f1041907040320003407601a02540a444200c0d1a0805100e20344400d40ca50701d001408107005c241c0818400c1d14400e03000000312002190307040b482e0311054292840e6421644020081781200001c125482d01203200801513035108907118501940062050301440c0f0909026000d2400d0400064199a0014002c07a1000304100001c0d0160305004085401c1147c0d9480640d03e4400400c4800b8026a90f041c0060fa000307282c15190340e6125850009034000084900520000b00401603256888001800703401809008180725589404484e248109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 235786510 1250 235785260 235785289
    0x1c0207060c0c0309060c03050903253807210e01030b03120c0f030307090501030e010b030604110406091a040c0f0e0105071110020703060c0e0d1202030c03031302 71
    0x242e050301403000690000c0200c000c4030b82c50308010040010600f400e5815205400c2e00300d81c14040c0010700b19610407007410180003c05114075504105407a445803014198100c0d0b004035075407030a546411402068814440b1491108504040c04c002c0310369180044ca03681c080e0151040c400030081d45108a50140101c401c191092800b4020f1807002c0740800e40314405500349a4601d440011000542c80080012a0501ca80c1c982200d40ea841e00c84401000860036010700d9000034100140f03032018841c14002c2e0118140002d010b0501038955954051780c03064200303181a04a62241000140d83c06140b1401e0400c504000d0b402d200c00c40880208000c0710a01c4581d20180003007992041009548a01806030803103003824040d81e20707a070a0178004400d50701480a2580074403901d17080008158003003006130450b0f10502050149605104082c0c80000508011a03001400e4500d044003044038410b8003d62803078180181c9180004a01000d803d50b80104d41420b401c01d1b500b2504011420301000ca00c002c0f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 235787760 1250 235786510 235786517
    0x21e0310060e0103060b030102190306080d3608010212060a1502120f0403021e01031b0f140405100c17090d0f0611031303110c0102120c01021c0207060c 67
    0x505042d0b07078807140360060002415803551050301e8410307910258115140c5022001003409180a0fa82c001000b13001580a1990035010320b03149401a07601548003c0e018081c1d030104200c602440d0703040881e00e082e01155181c403070004142c000598013028801000c151100c00c000d600346113014014444000d43c140c1c8110500c0b00f210b4844100241e001c928106900403007000d07a41c2e20190000c0700003642c02181c2005e9441015180300481d595000d51028014030820303203050084400500302c1c540e082d01114000c10100e581e0502103071089100e10192880448200780480c102503c560211f06c0e410401002d10010541013528101130103101d0258076255900c080700240740c9182140032810300c00d541c0e00028815002e06e0000e104001141e0004005404051501600c0c0d00d400202d042c00c0200400003940800d1901011400603040032906030304507981030b002800e1a035440aa4074255900072134514002d03540c20b215400c040716801c289101400b40c62100175841c3c016038180b2008071140d0000c517400b031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 235789010 1250 235787760 235787771
    0x210060b040812160807030c080f1809010e27150103020a0e01080c040203090a051c0315050a05121204061706060a172206050708010509070c0b06010903021e0310 71
    0x900710005402e08150745c0001c129441da5150318065a15101001c0018204640030505100960b000d01c058104501d890305036403144a10315003404941ca10a003c0d9620341110080058000401d0b1018610003848400408002e003403289401c0b42424808140c0345210540c95004009514080c1205405410801a02c00c03240d4540b01c82980c0d1131107926001d40c010354011002410041d024401c40c0d0000c0c0d040021303a0043c440c403240c01c007810341c03090a602d40030138134000308610004100003d400030303139001034500f51350b2074140002c03c0410303170000900bd2000d22032002001c2100d24480c0161005100c25120091650301400102000702401003a0a00a4109001c0808655481000342000440c2e84c0542078164803105580c500e08034180c00e100402c0e0b03c1402600c010050f460b8011031040c2c0d0269500030b51a622601003010045c0251403032000250808020000b2558241150340c0098050510100c0c0998136404034502c900d1f0000300701017207810400000c00c541010b00803514102e01641d0b04101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 235790260 1250 235789010 235789027
    0x50a210f0206060114040e0a0501170f0a060e030c0f0606010906030b0d120e1c05060901061d0924270a0305030c040905131e020a0905070210060b040812 67
    0x54602c40100018100710f09140143c42e0f1000392001c45026010101e904000c81c030700305d001d10700980b4080c8100c4c4041c82c10030280d00110100442c0c6041e5055042015043c901607a84034100502113022001171140420000440050010030482003181c07203180107090b41d45000c20014080640503448407042c1820301d03a41c4039280d80c2c1c1c903c8244c1c01c2548034043d00381c18400000100d8141c01c0029800e6009942c0201c07050548402c0601c440c0024403071001c9840980c1c4940b0690b080e1062889101e401110800c004031105d9002c460055000c3e0385001251a0507880f41c041d5020100034804800c01003ca04050000d14003d15603544000702c035002c0c00000c030155041c1c180e591270901d5000942044400b0000c0303400002c81404aa0061603808003c3c8410706210705029920214040300700c40c500082030071030010246140d007484259400503c0346400d14a040011400360400400101c01c40c024003024003804074681c0700c2c8802910b11400080e4513141031482603460300310440c50301d40c54104113122841d07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 235791366 1106 235790260 235790263
    0xb09060d171c0609090f0b04050c060712030c020a0209061e0324070c0f08090d0b0709050a1707091e1a0a060c020907030c0c050a210f02 60
    0x2095650340100c40861710303569001014448103032010306c04a011035a070140d2090088054415120481000500300c0e0b0140e0300868258211001c0c4581050345480b48410b014103600080019001540004100c070200407c002e100740014217041c1900d00190030340d041c02101c05022a0284003070349100800992002249062401080380080d400354400ca480002d03c54121000c9144c4801036183c2c504960322410308140c0007402082c40d203000400c04000540321303903102c0d075401e0307000d07820502046881c2c0456800040850100c54265440c01c1d000304404044600fa040000350310110344103c58409425080101c0f2200d02e007004002c40380101070303803404400344d04440c030400082e00d6060980e480051003601a400521100018012038081d90021001c01c00505109000c0a1240d96061400820346c80443e0603441c94072011740c00c003ca9512a0010401038240b80040b122800c0d0000d = true := by decide +kernel

theorem cover : BRFrame.Cov 235611510 235791366 := by
  have h0 := BRFrame.cov_init 235611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 235611510 ≤ n) (h2 : n < 235791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
