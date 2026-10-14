-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1716
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:24:59.259395+00:00
-- url     : https://prove2.me/submissions/416205c7-7da6-455a-bb19-0a98e8beeea4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 308453237 ≤ n < 308633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 308454487 1250 308453237 308453281
    0x513090632010b0d020d0204030b15030708060702060606180415051203190f09030c0e100902090a0911070807080d05010503060c04060c140a0309050102010605011103030114040b090f 80
    0x46415807500401040601c280441c00b13407001d07030000754200c0741d1840b44d0607100516088410241ca0b881c25071700b240c840b020f4580d59548284203041002844450005900784922800d6028000c5c80c0c480c4d4050106607003003000b40310410340507085c161409032580c0c402c03494086442004038440f1850038013804500e403080d52000340d0030b42082103904038140030100d02204078070b500d00e0301996064220a0450b40c07888650401851086480c10000765044142c0415006000f824900340480b03a841024900300d02c290040983c1107460f91404000d01d1115602041c0c6074807812044504c1d03c5815a02c0e480e0f1039019507411a1544804184004144424410381d405414180d004000b0741c1404014808a4040c6110748802c1041c00e485400c10082ca24a0107401100b00c40219000d0340c003140760246c05d51005000d0300d0300540c82c0c00c5000656612654806600200d8030028520f540d08007503243c1103020f042510140c1050320b40c0d050056a4441d413880310300c0b82105d00703410019828041254503041c5203800c089 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 308455737 1250 308454487 308454581
    0x7030506010f0e0f0909150f33131508073605060303040b03090c0f1012021e0c030c120915031305010204080c0109050603010602060105130906 63
    0x1c0f24280d15050545010981c007154400307540d40c1c0d1010454070300b140e0310115065084808003130140072101c40f00c525000f2150380079581d111001c1080d960440e003a022600c00380d140d4a0304004045800e2004442003c0443e030034020a4051000b071803511140b045a002c6200c0340c2c4900c0c2d080160140120000c000c003803411200b0221552545a440040000b2514810999540344040340040e0380402c1103c00610784129203644a140040c0c4054a8031004080711340070b58010342c1243d446103000d00c0000c0307202c00399450300100722411020f0b140007504241c0440e61005d401e04c0d0f0fa600c0c40c81d0610054011407205400866994200313940d20303070900c4035011600f002101c0c28801034169954888010030191404010a601d03640c40d003111606407007881d00e015101c1e500c0081c2c00324084030046801d00a1683c280ca80d114220368900030700141d03102c00d104007001038001c0ca005010340d20b80003680701c00102c2c0603c1c020407540403985940c01200c814505610003010079040050f6045104c0c04040203041d691420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 308456987 1250 308455737 308455757
    0x30d050a0605011e0306180b030f0a030f0e030c0a0b03071206050f010809101a030c010c0506010317070614011a090a211e0b060904110d0f060507030506010f 69
    0x1130100c0c20798500c581042046001e01c0e601e4107104c0c1c3e00c107500070800c00d040c06249068012a9000412281c0c2d01140240180c1c00010300c8001d00041c002e070440e61507a20304d0020001200e04407168090a240f1390707414054601103424980d2207071858809000c004040c00c0d62410445005050030543c0401025554100f00080029640702c040301c101084003820a5a2655501c0c55030900300010032844290451a00d00000d101d00b4030f03242c2a0f403201030268119a085801c1c0001550b185900c02c000409541c0a08014400194038043c0c038504c04904c0c629282c10650603a403004281c914094212051103101c80c01002919076038110115802481002180340808550100da0300c120180540704910b909910310050700001842c880307042c181c02c640035041c0c0140ca060b0403040c103a980d6070143c030000171201c08180240741940026000741e50118203000103000d00c3c81800400703410402300342c0340b00c10440c0300000486c0441c020070f8030603015960b0020380c03860801e00142c880f044241500040000500d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 308458237 1250 308456987 308456989
    0x6010e010e0c030705040b0a030b0307080a0c090903021c0c02090709080a14101505040510080703060b03031903150602060c0405040f0207080f0406080a050f040b100314030d050a0605 80
    0x31442e04550705600d031540c0c0f540c0f8454203803120b00c03981d03010424a034000170314210541d60681c800411414224240c98400c2e59a08000361b41e22504640174214410640c0308004464556010503c52480b07030042d508040b1041541c16024081c0c9810a40490315200c0d00790b045203801c6603050780c06001410302c0320005d0b003480a0581d807150740910041c2081e1a078281c4000b4420700700844840d81a41e00d4046c0018540e2020001e200001441041c0c0224100781c0070a11507000c4c10145002c2d140340c2c3c001404440d1440e01c40f04050400d80b5a0250540070802854180c0c40520062141414003902c01040405011003140c80c104080e074031040854001c0014000c1c0c29942108603011544121004500403541c800940024400c102c001090294006605c074520000035001d04115092515401141c5c1c2e03681d40302e0010780350201d0f100c074050740080b000140042c1280009507007007040703181140f400b107840703580b050a110f00705400c28156a0011601d0801c441c40c501960744d004a000c101030101e249810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 308459487 1250 308458237 308458259
    0x201020a050a050703020f0607030603060b0f0102210d02070c0509070309110f010203040b0a0305070807110d03020307050c06010305102711011103033606010608060409200306010e01 80
    0x480c5442007203000130f90341007403503c200403e80841011006484041c106140c1c00f8005103071500c0101d581a00744804c1d8901c900d4201c8040940383c1060300609a101100a0b0303c0f652140a9207036800e07030308030600090076800d4040c405000b002d44603080d054415030804042100702100100b40008042c24994248000344800d013500c01e480800352070f01c61100d00105c0c0180c2c218000d03600300c00040d020124070b40d5003807a490781105000301b05070f0b124160140c550b5007007202c04000798012024250301c40d0901c0030203148258001d40e8072000c01c0c508141400c0c502400c00d4101102130b40159150382c031120110b52f104405214030300c00b101556003680c400310048124007000000004000d40700103084ca030700150b03e9000b0001d60314409682030a69903071703182410b01214102c3c01000544003580107001c80f07803804010031306210f01e0100c0402c0100301603860040200c904980c000c0c90190016143d00d9a03c000507040f0035012415044400c06a0a00881c00141854540144e002042c005407010042050020780 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 308460737 1250 308459487 308459497
    0x606030402150903010914010207291504021c0902010201050705071505060d0b070306030b180c040507030b10050306120705090106030230040302011a150717040e0907060201020a05 79
    0x29001c5a07200c00b07040001030b0043c81000d0015101151880d505222081c040d2700404090384205e2604007508c0680003c0e070845107442120a19286451000c10500e84004011350440d00d4010310151030f000c0c41080c0202d2030030745c020448050988904141c801c41da02809800d5100b00c09240060501c030031601c0f00005e490348420343c0300110340e0350008600251105410381d004280c0205142da840d0a1000740100200001e11040d1241c014902c0410329901401c40e90080c0d410764140241160b440120070800240b0f006030035481455610f0200f051181c807500ca8014203803110707449058a0f0300e4a1000d110b451f840b20034500210350005d01d010b0006507211655981582d01a241c0140c50b0030851100c441e40112001c1001204182c00d80b84a00050701c161155105074480e80c000d01c501900c1114610800441d0107403140d00031081811403004103552380180000c0380c00743d007000388041c00d10300880390300307078001d420100010380568204200d8000c00c0000d400284446c1c80214a0302c4401e200040080c022 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 308461987 1250 308460737 308460769
    0x20f01050601020c0f0a09020304080304150203071706010c05010e0106050102190209070c0c1e0302031b030c06090a0905010906062d050d09140f190206090103230a0f050606030402 79
    0x1001001d01700329100c14403003d001d0030000004654034102401c02c41c0c031540045804036a10309100740c5010100b8207074002d0301e0182c0d220f9201d509009130802e10510b02d0001c0140014104400c200c20035022540074014801108560000010320714101400241012200170042c3c124626003c0107000503240d5044151303004195188c8001c0180c3c1916000d0484c15107035004002551100143d281c6840c120030211040f03a10850442c3d4a0408503485a00c40b0608264450b81c1500b01454010150030824020700c03500070010140a40e494444ea8076000321002078003c40703a890342e0b90340d042c4401d642002c2500b200320100c0b040c00002090101000038035400421000040220200d0051190f030700c2500920012a0321814501321080d1200ea01ca17501c82c0c2c2141c801985108201d210f000901210700c403448020340250099280c1081440158007030170036400c03d08070405400500841d00c921001015002d103c075007102041103c01c3c0800003003a00c4021f000c2c80c0c4110420011300c401079555030b0140800b625 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 308463237 1250 308461987 308461999
    0x90a080a15021b10062d06030b01020f01090c03050d02060c040519120f02010306091406040e07080f0a150501060509010e040f0c050c011104180b0a120303020a020f01050601020c 78
    0x402460105070380f543c100c044490521a04940000742141a00004141c50000301c0c0e83c0a0030f0441544607501c01c3d0700c4040820b01701c0081d10180807544c8a42c008550080040c0110340c0c0b6001440c03203090848410340001d840c01020b0a20600410209002e040c07101c040700d20003054182403c1d03c03029041d100d54418140f2444620001205810f41804d140c8010941000f000070100880d0802984146040c0d000300d001a160800c00f0499083c0361180c2c140d9041c500d042610103982d614140320044c100001800c001c0e119510000421000401c003079180760a0b9100a02800f45407480c0045801e400840034000941c101401840300d6076100084d103c00c910709192100101800348040340040c81c20b452880c01c02030800b1248010160010000d295108030341e00200500000090301c0100340c01207001d4001240101c81d0402800c6809402c20000c6403c0186044942541c410304401c0e0a0440d40c000c81c0401e40101358a54419014841e481041040d10006e200f2498001d000039200c1580030546417040d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 308464487 1250 308463237 308463247
    0x1060c0510180206220b13050d0807080a0504031203020406140a090f0f0f09021207080c0d021801080f0405030f0a09051302070c08070303081305030c0a08090a080a1502 74
    0x7402d030800115071550040c044640d101d41d03043d0a07851a90840c921400000d1281d100011001c10302022180064515010880300d1420802049030318941d8800c10b0b00ca4030002e2120702c000c05c10100081040b1789041c0ca64590702e61442c5030500c80000220b103500c3c285407041c0010408660800305100101408114450340e42c09101405c4d541040c580e0403201c000d0150150101c1c440440f04490000c0d2040c0c0d1b2031300d2844075a503c504200342d11401e080301e81a840c4807000320300300f10702406016070001440d055540c244803408210f2012608103a014070388141c00c0e440c043c0d1039560002c203081d4101800000d010074500e40342d01c03081d60340d21411500314240700001541a8440344210312281c058040184900b841c1252420f42c10081d4000c103400b41c542607a01c1e5000178610f071001910320100ca40c9500c9216555860f0f540c42002698501d0054170b29000070000700151180038403040c1002440f078603015171944025810b00c00d056015801541507a40145504c0000c1400c081c070403a0f42000bc9840545d40d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 308465737 1250 308464487 308464511
    0x70203060a020c150a0c0909060b0406050714030a08040c320402040819020103110a020c01050a1205040f1103030405060306060c07030507090f0b1f0c060b06040b03040b01060c0510 79
    0x40300d419200070f407512404c4810312880b02083c0d0090442a0715580d10303110026220a6100101e17a104e20031601880420001040524041c002400300f0601800800d080704140f40861411a8060001d5200151040b410801040840d500c82c001a10390501004035024900445045a80e50ba00c00042c5094194550710300300d5545404036000ba00540701554126482246044e2220381e14075803c034042400e00b81c5c40003182c0109400e40d15a6040b039402002e583c000900195010307444040158204000c48980020f0032005001d003502a91094040080e00e443c28100554040d03500c00c5068800d4008100c2003249644450580303030041c81c110768665803010b80b80c0c0c0b4986450080c0d800207109010300c10700080c4144803644a00d495020f0150f050005142410811034440000a00140050214000001014400c40301495418460400020351480d0314002604582003507010808600b000402c00041103541310b800b600400003400c0c1508100101d5551603111a0001c0e00c18000c075581c1c803448140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 308466987 1250 308465737 308465743
    0x3050402120109030801080105090a02012003070c080a050c03030c0a06021803060f041217072f0c13060303080c03070210090308090616020715030204031205090312070203060a020c 79
    0x1801048020403d400b010314014149080911402d0255484c01c000a0114140032a98a1486605039121904041c8641e12603c901c444004a4101031105022500001d41e80500b01c030050f06115001701f40c0d0314028540740d442d10710810303001d0b030080d0820302040010702d40005501142c50350041015803140d520604000c00082c180c4009640752003002c0030b01a03040e004424490049004a18203064030b00801c10603100c5202d008224407407a054a00001c1d1240d00c1041d0484040160342c1414801c500c0120b010b00703806202c0d5002005a07006040500c1c654604101201c8850150f503400380b01d4545180c5000d41000d000030189030130b030240000000c044c1c0b81b080c130500614060a040030092840305040007411400d049502d805148510808a41240038451801c9036a6080c1c0c0c0c001c026440c140b00d45a0408400800c100b014160288004800521509000f041707642c150394800d61a046420304151130000300e60030302071601c4070800c032410150310042a22a4000c02101015948850f104a1035213 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 308468237 1250 308466987 308467009
    0x90f0f051317070201080a1a031f2426060703020414010e1f0c080408010509070b16021516060f050106020c010e190503070f06080c071203050402 64
    0x1a151600d0200040ea2060400300c4290502401d1112184080115010440d00c25401d02a001c1814a0002042c00d02e40350001c20080c00200c03545550312090b00c01082c1380c0aa04003c0c015016138482c08208025030b40e10601e400c0b401c1120004903100e5002c1d07400c1c05d00002e180102c200301b491050113603400000000c0010700c10401c000440d080c51800040087c000c1d00107000d2201c2120244410360410362080d086100602c0d030081504040d04a4851803190398100000d0b1101800452402400440c411402400c018510140046039500c5d02d403160f20300380740e4184c000c0c0c40340550902851605031780c48080140e4030755041d566044001101c1e101000240521080a0801807a0410f00410004aa04080003401d140101445240d88641d4240c0c0c0300c01c0442e00f882d00141300e143e2610160300c0c10b54550103103e9150482da035102c44d1a180401e0070420036821101c80901d09074010028180d00c803c065500501d621540c0b8105006540e400c841c090071008030904154981011600b03550358412484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 308469487 1250 308468237 308468261
    0x90c1c0221060103020a120201050a0305041e14010e0115060804030219050a0b01080102090f040209040e0a0b04110a0617100816051305011202060715020d1a1504090f 73
    0x402004103280c07259540400d0008a00404d024400000c0000110b44844006a07058541030705051310008200d005280007071042d0b40400c0d00c45803410254900c1c12100c4c02aa01910000c5204400b050500d4291002400d0780111603241a1061014415416110303040d0b54a5241415071511a814100d10781034412032614403c504090100c0c0400400041c0407840c13500c80c0d4029a603a0b030381c80c1c0c0040d080707001301c800141c0c00c001c1c0a0746110030f91501e030b402031841c02c800410024040f40007031701c41803410440c40c40031501c1e2220f0800b40300905c0031310402c4540e070400440c2c01c031010310f052840040c05000364620040c0800b400303101003804001d050000c1000741c06145e08840c2c1d50110704c00e1948100256204080c0100a030001c0010b4101181c05054165903400404e1407408015500b4031206900107213041e80c1800100404e4402c8003150f00040604940c3d081004c100b81482444042403001c2c0421300c0c504c02c1c01e0189000c1c505102c0d007401c0d1400c44020500c001000303007040d8107c4001d4500900c0071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 308470737 1250 308469487 308469529
    0x2010609050f0610091406071e08070c1a07020904260418020c0c0613030f0501020d0b01030203060117060d0803041419080f030c0f0703080609090c1c02 67
    0x400801c1d02285540f040004554003100641d140c1c000b511003040e00e0190054040c0340d82007681290504000908190f44182050300c0d0070000107000400c1070111120071148000001241400c0c0855160880c0c0548100d4031404040d031301c00740031182248102400240030f218150002024403d807030520400c0300800c28078a00c0d202029410b00c0c00e041c1c1c42402016181c11810001c4030300360581c3d00c29100d00101c00e00042c2400070001c800c0200d281c1084120f01e000c1d07240301070040b0003c0d00103109064405d20620000d40c444c02c0c040d252009652190040c8e504052040c4100800c0b6a80100201854803122001c03543c662242e80105150010080c0050107a6400006000c10446841e104010a200e0070003039945010f00807282180784030f01640050110700003441ba41003030210300c10045810040a490082c45c10b51482c6000c3c000f0340000300d055010501041c06c1000c2410220107940c0e03c400c4800151080180682c0010f85c100311440c2d40381c1c003800c001c5108204546588440c1d10400c1c82550301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 308471987 1250 308470737 308470741
    0x2712120c04030206183a06110406090602240a090602040506220503070b0307081005040905210306150d150e070f031103010512010908030c0403060e06100b07030201060905 75
    0x480001c0e40b51360001d1740c000c00740e0b0381182100203d4080c005a01c260040c58100004d180c900482c18004c1c403e0f001a10304903642d03005090154081c80007480100160b40384c42010303520b04500031b410050341024880c0240008004040054022418550b10a800240001c1c0c081054100f03000203000d6034000581149001a408070751254080c14154254180000c0200a50710f0700249511a4024815020008030138004113103058061420154401c2030b00d040f10b012541c1d600c001030305592030200c0603192078200d1405002d0318040c0211404411011245c45459824440c012986100d0405062540e0440c042400c8000142c00d40204120242c09070711551000d0b126a85041d101000707640c0000851040880c0d0403410340280958404501400f1500b030541c0c1c688014003d4241410081519039542c50031004001136840000d54040e40403c40750310303251070840c6001d10450300304c0a007030003441d4030410030170a580402c0d034200400e50b9841a00107880740e1880c90706038003400c07068000751000380c10601 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 308473237 1250 308471987 308472007
    0x720070906030b09070e131b170606190909050a06060801150e2203020c10030c0f03111e0d020a030b040c030207030f080705122712120c04030206 64
    0x40400d490144403c010b480e103070030350402d0b541d241130305c100c00c25800d2140000f410045801d00303150341c46004110301c2039400c003031141021207041c1781d400090910400900901c1840c0d000c200103984201c0641d5050000c0401e0501b02c20f103900c02e40300b03c099250b00d400e040350400a05000514046a11070b80070b000603501d0f035001d240071706200000c070300741ca404501c00010681c020711141c0d030080314090001c0c0540055161030700400c00072084141c2c03c3d441074080c000c0c85522460551442c18605590001d074001d403503903004000c0342e10084628105401c208460740e101e9440004c03103420705401003142d03020500c4210454003a024191940284620200e9400c40a54041c3c001d105501c0045038200842d0303000100c00d0b400c070700038041e02900280e100840700c2c201c1d0f4001c0e40c40640160700da007013440c20611955100580c4020440b00254800b18a921003010285007070300142400340d044019180c85882e03802e00c5541c601071816000100e0500d4008030310140520400c440c043c5801402c000d80d520380d070308 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 308474487 1250 308473237 308473241
    0x801020f071703010308120a020c1501080705061c0216080c010c02060a02070f020907020309030d0c1101030203011d0c07142a01020706030b0301021207021509011407200709 76
    0x700050710707146412031248261110701011641a02d40c40b803891410070740b40010b15000350130001c103281101582080807552050041211607040c80f80400c96402542c10b00b00b0301403c0004030740c81640606000d0040915070700d032124102c20801c0030110300507100c407490386040030040e02040d006055000001030040031901c0640000892003165001c4800f50780310010560120f01c20100044c080c0f140d04a41d00d401071820070001c41e0008e080f481168104204040080c1c1025000c64195010a100f00201820414006070059800100b401c2c1141550b01d4100b134140b1010300c3c042c1d6900e00c0f03c1c4010016520f0041001500c1059030002a018fc0ca140601d0707010303980d2204000091007a00d0000c000000780c010ba1410080085010f0b4098664030b0714048040c0c000e03112084096074555002d001c0c40b4800c5c00c1d1041094800d01e8164018440c00300e601d00039480011014100c81500d9040c04164405c80d991501c0490b0006202c0c03804158400084800850501e8013040400d40f501840b200040c14802e96 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 308475737 1250 308474487 308474497
    0x150c1f060f061d0307120308060a1a0a080105042c030c01020307210606050d0b13090506040311160b070204020705120a0306060806090408090a0e040b15010e0a030b100801020f 77
    0x510683d200354401c2c042050b0366170f140c46c481d440300003034107103080c1c3e001a100312850b84c0c010101520310700200c1e0300d070325031400910240c1c3c0f609004404041202900285c3c48013055005001c15641000b0344070840303c0b010320380d42c1103880caa40c02000a5000340c42c841e00810031503000c54041030086460b400e24170b600034100d02003103801120b003543c02c4071780060704040c41c0f203070b101204e4a5031546031900508000e568041c0011404066002e10800010f03c000d900342c3c00344d0090207200d24003801440c50145400780101c0c060000c1c4400e00d030703c031201c1c200038144600407401c02e5030b040181d800c2d01c1d80303c1c51000501074421000700520900443e8201c0c4001100c1d2000b600304841152801d1002c5501c0c0d141c201d6000b0030846015500806c0c5601080101e02c4603002028801005050807040c42c0c0c803040c940140709410344048036117001d040e04001d075501a8001e2060f0a80c002d1034001c01c40030110b4001201d0100300d00000d08a0248a000300e040e00b41c15600310002445000000d41d120801c1c060200c05503008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 308476987 1250 308475737 308475767
    0x1605030d021801091d0f060307090905010c022109010804021201022205060c03030604050c0403050303010605040e0a0903080f2a03040213020306010c060f1118150c1f060f06 76
    0x7a24008074040c0071004440c0f020550050b17618000b50b66090495407003030b4002d04040e415000343e6a0119400319180650136440c0d0003580041070600f201d000082ca03041448400070040e48245c2075400448284d5002c6a6240f0000d01e03016a80741c442d400007601d403c0b2a090184429840001c510310801c1d400760120005a0300781d00f004421903a03800600c440351041480ba21026001000098480c1c40c0c517230300840d0400044800ca5040075100e41d50305c0d2440e8000e81192000c10300203d400c01070308525401c440e50011280c4001c0c06040700f03c1d50050010305c005040c4062180300580040c110804001c4020300f02c803828490010b0b0244509608680d550040c2c89c241d005d000002d00800328120350b40201e0780518010f940b42c1207006161348405c40101020b03d1480610394858507c202c2007504500039081404403280340003203044121040103005039090003240d107956801d100050f408580443e12007070001012281000f01c60110694030018006904a03d0740d10900100106440d58071091403945104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 308478237 1250 308476987 308476997
    0x509210a0c090e030904091121010e01060609090207020f090717090d02060103080304050307080d0b030f071505070203011104030501090201080a0e070515091e1905061605030d021801 80
    0x916400d402090f40c0b9650902c214580c0200041411804c1ca40e110f00c05803809840b000040012140025107144110150303001c1023130700d424401421010a104085003202e07070030020803020b450b011001e81012035900c5202c0a86a01003141d0701503455060624002800c001c2010b001c40c9004400500407100f4200541c1c0040d1080c4001500441e0003d200c042d41c501c41d40003801c040c0c0c61661101e070507a200400464644c00f0502c402c0e8001042c010140600901c44040030a1100084040c90315140c602e009a0031994800d003020414070078015265041d1440340e01d08955a0611070002c6030151921845030016184000750000c02e1040650000c0c1e20540300f40d0707901e445901e510f0b0781c15050710090069004250802d03607080200b480c081c64000b008114001d0114103204c4204001040c42d101c522001050050002d800c40081c60310311034840c0203640c0e945501d1051814400801c10740c0c025403800701d85690f640158007042c06420010340c3c28144903040155076825500020100034050002d003180070807 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 308479487 1250 308478237 308478239
    0x201060501090806010b0c0a060e0618030315010513030b011202181014011e02060a06060203040e0415021c020c01060506090d0f11030a0516050a050a060509210a0c 72
    0x98801c280700c42c2140d4148000f0901a400c0c142d44469a51140140307800c64443e102c00c10340024500d001d0b6801120401010748807506c1d110341d80e0b050001303020758481055001082000310b803061309050046490028039205460b19843ca620804084064101525501084000040c042410941100028800e44203d0003042080d06200800d04054500c0396030009240410700140150718801c2601c1c0e0380500d8480c00001504004941d80340f051803407540180c02c800308008002d221401420002e050134401145814a05032148108400c040c100038201520000401001000c6405480d030010140314480d0407000e07030944500003940151807540c81542400e074005140e103007071409d42b02201005031980030107200c15950080e003072503950400c80c1d1070800b400070fa0000341c0302004083ca03403070b00c90700003444480f503400e850340404c81095014034400c00760514142711545801d20b0407000c0700c42500b806034540e001d020000c1d00900720014020303d2500b01107904000090001940c3d0110381c012070480c0321007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 308480737 1250 308479487 308479489
    0x1c0b010501142a070807180f020a050d0f02040e0a140702071d0c040305060702030c070f211403030108010207020910030519060b061801120501050915010c0515040b070804020d06050c130f0602010605 87
    0x64080c02c0c82b04408610240441002884160022640d68006005c010b1510ba00c07520148008207056030070103074240e522400d0801c5280007a00168014099000411080345010783c9400c600c6400c900104c2c041c080070300800c451026000540c4e014590003000e031485441c205500030764071703004010885520311403400d00140c03204040168505030340d0250061128020380c04c1c1c4040700c014502104480b0148000070109142c0b60034070103103000c1c000340400549c1d146050300400c0ba20503009411825010b003441d41c00c000003503002071a0100c4a520b031035060038460490804a00a009645146400c044005024903507007003c02d02d08000d0110981701e0600d1003100600c00400c480c0e00340280e60b040a08480410362500740188100031003c01454491250240c9581c0c1604040740e00c1c8a14000c450390509200412901c6044d0036440506480d141080d80340c41d4000640317043c50044050009943c50300450900e403404c20445c0c0c0420594040b04810355910341008144140d00d203d40c40c019440d045000c681 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 308481987 1250 308480737 308480741
    0x61d10080d0c02061c150e061f09030506040305040306111614030c15010306050f15100309140f060c090607020f1c0b010501142a070807180f 62
    0xe5a2150004044100360160155034819480200342e0703018400f400001d020041c1400800340d2a00740e00000304030014515084100003119802045140d03487c86d0801c01551201c0d10203411480b110b03074650019500540c03090314084503d0f04040c00724044c1e0710400040c190004001e10032248103100c20011a03100200044a0780240c0e40c100e110080e14840c514040b86041918640000b000310070380380790201c4400b0b080d1400601d040e5070701c4202d420340010800d10900d44a244e5114240243d0700d4070629050b000180c484072240c840c0d40c81410803e000034461741c801c1e0700c034240705640b04509005494030078002c103075608034040c1c00d08124850840050420f600c92401c0c1c50b600300300a42400d0500c100750382003082284080d6a07294001e0300385041020894070354100e071443e150081c140b0407415410080010800700b200c5284042c500b0082100d0806450442103903018400304800c07101005044070300440c18450150302c045804e00c199070001c80d0320b25040c002c4c2005200f80100030860b5420400c19441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 308483237 1250 308481987 308481989
    0x6060603040f0b1906080601051206070906080a0906020406050d0c1b030521010f1a090a091e0203070302040e0f04030207030b0c0c0316020301140910110c01061d10 72
    0x40700041c078040c02c001401d90400c55000244d000840b0050840a0303030382412140d903580000c0080d8843c00c0104014180032122400000031030001d030203e40b5100f04060300d6603040b480342f80e04010180000412020583c0c0c4a00c103500e81c040c1c8103541c6c65a8443c8020030580200140100c0a89031240002c40a4050407020744c0c01240f0030711030b004621240d20b095810ba0801461000030321202601003a61342840e09c0c43c00c1c0601020b010b0f0400c3c2c0d0f8249010407140c00368100d600803c11800f006405090380d240100c52049449803080071501406105194152202100034190480d0012040c04400341d01071300908182c03251008074503000c1d518040c2401545900f550083e0158218580900c0407030117103010703181c4c0a40f10840541c502004140b0607481c5921071000d0320301d28a5081000f504516080c00307050705203494131200058608003001d02648521040c40b50400c00355480002400b00d1416505486140442038020014140d4403004803018800038540c01110001d9880051800481208600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 308484487 1250 308483237 308483243
    0x30e03030403060c260c07110a06020a05060f0105030304030f08120703020421080712090b03040c15030b03120a021e010605100807020a060b060d020a020706030f060b070b060d020a0b09030606060304 87
    0x9905c540f1014540d1659601c02101601c283d01d400c0c0f0410280e403141d41c8000d0090503958018070a8513401e0401c82d00309000500200740130440070004006a540010030b4600380e9401c8102140b00001c40c0c58071046611440e502000c80103824020480c0290f05a0301800490714410311941d014410004031040001420100070700110040c09071001148054550514400796030070856685903e480701246241c000700c0d400c40720b5400c900828031010503c80802420740340c0320f040c14405410b038a00040d03201c00540c031401c08445400714600400314400c111483c00c03004450f640400201c0c01e228883c0c040c190300d0145600038410341c021600328501c40c1d001248079402c43d5014004c52070f000c0da5030748060452103101607030290301880391141c100c04c140b0092942d1220768009200311882c1c2940502607d000031401201c1e01c1c80c0041c01c02200c82008205d40300c00b64000e11a04140c0d0702c44000a040c80c1140718042c0d0000c030a11000b1620003001c80040220140850844d101a600d840410803d80f10032a001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 308485737 1250 308484487 308484557
    0x1909062406030e0a140c060304060b0109050a0e1b1c0603020901080607050301030813030b0a0f0c0e0105040603021b01020403150506270612010c030c09080a030e01050304030e03030403060c 83
    0x5136000c614242c1d01840081e2140058444c61041300e40002c8450700244d4060702c80a40d079110040c2d80e0340c0c002c41c18100425040c3d0350650750303134980691031341c0303465005181d41e03410b10b1b01b8103606220150403011508660180c001640111000480d000c0c02002940001c07800f0341294400800d9201c40018807c2c03007015a41d5076646180e0855840c1015034001d11305031401020b080d440440055041c02c0301354490050040001081d409038410901a129440f40401c20b000c1d042e075042d000c03a40c3c45170885098801d04d05000d44d0b61503813015107849460440032002455440484c01004201c1c07894286c468242320100144015190340d4200300b0911105820203401d540e005588007035001341d00403060b90100009048100d070f00340350381e2381900f940c038180d290f00c0009582d0801a600c0b150004001c0c1c025000410090a0b00c0c2c4180d51301034540401140c80078140305010001030209445000400d0440c100942070307070f40310baa032868810003501181c0c03261070214942c01c1c0150000482d50b075000300c003000700c0701031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 308486987 1250 308485737 308485753
    0x60a060e01120f020607081206012c0a0506031003121e030c0201090209040b0603101a01030b21070e07020c0a05040f020f040b0301060f02070e1909062406030e 70
    0x30312500b4564030442240c0502c450b0510380d015035180c50203003c0d418041d110041c1e803402918904c9000c640700400c114180324001d621442c001c1c40a900100d8004c00d440c0c4140d200c2d40340c00002901030015a88015030243c1c00004000030700311405120800c0724450510103060b82c0000d00162040d000b00d80c1d60360303c0f2210203098018003e11a40040b103d08a00d4000002d0b80200341d0082007040301c04440c19079090450300c0c180074060404004c0058840c0c1462000c010b00d010401e0103210b21151100014101900c1300340c070252659a4803651149008079034038a203c07905040403a1901d6010b01e21440143c4010680001c2c1124000704100040140040c0301c690308c0380c10b0500304002004200104030586500b80509458421074200802c060602c42035842c2d1070b5898640014600c5401e01101411034011640802c4032181c100103441d00b21481034100300c44c0c8106c0c414020010300400d5405050030b0305290f068100c000c080c03500c1041c02084a880c2200e0306855040076001c1d10200180c1c044c256010310380d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 308488237 1250 308486987 308486999
    0x2160b0a03050a0b03030a02280f06150512010623060a030e01110a0c020a32030a0c090b0f01090b0405010804050106030f080301090f09080a1214150102060a060e01 72
    0x301095010f900c5000001d5413a05030740129195030070010602d400f580c040c0200c0c0c942006a0b503141c00c0f0391030020303402e4401142079603908000d200d10382d10024091b648500d480c000403000f082c14140a810040c246401081803258914007810061107034401d0240d15944d024103041d0b0001e0002010400940060700c1c10b0002c0604400405410046020355542c80304100740c600c1e88c4100521030703011195a80600c4900c103004104410041e80e00c9005040c92070048400d1010b840010214841203c0308031701001c07030402000c03d042c140f01c1000140030b400d00c144023113a559844d80c0240d19002c03080e00c8180d040405c0b480155403514a0380607151462205000810580d031107448041e070b0040c458070000c544240c2d603944100e0b003015000c8046072108404001842056030034850400300710002d403400d100715001612010610b04c9a00000401c10010300401c01044403d5080100b40c114844015256460081c940300b02d6000300c0c0e8441801805080049404040c25014140c00e85542e02d543d081581d113051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 308489487 1250 308488237 308488241
    0x1e0605030c010e0d02180c1305040902030c0d1502030a06031208090601090e0a0524070e0915010e0d2604050f01180e0a09020f030d0e1203120a02090102160b0a03 71
    0xf03001c99000104080b00c4103406c90700a240c40c02602103c0c0c10b2501c6e40d00300500d2503801403407500014016840c0010002c003503540042c04c0340e0300403415146082031213400d0800301038100160340580d0aa500000c1400030b64185c83c0e000101300c034000d501c030172080185240c2c1258484416121402a94010383c0144250445507004060800c1a14100e07500101140d0784ca60030007142911221a0030400c20210100240380c0040f1513221a5604d0020f6444240f1000a84c1c1008054010b40c800360302d07020040303c141d00810700c80d501300301d000b4440c0c20200010300e001c1000d0051020340040c0388040d81c2c3c03c107444684100c00d581c19614010078081446c0340e24001103450300782004410000c26440c110000e01d1060941d4000d000b015100000f060304500d03070050060407900f0f20000d81c082d43c0900755015034540d00002c000c1d25520202c0d0090303025040d000e0070701e16500035a440302c0c1141c00e844040c0541c11419034020702c40c002c420f07002e48121500f444000040340c60f4611404522000402400c2c102611035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 308490737 1250 308489487 308489509
    0x70213111b01022206051c18050606040606030b030307060209011412040c1d0f1801291c0803090a0b040b04170c0307110f041e0605030c010e 62
    0x95840c0d40d090004500000c0c1c03040001110294042e540068014241d40c8444240000c404200224100940c90048010710b00e108504028030061054000c040c0c41e940c0d260061103003078122090310000c04403241451a00c1e02016207800703100314508180092403c0c040d000714901240c005001d107007071881c10345072038010798801001d840c100134180c010100c40468500182101c0c61121360986842e02d1f1500c4d15981d41012900a940407e071a07520480b02c9104034042e440d40a01150402101c0e500c0e90070802041c0300700700d0101c84075542001999425410744c010000c10304078020481034188040141440401420030074402d01c1080d0011507107000c200c00e000110f0b0800103240464022041c0e03520303413444803c01a10704447c03104104050105101551001c6444600310b113021070324084120b5002a902d00c26800001c101e0714a80c6400c001982d2110100070103040064030500c100c00070b91070710003071a1400110b0810350a01d041c00200b160700b00001c0610844034103031036039400c400d03c41007008005862 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 308491987 1250 308490737 308490761
    0x203011805010510140f090c12010b12090102190f120c0201020903072102100c0c030b0117060106020c0f0d14030310060c150509030c01060608060310050906010501050a12020a021b06070213 83
    0x8106076003035103092200c01030091120398010cd0700c0389258080c058200101800c0c0303403500c3c0e0040c00550041b0100e45c2903401c007050a420b0076500960203c1d410740f43d500d00c00340c640780003510f800c0411040b190190010081100101c05036200c031074403090308004d0001000c28545001c941030300035038010308108044910b1702c9041d090103c1804046e82c0c41341002012a00110380c20f1558100400c02d03c80445144201d52000340c0282082c0c0d0704058000395107018108089208100401c84003810791902c000c502c844940059078040712607140f0090507540d40c07060326000c01b4541d46100000d03c440c407802d85030451039440513205a10300c0b2503100c10005044d002d494400345001c2005414400d90003403185400421160f1606140703803400208050610803030281c60710915040404002c1d0240d4041869419030f2401d080441d1a000240e404442c40106140341c560341d90310010f66080b050b0f03000940c2e0154449081a0150312007014000c2c0201c5010310b01c002508031400007484003205000e41c00c2010311010b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 308493237 1250 308491987 308492011
    0xd110f01170a0c051306030204030c09020c1f021b07140105070b0a050a0e0a1a090123090a050604210e0105030403113906090117040203011805010510140f09 69
    0x1040442c0117400495610030800300c0d500003010410484060100c00c02404074010440c1000a003900c40f03a00e0b101403902c0554000c0c19800d81c841d032020a5410f9814400c103a0404011054003201d64541c1e0b44a980182c1d10652000303080305c81c09621400803942e4480e4040320f140f94903100d01c1040c6020b0040074003d10b400340d840c2c40003009075400030000b48030258040c0e12401200d00907100c0d85040040c01030490700d003507410004c40000c0c1414052045030520b01c0f0f00315000b59a40c0741d5030320300d040c2400a000140240156814002070005004208192055400141880324004102a1090204054910b01182052000601190141040000000e8003205641621080c12802280c1070007200c2500342180c50340112255090780350441070b9078102c041d99854034140c0c003480040c140e1240c035042040c1e1015440300040441d1421740080c80720040c1c031a403c448014243c907245028150444451a4680c1850000210030359a9413403a4a81400a0302d100e07401c8007501c050142d440c0d00100800407100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 308494487 1250 308493237 308493247
    0x6091a0717060402090102030405010507020d080304050d02060708070917010f0c02010f0f0e061b07021302031f030b0c2a030a02071d130201020c0d110f01170a0c05 72
    0x10001591a105089940e14003207a005512101c42182201521950065106002c81c402998000007118180c0c1c3c02401d220740c41e07011610000d100ca06842000400003540801440100500054581d4400844e44c0960315640e0740d445080300e07000c0d012248040090459602003142640040c90f80989240c003d00126040360040400070555481e10b4541c00113030340d105501c14001d101c521400c52040b100c0c240c2403007484d0200c0103040d0b6a07003001e400020703001c45008821031115a21001c54001c940d020f07094a070890003083c540c0c402904200c60001344540b503140303089000540046010240c03a800280008561070300e03003e0214503040324070b07a50702c0c619940107480c01380390042c0445040803140a008560b6860340d0703c0002e084c003102d41c0c030034040d8010300b40c005100b4482c480f45069000b0b81482c0881d011a4032400100d241c00141d844941d0010003151030042071001481c14040300200540e10b09062102c0440112036001d0304510751402e42c603140010907000ea4041c3c010075100001850036038105 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 308495737 1250 308494487 308494523
    0xc05010e071401020d020a0534030606090e01231003020301090c0f0e01230607240c020c03120309010b060313030201060609140f0102030d090f1401180609 68
    0x100981c10081c0d11076512010b1075010341c0e0411584024080740e1018265a001c4d955500303a90306420b4070140110b1403040d1981c2001440700314091401d55081c1c0c4400c5120760390782840c0300180840e0248c64000c50030f050b140d0440303960500174400c403c0f9171152940d40d00009840704c0340c3d9210000d0142c500c800701c954000000f40e9000d0084000b190702a59000808600d00780c00082c250720035901c0000c00050540040006901d88071510403c10122100706404403420400178441d4071400d0303802042c07a014031403d440309207800b40519101070b8034007800700a4906038000980e6145a1102c410780d040c1d00c0000c0c615032601c8003202454121000c8000400c80509800001d14190803c032850030882c07c120306818140356090082200809030340c146606410f09143c400d0f461741c01c0030400079025112684001065910030030440f1481b1340318060130031042400340740c094031007614a0b100fa240c1c5e110919000c8405481031240c6090300129034402098900c4594482e0045c0c592200c058810007401400c4a01c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 308496987 1250 308495737 308495743
    0xf0201032301170f06150102101d070e16141603020d02061b03010905190c090602010f1416050702062115030d20030f04030c060c0c0302010c05010e 65
    0x400c490345441036042015140c50f105140ca210102c540c0b04140d80440002c000c54040d800c0401c01240450b442c1c4181d00503440e0401c082013400c8035030710f0700790450200c10ba0305484004010040d02642c5015540b4000000c0507201945c1c3d1051804640c0c0c40c5061983c00f511419045461009015050030342c500d59000014400c2282500540c001d0340ca2245c4d440d90500c02d040c0d02450b0b408454140043c4000c005907540014001d500d45150307528007189c00e01c0c0450f1a007203158080d6800500440240780310080c0740711384501c40d6001543c2000025000c0e03150301e00441d0320358450000803100583d204540c0744c10107010310a6070030038071200b080142d0160702c809006110b4a03071204011560007120311766186400c0c10003484411480c0b000c1442d0401c9540201d0822420245440d040080c0209059a1001100084080643d40c400001d01080924042014004613030103600c0d442d05a075030b03801d41541c0c00740050000400300d4450301011300040d0300881900034001c0c014000003424425101ca9685 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 308498237 1250 308496987 308497031
    0xb0d0b0d050d0216080105010e0f15190801060608090a02010c02150f1b0102030906240a121b0614181e0a050303130e070e060708041a0708070f020103 66
    0x44e0041110b40d44d000309002c200700000d10801000b04101d615100d20504945409031508070a030300b482c004a903e501c0090b2011844140080a07030f0000f0b040020007c103407001522621056500b004e400044e06400340241510030307416400507201d20707004c40d401101c00100d0804120382c0020f514105038a40c122140252403504605080555030b048040c000c1c2d030502c1c2c0b5603800c109043c2e00403c100b09175580e0100340c203504040d440e40910002e00c40e0105100c20f0100c914038154201100240c005801c144500704500b03047d01030303692429640000ca40d11802102280181c03000305240a088440c0143d40400801c40c0024401d904110030b4000000038010f4a0324508405101c41030b41c4203080140b800c10600340050404400851900c10b41903a0340030f06006500c0741c892003840600000d24a1401851045588000100311685d0340e241f614103c0032542050017000f44000035000204c80c2445408204d4800f43d03007180c0306030700b05243c6c1e581d03e00c1e0f41d40c90980201c2c101901c4482e4a000c10a089102103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 308499487 1250 308498237 308498263
    0x240c030f0a030b01120203042301020903030a020102030a0606260702030d0204170610050a0b0f0705010903020303070207050a0e010e191d1006051008090a0b070e09100b0d0b0d05 78
    0x403030b401102c3e000042c420301d400011110042d10400612000688410b00d14680f000150292926044400341d003d0080c0640340b6215054000028400f103181d0b41940118800c0e4400c8904000050701d4100868000f03000d0b1002c0803410361105064401c950700d8060440e4000d805104a034a0f10542d0343c107610a0740c00590100c1c1e03a4400341c03000d42050500901140e1b600404c0c0a51100c05079150000140340740d00d0512415464020005070340c2c640c3d18820342182c0985402000a00444100d49802941c03603000700c0322500180121480454246055900d090480788444140911079003040004103021b42c01030160350070841610900301010a03940a0003000341040407120345e2042030020170741c6c240442c0c10036008100d45001400d002d80d5494503460a83c4c0c0030350b40303091826541c03a03095961915080080242c0048104000c1080456004c004d5640c4000155034032900c0340c580000d044410304d1075014400702c1e20801d00003030f410341c5101e5212124110780103000c3d0341c560080d500d416080076101004a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 308500737 1250 308499487 308499491
    0x301050d1518061a0f13060317030f0a05070f03020c011506030e010e07080a03030c140c1006050108060a06270305030912031312020a03021c060b240c030f0a03 70
    0x30b00c2405114800c88a00c1e0384000c41103400c8090440018650350840001300d84103400750000d9a4105d4501d900203009954000f03040740c140f8400d418001c0b040c2e041203503001d02d1010307440c0000e045001503000b498083e041c103844138410450304820690182d001358038101c038030b5940c83c01c03200307084100800f41000070302d00741d240054665401030b0214203480d09465001307559071000074200040711b030024100e034015425140010b000c98002c00219490301d05840000c1d1440307000304214180704004209109402040740081040b20f030384400665039403204581c060342c0031220039410030516009035520361103410a0074511620602c68000ca0700f4000c02d80e042554164000316000c1410b08001400f04c4640e401c1400940c102214900b1940d0100c6140c01042200920340e2100c2c3c0031500e0700b01221015550040540c28901c0f5080840c04515001406c00d480311402c0180809903800c26800c444042c003c0020b281c2124400c410811030580d1101540c21a1032100f0482c0b211041c00a101a202c450307515900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 308501987 1250 308500737 308500781
    0xa020708070f2f0108040204050a060806041212060b0711061c020c060105060702030703060c030f0f0b03060c181e0607211701090504060b041823030301050d15 70
    0x2081411951403400301c0300f45000c4200d007003140e80040710a540507604940104150b03458004560150150b54003000e03261140c0c00c284020030445d4541600a120746030788083c04014004091300c284c0d10581b04082c0d004804204440c003040100e00444070000f409404280b03442080c0c020303080203c0502d1003245030309902203404c0801c50001d001c00c500420f0100ca4035401c1135020f400098032075005100007008075941d052281710307440c060b81000416030350410040140184031003101d4003820818000b5032090145034001010000b890040c1d8a401e40503403440540d414925003400031902c02c4200e0080c0d01000c9080c2601e04c0e86e104030080a00c030f0301c14105000405d4401c0320112601340420115014040844d4446101011030300314141100c4c26410089481d448a0030420020010784044039007260500801004440c081041440341d41e101d00b030002003d40d031101c8038190b074101c00003100156400c104010040ca00c1c00041c0c1d401494000c0405100c2802135104600c1210080a01e0000701404004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 308503237 1250 308501987 308502023
    0x702011e120b040525030e070603050108060a063b010801020703081806040f020f03060106020105010524180a0803071511032a0d0608100b060c060a020708070f 70
    0x60710b0754003241a1001d000c0e40c14400302c5807103402c0f41e406140d0b040740c0c86810165501c910076000300c980c107812030003910406034403071400401a007424043c80c18588540c0d00440c981021901c1083c0403187c05550348602c145029000c0035404408560351800f11880000300c140b035000d080d01d4540204425800140d0300d032f05601c1c000d800000024010684c00d10340d007410344400d00000c00c1440e80254004440300031a04103200043d1103083c5000e91580520030309001066840e0154030180c1a80d10481e584a03078a0340da2415444000b90020581c491030a0620070306400980034810548031490003062a00c003541c5070b2030510b14541100c40d0a85040b40003028550044000e4420802190010500c241c514903010300f5410600f000c4200ca0008900700141c0900b0f100c1e42c10081d510383c01d85446c8184007080e561144a0350303402c0100c85502c04940382c1900c0e0b00c91032500301c00b22514500000060013550ba030f140071040082d00030000030348218001b0480c14000a0602c01034110f094420b0455070031002d4200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 308504487 1250 308503237 308503241
    0x70f05010e0d03050301090914030c07050307050f0612062b030305070512180c19170a05070909060b12031c11070b060a030204060803190f05030c0702011e12 69
    0xd0703880c0142c0c1400020340210790300c041140c1c1515070715900464294442c1c60040d51608901e085100f140c000810450122000859080101d0f4821011100b0f05070300d074010400c540d0b600d0002c190384400104000c0d0344140b00000d2445d071044005201803001c2c00110302030303205410b03580c02c1c1d0124000d24400610815815104194110724207107807803400c5c07540846441410183c098808043c4552500d1300e800042001c011805013050003802c07650590840d4414064054210b001307280c0001c1d8451110601c290000540350803860b0408002c000399450903061200a00800340300342c44503a25840341c3c1c030140e140d5042204240e900c1c40003c5a40e500100000141d411422000b1070100341041c03028030041c0c03c03010a542a440d013002440c901c545809001030011001584001c1d002402c02e2800128440040050f052049201c04640c82d010141503003102c1c001c1c203909000001c52018000f1480c0408000003501007940b043c1401c548144802da44c00c039100f40801d00010014070034a4074044508503034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 308505737 1250 308504487 308504507
    0x150a060807020d09051c020d170406030605061614030d0507050415030903020d0e06090a03050a15020403030c0807030c06062414040b031f0305030d0b09060112020f0408070f0501 78
    0x1d24044501c6810140043c8581c01c1011840d1b00d52107400310800255564403c07443c0150360300519130385804c2404101000d50350003a2040700f003c6440d100c0000f409051040840301214180c1201101505059031480f00c005a4507201d210075120601415108111910900d4051070305034480d5a121450407400094002c1c4042e0368004050600c610b10780060b40009054020500b0b80c10035202d4160b54a001c190b050140301030540d40580c9040001090200104010389564000c0402160900c24401610300340d22a6200080018941100e4140400c0c4054041c0110034481c0c581042c2d0111140c0350300d010740e020f42c0c000003113807121039901821510620384d00b00001401424405501041c074000225940141d04c5850304039503000000070070000d0f0480c81e27220440d43c90031140d001c040c1c40e800c145940703800400c0400f08035458486100c800c0c1c6000041c041c42803805940b0070710810140354006000c0c0d0043d5134100f2031041e09000104541c038090140b0001303400c20400840c501441d04000400c80626 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 308506987 1250 308505737 308505763
    0x10b120c030d0e030c06070b090606120c040f0f0f0b010210060b09040b0f0310020315060711040902061e070203060a0c140a02070b070303050a0b0324150a06080702 72
    0x5520380c260580300403031001442480e03400d0501030180401c0100e424055030180f541c2d03208500140f0300301000702144da02030048044204450050341c41034107000e21415a0b042036070043d40008440c40c802e1901c1d400090b44103070000030125070920300c1c4c0e1851056400e8601004506525441e000c3c4540d40d042064502c46103c01009000c01c40c07401c5200c1d02e55204440c40d8500546d12640861503035280c042e205070441d4000740485000009000c4007200a40043e1001403c00703683c01124022454004203a42c0c1c4190011a4803c0120510b01000300411030003c04076084441404a018182000c4184c1c0700201c0d00f03550025911031240c03040504040d00103140e1013941e85042003681e046a030240c046a08040c8507102169a10911032050340f422070187c1c8014105600019964100355258004038003030b4490240600c9625041000c140d1142c8450801e1000f0240d0340008620010350b15100c150080034502081c5492001c91000c981200901d030002004503141405118025074100900038900c1c1d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 308508237 1250 308506987 308506993
    0x9060912080906060d020d0f0812011703040303050901050714031b010f020412080a12050a0b120106140d0f0602030c36010804050c030609100e070308040e13080c010b12 74
    0x5060000034a5045c0c0c44c60010340603145080d0914100103100c45641907040c5c0003d0766540b58036240c901f410502c9024060140b40d40030039207076200a104004240c4040d20b03490b8441380d052082c24401150340d504411001d03600c840c0d001445400c034002c14801085014900d14500c046c1c03010b41c154082c03e540002c0461420f00744104010001c10745000502c064107a80025516640c5420a20484000041c0740900d1342d075503d8081400714113206503000c603119440c00d40301128071902844206003219964810040c4c8100d226602d03902602c0c00e02158200244a601c96030244151b54a5600c1240c008946022154a000a141c04040d0a079484110740d05640321360030a41071fa0181c45902112032000a0505200014012404200051110103941000034044503031914090b00010f03039469282200020151402c058401c40d024045101820b694000d2011442c003842d015619540700c0c2c0007065400d00540c03485a40d000510418003d0560486400000c42d94a403401d0030440f2000042d1854100e542c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 308509487 1250 308508237 308508241
    0x3070e011b12200a06020702360a050f011802040308130e090f07050405180f070e0117061b1917071b110a0f0314060a020301080a0b040609060912080906 67
    0x503c0020705070080552018000da141c4100c1e1006c100310104c0b940c0c1c1400703070784109141848022403125228030694500d110100c4280c0318000f185080380c3c429141e00801d0210507005020050444280008a6800f20401880c00395039480b001142e42201c1c075a01802d401c2e40e00208607000850701800e401c4003100c400740980000100301503581e0401d5203e014080c2d43c91340006002110342510f92104450032005842c0440036043c0417580b01c95680c001e20a01e6840000042801e000305841d8904a01c0c440c4020504c0d5159501c11481c86000300a41391b000c1c88040080c003640d44c0754900529403401490321294903420183c4142c0c02200c000622500404c582031320301761300300c001502c09902c5042d00300c680d4640c69100d0a010a01c0c00c030264119080744c1c400014004100403800c1019001c016101066810944174010310f03500b40d110a125040043c0c3c420011100807400300c01c1110340203031041900240b00000c41d5604001d03a001c0d00000d54240f20000b28589215401c03a0707070258400c0003a40038046034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 308510737 1250 308509487 308509547
    0xf12100f0506070b070c060c030c02010f0e0d2016060912110409020420090a1e171f02090102010b0a2601020903030708030402150403020603070e011b12 67
    0x2d0b0090f00f07030181100a407100403840060280307514051094002c0010b1201000280c0060007400a40801030010b620701142c0d01c12803900c6204030400c688111025240c81036081c4000c03070b42c96032001c0105440c1d451058847c1c1c1098802c00030f403008031840202c002000b51800a01805100c1c10360b11040094550160500c0003d010213021003041c1000c6a000440240a0000c40c00401740590088941c44d09441401603410281010303007106141280c045403659243d08d046407204240351240c0d4240603640e481448020564501c6040200942040740d03030f01800381a0208a20070040c0c0072290702680003134209000e590a0285600c94101916462551480d007041540c040304004250700340080300440c1c480000c00d081d0100d41201200408503511100d075820920000c2d842680d0492041c0c004205040708141e1403019502100d8005040f1819541c8910081e503400040c644030314108144509104e01c95103c40081310b0710140240441c0c2c1c80314039402030181100c0456841c460601451091070041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 308511987 1250 308510737 308510749
    0x30a1a13080306010518151c020c03040546140f061806030f1602060405190f0813030c05060403021e220903020d08150f0102030f12100f05 61
    0x1000017840c1440d62020700000038625141340d41030490307200c0e1044140090720074092018051b11111200408055281c3c424200c04074403820517031010940040c4410800c0c0d04d45074544035500c426100444030f40200410302c5000f51402d4070151001e19036281c42281c4400052941c40c0060a0054050700d00c10400e100012100b99030000c4052040000180c170914655114140301070284c00600915240d0405041e40300715600c0440e8030080c1d008150078440c400c1c074400610540a01c0c0c02a02130000b01d2030054000c2c000506a010543c4e00e0844c1c803c0060000d40400300805400c0c00207201c40c80781a0462600081b400408e0307002c0c0748205800c1c00705201581c0c072032480c50880444010400d0300c10360440045071007621f8120f0b040c0e80350404800d0102217400a81c00c07914403e84280d00b03403144400441800e03941c01d00191504560f140c100450146141850210400307a840140100c03400d2226810550005034041a4402c181080c8001484141c01d5162200b201078a110070300d002e22035040c131011842d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 308513237 1250 308511987 308511991
    0x62d0c1d010c260c030408100207080a0e0a030209010308030a0506101709100e100c020114190e010507020109051e120d0603020d08210f190b030a1a130803 68
    0x21401000180c8a28050300f10f92401400d0403d40c015500d800319200c07000d46a411070721544a06004003480310031102900e2007201e056982c001c0c41c603800c041005400700c074950824500c49801c8240f105003c0050785c1d500074003e008501c00c03800d0700c1d80e9192610005003a180040e007940d000b038003501003a1003142e4100303000d041e03140d00c02411003001d69560b40046142c176003010141e4869629020340d410110304003041c080d41454044009011451018800301d080b1394492040b008201442d0021515510103242d03c44d40a008100011558120b01c0c80280e007103d509459590140c1e66a030713820810041c00f40a4034104d0412400f040444102d0004200c0d22a101c181c03080340b91000000340d85020482e9a4008400341d50041c2000005e043c4500c1d060341e59601400003210500840b610300c10349071030400d4200e4801c2b4507844440402c3c0d1100d0059400002c174550000b2080390300c0b2600001e00b5107081001000b00b60058664a04160403016150640100540264545c10190031900d010456a20807aa = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 308514487 1250 308513237 308513243
    0x53c0307060f03090f12020601060809030a0f0c0b190c030b06030f090a0f051e010207030c021002031210060306050303030903070f11042c0307050604062d0c1d010c 72
    0x20850150020100d0060240e500e00030585101060800f051029080403446d400103580c0855083d0707601c50000b035070941070844800c5040d500c2044403c03050782c460141100050240d00380349083c2c2c8401d60790044003100403074412081030002140d49904207104d00a03000449101d086c00c0202150b410082002c911005040ba02400e6203200411000c9204100c01c030300c41900a0b907512519052483d01c04d4485180e030081c0d030164109070360040c151260605c21140701a034540c640700f1002c21150f00340103080c1400080d1209600040c0b282043c80310231421305a12030104004010500e50801c5006003c40b02c094011318000c0d801401085519003001044800300740c0c00480100f03091220380b40603196980c403a400c05800c039051103c448200611009044541d40304054500b404095501c4103558030b0154050140869200001140100d07815030700501ca01000e008180600d4010030300c2c400140e12601000f40300066462001c0031003258007103180755220100001689400c04080002031644107049806 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 308515737 1250 308514487 308514497
    0x2090f06071a010617150319030e06040603090213050403080c031b2a0c150d0e010e100b041107060c11061f080a030f18053c030706 58
    0x844280315504120070103a60b0444841002c640e140c6400a00003003918100304074003290b000104e0b194103801110b02c0203a00300038009000c1950704801d4001e00202401b8240c0501a0781c8000c407011340c5078000200050481178901184204442c4140120070380700d00300e610b17613040c901028400001d90200740e00d50040201608140c90741c4824000071401c5241c10501110918001020303100b800b24401010400b0a98920444038144c8981c0e07a141c40d410728261866000701002540700c4000d840101402408440c0380000440048540456003150001280300d03215600078011140c800815019200b880b44099038140700e1410344404042c220b01490b2002485c0c1902e644a40b450310380700704030340255400e000701210600d04080309183c10100e001d10b13041c0b4403e104544d020600600010340303002044d5059480c845a0b4106c51001c81e031840c021200314a10707010420300040e050b590941c5a4100544080c00b506800c440008108403000004c2010b041c84408107000c121207982c0410351608840403802c107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 308516987 1250 308515737 308515747
    0x6090c0a0302210102030f0402130605010f0f0c020a0611060108010204060509090415050c0c120f09121515040c0c030c06050c0c01110301050906030601271e05040507050402090f06 79
    0xc1082141a40381c4043c00c90340c800300c02c121440b03c4200d481401103009a846040d03580c8009541e00682d4036502a082c08504051104c3c080d061281c1551142810703149015100c004483d4000341d03040ca00d50344200e0000b090800c10741104a000e0249a0042c032202c2c008500d041c0c40c142d005083d1f805940a07080c071588840d00000c0601414040380600c030410340008104d80c1c5020408951a908425041c0341d0f5840381815001160701c85500303c9000d0480c242031a8145420714040012a4603c3c404011080c003d4101e07000d403d210140c0b8880c042c00d90f0040706d10a00301a1401d000c105c4110485420800c64a242c54902103600400707020106500308401041580ea801c3d0101d106100342090345010b0342c600207803c1c14102078507020b14144c60046070841c0003615031400f0103684100030300542d40c01c9a94003d074001e8010840200c3c1400307210900300882e1010342620503200c10b60080003008021501e81042104200c414042c5402404d070458046082042843c08100750401142c041401150300181c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 308518237 1250 308516987 308517019
    0xa180b0601200303160f0201151211100203040617010e0f06040209030d05090a053a0b011205070e070e010c060f020313152d150f03030206090c0a0302 66
    0x2802c07405100c007908903a078074180340400601e81648407030104001030305400d11704c4000b803043c010300405000300d17101d146909042c034440e44860001c031001101c420419865034072440d2141d4000c50a02c0b1030fa40c0143d515030f490700348068100320010911001120240c401404400c0400c890240c0101100d038107801c00b9034505012070000e00c80c0c40020b80e41840340782c0d01109541d6000d001080021000e540f0341c620300d542e490900c414120b4101c003100c0604000700010700001c1c0154401c20203c410001c5500c400d61058540b40c010210a0300140b01030078042410109201d0208180c4000780081000303060503190603140100012140580e650402010741101c0051010380c1e0401c1205c040d103124119500d0400d0184102c0149804104517110a000e00c2030081e40c844603c2489a00300101c4400c0c48400400c0a8446822440f40001e06071180d58038800001b00c05071a005070043e000601d0402c03100d40c15802e0203032030210000c290810a5101c48880103060300e0340c3c0d001c03104507641500c90a5119440074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 308519487 1250 308518237 308518277
    0x60103060308040801090c120c150320030906070f0914010c0804151101060e0109021b01050108030a02010b03031305010c170a0c02010e01050a0e09100513050a180b0601 74
    0x181c0040c00c030300c4001c6000f1890314010f5000c08010381c460b03207001810b10341d44d20302c4613030388018050064000740303401d03000f01700159041c00b480f9011b0496260002e61840502c001101e1503a016051008240001c000c0040b04182003049640042c200d050a62310b081c0c2d81d52000345030004a0260348280040aa00128207034050307014174a03000e5003c11800d455548442142c0072403c40c050040c000102160071901c0c2c0440d040c840c0b0340559400c1c0200110b0b517820080d80b01c1c069401220405507107480142240b400e04428801c0d02c1c068010f03130f0003855031005c99420007425641c110040c41d01ca82c0040040c0f011403800b005820382101c2007801c01c0c2083c0c0e001c1e41040410b520600d2000301009a00044c0014150741c8584000c81c034078400d0329100711845540004451a01500b41e01c070000c00c40034465080146400070701e03640d000c80c41c5044041e015403600040f985801140c01410211900c4c0c00030b00c401c40b510b90003002c1d5130120441c2200d01d40034040e240c0c081e00001c00b6040030b0500c101e002041d14107098107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 308520737 1250 308519487 308519489
    0x13050609010512040b0403321b01141b040e13080f0a0e0102070b040617040516030302060a0f020702010c0b130c0303080916080d03020f04030c1706060301050f0703020306010306 78
    0x41160703c9120302c0d00d402d000c4622030086900704c000132140308a0404400390600140380700750103204074243c08508075a111400c0c5e03200011204100800d20303108104514240140030f643e205509810105003444084251940c925090048501c5002e110501c44c401600c640654046c201d441280103400706414021810b100c0c0c41408614200b001803400811604102c447c03d40340401c1e0300726485603581e1030000501d2b01480c09079034000782c003042024808007030095805421500510554802c8607a410b45020a6030040d8422409038000004110680340584104280824035400a62610140c1d50000304050240140106425481000b040044810001c1034a60a60105085007030310340b03900f400f9103011400c480700035241c0315400403042c2d4003440941e00812980414000c05004000744002c0d000f035001104c1d040900082800004080781d1800011360090080000002c1d20b0106190601d0410790028101402a8140000d0002d840c4400038840da03c1117041c070700142c41e030307d40c180100c000c0c0c111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 308521987 1250 308520737 308520757
    0x603061a09131b090602010504110d050f0d030608070b210415020f040503012f070602130b04030c0608060a1202040207020a1401090806220812010b0405010311130506090105 76
    0x18184002034120f031244a0001902c00540340c6218640e500d01049003a104101d030300800840342035000b5111801c0801101501c00e1240c0162440240c00310506454000c4886010000a44075241000080b10a205510280101d840d00901e1f01848000c07200000d6560a580d01c841e107180070004090140021040740c130186450300540d5904400545000c2c40c2d0064024248030794030f0403650349080701014240300600441100303800da48603888040005550130428050b1041c07074080194a00c00203519034800003410054096648031411403d00c0c02e440c0015420040034440e085092000c2c0b42d075507030039003c100d8181a100e400d50b2000c1d0300c0401c0203401442e038000e4001111030404504c0b032f03460078541d1b209140c00703a071080c0d54181d880c61240d90b03070441503a01004c030001500040e035000200b4110a5085406440f0381890f00120004124140b04240e200010b01900810180450344c0d1500500c0c1070541c41c0c10141e0b090075030400c00c2c411081c030a442100c0c0b0590000481000c2e82e40544181c40f1031000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 308523237 1250 308521987 308521991
    0x604090204080615010c05070b0a0314010e0f07080c0d180209090607030e0c090f101214101a0f040b1905041d0607111e10060603061a0913 61
    0x5916103040f9075901c01034981e0305004040b0100704080c0e510075541d9445250704103009201c502e2611034800c120f039216645030380c00c060702d6001440500c50702107050b0f4000c04515469100c0d52400316059004600054480c004200002c4103006814111070b00399a04008840e40010311070103002c422009040307862800a4201400038100300b86808085480362081126403014051481c2e0644040d0b2a071405c0b16000d44e00c51b03a000080b402da482e0040d0115400703400b5031940300413207894070342c6c2017083c00c08011700710760042c0d40d103484020343c030814404d0200003003d6800500161400e141d504410b20840541c3c9070003081a5901408280d0700d07504111003000025148020040f80280101010507182c02003902540c181b0081f02c09d082030686d880c1700b80b106504090859501d4510302201e110f5010304020441e8800c4002d2008100301210724004185101c0b001032045144141500041c0c40940d4064030078540b0340141001340005948800c81ca0048411900b642d5070341500001c3d6124a00c9c04480340524 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 308524487 1250 308523237 308523239
    0x12070308071e0e0f01020106120609060204170304031b0302090103021210020a0c110f060405010809010e03040603020a02010b030a08091002030c07081e0c150304021c20150a05090604090204 83
    0x80d0400343c5852005801d03105a9030924004006900342d404a00c14a400c2d45208556900820440c0d0b0000603035a220303d0000d854280c0c2c400240e105181c204004034800d4200140030010013003403100a0070004164003010034442c0c9150001540c00005200190003850a0078503041c000ca018820200080020003085440c1c204070140141642da41c00d0b011116080703003040010061508166550094200410305403905041c0001129045c402424803c429901d0b02c48441c291001400a4000781c4240da6005071284140d2000a00351501084030030f00a4000340b10817008503403507038110381c1031200c10340301c032510280100d100300d140d842441c00050584c01a01004103002c600803429a1500003820b080550540000310610307110400203200c603500c01d00035200100c020300300401440d4441d0000f440556101c513003d15003030358418818802c42c0d4000c0c4902801e00303850950b42410700040310550b0415240d81c50b40e40750010500c2402d1280c000d02c5404113895115a658001301c6000e0030914106544032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 308525737 1250 308524487 308524547
    0x2070c0f170a120c0201090e0415060902090a17031b060405071a03060103110d1e050c1c0902030a0c0b040f09020f190216080c03010b01021207030807 66
    0x2000160107580400d203040c816200c01444001404207469030042040303040c0c15074810781500d141c0c080c040c00328180215100300040c460300c10340600340320318003881d000d01d0521421b0306e6000803551203070482000c0d60f00c1030101403082d481e074004540541d17160800c510355404080420034503600602c00d102804121004250110030004283e40b03014610840448400588489520500074190031854003000c1090000410640c440e030450150f03406010040303482c0107401c8410109036052041500d0b24000d1030344003000042168452258040078000510781001c0f0085d60045100c89002c5411140e551242204002d42d50309111552903e64031500c07003101c244d525655500340b60454401c5204000600000040c2e604060080318420003000c200c4500d025a1100b401900d070443c500f10302c003180300707034100580418104044400a0403241d0010715030f501d000400c00d401c0d0341c0300346030017811900080f4809005c83c04150640390300795450305005486980701c1d18120303001c5442c10304011690079641540255 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 308526987 1250 308525737 308525759
    0x1d131d01090605070e0306070f03060b0307030510050306010503030d050402211b010f0c03050a030f0509070915030c030b13050118110d0201021b0d08070b16170c0c0102070c 76
    0x1a0b072185405210590302c242040d81c0310816403483c0ca400d81c00940000e0040d40c89004e2032202401d5508001605989540038403101e40c108917480070100742e0300d6050117104c000200000c402040c04030000c5c82d2540c1000046501e03805200c0702e0007002e80d25140460110360f10083c0840190800c801c4041e5051034149501e0b0b502c2d031074034200c0368481100d0964041954495880f185190020351104109000709540480f500e50040c281d070805c00d07035500110b0041032501e02803c2d002c3d9114000504001b41018900000c60390a101409183c541d01c03001040000c034140b02ca50100c03a0080495540c95540e41c520945507803041000600c076500e0a040c4051402d014103070908943d010b803108000500310b401c14485014072080001c0d005d80c0c400c0c2c8460800d4281513042521244001e05105000106030783c40c0d076030b107410000c811905402d1007400c0103d03190b54039100e10440c107810714004040f071042510200c03d243c00604810120311000900310440b2000750121000c06501c00c40f0f880f1610f40c4c030b60499034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 308528237 1250 308526987 308527001
    0x210406111507032a0503180102070512030105041409070b07031b03050717030f041e02090f0103060e0601030f0204092406060e010302390706090509071d131d01 70
    0x24243c40d1204e03c140c0b00284820b01c07008500f035407210361030b544803500c1038001814010b0320600340b99020400040012018803250280e01101c904c110380300e5040c00104425151404540094500035404108c1905000900c1900b01d81d140703d01640d0310026418111400004284a6068800c4a152620802d40c1c814028001030f40075031341c0b07160620400d8010840e944400d0354400322014003100410702180d1803614a4210606c0c540d80030240968036404130b105e03010100c03080c40034102094010000d20156004041070f03008904050f103610341c1590f889404281d40c0d02006801a0703584c21042c4200094800c541c0d641c40c10314108061042c0204083c0c501802e050302072100021070500c00103049500074000ea61920446c1000c0c003008000704035184540386070724900d807400c5070b505034000200d00e201449598054032071a52000c202505040034048061000b804400401210402c0c4c0d0350f0401c0c440e104090b08035400c480c1c64803401c0035a0f19020180c04030101391120030898021b180710b0071805510000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 308529487 1250 308528237 308528261
    0x5070b03040203010f020c0c0111070909080c0c09070507170d051303030f05071b02040603020402120405010501050109060f0e0109081905100203130b0c0f030a0e21040611150703 78
    0x40174251408042c1d02c240e01034402e0401f02c6501903004207942d907002d01c400c2c2c1c0e2600e00e460101c6107400c1e5900075140035100c0d6000d068504910004040081820602c10142c0b180c0042d5519180d42c00c11070b000070114400c1030f81c080c05000c00d03041c0000750280620700300c0c1c01c01510050284441c0c10107040c2c0440005290340100c000c81d21f49101c0041e0740f03140e805002e108540d69141c4425000044001394503070078005400b02c1e4400e565040c0440141d9a52000d40055019804064014074052074003d0071038106070045814003c40010030094203611914409645031b8501c2c2007040c001200e40142c505044680080d007a0b4000c080001041445220800d107030b160050044071001548138000000b2440f05440d1008444140003803d004204880f08542c0c000718a0501c0c22724080150030405030039041500c02c1c0d002c4545610194400d4981001400700394540700c41c5521030341270071000c603440d28400ca1007007505200300c141030480c002800f40320401c0c1070418550605000d141c4000014000c0810103018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 308530737 1250 308529487 308529491
    0xc030210140109150605090105090d0606030b01051e060f210403022d120c070906030b0604050a0b01020622051005013002011805100e0907020d09150c05070b0304020301 74
    0x542c00d83d00b481c0d0303400c80348039460301b500e0425040d0046807070340d000c03540040c0c0014101c1c800b10300242d800c0c81010000c0d4000c5c821007005506142c100a11100650500c54101400f070040d0307001a40c80398202c4c0c4c2c5170142400e616540740192091440854400ba81c0009040301c4001000141900442d0f003400d05020900b40960700030108040e0101c0c55034180d000d03101940203a5404610352030400c000c103004a1207000300d4900c980d0340c4503500c05940407034000f1289504800103010981c10301c2d014041d00000364460500415600100007941c4403c0240022500c000c10702101d150b030b44d2540300c880059074001c070958001c43c0042c0c443c0406054284070708c00a545400a00e500e0030300108800b1055881084106003901246400440303012681d10740c5c046800954650019040e600d000c00900c07241131548a0074064101ca1081212000c0010030340425900203c8400e040a03900940780740c1524100301c0004c0c120016218215000001c0f041c0041c1144140000400d000e14041c01640c8110310031002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 308531987 1250 308530737 308530751
    0x603070c110301060b030f04080405061315030902060304020f0103020d020a030b19031a071206082103012909091e0c040f21061806110c0d0c030210140109 68
    0x42c5422503042d03101e101d40c800000d0000c40c908445103035802c0d8219005d803480f581090f488000040603648484000701d82100324040070400e20b6020034007440104014101000481c4158010a02e2440000c00007803044001e00b002d4842607000b07905854404c551000c0c110b44698840c40090014002c071459940701d4032402c0d004c0b142610225138940280d82d4481c0a0214804060360038070b15540000d41039000780030940f40c03407082000b0f107482028018501d2200400f076080e0511050050b014210601d100c0c800000c0005100e8291000055415012201850f02c541d40d10424214042e000305040b07581c2c8100768806101c844200c4085400c11002ea0300c00342081c0b602c400c00349454603c41ea215504030703142c09407010000201c0808510b45855019003213448840011398500084980c01201c0303a01e0700307000c0140031092000c98410340001e644039803107140c9880d10114280355141141a00e1800b0841c1d080306620800d4824000c002c80d4100007141400109400c2c988100c600c4d01c240112184180740c094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 308533237 1250 308531987 308531989
    0x201120f20030606160c0816031b0305030412060b060f090a08030702030d1103090306090d090b0906160311060a09030f08100513092001030c020a120804110603070c11 73
    0x7040340d0103000300811180c64101c0d444d40314041048541d40c00e403401c0341c0c03260f00068644030501051104140201d4024881811450140c00b81019210071100040c176032541440098000801c46058a01180c07072483ca02d9218540700c4060031220004540104002c11a800e41c2d143c2ca0024000c0300c00c0842d40c1c08003258803091703203e40c2c0c0d000e1320101035490750100342004c0c151400b0f1000c104029079501c1c10380745400c100310701080c5010030036100031009a21403020040f204e503204940f000a8900c07216204d160506020008110340981c0d0003a03541540440381c94410540034440200311340050b00c055400500d484000000145201b00d0705a011451300b00359440341d64894050144202c40f0a251089214205000d014506000c0150300745203c2d5210701035000b2882d2250f04228014103403281c40c0c0820380010004040e02c40008043c400d40d4480281400003441f90300c2e06842543c4a4a040d4010760340724101100c42040603141c280c2c100000006000455900a043d02d0b82140200840030600200314 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 308534487 1250 308533237 308533301
    0x91e0f0706080712230403120506010f05121012080909010b0702030307230f07080f0706080c03090703080412021f120506120d080109060b03150d0201120f 68
    0x4466000141804d490f80d00d43c0306280c0e106081c40110004030903141c0c0350403088640912400e481c10342c00304050f8110700b0601d40c6980101984150b080c07905c8030070544628400b370803a0280001d805030590300180000c40f66410808503500601305408210b501526a040540391a03000b03410380781c01440d915002240c0c182082c1d00b01c07410a94090010f5180c040b241c3c84012442c25035400c80c0c11800032010b440d0084400c20008006d5600301c46010700b40d81450610550720b081d00c00c1d0040d12980d007060300c1c00c010301030300b101016500c0803800306190f076a41e60314443c10381480c160350030003408402c000c074010448242814000482503c01d460609a00488511050031891541c0d010340024594892048802001d500041e40010010f001d032107521402d090700364281406011004c0000c1c554000400c105500e9001c1c800080510021003807075070419242a10280a00090841c0103203941c400a00869204e586541d001070104c00c1c1c1085100c0e00010110007030180704184882c1290407502c181e02c250694 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 308535737 1250 308534487 308534491
    0x8070f060e01381203040906091b080c070803040c143304090207080304050d0804030c321b010206090c0d02030a060501080a0b1f03060203091e0f070608 67
    0x4a01440c00041400c003d14211101d42005140c92410000d1a0301c1d8030386a0103d41c1000c001404051501d44d401d1558040488020f54040c102c0142040c0c81e19580e51901c00390403040304014500f460482e41c42e580c1d09003ea1050b542c0052a0220000410040c0922018580203031844000f606c0f0885842c503003040a405034031403403180141040d000e01c81c8003501d2030a0341c02c00034012904050502da42c0b018400100c0c3c100320010b0366035003000402c2200f000002d02c00b14441c140e0342c1c10410150b0415031401002501d034100020500c1c0c1061801c042400c8a82450380741e2120b50500c800b1120308156660798403a1300c00b20031a2a03d01d00c403402d00540c1d41c008103a680c41201024001c0003c203a1410810441440895043e42c05001d000c1040300461281e0241c14081c065000040c42c110000d45440603c03001d009100e0710002c0e654480b01c00650500c5030502048036003040300584c503521030000050401c08800c400c08440c034915035014040e1100070503083c40c1d9200038020340d0100e0380d940d1000e5480c0002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 308536987 1250 308535737 308535761
    0x15030605090106231303080c0303040302120403202e0f0914190503070303020d08010506040602150a06090614090a050708071b06020d02070c080f0d11010908070f060e01 74
    0x80851344503850200150258038000117801c1d001c0c40ea40d4580815a13401212404820303000001007109140d0100a140d5000450084542c90245948c445150700d155142038080c2d042003030820703a80700fa0350781105903562080144007034034452602c610429040c42403803524008520a4410f020601e40250821400c5030f140000081c40800007508001d2044405083d89907050800c41300490191020000c000c00303948250001d06100140820190042105030b204a1140100300400d20845501243d41030003642882c2d2601050784501e00003002414064210101140c076180002510401c05003105c00142d8040e1282c00190300c40502c01c2087d510103c1d4244003040b410008129003034400d0082e52140369084da604107200c0c0c8595900c8051341d12141041e0b040f141c02240010602c0b002259100091038200024513240a03160110341c0c881c2d07001c646070f02c1808441c1460301c0100000f03421445045910504455580034285801114a050000d091314168900030750b40c145c0d00014802e250240117 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 308538237 1250 308536987 308537027
    0x1090b0f0912161425081216020d0c051003020405120105102112030207050c12100b0a030501060603140108010b0603040f140d0509040c030b060f0304030915030605090106 75
    0x840744d00c84458040b01d6414401e80e61140039031030a04400107100c01e0761101144d4403054519460403e03001d00d400c403400480c1d01649810009100c03141d4401c2c07010b43e01c0e0796064400e40d0300360780c1c1410312402e135003081e60155420031181144c03004455810340c01041914001c40d09402c625109040250072584202c2c0c040300e600c0100c10041c4a90322842d2208190084200c40d80c119002060f07485c2e082040050402c000420380200d60802002400d200d035498802c41911201800c1c00c1105001d580d6a0b1030301d45189602e41d032586c00d48429154240014040c64200009101c46035541800500820781c50815440fa400c21000200d0103c50600590b02c0501c801400c003811502c0d01d403110080301c000040107d41212014110103020842801418000d40240d2030719529410f01c00c046c0302c1580d800c550118201031070301e1000c4e4000d540d0242942e40035a111101603880350384c2e501d01036a800c0b805400801c1c404140107030015009034540c124005403201901c1545d180d03603a503a004d40300c14010342c40c1004150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 308539487 1250 308538237 308538277
    0x10801180f11210c01120203040b010b0c010b030a08070b01080601081b060412030906121812090b0f0310050607210e060f040306060e06010210090501090b0f0912 71
    0x2d918140d4880c1c841001071050116000300502c103504000310300341c0702c810b98000c140d6603045036800030110400c641d2070b140c00f0352551805a6035000030380814000e440ba09207000caa0305801c00710960022030038800140441c0c110300b9403400c0c200740c16007000c0011214125035400110301c0500201d5150704941450000b021040f981c0d0130304001544110140580200381440000b50240d992014041c01c0c070b00036105d2405140c01c12800402100030610031034000c40c203045a2031704228040d000f4000c1c90350441e00e40c2c508807440304c1c400c0f120310b1100c0e0310014181c2804162500501d004c40300840c05003404d1030840f489140e44000340202c6024200010306061440d2140b0003030001482d40b2040c0356001403400d400005c00000000d1038980015400401e00500880c041c01089220300c60580034210043c0204501c0ca0f146000039aa0310300010b421178840e807100045030800c03d007500035505c40c1e45e2210010100c0e103482515062904000c0300e02080fa80320f00000e004070201c4180840c5d444903428225500c01c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 308540737 1250 308539487 308539493
    0x100605030f0703140a0203070807030b010903081b06010e070e0405060108010302040213090606020d202d0703080901031a060f0a0207030203030d1d0303010f14190905010801180f 78
    0x1d040014001c0042c151290104410183c1a442c0c052003014240401a01d0707003048440100010001051881414134186181c002c070303a0806141070489500981d07595407010701c550800761135a05021407070028419a4000303e40d00300f240e070805201c1e00c00380d504c1074030000c21101000180c1d40f041d07800c0744c0460300300401800942084c1e0000e001d0b06801c80350f0184401d540e601400d00301e415513480b910050308492010030160341e0058212000b0101d00420003400d80d61481c1c41c031b80720710003c99207116040090300030f54141d11203c4d811b808054400800d03035170055540e0812403c9940401035450000f0b103001d03140c5003000040c24441c0030306800948080d041c6906002c1914a6a1040c0c0140d01584980c04000005a41c204000c100c0030080391000305245000c581c058034142000301041c14680c20501c014095036039a00c5207a8121108074405800701003c0d038021030303003524800000381c084821040000c108403545d600018102c401e6600200b050b9054040300d101c0d40c590250b0b000b09071903010b80c400e2004c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 308541987 1250 308540737 308540761
    0x40b070c0308060f0609030a051b09040c0608100305150708162007050a0906080609060403020303070e180a0501080d022a010504170601081504030206130c0807031a10060503 76
    0x113500d60241c0101d2900c000c0500092420001010448541e845514501b0700b110b00200001e030741c85d20680d03400d01d0b02d04160340c0d200e02501c2c2c5801135000700420385c40082c001c0d01c1e42d802100010754102082c0e80a86003082c5030f440a00c2c400f191100b0100b4080c0020030702c0c8074a81c1030034403200303003143d55491040351400702e803404a84210360440b00c85208844003c1800d41d101c8500c80c00519000800191062421040606049008051009607000101040046034000c0200c9a101e00310740351a1006284440008040030300308800b0421690504040001c03007120380d807055043e02c40381003c07200300301004841241d6a840346101050f1410350301c1c0807107403181c071245948400d109e014140305050607120000b550700400c0c5003040392500c1c0c0c1300388010420f0000522840c0a1020180c920031210315203907c01a56614014040c540b00840201d001800c0c000d1028109018103130b0403050f10545a500c0c00d040c00e480106103010b100b4401800c02040c0b210142443c20000c5504a40b601e0b811a6600007003485 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 308543237 1250 308541987 308542009
    0xc132d032402041e081507020304141f0305041a0c070201030504050304091b11060f13030c1407090b03030310060513270b0103111801030e0102070308040b070c030806 73
    0x840a6002d101c0800c140e1982131341c0c4000307078200300d0015240c1d9190035040341c94900c40f50303c0c02654194000a004640340d010040b01c0c1640d0741450081c222806003408140e0401152290351074201c61074507646107446c0d040c1c00c2280540d01542c2507441188c0400c0a90b02c5001c030644116452020412003000154001d40260764018000c205803400c040d0b032203100c03105549040701403442c0030030790109511074545c0020740340c402181814001d04140c074082610a218007800341490600c80008061740e42018440d0013425509680b0480a0801d00c070310540245d40c1301041d000d01c00805091600f04111810000260b9200d08100e060507180da92800c20305458030390101031045070000c244000880c01c0c1c0518060613956001035583c81d0b000640c100c0ba00030417140c480b45035a04240c141200800456803800c02d441c150700c4040701c0a0703103588601c00140c009240010400711594004220f800500d81c01160182c8114018010104143c0c0c5055003258609850400200410301500115070769040c2194220 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 308544487 1250 308543237 308543303
    0x4031d0603130f0212150a0605060405011b060c0e0411030906070c031403070c03080106050c10181416270c0507051f0c031e02030c132d03 61
    0x40c00c54441078000c2172104495280303220059204052401e0755050b042d100710b0780045401810046281808001403683c415449800c0c100440e56081303114007205050011001c0303034400001c0044850719640a0200a200500c03244101c2c82c2c8101e40e0409200c00003102e1080000d8ac014280a607034450094480417102131090b4100007041518003150050a07001f9801215243c50310a03a851283c0340052201c1e4050300224100442031001f008120800181e80100c46c50400002c10303501c0f0988103a91801001150180980b0307040e000360050020003150490f043c2036a100724200da16203c0313440780c68013500c2c100d01007008105981e04c2100791030644e022030b12150f5285000e07482c19100e500d542c1e1400541c49404a03c00d41d0108000551101c2c40c8625404015103040c180081100035000c2c1010300070154200503841e030008001a240440c3c00c04031691a0b1104e800182c03690348034408076510a19a81c40b90744000d001e64450403040e041d0000c50710859501030443c40031440900803800007000901001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 308545737 1250 308544487 308544503
    0x904050c03030d050a0c110a1202121303050606030304050a090c02100905030306010306150c030302090f04140f0f06131a04061d0a02040305031b0a0501090b04031d060313 75
    0x5400346560070700081c580c160a040f40459582000000e890854400c45013401c00d010040440404402c0082144090b254010030b0201c55a114002c007a428900d119a0248007294002082d440000c40300350108160390280e811540e45540d10700500d6982d1103140207407a40029006c900700701a010b42d0300110842c15061060710018101224030380c0036580c40c0b440886454002100b08005540c0c584038120050242140d00800c0301017007a000303065050320010240400d40c0000300c45107d6200c6032003501c00088040c1c801c118000c01071907002110f42094a081c40e40c4901180800c91002c80e090010303005500c010b041c20060301e44905030100030038400c41c11140c0644040102800c030303030308c03880768070001c00140740701684c0e0440065541e084100010300841e00c1603c144028000324900100382d13100d4810b9000308480b42c1150740300c0c01e490425081d02c000c00070b6091034031040c00c000003004034601491082c0c455202a50140078103405001900a203540c11040500004100410b0541c123682464010190 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 308546987 1250 308545737 308545753
    0x3071403120f0402090912030c0c120c070e0702030405011707020c090a0c090602030f03040204050603120a0e011214160908031801020f16050f01210b0a06020304060905090405 77
    0xc0340d0307804142262007030340882c2158200030540c1408808140c0c80150b14003e41000683c0d82a01c6009000c040c1214810b0301c8040380401003948100501000345a604c11880c1c1c80c0c0548201269035800d1174002c1d0b0b00d9020b212804604c0442c0000300341c50030359130140c403100b0b0040c0d0340101320740c5034450007441c070001c40c820f00c0c2e8600c426845080e000b900600d0000000b00c2d03d011180340c060030101e180e0344007030210b500800a13001080e0640c1c00781c0782c106504640c040786d00d84414001074509031003060504900c00000804540c815000b401c801c5403d0000c1e00c0740800c00000345800c80c101c0700b0cc039800075048402c0500080c100c60003222400f9003030b0164140008903507140e18221345143c00c0f0441c1c800c05103000c284400b00321360b010404500d11007560001000e0380d085010003844000094414a8010f05e00c6110785c114603030241c0c4e40700308210000d00d200d0008480190900b0044c0411034100c50103000040c0000ca0028400700485084c1c2d02a601c2d15442c0928102c02e2040e0030a0044c402c3d1001c1c00f501c40307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 308548237 1250 308546987 308547007
    0x12060902070528080412030201020f0319110a0c03030c020f120408060a06151211030a05040c151d0409140615060304120818070b0d050906070203071403 67
    0x1001d81001e500a0004100c031240c0e40f1080c0400880b0049800d00310510904040300261100d0211410303105003240d521103520307440c50140e019000c2c1c0010b00c01e0884021081128070100750241a031a1401501d0070701007041c4a004110440c40740c1140780e0300250203c24500082030181d08050302c5292140304442c0c00c0d1841c60b83c0785082800c02c018421b64070600180400040d101004941e0300400700b000e041012520300500600c1c4004045c102406000200800300c0781c01080d0391211445100144045640e40380405100000301001c80b41280c80c0903445c1804a421450405002030385c0c441901c5088070485000302c0b14422604450400343d0054a0f03182d1080082d084041c1c5040002000740100424140031707414064400304d40c1c0311140036600c1401000b002c2410411070381184212420400700c02c2c1c0b02d90304230451880d001d011070049441124400503a25012034018007044150300c804020b40d448081c103480e00c400084d20500700584c800d01095011403503a0300e244c60a130b140441107030314013071100d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 308549487 1250 308548237 308548241
    0x16030c0f021306090e0d0504030213200301060807020d121a1504080f010b010c021302090d080406020c0a030b0c0f12090307021201020a0909020315120a050c150406120609 75
    0x2c1950300c0b6032902e6450030040356402c0d0046803552161103000c0d104450103542c008065020354031019110f203880d0381c0701400c40038207503000040e6000c1620007010070400010400540307a00030300c41c0000080500e000500c0103031003c19500388061440d6a005880d282801072800a094110b4406201c4900f164080c0d1840d80da03504d008044030389111206840d60316040c1c1c413a081808601d241d0302580d05082407144c1680e07100d51241c40c1917504440004040328540d5480f002801030010f5560441c0362000b01005210500c40a8011030b1003d608484d0031410b030038140310090185d032000421100e403500110f400c0083c1d84005d00085101c0c100f00c0c50510308170078200e205030340054850620f96040040c440c01541000c0d0006040b64031003400a51821026080c028140780d150f00c40c103034046a010010894442d40d22800302220030000b4040c2111106440341c0c141c484080000481c1c1a00c41d1480c6006a410018610f1078170003c2d40036140e00702813505a0a60b4070007404100710a4070b541d2020702103484440e80c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 308550737 1250 308549487 308549509
    0x30d050f0a0605090705030c030a060503031611010e0603190b090703050702070605040308030f1b0c061f08060a0908040f15020111091e06191e0516030c0f02 69
    0x4520551401e169240c0001c0318800d0b0002401160142e04000c0e41e1600034040701d8101c1600348007982d0300d503a0700c074a0f50000c20950300800d84c9800000f0b580d0003405150b0340c1c1c480c0554040d10f00c8103040354500005541c80103c41601507004003040c00000c0c200c0900d1880300280d50912400402e1814001c8001920102c0441c0c1b503602281d42e80c410300440550404c41c05001c0c120300d0030410725090a646803117140740401000c0a0b8410469000a0410040c003d10390100d203c01c0c5001580342c05050010342c1d160030f41201c44c0b90001c12074203446c0b81c98010300d40070ba42c01c9440c148041c0c9450707203601c1e0901c000303041451002d8a0135071041100180381d91070441d20390000c0c0703000c0041c003103881c11005e4020700303403040b00d4100042c1c08004e00c0b020303160f80c0e00c841e8003540b141e80f583e091301000b040703184c00709043d40165102c8540d855141d5654415060300914069a085085007641c101e04031041c0d42560680075411030f22030103100d40305211000038042d60707900c0314045c090916801006569070010307402c0c0900f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 308551987 1250 308550737 308550751
    0x8030108030417010903080103021903050304090b0909010b0603040213090b1003050d0801150c1506060305011517070815100e03010e060105030a061d010c0e010f1718030d05 76
    0x18204443c22003640a8107021a81c00c009218101d040d0720000c01e85401800003900c40d01c2100204615507081e03251403402940e200040d1303900d032541c1c2c0604c01c0c000c3c40c034504150b020341d0302e00001610102040c8642d000440000300320354150b4950b82c0901c9503416000d06003107421a42e403280c00d0003044030041c06602c00c404601c2505810b500311b00d407990410844a0560090151460040c00300304400030030324003c082d01d8540010888064281041701c000c40031241415140340034400f15401d681504a603040c4c844050a90304058481441251020310b001d0302101001c68140124000f6441100101c1e0080000f502066810b110300c0006164404591000c5000c00e40b403250f08405801c0070701a46102ca9824005030800750f01d444003182e2980f81e07120004000f5a40c9a0a9409403441008000f02d4080800c0c02006801c40e4040040c1c4400c601842117404504429905c602c03052043c00f40c480f0010361204842c3c51a100e0000c10900d8034580801c0203910b001c01d12810115007500c0c401e051042070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 308553237 1250 308551987 308551993
    0x10302040c05091e180f01060813030e0907030e06150a0807080712140f060712050c0d0905010b0607060204150c0302151e0c0a020c0303030108190f08030108 69
    0x1155104000845104000710360512106001e070b242243d842d0204600348030305079041100750218040006210203009804a010b07005454240180d00c1c600400140c141c1e1010340f039800c003940340c003c40079081c001000d000030001101d801c0c0b0242141004003280741c202046040104491404110b0345090100846140d42c012041c5402c00d446490900d0b0004020403000d0003901c5030030700f45040c9603190078107800b07586181c4045280034401c100d5100e13409980071440d041601c43c041d9072041c07090b0329a00c1c1600d03031030b0020f0003008100384001003d11031503001c0d6119032000c602e402c1401c090b00700170380f5880006503002d56039480791b00340e10340b0780d4401080703054804c403c0160759901300200032008500d18090707201000417001c0ca00b80020380009140b200d8040e81a041d0343c00d036490140c03440d041c1444c652003141605202c403e100b10b440d0a076020340041c61a40e000d0b0b07a80305218905165880c0401d00c1101200d82c0074034000c1c04c19000380c02c1100340303843c05415600140ca24076101c80e4500d40c07007070340140c001780c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 308554487 1250 308553237 308553239
    0x7050909041e0212011e0e1018050102030403120b04020327160803071505060d170721030b0d0302100e210c07080703021f020a0b04030201020a0306080601080307060c0516050601 78
    0x7680c1b0b662030803400d40140c90100205c1d01c02403c1da550b10003070080e16105103580d60b030407035045104003000b9100e0725520000a5540340341c40d10700240b00c4005444d880c01003d04241e000e40091a1034002e0b2032103001c0888040600d81903840200c8642c1e49101c010042d80e0041280000420b404004400090000e4400560395404d0518011000300d007907a80c03540503a49010f090012507641c000141080541010f00398504071807030b6880d00518424000b004040540210b06030200c0f0038550714220902c452a1001c00c203040420040c03142c541d04c1c920b0000c006070420034150142da03a2030390001045003c001c0c00ca5100f02d401490b50f4082d51850307641c9200e201d002060215901008010381c1000c0c0c0100b078043c204036491540860031b0720540c12a21241c00407050824090148200100d04416400c44840c445904080c02c02034000e40c8500101c400007410404042801e50b000600d560403110402d000303614151030780cbc5450005010100020f0100324042189100d9026040015002c860081c4003420342c039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 308555737 1250 308554487 308554511
    0x9062206091e08030a030905100f050105010e030f1e01060314060103050d02280201050d05070c050c040603170904060302130608100b01020c09092107060507050909041e021201 77
    0x30b14214a03001000c00105050141c29004070548000c11041d0a0228490141d8070301a801c040c0c050190b800d2a41c900000740b244140e8540009049620a0704e4803680702240d4400c0c15151107650f80086442d900c4160240d10402040c8280c43d014082000001034103912a0342d203113086200100203401d079034010b2005009001d01800310700e9031319296000a10917220000d0076010031100c400340442002d01000700840a41e40100300b05e80400c0780314802044140345c45240900507402c140d40503611441001c49003002804c0501c00d143c1520340240e41d0308040095540903031120780c020a00c0d50303023042d05c031400000140c650714180245000c0710540440d240e428090380c98a45551540210380399401e29001e080242d8010030a42ea0224043d1500342440c0d44090800b46040c01c2c2c20040504101085480700d12202544044c01206102d80310900079a152803004850a00071701003095070000c1d14101080002e0310703200d04000c0d000c04c59039408070030703982c260000b607210300402ea05440359946480144a074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 308556987 1250 308555737 308555759
    0xf0f0105070207080601030b0405030f121623090604080601030f0303150b09010f0306050a1e05030307020f0d060e0d03020405010e0312180f03010f14011a0906220609 73
    0x1002019200070020305141c82e425640e0745d2018031014024000900115043c01030034000c03640508041d0038815030f00c05200c280d5065800044400d203078505d407215a4100d45902c41d80300300016202c411200b25981c5402c103080c1d003207940554003440d48400100030000740c41c40103012290007103000b48446941e12503a030901a0503181000042250044204000d0000c0507065043c2c51070f4031000c3c42d0040d600010139405800070100d9400160f8000028600084c1c1420002c650318817850700e0003200c08030207542e007051541d24001c01c84025032040b440f01d034100450600004901c07040303018900c08110000c003450ba050600c44c0c1118603d001a070001010321040d6000003038000d41c0340043c0e0080c000300f51003040070300079400f803401030384a0b21541c179503030b903841d5940d0003415194031074010000c0014400c5982000300030310b454143e01d540d20400100014003806108105034000c5c5000486e64078103043c03442004007039403055141181c034a0802c0041442d001000700054007825850f103c5185250410078000c40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 308558237 1250 308556987 308556991
    0x902011803050307080f07060504080c070e09070506070309090c0810060203120c0d140a1a1504060f050403060e010e3703050405030d05090a05040e03031b0c0f0f0105 73
    0x1200d400c100010030000e0710002c2280c00035074101c25a0780d10f512541071264094400c01300c024000d103007403800f1300060184000050200c3d56040c41180e41941c2d84451200c83c501085580b024680c0160f0002c00481c20103000505500f803203840c00c0314940c0e44503000141140e94507140040002c2c0b14608000f10f489900c02858003405403400210304041e0401e2500019210007860107403214404109146a802c03107403c031403003000d03000c4000c05c2989080c001020060684201c0400d8107018403e00c005103042000203150000e51802e00c5615003805c20605580300c3c003090802c041001810000000418140d10604030704410900020800c40301160780b20345021000328500051001d01c08480010801a480c080c810210403451061046c4031400c00f40c4071802607500c49a0140102d050b211441a4400c000388207141d01101c0000d005501c41301172004950300c0c0c04044103681d20810214050180c6903441307880c00001d550225180195840f0300314140906000f0707242c210382c80410708165003076080c01803030303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 308559487 1250 308558237 308558267
    0x20f0c0303070e1813110d06050405010f0c09030b19060305010b1e010903170408061006080912120901060f0b120606030603061306090c060807020d02011a1002010b100201090201 78
    0x1d2540340014913500391507034000d8940709005c10140e80200c20800103443d5041e4a4000400c07100c1c40030118145400584000c4800300e62552808141900d169020302c10030910410a03135484a005086658141c401d6002400681c01c40c4401c16800541440c5030140360091446440041861513840c820701c004c4080d00994a589032003a1a1980c4003079900000400840b40c0041507103e540d00101c1c644240341c456030300140228000c95003080030341c3c9043d09540d01181c0c641c3d9078040b241c1c0d03a04074102d520342007807400c80403103084204082c84510550448050304556120000100c2e036958039200070084000d0b6010940084021a9030f006002c250381c0d5844d07000005550301d03071840ca000c00010791140c41c001c00c00581885070b640c02509110300d0358000101d071588864125602c6450b020f000c0c205080c21280240181b24203805112b59034410301032a81044c80041148040d000d0040030044c2c04003010540204541d654048030b03d195461600e0809200c2440e00002aa0303400341c0001000562002291 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 308560737 1250 308559487 308559499
    0x91509101401141204060e0f0304051f030b090115020705010804080d0e030409090807020f0409020109050f01050c01020f0d06061b080d1404050601080f0c09011503020f0c0303070e 79
    0x4000c90501074045051154091a000200c3d1001000e4401280a44104440b00b00101000c1004001c485d5000358014514101290700b11300f200500c0a03600d10a074040c19401c0710402c00e003003903d10108900d9107810880c40c02c010075803040400209020780d000342e10184821f0040c25241107007580510504003c0d080030b2803c1000e83c901511188982e20400300f940c04090340d1410704580118007401a100034202e8200c0500604078681001e4a030b0340c01c811b00030303441495412040101c5280c0b602c1a90003056060715103806151512082016243c0d071a04280d042c0681000f4911001e00c080c03000b04a07030400711000c1901c94030030711000c900315111034220806000c1c7d07580c88002c08410f40c0500519aa40c030400c1d00350f861443c0000800540a90f0040110700c4c10524103001c20814041122070503919182d0442d0500e44200159642c2c07014111059908070111400500010350817031258994030300141005481c1228000300c0455075404090443c0c07058202109011441d03032b000103406444001240c40c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 308561987 1250 308560737 308560739
    0x110a060e01020a0210030b030a1a01050406030b24030a06090c0b070c0e0903070c0602060604140112020609060c15010e130c15090b03100e0108060408030103020907050909150910 78
    0x1c0e40c2e0f01240d440c040d1264600300048a03100c0e1007908074585040d0058103032119800c941c80c05807858819600840941c0ca840c1e4004141c905080c0b01c3d080440e41c00090003120b035203511702e00000c020a1903422030101c01010003803908607101082262585e40c810000042c0c21780c0141891001910f180d0041c041a840410030b14010030740c10f681d40019114220072502d0240c589520385440c0d8400c40c1c0c1c00030614407000800040464001c2100c0e41f140e58241c0f07041c031082c5e0442c500d51030403101c2400f0300c02c10019812509009420680050901c0400180c0307801d250143c01c0541030700d171607984015040c9540a01c001841400b504d025000d030030107a27848190b0320b50840c540c0d81c41e8009000d4040c00c904000c4058444116501c07840074000189080d034041a60390804441020303240c2ca49002d42109030301a007000186202d0005081449079402003110350869085508001d610000035000e07070100305040c010117045554034206a0f00400d601204012283c2c4038a05100700703448001e00c0015a0261240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 308563237 1250 308561987 308561989
    0x41706010918140a02030a1a07090b0f0f0706090c03020111120315030c1305090f120f03071709010203060f0405280626160807030618060504110a060e 66
    0x1510040b150b5229046040d42a210342e40f4a203003030000c2c4406545171003107003441024442c207100b45205290074403540110940e1040001d40d0081c40c144500b40c150708040003000c90641c454406483c01414a106440c5818482c0d03d82c481a5950f945d8291803c40c0d90107410004c540e0060542501040d495000d44109041030038852400e000003020080342d82e07180b980f0303c4407680d811b002c001e01001008058135400c0102c001800d0090004640c018810b124142402e4800200001c195040d20a41140245805000350725070100ba080502028140690714000c0c0000484581c81181700cac502c0c540c00184c07686400740810407102d408405803030185181c030701030044c1078200025032002240c0d14040402014070103807084c4c004003200e07400030b1251b0131040990f0101d100d030741240e10040401c240031541405000c1500e540044910f1003000c00580c4000c40c20000100660403100101400b4800101140c0e0203465030426070b23800315401c490140c0003481003281458901207460241007d854040000a0190 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 308564487 1250 308563237 308563271
    0x10060f1805100510020105040c050d0b041502070f030509030d0504211112070317030f01120305070803040f200a0e180d0203070501050708070804060c140417060109 72
    0x11404911030344801c00a102e07181c03160780c0d80000780809400c242400f000400028020300381034034125203614a00324000751703518094410074002600f0031841141d42e11543d850280844a00c124001003507000c3c01460046000144c0800368a8066201d541e070300c100304401c060074216845845010302005200a0203d00385220006005001d040602180403520341015840780f03014010740d550051800440644103600440c00400701c070f118401c0083e840c0c0340c00401c407000d0700080f26003aa011100400401c0340d24049060802054002e00b02185441c410b92901e426030b5000f00d0301520202d00789085001049003098004844400b00000300030f1582903a40025120a400e200740903560707141001107540b0140524bc0400d03c10f02200c119281e032258560042d45030b4012040130703140d039484e01000070071241c080c0c02c841e4462402652540b04656465941030014203201d00d1020403c45142d0090403240a410014805447d030845020100c1c0c01854601d803815005801c44070b07007038bc10651020031880450f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 308565737 1250 308564487 308564519
    0x1803010b0a0f15030615050a090b04090c03050c0703021c0c020901060e1f020606130605030303090604051c0e01050f07051203090706170f040512030a0504030305132a090e10060f 78
    0x241c50108c2c1e9454243c082104c000c81250000510f00c04002000200105158820b2060f01c07000c3c0c4042c041a550010960118021400c01901580210000a1189103044c58103200f200160504940403102500464079200c400d030070130004142030540904440c500001c6005400400280d440107a111140000b91200030241280c0d000d152204030f5a0368403086a005400a05005400c8030b42701e10b00840c01345d0b520302c1c041d201514503000c2d11001e04400269250440030104440d126000400c4600004407100e0f44183c5018134107080500c103520004000b0721030412900b003580c01c9141c41e41068007606082688540c400402e1107004040e180303850300070040c001d5011030a10501b680c1d5a640d828400e081c100d83e1010803408200c004200400c40b038030b42d030200780158040c0e40c040040d541c4440c41e0420b06202040051b103806410f603d1001106901c0319900690441c02c03040407540c1d5030719000e41c0b050f20071492104140750801160b801030b0130001e210703100050441c51064008035182c0440085410302c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 308566987 1250 308565737 308565779
    0x609070620030c07050103200901080a02070218041b031505131509110603090a1506050418060c050a0804120c0c0b071505010b1803010b0a0f150306 65
    0x1400106001e009511100880300c8070007002d4903903486010010a40360081c078085c4e0f0340400e2170541c04440301c40031030303116640c0440311024241c903000c10701006503000c0c41c004100d030395130700c0e02000740d50010313200e003050360608031031050a02c48c4c2800c262070a010110510390504114200180341080821030340516003e250a1803c0001601c1d141c1ca001465504441c10001c0c10034900d8820a4150030115403005601c0c0780110074800d8400c1e4000d0400c8081d10003a520070283d98400d07a12000030851b04042e0242071003601c4d5001a05a644002040c02d070341e85a108002a210032091031400c0c030000d40121064a01c07203280613071510981e4507019110181c00303071014051540310310b05458501c2c00748818074103213a04a080d0010780c1f41d8500c2c1c0c01c0f40d1a88441c8080b5a110300740e41c40798951000500617103040e518010003040c28200e20f0b02c414820b0704080c180c2154136640300c10041d40c458407a0000c52010b880080d041c005000c1c2082481021030410700410010942351000411001f1559050f44420b852 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 308568237 1250 308566987 308566997
    0xa090b0f180f090c0c0d0203040e0a181b03150b0306160c0b0a090203012d0f02040b031302120c0f060f1920010501030f1b08100f0e06090706 62
    0x81c0040032422104070500301d2600480b45000340480700d020000a800100e2190301150348540044908985a0181d441150000804000440c00242c65030300039040c8003400c15045543c0e0030058807000808d0114040c072240c04d5040d0742c07050050202502c5058100b80c5e042e1003d0050a482e400031a5842000401c4c60000181040c14402c215200340807006400760401488620350074052200c0b070080c10800d6040703100b50302e0f0602901c0b410030042c071000000c2d00d490002e1203c0442503144800174082c0f40d204c0c0c1111039801c0002256009410b0084c0d8041e80c1c0140d003814512640b8418440c2c00001405160b843d54070910404405030b80b220140d181c00c081c2690000e4070703489040403000040c01a4003825540301c400a082c018550ba0103019000400020704980c00b40c41804825a401c85500380030282c031900c04802078070013040110354105c648506124000030210381e11490a07085c003030244084111540c50380300f00c621010250080b01c140460540140410b4109007800720394444040c481c150500c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 308569487 1250 308568237 308568277
    0x1505010f080103022b050a050106050a091e0b040b0306010b0405012303150d0f0308071211070204150315050405070b180d260c0106080102030402100c170705030a090b0f 74
    0xe000160705d0540d6488000c5034a503901e80d1400d640a00362600407507002d00e4210710005030b58a0103008000c0c1800c030403094a001d089038000500c02070030342d400a264001d52561100303140e50b06c0c20043d842c002c298190b0203a880b1400c000004108240d2050100140f1400400c0b56200320040d600b269000901c1101c1d03032480b08504004200380042000300504010501301140c4103154100b0b10782d6106005642d10390b05148104492241150a400341d1001540b90030701040c001410190f000864000300903070320300f0a550f52030766200704040ba8514002015170b01d038401d000c100801044440040c182e011801d90070015000701d6800700c922240202803060081030103080510044154400ba1309000481c502a2090160031740400c13903104c1c43c2850001e42c030301103001a6801d410302c01d03280076075402080503290f130100080c11590145e19400c152204280d0750a14000a0318000040820912036405551141c014075005840c00c482039001489081c02000061240107512044950500c00080214403030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 308570737 1250 308569487 308569549
    0x9080a031707021606030c180e04110a061b0203100c050d0b1f030504020f10020a0506010909050304031b080601120b0a060506040b16080f040e0c0a0c080901020a05011505010f08010302 81
    0x18030070042301c0100c405000b100441c0c0c65581c8007841740f00300d019134020000c403446c803414000c0c2c2401910482c400100c84100890fa170b8080488081c103418001012610f458001d950040100d495280b55440407500010740211402251302500c81080c3c0122046003c001e100084e0f0041e001c2c1d1485410201030340e40000604650328040038801504001d022180032000300000039580f2031070000c007510b0911502c00006240a024046c01420b2a44840554200f40c07030b583d1003420400d0070510061000f4525600828500f00030812180241010711002581000500748015250005860746080b1420300d80d0601c616180c581c1223808841c005424156168070b001a075013034407041184000d0072a8000502449a98a28005803007501c240d450060105d4940d60001c0f02c1c01e1143d03841200c0810001060340010a00140103031820342018010b440b05510b4640d030b41400c6510583c100c0b050fa4000c598144a19640240c01c04110310150a00c4241541190006803900c0307801c10380314140320f004058130248 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 308571987 1250 308570737 308570747
    0x21005090d0e030a0b04051006090b03031911120316082502010e030f040302030c0901120209041109040c08060109111902070320100507080d05060109080a031707021606030c 76
    0x61305410143d00d885505283c9407032034a4140441000d03051500b4150042141c80b41442962031184e03009001b14900f4074409452840c074004004094140010095030003030745001070010b100e804803d09005640c03441c0c5010b00d509003800940ae0b04040150030f504100c4a120b00b28001c1d240e800c89248101d40d0028110004c0f0701406c0f01401d0030806d400007060102c032000b105009041900c3c821426140c070f01c42d01105002c54500c0910825a001c01121010b17000341c04d06003c159082405804c17030680b511144004201d040703500340c0d800c0b64890014202000a040240309803400f50103404820312420a92440b22149401202c2a0803035541e001c0600401d65802040b10350300455100c40c1c144542c003100107000b601c0105c1d4620b003600070711503903000c800740910444c2240d4510f07900081060a01d07180406440043c14020801030500c03440f844041501c50040003014a40343c0b00e82e481302c0040e00c0651881080c08c01c00351604056511444805104048040803a0f00b945c4484c607002903501428801121 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 308573237 1250 308571987 308572003
    0x110c0c0f0a090204060e0307061112090409080a02160f0b0d0e01200406090b0703080f0a0b0909030d1803050304121209110f09010e1801020d06080c01021005090d0e03 73
    0x42d41c00c0c030000b00010100e4105181e11803444044007030700c11050707445400f40c40e03008580f030b480c3c11150881d50f03100f4080d0b40990302800e2080d60241000a0180c100da4550809500408554015a00108043e00315800515003400500003c111440800e8907100f201000b6000d8100c00042e4152244100d99818400350300601d00105459000c071030241000e290881c3c0c580c4039008210010301000000300e90750303901c48111440543d1582d00c804880da18410b0301c03155000013400d00011292124003401d030a42d540e00b09140101c1a0801856542e211004070208580c40003032111304c11040341060401181c2c0040a4941c855009141d0811201d4030319800c84918030030340c02c01c0c1902462300d40040103020b00200034401c101c4040e02c18448d00c40c1c01c082017203603852091040070003035080c03c000108900c400c2c804010b4010780090000d0300f0b00b5040d110000c1954095040b480a990051160258540e41007050103807026044104100b1401e04c00c000380c1d00c41040a103e10309010344512200c0040d00e081140751 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 308574487 1250 308573237 308573249
    0xc060d021908060102120c030403030509131a0a051c030503040512070c0f120c0b0903160b0903011d071e0305100e0606040e030d05100302060f0c01110c0c0f0a 70
    0xc070901400040c0a4000001643c0e12401407081180080b02c0100b910f0484055003420802541450310707582d42100c0f10b41c4400050382c1c010310003500036000303100c0b42d01481ca45900c0c0e0300d4031505110803a00510a840311558482c900c00c3c1840c0902038a4204e0044040d6122034040c60320603925500c6080c400d00c0c05041d0b00211742c94610018050050100102c1100306176104458802001541c454040300d8041c0751000150034a42c441d24200b20501c8860001d001d10031000d4141c1d0343c690640c0c80360310084026035000140f82400004d0b00c20451030280305034a01c05c2c1c081079501c8019410034110660300c2c034a40c061000a883c4010b0801d05640c20480424002c50b440f40840c1c41c440611909800503085840e0301d101e540c401c800126846146c00d01a400119403050001c2d4200132200c502c12014080c090411140d036810f0440c00300c0580c0b01d080052a80108036440550360700f8186040300e00b1038455a01520a01a05100341c5d0003400d03000c43e500c0009602240c141821038441e070000348440107070368021 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 308575737 1250 308574487 308574517
    0xa02070b040f0b15060d05072007050a050405070819060506031e0f01080d120b0301020c0a0c09090c1403010e010c0e03060606040e0c131203120e0f0c060d02 69
    0x1008200c4403982003030486204061a0f0030686a00c490f9030a401c15090350103034000814805140f030050075510459101c2c0075450300c041c0159190401f4620a484815801d0f400d0300560014041420010401c00c0100b8068404000502d07245c04014442c00300901445042c810303a02c10400054080e40200d400340c0300090020380d407420b011490403102105d051040140c0207031417000800c00e16001100504960184010303100490015200300c880c1d211102010b44100e070f0381c01050003039460900c06405e207840403400a0019a0300d07400c01e40190003d03980408901d50802c030014002540071000001256400054101c81d05110400a4050312508440b0030656107001c1b070504406c2da010048032041e400907003c1d00e086440346014054a41b003680203100501c4040070104e440e041c810801821000d40040302600466103404c41134a0a00854000741d00003030400e8400e094046140c402c1441c803044031001003000048203a0003545600810140d14411040810440400e103159012668103103054415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 308576987 1250 308575737 308575741
    0x3143f0a060503010507030e030d0c0216150206090a020105090f01020a14010b040c0c0b0103030c020a030609081b03070b2406032e030c18021b07090b0303070201170a02070b 76
    0x40c980282a5449000c1c4a0760801001ca00414000e00c03070f00b40d07415800e01c00f5511b4040009244000340c040e0502e40c208501c1107002c4c2c141901c42d140a00e001410b2150a00710f4504442a002454244041c0022401c0d820882d050340050b84c20108660381d0150a82e20102c100e404040144c0c14004c550002400036161601e103404803041c198070005844200b11010481c56003205c80c11508000440c000601c0c034510b070300c0140701190040d01600e0b20700c3d10090004200581b282d9901003a02c0d07001e0800c9906080100d074002032048451202011104001e00460174009591100b44802030040c242d40140164504503014a46896040741d004a43c003928140d540d0400b05405c070800e90100303160b0b0160014140700611482c2d810704540003120741101c002c5176030b682001c810364101c0007400e0b1075081040d070810840d50700b10040002c8001c0c04420300301405009240c20350440555400f2191a40300c0d400811039000180c0e0010350b64042c50401d00203c0319241e84444040009100f140c801030000068441 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 308578237 1250 308576987 308577001
    0x30f030608190302011a011b0203071508070201050105090402030a0b0c0c160801051510050a050d0c0c0b0a060f0905040c080307050a15021903090213060b040303143f 73
    0xb074803211144260300070800c4080104142c40c1d00d4040c1000140020813484240c0c00920002c81c49044443c0000c0548200c1139884598002c0d400703030b00d1601000301d01100d08000c0722940a118942c01000f061326100214502540040e44a1044000051010b80c51002086890341c0c01e400361040c0f84024003c03200140100640300b2844101403044402541c282400220000b1305840c41011501002e04110324850201d0313019545500b0004030344081210902100c0f080205600584c00c41c416a0385030011030f401c032810031500c1558010002c0040d2402c00d8020401c01608440240407280d1510303000aa944591400080c1c0c222a0740c400e031650f11002c15504107009022801c20003981c8948079003080c04610301d001000384d000b841c4540c1c036400740418407034400341d0003170700031881c101d01c020032244107280c41c003041d0021103000d40c101e4000c229001c13405004040c0c0142810b004094000e03822401e2001070985030b204071620548203a1490740922482c4120003100078132110704500e9544440342403400381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 308579487 1250 308578237 308578273
    0x2072102030c010b0d03020d050d0209040510050907030c3501080c090a06050a09180515091b03190224071a0405250906090b1f0c030f030608 62
    0x1a902550b9075113010702c00c00144c90000c850f00d041651680141c0001200b00e0002d690681002c5801c0e07038801c1e0200664940ca0761544038140c454075420030302c080440d040c1002d001117203030001e281300c052600c0c2070456030b4983e400c680c0604400c60702c410b80324060005984d617400c803442850700c980d40c2182140004221040302080a0312080030550303103000300d44d0743e060300001a98920301c80c1e80d8109024110030301c242c24458001d2920752060f0000400c0280c8103544035843e10390f045025642030991003090000d003510a2140e201c800410040007040080c0082c0040d032954a0b0009801d0103580160b150004c644840920384211582004400092107481301d0070061544501800c403503201101c2481c440d1545c0e042c0c0c21502954106000704088200c4001d000342c414801c0301c03039658101d1100000110188180100009401c0d092400325201030101c0c01d1002d480500420540c2d00c0d628510f14080065101d4804900d41f905407800010210b0f1603042031700205042d8208103411300480785003e900000d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 308580737 1250 308579487 308579497
    0xe0c04051f0807140406080a09150b0112111c0e06070e01020601090e03090909100e010603060b0a050d0303050c0d091a0f010609050d05011506110106050a050d060207210203 76
    0x282c450716050754441c00e044508007035844201c100070809000621003988a6a209035004c0c02d041000107101c0406d4541c1d0708124892440c905216440d4054a0080d50340311001000c0c201d100c5c00b040c40203a00c102d00012041c01900400421070241c1180750300070305116085500d05440d264261401410205002031501c1850f114082c05840303950b00000e920340940c480c600783d030140d00010b90300340f05001c000c0268551002d410001c05220301c0507015111503442c819a0300001c809400003403038624602d0034605075929001881e1007590f0f810420410364542a00002c4403540c185800200c42c1c1ea180301d400fa13680a45200010407600d009144020000c0c8524980c05070b90300c070740c0120165554068801c02416003409088000785084104002c00c3c01d14082044100b44202d00105203001100c19540314074130164401000200709289404403000b00b8402c81020300000da400901e41414400400e2000b281940c000300207640c00a0190180b01158114004442200c006006900c03c1800000e66039000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308581987 1250 308580737 308580799
    0x1315020c0312040e04050a0c0611060108010c09120618080403020103051305072c0723030411060c0102160303270b010905041407180f02130e0c0405 65
    0x31688101160319002492400c00b03040c94030000d24007403c10440e00c0390800c2c043d0046401e481041a0789002485c00103840014104a90b01e08540764102c0381158074144043e8410100360340742c80120581c0c0c5512948003025104c030b0800c010310480c1c040c031b031030300007403030242c44c3c0100c41c11000e040da03000c2152070320040c81140d000b6a030600a42d00d40d030700912880d5514020081c020740c007024080129080b0070b186100580e4800c482c03410034a00d070b0208548440c208681900018080e52102244642c4c1809195017402203c442a0304620f031035510700c3c1d03040104102e414410340011990607041102501120510324090040205458451030082e0240c01d25440700c500219801303459281c55040400011000b070b0f00903400409030b9191417010001040043c00c1a00c81c801c40c0c00c1c000d001071300100b0060001b042d207915a142d0501c1845c40342000c58814440c1c210f4814010001d200301450100380c1d00301503d030a00c00004035034490080c0c01d11548203e511654005048042c2321204c028100500e80c00d204c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 308583237 1250 308581987 308581993
    0x90f0b1306080f0f06010e0a080c031903021005100b0703020a1e02090a1a0919060e0108030901030f020c0d0504080c03010c0f0e0301090b0a020c07060e130207020402131502 76
    0x1d01ca84040d078621804071441c0120060302400542c02815600220307810201c18104016041c0524010815800b12604210019404982100701038107040108420340049040700c1000710340740d6a0000d45408024981d88038054441004c0fa003503c1c0c00000b044010b1640b00e403850303541c040d1845c000c1e440740e080380c01c291201c01c0400e00001030304440840700131080d0760040c01c003e1030396240701c03420004069000488015200c0c0d076a16409071b440d203880c814064254202c80840c3c100c6c01d00d620f01c0940380d035500f05c40d6000420600400803103500000341e07a480303032090a01040c0486e03401a0000207001e402483c00c02c0c2e110b4440894600c4da00040284103850103a0103481c0900f81843c149030a80310800071540004020b11844c06c11304d40700307132001d0401540040010494401c3c070303118040180400d075070084109500058211003c04100080001407116042c006144902d0b03900080d400741002e000d80d034649800140344003c640d225412076816a0030440c000c0402c80c0c4801d01044500000d05203080984 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 308584487 1250 308583237 308583239
    0x7020c042403300f030c050405220c180302090c0904050f0103050d05070b07080430030b040207030e09090f03030109020a110a1101050c0102120403030212011d01030609032f15010b07030f090f0b13 86
    0xbd40f103025004e41e180940740034003004520350f41c00e024908600274010115660248044412640e540c0105801020300310719442065043d420243c1c01e2442212141e410b2005c00c00c000d100240241c9903850740015941401003075950307135062505941c0c42c40c85174507245040544080d08540ca02c010f4008010406a030b00300b005000032024801240308030b1a0150200d03500c154224090314001c0540c0ba0b1200780c10050358002c501e0744100354519042131b080f0b400b440b03401007a40c05515078004d0b07a0301541e800e00070041c0b8200c402501c1d1014a540315203002c3e41001070001d032821458500350100c1f134814541810000240c60075090042c001e400003c003800c050308028000050000304402d000a808040e0000140c440e4030b90307035401c0010949513108806000d138074030b403c6e1200000c10f18110443e10620100307020b020074900000f03007400100012844003010060040c40710750303040d40907074410035403504001d031071012050300607112403026601004c10044080c0001c00e448000c440600040031024006101d07007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 308585737 1250 308584487 308584511
    0x10e0a0308011e08060604050601050c1006030605090d0c030302090109051903020102011d030405010f030e031326030708090a050307030c09060e07020c042403300f030c05040522 78
    0x3014031303101381215075000320040740032444c0c5680110381180050600502d0804c00500301d80c03c10030072a1029119039030b90401001401a035010b429404000b8801401c4101c0300060044d022039251000a410107601203013481d4241d00944103440031708001000f58500720f2031085801460146030000b24019400c10318201c10300c00140035417222001c0844055810a820300b001120780d084100a601c04154039089204d05c602001e000074005001d2012810070154140f00803030b803051050382031a031006440400082e50144000c01501c0d00303980c0c0070108640c4c421031500007078034051042d0011a4503000701d540000810407640c810700c0441b41c050000b031003126a16515040411001c079001405a003102218a82600e0658070540c00004510729a202d03401810152284924640d0411552040c06141840e0030046460050106c2001681c280c0803260082d00c0040c1010070301c031005028103031660708840c2c1c1a8041d90070b03600506000351035082000c0c04c036500c08105600ba84803840f10b0602d048410030320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 308586987 1250 308585737 308585789
    0x614041407090303050a0915030f0b03060606041e090608100b030601030201090501050a030608030301080c13021612021207080304021c081803100617061e01090e010e0a030801 77
    0x41440c640c0c65107031002e4503540b01558564400c101c01030401003041004200c82c0040d5804c1a0004581d0750000391100b034040041003214203400c03109200364403000802c0075940d2500c08443c2a50a400403d690810a054031002440e07900d42040d400b03541080c0d0003207007801e0001128244c8900b0030605100e050070005c00c0c1600e4100a0101030b0020704d05010500175540180020308a0307001c10b01d000a04240d965409904607017080c2c100b4162600800e101d02e02d940b070240707026100b811031070000710300e0710104000c020a04001c5034401403c4400841703064244500912010b20009944c0d0207041d035030113551403c1c0b890380d40211000ca2094859038406803102c0b00b5060059900d1741d0061807980340084d82d52034625040c0c0c3d810b080981c03620844d00104220442800364000518503540130400d40034907508204d0400e44002c001540001c0d15040700300070350740c15468540c1103c4100780b002600030a401071441c0500314000c020130741885410105410154851400c504907000c101500d0702d55032106100307100d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 308588237 1250 308586987 308586991
    0x33010516020319031e031802040c02150a050a050702010b010c03320c0f03070503070809040212090c010206130308061905090405100c03020a020a200406140414 70
    0x10005005110302440c58003001100c1208900060456824450762003c04000310030003401200011170420741150034a410400440b6900d485040030b02130b181c00e03040803c060101008000c0d100303030b495441c043d82c000d0080c0580301109a000d8000803240c941618500060642521134490480c038100008102e9881841205501c203416550402c2442c1740384c40481c1c4807a800300b682400c03101c42120040787c49a40b2200c250a903000503228540700c0178000041405c00741e020302c440856420400040000034404000c554401c1e90080b50749e80c540d03024a01050003802291a00548a6000000e1000c035050000d000001c21000f40c3c2210595628040d11520642c94070b08010301060341400841c4151410344030312249a901c603044a01c80d40e60f201c00240d40580c007030310705542c80d800a410031820031a083c058000e16036801d00301549007000000c0300a540303042100014000b85c10258039084180e00c28030402c0503000c03004005000d81c0d034660032040c00b000111000c0c1d502c2185048110b0325141e41740e24000d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 308589487 1250 308588237 308588239
    0x90203070909050c07030c080409090f150b062b0c02030d05010515040909080702220606080601080a0b010c0c180b0a080c09041401050109051f0f09020702030a060533 73
    0x1c0c0c1009080d540c07e44244103018821114046c1c2840701140c42d040500c142e0480302e000340c80d41c0d01e543c01c00d030070010b441541107407090310300c1401c124243d030301c945400b021a0701c000e410b600c6a10b64214030525490b10007113410340044905085c036003800c00003075000000d4102e0400f5074400700200d0366900204034488003030a80c1c0b1104040203010420001c070440e030058070b61600424000c1e01c1d1008590000301e0008801e100c4010824998090004020701ca01c0341381c000d4007660911190504000c800030700080001090340945a4650310800b4069209440c00060a684948102e00080e103400c2210b442c3c080140402015618003540e00d10b541c0791680d07c030b4044420400281201c034116000b0f10004900c018420342c7d0701709000880924210092180c0c50080030b090000203140e05080c8032904203072407045188141c0c91002403050144000f0396200c04105c0d038032004010386d03903030356403021030b050045c5008060440ca00e071104128240002e14a810381c03144030100485400c948070381104481100c01c000301c1e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 308590737 1250 308589487 308589511
    0x60e06031c090501050f0f0301240e09060d051c02061905150405040c03170d0b010f301401090b12060a0b04020412050c150412020d0212030409020307090905 69
    0x2008194054001400e030032901b043c40500e0000164146c12070b0b90710170380c46490f5542420180c80800f002c0f2401860b002441840c084120103e0031002401104000e04407070b22038101c4040802c20044100104d4030300c1c0c403082403e2403184405c4000a501c03040216400000020180d4044e40c00d400c040c412103100d0a814140b4141c51503640080c0001044020320440704882a54008030200344190103843c0c0c043e1840400c01d039110003010110064809a1102905000d00e410a2010f041d030440d000b080c1c000c030b440c04030b01152683c40700950000180d03085c42c95401e6243c21141394402d08104001416601341c0081484030702004003d03c0011080309403e500660810000300780145000e401010094100520150500740c8070895162a0031040c002103946600101100486041c0682034003407051480000c181007900e400c140c05490030f80354400900c201d00c40d503031000855032403c1c038440311120500700b2203488503182ca50503002580195220004505880e100090240d814013626115042c16202 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 308591987 1250 308590737 308590739
    0xc0306060e0901091d0a060606030f060b03181c02010f051f1403100c020d030506090903120405011512110415060e030a0b090a1509030905010f050d060e06031c09 71
    0x29041c020131000505c010780d041c9100304961501010000c00700114000e0b0800100c042c80d00b10060300301c44201a003035a807641800300c01c01c040c2d64020203895000b9203640070410002c3c1601e85031420091351200c40325407070383c182e03414090503541540403904e0105c2076542003040340c840c4111514a42c4295051703074250f2158540c280031801600b00b13240103844014049407808000c0102080c1580c1d0400c6039440103038403880f601c03121f0035498041c03107070015800c0d141e144a030709000351266100e01c0b425007414580b2040201007000c0000940c44012100b40100b86031503c20344401c001e4401c40c0d41c994054800c130040104000141c80e0503c1400303140000c0891448070149004010f840300100c4120a0794103005102400340440c1c41801c000c6d00c140d440801400c2c4a20207460950003807800c1c584a504210303d4a1081c800190b04030a6038010784600342004040204035501c01c481e144181a031035942d03e81400400200d080c2166240ea0255108809540d072084003d0340e00c0e10495000c0348000005202c03024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 308593237 1250 308591987 308591999
    0x40605090c0f0c120a031e0905031611061602150906090d030e09010b0d06091512081c09150209210f030310080f070b070602030c0c0a060c0306060e0901 67
    0x2c0144042505582550380340010034500a401d508000d5511020a85510000e0503201070f501e03507044801007090080200c00c00030b4607480d942e406145c004600445480d1140014050741d001500d40081000306880e41e9001e03107501b40c00703100303201503000c0303010b60206003640122940b52025141046805044103041028180400c032020171001c00a0307052117268901d0103240c4e01d03490b0b03485c0e0103018458091556804180403420454940760700803800c9506d082e52541c0107407960a4130208841c900200d240c200e1895040c4944944240141480a0800c0c01c40c03101030b014564003e00561070049840380a00e03020f0b98290416445806c00e8281d0110709100e42c80c041c000300800f4000e944d1102011a204482e100e1001e61840c1d000360381e803045040c0c00752820024030340c1c20010001d50300c400134058220302e4070300700b4100c4c664001c8040080c181742d004030010380e19400c844184d80c040350131b030001c0704c650f0082c5040401c0246402a0840700280c100b800c007041d02401601411081c0300050700480c0e01383e10b009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 308594487 1250 308593237 308593267
    0x1008040206090d02060d06080d110615041107110a0605160b0405160608040209061008130f120315080106050114030405010b030105040804060906081b130308030a0902040605090c 78
    0x40519500c2400f481c2c03540056100e10029182401c0e40f10000aa041e043c60380d51894111030440042c00c20039007003a040700e060310100c0c0c0c95820107400c02800110900200c001000380c10320700346070b42580001003034407421300c070f8100300000280302c0903207101340c4803034841d8000c4459109000c50080400c060100348800103c148140b198418010803c0d43d01c103074281000c51389041080c0d8014400030b406141030000b07618021039416007181c02101d0b041c40c1c07038000c010301030070f00c0c80000c00ca12000350f01e1382c69100038006619101c075101031b0310501c016440c0303500243c05001010704050340b00f060310700180003003807107581403007140c0070784005865610343e030319011008038290f6000070002c940c295241c0403030300c0346034409000b9103010700c0c8191180341d211400d081d001421040c2691001c4c013001070403002d0100da8101c00a18078461340a01480694610f040390341100b0075a000d80c0010045040042000b1001305564010741000e4402c46040c03103010b50702c40410000020a1b00c001c83c1140041144ca401401c8103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 308595737 1250 308594487 308594497
    0xa2004030b0709050a0b070b01052b03050c0102030a0204060201150e0a0b010e0604030305040509160905011b1a0108010e010908090f031002070506042a0302091e241008040206 77
    0xb0310345102030603100c130041205d00b940383d800000c2ca03103004544542013107100c1220340d014240503120320700c1d9002054078114054941c000d14038241002803100d03034141480f5904a88100f0010b100079035880c28030002c1540250300c0b80c4120070055181a0380640001441a1940211102d100b48601d007601c0c0c2310803c1000307005042101e41070069842404506d6180c580261004500a48545840d0391504041c00711030107004042044c840c2c44c0c0280e00000313580dc40d4030740003918400c0c45c0c005803000b0b2790b0301d181d800311400c6070015000c07803240e41e001d0b401c64404074005030603154448028090301c05426000c41c2a40d0186c04003c2c003d410510070ba1400742050b40409500c000003e00300c0b0340c400e90120b1118101c0e4130144c003c4e10250487c40c1017005000c101c03003440f00c031500c0002608901070f80340c1c90810b501c4442804028851451440481e45c003000961400803003a80608070721401d4144510080d2a00d0b29803000301d44c3d04220f000c20a4494549100d0107600001030342c80d08100e13a030300c070f038200302c455808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 308596987 1250 308595737 308595751
    0x3312060d20010c0c0305010903081807030303020d020705060f04050c0604060215040816050c090f1501120b0a08150106110307030302090612011206110c03070b0a090210080a2004030b 80
    0x45104104013080800061100460040b07000203000c446500b002019607100402c0d61640e01740f0704401e400843c2001131044222605840d00584070011485000082c0c45180d00250030351066809000101090b002c0d820700883c451400c40f403c4580fa0024042c43d805513124a10141c0c01c10301e0582503c900009407035920610036040d1520300320704210743c9610080c1c031070710503100c1e40c0c40026102005e0815801d919044850341c00400910701d4609154580402011056410031400001440404916400045218a0003440c80702c0f05512010b000303a44d065a070070805483c1c80820300004040740aa4001c92038010100302944c0307001c1c6c65450640c06940b00d40e00c080e4020204028201e0300300300ca0318007a8043c1c0400024502c15203034600b0054240c84102140c0f8a00c90310802441d0b0207660004101e44031981e100040320015900c1180c1c1000a01005e000650041240c11307040c8161607000c0c04851292a280300b0800160070508e03079007101c406049031030340c640d084100814004921030105403580060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 308598237 1250 308596987 308596997
    0x150203090f0a0b07080415090e0118060905012d05010c0215040320040c0809070501110c031507020706020a0b0c030c09030d031a060f04053312060d2001 67
    0x681c0c0c040c001d121303a0120138151500034002c1418803104004441c0e03a40c10854500d040c100082c1040d0300b4a542803018480d80d40401e0500b0048060b200c40744c2c0210f40201060102049650387d2a52200040b0483c60350340a0a4100140036800c1001d4000000044c1c8070181c2d5038071320135600b80d801e0103c100d040042c2d0302190396040c03000100040200024a00740071152a0722580c0840b100240420b907502c0720381c440188030919082060100300090800304071402440c10711200040650380506210050601c41c0d01030191040b05010051200081d0780903c4560b0300301c0701171540d180000c9841d0320f07070444001d0a41201201241002e801c88018641200030039070f54503d44012800041c1c60100e6040c02400800e03207403041341d1112800702c152a03ca01400b660f03401d181400c1c620b4080400e03c02c1d4029a40318412000018426154030705440c604d1201a0003140c180316a219080c1c403480e0007001041c4010000c10001920900b0507910055040b6030040c5404400c01000c0341c20f0a4600c20302d42c82c1d5040007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 308599487 1250 308598237 308598239
    0xf2508090c01080c07030c1703071d0907021b040605060408241b030601030b10021608011109040f020702130f0c03090b0609150a180b0105040503100b040b060304120207150203090f0a 80
    0x510002300440c0a00c5084e1200e0140c4101d55030a141088800c0302000c0c0301e80d80d04000c0101060300450341211700304000f030310005d0810704000080c009148070b401c0250401c4000c1008100d071100028240400c40c1d00441c3d40091031040b02d0500d00c0c1c54802c60322000464400030960701d100032403a002c1c40d00b14005040100708003070303480c010400d164007140007200144e10040036009801c0c0600d804034042c0500302c00034012001c4c803082134140d030700c60145514050707a03030f90070222501c034a42c1d8142c034403e541c0101140c100c00c004000c1640034056200456440620f170061840c543c80c064465a5116684001c07550a207540d61010002002e200400c1c01c0c11800c00d0340b909551300e58a003103002025004410040140200c451b0340355003284e00030000181030000401050100b641c001524a5a40c0107071031010805000400c04034000c0c0000c8010796400c0a0007109100030044120800e00800a0550886040c2640e80d0590302802015180e54809a0000c1080c41c010f400e26a40c800d55228002d0260080b80b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 308600737 1250 308599487 308599523
    0x3032a160c05060c0604060b041b08061201110307030c03090f0f060b03060c12010906050d02090c0910030204080c01020105151003140a140108030406080f2508090c01080c07030c 78
    0x11350300a828220980c3c203e84100b0003017104038800c4001c0302c4020b071402c204805001e4a00405283d25400792014001c200c40060b8482c2e455114045242000e440244460948200d866070f00360000e035101d00c04a805d1910b6000f510f8802d10490545d10342112907030003080c04944604609600380e10003034031a242c8410320003100e0f4a041008901910071505100c2e50f595002c03903507008101c0b040c3c1003003c5027410719104110315034030005200a40350701254106c00f41d0702c4000d9242414881d21038050b401c20360030070f00041030070b4065011b00101c1d0721400580c1c070952001d4004900b02c4030101e172503851040400503450b0701810600c07241a240f80c2c090400084903c0c42a040c0040c03841e0071103040300d50503150205042450100081640100800070082d42020b08000001c1d14000000f42403100060310a00003070407a41c040000c0d142a001e00c1d070126a5403481221004264060441e0484a188601604c08a85510480031244910241d0780c2c1c00d400c0c00340c0c3d660f040740d000088550540320b911940c0004900c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 308601987 1250 308600737 308600749
    0x50d02071a090303180705060d0b060d0606080f070f0c03210f0504020a0b0403050a030302031b07120207080712020d03020c181006030b0102060a09030909090503032a160c05 76
    0x8000c05002144c80c0d1802544203010240384564661107500082c104102d281c5a0000f6a2105c4030001b10100ba40900f04021800078000c5a9091905908000001402c50341201d10180210340120840c1a26136848900b52451000600c1e031000081e40d480d00750f004244100550016103a0541b050340040034030b172103250240d81c50204a03010180d030316000d100c11803401c02c518000030860460b8143c01e140c0b4540b80da641f502c40d40140030b01816000400640381014501c014500000b0b0106e1151b1554450305065a5044440c0300d4500507100702c6101081c580000901c2c171080700c10b25003451200031500c0c0d00380541410800011070661203143d0014910340d41c0e04540080b41e00d40030002c090103182000c1070b01c050442d6a4041d9007410303e4160403c0c010303640403461941c48440e002d00403801040601d02103441f821107a014800c650b150411030410031001000640c0079040f81102e13844201748a2440c04400462108034040000c1d0400072640c0c90001d040030710303048234015414115151740e98004188 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 308603237 1250 308601987 308601991
    0x12051207170f0a1b090f0e090d080c0910030510060206060d080f0d05090a0605070504030f2910060225061803060606050304050d170105060c0c0301090c081c050d02071a 74
    0x1005c9100b202e400d00c402c4030b00d1811900117280c0c4041c0300c10103003407400800d5140c61111000c0800c210b01d11001500b0624007078103e0740c070340c000501801080c0841c00e500030024107003501d448071040e466041c002015440020000c1c01030000500d81122901c0741d5030762089a521204400f045408140403420703604201d44107040c41150310340c001c0c244c8180355140900441e0320040140d01800010700060000c1183c14140c0314a9650048502c0d2011a1000310500c11203983d0081c10a81c1d0000703010400640c007080c44c01421140160211040d00b4040e44800b80c81c0d400f81c0350104100402d110082052070320801c51121040e01100f15030b001c17240c0f6038489a0030749400d5001040461000070a100400c00200310002c1c41802c84d1500603d401c4034070b100e12042c0e00040c03041d01d108140100d421041d01d02c0521032011040c40050003045480c240c1d14091103048014807d05909005807408288419000c00c0056103400095883d03a10709030940c250107009401c80b282c15100c0c08003c2d4040341c034840000e50070354 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 308604487 1250 308603237 308603291
    0x90f0306040b071e081303020a0c140f010201020c1b0d0f06091110090302040f020904020301090c030509030f090411040308030906060910030809040209040912051207170f0a 76
    0x2641610f40600003900340d1640200101c80420221000f4080d103038802003140e00031840c031007840301c0e40c0d103142000c82c58050360f0b00d00600704503030402c000500081c04080e150302c403050a4610a0f80c4031240e100581c00c030f0040d460341c1c04841d0402c15070070785620454224002c5030782c801403a00e425804035480b180b016014002c03003111120703a190303242c10034001c207080c03911565002180c01122809054600410301103091200a000700e850b40017241014a954040d1050210080d00c00c640b2507039202c5e2008040d064001c0044007180c50a804110b04020105c12600b129402c3d02d4010715040e0b0590500c0010400100c2d43e1141030418440407001442e9a001107000703030351400c0208003c0c00c004003002081c241c0070f05000c207112024a001c00000700008255061044204c800588454072600032501404e2000d0004064019007a070b01582c0070703009005000e4110265028070150760b00d41c135040c4e500d207003503811904000c400c10380001c401620111000e940300d80c4610002c075500070801d4059000c044180d10034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 308605737 1250 308604487 308604503
    0x140706020105070e04051e15040f0f0609060620030d0f090b0f070917030d0908071e0c090207060b121e06100b0a030b06072003010b0a0b090f030604 65
    0x8464400d500000b04c502c120b604640821240c140350700487c401340758050304a450440e2040008c0c0c0d02c2c1014023048440c00402034424401884041d024a00600c036408020b00c089252400101701c850f101e2050038182c5440361034106a0b20100081d01c149030503100c880d8040c0744810841e504010401c1e0041460104600b9004113103060240b409207801030006040e00b50074012902000400f50340201c4040c1242c07002c0f0344170b2003407820102220781035108038030304c4594490502d88132400b0408018014140039000f00b5031100c00c84001e02090100c030204c0c0704040c0c485400b01406110043d100d41c001d0507036603c55040010800031820125004113405121580b19401c4010710b5186401000a01c2545104600207031a8910f0a0300d070004201010f4080d40c00000c1c4081341070304429000e0350014208000041490b900d452143c602100304090300d860000419940d0b042054250805005020050740002c044800300d034100421102c042e0450489103601403140c502c4042c0719103060006500490082e512 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 308606987 1250 308605737 308605741
    0x1c0608031c0c0e031c0e092a0304030c0303050622020c0c06070807030309050f0a050715020c0f090622050f0f220606170a0c08030f0301030f140706020105 68
    0x1000c01c4911001c8040203028020411803d195400308031408034000041040708540701c022401c0701c48210001415402210300ca081c414125881d50020104c0086040c591030301c10808500340c03400c1e00007070b01e00402040c00e4400c0080028000d0308015408071016000d86844030200c9034602071104056140a24a9030020303081c050943c05201c1c034402044107036081442c1448640d2846400c1c441c81d407024041541d00c07138050040000070700040d07414602c55001c40e43d816080d0b017800e5803201c82e02d01c5406403e00b500b00f450301c1e40500200b81206110301c02031071a044c1203100400d0207603c5c0170040200d40d03c4107800540d000f0f4541c8a02448910101c54900025146071000d820030212501801848140c400c1504022410011040200303206043d04944050101c03145060030103040c80c1e03000505044501046299040000aa07400340c160080e240407079200e5882c98455120b20440120110400040005001182d8200b940e0320a651003000c1d551610030812036810304080d07094001c0341c010b1b512482 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 308608237 1250 308606987 308607037
    0xc0a030b100e2704110402040e04060b01090f0303021005070e060403030203041503090f080c190506040c0e0c16050c03010c080a060504060e06010e031c020a060608060c1c060803 78
    0x42c48002d14a4071403510703d085120b40b90301241206005000419083d010110403107680c8658050b10011300340b03120b541e4110b051a1130450060070516001900007407030014001801c10074811020102c0341c145d000340c1228460b03070070400050500108944180200b8900460254550340c00800045020b0307806151a42e007864004114800141250820941000340e0034001c14549001e03191085d03440f545155854140942082c2003000c03031402028003918034180c40007130100c00315244d44914441e90301d094219803240600c2c0550103007031b103a10b0f842c600140100c06101c60281840c1d0007160144081307460100003000000d003501c200d40e240c01d002485c031905028003020300d800380f03001038001241c0030300652341000e036048112200145044d040080482c060f141d240c405110a000a1072031023101500d481051101950b91001107800b16003582c50010b000468413004541c9600800100d90428035101c04114400d4540550026200005603120400100f4800c1040201f110740042c01066040014000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 308609487 1250 308608237 308608249
    0x1090527060d1a0411180f0a050c22050901080d09060203090618011107030302060115091412072102040b100905040515090c0d0e150c0a030b100e 64
    0x1401c101c1c050318115240c1000185011030058002c0084200e40d08581e0711414014070000310720306402e4102c802c45c105c4c1e400000032440c0807480b5100c0c0c1d040042154407044414070495000b00c0c0c00407407d107000e000000502d1102d032668005244241c606664407900c1d034000030301c80300c6d0a80c4520565130008a9002030a500049036600804080c00074605104a00b8042112840b40390343c107420303016505600750fa140c0c1c055540740707141e4070011b8200c8021545030f00e0065a01d1000b800380040761144800602c044920500c1800d0a48055402070703060180301505001d14205500b00b516050f020300c420120755811b02c00d1180161428000d00da101c4801c481c01407100f1505100c0781540541161504040c1d11500002008121351098900142c0ca681e041c10851801002c1c1c070125030b00003a01400d1050200396803014082c005074501e403c224000d080c00c4a166614000b00c00143c08003c110700084441603000003030b124410040c00d011031038810500000e031000111003600c0010441100302400a402c1c11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 308610737 1250 308609487 308609491
    0x2011223160318081905071b030501061e0314120d15090c1e26040b0a1b08091905030307180503120d110f0423010c06090201090527 58
    0x11801c240c64104454607500e01a220384a881c81c181c01c0310076170800c00e40d8440e008a4076455080f2001420f903008901ca070f010784078034078070060343c45600f00400030401040300041580d0740c1500036640f511061850340c2d001405031041d4060101400340c03141c64184610402c00401d10000c446000042c0000304483c0b00603da00b01d0f40200348035914200030410240e40045020310200b480c50558203142d080c0400403101190b01c100b02c00400d003808850102c0501c828070255004601c6004103005a980c0c6800090448200060116040001e1502c00c040140a03030300a41e080b004480640e1003a485103400c2011102441c0b40480c1c440d0700003c108a40f01e41c0c400e803054010403a0f1101108620f15060001740d481001c030420151681c40014554040d4001d43e0124a0304e03660742200740e464191030880044c0d20b403c68858484460001c800c0c00f2140a1007c0b0000300c0600140c584070b82c6a10030307444280041c220044100d040c400d800c800490950741c3c3c5441e0800900a174912120066103e0460044140c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 308611987 1250 308610737 308610761
    0x20402071410050402010c0b0612070602150a0207050a0b0c0702100c030e01170c0c010e010e0703140114070813141e01090b0705071b0602070e01050d020112231603 72
    0xf601040c08010707039125402040880d00007081541c0c1c0c0c1c0716600011301203512041c0c0e141440c0b28420000642d240c0200d012441c4ea40c0150403409141e41d05444501a0b114488004041c2d030000d0a00400168403841c1094000c1100541103003400c690ba0f000c07a0000c104203a184c0b02045140e00c5000400d0b0744003900c45030b141002c4c6000003407552904000600f015010b4050401e004002c1443c00c00b0100c254412024071500310000d210755821035031015201c61180c0800d48031340c181e00f0000800124140070390401c0014140c400c1400355182c1c0b6040b260110f018141d55889546010f80300d011410f80700b20b0000c0964440041e080101d02c0041c100c4000740383e8030034510541d05050000e400300b03034403540c0319a1082c140d052403a40c400c814074082074504c00412551002403044000404c01d107500007403881c10b888085109240c60303601e400400c224402c0801000b030024411040c4403d1103845074101d1609030a03d907000700843c8041d005c0d8903184040032641110611051486e0751a00c40e403500031311044d207103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 308613237 1250 308611987 308611991
    0x1090501050f0f010e011422060f02060601050310080d03050a05090d0e040b04060e1306052401030f020d09080c070e01030210080619030f0c05090105030309040b0409020402071410 79
    0x36851002ca0032903d5192040c9040c01220070a04455901540c0c094180c90760300708200d03503204c428100404441072116412800c0e04000940840c002c2c0c0104d07013a007080c126540041c18156030720001100d01c3d51000701032a00c011140a8009800107042000d0584c3c0595510082401c0c40c1000020301103e13802865991254050703080c80c040359410041251480703400761000b240c140c040310042005403000343d00c070f81c59a40d4040100071007140050b00801a00348284c1c01480603456040581c0c0c2030300440b201441980140700c0d48500700390300950000690031740801003d13081a024074100c1c0308484501109581500c40007130311040020301400b1043c05400254005012541160080384180280710307188000e100d0000003044441e81e81c185e403000500c800240d07041c42d15442c7e14002c440c1700c18600307040303032030384403c44001c10316107002404141610300c054000c40c1840035a82c2007001810300b01047c2070b00295030350b800c90b01588a60004000c0f450140b403003105800c10385e80415192408003030452017a18 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 308614487 1250 308613237 308613259
    0x307080a0b150904050c041703040312020c0f0d030903050d0509130212071b050d0c03021c12020714030d14010b040315020706021603030e160503120313050f01050109050105 76
    0x300c03203503080d070300f01940655001402d6520f041c0703820000e1140e070308000c3c11200048080124920008000c100342ca200d14890000c5054000c0c0590b42d42e405503e4035684800401c0e241c04517418801618901c080c080c0c90000541a940d891f002e08120b62800c04000141e00080c12035a136041042c1036090403003100c542185000908026404004800340c080380400000024540c4014814428400c405801c1800c0d0794010103e95400f600b90f9a600d5001c030050f0284000c00c0203680c81d8903800d00081c251640310512202e034034007031400095001e401c00325140d8200c0c442d0950001410000b4000320407000400107100c3c5e00446000c4c0429105078402c403100c8504000030720001c1d0316080103090003101000056145c0f4014070f4484060b005061180d9040320031480c020080c181d05810480e4a80d00130410b69079108581101d114207002ca6008064040d440895551486a02030004580c4116090600d1034074921590f1007a0030001c1141c14000141e4540c40184201074a921990b801040e04465580f420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 308615737 1250 308614487 308614519
    0x1905070302272d162601060302030106080f060d11040905010509030a02011b1209020a050603310b1305010b090403020303010306060501050a020d0f0e0402070506011a03090a060e030405060307080a0b 87
    0x1104150f52007100b04414680008118a4404a82809084d8203217502c08035617151a0010001d4000f403040f140050350303003804205d001105022550144c80040d028000d001d00036100d4590308882c04034602e40040d03039825980d020502c203104041c018640407028641d2019102e00080c20340392006040c210801054402ca1006030300800400051030300b200000c03961007014000199490100d0b0322041c0c10900010401c08900b4081c1c2c40c0b038164444d185a103566041050420194055040340002e040d14240c0340454100f041220020140f54418000442d24000c05408106500400c1c2d4084000d40d00100040c030030032134135020311000780400303107007180c1090440da0009544680b0760000e0b00c24028210b00e14031071584940c000e06507001c0e01a100351354a41d154500141e81304000d10421003050740354601440d45a0f904012217008a460000421a200852300d0b000c0040c01c255510003040e100070040003c00d1344510700618415142522014003d02d0f041c2e40c4003040e20440d40329903100d0b00052078070480c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 308616987 1250 308615737 308615761
    0x6051e0a030f1a070806010909060f06110a02030a150506041a100e100c170702090402060310210b09120d020c070f0b0703021905070302272d 62
    0x2225088000340c0e5094110f801c042000300c08143c3c540f080d9800d06410808100c4d00301241d28002c800a0365050081c56640c42c3c00c01c111745050003603190000d0600c108202151150103c1201310395544240c030341f08482ca50010789404c0a00d40200c5101c0e5908201110b029128806d06902401c191028000b8261603951030300b0751621215500d204008001d0115003141c8103007072012a603a405400040d40010045018100001a00084501101247d8000b40710354010b800d840d0215800b4250300129104e95003001a03c1d000248041c00710101190001400d80d105214810780d0240081e0b0918480312a0504602c190170080044045500c0301c00200500305042084030a0032440020050b1180c40c440401401d2890550143c0600490750790040313150070740b24005000c00386c0300e0b800311214042d2038040040d00150402c006031158001c10310400140c1011500440000f001907401201039940c0c460056040c0c070140c91221741b01c6900102100c465039402c244005800b10201d04644902e080100c0503a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 308618237 1250 308616987 308616989
    0x1512010302060d0e12270a27020a080105090a02030f040605060a0305120406020d0f140f070b0a0c080601020102070c1707050a031208060409081e0c070906051e0a 71
    0xb02036000000e915090300c4940d070000843d0483d150540e51100d040142e041c4458101100020807540a070540d4222000003403000d03554a0005483d41c00c1c41c0d49404d83c1e452035148098200200351003d1070346514031800c188010030760260691908072941d4101002d01406003401003d140f2954030403c04d01251180c0340c61440e82c440da100102080d10381d20f14011610840b0030754001002e40c800c280e1400341c410440030151050f5229076003210701209450380100d48110121400001041c44140e00424403000e20009040c16004510040e00d064665501c06030028011680c400c0034550318070243e6800ca40c00300002c2e4008409100075420181180c40d00600c01c01113114407900e070380380d244909005060a2001500a08008020550b0b5640c1e0b420440c0209003074440c60000900c050000440c3e5161030320807204900d4000b0070060901503000500048481e100d6808010841c0a210180030b40c04c040040f00301910f40c4c1500411403515000601403103a201224000b00c0f03c040b0346041c803290b218811040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 308619487 1250 308618237 308618239
    0x5040b04170c01060b1909050d030c1a090309090f010f0b090d020402070803090c010c150510051306050102100506100807030e0319020d09080606061305030115051512010302 76
    0x4a0803046400e04981c42c8103200c1c0d20512942082e4001034260340c082d01811911042c084e403100403400031441110401818055240d2001c3c41035a4103000c0b034810140c00b0030681c8281c211a4240308495074401a0060881d00701d00700744c0c00002c00f021542420900e00750040f441e10020040c550408841006000c113502442e14800c0e400b241c0783c220b999581907032406d450740103032045558801c1401d10743d0807039000312800d146522440445005a5110320013419559400542c2c000c8440c09180004000d86809014803419051440000c5106e60310100b03004041c42c201c08c00010214a04000a418000010541000c4510341000c104041e16010700c16200c481092030031154958444031306500810034007c1089040c4408640d00281c3c0107100e140f005203c560b6021114803020010f02116646000d02894040b504004003241c45410000d003e800d2021614034116442625080460b08503200180400c04c0e07020300040c10005410300e1880300c95070b0518002c1c1c0301c1c5001d0506403801000c070b0040c4030003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 308620737 1250 308619487 308619503
    0x6091424010f1101150b040806010605090108070e03210c0c040204050d02010806130906050103030801081603030e06090d0809100930080c07090f02120402120102040b030c040f0905040b04 82
    0x1c3d07480c0680a41c440c20b51402c01c0c510000c0d01c252900034602250308140198213052049000120f1951701a00c00c3d5161070318140c1d07803000c044d0383d81c0303104450502003d580725805100f40103030304015854440340512811039081e09507407030301d10141c0c180746080d9030440400c0c011841080107100c0ca071203409607207800c5602800c207007400c9e03210400419044250002d801e03400b10716000000d0200000b5030040c0313040724020341e20921680d803280080b82c0c441c02405002c902d2a07000600c00c00009000d0b203407032610004000e02c42c90034005440085802d4800c030000841c0c1c80d82c000039450b5040d20701990700450b100303201c0c5002413007507062084041544200d13801640741e141a002082c0d404d10002800c0d8500b2641c4400041d8072103245c90b0b503540c1c1d503022034001e001d1942e051a5022015809910a40e644080c003c0030300d0300f15840b2a0280003814001600c00e402d9550200408280d50032842c00440c09800810703c0300c0e13952458000130040104803504240c003042c0c1040305100210340022443c0350465040401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 308621987 1250 308620737 308620757
    0x50601030612060c140304080403031812110a1d160c050601090b030a0602161505091002090d140a0b0108011523031006050108010e04020102070b0a0306091424010f 72
    0x280c41d00c1c58211074401800701c000040002304050580034108030791190315040c0344030040503103883d401c901e20300426182c00803c004a0001c40d0341d00803140340a40026040250190b140c410000b115038040341c3c4420109090030602c11118038202424036a100b040c0b5100b075944200360f6901c1d440701410f11907881c070f03161a6510704641d550f05102c030141745984028115540c9000f0340e42c50034011b02c0c00303101350785030000c1401401c034002c4a4020a071080100c00043c140d0025042c044034001e42001c1011394006000d41000301c00076154904000f4a0ba044000400d00407020745840c10b85100144c1200c58141d0411043c012400e41104019050b10214040c801003403505100314034061482c3e00303204d036041c443d184421489081036032050003925400e98514850740e0302c2c1c504420400c0d0055400034010380c0552001c0182480400140070129258500894010340d0780814000b503890988042c0745810451085c03090780ca4040da9030080e000b40c03500041a8030104100080c1c100101e04400038184072510031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 308623237 1250 308621987 308622011
    0xd1202160312080601030c020304050d052d07142b0204050f01230f190e160305060102160e060d0b0c03070e0303030907061211031302010305060103061206 68
    0x45501218694445149030707580c1c10300c86103a01d04031105602162070003002c50101d500c01c1c06452030301c2040b500110f141929240902031102ca071520b003502c080c002d41040440f8040c00c01141405107040303018560170940300810b01e5041000750b9002000c00c401d0380240764481e842d480000c40320948100d1021804040000c00a800f010452200a41c454545810012090008500307641a41c042c8200e01304071400c29885c03219510116418140c0c46001010304803014506800c600f01c0307902101101c1c0c10031940c0e40410a20b43c0c042540c6240c101c0c002140b000c4881a8980b04480d40000244002e1020240200104080b00320b28003d641818519070001a9542c840d04180c1d81010b46c454013240262408a84170344260304181c988200003609030406004500d030000540b070003190706002500c0c1c0c01d40340880030385d140505503003070640c295107682104c01d248050101440c401d48003240b00b0a1907140c40d2000408482c40248103605142c9007190511080c202d0444c002034060344160005205500302d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 308624487 1250 308623237 308623243
    0x316090f020705011b020601050307121101140a0c020102280b06061308011e05070f0305041716110301060f0509040812070210110306090c071505010914010906050d1202 74
    0x107a0040c09960130000071480c5102c041e17100d068054415400d980c2c160362101d040589039032151143c40001c21142c0484c0b400300300c040c4240d0381e0420050400d400c494414130442481500080610f01c08a5060102e003025560140b1900c102580002e19021010340388547c00c03059110f2175030014003411201e200140d6103031651001c0300c0102c18810303210495656551512806400d03401080b14810360522014140462140502401403410f6119501062611034040700100001042aa1080c401160103c9800c4201c4003c1040710707120f0300400031103000c50a03c010307815610f80301d05005e84c0c0340400421a41542c100c207042a0b941c11a42d903a0130f52a03900b003105060180c0e9032006030061a8205218050f074000070000c034051700740042032048032548190000e60b8001141c0164004c806640020140210b1000500c0503e01c40c03072151240c403000281e181e08a403401d80008200390ba5a80101420340102540e2900420203113100b0b0100d94184408654110010600100018803030384085840500034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 308625737 1250 308624487 308624497
    0x100c05040b032a04050a080c0913111f030506030d020d0e18010603091403070507060e03010f0e03041404021603210e010902010818120d0e0709090b060316090f02 71
    0x15204250b141004440703e05282d00c9407040c9482508901000076044901044c3d0100b1980000c0c0406c0007503440b040040400000703103c040f90714034070b10601d048044c0e65088600010013000740c06005d4807000b01d04060200c07000900740510075804016440482a80040c4485a1200500e080307400c3c41071300b001285c41c65901091020b003c0000030004a03d0991540c806500103004aa035400f04421040c10203407030780316030b50028140b900004414002076002c1c220305100310f41c0241c000510404201804030481d007074070080c0000c54000040030080069466a000031010084408500d81850580b01c2c1040b00c00b40f1000405004544103c000c0d10403948040c107000000a450512500e6103071401103008140e40d100490100300030b030020404103000c40032070181c000842c2c0024420300940006200050f04903003612140300b602c03403000040b4a48140203010080c4609103001c211007610345081e6851507001000710b8000d42c44440900a6107445600584c12900c0d9032100007000c0154400da01e010f8454 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 308626987 1250 308625737 308625781
    0x12050d020f160c050d050a11060c0a0f0b07090602070e1b03100e0c03010b07030e060c071403010e010e031602031005130c05010509060d02130e1008100c05040b03 71
    0x804118141d11a024010a549807031141074405035a540303540401c010580001c10150161f40400140d200103103040c1074401c81d04800a05003810082c07910403c0c1d00e004002d1100300c482c800210343e8170301041030721107107642c01c40d503c0c1c1001c01405040890096550710340e0320810300d80303482220110f00b12405070b40b00840c0f098040115140e1303e06c0d03c48400344e0003104512858901c4110240003541051040341968143c0f00704011f26031404140d44c50031100c4500c5100d03916841001000200c810740000c10207540108201c103040b298070a2030204240c212020417801442d580d041001c138144d1240048121815039841100c01c500f104001d00120b440c040501800304000d502c1c0100740003240764550880400c6034420340b01c800b00b03541c440d001140c04d8040d4034206504a2001e220b1659103410070b4001c2c00b800034487c03018545169441c02031051842003071320307008262083c0c3c15081c040340790288110b14404104000038400750a4608c002004c9104070710415070803001c00301c00714030031018a007082500310702 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 308628237 1250 308626987 308627017
    0x1051c030e0a050907110615060406082809060e0a1e050f03040605180a060e042a111009020f01050703030b1905030d08250215070e01030b060712050d02 67
    0x140c032130b2001d016030301030f4499070303003244547c40008800c211006507038000580007a20b094241803030100d05489103000600026038001212054001580500310744012141c40540041104141801d0080844e00080d130b1034501c0d600710321050404110000505540c40c042c80074620100001c50a0080c14201540208051400000350000701e84c0e5100000c1c19400d9485009c01085108803410009080400e108090100301c0203034048295280503403001c8095888042c0710000c4446080b09014a409019000b80120310001d419440c100010009010041104c4a0802c030f00815500050443c0c10f47c10203d5042203400030311502010301c00d402201041c08058104200741d0b07110f1007892903892160180034080d1103498005001d41d44241c2c40e141c01210000030201d1500442d5100809242520000109601c10060031900030300a5481080c800c2d501943c0d0340c0e0340d03130700290001015212801005486050b050000c840413078464403031103412003158140942e0306c0c007000000c040a80181030341426009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 308629487 1250 308628237 308628241
    0x70f080a030504030e0303030f07050a02100504080d0b0603011413020c010516080c09060f090604030c060305041a1509060f13020717070c0b0901021615020601051c030e0a0509 77
    0xd034240e007005014903c682c49074070300021000140360f40ea00045410039502d02c441c1000c101002c0c0243c00030802d10a20b44140c40711103070084003001c29a04195030441b680040002c018044c0500c91169410880d000c58141d4510b515024a00024110f2050340b20f10a110080c010b02c4004050b074120307000c14804000074015468580fa094541100002014001c19900c3d00082c401840c0c440403580310000083c00705003403000550314688680c105500c46500008200008800704019a8190004160030356011500d480e0610305807010358002d1840341c540d13540701402d00010280310303d000b401d83c400590380101c41d9641d4400140d000d01038801c0c0e10f40c11100c0c200301e4000100c0079400910081c2c0c06800030f5013000c1000314507000c0c244075070140130702001c2000a0500c1804a01e90042021100510440c4d0f1151a906024008808941d020460301007041c0d0701010ba03e03406101045c01403004a8000d5100e030040c2c1100c02e00044504c8004040000b10f4035010640d99407280c035035024110180c400007441c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 308630737 1250 308629487 308629507
    0xc020406060e151603120213080f070803070f0b0a0f0f020a0905091b03070e06030703060915210204060312050301050a2c090a02040e06070f03050912070f08 69
    0x380c82c5014901e03002d100b41070070980f00401c00c101110b00420030611980c10594203520700302d88580d01034406982890702002841c4604050800324005850b00001a05001c200e80034020319004441d4003007034084e04140010b002041007117118104094100140c000c2959548800b00d005200c881c007554921403412000301040c1286074003904005025031581c024440e11402009244201142e40860602c3d0b8640c520f0f000761084805190004002d007410345d2000342c1840061603a41044035170a001a031384140400c4039174140e0189105c907807000310000718a1800c00320180682d41c00550000c0e0004900700c401c40443d00c40758014002950401b61304041d0401450004010381d0003803103014801e110021010500400c1e0300c0d03d821102c1403003003054074a0712440001c487e6800e8005c0c8018003134016135000c5d1000d0303100e50098542ca00b13441c1d00903012901d06014040c2400f4041c12404003010320746410444010700005480c04501c0c000780c0080e889805a1401d00303880683d40c0402400c141c0e01151013060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 308631987 1250 308630737 308630747
    0xd06060b0417030903102705100c03050601120e03072a171b0f030d09030c170c06030408090a030b060f0d0b070e060d0c0801080c0607030903060209010c02040606 71
    0x1a542c0340581c50048807881c5503519038a00940410070340c180c020100178038800046034030694440e2058200c0500e031b40941d4002e5140040710302d0043e139154000e2880000c0d110f80720700c280c0e40741100707900b8200700c3c82c284003000821131254280c540800c250b0707651100c8440401003098650207580001c0d0300081c44003a01103000107904801c03000241400c0c0240104001008810203803401d14008020466150060703030007801d04e080c45a80c0350708268000200c3e09691000d100c660307504103158443d540030300d1452600185d40d54030fa5000d54a084064108040d00200100300070a603079004540b400d480341c50340e0074414210b1150702001c561104c0b01c52000810448a401c40510580b41101c2d0640c401c180d140070f002403040011030043c06042c001001440300f41c010f04690040e00c4015240c3d9003804d907548000012100e01c0084072000c96100c00040200c0c8004002d050012902501c5040c2841c400e9580540018400c0c0002880d484d00401c0309002c0e40d01c117041b00441d0a40040041c0205aa22840605 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 308633093 1106 308631987 308631989
    0xa12020904020d0603110102070e281503050715050708090418081c050105030309011e120606030c03180209070f0309061a0907080c0301050607020d06060b04 69
    0x1201c240a440b4030b40c06544525078406c40303040b900d400a86400d041c0d9011100600c2a80e041100ca46210421901002c4a0b551a4690103c2e44490600a001d80c40902ca01d445040c0c44000b01f4031400040310b00c1102c0000410352152107501d1011141445845d00c05041030380d0402404500d400e1541c0481c1c41089400c2c2c820320142ca00741c1d03460005600c5101768156501e856074000c40c01c43c0003480740600600c2e04400a41ca13040042002030114050b080d0030040082d249101007854500520b255000c00801000c01c012031600d540c0040c00802d00c0194a600080c5042c20038000c140d00b8080e4150300b00e030010000100e65451142c11150804001e16080415844900100c00181d41c1c0c000c92403141d90001c548071103400743c0024490303185030081034901045138030301c1844034034070307001d41101d0559200387c64a56981c41c1c140040f0327004000b4030500400342c0c0e10304200058070092120240c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 308453237 308633093 := by
  have h0 := BRFrame.cov_init 308453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 308453237 ≤ n) (h2 : n < 308633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
