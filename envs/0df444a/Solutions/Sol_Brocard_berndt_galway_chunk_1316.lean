-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1316
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:20:31.583018+00:00
-- url     : https://prove2.me/submissions/364b2349-1ab3-46f4-993c-415e6452dca3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 236510791 ≤ n < 236690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 236512041 1250 236510791 236510797
    0x60a02010e10020d1d191106040324060303050f0703024201050d06020a1209060b150310090b031c0234030b0a0f14090c03120904021804020a0306030b0c 67
    0x81c1c5c1903034010504445191080b24400d144450003000c00000c40403d1001065659000e50015a09203208002c110030388228610380e5103620034034000c108650380c61520000d146000300d80c0d0300b01c1c80170000511403051602c2008990114441101030030111a1690700300c02c00f500380069004030002c82202c00d031000c000c581c11542d040782c4001e4115880384c2069a5544000c0d4000b8003000280b1a6000b05101120074074400e84095512903180001d280c0c8140c010491008000502454180340070000c1024480c80011003100710b40f0319090100d0107003400d80c0007a0419400f8030501c0c180040f44c1141d510600d60000d4600c14a0100d045505000c0948032460001c070144030910848101300284100001603035007802c203602418003000090a0102441e00c0c0003510041c08900400b940300d641840002c440c280415074651800720000c0102500082280f40036000300e600240c4a194007190a103250300c44161640f0500314020070456980c529007001400520481c08265036250004000501800c0c000c421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 236513291 1250 236512041 236512091
    0x20415030204110304060c1107050f12060a091103010b0f06030a110703020706140c0a03080603100e15010501030912140928050f01120207110a03030f080a02040f0302060a02010e10020d 81
    0x4d00749e03060038401400740340140202110b410142d12104202c0605052100398010503681c24080307800b0f81a41000e2040000340c102d068400e034980b1221556650754142103c00d030401c1507e50b10348035586c0c040c8400051403072403c14070725a0f800040030010164007280000603a02951503550030640f0381004154140140307000b000a980c0310070f0441c000707c1e000d0701c80664132000080c21a540340a04950540c26244240d1140740641c3c80740c82d1140f000300f907010b2420b001d45001e183c100118000c0341c884004510a1145032002c1c845a01c41000a40e000c0380101d0b90407040103080740480c02c01e540c188403134030702c4401d481004400420f00c1c0805c0501e030206481054140503034800031b036000000710f902c001358001101120f501314184503024036900e81401900056020341c440c00303845500b03000090810000101007000251042009101b00c0b454082002e05032a01074a0442c4c0301e40361f25000342e0041c100100d035887c0030700c038010084040945d550010950283d04e04000d2240d103e80c0c0780942008194400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 236514541 1250 236513291 236513293
    0xf070e0406090c080708011509020901171b03180d020606030318010e030111030106080a0603020d14030c1005090f0a0b01062102070501060306111204020415030204110304060c11 78
    0x440e011510903000410043d0007080740701c2500303603101c12441ca040303520343c8241040d035124050203146004d074689003070092200c60410b5260102c1d4000003448013072650118440f035030302c00020500c140e4070091020044001300322290f0307890800d14022112a20b000c40c002c54544111000301048070300c04122303107000d258068011800e042c42030111411140764541d4082c10046103920840c8959424015040b00b614030884207543c80d41401402030040314014800345800d802c04400b040141c507007040c03410071141c000800c4842184807a000d030741140300303081c101c1041c2d100e5103100718080000c81d4070441c0036501c1c0c00b00301c0c1d040b035910104d11034440301f006402502441d01d001c010080513010394000e070708810030000c841c0044001c0454001c100e070000030003529035a540ea40e0500802c40c15200d00b6104100b8010302509041080c2c00944d80d07141c0c003c0c0001e00460b00c801554900340704011100001d107900400a000501c90600c507a0f540342c0045500f6100e0609000e030700e89085001d031020b810b880824038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 236515791 1250 236514541 236514569
    0x5090907020a110112140c07050715020c040f1e050601030e0a0b060d0f12050c0106120f03120b0604090504060b060a0804030f02070e0c0a0e09060f010c1a04140f07 72
    0x43c010356070165440340300e5481645a054000003141c00030841485001030203200c2c0d450785094240140742c40c000e90000c020145800f0781a013205a000221440c041600703c50104410081080501c050701c050540b441110340961742c011030880d856005244a49420baa00300122100c00c04481e5036582e8030034014004104070404600c0508015120740161400303020065006a5155110740d50301c00300250341000180089003501401000707020f500001c0002c0b0004810744a680c0d1a003200a001d05c1c000103090000c40d185070420001190001c031204030004205030b0320759645140c0000074250444080714041c0ca0031245540e203290800c00d484803a07030790341c4d202e40695a0301e40e001d884c1c0f000c8041c0d801c002e512a8800016848076080c100340c0c07082c1c006030440d5446018054000d8400362007040301c03510a220080030411651210800c89004203403d280408400c00541000512200c54401c0d4003c0040300c3c1007004184030b0700c078180c0404c445a450480d1030b100c40424805450701c0300d50003400d012003501 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 236517041 1250 236515791 236515823
    0x1803020a0b09030405060d0e0c1c03090e011a0903100c02070302042012130602180f03010e0d0f0c0b040f1a06030604030c0219080c18060603060121020a05090907020a 73
    0x50381c0548c002d070085070222662110f0500000e506a400714400c1109121010702c0b100030540e02007000002000c00420b00300d02d5504240440e844200c102241f4a66000301181d01486c1e80e50811150100301d81e040e104005004042400030340b14040b5001c00c0c2d004c2d9080c800c03400c80c0c40c0101c540303816a4504448400e402c2282140007030003200b4002c3c0c80d130040454030412443c040342c0144010316951107004006030a14a029051004070701040c0c0fa03162190340341034210403600c0004120010101d5244c1b818010b803600c80310056881c20301140014003c071080f80200001c00c0300f100400795825004551034205040528818400d480c4111002c03600754019202140c0000c3c02045c180d43d8941c0300a1170034a25124a5114098929440d4032401035544016898021400d105c440c1d40020b0368002e0640030307645003450100d5501d10024004a0401c0300144a6000c402500c0c4645d603000c40201b01c0c155078a006400004140d500040d125502c51121040400c01c6280009407000c50185e1040200c2044420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 236518291 1250 236517041 236517067
    0x1506020106090e06041124120103030e04151a0d020712110712120512040b0402040506030c03061605132706050112110c0f0303090d0c020a090e011803020a0b0903040506 74
    0x918036101c00050243c0740d0000347e540510140201c030594198000403036146041c02801c08048061050190b450200c01c1840107040d1945203081e6505c004200c40c400e425520303040b01521070300c90240012880811500c0401440e803a180d41030718010303542c90745008011501071b41c0320700842c440e0204420550801c44001500170104001c44282c5003081c03801d124400320050305455040710125103c2c2c05000401045140c5171143e503400ca242079004000446510010a0b9a02405000888024620f03c000a890351080003181d4192011140303184909507109040002011569108401009000b0f60301ca014001c5105840480d030f0140e44540c010311110f030340d6a0003080c83d640c02962503481001002144c9000b080120310356944040111b41c0da10b0124200c504140824200900b04a40c204222016980300c0b2110301c143d560012001406001c610000c07401482e1101085103241c00c00700201701815000315182c0750442c010141004281d560819694403807051740141548050280894040506 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 236519541 1250 236518291 236518309
    0x60c0f071202190b06040c030204120206030402120304080f07150905090711010e03040f1a030105010f02011407090302011206080d030207031205010e060a0b07020913061506020106090e060411 84
    0x410742c01a149442d00158242d06040500c460a441480e000700c28081c0508080c801c403494402d039841d04600301810070750900d108021055029102d6000880850159618007441d80c2054031403a0072255034998034180e10340c030381100c01907446150040c8140060001d007000407070350101295a0780c0c2200c40382040208040380c0c00180900c0d0400200035105030001d00244221540880c1c403100560301c1f645851080c0071006001e4101c1140640c0c410107002c8400611801d89041d18404d09040d0500900c4000490050103048459035414001d042031000482d000044038094034002e0340d414010890110300303041903d080e4840c001180d4000442203008500c20380c05010a41e101c0d18103240c180035401c80c07400681d20280c11502d01907a0140c2405817034a0522040d00040a2400d00907003008401d070001504144020402c05503040c181d401b0300200a0035a216404000211518041083d141c110082c020010f9004402d0040c1c90410400981100050090702c55503011400d03441d200103080034042c1d0f400b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 236520791 1250 236519541 236519573
    0x140306220b18060103030504081605100f050c010c0314070309123002091011150a0b061c060801090503030406020c2112070306030b150109150c05060c0f07 68
    0x1c0c1c820a01e4441c0d0b1030341401018001e60080c0e54054881742402a43c2d818150221404070000e5007000741000a919100c000751820348141c140844001c1652500303940c10b2141034150990340d4a042c40b14000160940d0040f889000d10440c0b44502e03507101d4006070b0450302403000150908070150105015180724454660007907002d26080082c3c82404c0b0400a40d03e0300d810418420741d5004a001c601d41c0c00d0a601240ba00c2109280588101f41240105a01e83c88480b0104028840070300011300a111150411814410f02804060352200000380c407212650501c0003819081e407d061002591301414006c0c1051507802001070351070740c2c9442d90303501e000f075018452481149c080c02090701c1c4011030a00f1744240d105407d041b501d03a01c01c0c54010786c1c035121100901c0d00040c10300d800000c0c00482c6030708a605a002e40000704080c440c1d100000141c5506030b10f030b0700070300259810b82d2142c04182e51040040000f188114101c400b01d49a24240c03808030b00514081c00030144080c0611008281183d104035514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 236522041 1250 236520791 236520811
    0x6090a1d070603050f061801060c11060c01050f0c0322061b120606021906020706090b1f050607050d080421080403020d0801030c060e0103060f140306220b 68
    0x18424100c065042400030761000d07000c030343d5500c100403a103550102d02c01c0c0e125000300c403800f03900c0b03d000c0210a0001c4040c0101e1303041000c442c186d00d04000a2005110206500404054454201e00358a030b019100440361a02c490358400701046800c011103007500d0191a65290068250f040741d55000c071400c0d00c034413003a51001d441e04c0700300700e03084c9150321542e20b0311b6140d507100c4000d10b6a080aa50999556034407440440d032040f06600c0b14580c07903410f1170040c2030b80204090303915455410544090081e040020301102001c0c000e01013003401d01c1d80b0318402d403852658040401c994480822080f4040c030440a4401e400c801440c0c41070520400c3c1030b6502c94416000e032040885094451000107410340ea405002c50345110030b1000f4183c0400c6091010022483c110b000f943c1141da40c0d101060f4540b041c142072025194111040f41c1c004e4000300d010b88a020300c0c0d140c0d174a0382d451280010118107002980280202800300f880b81c40c0041415808028202506500070b485686080c58217000800340044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 236523291 1250 236522041 236522081
    0xb040902100203190f02210d0f0203060a080f03072301020a031a120a1205160c0501181409131a09010605010e0915060403020312070303060504020306090a 68
    0x507900c0540a02924000d075000b1920f03142c0c42500041d03845100b00e421803d11074019510710000782d0004030b002d007110040221040d910032900c0350407094041c55850a444c503080011f408076940465024501c28401111565203140e6101d88054949003840c0440c000307908100240404580c189405514aa00c80c10400c44d0414403405041e003240c00680c10030001035165003408140c4014007007240b42c5078200301c3c2c2d00d030041c1300e010410650b01d41215800422001200b80c95900c0b280c06a4141c039080c50a481e00054100042d1504440c19102c50040303d021801010042c040003000b06c0f002c1065801d01d10400346848101420001d4002d0001d0802e000c3c012400c40c95800070720801441801c1c8002c0c003240d120942000081c09003502e005400043c100240301c04066455514520101c0d042a061107910085500b0003001c90070030f2140c4d410183d0035119940d501d911111141c001003081740d000e41e43c03c000302a240d008000580c407040e03c4081d8401440c0000c610b07a1700716a845440b1034407115400040f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 236524541 1250 236523291 236523293
    0x911042d03030e0915010206181e030403021302030105090c180a0e040506090d1403042603040302010b0603011215090605091e0a030c0b1003050303010e0601021c0504090b0409 77
    0x851510a4004900040710150030f91101e08040d0805a005106408803d10034150000001e680d900020103411740c88044030a8102c00810506c10245040d2131094000701e0103e10185840c1eaa034401d2004a0280b80792040020501c41284260790684500410080c104d4480580000c1e054006454a403010030390040d10482c1d641e60662035000805203842503201500d8581821420a5002040345030242c20524031300981e1580850701441c03030180c00c142d2540341d807500d09080716482c081c0c40345c01d036501d545407180c2c401c8215180007a5114030f00c6030f8000d11440c2c40e0a070510429001c207204400c5080f0040f200d2400241251762110100989000005152412034441c003094420540315802542c00c000d12103850311b29040380d100d040c04501030051441481680d00201260800340c00540400302c1000824440a0000c0920b00115004000c998803035071146402d54005d102a80e05074050f11070105010011003110000a240f40d450fa110581054a0002c800340a170050b0026a640076640d60380c194 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 236525791 1250 236524541 236524619
    0x1110301091d12040501050f0708040803070c060215010312030e061008010608070f05060307121a01110c0d0311010e190201090b070c05010e120102031609091104 71
    0x14000d2492620101d400e4120300e80d2500d081c10102c600049641000000c02444100841101e080320401c0c41c045680d01a154205001030090260040804a000500240824001005d05485400ba05920b200e441e43c0f002c080c1e03512040007008002801001c401000032a4240c401021001a1803c0c0802c894058400300e50405904035154015a0000d10043c4041c070b00c24410b00010f020080000c003003a504110640640003641d04c202e61150b100040040c01c02e40c4030783c00120340c210403548280302000541d94162000c1c00400321440c0024140c1c01000c040f5200040d00130200308018101c0400d450a0f614200c1d60009000c48030146592641612040c1050410040000e0b045001c00c2d561907401a200040600300554000364400341c042c00343c0b8004c60a03441c128400c0f80c2003400c0483c604601140440c100c45e907200e040340c3d0039500c08820003101c10401c04040d140d10750340780c1d1134982060729020304000712800020b459610302c0c0309001c01c1c0507450b5402c080114031004c2d0810b00c40854841341d001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 236527041 1250 236525791 236525797
    0x20408011401030c14010c0609110d0c080606010804020105030f060a1e08060f0c160303090f1101140309070e0c0405030601150905040209090703090c050a06020703050f06060f120111 80
    0x61603441c12080010028481c410071200013600301c40c3c2060740c0901166000800104aa038030240000d6a510a2003003004991000640005000f4050003114061420221803078000c41c41424041d020341c0001501641c42901120b102e181d05846860850300c0e2502c0d00b0030118401048560001d40062000c1050301206461155400d5a18400b44441d420885958140720010780b89001c030034112810301a03507c02a9041d5480c01c803548449120720b1b00e50342401c801400b40b40c14050207900d400c02c0b8400601008514481c410b990a0303e600c2c00c04c036480072103901c45201c211201c9072503801c138090500011004000d11394200c22201801428207440d1000242001000c1e03202d01e8507001100c05c80745041d60842c80c55002001c0460b011420030103001c0100d031b04804010825020143d844903030030108480e11030840050000139000b60300030382e1980e20195a500342d03800141c1d042e2040c180488a1400f000070300303d2242078090052040c1d1540e100901100c40d040c10703a4148655262130a1000d418021005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 236528291 1250 236527041 236527061
    0x110109020603160e04060302150c01020f13030506070e010816030f0507051b060f010b0a0c060c020102030a0b06040f0324140402090601080f0c03100902030f0a0b03031201140402040801 81
    0x24030f6003891a1010300016450420300e4040c9007858401c00160707a4282c0c00d0311261501200980e6525403e000c21802031080d034203c0c484002000c14018400d008482407441524411411141544c551340415030b8440e5030688200d00043d000740014485204031405000c40116504003ca88851400c8824040d1403080703c0e42c500007840422040702c0803401c001c4040c07a090641d0040c00c85400c214a04150140c4140581c08010030001038100b1503912503070b880c21071681c00801c20001da950002c8003d001c4d60023074411a00075401c1c91031205080c50f000b0100c07800c441400c2201c070341c003500e5640c840c1786e01c032031490240040c4007038601c5d0600c0340102400f90203007000d07608039844090301c0c0c40c0c410403460f00e6001d800700381000005005c1041c03d003840502190082c40400704a07880e40d645103032500165a15401c0f0401c907500100900034a1041207600e103016520350300d01440f60300250300906949010300c120b00c1c40b0600d441300040200c0c1c41006941c000f04a0080e1004d0310302900c803d01c1c00d0941c1e6a41207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 236529541 1250 236528291 236528311
    0xf031a01140d1a2e08060d0203030705010920010203270a09020309060c0f031f08011103090c010509101d09070e030607020706021f0212010f090f0507050406110109020603 75
    0xc0240454a084c0780701070740306034207421806030708035601c010040d460000407504800d000d00c81000c11410f545000440d10f086500804480d40c404c01850114042c1c44070301030848013881450300510b4a204117110100c040324069000b5800c0010405600c01400c000f56159545040941106055a00c401840c640601042031001d40d0341c0c10010078061034074100615402c1112424000510000741c40c0c2c04032071300490040b4501c8812000203509c03c0081c24280d000c51200e618114030419803a644602031803050b211078040c0c0380b00c907990000542d81449400720f110b5001549100b8850510b02500c00c141030000c41003182c01100700315a003c15154070091300c1503808249107900000f00341c507080050940c4040d5600c040e00d0500d1a121001c0d40e521001d00203c0c0d5200c401c034048130798120303607581504c0510f00094001e018550f9501d50014080c0c01c03d0062404079400d04007032142000f100e004a5014100c55517030709190a103801e8040328580030401540b111035407503a201d0340142e61108083c50107101020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 236530791 1250 236529541 236529581
    0x9080c04020d1d030a0e061c020a020f0105150a0e0903040e0a020f0a05090f010306081b0102030909040c061707050a0825050315030f030904020714060f04030f031a01140d 75
    0x80805083c10080c250780905c14071f400c000045d1810008d130074804060714001800340e100d8801d10401e03070500c84001101001507103000c081007410311a44420700041a400d50f800702103c0e07140c0b00d00c072982000c00c441c1c640c100e90080200700614811805d601e81e00c0301c0740c40c0e001424a0102010400164403444103140003e401003010f41c1c481c03401c03d400c86200307402420f00300445440c7c0090692100ba0b030f04001007240b0f03403402d24235206034000c0c01182c0303c012004040021616280c940144900100d002d248001122110701c848400403180c443c2c0d009030007a45490b410200d0716941181e010800074058440c060a0311442104481e0841c0c01089800729070711595200d1178007480c0d200418a03074400242c801d511412007080e08107004411140301c48030550780517907200403078101001c0040c03507a07081507800e1084000b0402044540204140218401d0b9602c2c030081a500404500707448007041d80461049550402a92940c0a2038100350b088003011040d80c2030036440c81c5a10300b03e910307240a24025074500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 236532041 1250 236530791 236530807
    0xc0e04060605010201180206090102012007030207060507051504150203150325030230010603170328150603060f050603270304090501060302091009080c04020d1d03 72
    0x203800303440701400d4207100030800c001b441e490701d107080d5600c60800b9004000c00078001010364402c1d0415241c0d40b6a00e41400060071507500800c046a002c99070075030050140741c5001c21854414812101c0b0b00703403c60002c12101c020040000b02141c409003080725111060a083c29040000c0c1c005180306600740c010441c0c01da4284805d1505284103d0200352083e41003030344600c03100001d240da00007030780e4040d5980741c00198072001e903c00314181240c6030004140c0d2100701c641c050030150480400d5a229035207050b007079103107002214054042a0750800000c03c002018440b40f0302c06140804090180e223802103101004006170310320b8901745402072000a501c0744070a0150040c200151001480152025407461510030101811513940d8544d041d42c104100e900e46003104410000c1d1006000110010043c070f595800010700254040326400c0d01880441c00f100030003e008001381c0d0101c5c0c1c9610050180000780c601000025400728607070742e0805030b88403c0c8003510f80d0b4541100d030507909020011540c038055 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 236533291 1250 236532041 236532053
    0x513050d0f0207090f02090d050d0909090807020904050a02120c0f030601150c0f020303030a140906062b05160303080901061235091002010204080a0b090a0c0e04 71
    0xc203600401802454003510750407030741c0000d902c0111004c0400c0004d100e070b07031114007401030b00c610540281d00c01c0c01c000c000014014086045444007845403100e080f1103070b440100c0e0b000d9802e601000f82c4803010a01c20f900240c20490011a40117100300250303040008181d0000e5a058005900119940d200f04410189800c0c841d61710150a9001c5004142543c0350075400c05141075903000d6141002004828001040210171036603110035401010b4a0300c91604001140003004440a55280c12152101007003118901082c003a008000141c0440241140c04120706c200702c56648001900903800c101c0100420018410740c03590841c2c040c0c00e0030320300c0d00d50b0400400300e582c081c00c0421103034034080c0f00f00112058a0390002100c1d50104070b000d000340a1900d8140d481382c0c0b4201c8100b08102801c2c04c8a0f102c5007090041c0040304040b10603c224038000c1c2000c038200c1c0102c0c05a03c078140c3c40745c0d21031000b0035283c10429520a8814044a0041c0d8056440c0e200d456046d40c0260101000c42c000d020401c84d0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 236534541 1250 236533291 236533303
    0x40302030706060e0a0e012f0f0a02100c05160305160b04060203040b06030d022107060e06220807080706020f0a0f0201060e0403170403030b0301020414040f05040309090f0906051305 80
    0x290f1001b44050030020f2080d01100400307400e40c940040030707123162110003601e540c1540c8000062804c4680c4600041c00c0180d2100d481c008514427551611417128000c40c0a0000e450554410f02180f014040c95540c003600c07203507c124100702081942032503030000a0038415020344180e1003608096100d04007850300301c2114a000c1e00c0c091094101e40050000b85500103144400c002e600d0800000c00c10107882545230301d208500010348441c1c1402d98079406c1d4280000c00b20b0140100801486107004820040404141f03042e1008003201d10030011440807038510f00140480034010780c4010710f401e400d4030080300a035124440c254042501c8002d8040720580a1180000810381146414494906aa0014444902c144100c5104070500000c6802d061080c0c0c402c10040c031018000f15600d40d1514910104108003a4295125a080000ea202c290368070b801114042c6506031124507606080c00c2c030100203020b1083d1081c042a40e20031101000c10640c3c05004c0c001c1d40d00001d079503207004035802c213942022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 236535791 1250 236534541 236534561
    0xb06060c150403030b0a03110a0602010c12020306030f03030f1e010b0901030c0908010507091a0408120703180303030e2a040b042a080a050915040302030706060e0a 72
    0x18410321514108080200e20750031180941a10030030a40d4603440c0582c004c2501c1094550450107950001c030400c03106400000c1030500448918035815a5040704a007a00c070800042e10005010f40c03d10f030b28a07074944c6c01a681160008007901e4024600c146128076541085035540803024491007030102c104120841910340e1405903074400c1c0c02e98102a0280c505101340c00700b003410183c0e0f500c0d6882c4194441c18114001e4040800284403d051000000b4201d800d41e0203505001400e00035660048810042140c00700c1d4102c002900c0e907081d040d484000e043c1c00004c01a0309100c100400c545c40c2c0b5512032a54401356100e510001001140d041c4041e250803015000c0b802082e05c2c00905c41030301c401c0c150b91450000c0b01141d0100782e0320241c0000c940a0040c1a07001a2043c4e0414000056a04062500714003142641e40d41e0b42c141c2e035603003c15829103406076078288158001c0404030100341e01030b40001d9401070190040382c1ca000902d0f960101110700c00d40c003e0b14905d0305441440300006007070150311040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 236537041 1250 236535791 236535799
    0x30206070912020f0d15060b03060102160f0608103203011404020f130905010921093c060e0a032003010605060a050a030b0a15120f0f090b06 62
    0x2c034400e603000c00d01492208201ca8130030841e41d100d5000b0820b15200b00f5a1074011403034140061659170f001e2a100f80c006a51031405402011030ba2134121000020140c205d800c403c002c6251203192880981d0a550050203103464401031980214100184e0b1054840007040140e1054130958030114080c524001802001d21a1741440301c94409040d000c4459a00b154044540350040e61103000055002402000150116800c129154050100652007a80514040d48280c020402c0e40c2084a0060070034107002c5010405c2c6170400c0c07000101030303401b02c1080045080c221a05036100b200404028621841d4460314502601041c4005540184401447d140650311484000d0466503616460041110051907030103001000562503034007500810300510015202d103542e4480500018240e074000d82c10341c00440c1c01c0802d0311100d41884c18807042220f68003192050300c401d002c141114181c06006802c2106a202c400a0381da0b90f07600d00c1441d41c0400c0b00d441c00036086030359140410b02004010f02d07071881 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 236538291 1250 236537041 236537069
    0x91309021c0b061c150e030c070605120a0b060a0e031e0a061a03030a050d11040605072f040504020103062606150a0b03040501140c0c1b010207050f0f04090302060709 73
    0x5c0c4896003054000c3c0300c8090046114000400300703d00d1400350518000c424400e42c0343c00215241c010b401481508104c0600001c075980c0c1441440035280751116144d0007000c03c1002e0042d89121b5850400c003a80014141c1e4180c480f00b00444481d1842628440300b00e411003481d400402c141d0344240c1e848500c0b0241c07140580a04e2400081d124000e5006e01018041e0002e18440da208031a801515580c0c004d09929803035644404004240c0e0704030001c100d4201c0000d10020b05070b08400c01c00007002c0036100303016444d040d61480500c03001d094040c1c000c90516849510104010701403c0c80424010b2007607562203060881004030f10b03d00407010740340841102e900c0d18405415202c800d480d80c1590700b0b100d0700543c1c945507071800754018807003000011201c0d1300781c1d024850168880f03402080f001c803280040700c06822810b109148581c801c10911070250303000c000c0410041c10202404460781000038101d000b01e004403004a400e6030103d46048006801c44410401c409400034084000b4000c00b0305a901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 236539541 1250 236538291 236538293
    0x3060907032009040912021e0102090904301206060e060901140d020a0e011106060a030b06030f060408120705210a091b0911091309021c0b061c 63
    0x442d40488a07486207503000d00080761012034485800502074168402803000036150540d00080d26624403845099034040035580300c12407200140240c8a15032001003982c0c819072100c0d6501e40f52801e5403010b40c1480001c000407240300c69640c00d8016010012525000190004060f54a044074407541113081403004510580d02252124015030b5100103080c02c1500c0304d1605032480d5151070040c462212125400080d50f20302542c1c1c00030050341c1d190002e884210540501244858982e10304640361604558001810004190300d48051900b04402a0035501d0855a00039510b0030a90110f50a564a500014004801b50702071a0880d42c4a06146407050810308041141e2801b5605030700038401503003201020401b2480c1c5030784401e40036584103000e1002c1e010030807012021103c551080d8419140751010040007103420348126140d81400400105100d54103080c12030041c21910703000e0360806601c1811400321512070480c11500c42c01b901003c00c0501d0a02e040241c00d010f1120750840c01795550000300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 236540791 1250 236539541 236539571
    0x3030c14070c05120c0d1406011401052a030a09050a050402090114031b0a080405010b01020304051014040509190b01020d0f030e120d14010906080a030f030e120306090703 75
    0xc1d03e008075144804c0600c0242014034003180381011590042c126059034042144501c40d420302c65404401360b811a030b0766007600c0d079004420425203601068042101c002d02052940e12071070421400090107040d200f0445075a8595041075100d8070120301c662a0500440c40d001d43c94100525049906510749102c0c0340008006802d110040d8280d440040089142c41082c01c00c51203903041d641c0c2d1081e4580c40c0c803980040c004042914140e840f94600220900e495102001300d07815180007030303d415000510410f0888d64038405400c2e2500c4490300f030001141da9900e61060a0250903101040c2e071460aa4107030030811075410b0701005043d5072110600041880c0c0107010411894402c0c100010301d00304210025007010300c08190200c0d001000240d581c0c1128159000e65404881240c4030001682c070303442640c00f1114940507001503a80042c455400203841621540d103c03607a41d10340030410302128240d651502d865616076101649000c010451641414402654480180e02e0103001c0b40003600058 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 236542041 1250 236540791 236540813
    0x1302090d08161e06051b160519051c03140f040809100f020f0f06010905090a1a071b0b010b03060607050a110306010f060f05130306050403030c1407 65
    0x1800c0040c040341111484030400c0b02d074118140c01140090b003030790040d06580010110054110707000e51502003c80d5001019081484254541c0d04845e071420220407150203030070f00249404c64061040d00b807102d251071100f0300020345040c8a18001c040d86d04418403850400f01d580d4405104062819004604e0044112051030300041191040c800984440c10710b46158420390003180e8001c2982c0c58207110190740428014071010103035007036038480d03404100e0040d2a40035402c10840301d40e0110005201840c01c59010540102ea01c0e012038078050721950350002d01e00384031024a10341c070111100300f10036150080d0004000c0c1d1f60000200348201e000b0340d035002d07010074180110040d026022000948076200c42d03040b6000d003074103c000ca6800320050b10b0300c10403031501c03004083d000f07014400c000122440518105401e852503a1140c182d03209120f40211101d41017400074080c507419488000004c5052481901c4c02503000b66070100b80b07440142c00140c240701803400d01d051444070070001c0d5808030f01007942d0303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 236543291 1250 236542041 236542043
    0x7020f030d09020409051e0705010e0d02091302030607020102041d0106021e240105040f0216060905030f07030e0f030f030904151e06080606030f04020609030a1b03021302090d 77
    0x40b03107256800404c0c000c1940c0c0400401621070700d0358501080c0d0132400381c182c000001e4822559080e0b1980011070740d40c4072000040b5004030f56458013800514240d03402c194801c00c10f40c002d030145807003500020b241c80b81c00e0303a0b5840941d600090510100140048240c8095040d50409070700d54074110000707659503080800f010501144c1a843d104114003400710080c2d141e08030300c01c03030140350940020740340b4020207201c0c1c144518601800b90035070307408900030b070f51102c070750200c081c0c8100031a40c035020058440c6c444107c5041c0000c0200c0d0700040504406014158066554004031902c03c00a1020408204070030607c02d80c810564007681c40ea00104407402c250341a24003180b403502d07074039019a2089280d044040d1007152010400309004038440268200d81d081d03079a0740929282c42c0f09000340740c0b1003942c0001e8965140c000050250500d03074020308610b400030f021100c900c0c1803070303c070175003542131130020341c0c0d001d802082c810025490106070640c030028000404601e806815000a0040c02403000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 236544541 1250 236543291 236543317
    0x6130c03060504110306012607060801052b0609030f0e13020d0603020a0b0910080915070e090f150102010225050f0304080a0204050a02030702070303031113080a0b07020f03 76
    0xc00681009588045021301e40800350841d041c80d6142c05030341442031254001c02c41c08070b03808220703080d5a450004416084800c030791206400327030342042c0500040c040441076100030311410016070b8007412074140c0180407a5001e120001200840703032500800a010032949003081010000000001c2d545810103010105000380005942d1042d07804513101810b0150300c042c0d48221180d0000905006800003001c0f10041200c08040d0b65800c5401a52a240d040e91403880641c0302683c0040c50606014075960880540e003001007040c81e0500010710001c0003141c60b039018481d400280003d91540340748030001c1d90002d000a43c1071500100078001402050310000141002c4182c0040138850148079071007916070ba500070f495446480301041580c410340c0d850228017962401001a004040da0300c2941d010301c8095019041c01491034804078080c0507140c00d10203040c45c04004d094941088952220000d22404000d80342200c042d040001103081c000f000282903410000000344210008400c45441c007080720307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 236545791 1250 236544541 236544551
    0x71101030b0f03030304050f1516080a0b0418030201050903120604051003020a0801020319020c190804230301050c0405092e0b13050109180203040614010308070506130c0306 76
    0x40006030a4401240110b509404001709000074404007058000b00c1e551480120b503001d02c4042007005003000121010407459a82103083c0b030180303104241c0c0d00d801031080100030402c180d09030001411526800030300c240c048007080b80e2104041d020b0081c0d80d4820b10007409903040600302c102c03062003107400800143c8103a5580700024014014841480b01858014040101c01e98613420224000d5000380d0f0b0111500340400d0040c000d40c03034580200c400c0e541007080980340000010700180041c040300703c0101e48501c020310002c01c0d402d5402a80c41700404541809240403e603600601d0708403100a0100044c6c5882044107000c503441d0b108600c0e4100140000d422402600501041220a001c1e00b004005603110000011803416203030141211240d11001c40004036038820040d51114214495100380c00702c412440788070564160302559006000c1c0001142920000040003020a0240c00c00c1701c006902041441c01d00100b000600e51102130400041d00e21074154450415003110340c84000c260b26154 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 236547041 1250 236545791 236545811
    0x306052b020a1d01081b0d030e150c070e010f03050a0f050319090608060405071409030f0d090609080a02090105042a05030604240b07020111070f030204060b07110103 73
    0x74001040080c28550300310040ca070702c407940ea00500d0300f00380b185007803c0c807074007000b011410080800180418802400460004400d580517650700c40810801c0b580300b0103008584103881a4680100307400030140c0050020300c0d0520029603110001a00a541e00a40174501070000800006a10b4007203074105512880c107440a1400c00e02d1803040c1413040c20f1200d00000c00041481d04008400152441a19000015540c00050000f1254102e440364006201c00c120400403000d000000c1c0314030f020140995184011010f000761505280c0700b02440007c5016a08010313151b8880000000b40008902401c030480341a00058500da2040c018036224a5513820902d0140f65201070018246416600314106000103170005881608102d500b0303400780d4101101c0183d40305101500c00351005d0240401c0ca04281040b001208035000740344220705001c190415070030707071010402015000b00f440d00c155003144e0341588107010564200342c1c050440300405002c2c1c070300010351480300c00c11621000e2a0003c1c000c24030b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 236548291 1250 236547041 236547049
    0x71e03020f010c05031c050f070c12030e031b0705040518030f0d06030b040308150d051b010908060117100203060303120907050a030f020301180b130c0b030a0207030306052b02 77
    0x90301c0406c110a4070801d0011619800c2908254030410b1010b03d81d2000da0f0301c4000a58145a285000601c1e65113524034480a01c4d020ba40841e0981c01a441140c6c10031210140319843c81100b0045c00380503a02c00034042100b071909001c2d09a01200d05007150882d001c040070242e03a280a040501c0170495000f0035031441c0800da60707005600075500507054000302e04003410090322000c0d003a2208170070380c280007020314071702d003131007201c40d001180e10000a08201401d403011a000d54185c56256041065240c400501500200001030180c840d81c6410000104440c180307a02e06003000c0700101800303005004004a540c0d000c410740b81030b040100b4032800184e48042a450514203943c002940c0f00b48810004018045001c80c1e07503210328400c0c1c4c000c01440c01c15502480328200700382c0009080a00d40000250401404103c1500c500c0c46042000461520b58020607180e80007210300310521a07000c070f40c0506240c0c1c0750040713070003c000a840541040701a10001a01c0d41d40f809000743c01031410845c82d0b011501c2d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 236549541 1250 236548291 236548297
    0x15050c0904020f0a0305071e0c052b090f0605090927030d15210302070305010908030601170106120b060d020d0213090e0a06050601170108071e03020f010c0503 70
    0x200100304643d2030b07002080070201d07608030b0140c080c0002d2501c000610440d010f000e607140c1d0b0a801c10341282e80303131403003e1044a80d4a0490707021900d5018030000450701442071500709403d00d61008040c0b0445403402c1c030041a291aaa100a4040c18010b00400c5000e13040021210380200a4504030081c0d500c001c41c80700043e00d00340c11350580f0548080401040000440070b040d000d6501c1106005502d00c03a10107140440441c09040c54016004105400c0034000c0751708007d6581c0302e80191202c03540d90b9118182152001742c01640c0d034900010820000d980e01c200703501100070710545500040c2d410540010114001802041c203a5031307071900b50071010b55808069400c1018130000a5640300c08401c3c511010b504601c24094500341c4001021480d10828021161501c1d0b50710018081e54400f500d5000c06010b01030b14041c1881341346040a03411110141e0b201d40038000c8680203100061401d2088440b00c0103084044484066040c804d100503903409601084005092a00f1454031842d8200541184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 236550791 1250 236549541 236549557
    0x7080a09050f060907060906030b0906061315050417061015121505031203010e04020108060a0b0a0c0c140604231017010905270f030a050301050307050d15050c 70
    0x881910304104d503035480007804000f41e0300b59030f9030403000071b960310816000d54503403d204a0784600e51900003151410108050702d03a8130a08103084010729607a001c05800c240f41c1c00c29000018100050510040c107031261440050601100140650729081c03004000d031407141e0145a130301e904407240381e100052140c030304000e010105a8040218810211881d952010030707229071030280c0101504040044980c2e81644c3c122100c400580c082603446600441760351400a2540d036004002035008251241120050320070050319460f13012225070942885054424aa40002d92600080031442c0c165118141603604890a1302a07014604030315004c400502010f082e01030380c001c0c40c001100b01980d54014114014001038040702617480c1d0701c60012805803042101c013001c1084881c001c0f000e07105883c0242d01c0710500d102d015145411820000c183c190340c0044c003007000090000c80140040d140134440b41005102c108e6000d0b200381c40c159a00803000711001204005c0a03a1080010909e0b0170310003c50341c0030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 236552041 1250 236550791 236550793
    0x20c180703240602060f06010f1707020102120103051510060c0201080a0b030f0709060902040b09060901020703150905011503020102060606030a0908130915060e2b11150307080a09050f 81
    0x103c0e03c615000b5511242166100203204008001c02d500e07502a022402c50013901d03503074281702c030000e04080780c4120002134616821076608106210420f8031003515640610300c600082d00c180c0f0300700100c101c1a03a01c060070030141031201940030048150404c6007891400d80c2820961160744c0c0d40305182004010b40611141c1500560b5064405100e02050a100303407010480100701d20b80d1640141c400b280500d0203400180711003003028100c3d52605c000a8044554141304440e84547c81c2c2ea00c80ea1448601d00849a411303444103086410000700b8003a480303000700303400d4134100840c2c40c0d0380000f5600c1c00054800d5006160000110b120850315800c140c09540c0c002298a80d1140307801122521400340d44500d6503440e10f020405a0080445445034041318025558015524501810009000989500008042d03540101060200b07050444210f005000d010030341905098a03092201040003c0700415104208004100845400064003a005055200005201c000601d4a2031400390804c10030041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 236553291 1250 236552041 236552111
    0x702010c09090c1403010f0302030d020d0f200708060601031406180c16050604020f041a041d07090902090705160b130b040507032310020c0102130303030903020c180703 74
    0x1b03000c110411f40f5080b80e00c241e044400d0400c40e400200e84503594503c21000042030343d00c00e20f00c440d11940300c1c00c0c0c1c3c10100e450444522a801b8000303524010642c1e1017950a0b0308000d080003815a0540b003620f20155130783d07464400341e00e040380000b038402000000b40b244501070900400c0c51b001a04041d42c44000ca805501d401c1d0381010700304140d44000c100c40c00c80c4108d02845aa161504250140b100c2e045104403070700c001e80c1510310400c4090582c00f951100192504040b20640380b00420100f03000b000410780000e140b00346c60041c0f0600700d00040c06803041c807208200030303000d24021101c50203a0035044440c5240d0b5455001b201040c000d01c0010142c420755012040c04180240440d907401120720562012a1602299802c00648080c10754603403200d0300624a1711141103082e400500301d2032026070006103004494100c0000814681d001900000e50b1059624209030f010400c480e81e58400b15a01000035050b0056408a000000c1a04c0200754840c01e1891074280002e4101a0b210f030703568100c000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 236554541 1250 236553291 236553299
    0xa020304080d1805060a02190503090a03080d0f02030105100c05010204050a090e0622030c050f0a03050d0605030313060e01031d01090302060105060903030301030f03090803031e0702010c09090c140301 88
    0x220f040310100400c5840408000198a1902000f1500c51075019006040c00d601018540200c40c40c901c03c0c2500c0e0b60008009050403a1703201400580a944102072141d00d80d4101c0f0134031800c44a4880c0c45006c150b10403c0140320541e520031045429119038680b6400c3c3c0c02552070824060701441d88003580010408202007000310781604480d549a00c0c21040720000d50700d030800745800d00c03c0040070b03c1e001190600c4102c0404c1c804c1003640c1c1c03d00c0c09201240c01d10ac2c0261a01d51428003404400d40001e1408507480009480314050f1800815048001314206010b003a400000c02006218041c00d0090340303c80c0c8a02c40c0d010750441011000407801000e1a400e8414065000e001040f1049005010350800842c140c602441510035030320b4064000d5003136131300790703994070301c1030124001f080d802e0042c14200003c1080082004600c105030ba0b070080f010585048022114045001d000c41055904155039000c0c4140e01c142c40307070304a4413003405c081040f100002003a224020025015158004004000300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 236555791 1250 236554541 236554547
    0x90e01180f0507091104140a0e0c0904020c0618100501050a090507110609010608010b04020708070807021807091d0412050a030603080408060709230f0414040303090203070605040e0c0a020304080d 86
    0x3004403158501d041d20149205410440203680d54060142800c01000c04100792100c65005000c41c01c001030700040c80d2201801201e4544002150000d40d108200440c90084321030a210301d01c0380d0104154180503c0d4140000038442a0490144005403569540081c910794420000f51040ca9000c80c144d800c2420b19030041030180101b030040220541c00c140305c100c2d190902f442200d02d01500308160300d042070640e54501c0034540c0400d505a03803012000074900f0741001c0c0180b440340101043d4039449503c6103440d41c55039244051900100000c09140100320100342900c0201407540032602d4519070340c0220a0044c4d0040450343c0001c0c041c510089800f068041c3c00003940e41c00703800a0b4641e0a25140d0320410003c2d2030301e900d40120710200a601d0b1142c1541007041010048240003000410403d50700303002d0303021040c4100e4090380000e848042d08825820240308150241005240c82840c02e4205040302111b94006044103513015000500030114078824416100030301606010b072109085481001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 236557041 1250 236555791 236555797
    0x403021806011d01091401110601090b090a060537030302010906050105120a120e0402160201030605090c1204050f03040e010e101505090f090a0204090e01180f05070911 74
    0x502d0210b4000740c803d03003124040c0304000358400016526000043d00b4010100d8640354900b107032034144007400c080324002140502452703004e070680060024402d8268030802210040c00b03001509c440d880c0607014000c1e512440c08900b2000f044139400c0741a107001c59103501310004100701c940707600742d20f01e200842015419000030703001501070132081c081d030790700ca808020184c00400302480596014030710010005049241c5c030340d01c1c0c071445c0c00c00414001640d00401d05a0380720190f044501905481620119038161003064050482076640384000d1810502520036445003021907a100741c10280020b080040401c2510740c001c8071902a03a4a9a94405000040105c03c0c0107030048009490005022820348410341c00403500786403141b510f0450301d001c00381e96641c00b603100e05400c03440340d480107046601d42411107406000c00c80c0c40146e07101c2c50124600201c500030300444140f641080c011001622003074003200581c6070040040607840d0110b00c1d0013881d10384154880f650083c20800d40c0c2040044180107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 236558291 1250 236557041 236557051
    0x21f020c030c03060f061905041508150f0a09020607080c0303010509150a060f0201331a0403020f0105070f1101080a05190506030c090903071b0b16060204030218 71
    0x100c441d803003000810140c4500040320800c2680b41c0500000e200c070320301000344601080c041407c0d61803a80c0c80e00086416240920b16551b816920441d0400ca941030802034080f0204070201c1421041c2090b80c0080e0462001800f041040c40d21003c0220941d0303501011260b4503a480001c1580e10764a1703540d9a501c1c0d030401d1103103e201e41c1c00c04001690501e2101c245000c00e00300205601e0b03560341400d07803e44180e1500f200900441d03684210004481c00300c0b0000035411101d078480e0b02c9011203602224104001d558003e6070704003504d0140c40303d000058100762000ea9038121030303c04604c0d07030181c0100c03240d01650101501d8000340c0700d900c9040c0310042c0c0d10302408120aa0341c802003a070301c0220035000d8560aa0303e0740c00c03461018220298800407a80301c150400401002e40301d8804000d0002180e80c0c500741d400c0c140fa5000040c041040108a60020262002800007840c1441c504804051a800b8017203402d44550803c0c1c580d20204219070f8100d42c06184e0091038132242045e00d2111030203003102255 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 236559541 1250 236558291 236558293
    0x302010e061309200f0d0f230414010b010c080a0201090b0a0c08240d03090810020405041508030a0c020f130507030507030204050a140406150503040302120a08010b07021f020c03 78
    0x200c4481c44004410032076105864082c0c0c420b16111b101502e80c0c00408005c003020300807076924181d44901c0c50308030b1403000303e24031502854011401e082c1010032411000340e1420840d40e01d40103d040150340c100220410303481e00b04000945442a1a200ba4054403107880000e1a102010040140e408816480f489a094195541c02c0031075071013a0780303d0311511075001a2078580360a00d4169441d0b00c3d00f4248524120703c01c0c0b82020303140d41c1e205403152900d04403030715100c8200c1c3c0109003400f40c2d06041c0b01d80c3c4004240e10003400740c990700d80440c003620791280c07a0343c640411034099115000c0d034031560b1211144580c058140c42104000f0613107013000704030039106e090000c0c0c100004140014030038003c0c2d406481c0024442c1d200742c1c0c9800342680c0580002083c00360032584818000805d80000b201803c003039005510b0786079403481e003031400a003001c15110205510f403d052003000c42859200d01c04505455402144a47d41d82c003e000007001c13a44000008030340e02009003111025207034081403036005140154 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 236560791 1250 236559541 236559581
    0x6090504060f0311041e09020108060904030f121e090b07030b060406030e12030702070e0f0103050d030509151f080703020d02010c0c150203130905100302010e061309 73
    0x204000c2075803507a12446a901101803800d0000c0381103152221141d003001400003601300f607480e02240244844821501c06603554540280942d40c10070700700c0b580240200c032100001d142c0303943c003c1c0c000c03071109401d1010400039549200e01e80300a540001c078130105059030001000c41c100c4560000c0c0c03181d400101d81003a040b401040f411406400381400840000b406542000d0910030120010720601004d520301d44031340008640d5140c000350007180a603101e40e0103069641c2c2829041003240074040c0108050b0400140104045500802c508001d1141403a02141a49850f21810320b0b2050b14540e0507000b0a0900c01c3c01040a4441c441304050300001641408030341d0b07204042074035a880b078800690480d0769140c5482c0190b01c0361040c00c501d2071059800c3d14000351124512080c0c21580b00d21040964800203a240c003080350080545c0080c44480010300581c41c0c200305060070f44a0501c4000d040c04000c07a0601459950503007500c01c80900c0754000316420b55a070000d20081d10040c00301441c0e4271070503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 236562041 1250 236560791 236560799
    0x1509060e0102031003060203100302060408030406021504050304050d03141b0601060507031706210a170c0a0f0201050f0c03030414010b010512040203100504110a2405031504050c040609 81
    0x40c020780b031180c042d44650103001031446d01c6100c043e5000402c54250344d10381b8a40440140d41c0d0300040e0026140d030700011a101c1e414404003900d451440d26091804001880420000400c00030448050340e00680d51000200d03030030325003030340c481460b802840070351000070031698022222000c00b1054495904111100b69984071010381d803c1c480c141010b00021081c11040d01054201c1c4201508518007030000b01412410411600140304d262540b20b401341c22203407803071041c03140b50402c3c40e9209910f1450386142004201c003060380c1e0f48440c2c0c40208443c91102c1c40d081036a01400903501210b5800400300e64501994142a44940c02214115003529141845407000e00c4148500440120180c480c9450011906180c031a8210001c20499142c8170f08481e64500c052036000d010700403481940c0e141416041d001c100168884107420800c1d50030015030400b00c21000080c0010b038010f0072402c00aa0340e031100c075188400901503909087e0400c0c2810f041c45440c04442c0020411907600d6540d012541ea11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 236563291 1250 236562041 236562043
    0xf0b0901050f100608130204110c0606150702120111030907031403040f060513240e040903090506070c03050d050c1e100f0905160f0602060112030c0309031509060e 72
    0xd070f0b181c038801c0c8032000090003082c3c00b0b201d11035005030f000070404011810690001d001e8540074461b03c0e1080130080b490800c82c4004002c1950880800c5401c0c0800d017000502c0d109080c05003a00c01b074070a514101102c0c4e12100d0a60000c9100180e0000050341c910f441c40c4020364880c01c46c401110381d9481a40300003100f20011094805440c0130004d00641d03a441d01508650582280c2040c1d0a0560f007010000f13414103130307500e40c4580c4011030310b8901581040b2640107890200c103400303054020f40c100421240001d502041007001c1da03404940c07183c0c0740c5101d8148003045440b1504014004d104040580c02c50a07004400f4094030066001110300e031001080c05600521142c180c00c21080d400010345d407020010980010005400403d00001c8200b4039450701464040e050714448d81e426058070043c040545805989005412940002c185a5142401d20040c0380d401c3e450240c100141c0030249030400d4480d482c241c0095400000048000b803038414600c0081160642c2142c0661500c4120001800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 236564541 1250 236563291 236563321
    0x9070f06170105040b0111030408010b040e0c0a3f11011b0201050304020d050105070f0906030b061605120408030a02062d0702010b03070303050d05060f22090f0b090105 74
    0x10000740e11610341d1800381403001421015000381e040c0400c0076484003100320208040c4c0b000302442400071031211804400e2208840d00c02903002d07550f40081c0c180d40425101c9221181c12a030004d00b140300030088031902e001c2c08000450507044c41d0448051400303240040c191040380114003541d9181309004c0000015181582c9070030a03100000a10308100c0c0156002c0c102860348180040c140c1c016030352040d918a0702b1204119200390100d040214080303a8642c2c80070302d00d4054906824100a010003020028605010300020b20192504106040080000601c44210000081c10342c1c1a121034480d4505600d0fa000402d501c0010701c80d101c0003821003251448840c0f401030b4901c0b09c1e010781900343c4c00110042080200030b02c0640d92038103948940c2c3d44040200000943c040d5861390b4455100600d844140c400140c1018414148400e84044c00e60300c0000840e010314043c0428900303d0b0300c000b0004090074002c140a030203410001c4800c020300a105080078401c050640080281d0b90f41c2184d5100589 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 236565791 1250 236564541 236564567
    0x11040302030703030509180a0c120e03040b091f020607030f0501050f01180e1806091209060a0c061e0509010623040b090108010615020a030c02090a09020909070f06 72
    0x25004503003c201207401a4020004580c1c017034407100a12280c884050300850041e20245070301541e422802c7ca0055008001d007044001503142423141110300c030000d680d6800703540a0a400d5010010742040c40f5681d11040c40540d507001109000841c01440010b91074010846d07050700441c1c01e02c0e161203000c0d121840b4040c107950000b400c20050a981100440d50301c1021100004207142c9010302203489407000039054401d00c01c5058aa510407940701941e814010064032138501b9a00c003240d11a03002c1d0040081e120788080c103a40d4140c0305c08840c0c074200c520079135080025051a1500d14420701c60804213000fa00b1004d5804401d010380d4407041d06c1d160803a24648180202c07840b034480c4220b15121801400b0071800d1700188040344243c2000000b40756103100b0b80c007410030390b0365440f07042015940d10000e0402c02c80540c00900000e12864038060200001810002c0c4120464400954548480e9104070301054000e07207000510314003140480d1f9a101c250003001c41c0c01031010000243d8a2207204450f00c01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236567041 1250 236565791 236565793
    0x714040e010315090609110f010503100b0a120c09050f0d23010603060204080c12070b03010506030712020a09060809280201021203070806040507050c0318031c0201020d1104030203 79
    0x940c2c607685610001c8a2044510051a5280c03070554003c143d841c021090424080c1c0d88a1081e0300e202d008101c0c04218003009a03050080038400c00920305641d86500048404400c80b0aaa94400010840301030010a80080400345004e04802305641c0c0104120207644d010313101ca44000104004000584551480c000c0005411800042c5d80c40c035401d240761410311203200003042d102e8a0359116000e9802c190042c8516900c6031422000c2c925181c84042004030881010b01802403e0001e03861803072205020f240e00564001020904040c0709503c48a0f030400c80340f0045480720342c8064010700141c01d6104203800031b05d140380031903103072040882c000c0f0f400001808000b51040c5204004244400704050580c154001c0c2d88202070741d40a80e800442c0300b02450381d55560a4074000040008690b070240c0500108801405018909640002200c01803043c003a0100d01204d640c100091424914070350480d2604888008101031b680c054010340102c0c10a00418440c01d1160301c0882e25a0084e0310000e545 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 236568291 1250 236567041 236567069
    0x31404030b0a09081902010504020906060c0a110a0302090c091809030a0309060b1011060c032806081002040906050405090706080a02040509041103060609400308071404 74
    0x2410b240e07911603441c02e40b260600604000900c100b400c03044103103014000140c0d4541007008110310700030902c07591080b4100d4500341404c1ca180001a503075058000018010a14040904040c2d81d030405030800459004200440703616056011241e5a00314443c680c1c000c50301c02c0d40d05000e81c0490b001d140e108074001d10065060005420044029086180042d29403554038034601c401600c0710240c0c142c0414542d212041d0003450590355070703d400e01c0185480300c10001030090100e03100700004003220003150040c0844203a90052980d60080c500c0358407404061041c1400003003200400c0d0040c200b1035506c0c43e000c10140d66998140000c0e00d03012103460489800c40348043c40414014481260001c0051400608041e01c4801046908d0720540d8140c4440920031002481803804001050713102070181c80850b400d0070280c070a01c080c85030840700303040050002103029640081d2044198100c0007400344140c092080ca003400b411000b8203541040018a013803024a00841040d812202110014110450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 236569541 1250 236568291 236568301
    0xe010f050906040b0f040611060f0f150901090b0109090b090f07050c0703051c020a0b0a050c09060708040f060801030308072a06151a0304111504080604031404030b 72
    0x24a40d004510080d0b01c00c109001c00315102c2c04420190403460800f83e20b0f65a95801c0000c0a03080042c01405c0d03a00c41c0c1d02150402c01c4c602704044009070848070fa010210034544070600804040d54580766155081481341000142d1256190003038101d400c000c0e01c0307000c1d8003900c8585d144181d9484603001508072110b01c2c045501d40c00ba850525070301c610755107051404d0814403110315041890315441134880740d0080d045004140c0c90002c9a0000080600061140d01003560301c01c14500d01c000c02d4110075903039500004603140320020840c2d030155001410a80d40300c0c5d0034a002d000c80c0c0c00500038000b0066400f4408540340d402030b0042c030f040c1c03a015100c2d180107556040302140c0710351010f00580f401100d14098100c071000c035400308803402c0d449204086a0070540099070106161558000f041c521064030500182100c20011280c02c941c0200d19000002490001b0601c0c1c500c0f804001c448240e400140000c01c01004a413041c001ca10075030b104113500f05c044400e07040034029400040c0120f10880f01245e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 236570791 1250 236569541 236569547
    0xe040b1912050f0a0308010e10051003090201030213030308040b0601050304211b0b150103022a120313061b0801060806031005010b0c0708011b050f0405101106070e010f 74
    0xd000d16102e030044420f00e40c111861a0700304428024218040b501100040c44200114541560f12907a00e845090400c0d240030005400400c014100c0d80516030368112010039640f0030b804480b211000c000d84483c03816580d24004040f1030f0111002d5a00000b003001203a4998030070400c8a00980d0422481283d41801c480164109442c20800303005100d2085100e45d464100710320031300d9810f80a041240d0303462510307000c2c40c0300c800710341000c550406104000c0302c0b83e24085100605c01203454503000c0395017041840306440c40c2951070880d030220030401100700400c007400301110362855031080078103200d03107121400e8888816a04101d00000b103181c00c0c0051000600ca6000b040c0d000c18007c0071591444140c20146c002c484003070b00325010102c80005d54022034001080542c0043c211070b002000100c040c2040019032600b401e4402c4d04001000610180b00b940c44402e030b8015102c002c084c0510903118074409005040300c99140c07085400b5100000c0c54490041c8a01160680180c54040030b17125814021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 236572041 1250 236570791 236570819
    0x8070c0b1303091d010302130f14041514070c0309050d2303040308090603040203031605011a0a05130c020304171b01030e0d03110d020d090b01080706230f0a0e040b19 73
    0x611825682c9015038440d28401e40540044ad001e109100d034800d003003505081807041a1900301c03a010743c0c20010000511400303225a5540580d040c500701055400e40d1604483c980c04aa020661088513a4140d005202d4402c810501603a610400d0240030900002c08580b240100e00c00900800c0d414411a0f08500b8040010740c1c1c01032005064a00d00101c599124002202111303080c0c4003a1341d5030464421300c2c002950701205818040718030a10341c51501000640c200c03204010940480d071030303612900712076008000356800360140d030b03e20f40c00340c2c0ca20394049035641032189403280c1d401d1034030010410706501911410224000d003401816101e001008190050041626404003500c002c005c1c0410074903240c07000d010101510603012501a1250030114421441071b04900400d07080b003201002160b0700b104c40c8002c2d004002c51040103a201c0142240c80d18051003000d05080340b00000d401d8801540300070200d40345882100c0030403920402106018180c64030000c100a000448101404580100b00310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 236573291 1250 236572041 236572069
    0x30f09322a03031309050601090e060f030109050a06021c090812070e1e130b01050313020a090c03020d0c090f12060b0301111c05041208070c0b1303091d010302 70
    0x420a81c4034082808246103620181d4103144204215400b44916501e0340a0a40c100d0401d103417030280103041c404038121828000d0a158801d50f26055402410b8400b90060b905040d0004155100c180700f0342410310181d8010340940507007005003c03580c140616548030300003415410050150400310040e141c5513104130003820316014800c11040d240b9007540d440390114510b4002c4c0e211403a902607000140a80724049010a140260405c1c8030070107144d902400392039110b1a480400c00f500b140030b0010071005074007a004081000d042002c0c004081d9090740041900c414950000c01500b41d010004503502c11990203150301b50011010100000c40c00c0c42c000042060086100061240e05400040c1c2100d03c1c0c940a42130f074040100303404010f406402e01d01c50580074002c505003e14901550740d8040090a00c00301418445075401059034035100710740002506501c12004406400d240520031041400c684003203001800400c4d001c11015512aa40d18440604004014244c0d007560701f00001c1d49213482c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 236574541 1250 236573291 236573353
    0x10e071403071e050a0201060f03030e2214150a1503110918100b04120b130605040501270506010b092202030105040b0609150a030f0932 60
    0x5001c0c46200c0d20f40c400681ca2105921040d80c1c6200701d040c06401c2d5216544901114080042d0800200f600050811000241290341806003203880800c00c10001c0c1e0080f10b0f04400f0715040030002c0203a041c0c1882c41c000e003030340640021599003d0080040420250041d8a60301e800b00004000990007600403c00b080248201d0314208140480400c124008075402e03180032142e040140003218074843c9603480a410010501860141489030666012904503402004100c089001982000350b00c4440d040d0190700180c148074a0900c1c0c2481c6010b0052070160408140011146590911030f0120054250340e00601418107a0b03e84021510250042d13140140c1000d4004000703c1c042465031603d0f580705007500d40050b00c039410142408210b4400307080b0680210010031510005030341d04c0b50001c07415052112400d68803e24548100c018020180e03010440504100f1110100300849141360400000002c0b040c3c4c0f103c41c14801c407000002e40b8650b520300d507000880e181640010144640c251044500c3c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 236575791 1250 236574541 236574557
    0xb0d020d110f09090303010905010605030408070f0c0e09100b030a030c060b01050c0f0607020c01030204050d0b06010908030c0319020607080c0c15070c050c04051902072d0b010e07140307 82
    0x102c08500b4440c0202c40001c5030f5017000006001403105d6100b5135025000a10b0b01c2803e5103010b84e01c0c45c8507032041503009040c0c00408072400b820044803403821300103002501c060320342034100f031100d13240c0d00c0d051440300140ca60f08041c080000ea0400140403074010340c0540e5441010100d5454100003051100b410744c0c1040810000d15524841c01c0040d070300100f0840d4000e000a18225100a051411030b80b1500d04140c01040100324a60703401050900703003504011962400d888000050719454116800401d9502011825103410030020000d0142003544100312115040c1c2070704100d0301e81104403001e0020865620114000e0042d02014049032000b400803a038980000d50100f68091400700e890000280d42d0358040da040201c2480907080b006400c9d03a00340403508014034000c1d0302503002c020003511103601181490074880103078964038124a1060941145880d1070400c1514056204415a81045603a0000401001d200c40d0305119007001da841c01800340500c04100403c2d4800f528010800200e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 236577041 1250 236575791 236575819
    0x509040f1407050a090509011a030613060611070905010302061c02070204020d0606020d0c0b130f0f05030a08150a0b0703050c0d050309011505030303011214030a0801090b0d020d11 79
    0x316504030b000b0000e030f031651902c40460340c0d8018030f0460142c010f980113800700e00041140e48a0416100c0801c0900c070082074680c2c2c1c8500104124051101186070881d042400014004e500b00d031003a580b003841c01060b5103070251034030711550a946c0284002034020720100501c0000c407203200480c0803100002800035150044c6070300040c069070004145a800c1136039401c4108881e503010044800d80101e01e0400080500c003c0e1203400c400d9400400494800200c144190100088010030b1703142140d01135032070742d403030700301ca091841c0d4a070810600d0001040040b00801c00c1c0c0c200d543d40b050b4503004014641504107081c41070590450700710000807800d0107014070511b10304542c00d000e002030a01580c2d440e42d85907c0c188405e9420340754100000d601c5030140704802d0049480c04411241520340701c92241030300d00e006181a500b08c0c0a035408102c0240000f01e1541d0038070345d201c07845030304072481c900083c4503003011402004401303882000020341c025442d2103900000f0705d03134018015145100410b103244500c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 236578291 1250 236577041 236577071
    0xb151e0f190e060a150c03031d0304031401150e1b0c0102070b060103150311060f0418060603060e07050a180f06050705010509060105030a06090c050618040507020d0509040f 76
    0x594101c1d00b42c0c2c49460040080a0034040f1044c002004015400c01c15102a204080c0070140f01c90006410141c440d001000c042259010107180c040d04401100d560315a80c2c140740750020071007030005140e035080100400b035070b1002c000030360283c0f1401000c1008035114211140654140312500d8400c440042c000d00050030f20a02c0a002c0b000e016020700301c51860018001411144402d010907015a4500424404903030110110841818207039540c903a070310b40b8070904055502031540501c075034140301603000d80101041d4024504540e840c2c2c4003800410b8503480100d0302c12404555680008006000d52406907101c0c0601003240821342903401461926500c005840c010581c11490118100240d1642004002d11271180e0103102d00c0c01811540d41801c00190b100c00c3c036000041c249603200c0101c9424400e109411f4401000002c2030349075030748584259a4820700c26503051034810f5251400040e040c50000c43d0304180007465a407554981a44030f420400240002c0c3c040f090580d40d192028208885 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 236579541 1250 236578291 236578339
    0x31f03080304050105400602040f0e160e040917030703020703090f150815030d0903020321040501110c15090a0902160807050f07030b151e0f 62
    0xc0140c0c225941d0b4541030800703c0c00d403031018155581e65415000400351844901110745a01e00040250310b10b00356211503c941c208000d0807001d0a0184001070004840781d810110344100c855000d4000d000366a0400b00070302c000171800007080030456a2148a140380b50a5100d0407956109603040d5640302d0307111301003000e070360000c0311030001103a8001514ec1c141a00000a08018030902d0343c00005c2505004a8842c66540b080c1134505005001d4003080a00d000c0120780006140d0280031513641c0095000c1c02070511409100c103a01234003407429001c91007501d124400468802c4000503a1409190400442d50343c00741180f0b620080c06000c090115a948500148100c20003140703c00d9100d402000400800482641c0a445a284104800b0115001d040301c0e0700000c90f08422402d0310b451150500c00d040504040400149000301180801007009c840d60b070b14020204528a1100040c00c0700501c03e650b081140c80d0094600c1e0098511010320300302c5154034803468054196a9507250b100700c004c0b1002c4e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 236580791 1250 236579541 236579543
    0x804020114071505090c04020702030304050405180a0501020406110d0c0b130614060a120b0105130e0d030e01060603090b04080a02010b03100c12090201050d052a0903070b07030212031f03 82
    0xf607211003c2c4419400e003004620302d00f600c00c443c114079122180c2d000907580d11440c45403900990312500003807011490002b4001c0d005000c0000c5d503c040fa010326245000358014080c5101054862001c107d85003030000b87d0045510301911038182400b41074668031205400181300742d860020320109100014980e0080d000e007445000444c188a042050802641901c182c02102c0c8400c50501c8440101d0715007060303241100c0c02034402000e81e0301c409402c500507107480303013914155204950104800da581688003841c2c2c0c000441c000c2084603192a8101c007a00d021070406854607220038007003004200c4c0400201140c3e015400006184a01000824204a1054807000e0002c0d034400c1081e074110f81240440201b914a04810400110a0781c00680039001d03695000200c03a40d54400a0000d140c01031050140054065400c800c01803a05805180c41d801000300600a0007991000a82500200256000c035540361300940005240316101e150913400003856400c1845842c1150341e8207034600700c0786070051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 236582041 1250 236580791 236580833
    0x801051008180a1b0504051e09070306020f1b030405130b0612010303020604170a08070c170f071e0b060d03020a020a0306050108061b090d0213050108010b130c080402011407 76
    0x213400e840d4042c600d081c49682c0454003503030400d4204070b40c00207038044520858000340d02140701500c0d600c29481c0b400c0955000103000310300c0000e6021080c6031041c00b0f800c1c6245800c203441e80c441881c001207034690149108035600102c52400f140c0403003d1940100d01c03400d01c00380049080c03000c61018580c035004e007030b441600036801880130b001c180032121911030715034601b40080c01d1415540e607800810700c00300100b510b01040b1401c5460410082c594580c0203118074030f1000070381c0b691030307158007007130640d200c088203c03003c0c001b10040c40c3e14140031001c2c52448982040082d0000d41d141c0301440810403003290f040f021030086680c0800103a0f2020045170103540039100c00151581011900b9242080c06800c10f42000b40141d1681703400080340c011914a00001d441483c0c0d90102d501c08030b140d990100003000c501900340400400c15900c1544501a8214222a45070180000990480032114542c0071040040c2c8494005400343d4011800b422804c1164602549020700395201da4144c50301c160041d00d41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 236583291 1250 236582041 236582063
    0x102030403030618060305150702030c060f0106180311120a050f0105071d0f060d0e0f030706060501050a0c02150f030907061107080a1403130602030c010501060801051008180a 77
    0x5034020224185100040380745041001700e044d6294156034451a4071001066943c4800040205200340107072144148503070100d4009003007806260175102024094440020b079140340859840030401c0c0340e0421280c002080000140c1d000040c082ca0803110b03001e855140c4241d409420028100300241018000340000025160510700380c0100723103072031f01400346100700e00c18498000c0c00c1c1d4940040001c0f40700e086030350641e145002d8980301c015118960035030341c0b18080e8003041c9004000200052840900c542401c00280d52100015116030041d02789803030024400444040042c14245078848084c401d07001c0640c00d04490f101c005a866004698240158100c80402c2044540003e000300601a051024120082c06c240d15141d491300720305c0c00501042d01201c081494030100b44104c41e0076002d18030a403032003d80c807100085e589501c41ca801a4003980303840e000080c0760b4442e044c2e0310b0588000034a17003148101c0c0c10b1002c41b0b000c500a05207110f05901103294032000c4104106201480b4801c0441d445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 236584541 1250 236583291 236583299
    0x803010504110412030c1109060907030902190b031f08030d0c03090f110306070305060d02010c02121e19150f140901060f09020c03160f0501020d0e0c04090c05040b040207020301020304030306 84
    0xc01f880358194450151a0a00c02c1c0300c8140c0d0784189081d4001c07142c1c90300040c450740c41d000041100c5900d000008603550202c9010032a00417000085200301e103410044000e425016a2a000355000d61040c4d0302d45400c00e002444c20704035190408103025403240fa0208800b20b00f51522085c1c0d401c1c880c01100c120000d070b2400304c101e0805100c0f080d03001e6080d060400c0180b1742240030440d50044503070000d04101c079201c0d0700340865854105010394a03511070221003010892100342d4800010382000c03940d89208030849440844040c15050740d550382d000c0081060302c403c00c3c2b04e910240141d91445200c4a494243d44100307410b41d582d00c0d81c4544400d44c0040b0700d15141080790300c051a041d03048542d004d030042105404070040082194a464a0101c640000b1481030a20001d000d0030003200510a5000290b9181c25000c09d401c80000c4800c141c0c241c4e0740c11032042040104481103600001c0a0b2030038000708000e81d140c1540440c0c03001038050005483d0440c0e03640000c0c03c9a104a500304c0100f80c2d1044144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 236585791 1250 236584541 236584553
    0x7090504140c0a200f0c01171003080703050c060a060f0801090c0b131205010c0906020d02060a05150a03060f38041e0b01080604090803010504110412030c 68
    0x80c0c2960701c1c001e210918180b1440e29080c9108a00301d150510000300e0204480e1010902140203000000701540c0400000713030701c02a1030300c85241e002c0d400580d40c480c0081c003040003070032250300903450b014100034024a156216080c40c0c01c4030b0340a4040c4502800b4000130980709210041c840c4841c000c3c0024024146403a02c00c4031051a0482006a031400c0040b200040b20441c1ca80c050b1406c0511941d2120440c1c40e0290080b001038004610440724a0724070020081e054000511020040d01c0780d0302e072140c0700d1000b2a0b5070f65a426072080143d000c03501040107880d84d40d01c11070f003020307240b0b0980750100c0584000ca602c0100395407045820550342c008603440d12443c2c2c86080f8406c6078024084920748101c0d00086480b2008084a00340c1c104452040281303130b60f4680c805590780c0c0c152501034410414121400004004d00c0b12158040742659000503070901d0075108900910f980840b80509507400c0800740002414001907900d00c004040202203480703414420b00080040c4283e94200101c1c180740b03490 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 236587041 1250 236585791 236585801
    0x23091306050c04080c04020f0408030d050415050702063103050c010b01050f07060c050d0e0307020906122e0e03040f06020d08061003200c06060d0f0f030903050607090504 75
    0x40c01440803c2c001440403d001003240303160030b039080310f02588440e0404c101d0070880c0b00e030307a000303c0b01031200140c3c80841c0e0502c0d1b04450700c154000c030980c03812621841444030694000712141c00c01600001c0000b03900c110807071000c4201441d0890750311303d51240412041075031110900c0a42c08600042050034440b002401900d8010a082c030b807950801d400d40701251918090361500514068440b0b02160100e03200e030341907030340a00792030b002070050513903400c000394036640041004d034004c075041c80000b00d00d0700b0080c045000d00d0260702c00500c40c0d0380ca802c4111903820004080b8030183c180c01e02e00d008003442a40596010300355040c0c0a50b50391490420038000c12a06135100c141550000c0300314039860b60f00042d44035481070341529911540360702c04c1c4044004112121075031482c40b2447d04d0840f6a8100c8c0406002480040c10444085803a034004021141020352002440a042007980e0710001d00c001400300300d494443d0078400c0409840780d4a8605001e130071200c40e0b000039840c64007080030386000c0c003070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 236588291 1250 236587041 236587051
    0xc040b040908070b0702030909180d090b0405060c0106030204020a0215011a070624030309080d0c080301050f010c0f050a020f04021804020c12030a0506040e060705042309130605 78
    0x104001504075661074a0320703030080c1c0e04003414411034036000585080c024011035943c948014604211450004505100705c4040b407040d403428401d0804181407640604000826070300715900c080c1c240b500d0401042203940c000c101095855483e000000010f8980e8000381446101d25006841441107a160101c400740c0141d00a2245440c06d070004107203c001c48084441c03044c1c0140c40451607030354403070401144c454000c43d48440d1310000e410000506070b1200c2e0039816555141c058400305445035400301c801c0d00302c008010308508003c00041125140514010000c12418106001c501c0685e0310b07a21600a600c00080e542c80e0409403481c81145000c1902c200180c01c1243d00714104071072804028030142484010a01465001801c80c180c031201700301d9440105203018000341d583ca0a0b80552015010640c0d109000d80d081040b121015400440d0140c4101000d981c3c55052900c0c14810942500e404460405003003082e003101101d40d01c9400300355100d103900f4880c0349510702c15460300320115840107003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 236589541 1250 236588291 236588299
    0x1c0504140604080a050a090509160f090503030d05270a020a170c0103050c04091a1c03050a0804110904050a02030d020c010e01230406120605030d17040609020301020c0c040b 76
    0x10811001682d10000c2d90001c0d91360749003040e100c950a11080d40c420f6001c3d00103039070001550301000301a01544c0b418002d0740e0304694a555130011032080641d42c02c0221b01465925400a201050f0200180c0e8421540b200304012041f04e02c04d5400c0c01c103003600312880148801604007101102c15820302e00e05090092400403044042d512600700200e4460700c01030805c904240d150360225450603024002d6502401d43d031102044621074205030b40d80c10940b1500b5541c0640003103244210410078207a0803d8401d41c144d2a083d203400800380c02200c11000040c000c0f5020403c160400700581c84100d0b42504c03d601c200c00504512031580105860000d96078000c404660080403048040e90740140c100700c4004080c02d290036021140045e00c0c44003c44204004446013000c10f000401c0e43d8080c5001c40d100d0302d0140700b04041030300d40e41407580700c00c0385086000200e0040e0b40121444910310b0107459206001d030a0001d0080d05903400079007640c4c008245000c05030b10081030300c00d803490180314004004d08111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 236590791 1250 236589541 236589553
    0xd06060203030f0f0901140c0a091d0118020705030a050a0e0d15020c0a08130e07020706081b1c06050a050901030c12151401230a051201021c050414 65
    0x18001100140c00800c04e49842c80c6500102d880840b0075006002a00d80c840c0e5840303072178a041c024114050b0040f15001c0c0c00981c441d034000a04980b90030040c0700e08010240002816804c100d40600380d101c0c0c5441c0310300369070760070480500442c0c2c040c0090104a02565100380da00c1c0500d04004203003440030992180704500c400451400100303180400380b0601d030000405030310351030044080d034100810900042e00380074001541440c844416203e050aa130300483d091141c42d1540b000c00c81c0d0300ca5407405080c02007000003000c5840e142c2c400408002055440090925048200701c14001c2c6580020583c12015181c80c001d11044c5401183c05002c1d10b803e940c011460b40c99a1910015052103102d000c50380c1e140051074405110590440400702c501366901800414040d90b03542130750342000d00c94243c0400c00003415403084182000b8010304040014040c0c603d07242450b00b0094100c08400c5000701c03a40d4200300c544807501e840344d55588840480c800c0001c00d4a05820101c02800707201c0d052000e25040a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 236592041 1250 236590791 236590801
    0x6090501050f18070c02120105010501020616081b160308091002130e04020a0b03010b090f04090f110a0819050d020a0f060504060f02070501091a01051c05150c0d0606020303 76
    0x21000741c00c540000071040f140301e62034401041c2d132070310701148002e500f194001c102c00103503150540006040316000e0382183c0880d0790703010341c00d412040408410000100110081130860a4200b59900310010714011305180207100e04951040412240048000c1a241c504120700010240a040019881c4041c10340c0b80403441c0540c1900e0940038000c8181c00d10748080890255160200d192014020381618540d0360b58584501004070f4112001082c0f180080074280540384c1407a0141c80302c800d500885141a0413216962003079181d0840411a4114854071800111f0050030841d050f084000103800006511003402c2441c1065540f800c0d12080d0b41c071015540000598036100042815004200007549132164545503015042c15003284990340d00202d0941c0c1400b0b01035005a19017449108a4440481a444000b9114900740700da66806004440d41c0f2688420703034500074441c9807042069031603055003070380e00712140c80b4240d0320408100b8000c101c00042c0b01a0344036000281020380000c0d400c610f86 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 236593291 1250 236592041 236592049
    0x806010c0b180109050f0601050402120606030430080c13061d13060501080f0403090506090316060e10051303230d12060506030906040201110a0b040606090501050f 72
    0x10040028041d0324940c1c00200c050000d0141c032014500298000c0c8141d0341103041080d90340c111029500400d0080000009103440d16100322200c1052428000c0d00c2d43d0390703030300402c515904018003e4a83e039600301c596084096031078860310b603003131302c034002d2100c000d150708000a0258cc401032400419800c200010170307500005c508081d04070780a91400510304200f80c0c0c059000007040c01c03022508245060000102c50301c19401c17800680313100380d861204175510904a41d501d0103064402a0100d0071419050080d402d01c0c0c4010301809802504031032510307800091280010400380e100708006a080340c498040c51600c3c440c80c0721010308a20b0041d050071031000c000b0174180c2d1284001080400000407208411460319481400c400402c401e80b4040e181141c005849081d281e034402d103113149440e80214961401d24207403801184010010410356440350300541d42050b041d104065148203a54031030002440d8008a240300b107101e0400828103d00d031400d020b041d520183c01072881140c0c805807004443c2c071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 236594541 1250 236593291 236593307
    0x3606010905100b030405060f1e0402131515140a0206061009030503160201020f03122a031e010510081f080316021215010b0f1b01090c06080601 63
    0x4a051030000715500c401c0e841c004034590740c0d4003610301c421002c0104810300c400030505a1150020810803d81540c1e11101420001d000d00312540c000c400c02804240503003490f008a85120070305040000700e800c0003041d960003803045a40040e24424800c403110500907808506d00034800141043c503418142c031140b000e034547d0f000900460245045020b46a50b4034442c4183c980295080b2082e03a60f162141204013035440580f1005034054480c2c01c21011280790000200d40c2e00000e407441c1e103030107a20750801030040d00242451007a03d00d030204058003681d40c0d0401c011800b44106000c1701a040030700d070006a070b1002051348181d10403444405143e620b55004102c60ba4084561015048090004540c030070112540303400134602844081b40384120200d00010074903042d402181d00c504601ca0100300281d07a118040000c0e03000011403401000341c04400f2000e0030103a8411000107041c080f8081019031401014200c58451b40e460381e11040c28407842640c007402800f554640120780e4134003040040d00820f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 236595791 1250 236594541 236594549
    0x7141e010207050c180c07030e091519060f080c07021206010e0604110a030222060905010810050a061b02040507030204091524110a120f030e100b011205360601 70
    0x22070007c0c10b182018807540b019400340000a1141d43c5a04250000429161080350f006024101030121000200b41c818090701c2122011350300c425034413003070a01c102c3d80d18101500c1516030000c103001e40001a5100c0c600388880c01500801020690b240281011f07209801400c4280290300d40440c03032124103003081c1181c0419401c5c2c100569190500c0e05202001000d0101e04648a20380210101d8200e601c40704503c101c803c242d94068085d1a0314600e105c040049215540e0300c0300044c2010045140150308580386e102c60034451088003106a0040360507910200c070150000780e4000340134080c20750365210f80d0340c501780f294080c51852410101586000b41c0600712407000044c0c02606641d62030710840e50084c0100841c0195120a00103107000c00500b42e0960300706002c101c0c51404605c03240d1091003100f440c0005000100301010105440300010000400c0c6641004234000348080000c2c4140a42c2e80150340d22007445a00300726510110307030b040e224906d42e0303400300d4000c81700e20031300305c10009030340c0e05407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 236597041 1250 236595791 236595811
    0xe3c010e0f06091003020d1103010e0402010809120307030c09080f070302120a05030d0b090105100503070804061812080c1602090c0412030306060306120807141e010207050c18 77
    0x5901d044005055801420390303095000e42070181107040d483d41134005d80340c803d01038003081c081c9481c12441002c03a80024091646440e0310000004e001d0361058259941141c0102c1c25030741072003150500030f906640115110b4002c40e48803001c9050f001e500035540c00091a1080151a42c0080100220b8641c0741910010348510003008195000c0c6605000d1080d07050350010469a6880402102c5400740c0441d0300354a1083c040c0fa400003502c0d041c100703501400c0f0b030303110341d00c1c5490341d5603d100070740c0c0480b00584151031150f0381e003030316155001d03004804800c503600408003100090340100c0010714903540203020252100f401c0c0010700082008451080c43e995040303824805036914010040903a002d15400300350464030450801082c1600340e441007007a076406903030502c441c984510000607080c00c0290018a0710404000e0074020034082000c0f047d00184c0c910640e180324040704d60055510003201d1401c460b9941c0010064200501080603020145040d00c0242c009140d062040b045400018203e0481d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 236598291 1250 236597041 236597059
    0x103081b0f0d03060e0f06010c080c010207020a032604050a0324020301120c08030304020105030a02180604170c040905030a12090204050c030610170a09030e3c010e 72
    0x5200c805108060080780450101c8040c0302c80500010042d0405108a0031000d852034003003180c4505a40f0511310613401a16072803403845840d500c155459000c207a85d43c4441d54288020030041c4e88403c042e80055000d001e60241d034a4601c0051100040101ca80322400c00c0c04000820140e21806200b000320398110400d0500b40d6072100050300c000031181c11440001384000004200890b03044240d245850283c8540e45a0719120400c40eaa6840282d43c0a40881e10038000501c012202e5001810184846081d203091070000001240c100d400c180c01610800c41c1000001255800400c01504124411501400312860070340b900b50b02c030700c10321020400700404803003034030080c10042e000ba40780954041c00411241c90030f081c10440c01d4000750b9600d882920b1070140c244000b4440e20100c4108030440c108000251201c89152009208001086040c402121490300301562030081451203201c00d4842c00070505001c40c0b5607c41c0105044020900c0780004140e0340702a40d001641d442c080f0420b9646401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 236599541 1250 236598291 236598337
    0x1b170c030409020c01090c2304020f0d09030e01020f0118080c0f0708150601020a17090f03060c1905031612060b070c08101107060b060f19020d08010308 67
    0x10035441030760000a1102d00000d052850344c4015800307240702c540900c2138500015154003000d02013090300326800450781110071004005280c2940141000350418a50924143c2203452020a9070311030101500820004034001103503580500c014100b02a000000304081c00040e644140706180c502c8010b001c5031000f0818140401080000151a07525803003240e07034440d520500640c2c0d418003904e138690110b0315a00450040d5000203481500260300c500301a00e60703010b0542001140c0c1200c1c14265000682200380c03101d6403424000306001d59802c041441e038440d50048400e002e10195480c1c2800c0010810802580034041e008408840c500e5103000150810b95040400c0a0141d540044040c540d000400030104442e8118507021982d0480594048848088864044038000608010701c83c1c0200314010001e0500d6000400a800041515081100a000443e40d81d00821008080c0c2d800801a000307415030108517688002004e850007204c150704554404455019800075481a41e21040d00ca075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 236600791 1250 236599541 236599543
    0x5060f06042904180b06010f090503060402120c1c05070e070813031e0518040216080c0132060625050a05100f050105040e0607080c0909010b0702011b170c 68
    0x162074082411004102540c50030300711020f4201b03031401404980b480c845085540d006961500881d400100034003c00d5070740e9000c0c8820b0403000300000100d8080c185611819503142002440c4000880041d162214054070740341d1328010040d00600325401d203500030041070940c40000c0315403041710150840d151900a18007a116040724011065000e0710100c65107654a0384a00507161206950b1007901c90900c03010144800c9210344e05054103103004100d0307407070301003038100b4000c2941d507002d90f0000425003402009141da000b251001c1040600300001000c40d00b617100150590440c3c01210750714a0b003c3c90101221041d0585807400d100302c0c110324140c005010381401803142141c1c0050a03074241d41201c1c201000284200c0c01d011003400e19260010819052500c81c07208a040e46100419064803080c00c01d84031014010301217a40134004020a1440c0e8480741b03511402040b00c4400941c0355101440003400c00d1412003141c1c01160b4104002c02c002c9240075040c46100c1036a44549961803904203081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 236602041 1250 236600791 236600801
    0x612010f0606110c040e100905150414100c0c060b18090102091e0d031b0c03080304060c03090b060402030c07050109200a06020c101b05060f06042904 66
    0x1245a5a00d4032078009502e0f034020b03071105469105503041d01c1003203002c80c0c01c000c2218107461038544c3c03039806082c5c0422012003660111000e81c1c010b0701180c040c0c2038907022a030b85d07140c8112400c58a0750804040d00094140410464000450a15090000d1940900c2c0180902840e5078090001c0391900c440841507110b00f4000101d10709070110020300740c41c1080000340030354401016580a81c80d5010308030803003000030001c4840b08400414080031802c0da51801c41c1d0b0480303100116481d4800003c0102c00003004548180000c0d481440542c1e16440d090500408481c0c031301d00041c003454104110500050700d00242c40e50304c02011140144c40307840c0c11400742d10358040c1110083ca07640ca003006500074003c0c1c641c140309401e01040c1040d51007400c041d0600c420130300c02d03200710700140e48443c0c02caa00d5450140b00303003001c100c000c1c178000c0c0306100101c1c402d01c07a01c541007038143c031300c0e42000060020804002d1400e07540024183c4040c00300e0403901c003d181c00d805000840800700001003010b07900c0756441d82c000b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 236603291 1250 236602041 236602061
    0x60d0605090703061e08031801022404050601060518010c03180308030411190312022109210307020402030402060c150a050603010c080f040512180a0b12061201 70
    0x804902480c0088010740101058041e40c0703420b00800e200c1c500c40f040b100000b0000d1b11030140186040030340030140d030282c000d103d03550241503019509003040403001104100480c24800e10f400101ea0516060581c00c201043e0800310401c00d0400003420380c00081c990780c1d9800042884c00301d810044a0804450700b00600c03000d42a024450000001844584009580114011403d40300d422102800b080030003092180b6030751524042d9102040031849100c1d90081070800350040d038030709030019240740818603407005080074a8180840c48040c6424902081c4d180c0c40d10400086130707000c0c0d00840141e528001e1010003445260000000f0302151181001d84401d030808004a42c0b81003103003520315242c42002c851705001d00d86410f0010300341d4a0705026401c681041522801001e41328485009600200104140c1c0c480c801e004401c59030034202001480c44800640c40e40e40681e242c4801c1050742041303a840911200342c2407001400c072400500c50035400000c21100d003d51010080310040c090300030080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 236604541 1250 236603291 236603299
    0x180b06040b040906050306011d04030203160609060c080f0a020a0e0a06080106020d05090604060c02010e030d020105060a05040905030a0305040c030804081f05250201060e090724020a02060d0605 85
    0x80008050302a2005007083d100f00b108148000c688940515541d1002449446140900e81d95a1452625603034803081d002170103071040e00e10f00311000e08a005c0340004c0101c115415551005c1020601500b88a0b000c4003c0181ca880704160602502c0c6804420000d09814010303903002aa80c80c019008100803404000083c1030602c0d8240e40d501c0c0a031401200b44240805402030400111025229204940c44e109000b4041d0742454208041107819900d00c0380304034144604003c0300b40d03030750340c0401281c04a2030059001107441d140110030301c20b106003294800740c0907900788000080002c02c04015161003c41c9490000b807256524244241300b280903510140c621400001e0102d50f80c1c90100c0d4800070b2144070341030203140e680d032240c0d00400c840742210080c22603100300d5001c0e481c60408140c05003810580b48000b14445484900b41e400949050b1a99101c56108403010071120b003007296007440a007203402c842c6458500c0290701035201c1d141400c0092165a00054036520007955074000405414090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 236605791 1250 236604541 236604547
    0x23609011518030f12090e09011e0c05041421031e04180c030b030102040f261203040204090b0108010506040b0a0506040308093f0703030504180b06 65
    0x10650380341c04242415503000281c00709111030911540364250310460764401003400405003180c859034600d5645900382010440d00c4040042c0014220150034011540480002205a100c01d408410350017240c0039401c0250402890008840c1c20030165400c864129010071070720181d481c000340302c5425038031046035030091340281c20103468000005006014460003907401010150101c2d070445000740d210b2010310380968510b40e1032509540e0000c014a00b4503080c08601c42800100090980e0065003000300241d2400c40200680007120801418440303001050391250000440d900340c40f41a1114610550309000012808645072580101580d41e0030a02006e080e585412005000e801d060300c06501c80d60500c203401e05149000062841100c0307004080c6450a0718503078814115400c078520803035120700c0c1e000c404a61001c04ea004a500b14141c40030100301070080103a080c2e054940041c3e0b001d4283e226a0050000942210469054504007032680400038246526500944110315072503420071408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 236607041 1250 236605791 236605799
    0x50d0b2707020c150d0b0d0203030d020a022b0f1403040b010302030c0901060206061201020c0303010608041a040b01050906030a020a14040c02030c0a02060702030a061a090a02360901 80
    0xea804030303006070100da081e14101c0c5102070800482481c00380d04500224400c00440000d41d00d05c0d88449413510b0040d1007070420304110740019065420000c4001c07c0740e13030006108000540d0500034502400005481602c0c282001c42c400c29101850000d80c0050082c080e016001060146441c8056082507a50b41c9a480c50140f03080102c00b44203100480c007d11816a9071501440d081034807606035007640d8020711180d5100d2040085040803000102c855541c07c2080b40d0307032204284001c5028180700d40701c14001d070825107084001510751040750115004075505100014010b060134904445086812030125141e21002a08205d04000001d600c900c0c03c8100189080701c4080208854008440820011042420a985034481c101d5162126003042c015180103180030406020024005000c5403407003682691410100e680d005c0c2d68412461800031499a540707800004160722503600c01043d0306001c51050f0032981018103c403110a500d5148842d030101002d0102d442c074a2000042001c1c85a50751 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 236608291 1250 236607041 236607109
    0x91e06030615060f12110f0403140618060402040f020903030c0106061b050c060705070b0a031e0c050901120e0d0c0c140a0e0a060b0304062a050d0b 65
    0x145264800e015840300014880b80100a070040303c1a568460170108250310360000d00400400e0f0322910002018081c040007000c407480070344051449030724860031300300116840c3c510b01070008055250300038080f0940028813002058a541041c4c2c1990085141c0c1c506104c0c1d0340207806036580d540c1c1c0620002c1488003098005401c283c003125070544038000300c501c3c0c0700c514510144410320007501d5076129404114803410984c008105960080c8140c541c0140c48041d46145070744a62844000603403605103c030403401400d003541e124080c0c0301c0c07400c01000740710f154090058042c0c40703010340c10720a00c1e00d660044007220350048000e10740380100b5150b24642d031041c040c001c3d8040b8502503456092214021030912040103c0c84030103600284410307031161030094489100740303008022000040d190100010005414009140113902c030301c20200b580e501c41d107413505a200b8071074058914070160500e0284031980080c100c88150081020100f1a1000b50000c40d2200c4407a081013104c0518410707488008003a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 236609541 1250 236608291 236608301
    0x30c02030910050a030f020c150606090603180d1701180908030a14060f0303340f062003070c020102010204080604060219090803030601050702191e05010c0c091e060306 74
    0x81d1176101003114405480402d0700f00d01030004402c60340d80c000c1c404451010020810386a001e070004004a19000d000000710b612908107648001e417009000c000440104403d00c90380c2d607001154a000c4a01c04050240401c4e801c906124004100760020b01d00310070f02d8543d41110081903000302007e0354a04218001c10000c1403400f00050b02500c4a2002c942640307003004490000c640002c1c010341c200700386c0218070100e002c060004409980e90003181c15500c0c1c040c00782c6c5441d0341402520741c400c2e120814113101042d240f401f8414807103c00b811408585c252101001c2e00e4011200d40760a03150034138541b00507402032050b50416643c502c40c0108000800c42075070002d0101d101901e01910142c0420320080e80d0307468641c010864241c005100091b06544560094105603000820740201d52803a00100c1101c00819041202c803c01c00d04005030743ca45e4114132080040c1001c0c0b90250807038500e5143d1f00040100ea0044c412825200c4500703140340701c044581e1028a0240c1101007059a689141980040c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 236610791 1250 236609541 236609557
    0x318061d10021201140d12030501091404020a030b0606130f080d09080309040f02090d120201051303080109020a030b0316030201080a0216110105190504050301050907060c03030c0203091005 83
    0x1105445000794450440d000741c96100c07070010015183c13030342003800a4040c03030900b040f20380c1c001d040582c0500120f003000d001241a0109a1800216541447c0020050b202e00100130424401400240f000603110482c46800b200d40040b4200c1d0b954880c100002d07803620500300310300c010010030480401c140381960680c404881f244000c0310105983d101c0c00f039812908501c102c1645410078044855107080c070b90405030b60580b205100502e0700c20150001995102c4051003964040d42e8441a071038030903024403400390802401c01150411000ba0740c0c0003402024140120000f568003c12005920341c0243c11030800450020265103191200300c4407000481141d200aa00141420012584047c01442216402c0c0300ca11016203003070a90f600c903c00c2014100300100d042100800c80c04101c50700e0516524540710095940c9030380c4030720708420107080d110054800040d542010f4000c21006804c1024421803030740c1801c0100703e40d140c96200742d040d030040402c415004864038104400347ca43c0980141401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 236612041 1250 236610791 236610793
    0x406150305061501091d060112050c07020109051e120114010e071707050906070201020f011a0a15020319180e010806090d020c0f13092306060901060318061d 69
    0x168683c0045454191600ca911000e003140b1149881805440b0440d903070000040c104039000e0504102d2041c00c40b6000ca078060b14400010444008540c1c1c07110b02e100050001720780c52050b00c40710078408021806000002c620428001c040014000c10a400c1240700751604000d4118969444210201c1da03902280c141d4001000a0720480381a08500701203030041545a490b581015a00c00500049622280099047d4814413507810b0800400340103090a030314840707104080c00c4401c6020301089480c40c0d045910341040c401c0b101d002c1e45a0010566200f600501088401c40d4100801a541c42394101d041d20780b0154030760000f02c2c0007100a00001e04803900c80080b03807800d644039020f03d5183d00a101d0002e005821609014405240c510480d08a990b4000c0040760283d6061349007200301e40c01d02c241242c14185a00d4007180c02004410b100420072010340203006140f401000041ca0b000e41406510181503440c0d4241e50070b0740202c9041058030764881f01c10045e640c4070750710002e10080000403903c86 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 236613291 1250 236612041 236612071
    0xd02060a05040c0501050702010215010b0c011808031506042d05011d10030f1505011e0c0b0a0e0f01060906050f0303030a2d060504150509040209040615030506 70
    0x41100d80c0d1151030b10036a00900034400d054100401110036520800f0103904501c07803044031192100961a01c2c0c0d0003485030001d182d6540341c039600180c3c00d4460f540c400b00303040d502d00542c40000c54243c2d0200c0354403802c0e8070304890b8080d41c0c1d000041c540e405140c00c02000034650800c0107403904a0142c0c000903405982007480c1007140e847c0d0044882109060742110740001c041d101168a0405075031200ca0818182008900c2c0246243c40703904490100c00d15220544509008100030350700101c0c0f40c4072404075405420310144001030302a0901070030f0355000b8000c0184800080c00b03140250700044041509405455003440f140d240303107018011300d01950396183d150010001d114a4500003d01d81c070500607000d18210781c2c841400d01c000306440601400100300000c0c03180314070000d50b107003803a0b0704440c4240080d241d400d04050204844000fa03104016004020003800642d4a0b0410680d02c20b5044171215400d540303070b03d4154041d02c1c40310317103800c80810301c404007204004000c107a007441440c200226401d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 236614541 1250 236613291 236613301
    0xf0f060903030522030c022d270c22061205090606030a02010302070501060b030408040e060307120602180402030a02071406060d031112040f0e0603010c0806061b010c020d0206 77
    0x80b110044071304a401d1503108400040003030300650410510500041032800c81c2d001002c0040708105001d18031209001b044103c4400b180341001c048060014102d900d40028012009294012003010b480381070f900c0d8000c240c0f002e07003803403440e003e0369049400b00790000d40c40e6440f030740980300241c0a41440305d007609080004e40540030000302c0034815080200100321110300d9400550095015500640d0303255242e900114802c554074004601551041962680c0c40d441c08009205980e80900040d1003a00400130400c000500b141c015480b4607041140140c1ea5061183c20407903801c0000202c0d03410900200c100440000d00c0c2e4003a00d0030a00840f1303070f1005c1c400076072a62a241c1a0450b002c950080c01c2e100da01000c02d209400000c20300c04400111802d0a40c03131458100d85400961020b82e4030f00c482c07841840f40d16080c01d2859042001907001b0b204000a440000e4140031000b00301500402010880c1800710700c2c00c511607a900c80c0610020032800c82a028025100c0a040d00c10001605c1307a040824 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 236615791 1250 236614541 236614561
    0xb0d0e0f010b1023030414150702151807080c0a05030307210507060515120a02100807030207080d0606091205060106030209010e061210050102070608130f0f0609030305 74
    0x100074508010f0440e196681d5102080c3d803001007502207189641e0303401413000410707040301c0021800b0320301824144c41c41190701802c0c00d1800540c0c14854159501c0e59062001e101d40000756180d6501a40c0140340880e43c81d09120581600c80485c0c000051081c40000203403040c001c650050040c00940f01080500d803504107040d0340e84a902001804d82c28038040400c0107040742c02e030004441c0356a01c0c0c12854440141c40e0282039940680340e50200f442048910720301c902d000c03068000c0b60207044010b000e0000041c0c00040c0044500c403a000e040c0400741c40020403040c480d504035001c991780f04048030f0b00e0341d5405d16404001e20046c054180800d8441d800480d0140d81c1142d5140b881c0e90100090545c0e0b030034100202c0203500900c1265060180c2100c0d28040c41e544c40014103402125290501000e140c038007001c030300840c900e07400f081c1076401198040c0304103903100e00d0f241d6204840b030702d40c030000001e5841c1002d80740c080340c1d0024000504656010041003865008000181d019039014440da0325443c80391 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 236617041 1250 236615791 236615801
    0x7020f0c01140702010302070f080c010f1812090f080a0b0916120609020915040605040b010207030b06180103120f1706131104121707021c05070b0d0e0f01 68
    0x190116500b005510650721a503402031010f14810700d000342c200702c0d444c3c0c1d4569841c0d101c0032044510002c041403124400e00240302d21142c5030396901041c040950a0407034007403085404880640185403c80d41c1c9002c05000c0d0619070024000440f2600c4c9542d41c444c11141c503103002c00701c00c4896800030f00101d0014000081e0144100a9502c01014407520745a1030101524811200321411740c0c032031401e400940d6841031054440e40c0d42406c1c0c0110310310300904110841e4955044548190b180600e000010390b4001049402d8a91004000e040c03625180002905045140c82440c80c0324207600c0044100042c0f40f00410506c0402e840b0038031607101885040c0e402c44801648504c05036905000291686048034101c02a003500c800c0c009103020f040b2212004561264201005184151070718070304000d2804a200041e480d40300640e070030620b10b640051840c003404c007403100c13502122350307800000d1042c28001e51004150785008540e41d41c613184038007405407801c00220023050140400300080c0e04418054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 236618291 1250 236617041 236617063
    0x130305060c2d12040302010b040908090f012a0f060c03020c07080c0d0b27010b0307170606040b01020f0d0306030b0a0213060f030608010e060a06150e0103020304020f031507020f 78
    0x309401e0002c40f412104500d40c008006070215902c400c4440c20356111440381e02449402150210755a503180c00500520041901e08641001100d00510080580300c090b81c0301744449111074040d003507103e0b04184202d2445214050031043c600402000580e070540c1c001c1020076021810358130360554030034001c0d440e03050541d641500078150045400014144c85545503100050840740d1101000300b0040245000e500750080c0c4050f955440d002d140342c44c0c2000220001e0002160308040c001000011a890f294060309450041c0d0315440b00700791036030082c4890900704003100c0460b0b90408442c0c80080241140b48001d596003203128000c2200480c0d41d000700d90720354070040131080c00c440c9070a10480d64003170315000703002c20141e40340000301da00242030007461b41e0302d01c40074010200c03030806a22034000c840c00c03540000340888034820741010391500014050410324007402c0c0141c80c0d94a1b0f00205511088165600c2d516004048054466086501d074044c003440c00c560807140340e18038070341046581e07a40d80c001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 236619541 1250 236618291 236618377
    0x309030306011b0506040308012405090f010c0f05010506040b01111b15070309150e0108010b070c0f08030705011b0e13140f1603021608130305060c 65
    0x30010303240e940034000c00010400115600803003500030f501c80e50708013001980c0c02c0300050b00d5500104181804401000e4040d04044100111140c0031040a40303c2e208044685004940c0001d60f40016801107a07904012030b0010302e4000c220819103070860080804864007032050b0328115040025504c03407820080d000d19080d0007001005200b04101100d039401245c00ca40c4005441c86919020360010040c00074540b00c0e440d0408075600b000b0000c00d80c04001d6949204105940284840c160b038010003060440e81d800709542e5495890f41846049203580317800c071540500c03042c50b0010341484004010010b02d4012002000710940c1c44240c080000380d0400002c00149480942ca00700e03161154207003402c010605800102807103800d0281410400c12184084034841302c2c4200004064058101c00c900c103440d06c1c6c214501070b83c103492942204015800504401404500620509a40e0294001940d000807c4070701d5440c094031119100e5210303031a512000500c2c3ca410340b1002c841c840100e140410441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 236620791 1250 236619541 236619547
    0xd1a010c060506030f0f161424090402040f05040b0405010e0612031303051e0d023c03090f030a05100b0a230a060e0d060b06040e010f030b0705030903 66
    0x184601c0050030028102503818024010100c815410400007003606242c50805480d40e440c400a250920000c0d1745d11100c4c402400310070316035203a0b035004080c640c94a941540071820010100901c6014003070003801d15041440010003155551118075000b00305c82c0c0880342400740450900911055440030300c00c01d4003156072034020a00307514200c2980203032410340c10200c80c10422020802d2007064043e03401980c182c2c0044e08844105030000c0d4500074001c2d8008001c05e1111084400203584081100841407504204080d01c0350716107001d510170307203003112691000d4400c80120f9820380d00d82e889403d2030391080580950001d05802c001c24144c0c0381c250400081c001074110202c50901410455000030703840281800040f5500e030010010035140364941c1d030000f06200c000401c1c04401c2a44d50458401d1000c080ca1003c402e80d41c1c0403a003040941c0c04403021542040c4400800c02c01d00442c4c203e00310b00c2605a0010400c40c0911218108990080740040060703260702c04c082d10180320643e1020202e030010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 236622041 1250 236620791 236620793
    0x50f090a05072c1006080105030a050d030504020a0806070201052202130903090503030c010e060601030e0604030c0c1805090d0311030403030207080d14070305060f0109061808010e030d1a010c 84
    0x2101c015914038080c2c82074500303e40b02c02e20704002900d400c070b400d01004031074000203104559200d0502409803100703400074840718100e034031143e6aa80703505900400b0141c50b40c0008045444100c900c0c00100004801c031403440c106450302902a1404550b01c484184208912240c4004c135910946410b90f00540b4607211249034030031540103080f5504064050101d039280008143d02d0800003031611400c2440009154151420b0050070480060810b41c10141010504442d1140c0440d541e90031a07418188039079076940e0340c40c00c4041c010540c0e010801c03000e41255007501f066216040b10748038405200595020850300e81c015000c90781000c001c0c4807008424800140040d02940c02000300b24020382c1d55508280058140c1000d4500098001000c22180014040f0783d0f90180642504560f04a1b800400da00003480000c000480314030071481041413503040e40d41103035101d10a0501600300e00c0d0003848030050460445999a100044070703040c151400070b420004c4000300d0646010400140c0d110706001c0d841d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 236623291 1250 236622041 236622059
    0x140f0c010f1b0807050a05060705091008090a120315080a1208090f0129040b03030d0b040e0105090703020102071415070516060815030f0606040507140409050f090a0507 74
    0x10008881081c10300e20801c2d011400107405400c0c1944604000c2c000ca4a291409a00340b00c005072440341404402c0c0568031032540c90a0700d4040d045400e10b818000d6658035078482d440e0020140d0050000307880c500740c18185551580042d4105480c45803000b080c1d90351840916500c1204a5010b0030450313070042c050021601c1980c0c0701b134101d0400012181c0405144200030708540c220b40e0843c4c4081c140750f03403612100d2040382030b410710200f04840400c41d260311540400d82b80d21440031101c5080380d840015403203541e95039004440300009000204500d00d0b1a452a84e501c01d0103000aa0140c41400c1e0001317102160303403d21960241000e071501c240a250b8035034403980d0ba04585011103030f9004000391030984204000c0030340c006000ba40c0e00c60000d4280110110070745644590301d90301942201110300b802000005156400040c2510700052956510f8400c40346c0e546401440f940801c0000f80001d006002c80c1c010b540500307640c220500b41c5840b0031542c5640c80c01d0f040c4000308241c201460400c50a64 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 236624541 1250 236623291 236623307
    0xf0611030924030c0415020a03080601080a0f0509010203010504050f01060903020907050c0d0f2703020607020a0e0a050f0a0c0e010c080f0c0a050c030304030b01140102030d09140f0c010f 82
    0xc000d201114030740094a4460b003504101d841c820001004101005420410f940c4500d1684050002d00790311540d03610f00a0184800030700d06c2d130500c024000132030440b6200364854488551104020005400c1c5070314107034043e41c07080c0720702d074420340c24580412650044c41c4d10090484a240d11101583c914540c00c0c00300c5080020605001d000d010721120411040034410410007001c980d5034007501000da00c401800c008210300200d164109000d040d0341d4410020895082a00d804450a503201d800600c0082c0300700c203907508210700704107025040c4031102c0001c1d04150701513261035224504550303408041c1d008aa150031010030018681c0003000203254050f0b401001c80601030034940e4602400003e1001d225071080e081c65402d507004060300300a1041c1800107442c03011086024603d00762a603215544980c50600a06d992507034001442c1c00541e000b007040329a000303a441030511540030f8a05200010644402d40d282c000d0241507040004244042021040c0202c16100d807036105038655004c0320b07202c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 236625791 1250 236624541 236624569
    0xa030c050a0807060c080a0203070225091506090e070914010903140c0108010801050c0301030305130801090f02090a06061e170f0709090902060405100513030c0f06110309 75
    0x7024070403801d004645880000c084490207204089111540321400500942e001021200c042e40f040c428072564035408a403440d00c4a4600b14104003850700c1d00c2d007042881c4880d13440f11410600e41000031080307603c42000c2c5000c681d19900c0c1c1d054003a5850124100d40903086403030100180a084050140121400e1101c110f224189000c034660303901c030b03602d11006000c4982d1321007543e801001c02600960780060220b01421020009129504001200c034001d400180002014044046026401740103000421402001c20700000e004185031410802d004204021050303001c1c44400b4009500c1242070f00451040712080c0ea07444510748000c0c0308908040f09640b11403010402030501091010481540050007504062000d1b0701c0340c14410030141c01d4548a41c000b03060030782400d00040142c0d4541050747c08586054801103000000110212481c2c49140014164072008050100a05c000482000d00b07607a580c1131801c401540f030b14400d85e05043c4103c1c541500350320030400503034141054142c0b03251748 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 236627041 1250 236625791 236625793
    0x90e06010f12050708090f07080715171005180603070504051003050105180d09030302032a0a050a02010e01050405060304022407060f11031e090c060711040507030e0a030c05 76
    0x240a0511404241c0c3c1c0c040e40e03210005111072061002c180402c0c88604440ea20400003482e040e0b01e800c92060b11480035200b411150580d8114005075240102120314105c0083e2416403085c0c9042c010b11940d60a00d409540c2c00f5450100c3c502d14045510070f44103000329002030091044a240c041003001508008003c3c3d500040400c0000000803000d00405000380e450540a200485c0d03040421407a05036400c9804081210216040000c660080200d0302c0701c0ca50304c55000c08081200c810b212003c15000c102c0030702442035030041414442c001c5608446540700f680c40d001e0100d1050011074040c001c6008480d481070f0b042000c10010719102c4c4480300071003a101d40810340c001150103001e541d500005c0c410f4851903110707406164903c0a910030145012100c12201d03040d804e2008010001008203004800c0b04403034000440c1d103040081144115829001b0040c0d80e5402c080c0c501043c1d141840084d0700d002c3c80c101008515490b003c0c2c06001c41c5200b90f03c0c01032400340b405440c100c41c000c0b45a0829501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 236628291 1250 236627041 236627057
    0x4080d0b010e1507150213090f0b0a06050a020601170d030b040b0301020f0c0c10050d1815090c0e15090c04030f0803061815041e02040303030506010807090e06010f 72
    0x200d031241a25003621000c4409140d84403189800c241503401c05d9010145c1c100f51040040001c09400c411160060381d42c9040c00140e400c80705080c41c1c0081c0315554110b0b45c8000070700e1000410b543c1c08001004569801d60a4501699035101a80d04c48420705050010301e801620083c01903600c00d07804140f203031200400100c0c1305201240030038224ac0c010440c04d22804800590720302810020004008502c109444003204407440060040042c050845d10045da251540d0800c0105034000840e03003c503036000044003e0501c002402e4000803d00c01500319261000b2400014501c2565080d143c4504036a03180701e0030f442540d004101c150342000700000c00c0310109200100215240c06184900c8a1140384496500e05040081059103a06100503005e903d02e01010001404a20215070b5500c05041d0360203c0c00c421205006041010308402003039009102140000603d07906400841c000e0200380ca6818140d00c3c0c40804640a502d036003d15000017141a02050295120710031101c032910740742c905010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 236629541 1250 236628291 236628317
    0x60e010627080604030207060203090f01030506130e101808040b0a09090e070306050901021804180b090d0f0503040b040b07030f2a0908070b030411090a0603031704080d0b01 76
    0x4440d1100790011031550f403001041108040d01084650041e21890006600b00762441002901e50604907502904050311840482c1c0740b038441189985002e01c00d26414485404c0042100d80c2d9149103c03d01c60078182400001c01801c2107607040c1009503070300580c1070b41c6401c0c20201402195400348050008100c21500005102d003d1031050b45108880203002d00303001c0d0302c0c5041c503000b91800a031105516920410050300780000d0243c1c5101c02106c103640110310714036055040728070f811065002070291000c440070440011004140b40041010b640c941c80c1c4080420341c0c0c01c94181c00300b01d0b4000c1c0f010481a0100b80410081c101440d80f01495150118504400031080c9007a0303094070120140303034181001030b44040040035502003803040c400d03e44804510324015049558410900c1102c071440000008141401a801c429000c01500a0880d4140c1c1c2414080d4800401043c40140c000458684040c003003640001d46440c007441e0480741d618103005030a01101c00408000c0541c50600201d461a46 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 236630791 1250 236629541 236629607
    0xa1e030b010b031902090d1103120a03050105100905091801180506090c0f01050d05090712051c0503270703020307090b0a0f031a04080f0409020705010e01060e0106 72
    0x34082c00303145000c2600ca04202d003601c03403004851403032000210300511050019031151152200c080d034105201d07409648060000c281090384200f0440c141c083e0000300c0f01081ea1b01a0001412161305a404103400500c07084200c070041c8160042950001812010918141008049a01c034031806c8000040191569001e148185840b00049905d50080f03805c00115020900085035070100035200c10740783d0742c0306e040001e2071072040700341b620301841ea600041100c06004102e0349014010b04032501d660901d003420800e5842920300100b50501d0091110104003620820503130340104556110055280100b14600c4d01d0503401070340215192041c0d140010241e501045484000c0c8400000000d00c1090a42070065680f842d801c9075a074034500240800000f2034a01550036038408400c1c981c501c540311483c00c100c40c1d01c118094000c2141d004140883e12200690081c010b061191008018010b0892202d070700341d071014402d840c010030442004020940c0a002d80344450809403041054030208003400e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 236632041 1250 236630791 236630813
    0x601140304062712020f0309010302070809060d060531090501020d050a1a01020f121b010908040e06040b0d031407150504051203010f091107050a0f0b13020a1e03 71
    0x4444042008403002c0140300c0e00340b14035107001303515101600c0c92150000c4000d5580c45801210307410158006500d100303101c401426500c00b00001001296100d0030f00d4a080058803403800b0b0507128420b403031801026200340d848a41c000d107460340c01e443c0b07001c1d00001001d0010030042c04e05580c203540170000b8614075181417141d68400d0f0440c1c000020920004003215903c030840e8005241550f010301144010184002107941e40402060040c03680d540d01100749019540c0c1c03100c407520041d070810700d03030a00700850030024100703071f80310b90108125594900c000c1106440d0101006038100c041c02e003141c00824030840204a458147e00010713883c084080d95035417018036002007034460301c55842040c0b10800400303100900d03410003080021130865042920b44007110020f4407440c1d503000d540e14504040d1102910569022035045410b0794014000c6040c80d03441405403402c100c070300c810303082c000890141140c545040d4054002c0c1882404d1802c00040e4140c120342440901503041600c44000002002c02d500f03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 236633291 1250 236632041 236632091
    0x6050613170304060e1c0206030f041e1e08090d050c1503043801090c080a060f050409020411070503070b0f130209040312150501110303060114030406 66
    0x60403060500e440e145001c64400c0703900800c1c10b5041040304000040c4d01c10004882c204089510414820b00c112036030400710b03110346009421281c04020403000d09654a00c903441140105c0941c9140b090005030940600140e0034000d140c05000f40c2c600658100707140c004580c103880303465800e04e0500c010001502400c00721600700c580d507103d105292010700b007059030111080c7da200003040c1541841c9e9141c000e5900740c802c40c0c0c02485140c10400c01c101c0d68107150020b01000d68400040256129080d14000d040041ca03450003042210011442c0240340b48a01c03021200035152041801c0d0401e002c00c030103800d044101781d074403d8070f401181d05d05442180c000e0a506218100442c0c2e550602c2c1380120304280007d040d080c04800400030002c2546850a40450b11941160f002000f60750318a410b5a000c01d01206110003189040008110610303040100320035100241c0ba500507421460a00b55503e1208803116400a030618039000c08103003007003015580051040c0c1300840c12441a03c084d655034032030454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 236634541 1250 236633291 236633317
    0x4081b011505030114010308120c070605041a1003020a140102100c020f150103050a17070f0326010b0d0507110d12061509060f091703030603011112010902070303060506 74
    0x210400443c0350074443c0712980001c0d007851102640c51032319209028090a01116200400c00000410081d103500481c0c1c10168060010001800c1c2410580c0f10203c07040ca8078400040d20b500410803030001011200202c940c018244845a0b00304000400400d440304000e03415445000e03d50944070026001b01e0700506d606a008181200280789203d00c1e040181998401840c2c940c0d0050003c56808150ad000060300300101001001000f144006148030f02a4050143e46082560b1420103a2241c0c05c00303a0603602c0007080340c4c0d0f52101d0240f940501e6003842242c2c0c41c100100040449500c440d00b146a202c10f49050451400c0b05600081c0c1c28440308058042c0000c9054401600300126442814007404c4002103207006031602e903401414522841c0619801d00604c4030340c030003000d48200c3c0080082e041c50385006ca0489540440780c1e91700d400a03103806119500b4035403866008907440d02560500d241e01000c031003660740307010a800003c2d4001d03d41076040546a882c042070740e4548030010900c00c440780c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 236635791 1250 236634541 236634581
    0x6051201020c280b06010c02130518121207021c030e0601060504050f01180803070605010e0705070b0f271b0619050c0a0f1202010e060f04081b01 64
    0x1800542000030411030035905011984811046208030502d841d0003a511848280701521707080d0043e140840c42c044001c0d4070076510180c65004103100d400450003115203401111040300b44440d000d07180d0a01c80113424000c0401d100c0c4100b078120300389841da0001000e00550364a00c01d180303000148003041d140594042074550040d000c041000704401070040c8035a14015003000c0c2080005150513401e141c40c00e0412000d0031403e045d20110740384c008001c0920382c0803280e0798586440c040700039010910032400f4884050001803015400344049480c0c0d1540503e0229082d62801e41c421100c000150560a0302d180c0881880f008810010500c8211040c01005001d003221000903114146007a0005c94000c000a001564002c2c900721030010b41000303c0d00301036813a08101c84c101840c10762910030180a080d0310039001d84c24410340d90040080c03071401c2c2d4001e02c050080e88512036612001641c282c0702e10040240060081580d0101500c00000c2e28001c040550000031103150958100d446c420804c20504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 236637041 1250 236635791 236635807
    0x6030906041e0305030a0c0905031e07090506090c0c120703200715030902030a0c03060b1207050a03061a0a15091d06040c0504031e060c1b110102010605120102 70
    0x11284000b00b000d09481403500202d15660020500e0001610200d1125210075850410074080d00d5001c0180c400501111520300b01c0800b48904c0c45540803040382c13140560720000c81d64a599014a0f4840c107009800c030001610703210b07410f801652119441000e5030140b00c00140d500083c070401014198020354a008543c141e062100101d100040c035031040c00da0000e8400c000e248883ca80d045070352103180c240059041c0107400402e0428185a10040140f105a8804004c2120307a1340000403d40c010f407501440c0c840d11224480d07aa0181e4000c990340070061074001c100007001c41d0043c00b0030744a5541d17800318041401012800c2441540c0100b1210310f444c0c81c85804580d40400c1c513000810b2000c00584424071001041181e1070b00180196004946911040311018007803c04c0340d0007541d001200a0f48010074032081002c454000e0b034202c582a041000d50075406124100c0320415030194807002c2d09410240c0d503043d2a403580951064155500c03440009080c0e0f684c01c0304014102135840026030b4904007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 236638291 1250 236637041 236637053
    0x90612150218091008120301140a03050c0405060d0209100303030f060e180f10020406020c0a03150b030f030d090605061203041505090916021203130206180603090604 73
    0x20030060301031648103001c0444621416411181e50302000e5a180d5480e071207110003100300ca24103402840a80c481c01400c4048003101600441c1200d1002ea000b040c0841044104a800c82c228071014043e944000d0401405250581c41141c1144005207154a82c0c889640403c80c0898101c43c0c8411991100504106043d014018040e40403215842040441c0c113213686810000380c0501070a070140c8448a0b00d049450707040104000844d03030503041b01d8030700c40d403040d042d4040d51150044d10014098500007200c00d041507009d1320162540300410340782c00f03c110460b8200030480420040e030f05100380d00000180701d000340300900e0304180c1d010300800c020301e00e801c1c2074090340c0f4090f100d40c3c0500310382d42403007103481c5020090300e041d11101c0c1a01e4000c80600c00781102c00f40541da0003668014841028400b010715400b0501c07101464680a5038281d200c09a98881c09010071141700c51802100500c003c010302e005c0c0010228580300c0b0010141864003c1d01140c01a08200c1d041c0b42990b0101041c8414808 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 236639541 1250 236638291 236638313
    0x6020d0f0239060c0703030c05010b040518100c090e06360603030705030a140c06010e0103060c09080c0f01120207060213151209020d120306060e1507031107090612 72
    0x3000340e6180d480c4c4502c10801541e2101a4880901006030300e02001003000401c0d0411403100400a0061001e07080003200d04800d40c0c00d0401c0009581b16020458050b00d40034010b500001080f5103030058021300c4c144410b02d8185005144542c050041d996035440c45882410200d000b000ca030072035406000c0d0b05000c40083d6071000e00254030070361051100c0f0000610000880d010700c1035078a0801214284d9050001c003901816011401a024400c0003091408110b42c5650480303000d100d0038401ea2180c030300281e0310f0b8001401001d000d81c0080300300e4034940c1007001c0c40e5610f000040c0340c08850b40102c5031040007281c009003001c40d015030300040c1032070130306010400d03c0340074189002c1140501e80143c60058411200311940516040d25920300d4010740d603401419003891030700040040759050150900900825a5004000100341940d10200550505040c02c2001c030300140003035858200261016a64191a10460031085c0724400c00495500035a020750001131418034110100358104c1e26017070740e4141c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 236640791 1250 236639541 236639653
    0x2030d0c05100c050d0e0106050d110d0606060507030e0f0f150d110703030b0603011508040602090402220807050f0607050f032704050408071209150206160906020d0f02 74
    0x7c0e0521809100e0b5a82d00c0c101c82c44480e40c481014a105d44002c40420021b0288a40c05041c00385050000522140c1000040901c0b6109070317201c2c80f12400100410a80ca41525071280d0040587c0304075008500346040346d5a60141d59014007410316205014030380580d13521298040c4400c002042501c10140c05020302d043e10402250b00900b17660401c61007080c035800b803114120411a0820100e402d00030f20750704403410190042c100390350b6080e411024a003801640e0342018039540b12000c001440b41400326032881900c00041036034002004000421145410014050b42c1d03a000d03d280740400800100002c0100c0f40000c0500028043d400944200c01c41d58404e8080c0214200350400c0300086034002100d95690703019070704002c5442c45c801c044400e00f03001d4110351f500040404007410000d40010300700744100c4001c444a0280313000b441086941c64118416003000d60b2240b003010706458091901d0301e40380707840d520403112060070044016980380d0380c0354090200c03800d080503e500c052103484000d6000f6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 236642041 1250 236640791 236640793
    0x3040509341b0c05090115120506040213030602031f080709021b0a03080103032703060218041d0c10020a080d1407051b0105010b0f0a0203040f140a06030902030d0c05100c050d0e 78
    0x51410000541748a09440c08994095509e07070004046079915419140484e040b1010010210380301c0ca0310400940c415540301034000040f40c62182250000d600050940704142d01038901c0741d29042202c03010390020710345048106100070180d003002e1400c005440b0003d000341d0b03d07188994950305010709003214207800b0b82d200808107640403036851312000c03445044903032043c00165140c1558500358101080d4200c42607200341070440980712800300500301a25944c0b2103003511302e40d2040004100035003101c0d0030901d000d40c0007050824041a404805040e00b50b8510368085103d0710752040040702080304441e038201140003c98440c421000260040301300034030b004000c0005504064a9400ca402a0711044645c1c10000a180666030f00c24802d450040c81c4450aa01c1599240c2443c0141c4004c4c0314003032030140480398000207a04d03109000c0d2a603041c6c1c014014008420340404129082d0b4411034050340d06100e28842e40010841900ca0781074400c2c0036956003030b01c404800300c8110948070781d1034411440b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 236643291 1250 236642041 236642069
    0xf070201090c051c051c14030112020120010501080d0306080c130f060e0109230712021303050303040b04411204060203040509341b0c050901 62
    0x2441520701034103440c3c04440070704410078512440001d0420b0894002c0086c0504009041030b85011007a003101024030b501c0340000301141006030b0400e40002d10a02c160300074039070340d003c000d540600c00400000651300c80d14080b142a030313240c041c04d5a03002c2e801440d0560180241d1002d007541407040310003034000107024040203044240020824108416500c4c03e2039030f01e04000d0b0910345241e104e0720007003800d410124610761707503146600c00600015a82e642901c00703c20755007185a00c00684144900c610b40c41d1780c51215004100480250805509a205000c081401201040e02080618480e510803140310300f0520b0b2510300712070031203400f001403009211030343c501c1c1c40900450102c044c034204040e280c13141d00d0344848000e54580325102c40030b1000220b000a01054a41c0d02200420644034141e440006640315241c0750364084480202e1081881c035440c117205020300d200f03880c0350740030341c03da02e00941c035056580d045000345410504115140d0060010412840c20200c01e51401041c2c14401492 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 236644541 1250 236643291 236643293
    0x31f0b13030b0a021206210d0909050703020f1b12030103150b0a0513051e010e010303272705100305010e06040206220306060905070318080f1803010509060f07020109 73
    0x20a40d17401428981c4245041620001c101650754440d07915038100608071000010080c50141c0318214500918661602704400a1881d40c024000c5036035916140300c04a1510002030b01400300c03181c49003040481e83c0110502400f189007070101440c041c5000d00400d001c039410404040b02215840c41115026100d00700d07041040d0355030402c4580385c0c1740300d181011400d81d45002c0c100901c2032078484900064180c03140086903001160380510b0503244030b906c480c1d01010030b500d4015803000b03d0f4803901c140401482020f00441001f00345081352000c403c144100d8401a0411010580c0c604840e220f901081d406030400600c0b40901070003440c00e51500141c40c2908058000c210b2611a100003501c14100510f020040078038080e50041c001c54001e442081b1054452060001038032003075500e030700000d062a2968103802020303104030348016070140320b40d0301e03040701c222080c0740c03581241ca02860200c3c60000311071078540b828020180b03c3c1d0743d020054203040ca0408a400b01e00d103005407804086a1415000b50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 236645791 1250 236644541 236644567
    0x50c161401021501270203070324030b01050d06180510063c0815040212030c060f06030c0d120906050f0d11160308040302060106020a08031f0b13030b0a02 68
    0x181903a00b104050132003103011400c00c1d185c81d01c017943c0300e410140c80041081001030745540603201828036640c609108013130b8859414100b9105001c0500700c0b80711100100410314180604540240c4a03940120382441ca1442c2c081c40d079880b5400c00e0307605420a02940001182c1c2e440742c80701501c2e502d071512440326103021103141c40401e007007400d221040c03461480d03d501c1046000300400130b0190710212589130405480131021014184c03022030041c1e203900c40b0111011340100c180c5803081e543c140240070136070300c0c12896500401c1c09407c141d05802005c41c9030140e82c48901c072281002c0c1c014410010702004030f0100030215500e0350b001004111092004882d642007940c1243c00c1c982c14a0000b080200c52000300071068400c208014150b00219581201050741000a1038403d03030082d0281c0700c09a0380c0c4d10042e80c46800f0a0030060001204200081000e01404540208070502400e07400000d501c5400c0340d400355000e94117800e0030040e244401c0042191510b4010b5000c800e050096007041c1c583c011300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 236647041 1250 236645791 236645833
    0x30e06040f0203010b130f0b0a03050c0d021c05160b03010b0a0503060a050d11040b090603031b03300c070f02100e06270406060e10050c16140102 64
    0x5184581c825000001d650b403d41100c10348041c0140f44149000b100702e1004010a03800c0c14225007030f420311100840c54034009260408030380e02700300500041440a4100600c50349003070400c0f40d00c81030000809495070400d6124000883c40b8400501ca40c503019580c41051200720741c410f40200c40e00300300500031030303030000300791010f1024a0500076126210000081c0d001b48450300403640020307840b81c4d031100f0b000c002d11841d40d1145013940c00300072401000d000d114602d03c1c101c95064059004000283e1400c5a028400072192a030b13100f900d04090400440d010a0803500c12850a121510b4000b000d14140614140d500010030384021480c0c41000d076100e010144c01c1c1b140181c403480000c400440918050103483e8648000103084640d02c10480c40c400c004403440d1010782181000c01d000084c01d6003001d205070f07001d5070102d450f42403045511a0030032282840640c441003c002e4288a07203485100208850900603030519011601c0c00e05008868102c0a40e101203603045511880c054140404001a8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 236648291 1250 236647041 236647043
    0x20c0d0f020d15020f0909070903080f0a03060509040602031605031e0601030e072705010b03042405010e0615071a0703090c030503090901050603070f08072a030807030e0604 76
    0x4a02c1066501c1c1c10450110851210303400c5000d400054644401c020042c010b06c416070041307501440d1342c4c540303a00c1110101c036075010007402002c0c00c215403c514a42c02014111303c042c940b90100d04203460302c02050030101d013954211400c079004001d002c800c002100840b80c900d11240b82c40c509502d04040c004411040c1807884481c40c980311008a102644aa00040c14641080080390300031603840b0300522146680d002090110302401d9405030f8a503c141c00341705e04030b80303400d10302d14215100c1d5140d142140d400950a035100c54080c4000e104440b03200c6c021507000384006903c3c16501d24212043c4110744020140c41d00101a0400081000807008030012a07481281c4080300ca2954440e0810790040c441c007800034002c0d6140c01c41c008100a00000144400341e019507040c000c80c4d0341e800900005000c01c0d1100c0002c290303d0f442e14440d49109e0501d180c9c0c06001840c280c0d85075000b007007401d17502c1122501c0c14811070464072140c40c00d05410124290b0000791504c0e0401400e07244150f110b444940c0a44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 236649541 1250 236648291 236648299
    0x152103020a060c1b0b01060801080a020109030b151509030601120f0b040206091201051803041d0601051b06041407060c02010c02030a0b012303030403030f030f06080304080d020c0d0f02 81
    0xc2e04000c5110340030801e0302645034400707030820320704178103140320400c10920440000a9006002280c58003001c00c00c5800503606859200c040350541d03669404219008102402e03101c0c86040e8901d0b141c0d22204410800c041c0744d00c07901c2c6d441c6e104805050408405801840d6500c091800e01800280b100d40e803104a03a80160305c61159488510000c1c1c1540300e4800300c680e006000144402a1034410340c0700f40e024544084441d103508120740717811902c902407485014503002e40307605d16080c1040b00d0700c0c40c1c80d88000140341651038156200a45141e5110040c114011540840200700c100010304d03030303c140b0107103903071000f00710700c074a030040040400f030103103000034100108600740e1000c6480c20800a1041580140600d200e5a151124100c003003403205c0c01039a0035111590000c001d400d01108660903650190b841114980c0c6188058014101307058002d070a403907803130000194a0780c1c10300c09040a861004050040e8841144c002444c141c06882d11a200303513204074090002504142030a01c850364151 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 236650791 1250 236649541 236649551
    0x90c03150307030501020f180f060a0f0c020411030403180305032b0c020f071a0f0c0a0212030d0e190f2a050a09050609011a040801152103020a06 64
    0x9000c42d06150240e44002c2c0150b00124100009200d14000750805150310041204d4071100101044074081d44c4403102d44c0c00c404104243d651b9180704101c40800c1c18010b06018120743c84079800b040c2101d48103a0f117085038400c08010721041550006195412194110210300b4030b908548503140c89109000881c038200198044402800e081039040c145800d00148081106640f00c50019481d00401c058000190240c0c00f008244019101c41301000c0c00c408100031800c00d10422028807255100104616040c800c0c1450b40d40140c0d102c4141110055080c400b0b15200c0d03881e903514109a5100090f03020301c5811881f900c0c5d0000340345510302d40c0c0041d040340c0d44d9501040c0300d003022481c400350090a81d152000300c8600b100402c1002c001c0c5001c0390350a5a001d0789055440c0f0119084850950303c050340600c110004100c00d219107414030300d040074405441441d0644d1824442d08440210b28805005c503101c0310200509540d80940c0741290040c8402940641703459072700207494144e0324070003d054503911 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 236652041 1250 236650791 236650831
    0x504090507090e0a0c030606060206011a0a080c0f13050a0f080606060d02040302060a030219050a1b032105060f030a17130902030117010c1103040501051e07120806090c03 75
    0x70000c0315241031708a4031801c440c1d9128100038001c1d160340d001d40409031003800000100341452450b1400150308140c1514103128400380200c4aa140240103260504000e2086a01c680c804800800c0d902d070340c69000c02d15561614007404200c5100785d0004582103c81d00b401c000b820b001041c041e6201408075000341c0e8842c00c090300320f40240115040617410541c040b500200580e0181d005001c1d002400343d94011500d01c10300b007155184035000c2c3d00b00c000392048484135030740540240840420391184c01e2665004c40340b0011101c1c11480c0b80034040c05291640148242c604080042c1c4116000c1540079108559882d1120f203c988111250043c2c480c2c0d000440071480f805c0003a80e200980141c1d6420340d66542d581d64a207441c03003200e02041140354a84004000070340d000b41d0068a88160000c003031400c062411005441e6504400000c20020401c840b00d4800b84065800410343e8a102e40303a0400080c069400083c594107009299502030a081c03802e00068900c003d05980d80141281404280c079404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 236653291 1250 236652041 236652043
    0xc0f0210020f041a0301030302010f0510030201030903020f03160308090d080106080405010b0a0b03040212070501090501031503120f080a0513140f01050a0e0d0203030105060904051e070906090504090507090e 91
    0x7541c3d00c12079056000b800e03000445131541006504882c089d90081c000c00301d8a0702c0c0e42e000c99009640060b0349200c00c0354100700550180e0041d501c424081d00503516610404001542107a0242c1081c0f00142515402c1104042d00102c1e66a080030840c001440070251048028086c14410700500c1d091044010014003000f2094000391508100500842c0c400d0340e5a00154811b80c100351001c901c15140500e0380703099107a00103401400c03554142d694107185803600005400808890001b10f00491604a001c000300b040510040200102580d1f240c000c1c00e80744d64010b01481003d0816141581490203110150b036210a9405140c0c0e0400d2002c17003100307a1403c03a145440048490407045508103810444104099806009135950180568070004d000c5101240c0300d12090050740c0d072241c4240024481401c0176404164480d90200c1e06460052032901c0b078003c0e4200403039080780007170092042444400da201c0140c4009040583c0c040c4949034095403a0381c0c542141d4016040640d907150244403050308 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 236654541 1250 236653291 236653297
    0x30109151d0f010b0a0f0e0109080304030b06010f0f020601051504081c02010c02030703020a1b0503100e0106050a0b0a1110060f0306060510090902070507050907020c040c0f0210020f 80
    0x4002803001d80180c1541041d4200000300d07250250402030500000308628503008846880c2001d644010101c04840c0003a20a0541c070100c0c503040054498010945000401c01000a14062241154a8903000c0001400f0b00302c0000d040c401c01028240300c520503a00011b0282c1503690403221041c90703800300340300388400340100d500c0785015104800d01c0200f0350120700c10004501000c0e078002d000c64800b09000ba0303039a200760503000303005074800511032000c01c0003c0c0c03080c94001e801d0b918404a440d0364500003847c1035001c544890850b90b444401c40140c100901c50007005141c2518100340992034952009428041c0d04844820b2004e0411180464002840500c01d402407403d001c100554444401c1800401c9900040300c0315482c0c00008102d0f8038245110f440404001c1d40d540b102d4908010070311b400ba400c043c0d0b040301e041c4101e2002044a50790f1501007803050f80715600510442c1d20306002c1100f42d0b01c606c45501c040c445050b43d07611201d075020490343c000203000e10002da5144603510008540d44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 236655791 1250 236654541 236654549
    0x40602090424172503080301060f0e1804030807090302030111040905150d1202010e06070809061006022d0712050615030a020906010302070204050a02091e030303010915 74
    0x1030b2070304003500e24081040308102c0048200c0400030050903222072003020404908410340d5001d5020200038212122880006030404402078240501a07070340e03507103080c40fa0700b082e00540c3c081000040c038400140e034003400542101c0c3c0111542e18103408044604102000301810280802040d6000a4015170040c48400c1c021a4090001c009583d9a13031880e0105800c14003070881803d040074003003811450784401001000100400640c2d42002a0303850480c00004011800159501d8a4900c4400310f02842046e102d6909ca40f070f51201881c1c1800300c1d9050460007000d04071071080c01c003000d11446030b00203040481428400d150b001c0d002c6401181002c2031100da9880c2005101c2d03141c0105001c0045581004050b2103081103440ca070311507091045291030803030361403500b541c032500d0303140054542002059081101810010b01c0c004050700400c00340c0b00d080b20001299500010600c03c02e04050b6080c1c08440c2c20107008150010f031400c0069103074401071060500080d150b0b12419142e031904050030000f4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 236657041 1250 236655791 236655799
    0x180402010c0506040c0603180c0b16061a01030c030c1d060d090602090117040302100504060e1605030601050d0f020f0301020c03070308040215030705031f050d1103010c052104060209 80
    0x545400c4c0342c0b4254011781070007417000103800c000c0c4d002000305030840c55201a41e40b00e03507050291810076000d0703e41504582c900d0b00d4049101c1da680008100d00d403141040d0364503802100205c210f803910001d02034582c1011038804051801403103881995012070040d09c2c0c8115507100c0c40840302c4103000248140524040c0d00802c1c0d190010342d50810101d0b034028285900700380c13554904062a03c1ca496000710f001c54015000d41c10500313030703c0348508260b4445944036105e09030000d03036542c0e40c004540c80c008085401d040759800c02c04040c0110310301003002c1801400b0494010000c100c50f0b94511940000d14000280225201420054950740a405407110444034a003180c2d01c514050074010000441980c2c1603001784041e001c071204640801c0c040341d208801903258245540c40d1f0126101e5004525034030769448201240000c105540d88034110085c1e03502810a0400c0754481e0020142180c06a04070712007808000c00c00e0788041c04003401d044070307550384099180303015543d030b41024000707071003080155584 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 236658291 1250 236657041 236657053
    0x3060f04051b0103060b0a2606060d0e03130303180e070c0f0809040213031202010204030b040f03021204080a06050a18021003060e0f07030e1204050d0201050405060f09090a0605180402010c05 84
    0x107c3c5074408411100600b4814141204e0300080341400c400a000b83c031020f17084401041509024000d41e08018400b0403600c00b1240740031004841c0000e95202500110006000c403040d03a40600d0681c11181c016158801c151510360800390005000b40305411001014540c00841c2d02c0300307011120081ea10100c80c00361041d9924000829400207040a5000c1214945a0614080c085030310501c01e5906690703003d58014041c1c1c456483d21074500c00141c46c1141140714101c1440881e2202c0c04c05072000780350840041050700c00c2c520742182550401440030a03414030340b407102050609201e14910119806580c00ba601680c113460403000341005801000c0f120041d1002d00c0f6031400700c000b50522610a40d5020410500010000c980310300c450101c41c08001c0b8140410f0240c1e180200006840303510504000745025611030120300107401c00c030142295481c0100b07800e03d081c1040c0d0049540510b09900411203170f070034240002c1010691040503164071414000080459000f03818040e0303495041b00c11211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 236659541 1250 236658291 236658307
    0x17070e03030d1505030f01050f0103030e031c02010e190218071107030f031116091a0d0501020309010b0a0e0109020306040608010e01062904170a140c03060f04051b0103060b 76
    0x1980411601c203140c040e11138546c3c401c40012062250601441c8044821110f036440e68401320350105241c1d4009030b06005211905846070b504220f8028960b0080d00003080c850041036016045c010990303c000b010802115401005139100c00f5800e18401c12058000d200b81c5490400311540820030707a92003640d101c0e810001c01406070b00302e1001160ae103e0b039648090b580100d00360075126071304000180c1140008075401c0c020030036140c110f40c401c940090320741c124480c1c3c1c06000401c0c03114804429211654000203000f030304042030145180f114000e850151241e803800d903041c088148143706e0100825030100125030540d0302c41c1c01c0380000340a918002e005a07001d6112150080500c3d02c60003420788900c0c4016100410b1142505e610040010341c103a007001d1401c0410a081f02c0c149401d442140214021034001034080300315241409400340c0201440c40d001410b140c80c1c01d03809010010018907600410002840000b42080d6861280341180c0d50300001c0030059003d809981c02500c010000400c460f4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 236660791 1250 236659541 236659571
    0x1206060d060213080c0405070e1e06091003050103210c0f05120304120305070e0d171b061e16030c140a051309090b22050709050108010c17070e03030d 66
    0x120301c00c0d017100c0c100707c10f8a515078282c0341400c2c0074240d031340c01c00c210500d191500b010b60780d401d14080384041d2180f03140081d4580001c40c5480d50109000c0400d13580e00040c41441900668402e001451000c640407000200c50060038694007410000d04119180c43d004003048000c0c800c04000c0c0c400d2030003203902c90500d0320f011504010b401c0400d90000e860800011071482c45443c6281d07a1160140c00d000c0b0410454a46043c0b00201c203909401d201d0080000d072000d0380a80300c5280004000c00c3c0a090182450340700a1072181810180081d1400c16800740409070841060f0341070155285d080005080c0002c800c251400c050854141e041c924011810501854001e0011701881c80100b40750b880d01c1740c45a403505c3c01c075695804040c060301e20380da0000300401c3c500102050482100382c0d4408810101e942c95500d421010f403ca81c80301c0d500ca4004110000d0240200680840c3c1030414007204000701c00d45881e103040c0140920104a101c608008264600b40100c03134420001910502064400e10105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 236662041 1250 236660791 236660803
    0xc0109210f0305010302090604150b0301060e150a05041203020a0b0f010801060b0301180b0a08030c031c020c0a03030b0d0203060a0c0810080709110903010e0c0a051206060d06021308 80
    0x3000108040c0301c000280d0512910865042c4c0c0c2c0d00802100d440e48400c424003004040f080c0d0220704d20510000301103102e00d001c001460007045269902c1c69001d0903007040c4140c2d080c900048400d00f030b00600c6284000c0d6000001e44098a0a0511105d603003100c3c0d0904030301e4030050b05009440d1084000a012200002c420b800d030581c0d44940081c0101541c5188900042c4030034881c495100668202c60113041209801c19288100000e040920844d12944480d04550005c2014100e40c0d10015076074032460040c0c0c5141d05134402541e030850a080c0020041600e0b100344820040030160b98030a10800c6541300c10407000302c140c014045540b6403a0010b900070050481e6100d04000ca002d440001d200c01c1d0f56500c0c1d60094880c008003402d1441d04e01680100900480045005216414440040551800d01c1902d002c103071818003c040e040f1900d828051440816088240038040e00320044224450000ba0981c2110303044c0c1c5d00940c86030441c200f100081c09209004000c0391321141c03000841e03040000d54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 236663291 1250 236662041 236662103
    0x2062809030b010602030a020c04020a110d0f0305070801030807020d0c0f0905180d0504090b01090306020a030515030c011b020a171c030b0f01050307140f041d010803030103080c0109 80
    0x445543d1300d4040a0b80c2d01e00034140313240e0040c0c2c451a01d114843c203007034016044040302401c0281c2240313550b45085c2c2c01c14501e4000b8000080c028002d8240c041c1d85070062071b070440c0322801c0c80b541c03550564407a440c4d14481d086e0080e004101030202c1404109181c5e40842c01401d098010304405601d44140501401c000d541c103040c2040808051000503a02040784031140f0290b0b103c50303150500d0000d01d400a460700d4842c080c18002d075890b000010a44e80d00090940c84c1403960000340034603201c1d422039800c900c41c0281c9400703a48421a5841640d0b041301e28110b0b00c40c0501012003842250b0700c0003441c0710103142c1040407100340001c1d600604180c00110342c03481c02011000c020300441807030340c201c0440300b0640780164005080422507030f0300e50003403000310703000302282c03501446c24407518a40a480381e210201c600f400d2540040c042000703248032462079090055031003181d641e42d4500141c003a9039000602025101120004403201040000d6021039030407648103180243c000c40e10210a210701040101d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 236664541 1250 236663291 236663303
    0x12010e0c03060609180a020316061d03072105030d0902150f030103020d030c0219170f100c110106060804030e09040302101a09040f170f03040206280903 67
    0x80d0061501103441885104040d0440010781e40f802042018040c0c95903c441890280c0503c510260714184030860f982d48141001c980e00034640030300280140b001040f040c1420038403021805103598089091411200503c0c0c50000c5000e203080c946202c41881c41740149a0320000039540c4d07041c4003e030018042d440c0212840213000c5c02031070f41e658140c0709150740e0b020768110400052006280c203034941c28646001e03150414900e05aa40404c520503800c14a05c0d41604100e04200801c1100d03007000600100079402800a0240a8980964403d000c8034030246964039240c2007146548030306070b401004e800c04070003440602d0f990360700681400390688050300060301c182c400440c01d0501d40c134914000e9515a00402308290030780400001800e00c10790340040c00c105404030440039079510700350501507030180e001d44504500500c0e0004904d102c1c803000510030f81081c00318010381819a41a203500c15019510f46a5070180380c1541c10004010005c8000548120b8048003010742e4400394040643e44200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 236665791 1250 236664541 236664553
    0x1507030b0612100806040804360f05011d01050d0809060f0406030b01030c02100f0f020c030d0c08070206130c03060f0c0906050f161401060810060f0303050703180512010e 75
    0x9420540c88050031100900313025010023080081c1c15410500c50800115241d603d80f90400007800d03803c6149041c40704449907a2103451099080c081449000e00405032104c0301540d01c104500c5014030100c051203043d224013402015241032103150001c88080100052400d0b41e51183e1010400154019000344d03000a803802c0f800400341c0d4021712078941c030791a80d6002084007030103081400b00504402d40d10300c01d0894650540075440521800a848034140c045c1c095074542010b0505001200c5600a03250304000194050101c0d0903004070302160844040320860580720800e050a80c0c4400880c1e20080c407581c6414440700840d2503540c0070384952505591190301c2d503655030000300c500380aa24104140c4075410458140c404010306e10488000c0e02c54401c03941810b4802060908450003a40610f001c1d4001c0300022102900c540b0071038020b8800c2c2001800f08074210348009016001d850401400d011817414880300140183c2000c2c4000d0000918001c2401c1612000c203020308145030308807170b40d031140b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 236667041 1250 236665791 236665799
    0x20d020c240103030c0b09070306020409060303261605070b0a0614010f050306010302160807061e0c080406022203050c100215060f0a09060b1c0902031507030b061210 73
    0x1030921075049030b805075560303c07080c0311503112002032410282c0704107082e00ca0703000c0000000b566030015100900c0350890000d40c49145040c05401c0d0f6006610710380d01401480c250074124551344801b690003107241290203a0840c1e00790800e44aa03c100349000e00180344240030001580040e4004009032082f1201540e00c440442c00155420000c3d1580c103000720380288009103055200394040c141c40b070700000c039011101865848941780c690145070b041c1d8243c0e49440c0000040701c1c01e002540c10b20a81d8000070444502400b0008010000142000b03024940000b12006464046c442101c3c1d2208111106480140d40e4540700350b4034148000158061000715464540107030021502501548180a6401d5a99a42d1003004140004600030755840700c0000004220b0160f24420203015103c000005599100c100218491000701e101365042040c1c180508030340141c9002c51612201c10320303284a03800c60707150203100b580035000a01382d943c1c000303002140c4200552001c4400b01e0180340c5c2d400703d841d021a00c3d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 236668291 1250 236667041 236667103
    0x12030c0a0306080a0b04110303070f0b010e090a0b010b0a050f1902060a15030f050f070915300c05041406042f030c04180222050a0306050901020d020c 66
    0x240c607001400c070301072a45c00035000c20480c0700101030f804002030589260044a50740c2403414041d460003a070700d0a40d208014400c1800c070714512600103e040c0010701c0c07000f040da5034004801700c0500814800c060045030419406000d403082c1d5840c86401c108560725840e0034840c007030710000c00c580364030018030680001c00d8401441d40b1034442c4002508070382c210f031582191510321075040c2403d4210b1740e91040d207668840c00e080038080800600b0403443c01040c420300c025440c4d44e401c40c8a400c00308490a2640c054800c0450304031500380c5c000010340d54904609414180081d40e0f05540c0e22260f00141899003d1f00c80c8203040070164498201102e08008000d140800210f180c0c02c1d0040b0744200080c4080800c0306014110069a071002982a480d4500b54403140c16404400d419244200e0007a00841c420b030180924500c40000c170f10803223010310042403801300010f0b5004003600c406401075503100003244801c030080d012030700703a503074050402d5540b1154004e03240e580b407100c91003003e070204440b207068a04601d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 236669541 1250 236668291 236668303
    0x109050409050606210a0809060c070807060f03141302010e130906050a020408030306090c0c011a03010c031407031a090c1c061a0c1f0203150319110312030c0a030608 73
    0x412900101020820751f40c2e5851158080102c140d4425014046503034480e04c00c020710805003c0b080c0281c0301040c50302c5000b80400043c0003866090500b088100c50302045400481a8030100648910040c00e1003400140d600c00503000c9882c0d0001e0202c0703540582840349401159a013031003907408103e0f03503035400c88000882c0a98024440d0a030420408904e041ca00001c8158000083c107a82d18070b02001910340a00f1035940140c502041c1819404000180c6000e129244200113141001e010452484201080c100c1c401071440c0149039692100705058510b5a0780c0000012010b0042e0080d424000c2100c11190008080129904070900c0070001d240304038026082294521140c1c140004107040c03406103640c1020054244a11412558440d00380310541e0141003542e0958005a603404d149603c1c80402c034942d441103007c0d5101c0400b00681a42d0072500f6081340b80c001d070a82d003040329a440064180a0007980e100007500c804024020101044401020302181e1910200f00b45a034824905484034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 236670791 1250 236669541 236669599
    0x30916080706140d0207030332162a06061208030a0b0d0f031224051e0a0303050d0c0e0d060f020d0c030e0607020c0303030a0b0109050409050606 64
    0xc1c110700c10030840580580741d180000e0014210250609820400c4a000c9070000601500020303103c0100e0301404800514904c0e45855040400030010140010070307800603c042c121100684c0b044e2014001c0307600c20018803032000c000c1254160f03841540010801c0944061400752211441d00000082019421568216255101c0d5905056541d200d00100080075407018182d0840c0d0083c100e070001511505404944138829111311480340300350401c090441d007001100c00341c0000715101c82c1c102d0405c0c0d80b003002c00710b4004840c9881c0464900c100c0e00c036001c80c0f509900380c0281c1078a20210406810030060700707c01c403103540104005030078481c0444210ba001400241c0111094104002048075038004509800f56070b5009494441a4803d510898904c442180000395817040491f180d40802c2c480c443c4c00000c10b200500001c072540c00000d03160b100c09006d224070740381c0c0c0e16201c2c01d03e80d01948400004082c010003c011045072802d115845000481c4d80d60700ca603100391a001c41c015040c88031240c1c16 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 236672041 1250 236670791 236670793
    0x206120603010b2d01030e06130c032a0b0c0703020904050705100203070510050c1c0b0a0611070510140c0a020a030303140a0915022b060617040206120402120d0503091608 75
    0x154503402c240340d41084c83c0510641e1407460580c1c000c0003040108176020184011449040d11014cc007a00004652140e900802c202c00001c00c030b07800d403800340010000c044c0c0e9012219010a91070300d03d0120314100807588203980080e405c825130707001107030084094864140502e0030b40301c1074400ac107508011070b0011200000d8440d42485084140810f0f51554400001c1000000500c400c0705000104030445070340c0414001039520001000c900c009005540040200f03541e0240d0110f96510060720483d1065040400c441c40401d100c12401010803941c0c4038103801501480a207a241c0c100180500500c003003140103103850001060001085118108038250070007d09031408000c0034a0702e010b03600032801c444000c4513000e04103003043c40c3c03501c10340b907484840030380001d403546050030107090b000e1007090201130b04008804000c00b6884a004072900c2d074040c00103220050303071244001840b100324000d20010512502c0100401c0940000c0190b006100701c604880155590b41d0060b1119851070150b10b00d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 236673291 1250 236672041 236672053
    0x60c161502150c03130501050a02030915010506070204020903070e0a05060109060f200c030f1c0504180203061519090f0302060d05090c1009030c090204030206120603010b2d01030e 79
    0x486100d40f409540c1100281030010120082600c445003514000c2e1464481d0350b0b400410700500d10702c1082031555242501c0d10448096241c4000100b9a00074140b020b4003640d00000c4d404495501800302d070010303254006103001141801d600304070003000304580c4107011982c50703030300820110f01528022403404c46a555149108403218014035005e00700b0700545400d445484107403020395034240400d21810040d840240b01600c001658000f01110f03840c4503605025003084280301400811007010008450f00c080942e8a46074540031594441ea071300010440c4610100f28a50010109030780800d411a45589600255031108902d011802061200035032246003088644072103059a00950340c450b102c20140d070001d21103d40415036a82d62485192b000540c000800d0040103400d5000c100941039030340045040500317540c0416918801d000800039500780240c00110213a4013500845a0000c2c054068609802403403174025035000740081807120f070490140050300f5075105e80300e446070311501e03540200303c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 236674541 1250 236673291 236673301
    0x14040e0316020406210c06050c0a24020a170906062b12020f0d1803060207050703150c031a1c0807020907090503160602100b060c16150215 61
    0x11000107038204981150b100c2074006045009001c4841005586040361800b403800742c070b00381078130284e50f0f0003071418041d0900010500c80710000304440c002d580032841e010340740034010020301c2c1803a0741c172485a440360000a51000c099807040812403104000e49c14a00c168540040c180d0310703034504031001c540140366202c07480440c01c0c06c00100c00003202c0310300303903440c1d40d000729100d092502048042c0400981d0141e1320201000108100300c41b00d026561400c1680d034010f48200c1c0d0150030042c03001410300e03034020481005114040c4a004000c41d882059800088420004140170300003580c44100800d240130000f000030f00f10248180ea4090000382042480e20340c0010f41a9000e84409048d07038150001d105460040e00c40000041c001c001685802d41024030341400c0502d001c80490044042014907075003000034640014844080041c8031002043c1000c003640801c085000b102c1c5182c50303500c1502d02c4444402600000c03102910180051003542240029040c0c1c0d540e80b90040e001200c82800c40001c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 236675791 1250 236674541 236674567
    0x30c040b060903070e040219060e10030b0a060906030e06010e010e0405071802030f130c031101031104030c1d1b0711130c0f140f0307020102071203050114040e03 71
    0x600c0c2000c0200000e0801c08110003107460101c054010084810b80b2200f40001c0d031030314010365221080c0c20400c01c91403a08020005040f0101049a5805100d40d0020584068080d0b0400700f101400035041d031201039542e0b03a00602c0d0361020b00c25a0042490100e201f60140008695075041e1b407030540d40c94504c5d03480c02c85040b40c0403071300600684407070003602004a5400c1140002c1a0380712082140980c490511103000348041101810076400c5c90031854207480040d8a01003440708607504540c0b404000032842c401a00a401c80e150011400a4002404800c21640c1280c800a541d240c9041c0512520b48042550080d401510007420b03000090f54900c6944200700e0003020410700c03c50348548040000c0300450410545481540c0b0020307101c102c00006550300000b9200450414074001d21003840c6a0610384040c0310706000740e0503180c4000002071071710b4001d4048421580d40302559410b0310556480040081100703001d4644110a120f5801e02c1c00e2030070703001d1301c0d0700ea08907a4051031030f2144100c800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 236677041 1250 236675791 236675801
    0x1401050f09120604112115100f0e0907060903080417010b091513020910081008240c04270912020c01030b040501030506010506070302011113090b01090302030c04 71
    0x10341c002460b040000104409000060046100342c07119030520b50b49800304982036100c8604800e980e80c0c241030b039003440c000c000b40f909240e50800c5801c40098943c0c03400c2c600102c1305600816103200c1ca60100080d018220b40503d489000b409080d24195622400d0484081d10303c2e2201a003001f00611003403019000b07414a01280d105e5000001503c405904003007500d01c10100c4150920740440720031402b45007040c1070100c1001c480740004610300398240c0d001a40050031038003524200241180060032820120903110050300582080780e1010900b01e810748100b030510081c06c8040d0384940c000c41c41030040032091b80c040d9030300c00c2000b0741090402c002c00000d2068030300305106403680381c80104c0c0101c0ca05a4829142e02c2c800e07406080100c0340070b00094251007910f40800d0240740742c0001000801c0004c1803990669404960311a40c0c0c12140c00d00704e02404920401c20180d041c0060050b541b04006403d15045865500040c080194440b0041d5420151480041d4041c0c100885901c068a80f076401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 236678291 1250 236677041 236677057
    0x3010b150406080a0f1802010e010216092d020901090e10141c030306080111031608041704080a0b0c0705100c02030c010e1506030f0a0213180f0c1401050f 68
    0x50f4000e0320b0400000b900c0c200c0280160391b40a54000c1d4041d964001c0d01d0035070031042800103103d07490604001e040e81c1d070b0952141c0d04032681d440e00c10107444c0e040b070402c0c552000102e80010000d0750701c00700c0050003540200300440c0420360f51000001d200448114103445001d5103003140600c14a0040110304030040c0c0010143d1048481c000b000600700c0720b02500c103113075001c0d0360001f4481b800e0800c09401c4075001106440c640406100300a2245200c1d0507108c9844064079014045440d01e140c0702c0308039032191301d004404600200c0c000c00c10074130020b0941d0f01c03980a02035100486c0c4030800803004622480b18040c249410041518441140f903030041e40c1828494812a8546640800802d0854511000300a4583c02c4000058400381700b0a0089800120880140c01c01440b03c0900030350312418000003d000700000252003010080b0765100c6c0406503420111078848254500d0319a440b8403455030308070f03500504070501140f0240e04c603a087c0200e41c010f869440ca0008620048181170f000305203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 236679541 1250 236678291 236678311
    0xf0105040c1202040f05030c0d030e010807031d070f0909170d0b09010305030d05010b030c07031107051918060b0d050705070609060e0f0304050f01080415060b0a1706060307031a03031803010b15040608 88
    0x16640c1d604440343c1c40710d02c058030a0b203010b0b0084500b42031301c06034811803d40c010004642400418004540107502920030384001800c120790b140f1139409404060100030969a620188a03c0000203020003c0003c007002803c02c8010401a80c848110103040c0c0070542d8141a421820300090b000207010340141d40e24000102d0032182c0d299a00d00000780507480703114107a05c106001c00b00401c031001910400200704429400d00f40035250900007040b105000d00c810303a4403190303240d20115a406000d48119113650303401c517005105101c07203070400c1c0c00501071080200d40d9038840c2d4688401c43c2e103008819601540d000034404400345031150011580070310301400540f460f03204902c3c1c2001c0460548031f42001480001c8006441c1c5241002c042c8c4204154900d100c10004980100941551520200c0754012010b040000d411050300c84a4402010140d400540502c00020500249640001c80c2030301428110002d0250210350420f1000c0c2616100384030000d1101440103100340750180c103140c4e50100d0842 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 236680791 1250 236679541 236679551
    0xe030a0f021204171f1a0312191e08040b0a14060d1103010204060c02030d11030a08040303090204050903090a12120c1a01060507060e03030f0105040c1202040f05030c0d030e01080703 80
    0x1544117000e20608038070480041c1d82e2441500c030003160245120802400c120003030155070b0314203103141c0c005100d5541d003405030203502610300c00d005c1d02030313148100740d480907402801c0c07944540000a01500d4054405540c051541e000241d10741400b4003400c12007002414484825807980d0052140c1000010b8003281d0232030f07440c1c0080445803030902c054001480346070350340300400e60107005050419100d0451101008034004a02030307010400000c689025030b0714070b8a40c2c0139540e02d081c100c0c01400c1d00e22009502c9400c010074000421030000c0134103040101183d112900300c0d40c5548000c2a0403c16200800b074000c40084a40320741c3c010070b003907160f080c02000c0010103006c120440c4400181c2c00d0b009030003c05d401143d944240100d502c41e4030803800480e0002d5185062161001c0781c0d1410500c99644126103c0046800492055548110032800c05505545076030b206c2c001d400c00680d8900070305c0e0003840f8071400302485280041900d41c980360180c6a040850398007200450b440d19006010a0625844e2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 236682041 1250 236680791 236680813
    0x100308030702071d0114100207060c080904050f0a0605040903020a081305060a082508041214040603020702130c051602150c0a0317071b05100e030a0f02120417 70
    0x50780801c2028400101289500e43c11b2803050780f08099002c03400d50142c0c00700075807074088640018000c0152642c40c01c0081c19001a0301e003000300340c0b103210001500142400305005c014160075149500446c266101444850b444201b4481210401e00005c2c0050384003c400b075010801c4240103118a5030305000c101c50094460011801e01e910040b0070b0b4001030501c50030001d20030380c240300e205025203105c030703c40301041c01c0e403200200b0341d083c0944050252204050480710203070007040200800d200015400e41c84950305c15016000390440c2c0416030282d0002d4a048449004c148940c2e840b0b450715072036039400e000c000b0181005802640d10101c3c6c010740700780640c91000c1c042c0310280030303276403030210043c03844140d185001812280080d18002101c200a01403205d0036400031404203500000d42250b6403000504c2c2045880c1000c4c00148002107480e0241d401040400840146001c42c21501c40c1d280c50203460741e040b43c0c0c402700d410300104480e80c00c2c442441045007802c40401c141c9156401c80d42e2503000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 236683291 1250 236682041 236682059
    0xc0c0d02030c010c05040311010305150901060e0312030f0f070e0402030f07170606030a09150e0304171504030c05100c09051c05060403050c1903090303110610030803070207 76
    0x188a250025a00104004090304024054800150b90030b14209040c1491a954100c2d00081001042d041c182c82d0000288203161812001d0f10081000b02802c0313455079034210103030954184490450103030196038503041c4943d88007001c80b40a900b42102d01002641e52103442008180c01030140820403075007182948169580d4006140106151140040c250400345006448902942d00c03041c95103000b0801c00013103698140940764061055480461320010f646481c28a9117403901d68202154688807908080c0500000900255076a0a500b5418001e100350b113207a5070110450120781d1540c84400080000348100400f03220700c0d20130002ca800190340501d41c10192003207004c3c08d000180004c13504000b10b20f0210907001c029900c2201310441d91100b0746a16484420080010341441400225110490020042d0326540d514018500d14035845510700201840704622060700000d03041c051546010601240540c015510864001300151450b59903800b903070401401c0782c044d80503a60380080c070040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 236684541 1250 236683291 236683303
    0x13061403180709060f050f1c110a05060f0901030b0d050a111201020309010902210622050304030303020d050106090b091002120a051201090501062c061b01061a120c0c 73
    0x360082005c280c241040c050040c0d203010028018421200514002c03000b034109540303035842c0c0d5001440d00020100c5031011500000065100c160890360014803442c10321188005010050341c240c1e420322440e8004c00030014802900907014180c2d0308860302900019140303035401048034001a0003c404880100000ca0883e00122460b204503512020034400314903200c0c6034540c400e510003412a408800c40b8907210390780c0d480140103c5505019113486615094140c80914400e43e02008890340d03552a49002000380d080450340c0307801d403408d200002c5000350040324000140c0710341c00746460810016104000118007101d02d464294000d018103288110782d00002070100354801c1c1c44041e907440c99102c408004182c168003411810345030100602069900c008404501d1005000c003a00058143c10f029409955541400e544084006480c800060806003210900c1c0310240c001c0120035507415a002500030032005503940c0e03102c02c1181c0746541c01d098030890742040c15002c0340350906d040069203902c1e043c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 236685791 1250 236684541 236684549
    0x3060a1a100c02090a061a07020d0c0602070303080f0402060d0f060911040501080117030a050706060b041818021f11030c01200a0906050f09151306140318070906 71
    0x26109002c92000e500b0031142458001580c4181003144515041c41460205510000540c1e42c03240091490705565a00d03410a0302c99801418000c4040c1d82d070000a5a69051391200b1004254000c0c0020441038100200e5032081c0d401900480c600416504540300030b15841307a000e441c240d514040428142c2c001d1040b003406005d0743c12000d03982d0381008005804041d05a0281c110000024804007100201100b500c80482641c10301a07212802480c03c00c028201c140c00200c3c6040000c03070009900084000030841c90140d03101d00b000110301844441c1070f624840c40000e500b102c0c47c00720b002d540c0c0d410060511142c1d000c0b4034128503107040b040e1a05095030300010740d10380140c3d12100b030b0f681a81c44010100745081460000a0301c0c003010644043c01122083c4201010b002d004560f014400c0d04d80c40848080810003001000c08000701403c82c00c2d141c020341e004000c03410242a01180c01c6012f2011320b200c4403015140719007180c2d00c04581071281152903c40045034003e2410000c0c2c00c0d1001e01801010f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 236687041 1250 236685791 236685797
    0x1b0a0e040e0f010e100209030a170705010f1a100e060d0908180a151b0c050306090a03090b0f030a0e030c03131d0c0d0c050412080c070608040203060a1a10 68
    0xc01342d00b42d2154500f01d0219252810940304120411341030343c0c00a0007034145984411345c900b440703d044058801da0700500342c0c043c10302e500740710000c3c0d07d904855000340c0b041d1807015907180585803060184498000c0c200020703c0030984903010f02e4000e01c0c1500180c40c84a503034980110380e4a4241d600d0942a81241b0483d80c1011240202c044084c5484074a10024101e2104442d482c1400701200a012884070700695111145821000003408007050340c0501400740541102c60a080803032005546205107070080d00010400c01000c0b4941510b803007101c0e0607501c00e001050641c0ca42e0660500104940f80307407084603101c01c0120049052050014000c0410540400408641b41039000544100c1840b0f0720741d0714a60000c01c0140c0840110142c4017614044e4800240b142902d004c282c0f92882103030462042d04c1400d5403407008000315800140310040e85801510400e65441c1c005480d540001d0b90000d42c5030304110000782212000ba440040c0c2c1d001114001030790000718201050b08694401c0e280000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 236688291 1250 236687041 236687051
    0x12070f02040506030102190813140c0108160c060f0204031205070c06030902150306150c240603030a08190212011401140315030a05060c03010e1b0a0e040e0f01 70
    0x941c601407003400c1d4440750039802580b50419804e80365030036100c0b140c519014000d82c1008200380c2c0c0c0540c070340002100e5004007101200e104038125582d0b00c05803404145d001074814000605184050040801345001c40d451f0915045116681c0c040901201041004a02d50174000003010800c0540010948460383c2c40c1c00f40d50700740700d01f000c11000302d4903000390b02070506040b007d900584410040070138403152000003c0d201d17250000018921214031109070f00301c4101044000001c107020a10710040c80340c1460070940465044000d004080d01200e51544c142c00034412580e038107002d01000ca0388002c00140750740c00d014455100c60100e0f082012201090741d0141c00502c04880e000e12070241d081c109080841c0b4812055051031200c2c0b0000f0424003103846202c01d440000c0d10100b003414a500c5e4464141c1d03005181c08007100310103030001d10400500c0d42c0c0c06d4020407a19150723010340d42001003413502c00a24040703400c6c50582d00080d0115821750030966138484206280000c1c4403440d2007021140010032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 236689541 1250 236688291 236688293
    0xe010c170912010204051e04020909011e06020c0306130c080601080c040e0303040c15090503150919030203040e0c0903011404060c0e0a090e010b0a03050f12072312070f 74
    0x900440111a1008280c4c410001130007190354200d1994401501e11800204410514000c240a80510035015800402000020071030f1389103000f807110034000207184030403401d0307176044201c6e910015040003d8154003c00302058000c448994002012400390f064240199920822523240c800260301c4604650081c401c140ca142c0340c1070044245117071004004506500301600c4200f0540350a115043c401a44260b07007480b800c1c0039548040c02098001c06542105607600321882e00c000b411900c02c40c1c0c2d13014000f0a449900d8400308138400d015016801503051505090b4003c3c0301140240044401075400d00252440c1d9400340606003080c064407107504200e0a0a14000c0180d560446440013404012202000151a03d1811a045500d002e902281c400c0c5402805070060603081d2001d030f0441c3d040c1c00d0200078400001a41c080d0301e08928200e40c00e0704004007195115008000d4010a036001c1035001481050b5910200d1032030484060a903501c800102003010225805500101c40349410852004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 236690647 1106 236689541 236689549
    0x31b0103110a0302130501021f0902041107051f0b0102030d1e020c06040b010b12041101090807140415060e010c0602040302130e0c0109080d0e010c1709 67
    0x1968070201d82c04020041e61054281000034001490002002d52000982041400080680b048000b002c6805100503203080382c01a60310a8a8075869507090406d00001c0c10070342e109400800a480c400c2002a01c07000a0b4100518818030313100c40810142d801008541510110510029441400052000c054101003000070560b51010a50b003010b181c000401902413409104101e80301c1e03036150740d001d069104050892003500e11002c045800282e4159100c50790b00414100000650f8541c00d0207480d000441c0e210850a062910011015007060320444000d620000b00b003481741410710002a000c0c0c14910f070864104101e22152409200b515410b40300075540c01007510085031031001080d40076049050030281e86020f561004209980140400740480720711101501e01240000d030184c40400880316810306200c011515200002d4600e0703640e50300d201d6815520754403611580c1c144 = true := by decide +kernel

theorem cover : BRFrame.Cov 236510791 236690647 := by
  have h0 := BRFrame.cov_init 236510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 236510791 ≤ n) (h2 : n < 236690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
