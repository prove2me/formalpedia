-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0424
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:44:37.000022+00:00
-- url     : https://prove2.me/submissions/3a3945e7-620a-4780-875b-7e2ae783407c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 76079138 ≤ n < 76258994 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 76080388 1250 76079138 76079153
    0x1d0706181404051504050c040e160206010303051606020409050a1409030301151b03020f1203090c0d06020c060708010612020c0303060907050417070e0c0913021b061f080712 76
    0xa0122082c00c1389040c07180c0700300c0080c040703604c140c5030001a560041018814940c28115258001400c03c0340d240e05203131808402581d070351b8140402010000045402500d0390402c28102d40c0303a5038410419925071f83c5425480000340000c5646d454800d040c0170200d03403192100700886000703141180c069451a0f0070140718600101181115108100224200408600d841d90741c084245100f9406441c5084130107440c0740c50141180410400e0f040108140301c0303140000034040d0783c6e00c3c800362840d046201380c40c1000c10090185448400e40c0c0e004041c20045110781c404081c505903910b540ba0040d8123104401c1c170a04078001c04000310505c3c0c1c030402c0810014a00000d005500031060325015180607181d1541c5e0654040442041005510a00c1c01b0301080b2810020160312203100401c4a04141040002a0301c580200c9403480a19500065040b980800b05000611040800e4121142030038000c40700030b5401c203000b0890502074501d0328041604640031a6507070403074054044c020390000703450700c0700030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 76081638 1250 76080388 76080391
    0x1c05150a150917010e120a0e04050403050c0a030801090509070302130506040908070303051b03070206040b0405210405040f0204061202090a0f060e0f1203040b0d1d070618140405 78
    0x90003020200002c0c018120380c0a151031203e01800400d03103e40e031200c982d2078101d50460800c1142e4083c400540c2d043d60104580e0310b00c5e03500703d0300441c0036102c85c102038481d40300f1007200205a024940c0440e0074950410415812a0240101003040b50b80e105200c944400c1c143c000298004d00c0310b011002c1c840807541102c4d0b00300300c00410001ba00c5600b030340c41e04c82c584e01484044011984030810811210b9440008500000032009040e02d1450f00b03d2000b500e82e040140024009103444001ca02070000c03c1015003019400b044060b81400c880c10145072043c0c00c00d2048901c204d05044a82d4051b1515000f43d4003221001c0d00c0d615061000081c03a10302a42200711400e4204000303040020310072480c816143c00408403a03c1d901000340c1010b09100c3e481c009641901d00402006405ca000304100204550444c2c01c079003081c0351200d40412a020243c02c40501c0c0031901910000c449139030b102c0110f05003040380c3c01070310b582400c0c41d043c82e8450042d02c45449101c911101e120b240350351504140c0c1105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 76082888 1250 76081638 76081679
    0x50f0f09071d091e160905040825020303030106030914030c03030609070e130b0108060312040504020c010219020d09061e0c020315010f0503010605040921141c05150a 73
    0x140c9100240d0045820107800c4002c1c54440d17170340b01c01d081c0c4d4884900419101c0c068640410180990310381a294170b10240329180c500004c1d0b1800403c20030f6005118419001003543c0101035966a59480300b00401030282e0b5401903444854080d91031105010020480d400c03841090050f41c19a5940400c0011142000380348030705000020308845016a6281110746810300c00807070019400302480001081c4000c02428030b8040d510209150682c84010800d8a00300e400855000d40c0c1e078240c0194460190186000043c851551015012005a00441d03840440301d940c0c1c0d2540c1103a0780d03e90085680c010410302c5031040c0352500d44801c0315540b08095a80d1418000340c200c1e0050341050081050900d026880107c3e80b180002c82031146180a010b841e0060004580a0000640036100c004032a240040a8505204611040c600d00c900404100044c0301001c014a501c2c3c2d150030465581c0c18460810049100b407a000028483e0300d0440340d45801244041c0c11903c0844c1407101030314610400d243c64 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 76084138 1250 76082888 76082893
    0x50604031407050703050d0806120705040209310b091302060304030903120809070b0903060126060f070315080c13020904110705070603020f0f0a0909050f0f09071d09 73
    0x40e0382c045802008041c00951145000301072661107250000e249600103403030a8441e4482c0c3c00641754100b80001d00038141e23441201d0040e070f101a0140002c0301c0b038a416181240030104502c0e4030403107003008a003c00a511400005100c0202e0715010040c0c2c2c0c43c821540103420890607128030b405403d000020f035034010701c241445400d02e5101c0d15000c0e80c5012208440e80000d1185040004925062015800410402c2c0d491824200042c2c006900d50300140907142c42e1440c00030811002441259101c40540b15840070b844c600e040c80c0103c0241803c0c22100240428208240e0034030700440003007001e0849523284060b03c0c2441e030304d10800503001e425100c18680181c090010791441d070368a10400d002d000c100144280e03a01c0f110714000d81403c0280d40000140b52041c48404180b04540003106c0b06840507d0080d1360b1280c00c484140c913103102e543c20501c90340b4a0101004462004910403d0282d03501c0e01403c602555203d5000e40e50380e01901849124036101c0c0c11140640101c8840d954015910409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 76085388 1250 76084138 76084147
    0xe2802090616060c02070605030c0a030504060f021215060301050f010f030b190503060a0b0901060c03030608070e0916140d02010e100207180504032001090c0b0c070506070506040314 80
    0x350050031042107401640c2c01941c03440c4c1e400f83c0380d4041041000a00403418210b04624200303040354003502400c0350f5003040c540c80f20001410000f20741d0020140d492071110440d255101d03045c1260001404994503040b60780a460200c4d010718061042c0c0c0c0c120340d40103041400986a000045411440d00c0003034074140b51b124564803003541d0f512a814050250b07131801004440c4d24200c00c06107030000c0504850348040c58144902920784500304007506503040303424101d05a0300b103031504400810403a031140d0540d01030b89001181049200721802d000c0c0ca0400b084550340c0414141c004030381c40d95881480744c49000065040050f003440000500c2d00750050600301003640007040410030b000e1080c04a0b1006800245c4288811002c2c00008c0d0302c04010b40c4801c0085240c5550302074410905900080b00906850794501c1c05a0000d410000c00c007680b10f0a03107c1d5075a9038240f0704045401c040359555260060382400720742c40c1000c00694810760303003200040c41e05485548081c0e03a482040d41500c03580a10800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 76086638 1250 76085388 76085407
    0x3070c03031416140415050c030705070e060a0e09070303180e0109050f010611150a0b0d05010608070801200a0309170c0606060c0d031a1008010e28020906 68
    0x12100c2c3c1c8181d60244000300e111020b508002c00c90000c07800c03005078503003092109000c400c12102c02c100540b5841d0906540d10103c0101c120324502850390010464414250702040507021105030500441060708c80641d072580762003540400785011039950185601080c2d00300040781c42140148030350002a02c141d82503607151883d10300c6403402608036622040c3c5410600c01701200d0f51601c1e0f401000300703240c001c2401d02c08510154480c01d000ca000741e070b0340c3c4c0b150010a110710642c0d070041c807082c00e008040346040341107451f045018185610540710b550152040009200c001806000000005404105034001c80101e01c00c02e1900410b01030410503542d03c12400c00200340c3d800b1860300348203007034040b03807904001c080c03140c5845001000c49005400a000746100e81030009048140c51129050125071403421611200c81c400342d00354069170203511003030720000d1a600481610f05903450003802c20b029944c0c00c0340c102c0b180030f40303080000c0448040d00b40440d07480c4000e60203804071b0700d4000c112520303009142d0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 76087888 1250 76086638 76086671
    0x305160206160f11041811040f1b0206070e06092812060c03090201050a05090d021f1101020405010504060813060207120206070201051012020a0306060b0405010912050303070c0303 79
    0xc29045464440140641c3c0c02c2c0129907510b2a0350f0b4608131411300c0062400601480804a1071500810820b0b04442085140c0c2c1d594021280e41039030f0010400c2400c00f0300300301e4404044948031031805401600c0c00304075410300c035040a20380c041c0c001e401c65160507441c200b0712000c81d12821540902c451584241c101106500c1032800040c01001d62403600c0420f14100301044903108104030b8140362501480b440180d803c17905841024a150070602d840c0d09101001c1103e444d18010029071000440c111210b40c4070002015002104039a51500559031650111900700e12507400b800c1d010a00030302041103101d218118480c0d02080300005950100302c00e5865400340e80142d00b04442980d10036071b40c0148076070b04004441c5d2003039261000740a40e05080c0100c1101810310b000d18526180c2e003009642c00c0d511184010401190700c45020840349903607145c005800e40260145c0d9000860032500001e00910004860b40c00c550131401079840c40e02c4685060300ca0345004c0100701c081c0f580710001d41c03080c3da101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 76089138 1250 76087888 76087927
    0x1030e060112020a06020c010c0b0a09020d03050a03060e04050307021203040905010f031101050703080a05060411120a06151413050418060b0a080709090206070f0c03050c06070305160206 82
    0x10091070807900b003410b10401910f12420b4103c5000c543c802c101c1c40c11240e0b8000740c842c80c0140c01000c2040da41d1918095400603180c0c610000e5000210341c4466010154004000d100903905907400308126034070b5040030642c4000a40b0058019441442802c01616250f035044c0a155501000ca0f46403a6940d2803504c1941c4c0241e10107004503850709001c10034082c070a1000350100178246001407034802d060f40c2c0a80072110207801c446980b507490b80007407003c0d1200d0b0301458555840d010102e0700c5058000c161900810308603100900f6030304004002aa5941e02d01d49854a586c41c1d80326014195000b545408444e0840011510489101600069981c88070300c1060603e080018041c0609141c07810200241c40140004a00505400707400f084072001c0865000c090b85e2602e607000c0f0b0a503100303000045850040c004083c00c6100250b4031a0b04000200030003030100d9100350169070320082000e00b040064001d102c000344c0422402c1158100c108104500041d8451000741120308060102c0c07044800c1550 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 76090388 1250 76089138 76089149
    0x615040e13020112020c10092a1503060303050712031401030f06050702160515070206030f0a0509030f040323010c0201061802040b0403030c1401330608070e01030e0601 74
    0x1d4540c0400c0d07580c444200035000740c021205600d0102d0301103c00d95140c00d82001c1d220748075aa0300c5240100140c1d4140444800d44e0b02806821b010b560f0b4009940107105881241006155520010842c1b406802840c0403650541c44440c20110151940e1032894003090900d410990740b2030070b078100c0000300e5030302c64040c602510350200b090b003442c070f40041104d4000e0f140300c0540d408a9a4502d80c0a030715600c110555005a0300e030034016071890000c0c0c46c1c0b80500d10b4003d50084011041150000100034603a202d4020f80800703000d507403035450000b9240e01c25080342c2d4003001c0c000c110a03c08103120403068181300b81110401510f41c140111540c0c212104c00d0390b030100603510740e881080246110184401410070084046142618001c05401c0d0342c8a50700c4005d003070051152070302052003a05080a82401714400081c80303103281035994019404c1c46110500c1d10f24001d5140c0049500400d081c0c40d0aa441c84e84541c54503840751305059401040340c0510904154685c007500070510402e02043d8020032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 76091638 1250 76090388 76090411
    0xf0209040b040b0702011103060d050705040f0b010206070c03050f0309030c060702160f0b0307111e010506100e0315060d06020705010605030d021209090a0906050f060a0503150615040e 81
    0x40c14a4040d03c16040500790008581c102844a050b1010120440f41c0029044410b00114801454000d05000c03d55014941c018a065070000019001d0b805c401b4090341c00361700392803190f9030300c1806641442004502a00180d818801c8210900340e4800035078002e26030300112810310000e0101c540c5000401c403000ea00503000000d03950544280040d0050140420307090b103000190425849111034003000b02003034104841f100002010100520071541027000a80c2021404100c0c20034980c041c00e41a0b5140c0e020300300c2c140e0000c100610900231300380204001800750020f110214080242c460015103070f02c1d03000c141002007000003100ca00c0140006485940040740301ea10b800100360038220794200c0707071044d0741102c01d40d114a006020101c0d0100b16044500702110f4441d1030403107004000f80c1c04000d108600c1c1c04284543e00c1094070b14544103202c216000c80182d511181496140c941c40301c80551810600c50202e807151807c4401c1d100140b01c040e500608141c4e40710882c2c1d0141d4000d554044400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 76092888 1250 76091638 76091641
    0xc030209010b0909130c080313080c01032c0304090204170c061c05090c0409080d1113060305060609060a110115120201050901110d0207050406051c020d0f0209040b 72
    0x182450a003003030040406080042c201a100e501041e03002c00018424501c0b000b900d00342c0030400c6485140381000d800000b044070744075508011848004411400f84c0d6846110361481449190f20a00481c0e001c0700100b41d404401c6010404030490006013000d10b00000e00081c48081901c8116101030801428a16052411510040c14003420103a0911000313019990030002c56101400c0e420060304100f60320f10303001809a44611219083c1102c0c82c43c16903001d070401b003054051090740c0014289003003c2082c00c0010281166044646100300309011042c5061101e0030803405000e607110b5588240d0103880e043c50008100006800c5e40d1010281078086450550300c00c02c00e440920410b0000104829510380030f0f81400070341c1a00d200103a00003410010009191021399100f503c00b103000d403400740c0454901c2c03103c411001e5158030050080a002d14a081c00000345072074419220b440003c0300c82c01c0c29a6000054007070080d80c01d40c03003170705940e480c180000c003c00580304d00300118412801003a039810725 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 76094138 1250 76092888 76092893
    0x912040b1b010c17090a110d0309031a010303030c111c050c0102041d0a06030f020f01020102090a03050c0f0316120c270615210b0d05060103052401120614040c03 71
    0x40074400340c0248021b40c00340e008140002c03000b903400304c0104400c035080901d0750300510303040741c1e0f942080d00010201c1258402a180e5000e81030704250580b44640c4060241c010b070320900f110002225100700500360311003501d01110a85940e0481a210503d01d0120703d01400e21910342d0980e4400e40c80903541c40c9402580d10000300d2a81c41d02da1b0400c800b040188800c5240d911425558104030102a2141207045840d190681c000d5048803460000680b101e4191580ca080c06901c4045880d2901d00480d00254400a1403a000c01c0c2d0034003640307028049480c0c00d414906680c1c0104480b02040784d0030490740c0c0011400140000c040781c4842c2c4650442c580108036049044159600c591090f210650312464410706580c2007007c0c280380462070b0340c14103000220050f802001d0200d40548a0b08a0081d190840500c100480ea860503a4010f5080310707000481c44100c0004103030240d0210b0740c038880e000014030654800741e00095000d401282c001c00c140c03c420001000d6150306039021954000c410310304108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 76095388 1250 76094138 76094177
    0x806061b1f0b0607150203060a03020d0f0302060a020a0903170f04030b09070609080d030f0f020403080903060609040b010314010f06060206160f02030405040203130c0602150912040b1b010c 83
    0x2ca080a0f11180d051080d2643d520b03d0300346440c0c241805194020000405640794510490000c640040061640010704c0c20803140c102081e050a80040c0101000034000341218000c40d42940815a00c1010701861916419a00e2409801c01200c2d6a0100840301c41d40f1100300242000c0c50207008141c02c4c60030441c460624006060381302074180005104100034021011a00d040680c41a081c0401c9540740051042c000b05515140c188400f07201160202c1801052000b4014500050f0308035210b079112241007094894040344d00030400d00c40000144005410111000c014207001000402c034101d07007541c0c04051314001e40018006038022020006150542800707140c100308a420480380f0f100f51100700031b440c0d1196010315806141c00102007181e2040c0c1001c2c2480c0f094110b0000e001c6a6228000252140742c16031021002d5000034000c211400008101c400c21030904241540ca41032034884004a42e03048082440b00e0300c2c1d401d415050340c11200f8040c003075810202e0350301c450100c20200f03c01003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 76096638 1250 76095388 76095401
    0x3030f010e040b01031202120c010614040b0901030f061425030903020316020604080601030b04030801090614010309020f09010e06031e070308090d0c060504051201020304030806061b1f 81
    0xc0601d0004180004115201031a50540350860052080705413003010503441c003c80c0c00e42113518254001104401004103520000076100c2c3d441d1840e08440102e020002501d003881040c5601072600001000015103044c40c00850314031580002c40c0100d0f9180d00c050354a2070464042010402d400f9046481c40e00c602c0c8188260001400e0404c001300300d40d24000e40d01d008481d000718501500c4050300095595883c159130082c0440412202d00d0b603181d1801d2800510262070441c0820390a07000491072407100d00941c0284e412004038801e64001000044015251036002070782c0040c00c0c0003000e03481e611084000b034064411020302c0e404a0421800f450324021256900394418201c510030500c03a00000308424040360307003092505440c1c04c1c460000a50a0360300700f00042201d04030180000304240c000001d40f0407140201e41c001c031203140000b4854242e110484000b00000d0100000491500d05074001d80646515010003000d40c0315000d80b0117288c0300740070001ca80218032054030318801c4181800f610707 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 76097888 1250 76096638 76096649
    0xd02160602030c13121208151e0901060507171305060706050402030f070515070614090601060906090503060a0509160801090c091b2102030705130b090d3203030f01 72
    0x5c0e10000701c0791104200e0341820400003040001140c00f00b980a210781c040b0b03000c103013402010b0300300c90f80101c0940420078090507040c80c0581480c1740001a5540113031b00b51500141c00607600d084c11244001c1004040d8031919082e842c0c010b14940114150b11100e0140800d00e12641000401d41058010149401c11640e5240c1d070944c81810280715503181d010350020102e4660340403e440e4001b82ca0000e0180c160448021a031499110400280c10710004c6c10134101d4009854403e00c80d0f07182c503801c6071030070704c070f402500d4155101d4400f141228000346c1c041da61192000060300d60480d02602c80507020100c17944801e0f96a91540c01c0d4a00b070045509000004004c0c0ca60200654800400d070b1442c00c075040800c440901c0980700d0000a103822070314401060750b00705d4004560341d03c1e01c4240640a03401c03102443d20007100c1e091000c05e0b0015400300b10346031803070010500c18407560580c0c3e4548031540001d0f02480d080c0da0b80c0f0701e24a2414040c28803500d00d9650740c006142c032460190f810250051050f40304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 76099138 1250 76097888 76097909
    0x506040b01140f04050c090303070b0106110d05090f130501060309142e090605010605040e100e16180f031b050607030f0c0b01091506030905030d02160602030c13 71
    0x50380d450f50b039000d81040a0b54000e54003c90b0300d5a4242ca41c01da180514907040f034140c04001440c40c104030b0b00022550599603e40c0340c05260021640d800e650356410b040d103000c04281d0410410941e440c0c00301d1206000603000700314102440c4048001416a40c0c00e0303001002181e141c03001d08042110a03001a841146024000c1c00309000f40c0140d00c140d132484040d00418600956400441d0800c2c5422040b415604640140210350303684000030150390151086645040740b080c00b00c0c42d000b030103003030000486080080481807502cad454462402864005105014000071880d180041124604190014400700c08a480c406103181020301301071603050804020000390110501550b03540c402505c01403501440c04a0311500000016114113901c030798007928500481c0000a8800401c0d0001503086051b81d0030010040e41d174100c00e50030303284010402412504240000d000f07119a82d8060500940c4503447e04038071a14503140c4a00f242d009590861040200050f8a00c4158071314107004002c065010a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 76100388 1250 76099138 76099169
    0x20a0e06070b0601030c050706020703090312030e070e06010504170304030323040308071e060b041d03120a1103040c030204051303051206150c010501050f01090510030f15030506040b01 81
    0x95440721402d00528003818140d480c4901000580f00c3d5040d03802c2658840c0c0c0840d80c9142500780981069014401100d600c43c2a41496060700c2c030034040d80403060010300051a90310708104141c01b801d1001010541040024800014040e00714864007101204e01e10146913102e013141001403007280c001c10400b19003803201c004580c01020120803682180d4000e0000340c2c54000a113069094101000551146103110351044410f001c80c5038031508039214200c4041115203110710483d0f83d070b5003d8604c4180d10350028003074041d04c0c034030640c42168080402c4600003a02441e010a403150303a00255410303100c0810069092007141001c4c8142a000800f00c0b900300140206a94018481d1040d02c0d400704107144a100865250780ba0281514207000d1020304264446c0801401c11b07000303110910989102d9100f00702d00c803c60394020440e07041582d00142100310398035542003081d0041c01c040019000d4555482c40315000710380c1c1d1590954061480b60f009003205c0d00b45400d01c0390305000d0681100f0408100c48c40c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 76101638 1250 76100388 76100393
    0xd1a060a1d03030f0304061d0601050f0d0c050901030311010c1403060d060b090a020c01140606091c1a090c0103060501020d030f06030c080a02010f0e06071e15020a0e0607 75
    0x111032802140d07140001e4410509800d0200e4218040d0290104504402005000c01c000f0542c025504020298041e5124205401071040e510f03d000e11803150803103a410154139440c1082c0d00385d182103030b004074150100c0b682d440c1d004c80c02e122000d90060340000d9900504883c0c0714000e008500ca0040d191400061503150000b02185900c000f521441c46070000684c6901000326580040c04980d00080c0301c40210f15001c0359000113544680300c1007c1651801c0c0213100401c1a1210042c0115400b510300342c1460f030700c4801d011340744140c1d4101240c807200c1d24110400003038018014022400c5400d8003a0758608040c40828588202c0f003003040c3c14035080407011712060b45e0000d2400350a2540e483c001c2551b41c00050450b000f031103160030190100040d10070200c1d242500055050b1418800c0e40c41004550070014212a0f0028000744c15905c00010468800401c5c5a0541c0e0307820368000312100d89140c94180d40c0c0c2501c40480c078815105d0942c020800310285504110451304414058510525040165 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 76102888 1250 76101638 76101647
    0x503060c0702030f01050c0405120105010e0105010804080f0406030b090901050708042918060708011406090f09070c11180f0a20090306061f080901110d1a060a 70
    0x40003005140c001140a1055650810003d15444100341c0200154105a92558140d82c001d0240a01909007920b542510444c1485994100c90395500c4503119a4205001140c4080c4e0142040c1c40e2103c043c805020303102d01100041004003050b807400106000070805001d426200144410f04592406080202990304040403030703449580315201c010902c0c0c411b0320240241c502d04c49c000a001d0207440401107100101e14514425882120454515540b040e40c00c03207491809014041011a03180380c100034074140380010702071007000140006000b0541501080e0036610440e03c420004482d40c140805221401d903a4510000c419203c000395034076110b643d0203540d4405440032a00d01110b0001441800e800d9009500e425404266001c240b000c0b000b44d54000c4d08040b130701c2341c03007070140c940856040d10b000100001d00c0c42c03182518100700901c6800c00d4410f0000244000e40c1e035501d80365034070b082414450040608085a00380091303c02044000c4035078400384501e0145c0241d5040000c407001030b401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 76104138 1250 76102888 76102891
    0x1302030c0a0f091a0c0114060607111f0816031b080a0b09010b0403170a140d060b030a0f060b090603130f0f030314070905062a0f060f07020304050306 66
    0x50341055268003115800031100307000d1640c840201c0c4c108a03448041503138540d80090501c480c0b844024050480c2003809401201015100319a000c1010482000040ca00800c004624078004204405140459804480744544680518005850307902041551090183c070384031454040d01d41040121000100441200024a646002e0200c203c001a00c0c0c021103400804100c600613101d0446543c0d600708413080c1c0d800500080700c0c5030494100303c40c13002504a0507141d460050b0780d2001e54494030038040318020b6200d842050a15525800041040a03443c402140a15500080020a0002c1e0710100e401c0740d510740c000e03d2040500700007105c460b98800d810f42ea0001c1584104054600d05880d240540c1032a4100040890044414182c01e2541640c440d000030381581d0103078100361392100c408645e24101c50042d5680322100340019600180e1a61186007454411529811540e02c82000541ba100e4051400d010310f61059040212003140244074581000003400114246404c01e00042e0b2030b000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 76105388 1250 76104138 76104157
    0x7030617010c02190c03050709090c120206040603091110050901020d02060c04031209030501050f0f01060503060a03080a05040f030f03090f08030906070819021606090324090219051302030c 83
    0xc814050001e104c04541751000550b031000c00c9034105603690703240001400c100d0368152400c1206d40c0c00005c1a0b801d0000c19044158010143d9241900f8442c094004000042c4150f0301d20040c0c00c082403007a100d030811384540c5151501d4082d05e41c050407000910344030000700c01508540000d400e21121912140942c0c0030340c1c0c1e001c0e0f2904403815400e01c0441b800f05031380d07102510741d40c20f04c2d046c0b0040480d079600c810302030900905060354580e280d640584070341c80281c0c0d40d141c000800400401c042407c00c4050038407021139240042c60f084e0344070041e2038146503a410907101c0381080400c5108243c0c000352800c0c010580300c452140324070325260310b041d01d0b0f01981c1c1d4460b00a280019209007000034140841e20392200e1805a10346034200c899009640740120303417295100241000e40803610a004501d40d100712544180400c840300140414380030380c034041e1403e85403007039140c56050005950b001e0803000003016501d0b010101030301e030504101c10160380365286043c5c98810024000d403d00d5041c03c03a001c014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 76106638 1250 76105388 76105423
    0x304060f05070c0b072d020102090303040b0405100f080402040903020c0d081b060112060e01021308010b04060837020d080d11040614070f0804060e04150f15020f030307030617010c02 80
    0x60010f421f9000e4440d503e50113a150000207008505001a500540700b81c407030a44902e080e6400801e000e0310f41c080030034210000b24081800140061420f40c0090b50f0003840b030302c1524941311001020030755400002d10f0032112008042a5650344d401104500340001990030300901c01545801098403031200c020f0000303803507a500c8031060484201c007501280c0382210400030b08070015503120000342c020030700b80c00d40600c40c50614000003040900042d550000c09030352025200c11081c908116007041c1c0d82c1032212052100b175040d1070310160342c44003103050000d40a9507040d82d5415000c0104011140200170b400c4171860180014000c1a505c00c1d04446004001c03000155140c040c0e04290000503076030303c001445602d00040c007144082e440140060080304c1030783c040c082f454189204000078074040c000d0030404440528104440304030b1510b0814090386a0059580718040b5a84181c00d6a1003121200040f0f03031100410496070708044510703250010030000801182d0480312000b512000846581074098 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 76107888 1250 76106638 76106717
    0x31b010b061c060b0414090a0b01120c0903080c030703020708030f040303030b1c061a01050906030601140d050a090201080106030510090c050c0f1b09090607050304060f05070c0b07 79
    0x1d82c401d510060140c01103042c02510741d44d5440c01580001a1410680d004141c2d203800709055203514018009100300c147c4030142142040b580300c5000b44818282c003400c120300000000b0208041030000c044a05240024540c0c919460401910300341195118480b158030400c8200d4040c0d002005072003d59500d0300d030100fa801024000504203141e8a4034400003050781c11102003c1055aa005900c1c6088600d9522548030701c000042d2518019284503e400020070000911f40d51700c170784603118000950b2210f00341400d80a609030340c1200c0c4100d80c27807620305681d84070603030031366803c20100743c0103000300d10b428030070b601d44440f400303903101440c0c4201020240c50b0800216600d0003841138412031940304044422243ca101e664540e00c0b4a00c94006812118855082c2002d00384420143d10a03080000206000d458030701e800c8580341e02c002c0c42500c1c82587c8480c0501c086d034050103a580078504954884c481640c940c103104010320000340080080c0008c4511421a802505c900743c20428111544181e01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 76109138 1250 76107888 76107937
    0x10801060b0708090f1f08042a050402030604060e040b01050406090912201b04050108010605030312070c020a06050909060102030a090b0304062a030b0102070f0b0313080408031b010b06 81
    0x204100001d0311b408144101c5600e44429910a020910480c0910b412440399a04001d5000c503800140c00d29092104500409024a041c1138004681140005c0e00000340307136a9035035008034840da0a98003152841d628000403c013601d0140202d2000e0f05805104010741c0c04a0340d240ba04110340c106059040c0000c3c4110b03048145030480074114002004016a0307d4414030580c01d028181311408130905c00d91400d8004102d1100521500301515030190095251013a51503890415090007081300d0700b00501c15004000580798090312100620b21f581300d90303441c4e14501c0100304004000802c002c2c115407052090365962607224a8000032503002d070507050b41e42e031074030304041c1c000d0600c03d01c0742c07a00d08030500700444064062100c41140003a0b42d039800c10132441541c0049849000c544646078a200e00ba810510220442900454100300c01407428002902242e5a4100d5508507502c03402e000d4202058032810781c40e40c1110f80ca1100c4040000f040f2a161490020700e0358068446c50000e0403820a402000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 76110388 1250 76109138 76109149
    0x120e0705031006030c0e0c07140304050301020d050103020108070e09070309030e0d030c03120903050a11030d0905010209130504050307030e010216030b040201031d0c040e071a03010801060b0708090f 87
    0x1409000d010b035205080051045030140c12644012034200c5100000020149200d81d040d5000310305805c546490440261188600161a04241e94040c0010040014282e030248010200c0404400340480d003985180000740c0031800040c581420f0254aa0040049a4030b40c0c0382103520141e04d080c0082d0005041c1000ca52104402012079006502c0c4180ba03424580c02c1802c1220300c40c4299940300100b9071000c800d009584000a0003030201c1c00c14044a84024050347e80040200d400b10704890421081d1059803041e110102804c3d6180c0e503001030703105c00504003c0300a07100386209010a002da42000d0343e03500e03902e03c03944802601704100071103244c245a2082c0400885414100b0745d2058040e00da060020721804d0076103040f804203144c40c581c00d03202007040000c0741c0e04219080c040e002507451582407001400c086d030f62000c454050a1400b10f01c2c540b08080542c865a0410381841d1a5030400c042c00c4c0c02c45500b900040d47e20001800642d00041001c0100e80c600c1c030f02039070200f41818440b004280c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 76111638 1250 76110388 76110403
    0x40516031a0d1112030a05031315090605060109170712080c070e0906150d02010e0301060b0d0b030f0109021005070203010b040207050a110a050a060309051207030207031a07120e 78
    0xa512441d550b00001c10311024007000159801d0464446500c5140340070707080d030f5034820340400d0f4000c141d06100040d00d4a20f0805070540480c00707810800103905080c591201120241c8104803a081c0d41c82d014000c05584c0070500c0800b03402284448600d0000321450f1a960f03d003940b0803500d07503035940c60582080200c50800d840ea00000402121510340d200c1a1100704c0520450b074443c0c0b18460f0800040c003800c20202e040c0081407016100e03482e00513954004443c424404000c550300f564880c0d03400256207501c100240708059030140001111414403080508110030070b0070303001c200d030304000021016a8805003404400405802d013030b0b80d102c220b440424050088880d44e194428804569507090140c042071240c0c00611401804400b409a1020070003c4003450240315044003140d1028081ea43c003980c03001754128014801c880300342800405800c910350050f1012001604249820001c00c2310741081c242d440f1590384980a0103182100c00140010401c0c041c441b1820340721101d04415050600014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 76112888 1250 76111638 76111691
    0x30a110a0519050708040303200303011e12080301050607031404030803010e0a0510090b040e01050106051b010b310603031d04090809040c1103030708041104051603 72
    0x54840d101000d000d04280c0040584401421040d40741624191180089983c03c5911040f00c3e030070241581c40c103e620f4404402100820040d624121220b003204201440c001d1603001d5150448403080740320700181d02e200342e0050140000340e00c00c1c280003902e0801541c0c103450382910000e85407115400d04541c000140c54000380101c200140c084184111440214140c40100d42d45500540b500000701081701e00072503010440210907042070003070160f6500400030030302c401040418a109150055400c45000b0ba0004000c0340300082c807074010500032040414205418070082002050081c041541c3c250208a40e2100080036100100d0924140c81c000c850600700d01400c0140a0301ca16015080c402083c02031070308040e1803030700324040b0324042c050148200e0340500c4443c1814541800d200141448070100340501c8100000d0201c54130080020354402d01c01c2c1d545003241c1c1d0a02d410822240e03175211446500032070602c010401c0d2040c030306010240789076051800240d9900f601d04040c8502c1e4100d03204 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 76114138 1250 76112888 76112921
    0x1c080f0c010506120f1b010e04050109020306010305070c050a02010e040f05090a02120304030201120b06161101030506041404151b09030c0f1a07031b030f030b01050301061202030a 79
    0x550320001015071000d0b100345003c1e04e09240c4803030040d800395640c0c0c03800e0740b5440c0c150f8031840d020b068109911408140070101810446410a42d40380040d040d21000d030010860b095000c400c1022640e85809501c0c0c000a003030414824205840d103485403205214100a418019080d84550b141e4440c2d900521480900c1c403c1000541081a000741e26600171090981c8203181c5030354030b803824144c040115011683e058480052007001d01155030080e0030214034090f4800303000d00001d13980d81c5224009076415071280d00410141d445000014049802c0501158055441c0401d00b450404034107142e81d800c250000d41020004825500358005483c2d013000f001c2440d00c1030315841c070100da00b009510040e80e00c0b540328104ca46440f0341d59101c00047c01d1140100c140300c2003590f003003034500101c0123000c0c00e4042d103171040003401b14440e1103200307412800c001c80016483d4102e861840c2c0e03051140c00074210003413038110324551412400521150030b04540e441e203554004003103141000c25610203012804600c81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 76115388 1250 76114138 76114147
    0x90607060e060601021c050405010c0f0605010305030304140601050d02040504143c03070212030d020a26010b0315031c03090b0a02040b0d020f090a14030705010e1c080f 74
    0x800d0b6154042694114050b00ca04d4444045031410351388061070303500e000d60703a141c1001d103003c00465030342c0040304040d40d8500044402402040040c011a4041c0d030150b4002d43d942c3c00c15282904c89140c14649a00c080d401c4240180003650303031300e444900c210380c044030081825151820310300c4410480860422051140310510815800c901e0b08480385600d5401c684010070080740701208003064210b56080c020742003000b8403401450049044400d0305813034811242840d01e40d0811108030391000d44030b0000306e14140c2c0d843c50303081310400f0901d001c01c18504940c03040703501d08507105806010140590404d140f0707081000d1081c1e10200180b1800c4500c6a181c002e400e1411840a8014103803580140d48296801e0001404509140200c070202c54500e55500c2c9014000c008000003900f00203000c804821040100481c41e0795441040700243c0014ac1541c459422200205032522410713600242c10702c0303561b60703000c40c1558881c000303901e0707041c3d032107050308811202031500651a20078032060071900800404d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 76116638 1250 76115388 76115411
    0xb27070801150524040b0c100e0a0f020909030d0204030809010206130b010e040c08060403030b0a0f0f030807020a050d060b030d1e120b0d06050405010f020309070b09060706 76
    0x15829049540c00002080420740500c040740c55400c040c010581c01002e80345200d4842000e002a0111501c1004040c900305034840d5030f142d5003580030308100b403110760100c11190500c2c1d450784924040d8180c504014010f216042c3e450b2007001c262108080c1c41802e43c40c00044c1241d00c24022251643d5000c4002c55640d9143c1c6465009500408401d600504c1000c000942205c5200b800c5121281c00c00c181c03103c103030328050101e1030b02000140102d8190203a000001201403003040101d0141c0d12035100410107149490600003d80e56035440f042c00d0401c4400200710311180c0076040000c2d07031341103100c0c60303550205800840c142254660040e03400c0851080044c041c841c00e82d001c4c0f040900114190781e24002c1101085030204580350540454404603a070f9070442600620100340b0600d072140b00072800609060004603003a2484100340c4503a5254409c1104110080c4038000428020481c02c42c25170521000c030a95401070350045046c0e400340011100074568030401592019070b4040c10601083c551034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 76117888 1250 76116638 76116643
    0x30b041113091401032901120210031107060e0102040806010f080c060415050705010e060106030c020106081908070503090604030c03060e0d0e040c0e0d05070f0906120b27 75
    0x550554140c0180c82101142e0306525014220311100800d248180990850b241e41d8441d00144013a0914004a46040f0040340034080d81c1c02d0007000440704444c00c013031981c0184008074031000105000c06140030203041c0f0b030f21200c1e0142ca0415800c2a40043d210801500c40350091103144c02081c6240300700c00002402090244000054031414419206101c0e4001c0a0160038005ca000364402c2402024011030228480c1000d040681d00580000c036074040b80354000c3e4104002a003142c0700103911a03a2425102d602401032000506a042c003c1c405824800d4090f41c001c8050f500007060300070002000c0c81807050030000e40300701e400c0003485070740d0b00e03a501c0ca03000d01c10701928401151f801d4204414901d80303480100b515130949400b61203a032a002142e0f400c100c001c0c0460210300c001d22500d51603030900b9495500c90520014824001001c03940d09228054407038040c581d000c000002c4c141541071100e14299540d0720f86159001d405807040f0b888050020180d00e80140d01c401d90031090010031600316000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 76119138 1250 76117888 76117897
    0x10906050c07020117010b07080d2901020c0d020906040504080d05090d03050105030109020f09060d05010f0c091e21140a061d1e031c1a0d110d03030b0411 68
    0xd80b12005c41a0741c0c001d0003502d82d0401d00c00c01060513414003900001c64606401010300400701c407400a440f64150385222012004800380c82d0313685900100c58045135804001d045001d07401101c03441810045980003407521540144510f02960325100850208000b22060b5140041c0c5ca0707000388814504440801e030f5600c500d41202c00080e04000000501e42010300c2031841e015009407034424444e5555041c4041040050f00c0c098028520002c5500030807400c2c419811014100d40c8045041c1c06243e0008106800942003600540203034500811021841640b14007141c200b8285500c00402400c00036a803400344c00c03c0074005a003041c544140b00d4401081120800784180301c1004888036512103a44040d41945444016512030035000d8106e07034901019031000200310341180e2400d80350310b13100040c4242c0150002070090301c4101303e4840e01c80a68030030321030702c034241ca03070b42080181c0d83c444102d040340a8554a01907000c1042c4041454400e802080321507001501c1800035000300e0700b1040c0c160b0301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 76120388 1250 76119138 76119143
    0x81c0e0708100f02270f0a030b06090a020306010219020d08030702010c090801020a02070302241b070e0601050307081305010c02071a19080a090642060c05010906050c07 74
    0x81c018911901e88618400c0c3c039002d0041d04094800d402c0170010032510059141c403030079800001902402e903c0d0380c41300b4518010b54807401f698040750600c3e40500c80c0c2c0860142030154410700520400850381d0340007900e28605040791600c3c0300600c50314000f054003038901c1880649048800030400c81c803a81c0540000000c0d803015900e0143d2140d842d1025400c03070040da2004001a0484142040980b5040451070f20a80f46a410300c24845881452880682e02014802038404140701d40407000100c1030014400401008020045524100e40000c000d40700061207241401107884c00700306404807140d0344505159101c0d008200000040b00040d659554034400c07034020001c0b0146540155189000b0b80c0c600c101366080d6030f4a1004440000e0740caa00c0c00034500c0e070310030b540c904031070340410501d01901038076204151120b04951105001350701403501003030300486013062020360001c5c0d856074100020103d6008fc030b862040c240441c903125014041c080e4000d46800d0a00d803d018a8004010080804a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 76121638 1250 76120388 76120391
    0x70302030412090302030309040e010f0207060b1003140123121006120819020f070b04050a05040e0c04020306040e0f0610050a06020d0c0201110d0c0618081c0e070810 73
    0x71682c14100d0700c0308514040203406400c103100a15040c1400d421440e090807030540080b4605002400580803070300104426034a00b40c840c2698491400d00e0980e5070402c204628050140c4001d07450003480c156010312032901d1201388010185d8420702c0352402e8101c1e80000804a503da003000c0f0b020165039031b03174851040755924503101c0e002521181000c541a800c591003039460b400e040c098640c4001c0003184940041c1540108161107010030003d026280141007502400e640365410f1400344031029102c3d401880c0a01e213040301907240b441c4000707214881d005007240d000d40c0d643da403800864082c159000d2800380900c100300404007412300c0401c01c144036454034009000800d40d54010800104040d03c103036009604002c01e016200d5104444089140d401030401c1400840b00c00c17440c2e8500b56034070014100049002d81c244040007140d0040c039003860800206030013802c2454641c0101441600c5071800c64420112000400c100039400001010710349009490105941e005800d4880e000e40180d1115103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 76122888 1250 76121638 76121663
    0x50904020903061005031002181e060406020d0f110a12030f0905010209040e06042303190203090118051008150405090304170109031b020d080409020a02010f0204030302030304020108040c0e0703020304 88
    0x20401842903401450042521270380e1010f80c8020b00040410420b90500c400c2d4980c0d20045068450400410007030000758020702c02c10320300d0b2000134141044401c50404114402e02d40307100728580050a1084960003d031205000c000440c0c3c144c00500040c6d0750020780074101110343c81400f406602400ca90300007074074103104040741e141c4a00c2d1161412540201b4012425801c3d207042d10803800510000d8642c1030449140072050030b100d402000e400c00c00100103903c0064560541d580c05110b14512510b85003407543c150303040c54005803140c1c1c03284401408100011000031168000480d0542e41028040d004002d0b908001e070119490b9403182c098600120203422540c52640310501c1581c0000340c06a49402000e1704002e1600250003403010142d030f1002d800404803021580c641c2c001c0000301911039005a44a01c1c88030060b00351240000369040045c414071003007000ca600841100d901ca80d092070304000b0b83da038900e0543d0940c01d494111084c06605001082101c540680c0111300075401810000b054 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 76124138 1250 76122888 76122913
    0xc150a0c11061003120203040801021207030b030d020303070e0a171c1701060311190305090f0f0303010e070c0c080705130b01021c09031a040204050f011505090402090306100503 78
    0x254641510910510505904100301145081c201d0001c400886c0c4103591030130340d44110703160a981100781019101044030040c01079481d00740c0710304210b800c41a40076191030403500ea8003a40300e0000901c5101803082003e0100e05540e81c0d1040d180181078013140001c208408400c0c03aa40e600000038801d10303482c00410310071220314003802810080c842003c0c0d80c07080d84d0f8200720045000c0c02d0400d0000000800501034024410451160240d4055007954000761b140740c01d401d01483c0c0891000d40c03210701c2c0c01804422110042c00f00460b41580e0031481d081b50140c0782c0b09011078400100070b002422b0081e100703001103451000442c0c440100d6004445080c0302c542c0f001c100c2e00848402c0082240541d0000030002d000d0f40e050401d1000d4818542030038400e040da20b44410721500761001c02c0420300075000b0304100031032030644540303030b0401c80301840d2040f80d60400f04c80f54038001403015240203008010402d2140b80d901c58044440c06240503007a50018281816405270901c554080ea920900910412044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 76125388 1250 76124138 76124143
    0x1113090b0102072106090b0405010507080c07110906010207050604030620040501320c011b08040506010308030405070b040605030402040e030f0f1c1e0b010813020103020c150a0c11 79
    0x10b80390f41005800c10181110701e1440340407260300b02105d038103480c0ca0260b4085055001c140b4800c50080c0c0c0007240516040c64020a05da2004206000340b0200b48100e00115001508001d0300c140281c44880403515104c0050703280c911a584040c0d44100d0008000c03080010f41d0b00803125840c20070070318083c0d806c1e0344000ca82c594059806010300040b50380074813109050f40107080c420100d14049000b1408199194198826406a1200e81f0281e45841e04509030a08024200c900c800b800c0c83c122865080940e40c058640d141032101420105010000c94188003051000c803008000230f107081e9541e90382d12034000e0015082210182d210340d141c03000b5540846800b004442c2c025045c044040c1c0380030000c111404c625002400d035040f0140c081c900c9606940e03a1131090080a5208100d0b000c01088020110030541e50083c0f203030fa040018200501c440c81f00307107401240503141d09003030250b190035454042d80d140000d00b564248440d00000c0c284044020294050800c60101d47e071001940c461801c40d542c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 76126638 1250 76125388 76125403
    0x6090302040b06090301090f0506130213050a1515080a0203060306010302060d0e0d0c030206130804090c050c030a0819060311011b02040c0509040606050301120201052b050f160e131113090b0102 85
    0x1c0d0461512810344d549518103a0209078005036820740014004e0b10c3c011852000411030f0003030004440d040344004405a0040083c9500044400041d40b031460441c021039201d00049c80000e00401e800b160070451442075400540e12020003a0458403242d21402c0300600e81c0321042c00950160190401041c0742074041720724064115006003c0c030b45000d2600da0f00301e000b030000101e840100720080c048020100c00078401002000c13950342c0c1c0c6003c3c41c20311456519141c1c84100e003041c1c843c0d00c0c100f42080000c40341c810303174040194242414440c1d030400d0040d01102410304072000703500c5490a1aa0501d031904070025000d0718000f0b480801143d92505400d440d00e120038011401070102002c0c1c5500158030134001030401480c0e2031015100c08c002e10120b030f40207089200c1500e040302d0312042040102e000101045511143c400f107a00e01890a107800607080380c1080760414080d001c20842688014050340001c0700c2e1040100103103a81da04118000705a0354004d018101860742000d80f42c0c16150300c0000c541 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 76127888 1250 76126638 76126643
    0x5090f0a11010e0405010305030a091e06050d0207050f0a0506070203040807050906121c0e0a0303050a18050a030305030a0c03090309171006060c02030c0a06090302040b06090301090f050613 83
    0x180190100340c0c59012086288061507810003c8400300c0c40302c19210750141600840c80340300199201c02d070401d0043c0c040c03410358101a0300381d4181622403a07840c045004600440d12903084c59942d070098000b100002c2c1c45108401340080c4100c0e8100300e03c20100258400009000f10180c1c0e031141c959a400b01c2e01c074030a0380311744c09560f40001011310043c40e082d440700f0f420640003091002c8540c81c04040a06106a080c034200030748159400003107141e508882600b80782e4000b200d081c1c40850070b560740a0058010140ca54040041c409448428143d40c0b43d500006090020301031074405559280c020541d6200b101e44403030817030912681c0071080e0700a01a0701c0300700740d1684440300d00c581403031541005800c82ca00810300c240710309184041058028030903c00501800d5a8160b0751b4080350051628082c5e07415400c5001d120040c1b8100141c80e8800055402e07a0350490700420410500e000150060180c118070581c076502e81520481006aa048840c04251042050f102e030780c5e461040103ca11400c50303101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 76129138 1250 76127888 76127893
    0xa0506120f071b020f0d050f06090d05120a090f08130f14060f130906170d08010b0d0902040615111002030702060402010c0f05060a15081906020f040b070c0905090f 72
    0x8060041c500528601e0b20b15a025107940c410000a40f149848c4c04164415a4a02d8201609001c0f00700410b00401403d9413060602e14500f0030380c02d40360010404003d2800d0344641d40c0303008100c10060499000c903c5c0d1500000b0494480260081c00e000c140c0140c442c042d91010103480000c0d1111b0380c00440f07807103024010821800c4c00d101c0c2004080030303480444080100003000201164109091007004050901c9611040d18500031404452034002100c8414003800b450740010012041140c0c101c0b001c1038104080420030744058804039010305225081141c0c9581400441d8001550000e041800007480348112548481c5611081c8102d100940d0060010381003400050055405601001e000b03512a80111002c400c080d2501c504001080c2c59040d1140d031070f40e02444440c4a0841c2c0d00001c0c120304406010036040941c8043c0d0040f50503440180260f0b0003055510f041014501510012b0a804004581d24821481c00380c010780014040c4d017030b8051a080c0800c04c1000c00180c25203020049100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 76130388 1250 76129138 76129187
    0x6091b040608030f03072a06110313120504092a0c0308040308040f150c120c0e0915060310030606061409040509010204050301020c0601140d02060a0e0a0506120f07 72
    0x2130301c042d03000901d00c2d810b0084001a900f440e003000380401602c1c805140300217103108220b1602c0e400f56800b4003d10a4a5070007841030060411a1480c01204c0d1507000c07110200c00c0820300340a698034021a1f00c00780450346000c0300c070f0240c0d0002c03150680d0b102d00c44c2490101c401404c40801c3d5040d00d40140d02a0006001b0310028000034064820782c0d030043d006034041c225900d22582c91101800603240a00c200c917468000e5001c2507a0042420614500900d10601403140200c1c0002c141d01b8124a06d20b2280301098080740d084982500107201c03020b03011702040d99921304007140140600c07051100f21261490a000010160310a04011541c0f01403030070041c0c2380410a500b040003412014001030100e540c200030000e066a400d200a12050f1910806005035601d0060016487d04107040240c1c002d02d4668044801a541c9100301e407900840c0e814100c8090006074003198a8078941c0c3c0101d40c000c840014107e2610a411440300d218000d80242ca200303940e251041142d0341607401a202e640da942030784 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 76131638 1250 76130388 76130407
    0x7060201020712050702150301060e04061418040809120304080f01020f0406030c020106180b190608060105030709050a0909050c030106050a0b09030a02090a020a0f0c0c030209070c0506091b04060803 87
    0x40141710040c0000e10309002e503800d11800c01c08039807080c0d00040104100402d1481c8900785805540e004194101050070000404d4010500c000944200315904000c80c0000070200040102541c00503038001c0c12007030a050310703045035507a81d502c00e0151148521889111220280c0305008454441c40210801810309280800a5026082c0343c10100159520390401090341c614505181c151401150740105460110400740062a40b410405a501d10110340041c07000c607400c120400e400010a290050b0340c0ea0b079880c3c049483c60340582003183d00070000d10000419001035040401c00c540240140e502d444402000c1508071a0940314241e0005211340b403c114280300c1c0400b42c40c1041c006000c0e24032803003850380010003140c0c04860b101c001c40e601223030103059580e00c50303d0111501c0043c01c00d0b25501d032103500ca440784501c05120080c0b0404640c0d00013202140308101100d51550b200c0100c0c0c0c5c050400000c00ca444840380c8480c842036100000c520a007602d014018002200e0880700990714126400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 76132888 1250 76131638 76131647
    0x203010f0515250204141006030c08060a05061c1803080901090b0406050c0405060d0e06090a0c0b03040c0806040c0501020c06041206180510090201170405060a0c020c060a0801050307060201020712 86
    0x290f0b01aa40103a417815100d08021010f180b55100301c25030a030740c0c400241803010103022603903400829010006410100036054807100c8441c1d00782d80049500380e0f1aa10008401e0801440c034003c00011582480f040d4944010a4103103101114840d8490324040c1e0344440180b400c0ba802417101914412100001c203000c611240e1183c4e40003018051b00c0c03860f09407260007007230a0364801110001134a41d44c840c01e101c41c80050000ca0b030000c444e130f0042c0c00c00c48000e40700e00c18440e1650040000158000000c07500304091441e807080281501002d42da064680360a010701300c40799500c035860140c01342e030081d24003034600a0122030560b0304100178504400b40c2a102d000050900c0e1442e0115038036540150400318100300043d4031202010000465403001d28800100200b166841c040c00224025081c80001070000c10000d03480802e407400058140c8488600f02e1070003500080c0d80b80c02210018a45581079448462203044c2c2e0f00541c2120175003550788004a080f4030803400080c0031100203074180b90059114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 76134138 1250 76132888 76132957
    0xd0209060307092d0b03030f091f120501051215060301110417100507090b0d0902040509010c1b03020a02090c0f03010b0d1503030806060d0f0203010f0515 68
    0x942107942c02c0752a00c62900484040c1105a4a124401400701100410103285a24000302010080c88500404000300e9500d01641262582c02c94002c01c01c911161640310301c0c8240602c0d804541c5070b1010180c640502042c60040d04ea00a66050600114960800040f0400310710300c050010310584001b010341004841020f024a0b600d0b5485e0340149200101440181c400703000300c100c90800480c501101c0030b2526040006040c209400c2c18200440b483d0040c01e5542100c15100600b075423400700e805040c006101d0f0842c0254018984000d104001c1c070705501280089101d5114820084103540c0440c4c0c0894a5040c0280164000d20400c001420310100f255008031084030994206200359400c6002600260804c1e001460041591041d041c2c40e4080d034164032000b0100000000d0461f01c00400f01100100b28a008040004d541401d10b001c95000035000c4441072030454981d615000c40400d050704511420344034110722a40a40c100030100b04035400f150b080784100b907003401c14550700ca4201c0c56 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 76135388 1250 76134138 76134151
    0x40b090406080105041a09010c20031207050a0f09030b04171209061527090c03031606050c040e06010806010c05010f1b1103030a0905070f030309050a140d0209 70
    0x8072101d00145071030003400f8042c029880f50418504a595178043c003014004020700406580c0c2c10403550b2080341d0b4011040311030b4184042500380980300d0a060540c0382d446510080d1421500c54407c01140700d80c404060f144903921561141c0540703000d0302c401c865202c0c0718000034220354814400715000403501000e400202d503d10b510b5900b000440a440c8007001c008072100780042d009801004040d05e00c03e0000c400e0120202c8503840114161a106240b82e40d0380400f042030f440103c0c0101c1c019107000c020020003408000c04580d5103501d4072501c0c1c0b2090a0302a402c888460400d0082001c0c54030060a60341914901c003024440c55440e9001102c4000001d41024180000303001e001d030100d44280141207121900403000308a4005084000b42e0011010b5000b0081041c800a802400d18020003203d400050056020400310b0031030401c1420108164040760440e95910030000402d90850355003412a441140c0c2446c103150349070301410426070800d12965000621030700680c018a4240c0c1c48941020b03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 76136638 1250 76135388 76135391
    0xf0503010504020c1c170709180c020106080304180c0207060f0e010302070602031e0106030c0203070b09070b030f070e1c060911040509071a0901020d260a0504060f0902010203040b0904 81
    0x20003c503a0380000c401a86030b040c00043d8866100f550740e8106e0800d0603009447ca140901030300c0c0c03030710f03401c0450410790142e00f0b11a5904e9507102d80f03c0d01d100350440c0c0068104a01500d5036580d503402252880c1109940b5000603604007004815030038000b04801d0700f202c0040e01c0b804c505240700b41044405401a680303040c140b507428000c0c10049240340c8095403084600b809004007400a10102000598050f8804010142041d0b03400c0355285d40441500d041d140d212250707034115103680401904028194001c124041d03008000c0100811001481c0f038098661034651030b086850b62018032201c80c088401c410003903206030509000050007580001380083c016500804440d643e80009003d0b154240c0c0d52041c6035000c40d00510010a0035500740c00e20701c6024000c036180c00764003400030f5101d060394282c00050002019900c140070721a068146c00013010401e0740c2c201460702e0900e640040c08255030503510189402d40144801195104060b1501e40507002141043d10b044440c080310381c0420364094009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 76137888 1250 76136638 76136653
    0x6010507060f0203010312082a0901031806020403440d0e010b0301110403050a020909120408010c0807171807030506090105061503010605070f020a0509130309060f0503010504020c 79
    0x7550302d840078602075481001c18005240307a10f08010101034001d02a8000200204c1c503040c06d0000b1011100151030100c40c10310b4840d59201c1c0181c1c014000300c1c1000d03100d02032458114040041c144e00510070740c0d00c1a6400c1c0c0d103e07184400440c59440c20200b41180d400e40062844d400884550ba0848007965044040c42c54012041c13418000d44658020260441e911251000d48514081c00740d1802400d007181c00c04d0510385035407580b950701d24080b40040e000b1228207021138003141041c4204a580000107010365075881e85e804901d030003080304901e030700300044c0c040c0c01060f1060701c03504c130214120118008512483d01e0b000103060403901d0844080510388181d22001001030703002e0102a126a0a0790300010b2075140c5201405441d0642c03040c2c0700509401000148180754011003540c01541d049850b0349510321061002c07681c50b03c0c3d6900700650017a030b20001c10152000030100c4000451103941c6e1030701d011b0340c0c42e44103881c44000c3c00c1241000c5801800140090704042d40030340340a02c10441200ea08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 76139138 1250 76137888 76137911
    0x6060e1006050a181d0f0c090d020409030507170c0c010302030717090f010f0b090c04030c03030813020d060c0e0a05010c03080c131502010605190308090d02040f0b040e0706080601050706 82
    0xa40301d6681c0b4645c02c0c01d01030703010030105010004040e64014007046d86c081c038103040c020005480c00c4080000a00c80c039911000d00c41814826005d480301c442d802011a0170404001c16a103480d500a54100c0005200e960140d40c0d06510034009c0d00d000700c44a03100c0ea0008640074a028440250080c0081040d2064103075039480d05500740034060f061101180001200360001041c0120b03800024200c45881504100401c00194031820200403a41c151418810986884880c0c10001091601c081c0d8020552050710046c0304166005c5028010300e51a82001e80448a05110ba1004103105040c0451030384402803002c00d000d00d0f90264020f807100e040c545815402d11403441400c0141d00802100c40c0c0c0f61880300507442d024032030000030740011102c00e0710000e03201e074014169190b1400014450400450020800e0b240d01c4007482d40664010b006010340303419001010010020042d58901c16420841001d400590100d8100143c2d505a0348604069940c0710042d107403640600c00c119400c1e0b6441019110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 76140388 1250 76139138 76139159
    0x40f1110050405010e060a080115020106030c030b160309170c03091c03170c09010f0e12010203070306090905190c03050604080405090c12070f020a050a06060e1006050a18 75
    0x1800403940c0300c40342c8907400c14000400901c1e001c0d402c5405401c04202c1e840d41e80d0b8010802c1790441c1c0c21806030581406100b24102d02409031540020700d66869686c02004204e017010b2500e20503c0d01e580d80079850824050100c05403000398a0151480c82da0a50780ba91100c0403c006002d40c4081c402101d00c0c0c00c240300701083d142c05e0344a20140c1382e18049454241050b90140c09104101040b0425a000f8100010703401928800c600c40581800f002e0200145114082e013541c00741e11900070441c4601c043c2d0004824042e62048a100e40040d180c040c02160039111480380301c0a00b80c0010080c8101b0650400300b48048004070320666a0b11403080002001403000c20240c4d2142d44240500d58880c2c1c506014084240cbc00a401c2c003245410521021082c0c1c400e040c1490703803004862034403601810050710281e0410703940c048060094059100d54000340710050300200c0c1114a400c4c0a01c080da174815141d600c42c0c4920340a4000001e10070880025810300ca03240504d04c0703034a484a168000b0b0b07a81c0c014420f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 76141638 1250 76140388 76140409
    0x5120406050103060509030304080406260702010b15041202100c050708030c06060109060804030c140d0309120e0604171009060c021c021f060e04050a05010b010306050108040f11 78
    0x3100292101c0041c810002c032802040e03000400740c001182941469550002035004a002d0a010405115843c1c0d0311426443d41401040c0c0da0742003c036483e81840480240070b800e40911050080344040c0d00000100003007800c41c0c00b114480f500c5406842c0e1964200500709a10124000821101090b844086401840010004d1a40e2030007036031f44050002d031540c14403c0c003d013081d040c446010030401c03c0d1508038012562003035161400030409442d903d000740c25010000b0010245225820300012240e4060344400a00341c003a00101ca220400003030112054016031140d140c00a40912041102a4425581412145503034083e1114840001c03210411101c0700c140c103495043c0c681045040180c0c05010b1070040065400401d603021880340301c040c1d5105901c9a10b0b141d904510200b030b000200041c0c0c0428003518050b88410411308190400a07a61070101c501a80c2039440e10800040030342c0248078000807920180c40f0720400e5034580c5c941d00d620001e202e8083c1d4042c2d481025405040d40c502d80d051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 76142888 1250 76141638 76141643
    0x3160b040620010213031106161121070501080105040507020d12020706020a1d03060105010e1002010b10050408060f0603070302060d0b0a09060f09060b030402040b0d140d030c02061e0601051204 85
    0xc0c0e4a4131b10700b05030348500c4020501500a0208101088a841d000342d41c800220303400800c2083c041d003410000c00d03c01e200b121108030051740c0c120883d0088180124000382110740903a500401d40c0d882c1e500308403c0751404d0742c0020160303200710080440d13140154611400311500f00c20041c1070030081d844000680c4c1c04503100c02c000030340e0803200f12500644803858000500042d40240055814440080c21600866260520641c6050084072800d0320075000355040c1c0320f019042000d6851081d1010f856a00305006c0c141e1103001d468000352411540c0d010551003014000c0c01132100a10310340a20956601a01c0e546076225103680704e00c032036134035440c0c480300c004c0a4821001a205290400d0400c400c00581c012420703140c10484100311711125032003503d81041c0c044034009080c0850500040d0300209038100108000d08540303180712042d5010407140828122614248103410808404a807107500c101c504002c8001c0ca6802000c0003031401901641c4100181030084c40c00c1c10000401c99483c4088608 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 76144138 1250 76142888 76142917
    0x51c08060a1502060109110c0109050105041a040507150302040b0c1e030705060c0f0c070b070b010603050412120b040e160b12010e07020a0f030203030603160b0406200102 75
    0x2400628101810404000c00c040c0032101c50b80004640000c0d1582c406200b41402c039600d0b0780607951515000e20031076a2004071400200141c40f0103182141c00b81c4400c6500707031249090154030002004000c41e00e00d02c1103600c00040c10105040c010100400000300d10b41808040c0d0030b00c004100590503400130300030740100030010801080f520030103811404010050035030580060202c140060b400140c601d0300208100d44c51600c07410407045c500810700a092541c030750340c400c000c0d00040c0f1004400091030030b0b900441e01c0c0c2e0410703a00e40b1026400d030341056a005041d00c1c1814901481d051141e540e000034848100300c0460a10708080004041d91001c0101000503042000e006131568121121075000748400d0454a0900940014002480c0e00c1440342000b40e000d10400503040f40c1c82800400103042d0b100d102c4282d40e0449040083d629041213a640b402445103d0180d0000f107a228640021a20309402c01c610b0507007003600c100e84000c100004050607588030250a240341e0001e00181a141010340724 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 76145388 1250 76144138 76144141
    0x151002010515030d05120c12010b041a040e04020103090609140705010908010b01090501050a170c04050907031a04022d070512090a0e06010203090406080f07090203150904051c08 78
    0x40440c5242d0341c000c4551113607008071002054660410140d9028404442c80c8141035139070040c0c0e001c264810340780d500302c50081072030002c10000c0011000d4016226010340b41c810904440c2c4042107a880b6500901815580c0392001500540c8a500301d43d80b140d22a14010071005000d50750310701c0d01d69811021034100d411100090005c3c1d64005c800302c00130072810300240301180d80e00c0000307803000c001c5000316410041e0028000c1003a9018248441c40744407005502070184c5000b000b2000d01b5000390164922a00c00040031403080b5209014441e140704003401401074140c80780302044000d500244818070740d041100f0004d00307180001c0301e0b00714007414070b03400550303540c1c0440c900681010a841301000c08040180b181201a0f15503200000c291405400c3c2014141c445500507407642c02220701c1c96034800c1c14800007044580e404281c0d01a407110240480d110161180c3e40d54017a400110707039034060130007804001d5030b051030a418600d41107406039060701c4c200458420303060303154100881e02c82e0100d0b00500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 76146638 1250 76145388 76145401
    0x130f05030c0c0415050906030f03040602011a04020a17100e0f0a0501082e020408010c030603020406060e060702060906090d03030c14030702060411041b020c0913020d0b1510020105 79
    0x44460302500443e810424510365600c8100481c0203405001d0040340020001002030f102004551110060241181d8480d5038928000b4080c012203c03010803400607a07014138285003000e0007911041d0000d901c0e04a40c08c800ca40312200700d075000038033241c1d034441400000207117111780c1000180101c0324101d451100d86401303020b2000756801a8403c05455002c04c15080c0c64202c800000448000503413140300c01c6001000c801d030080c1c0902d4005810951a24510303281468042c1d001a0850303100392418810300d40c0da40d46c00d07181a0100c0d4207150b04400304101840044c9400d200810702010024800c1e814000000d0100e603410706403c40490102e07030340d03000b50203980341c2242c0c1d00580742107841031080c55403400c01030081d02c0c1c10303010704028003950302c0030781030300517603440760001c03050407250030380008040c1d19080000f95117421011103140601000d00200d461034441c0c0d48090350107074010303240440f1082c56603680001c001c002004941c1c0b00114441d4411300f6560840d503410041415400403c4608045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 76147888 1250 76146638 76146643
    0x6061b06010e0c0f1c14150301050c03090a2a0f180207030e04050901060b030c070c1502030f07150f02030f06030a020a05010e0f120304180207030215130f05030c 71
    0x2400c1c803c3c3c0d000041c400e000c6008401802c60348425901403245408144503404040640100d035003185154002c60308000c0c0185103e00300ca0b810800440007400a80c98020280d4030314803060310703070707000580100c080200030800d00b14a03062071a021282c0c808503905003803944c0480300a1900000c40d01d52000004004842204c45203420007180b2500c211b1803d529960058030701034800e2042c40c069600d403800684401400c1d40103100900d48074400550b02d00c0c0503034000c0710b43d5204010460314807038070315000300f420004031240c1e003403145154004500c0e007805400c0343c04554210210481d07002030a20322643c858003d90007000c9500140345000342e1682000c1402030409680100b845000783d00c061025800769403964000c5080703c50a084c800c244082d06004604401622a000c07904040e101c21808080d09000009000b141c4503040c001002c0f5640700f440100340d209442c00640180e010508141055110041c020b400c44290f510301421030005591301000f00201e0803040d00c46800124001c024480103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 76149138 1250 76147888 76147891
    0xa0204081605010801030b06030c10030c02010f050c04090e1e010b010e01030b09012c0f010623040b090402070515011e030203190503160f020a062606061b06010e 71
    0x892001e8064141000002000030005101c058485841319021410381d880600c01c0007503445001d005181d81c5654540040d014010404040b0010342c607003410b04011035610b110341c502810f80650030703a00e0107191164200142c900e041401180e80170b80f58611444d460008000c120300d1101000201b900c00e0140005064070218420403414981042610042d9503642c680003030554101c0300c5000c0404040c9144019a030300728401d1504501036003414071552815035109103040f5807850342c50724035403103110780c1c0c4802d5421942c103150f848000c18003007407011303200c08809003c0b505009000107003480110348580b0b10f8203c005d84072407a0021194010300c000c180c40140ca6900020006c03881007403e2459010070f990302d1410282d0b0301c20102903103102080110900c01c0790104100c41d13400c0c907850030a60500d91100c00d154072080748a4a902000098054000c0e000060900980640c1c4802d41403650081c0c103031010010b2895038044401c203d031008000c08096401c00000c6071000406d0258149491905582c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 76150388 1250 76149138 76149163
    0x2010201022206180e1303020c060a05030411031f02090117070309030e01020c1c1a160905030a111009050907170109150315060e0103060507021c02062205060a020408 73
    0x601d040c05010903941701c50303811502c1c004040c0c410107002e0038100c0c140241d101c05940d000c000018060301180e4000040d500840c0a51013800307504c0c0740783c001c15980c1c1070081c0d048880310301501000b800502059005d05403158042c1480d0040242801c0000700180040b1190008290355200170001d0582c0810420340c1c6843c207000900703000d144070000642c0a9001c3c031044c011a092320000300304119103071100d16040c0b1900c01101400d4101101c503c2e041c03008640c2c24030001180c101c000212403800141c403465041e0846420303042ca0160906014240742060b19860602c600d0441c00038150321162480340c032906107541c0c1e5200303480201ca240f2400a00691080c05058200702000140d101000300ca0780880340d001ca05041044440e800c0078010b040c0743c0e80400c0ca00c1d00c1c80b100010a11909821080c45000d0396420b403401c2d910643c40d00c480c06100c00764a000141d100100003a01c51002451481944040c010740c4120a81c960b40c23410b1500e44221809403072140c020404225000c0c2c02c1015820100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 76151638 1250 76150388 76150427
    0x7080d0516050d0906020c060a060e090703030c02100201200a09050a03050709020318070b0a030c03020711120109050a0c080c090108030d02160f0609110307030201021902010201022206 81
    0x2461124018198043c00d0001c0441e2a9101c0003642008042d504554154801c40150345181c54800401001454540314001ca007004030300000d14403c2c070104030701c0c0c103495040c0ca640c5070160180e02402a0b0340301c0ea26000c1c05640d40d54008948440115080060116080c02c15a945050b0844020810b001592285014144205080c0000351000c145101695846000140c0304d0781d549100d00642c0c00c4071555000907000d42500895481d01c00310082c441268a074500340403900389160110100c3c414513601412002510700030030154546084800c43c0404004000f0844000342d40312203003800c03891503040391001030400081114140c1401500d0411750211421039030b170340c54400071540300c0c410b6a0003041042c0e170004110a00d20301902400c686680c0000303030441c81407440d1808030300503c6110001ea54200f080b402134141403500007141c1e425a941030303010345010590700840300d0103151640350480c190754091207100c1c480400010b911180e03c42c409200e05400e482d1805c080e0405c442c0c08074483d6080f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 76152888 1250 76151638 76151671
    0x60807060e090a1103070203070501060f120b0a02040902160b060103021303060c020718140a0b0a0302220c050703030f060f030b06011202040f06020f070e13050c0607080d05 76
    0x80350400d00104180c0c00695114842c0d0ba94100c0da503008003144804a03080c0350010040c0845c8030f81c0000641001c40c4580300800509440d100b01004040d0940705000706c20701e0048090f4005001e0135074464016400d4500517041c9600c42c80100b00740e8000702c1082c6400722486031204140549a420507410a000b82000c52504a01e12104000c1180e00d020242c20741d910f031001000d8280c0700700900c1004200002c0340f484141070300e01050000e41000d0306841d11968001011521290151041c0805108000c140c6802c05203564207118003044044034020540514055013000b041050041c8048a2440e80d909a031b02c4840d1718014040306c006007007520001c0d240034001e115500c10489000181c90304803800030300304d0b5503010040b0b40e0030034519803030f000240c00071a0015520b82c2c4e00780d1820544000b40c080d82c00c084049448641c0da0074880c4103152403001400c0100c0c400f04540c104507070b001d80c0960b040d15903881a680200d40c40717502904080706d02d58030019040e01c10700844e100e0941c02032681c40514601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 76154138 1250 76152888 76152899
    0x70303150b030c0c0c0405070c030e010f0f030b0d021906020d11031b160f080c0103021c0b010c050304030c030201080a0b01020a0b0603010212010e0709080d090b0f0c01050406050406060807 83
    0x50100038500094400300080000c0d003120200000c4d071810704006c01c10b00152a000700010240a460745088000c0340321400b400c5039541c003400d080308200c0101d07519500e41c1007500104801800ca803c41b004d402c00413101c070740c01c0542c554043e004209000050524201c40c90240020b1070203440508030030421960078002d1004020100403201c0100d0040c47e1101c5411858a90034140f044012102e20442100d18000514410281c07071081200c240c00c1c25500c1d040324900065007640b080c222000f03101421401d0420f07401c88141d202c2181c40c0e6062500c0404072600742e840e03d05d1940325800070741d4081401a010411503a10941d0658490382400c02444660080c00010b07503550b081d0540100000c415000040300c0351425410391329990a03007070411100e5659940f88124064041d42c00d41d001800d40302c030105d0056000101031510701e415a039103d005525011218055800c98441405280d60800a00002070402d019450250740592000945030805150000440d0340715406094a9009240c08010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 76155388 1250 76154138 76154159
    0x403110a03020a0807150509011a010f170718060809210304020f011e0302030f070807080c03190f0b010e03060106020309041a0607051f05011a0c07170307030315 71
    0x20f00c1e03001900d02d40b503003483e140a03502d15041c1c01c80240b00d10702d40700820035920415000241e00030300901c0e0110885462100441c0c1071092240c010340403c4442c0c011034940344a0040d5607900c9000d0780303400b0245240e5200d811030031032160380c0000300040310807050003d0b8810a100f00c00b40c803d0f21000b40600409410b0201380140401000a032140b108001d5003202a400368800742d40241502d4800400b044000e10013800941080c3e402d880d81402000000d0341c40c40c0900c0d880c50048529842390003017580c8810740007949520041c0103400030303000301c100500da22200d802113054048040e031022915031701c0100010111140260403c0c803a41c0280010024290044200c0b505082d083c0c40100f00300ca56802d10385080c2c420540b46540041001807420b05000c80480c076030410320284944c15a0925010b0010401d039207003801018418440c0100c4042210200001881051007500995000310b68811010b04550504160614a81c200040e404101075042c1700f4a00344007504001d01072007038101181c544c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 76156638 1250 76155388 76155403
    0x42604030c030602030709261e150a020706020d06140307030308070302070c030210080106080f04051203060316030302070512030c0c150f0304030306030b061206040201030216080c060403110a0302 86
    0x901c03040c4c0c00404100060b105024038409008028259014081ca0008051118520091104003400341526400c40102403144154008940b0001030031442c070454095040240044c0408465a03400c009400c0040c0179400600700c0c02840341000a000c1e442c052030044140d01705440b0340d10030703001a60700703000198100341c0c5650891210310b40141c4880447c80c0038142200c0c3c81c0c00195100140c400e402d841503500c202c005050b0740c504d68070101c0c240c6030320004a03440c020545004246810166107901042160030245a100d03200074100c0c0e4240195203a11000c4c0c5000b90400d90051304250003e200d60f0030b2554903d010301c1501130041d81380045440d19076850b4050700198031b12a51900201c0301070000c100003651020b0711075000590303513070420f440d01400070250b03031000f102d099220000013201441c029100303032600c2c1021005404199181c0e40110002d50007240c0300c1581d05001030111004c1400107002d0300c50740c03c4420040015042a05000d06030550a0394801c2d45540000f042d000080e5000c910780 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 76157888 1250 76156638 76156643
    0x108040209040b0910020d050105010306170a12030902060310090506060c07150c05030307021b0901051003051b040b070c0503070602070902031012200f18060a0509042604030c03 78
    0x20050312003221850500c08651780e80d003017150020601440c500300d01d6001e0760403170394242c030204542a921074400414005411114545400034240600032400d1440e00c581c40200303a240c0011192040c1c1d00045403078005031820b0428006c0301005120365031052140c25007050085405a040483c00524166101090b0185440c040d61264006c0361640c0501070980710315a10005881c0c603803400c800000d5032003100318150001d401040e0744880b0281488800c07503050b1078024100d503403507039213916054016120241203028401c008601d844040700c55240988007030120000350f5581c0384480d08040484020a03000703d032198000c1c240030401c89400092400448484180140e281d0740d48480485100c08954446480c05c814000d0760010815100340e50f5000c409141040d21000c0c00742c7c018004030511000006805c40a42a22207504440390b295080c0d00500080a500a680e00e680205d100c0301030540e011a400306a011514110100d40303908030101e040400105401c05181d510b0300400c410300751101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 76159138 1250 76157888 76157903
    0x70b040b09130207050d0c0b0703060e070e010903050706030b090606040f1211190e100e01050d05240f0108010209010509130b03060f1b04140910171506010804020904 73
    0xa034a2030301e91a0152400c0c96004410b0750b80010b8031b944003405003010b407101150741d0300640c000501028041e02c5079900f51140d0f1003525a503aa03400303105645002e80114098180080b05a00200007403040050300068441c641d0f020800000f8101440400280505054810741c002d210500c200070704072124204a81010480842d988018141b041d00c0b400140c0c03200f50040401c0f50740c0c0b00400d00401403841202c0c1080200c4245d56154034560500c10302c0b0307018014401c2c0030f03500108078a2410f01c40084007a0b015005903020007454907803420000110070960341403c0c104500300803403010441d9209004020103402549041803200000308580f15001105e0302c256401500d8004d4810142e03c140c2e0107a4026045030303030328144500b080d050310504441881d08000d80301d0101002480220580d81210103494901580d0500d00c410032544507402480100380c0e105007100042c0000d0202c0c00f843d440e40c503405c040c2c60348a00000d4031500c00c61006001d5410f002d02c1c00180801611060301c65980b20b50000003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 76160388 1250 76159138 76159159
    0xa0b06060f0f040b1b0105090a170f030f0412050304030f05031504051806090a020f151905090a0e071b03120e03040905130203060a0f020706020c0303040302070b040b09 74
    0x2001c04032801007060010b07001101040100d030422414008041c03040450024681410110341800d00342e850840d607200303043d04281c40020003e446003040280c1c0c10200c0c490241001640900034019400403101c1d902c81d5481d0720148414014403503459600751072103117495480c6290a0301d0182440d03074075840d480c0810000100143c46041c0c0f01c4035403076400310300810510580c149200e044402c4505005842d40e24010703a804206030100008404000c02e038041d00016500c6e040c1410855104a00f0310b500000481c104403482540c2410380c400c030303024840b035181d0315154070070003060007103145a54100692981d51401401b00303040e00032044103007140390035641c41000701c8a070dc0d00f1551048224502d82d160790422400701d5009001001400541e000d9940030403040e51003824100d84503442c101c0194141d0008000b2032151046a0450484d0744046c140c05890070a16544110480c3e03c00506c048240d00301109200426071305000031070003030180c21125802c0900700f81c2601d6652046401d104d1080c0504070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 76161638 1250 76160388 76160407
    0x301151b0803040f060e011814010e0a0c030605070503070504032301110d05060603220f0f030903061d07120618050a0203060f09100902011806020d0306080a0b0606 72
    0x2001603550068040c0e44a040504d00b03e0400b60400d2401c90f010390925103c007103807510500c642c00050f8012400c0801c8801903856540b0070040c629003001c143d540319402402414410400304010920407447c510b0194070b10b092050455030003910f50b50400c9020018400943d9024081e5410b89402848184851101c50007040652040d1a004090f95080441e101c1c0920404005000b039440070f0300d0288034a0b620101040254441243c92058071441c09242d40d990080003500b00444a1050b01092001c13082034550b0050700c1d68910045000400c414400d00822119006440d6410450001d08603810002040c10751244820b009011082e5480000c1c0c40911909800c88104130140450750800b001c29410034640b41c004000081c0c1c003074440c407400305950900b0761541920518080001d0180c42c02c0000903000640700c00c00090341005101c0000742c60003000d0156040080005400a0140c00c4903982e01500343c034415800801142c00c0140c500c004116140002544041c0440d102c0d07079034100c4c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 76162888 1250 76161638 76161677
    0x20f06040f031202070c08010213080a02061b07090608010209100305041505070509132315040504030504031406011502070503071403160801020d050a0603020d061a0d0c0f0902030115 80
    0x405c03029020a0b9034160005070844107500402c032082e80383d214801c1b195201d5032460780e10440808000e4100ca8104980001d103500242e41020340400c1405440c0966901c1d1160001d440007500001c1541c3d5000601c0d840501c3d08418095034205c550a0501092800d611440c69401c503400340441061307100c0c0001410140b082048458050004040a4409803d46081b100600c42001303403c241040d035112402d01140181b045502c070740e0f2a0080021006008020700000c0c05020304200c0500a09110200005000c001044040e140000007000d0039031400100100902d25100c00c4802d48d00503040034461510007207a803c090740e64140c01d100b00c1c0200a000f00780b41800b44070046070041c00e00d5401044001c01900108076013409810140300680351800b2a0b000ca801600c4000d5000102000035800615960003072842d040c0d00a520b5981c00c1408804111100d030010811684420701210600c80010110300c11b80190030340480440c207560411110740448058a54042c0c14460707044004c880803080c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 76164138 1250 76162888 76162897
    0x12060501200304080a0b0610080c0307030c09030b0103060203040501050c04180e07080607050301140913031d12070611031908181002090301050615030606070206070c08030a020f06040f031202 84
    0x4c4e20413500100e040d400c01c031800307000640d90a446840d80c6050005810b2151440034000c42c10050140e1854981c6a401d90041c00003074940e40134070030500400400308001c45880340c0210300810026984e440e062400508541c801001581d8540c0d09020a01403009611407035a0300f28401c40d4005061080c020800f850841594402446485403400304407910fa0b000020310b040726051204600020300030820480d50b48030031030b101c0c1d807048020240100400d1040c0034a8a40d446000b03101e42115071990085950761500d0038415855500241c010443c0329807050004400c003c50b1400765040064800044c001c4640c01016081005851000320b140810000c802c1d8445046180c100da0030980124a180702039007040d8060ba00c25482c207400610582045003125040d18902c2c61311910359951201000a60f4029041c1030360018003d02c25640013403480003824010740349440080d600d640402c00d00900d841c2903020043c181d50000814400064940002d03c4482d950509002c1c0303035404050a0700c0000d018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 76165388 1250 76164138 76164149
    0xd060306020406030c1815030522031d010509130507090b03091c022b020a06110301080d05040e070f110a0f0203160e0604020702010302090d080a12060501200304 71
    0x800030b0000342550b0550b00c215042c054a8071344000001300c0b0b8010454400c03980c490042c880100e80342e10300b00d651080d4055035100800b40400d64802c225001ca00007202001c00c02200801d010b603241480b40401080400d921040920b0164900a590404280d643d40e030b00c820b00c14031544680104685ca03029006000103448258090707174a0f8902150007941d901d134140c22070b818909049001810003880403c0040c0c0100d00e1041c8210129031942010b0340d109200ba141030210f000d641d0160300021014082c8400c4000104401d0b500d95050040a608086a40c1c2142e0f050003000c00003000b03651584408194000540d044c0076014582400c0103451302d122a10015010b030207019954010080b0b0080e0140499000b41e00712020103014001702000c0103180e001e40300903596008005841454290010401e240c0b0626002d81849880350204510070306a075800c550028000c0b0745028400c0c1d104850701001020418140406803034180041c290805d0040f001c40d000300361840016540d2000c00440e0002c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 76166638 1250 76165388 76165391
    0x2090d12030207060c0801321008010e0709030309090522080703080603120d050405030d0c020609010b040b0904030302090a1701230906010b030901060308031302040c080c0f0d060306 80
    0x30800c860040c000e600c1141d08131609482c103000c00c0c00c0da0344034411090580c0c4c0080c64098025803240c4610320390040000c84040c039100100001c0703645484c3c81089501c00d4400f511248400e50608601070fa90f020010b01003810806000c4040010a91010810013280c0e8070000005554a54091018801010030f514042c00040401840d0410495000400c291402940c619a160f02c1d22000c0584400342c2e02c26540414806201040c8480001d40c003084c0c01511901c1201d241410382200358094800d030303206103005a0000020040302110a0040c4449008200c404024520680c40000c001d04e03030241003c1d040603404a000481c5840394205a0050300565503280141c0c400340402c54003a0101c820140f2420400041440b40701c2d00210100d80950840c0014040d6a800d1807044c1d0500e40004168140039900c2c0d440001c0452000802140034004100d00c110421015005100640e07a07900b00b01010861903400b0040c907c1240e40581d464165040d944507540d0391002c43e1039028100c1d0303400191445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 76167888 1250 76166638 76166663
    0x1209050a080f0c030a0f0206090d0519050c0f0a02010807110703030e0d020312090103060f03051207051005040b220b0a0509030c0106090f061a0307050d02041d0615040b07020402090d 80
    0x950406c8981005180c2e80e800c84009035039803220b05855508644ae0b070300c00702e00c0900c203103222170007980c0070451111043c0c40c01904003080c4091603403810380003100c55946034101244000a650303110800c190b0102803401d100b1409845428800d81c1c41c0d51a200113400c00c0f5902c1e0207440e03950740707030524140f0254008046900c09078501c09604102d0740807102e42ca01191400c18000303200120103002500310382d0407001130099800c1107241c110141e030080504613400d008008600c0c40504551181c64000e038021200e051591400c0340c0a001c51404401c10780946035103110544000401070010141d00200c0a080801d05440705101e03603146000e83d4444d0141542040306c08680041c0550011064012580080c0100c40e515003143c0340c0310400c0440010049420800110740034020303801400c0e90b041e000c50040c81c1581d224041d003418807004008401c0341780c002c404e000d02481c0c507461225140808058540c6080d1614442c00c0310b03403003000c500a01854001c10b1522560792190655030a05401c2030090510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 76169138 1250 76167888 76167907
    0x907030e010b01020706050909070507020603040818090c031807090905100b060f1905070803090309120705010219020604030c06091706070e091003080a0f1209050a080f0c03 76
    0x1030050300c440c4100662904200b10101d41c40002e1131011610603480b5903140054860034842e12900091005085c017504000c1c9100588401c2c000b50300c1540507107020780c0c0f035001c4280e01100c10100f104143d445030610409002c0c40703004071002ca80c2c0041c0385503190442171905607503c0e406d150490380140402c40c80c0100c1802400008030f96a10640c00031a810407108001c1010480e043c025408922035803d010300c41c03030140c1d1610b414060843c10060038141e040c105103656820807036204403046481034001081050b09400c121526019011401d80075103204d504090001f07644110300006001180361800b211800c0d501c4400448002d180c001c06a04c203e00e0300c0c0c0001600301102d52207007490720250f2910f42104000046031050280700350741d5501c0c0d05400b00d00c040040717414014206600454854a0000004034002d0050084912544032110b5404203501c015007100340c3c25500e007031410b00741142c0000040010807a15440c9a02001c1c050300e440580c1117500380e5004113401001c1d02e1000181e003c2c01d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 76170388 1250 76169138 76169141
    0x4200d050105060c060f13170c0d090302090c07060b0405010906080607110607030e0118051605030f0705100504080d08040b070e150f0f13050312040b0a0509010e090703 74
    0x602616060040c4141d03641e450510566100306540f04100e40c03c1036012407400640301c0e44c1540c000c000c2010400109000b03465100605080c05265a19070100054012480b40e00380809149506141460f000c168910740100300e030a80024219010340000051b96000c0003441e07404040d007007070040e00400c6151b848045d05002042180503040c0343d4070801c000208268414411403010724068030242c4501e88940d401500074095200c044440c43d5250104261703070010344240004814041c0c1c004049002c1c2e2048544401070140c3c020501a400c1142c80d803a085a0003e112411142c2c29541c40281340c0707150317004403058010b9802c241010b01070b40e444034500035480000903000d00d0142c25005c2051b1100f00702910700e41076884040390403407012080a0240129000a0240c070150010300501e0a5900040101182e2100450701045040c100041c0700703600301040106400142540310030301e024100381c00c42a4134000c1210b41707000c00c00001030b40c3c55581d203d420328045111004c1d10950050030110300260 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 76171638 1250 76170388 76170397
    0x20714210703030e06031e060109080303040317010602030c0303040803070507020d050105040b070c0201080f0703060819150501050a14130504050604030806031b010507140601030c08010e010203010302010e09060420 94
    0xc3c00120010314030340302464803500300ca0003000185100c80070b100c1112541c4d111410003e02c402d0611050400c00550041c040c00210300c6180300b03941d014607109035841c0c168030640c41a04004119407041c001e004400d40300000320303500650000c1031a500c070759503224226041d104584000350840c40384030404081050540050307001d00e1103200e08400903a21b2030402c4816412110703000c2d001503188004507281d00c075039010594120f0780034540841c41d55140c0b0002450f04884100310590383d0f001c8400901403002c08540c10300845030540c001c0c02254503140001b500d00c501d500417000109004504900d80da03a0703076102c01c0078448020000303105d0380c0f40c0341c244280c80b00d5040750194049141900080e000d4038021503d06400d007031370040c0c4c00320110a8401140e180d04200400c85004c0c1451028010380d440c1000100c0c02540324000604405043c82a280e09440c800e07a0084400c0c2e00510061005230b0f00009207a900240c25640b010311036441c078000a02a040892641c1240807820800c003601812640c000c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 76172888 1250 76171638 76171643
    0x150213030503031605031e0703090204180201020c09010b040b0a0318080315090424060302040608030910030b030c0607110409060506040c020a080d0902151c0608010903020714210703 80
    0x2c1c2030b0604c0e00070064682d880b040ba00c03000c8885048144030365022070014410b410102d0b900d4001119001a80071404a031810340445c400b101074044514119230f1b04004202500400361103036051940b510b03014081c80d0149018138598501c001c500c41d41d10b00c0c82503100c034110000e1a0448814003840d42402102544282d0300d0941c202a00c50052032182804910b09003d26444640c00c5428501c54404402c0001c050f403965420b15141e500000c0569540d0041002816110000d075035a144250200480000180c1403c02450704207074849081d6a408680c210010b00c080e200c903983d601c0e0030302d449807408030308104580e402031500941390306000003540070341e114a01c251400c01400341003290a80e070740d0103226170082000b001001040c07240041c030303040f058100d4070242154681c0750014980283d560803098031040c80007166101005061a40d005031002407040324001c005240064400a444103001d0050741d41c181d002070900d0030562901402d03035400c4061303d60440c854210704580300da290880b601c0305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 76174138 1250 76172888 76172911
    0xf010506070b010501030203130c090b0906010c120c02013f151202060f0309010e07060c050a170409060609080c0f01080a05070c06020c030d110c070315021303050303 73
    0x81280e04041040703504807600705151107010703860000114041c0d4001044602c110404100a8000030140022100580140748011611203401d90600400c0d0703000400f41410000c1710b00c0720358003285400442d080703000298608200454080d00041e6900030f5441d0202200740a1031641d13684083e070607a081c01070341c81c034060300250800e000a01042900c0d4910701f03d44c0c0046a0050170003140c03125902c072812052002e801e0b281030103508500080c8940044458a105035160311120b0507000e800e2011102130076507410500c6101200d91070b450350315030304410001c080c0a002e001a051840070758041d60b0040c02842e409010480d107583c0c1c0200040d03050f219210301842441130b02502c614220742c1007a6200c40c1a502d41100ba603914902e1009020040d103040c1c01d011081c0301000104002d0b000030411241654002c640e20101003082c2c10890384840b41072404d801061000141c40c01001c5103441c2140d0b00f00302012040030300e46040a00911581810080d0032260500002c1003000101c0a544106079039413a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 76175388 1250 76174138 76174141
    0x11506050a020c0f040902030a08040920040902030a09050105070507020109090204062102040302191706060609120f0d18140a0302361005010e0a05010c080f03040b0f 73
    0x24151001d00a55049101507040701c402500d203401d00c107035040449200108082101051a00824101942c0c800309480305070000406000c54411030180028106d4408c4420405000300c0303501070654042c43c020100803d03000408a0b0400c84c40e500001c0c0c0b41740e0014002c004901380720b80040c1840e0b000440484c081f508005002a529486109580445003640c4a140e4042e0b0141881d0813034614070040b20088540c2840044050707119140786c9803542012185260155042c2000050b0010580d54440c00d00d0740008100840764a609040d0742012600751441014503000041d1070303003810072407540c1c11024032808900706049980940407600140007201c207403d007192214030940010100030809034020001000030401800c220000c80b550030341c10381102194651550354a0960100e11440d03940701c0d410351041c00801d03621000d114006010900f403030340304505418046600c40030648111414042d803150060180064801110a1070100104aa580345030600d020080290140ca6007510f0900490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 76176638 1250 76175388 76175399
    0x240b04060e0423012c1503031201060801061407030c020913060207050105060a080f060103020918030a030608010c1809020a1e02032119110c030f090f01031407141b0115 74
    0x7029805c040120030726200040daa2041c925980705204448182c040c4810004107500070552030304607018154aa480e080706500d00080200000241904245480000c00820380004c0c0c2000040c800c0350f5050318041c1702d42d50307040356407a141300c1898406015503000080b50810003d06600041c8140000c0320092403040e1508212540c42452003207c0301943d00020041c80549090306015900c0f11010100c1c40303000f12203080a5055400c0b0000321000300c2c0e241c04003800f59034401c2c0618600c00800f450403142c400001207816802d466581700b100f50a40e400925200c03058802c010315002d550800680c0300c601401080025a254441d0b09081d5008102c82c0110403010500b19406005140c810100785c049014155440020301c034441d541c500c0650708000c1c0004045050000e40907600b2600030b09500c1c2e451010a20144240700002ca90400d031905031034072000560f0851042d005100380c03800c0050740240c0c403030ba1407940c42885c018401c04541c0404098080e5815002020400e0484145202e030680c2c070f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 76177888 1250 76176638 76176689
    0xa0e100f0b0604090b0901142b20030105221509020a0f080105060d030c021009051f0806100203070f050705090a06151d0123030a240b04060e042301 65
    0x23000140d0084103d2508841c2c41548202c00000030728107038071080012015542d0169603250f1a052024010365418200355510b0207201c1c0fa54446c800d0105101800c00d034008440240c0350074500148000c10604c03010f410401c0551180750829805000c645035a91507040100c0511941c2c81102c400d90b003000d00084960800410300201c0982c15100c01080286560030070880502c4402000104904008002110b544a40c21520600207d01e4940100180801d00030403141d001401903020f6004151041903550340081100ea4468020350070000700703c101e28105080909542c040ea42c003200540622039560500d40c0044101c4200c0460121507c03d4440c1c1a90981481c500060740a442e110200503030303500030000800388406540b500c1d02c80030040c841c4251550010303543d00d11119690211101e0504400601d443c0881d032600414103140e1030a076103480c451150f4002c10040080b21000200c064031039410042c9c60350740c16580300c0341940c1d403840984540c200900c162490b01014011019296500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 76179138 1250 76177888 76177919
    0x302120f030f0d1b030509010b01080114010809030c030c011b030b0a0302120a020d0606030b1807030303200a0e0a09090203060105040c0e0a060806090a0e100f0b0604090b0901 77
    0x404061070410400b46034050481d045055100f04850b101d0341c2c043e40200e5025681c492507031081d100010582031598182d4212225068005c1c18400d041005100c09200c81400c519022000d18250040d9565052507e04602900c103c182d414030000c600361200f518190844a600754442c0204607203540c46120441c183c07181a1581c1e0382281d04450300f03102504150b500d20103200c241c0b100710b6040b46610307070205901c07080c0300206840b510f90700c02041c02040344049805030002c1d5603052010684990249950b151030040c4002818103580d9039071194200340c04910f00706051400f408040c0c0b12082c41201800310300f121680688200c0c1d40420205a840d000d1042040e05078020300200324982c01c0c181400000d01000da54030043c0000d500c61084242d40744010100504040c0da5007503620309010017800048800038003804031460411403114042c840000320341d00282007107000800c1e030455518910f002080c20304a0b098006000007004104005281c1100ca400c42c0c040e940b412030743c0c0c3c0c0c48191005e25200c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 76180388 1250 76179138 76179163
    0x1021006060e0d0602130306020301050301060609050306070807180605120a0c09140307030804180506030d0503041b090608031c0c0503011a0f030709030302010e0d21110f04030212 79
    0x9021025032003c0c14185062046680300301e2005162040d412038040001c2da5a41c021102c058002006001c0c0d03007402c1c011800100030604081c05064242000243c8404ac018080010030079107a001920b014404d04074198a62010707840007503203075144c1d03d000704150710008440222141d02400b0604240d42842507421030a425921001d420381490b102407500b41c00415115490f200d007246c08008210740d40010801060a0304001501c0d000d0760950006907000100258825005500c2e4040032079040021658055800b00c940b840c1c807402d0840c0d00600402a40012150514001000c07030900070010042600f400c6103035484010100c403072284026039490041c52800603a0a1004100846241500c003001c40c4c200300280e4200010250440e00c603810031990940001e034508001c0051540a20a410102085901801441c500444007524401c0092244031415101d618805075600c12944842d80f51100c2e804410341e29400d4100785800e640040c0002c0c0e201d1419111664900f0350001001142c1c0d070b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 76181638 1250 76180388 76180397
    0x601060504170f0105070306080633060706090309060e031c050a26010e13050a03201e0c01170a050406060506160303110a020c0634020102100606 64
    0x5040c1600b2104040c0b08900c000501d2149030f80c900b0203204280100e610402c100d0b940020720300e15100c02c061900710302070001485e030300002822610760000001117050400460905200c0c40f0302132000b06010b48100c0101914080c07a110030300c020940c0c48102c0b030003100c1c5180c2da01260903810a0825031214054082140325000003503000c818640a4405442c000a450905004920803503001d48542010313407580103141000c02c00184403622070340109a400048071186a64600c080c0d0b51000e503100013484000c2c0511100e001181c428980110701508100c0d40d54080d1000d8140800131041e0b2034a501c4201c0410340200340440016500c0b40d00098502c000820200c0700741e4458501d180000c02c00a801515034580b07400380440c3d0717a16024000d00e03020341c41403a0b0b100225600e0038003c040362040900400102c0702046041e4207180d000031040e80200003110a29030303549020210804196442c0074266007211500150300740d501e52410150644c50007a000d6542000c40804040b0456445c1e000303100110313 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 76182888 1250 76181638 76181647
    0xb060a08010c0804060b01020114040501091527050c0a0f03050c06090108070c020102030d020c03090a050109120204021b0d1706090112030807180909050c04180318090614010201050906010605 84
    0x5885d80c20080307014006000010b07000850070380743c101300002101c0c240c41c5607444044090422403000c2c1c2c0c0110882110000700101e214449004002c01c03550042030458030f082c25004400d0180511000e10a600300a01c8405159a0313a00040d0001145200076202402003135076464107410881c00725000400141d58004017a81c0c4d45030185c0c1c008404510a034118442449040040c1d081c40c4001c1c0941c8030080700468965005200f0007082c160250003090400240001c1084042d1280205070051541190b0141c0c45162007191115582c02091001e45180702351b0520f0010650404000d45007072503000200d42155481006100c08501c0030f00c501445a041201060003203441880341c10b8101c3c000d4500403410504106503010030042d907800c5095015550410081005003c002040703001206075000c6c80008c644041c0004406002880502401043c6185240e40703c0003070101d8001c0d02481400f0043c2c80c2c1c648121607811084180154055032038800881d804540000b41e160407918540d44181c9030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 76184138 1250 76182888 76182893
    0x1b09091802060a03060803030403050702030f0a02090a0b01110304030c0302030727111306091d15011b060e03030403090e06090c0901122f0408030d09030e0d0b060a08010c0804 77
    0x50340f101804004040da10340011403107140610082d0f020310b01941e40c0310385604990041500f001c104885e800c01307690000c084100180ca8505d43c6039405965150009000700c17455006a90b100081256603005001c009000300c108400f1154107803e40c0d00941c1254112920703038111360140000f00704031000040b080400001c904c24540c00280318030700741516403810712842307001e12020310083e5003026001c05d460070024401219503109040e0300f540c400d07069042174100f18141502c0702500c282d0060401414081550808054611801c001640084108441994008940e40300c1d00107580450005d9607504000505400c1201020701441e002000c041d2507440b2079907010100d60210500a051001007461191003040c1441008184100c0c50021401c680c1f5500b11100340c41c3c000010035983d00001c2c4000c0c0106c1000105988505444a01c0010b51501070309080d2071201c2c404d030748258084020040d500400c401c146107680203150541d20b00c50040c0e1591078072800d03984000c03e00c0c00050980d40000b0003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 76185388 1250 76184138 76184149
    0x3030a090b0d020d140109050a02180405040212030705010c030b0d02010f080601030f0608060103140105071403070c080a030c030b060301080307030806130c021c030902010e09090c041b09091802 85
    0x19001042c2c40040c50100e0411124040c2c581071400d80b100c003058540100403040440c0141075020b00800400c43c542048030038862034000071985458001c0b50b6400004045413621451101d0740101c02c400c81c1c0c5c071100c40e8501a4045d000070001400080e040c60b102031000d04001e01e41c40c070350960507128503e10400c0c0210480f800c130b1004141c24105500e6400e1094495114031403840034081d220007800056055003400d860061407407480c02060ba1400041180069000046442408404001c0783d40c80e1a03210003140c01c0c610343e6801402040b0000b404600c5c00b0381552001c402210513884c01c2c0003480c158020400e181c0004d1040014a40080201c1c000003403088184c80d41c0114000c020345411003812031008211041c5a0b03460340942d1015451005032100c1c485080c52228091070305004589103507000900010b20b4840580c040c2c900b9501003060003809101c018652140a4020059207007070307401500d43c1980e0081080c0200b0b044070004910044030740215051282e07060f1a84071484601e501703001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 76186638 1250 76185388 76185397
    0x603020c070519050103060506090904030c050312130b0703060308090d03050f12010f080102070f0b0604090210051308010b030307020f0105160c03020a0602061b0307021203042003030a090b 83
    0x1009000d5041c000ca9907070754100d0306444402d2003220080c82641020009400c840154001c1481810140304000d8555181810b00341e005a00d450804c51041d45845e00034594042c58144028915078201084181c4c0020060701e000d860148120740c0721501d0744d1000358104c850b180006804100c080205480609041c0e0f10940c0161091070300701e141c502e00501500391908a04102d031001094100100041d150440c00e200203803600c0d1000f186812e0a955600c01d0201400e18002e0003109010b002504a560725407021b522150040c107101002c3c4000752008002d03074020541409800e040303000200d40c0f11030500c01e103203507100080e004501c2c21101d602000410103a41e541281044000c01c4140c0c580314070720041c05e07030880c4207070f00e4052035600794410001d49000740e1b0004407c550204040000200031081507000143e11120700c0ca07640e465580f400c03411704c4850107541c55003034800002d00040001d81e130700149030105041102040c1d10026401c05071207104807580c440029600c61000d210450452000f80f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 76187888 1250 76186638 76186657
    0x120b16020a2a08010b0a0512030316140313050f010902010212130314010f06090c020a02040f02161506121208091603060b1e01140708070b04080a0e0a03020901060302 73
    0x40800d20079060302400d1030020b079040005665115003910030b031818900c1d803803000b40c0300446542041804050b42a0754a001c010009007948000d030315000d82c080c0c050000d034a0f5524602203010355915210342d002c028000500c10441d40c41c400d004a011300100d0600c01c070a02140e0503070160842c80c000c0210380c0d83d02e4000e0303a0404410f44511400000003216051302c00d08244142c800401c1107844100c0c0c00c0300302c440a80c00041040d0810b510040d0650340814422401641150700040d4005d40361161b00c0203020b03603070303241d929403030a2030b219420300910345e402c00a40400b10b5801e00c002078440c51500c07070f0501c0c0060b008042e00c00c040201c00100d80184201e80d0301c00340c1481100c0c519100d50076203a008004da0740c41940e125a603070503d0a0141095401034013a9450300403490361030545000020103e48556008402119022500c50f00300000c036012680c160360450f4a9a240c0d003050b051803051544400158000300e0027041d00441e09007003210801085a400404009250780381800550182d480701451 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 76189138 1250 76187888 76187933
    0xf091508150a08060106020f1612140105010b04030c090b0f010f0e030d0e040510050913030203070c0f080f060408070206030403110f0d02010e0f0c01180e01120b16020a 74
    0x1488649800c42030b8002480302e0401030000b5450201c0c068105080c0e56035204040d0841c01001c1c0d8860082e14042e400c403500403074041504441c50424241e1006082c0f2502d4465007454000250740b040349014000f900d025014154091f41d40b95858411188019101e07604012080c80215040d80070b894441c0321141103041c104141081030000a0030300b0b042c002200c0c042002161402c43c68102071150030340c00054010b542d841c1034240800a100c2c15002011060f690007a4a2203908141c8280180c81d41c05034054031b2514441e48540b11035032451041d02400e01a48219021001848000150240900d03008201145003101c141c090060036840280107805100000c28441c45014003040310300c039100719440140000c010020002802c0d0f0f290225007110b01c3d0322038141d0b80c402810100368692030f0309003400c1207a135440b0342c0c000c0185240e2040e404000b000b9860000000c00641841c0c4c1c1078011403003030450b410b10360765407002054545084152000140c0c40307000c2080000d0b041e041d2004200c0a121003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 76190388 1250 76189138 76189171
    0xf09020f041812051b0c0102061b070813030501150e0c0708040e160e010908030306040e010615030e010c0f0507021207090c020f01050c03091c030f09060c0f091508 72
    0x464143e0f46240c003220070002400042c4c055a2040d9101d00020000074200107001c41d030010000003545c0b10806010040c0d10f49081490b5074083c5203070310480b851f01d9030000389151a04002281414044240e00c000d032180d500380300d0702180e0202145031070001d83d49078503c000001c0d221004030803629080270b1001c40320010100b101103000b01d41a40c0e20703071092201180c2c80e080200f030404020a00210a2465814000a01c10900079090044252030f0701500656000606494003c50306d0701600440d400041d039440c04000400a0701e0b4141c108612840780349000303000d0301025180c00c0343c5000d0403038151800204140003180052030441c2c0c2d10700c0700c210039104995070702d501c91074003e044a200d0b84107040503034001e030314544c42c251083c094a940b10410f00b01d030608501e0003025a90300e6040e2050501451003045103002040c9000f5446080602c0340044200900541844d00600800c0c801130740c0800301c1c0e000c25403002c50724481d90040064a46103a0000d074200c541900a0f25540800f4041070205e0b515280e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 76191638 1250 76190388 76190393
    0x250206120c090111190b130c030b011a1804150801020d02040311030d050a0f1e08240a050402070602120f0106080f060603150d0507060201020a030f09020f0418 70
    0x306a4050458480c00c565200e00780300014200f50510424510240c0161404054400300758242c1d90380f464014410911342d654100c49441c040902400050418030034400100034411000d1000703060350b0340c05402402c00c0354000384e01201d80c05880705a2007000c0c02015001c00f17174201600b001c1c401891000c0392501042e140c50a075402d90b0080785260701101d40c046010000d0010142d01508074000c146c001c1e1204e494082001019481141c030148103210142104250381442452441100030035015400807210800ca00104481425500e01813076282c0c59030b000d5000700466242403180ca1009004a02182ca0704d801d00c0042c0d0451441900c0c900e1342848074134003002c9044c500798412110040700701c01c2036040038006020307840042d0a0182c5406c00c4001c2011640742c000c03c903500f04546c210300414002e0710000080c100510302200800c14004c3e02c2002500a0b0150080c0c0203d28041c1c5040c070047c40320000300d40c01c4820144001e0742c00000c4106411881c2000d500c0300010a40501b920a01082c458 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 76192888 1250 76191638 76191667
    0x705030706050c0a0306050a0e01030303050603070e04050a110108090a03080a14010f06090b0f0904050408040915140d0f060e0a0c0e0601021002090d2307080106051302250206 77
    0x1c4034003c200b11000594214016818854040a010101c40040c80c00c1c2c11300f440501d0707017641408014189551031001ca10940c2d0100300c420001d000703a4004080c11320302031400507110000307041d04031030141109901c450258040c400c054407842c0c000c1c005024000d0562421600c6202c0035001b05195035484030400c0e05098200c1f120741c0030303001419104980600d00440108203080a90110043c0001440924030241a4004031080c1da40200e0f4042529103803410310301c115204641c4038180c1c042c030b0014803e5405901001038021600d1030a510030070282c116041c08044940200002e0610300c200341c0500005072144d0020314000c450404440300344140d80e4445d1710103c1d4a800c44040e124184081001c10340c1e040190740e000418515007541400900302c0805d1000a54104c0208121072410b0321442c1038480a0008000d11441004c54030b00a0f0f80340746490081075036010b81c502071402c800051141c0d42290003140c90003076194201480403d80e0b98000195600004022640710b03108100f1045042c451 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 76194138 1250 76192888 76192891
    0x402010f180b03061002071802281d090114060c0c0a0b0d0b01030603080f03041b090911040903020a02150d02030711011803020304181e060602120903060705070503070605 75
    0x2491403a0350f69040c650200325000040c1070503074045510aa00c24040044c0b081c0380322001c00c01c03081026072200a40301808888614807030b072941e0004032100014280365481030750100300c0f840103081900640798010612030014030074082c0002c0000080308644207401c0500041001416840c15201d0007001030340080c03035650580e40f08a08200000c503c1003030715034840c0304207580d11609084c2080200d1446c0e48030112401050718400300d210003c00081c0900c01e4404d007a115111083d180400880d880344d501c4002014003560035600070741019864101e500b80392084901440d0580c00034507440b980d0350f0030404290355030b000e551002744080c0120f035a407403003e002441c020101d80d01c40c0c24025815100480c2103445000a81041100540001c400f01303402100f100d00b980c80e090b0040c0316400b0941d80341009004c80d01c11000065a02114110b8038445661001c4107403a40c9609660290070488001c090380c1c0111a90f25a140d08650042010300340240300031301c0e8040c405c3e81a40c0c00c24606880d10012200c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 76195388 1250 76194138 76194149
    0xf051605030f090a0602010c0f031a0904120f0201110d05190908091c0b0c090303040b070507030506071d01030902122401050402040e06131e0c1701060203030402010f18 74
    0x40c0403600c3c0c8510326012902e0400342800e0710080042d41c000308030050004162194100c18941e90f41c010000d10444071200c1c0070091000b601c81c0408e070429180c05c00c104003031220f01c00d001032503a011440000d841030040c1c00c14803250760500760600c04402000e2008110240080a01c00c40c03104184d0040142c5000340c03032403140160040b40c1c4606041c0e085c0b140d42c0d01500d00c40600c4954003502c1030006a00c02c4030807078200441903d1242ca414000c5d011a1951207103810002da841404a1a041004400183d450030b60f0300c65010b9503010f0311103090940e060482c0403092640b00038810000d401c0743d48654030101c000c5000400e2035903200e10550240d07003001050386d00d19240001c015080c2040c160b411003581d004080c20f441c11803420b440d10420380300340d00005d0480c6210b004000d0303101002c80c20b80d40005543c0c1580c00c804400d60100e5004400050030b001e41e07100080341c0e000440440540d80703403105904a803800d0b00654a036543d580d00444000c00041d0b50081481aa18194100b00062010a801a20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 76196638 1250 76195388 76195417
    0x100504020a05090f070e0411040b070c08030f070f02010504050d061406010806180402060409050106050301060318030906030203100801050a0207050c060304050a03120e010203070507150902010f05160503 89
    0x40a0041c403400400765004540500420400d020a008505021950100b414a0844600084100054041c040c00001c8034080030010501042d0216084000c1942e5841120b000481c190703100100e030303128054415032661030701040c0001404035004580c2001e6203881454140d240640380d10029111894800040d10f825a880f0480c0c2c068034010a04a6000742007402d01c5800c5d0b10b0444000b41c004a40300072051840c10360761020030210b40742c44003914060800300a0900203581c40316801030403504240b0074140081e0030181e07001350184c04100c141109903003560310703034070f1040c100130b805c0e00a503101030080e10b07440c514084005811a020b11032640111103441d400b42e83d4202c0c40c1801840c200761040a24400d10741042480300049000801410b0103601d4100720140e1380103030707480704005c03d0083e540d2401940004100310046da0701000031310045110f405d040b101510305150705011100d40140081c0810743c0c0c0d180c0c81c6400d80c050000b6100380f041c0a000701590f6642ca1341d4503811354000d004000840c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 76197888 1250 76196638 76196641
    0x608031306031802090c0a140d05041b0f1a070f0501020d060b0306060406030c0203070b1e0901020a0e09060406080f060a0b180103020d2109090c0e06030105040e0a051005 75
    0x560b040c09445005007441c041440324860701d80019100f1a000b4006d4810050f00180d0030100d41d008078466030107107003c4251652140303000810710014100841c0c0448024161111020749540c0c84441041652005031038001164180403130f0a540f03c40100128605000c248140d000080242c2c0c0700b000698072483c00562a90700c0003000b0030a8610a030001c414400007801005015100c14040c0c0302106c0703035132801043c180704d880e07801e9003184a003410240088802d030b002c00801d04010030b4110007441e44070041e40e0844d40c0b0000034500b00d00807811207900088042d0303109811403070560185604600c000b0b00000c1c00a80c0c800e686171400e440b48040e100c15421040c1080300c1070f8031610078001c880005035030301c3c5115468080e000031200c605001c0244508494140743c0c09002d00b0140a0604490426004018402113940a01842d41612401640a04005210045501ca825640422840a00740034210b0b4201403c00c40500a600c841100c50321a050003400420700400000300c1455203201c00182c903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 76199138 1250 76197888 76197899
    0x30e10060906080a020f100516112d010f020f0703050c03060c070203070e040f020904050c030105090304080703030809030d15030c14210109022205060f060405060d06080313 76
    0x2607a8440d80440c107030390130045600c00542c84156110307a0505080340d0340240f000100070141e4150003950305680d185c036a05c0c41054100040c482680196880880e0f08021450284099040100d01d04480122000c2015170211b502e5004410b81142d214060050700c01c105009a40d03249000300c20b1f841030b40c440c0d02c04403240c45541818800242c024000404151400d0031940100f50f42d0341440c0304142907128a480000c0501c440c11900070b880d56402000786140381800c0c2410341c0d036501c01c441c580703210b54640008144204000000c0b00c0440311624080d048143c078685055440020061000885000801102c424098240709281c507901054008540841c2141803040c803c0e100343d080840d04a215501040c02c5a0325244000c00040c001801e4641c00481850002e02400145000079000741c202d04620b1000c02404010b0020490b0301481041503699800030080c3d90303280b0880b0300b500580100020300c400d06180c0c0c01441000700007180450103542e02c07607041d40b96a120380c820950354040084107110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 76200388 1250 76199138 76199141
    0x50906060f0c0f010509070911090120010204120606050f090108071202190909170a05180f0a030507060e0f0604030809060c07030c1703190e1201060f080118050a0b0601030e100609 79
    0x105a40b0807464103084c01c02b08400a8a03c407100324001040f40301016030305103592000d4040b60f018010303084143c80820801d1404030007400305401114807608021080941a05003e100c29040750031000091805610300072035565031504942040c0d820842914000c0756030702d16813240700700802000000041040c8035003041003245142c085480034084080189191080d8042e0a07586a400d1035504011440c1c0001c001802082c00c00c10000e4126401860004c144080444d000742194259142c0d8800c2203100c030100031124401840240d4840740070707c41403012404540250007081030140000d8986101c0c41b1255151a649900c102e030003805601043c0031105110842c15080f0404000650070008032002d20010310b03840201c1c400c200209070f540348071f159036001c03072140b0703140c100030000c01c025030b1207920200c4084d0060150101a45c20aa10640b843c000465404030003074022004e0815000c01b5915454013240c05080c2604040e1502003650301c105040c4001c0e41c0842440f400015018507280700f800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 76201638 1250 76200388 76200401
    0x603110a060c080a1805040f050105100207081b04060302030613020312090f0907120f02210405030a03020c120417070f0513050912130906050906060f0c0f0105090709 73
    0x80801c42c540101d10b000903024010398450004c1801d04280c0d602d40c0c80a401c101c01c0345540002e90081c01c000325032021a507182d0105050356400d4502e481c1c19080034100b80d07510f4145200c1c0c64079551266002410780d11b42e255038807414050040020941c0c554a80009141c44002e42e513043c0c4440b00c0307605510851070b04224401105221402490030705620702c1c0001c9a80101e162000c0c040e224000c0082c2110748100c0c2c00d0103601c0040142003181a030142a900002c0d045092003104070001c00c250707881c06011021100e0b01c110350082c02140340520000b0210065081000700a490344546220744103030f40580300240c0040c02ca24800c011400040c620303950329007502680a0f221011501805102d103885501c588403202c4150310000c141a01e890b0620b91506540600580c95007102069201000c0c160303610700400c0b1340d10100d061011503116020840045001c2e1031481c0d100d4070030032904110315404009071860007451700a90744090b0729800040c0c21340e20200c0b1603590a4100b1803050000504521510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 76202888 1250 76201638 76201649
    0xa1d06070f090e04080309010e010c030e0609030310260a030518040c0e0418050708030717090306060409210503060a0b0403170c0703080409020a090e0402010c0201110307060603110a 80
    0x1010040d162400d243d4855070058005044100004000f41c1d05010035040848a10444402041a144803500003001429200c46140322070040c600418407848001040e01d0050440104501c030261a165502c1c40094050b000c403013590f00a040340c01290350090001001150080c0c40d40c81c1d07991407004a0107104a811900340e0310803854104000d1000d540152035651080c41034400080004200080004880040710003d040340b041c40300c0400c00440200c0504803171445860582515114980300342e51500482c012240c2551140300003503058030389500041c0d4181d004d2185501d01b401c4000645241c685c50458440126130000184800b074241404200c00806085400d03038181801e6070344140203040301030400c44080a0100e40707489003803010703c0345500031688500c01ba40d986070341d141000d004e900801d20300c501042e800c074000590038414a0210303106541c16500e0b4a45004a40d0040d5440c000e0003c444000e4031040c08600300041c0c1030f10480001c1d500070414603190340342181c1000b01c10f039120b8000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 76204138 1250 76202888 76202897
    0x603060f06240a11010912030b060c0102030a06170601080a0f0f150c090f0302030705041d07030f06060504050f070c0602090d060609050a02090d060b04020702041109040c090b040b030a1d06070f 85
    0x50070046540482c0fa91f002540d00e18012414814100c005003040c092900401c045500c000f0910100410a90040040312401060b280a0baa41c0c182c2c11074981074240301f50101e0b90815003005000601880d0310620103440f075809001400307a140c803004c2c07901d2440310781d050344140c0d1030412854150300026500010240c00c503080040d2421580404e85030107491040a0040d5194200050000040a4402003110440e02165a155500d08108499100782a800e80e8003524285010400b030030107000b0603100310710102010140e0744905034103e03042c96048500b40c802ca030303090182c8405079440c41e00009245029540c0420b0407400c0120250480d480900100c03c2180b040140d040d250301c0d0785000183c05504180001403106600012a01078400c1030b0b002540710717162090709100d900e0084050316140390240c44c204011440344c541500c5031500c4d8014190b205505000422043d44402d0045a000c058100042401180e4100d4219410700c030203255041a0005000c001040da0b000146550407621441c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 76205388 1250 76204138 76204151
    0x31306090f1119090b06040e0f0a0f0506010c030e01020f0607050d0e0f07170a1e15050105031c0e1002061b03040c05010302072a060f080603060f06240a1101 69
    0x10f000c50004030f10070b00790900d45a4041245681e0b4010035103008014011a5100c245002d42140300c116008607a80d034503442c074000ca20202c036038482c1b181d2445003d0603142e4410104060310181c52070702e104010681140700d8580340c0d0322070030414041c190052019480c1c00d0344500c41081c5403030984074035040701d00896205c0460b000c0724010004d41d004c1140c64035680581e950781a00380e41c5052140d6202c0207003510765080011955030300c2070124408014001e08806c0601d0954403d0380301950390a110b02a40f43e4081d020203034880d800391401c00d1010840d401c5c04041d00c400701000ca841c405c600e10b0340b4030240e0405010000401c0900c42104124000e0181040c81e44c6410f5135450200319035801000c1c10140e0201d504001c00c61002e1810001c10720406d11030626070b071448925848034949004120020300e00d001c4118269025448040c00b03000c004000d840d560b520f078071414501540092102d0741c03102042410440d20708501c1c80b048129901010b100b07568041c1803002030310101c0d0100c520042a8074042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 76206638 1250 76205388 76205419
    0x5030105101d09190203010f0306060b030403200c0307080a110306010e0403050304080903031602040606021b090402181305060f190e0102040f06080109050a02040b030c031306090f11 80
    0x41e801c00701181c210340489107901c4100f4903840c00404d1a40f8500c0c524400000030540c82d0442403c00708592103603906004043d00c1c1e01400013140001d44000b000f25079020f404203040b17880385d1911800c0d041e1203801c0307030b071203056501c0000e00e840c60907070250780c0d11307005404001c080c0300c154400c200c5450b60a4004080552418850340068000100701604208004c404034082007251412034001d20001011284c0f9920b801a1031010230300507507812407156141c040c0020780140042101010320a40c46c4045c000344003440305124000314003e004981c04190205501c0d40c05408056440c00344010300f59440d2880c4a81c0f800519103140070707281c01d205100c0301040104c165492440c04000083c03411300071501d031404083c51406406150060050303000080004070340543e00c004090304840d0b50000c140031a03100d10003204101c1c415802251540041000081c0304218502c0c01103421000840942844a103075480c2c0c80d0440b18527150480c1c4d00e41542030710b03006014001507040102001150203842804030003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 76207888 1250 76206638 76206677
    0x30201080a0c0509090f0f0a060b0a050f0c0d120b0402030f0a0f0902060a0c03080c04050604030308090a02040510060305250f020304050904060e0d0509010503010302090411030d0503010510 83
    0x200782121142c2c035241d000922510990965094000c040c0544040d0b0400010201c44244221071065510050000042440c44140a100103d92018180324a00180f074041104e40d40d0000000c040100c104118000054408214200d80307c000750b924140c0390929100c15400780d900b03d1242038403070740c0140309000c41d00002011068220704141c02c00508140d5140c0031001803c0ca140e406588034802141c1240038640240444103043d101799590101e50b614585080c403030b03010f1801115003001c0203110a20000340500c207616081243c3d03108844140400c0e9002605803807040300d00d038080a9170010204000c0341c25001e101d41050705803580c07400c25101507288100303400c9400300381c0040203201142011582d0080c01202e02425001c0c1018000707207803130b0a0000c040c00100006030442d01c00c01034070b034034124411019070f03a034800140d50316442d6034a15020003a00c01d40c05003003a200c401c8000c2d141c400d82d075406c1202c2d14100d42680c481c0e40c0c8962600081015000398202d8240074060b504600b40c4030302011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 76209138 1250 76207888 76207891
    0x90d020f031b0115030b16020601030f020909160602030721080f1302120105091c02030f0a12020a0806030d03060f0e07201b0a0e06041109061201031b03020108 70
    0x68420000000b140b88500703501400410340c00080c40040b210303012080c401110801e520030913001c1440c6c2c20902c542c070f03000c0f81c0d9074509101c040c118040c80300c6101c00500e8410b84550704444070310704607816480c003959030402c1e41c8803ea00090143c1e00008041e03080000c0b040c648410745c007828415041824200300041c0c2441f400603d101c051419100025240061a16120f165560040c0084050200f100640d600a01d02070319190002d110340c00c1a030201441c14800c01d0010900c55003d942400c1c28210440b0554001c012500d0178404020f004c03006004503840505840d13a09540c5500030b6003043d800f410306016208502031304150819105000d6194280d0010081356070300002105a07030340705041111034030748805023a03001e4003501000c480c4000000502000c1500c03c138014000f5030b400e81d400c10950040d588540302816035100001041c0c4c4c6840c0d0301107141410380e40800c916145104001840a42c016001000c06108440045c0180a41031240c1031461005c245416440c81c1140c0010f442c4040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 76210388 1250 76209138 76209157
    0x16020103090302032709011401021009060615021605120d0507051002030c1305040c080a150308040803131a040e1302030105010303080405010b030a110f190608090d020f03 75
    0x100d4180700001c15100b00100da49103840f264100e1200c1c3d00090448030b0241307100a1241c490301c0c0050010407800c240c8041d41d565942d0580007400d003022408215000382044400c240c8065540300d80004030000c507104074018900580e03002e802141c0d5518940a40c0c0503450308854040c0258800c04500f440c0e001030302d2050f000c034509107c1e46072640c1d403a0880c070f42660710b0000004140007006000d560300713800700600380403800c0041c401e945170f86420034007003260740d0f0f0010140000c40710000300380d4480055200c601c440c100942c1c50304000d9140e4071419429481035104100e07551001400000174810050200c0290522480b104000710311b244003403030b41c0c0c0118020690f801e020080411400d40c801545030340d01300d0340903000744102e6a4a0801901d207200444054401c0d5007013403146140340c50003045400c2500d43c414002a00c003907510b01071000a000c80d41c10260842e40401800600788030500603c0b0003800e483c1d4030540d1074603220b40f03603d00784940d8a41510540d800400e0401000e107012099486d00b10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 76211638 1250 76210388 76210391
    0x120f050702070909110409030c050609150a0b0f09040506070306080a08040312020f160f0518070806010201090203010e01090201180b090603040f060c09060818060c030a06030c1d0c16020103 83
    0x413080c2403903034890282d030012a0348a880e100c00780003095003112807080a0307401041650382c1030f030b50995610b0f1a04000d0801c46440864800000c00c448216441842d1050018140c0b02440d141c07200400c01e000010f41d003e446683c03040e070810030740c1545402084003500c00e91000d000c800c01990740b0f0300254007850200414480310080b044046170b02c02c002c18000810104111845068800d0920700a80c41d14056030354805015000441c0e0785c2000c0a4a1446030f0740812010884d80d20b020085030403880240c82141155220466600507a800f401010ba02c00d080c44000103950306244009000c540700c03044112030301c00b052842000324883c0c047c280c8000c00016a046680c903070f210f01d440d4050307404690004280c146444420002c09074040c01810640304039841e0442103032103411020920138a00140d0f42c01da58031400001d40f9000041010316000320008401007221526952144d0110b080c9410001c1c09001140e4081200c0d006404000c0d040003003107550380d181c050106203480f6201c0c5c0c0e501000e410b26 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 76212888 1250 76211638 76211651
    0xb0103060b060a080c090d0f080d0c05091e0102071e080d0804030c030f120504030e09011a09040b120d050d050a0207020a0501050702010c0c1202040b030732040903120f0507020709 79
    0x544071010324000c90f541c00048c2e00c0c40081c1c140b502e24402d410a445060510f8944034044105074021411214840c82c001c1100300640300b5030f0031540d41c4074072561f0f0240c1103004041c00061080f1014244070078001003103202804050401503914542050700e0300c00b608108640090202107074001c1e800c4c4078107d4051034441c1c043c1d0113225083d580d07a0702007a840808286081c2c1048185030b4001013405800301c04070380c18219a42c2e0b50b10704040c1d100c001484800114820840440c8618199002c803e01410182031504400034010303070503007011404442040411030000b80a01c2c2608103108680d840106900c045003042003d4001c1802d001440c004c180c1400000035603a41968000e070100d20542e075200303146001d12500c80588030b403e1100301100f00c0c0140e04000c0c00b011540780100d94442500d01501041c0b2540c1e021840c00d1491042802005120f0014450503100c0d54595008401c0c001e8000d03118065000601480c0c1c10895264450707a00500e4502010b11949603070104600c800c80b5414039012688 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 76214138 1250 76212888 76212907
    0x21306030b0603070c080d02070503161103062509050402040603050115030501230102010b0907200318101101020c0304180504020d03030c050904060e090f070803030406110c0a0b0103060b060a080c 86
    0x2441a01c0012b02a48004510390005051301c04071050340d10322540d055488006050103256480000f90344644010700c160500e1814402d2840c481c2449a49500d40200a9560f50300070900320b0b44140c00800000b6121001801a00c1d54214000544042c80c90300304119032402c03900e0315058041d07170f42c03d0481c1c4d03218000e400344c6c0380c0c800d4000c000c1d0000c0081030030005041c10744005d0282c041c2580d40d6400b5000c8041540c000400100903545007842c18509255051014020040c041c43c440b0140c806000318401d03403900701d0500f44042c0400c0c0180c01e0081d82d5403401c0c40c40ca000000040c10301000d02c01e0170b0004120042e1140e40d03005008a03450f003008201e01d45225030a0b55540240d81145070400c5c075140c2c000860f06100360b8040e01849030748050b29810080010496120246030041d50440d503c10808100041d42071342c0244101c81c0000c44040c144444441a41d00303181401000b655480714138401401030002c41e20520010b141c049462602d88003d040b8041c0401d14000d2038010007007030209a0444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 76215388 1250 76214138 76214141
    0x6040603061a0102011a03060f090a14070501031d1506043c0501050a06050903030d05011509150903020103091a040503070c0e061c030e0301021306030b0603070c080d 73
    0x34580c401070501071a406002e03a55640111081200d0041d0700b084c2031a008001c0995105c100894003401030b000d0780d50741004a164a800c058200c3c00a40b1036a08188042100464031948014119002d402d6040c0b4180004040e582c404011203403040310740800e503101c1345001403210303040c054400c0001c0d01aa10480040c0080119903002c0001061004650040c800007110311001c0744502d100c1c10a001c1d42d8100c3c0c4030100c030424059140c00210405083c04001c0c02080a00044c21b0010101c074541543c050230304007615420b17442140004214419002e81c5d607000005030010b05150803121210503040100184601c44500c40a4185a65401c50100340a01040164402c0d622144843c0960a091a00994039880403006442400c65814080b038201c0650f58444e0144000514000804003800c1001390682440c3c0c500302d0922000ca00c1505898400b0b00240008805203c19005403500e00070001d0143e44090384024842e100420170011400c0d00032103600419604914044d0f10f68000012010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 76216638 1250 76215388 76215401
    0xf2b1803022101050f0103050d05030406021315020f0f0615010203040305010e1e06010302010909020f0d1509061d0c0a050408011406150307020a03050a180308121303050702090604 79
    0x80d001540700c9a48a103100310464a140c1c0c072030b40c40008110507620b010420b0b210481c28040203203a50411041d43c0b01d040d00c00d40145420070b0051070014644452001b1807a10054a13030f01c1800c00d41d09107210350b400250148002d0040ca4158400390170800c15006c620354840c6d40042c021030032074103000c01c4012140d1080080e24040e580c0900200001e10401c1e075044c3c3d6504800400101c2150040c101c81c07200c4402290040c12294181c43d01e07070300c45040c2a40e00010350454007815580b04024003100301c0440d0a80100c6118107241c411118901c1d0400422506803485c54200742c1461502c44a00303161140b406120b954007410341000103488068082c8210b40a03c00d66002000940c00c0c250440014028050518040c000c119041501c0c0640c24070100e000303000848016000d03801c40e000d0140441c0c0607100500c1c501e0300d586407104c204e2003170040e5014122070580080c1d0b070301d00b00821000c1d208003001e00c1081d0480030380c00c0b481405801c1503400034103611449034000c0c01006400d000c40c40507100c580100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 76217888 1250 76216638 76216643
    0xd14070209100f0807060c060c0c0206120103110303070507121403030a0608010b01090305150a020c100f0c080603060106032004080d1403010609030f05070b0c0f2b1803 74
    0x509a0818600310348844500340120403010300707140d8000496220014500c011210340303441f150403046d1261a5500205503591607002400303400b0107c040140d40f030100900942000c0082080c640d41541469940b2030010300e4800e000b07520800001c00030860008140c0c045411806140d0b1401041d460481000d408070f94001c21548408010311030741c2d0207150030080640b42031400801220045200445030340000b440040c1503504002c0300881003c8240001d154005d00ca00c0c00946400000c0b010b41c1c1c0303000c15125440c40d0103a50b80c800200e52440340d01460018002a180c95403007420000006601c40d00d06210b00c9041c107554121a20320040b054110406c40100903500e181c4495440d98101c1c1c0b0303016001010400101d0042d40a42500c50131020f0724141c50b8555108083c945c155030300e11188505201c01030382e15120303000000415081c038000900102d07880300058244d00b0280f0052614006075034868801010080790480301c40444000c1640105032140380440c1519513031565091814102d030000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 76219138 1250 76217888 76217899
    0x30f0318031b10110414040b15090103060b0307090605030702010608070f03051c050a0e060f03010308070b0109020703050d1805060901020301060e0105130608070516060c1407050d140702 82
    0x34100c0c40519408a4440c0703000310305880b54940f14107000c1080368403030301555800110a000070301c0442c504007030741d040d407480113803001402041100000b400c0c04d0280100302d4a00c080004ca040c00365902d406018014018607085900310708000c8000740142c9098002c0d0000c1100100c0002c041d58405d4112030024071804087c0d400d141d4417241c000350220b24501040e02ea91203240c544030307581052800038140c220031583d40c003828440c0d5070f01c0450300344412205803940481d050106601d80717948800114029031140102d141d4801d401d1600d48240034050348080d0015105100ca034022035003240486044028486001950790030441c0d60fa50041039003100581130707220307000c00c01003141c00550055058803120340314000c542c61103d0044800d032040308050b004d0b20f2209d40082002c0c600810100350031001c5800d0a0f804c0602a0171009030001a065095071910b89540f904807946410008850038050350b04c4031207140c14050f854a80e0b440b01103055480070054016080c0540d002500241d598080d4010318 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 76220388 1250 76219138 76219147
    0x6060303051207050a080c030601091706090d09120602091c060e0105090c0112270305040e01050a0b090d05010e030a0915080403080403080709090f0c020d030608030f031803 76
    0x34020802d40020000c0c001c41d48511000c1854a40142d0685418440d142d9aa104650703034001c10714040d82014050b1410300c0074003200442ca8500c0c41000206412031240241500c2c5007110003280f0b841c0d1402111410300c80d2407682031210141003100d00070b055810120242e41d038000540031900b030b4803d0100c6001c80c00c103034145000400c003068100c290075841880091200c1e4a480c80c205807540307190b442d030340d0208010081b60307001c0c2d40d4190000e60b051740f00706001400340c050400c070010301104229030440000300001010700c500500c0341c14050150000340c82d4038110342c0c10046d0595052040c10759003485031101c43e0301d0300304000094000307090141188040e20344481007100c001d0b04210035805004c00410aa10700e02c4206445840f90a1246030141ea4150b4280c46035201500e01800103000e01c0e00700803102c00007143d501c06138010507040c510318610008601651900082c240780343d0000e036804050914608000780702002042c1d5403005004070b5004d03640d881c3c0001d50030b00502544141c49083c0000304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 76221638 1250 76220388 76220393
    0x3040b0f03060f190e0405030d0606050c010c020c0d11030f030a0c06050a0506010806010c0c0b032401090302030309040c02070518060307140120191101030609140103021903060603 79
    0x30718011401039070303501e60b000400e804004840303441503941c55844540346410407040c010079040c40d8000d0f0040040d41d140400c4084800d0a440b250b8201c88040f40c0002200c0626032070911070158a01968401b418076072061100003152201e0a060103069906090216006650240300029110a40104403a916030442c0030140c18120220025a0040e04d064001071103101710b07008061140c0416500c20b41c0076036420b401511009010340050719a401c0009010400000c20b0008600800c12180520310701021044111029a41c02d6441e90400100c07100400042c0c40010644d07040c0c0104031804269034122031002c900d45113150348042e52052440c403000300b0440c100c00312280200700c298243c414054440071101441c1034180c00c014000764420140390f007924440d42d41c030b1040b000e49a09840e080035024a51070044c480481c4182c400c4401c0c1c6a00300c0540d80c25124800090460507800d0003100c4e0548900701c0860750511002c2e004802066080050a500da1800d1000e10380c0010200728140d240d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 76222888 1250 76221638 76221667
    0x13141018050919062409050a0605070c0f080102190c05062a07080c010b06040e010e070c210f020c09160e130b0108010e04081b030c010e1501050907021504030203040b 73
    0x9205041714146510fa0700240d252040d00f100c41522400740104040600c0d0010071219a8004030055400e800c10000101b980703c2c040045100903c060030015071038485c1c006204c0c0b114034500c4111030500024041d1600041d40100307480e54854400c484104184200503083c1440302803191241007a0500000c00000304001c000180c022030001c08020415600184144806480303107016440700011980010401c135800c14064030b62024140c40c01c488c64004556070300e0303461a20480720f03481018131300400f82521507100369100c0f00e00144c0e01c005e043c11b24607070000c503084010141c51200d800703440411301c002041c022040c40100c0c0d41d01510208a0b800005c845030002c0104900e0036000444032000060151100c9002c14069508656100e2600542000a4690607944200e10999000500440005200070b10a15403841e080b400584461510744010085aa8058004610521200c3d05001802c2c0d030016a8803000c4041c0140007446031690306003689140103942c03084000420000702e40d0b801441c038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 76224138 1250 76222888 76222919
    0x80c0a0302150c0a1209060f18060e01110a051b070e0118110d021309020408010b01080109020711220f021c09120c03051314101805091906 61
    0x4103080c110a489140f0b001c0c90350700c00c031030780306001803201c0640c540c00c411281c1c0040b114a03c40c20380020210605c12820b025178250188824096400b4829002070006500640d503000002c00020410413207101c40301025805070303001d40400c0000c04a03124441001c44450b09850600340003c5458940d0303103011040306a0024081d40c1000c290102200381c1841c41d42c0500044005004c00483c140405160034200a4006500003802d00402d0b1400040d02a15480100050100c9a00114482904400240c028001070b40a03924580c4100711040200d2104c1e8a460008002120034103070585130f20030342c800050590140d0342c58407403404915440c44c1e00c13070703a0041c140e500700001c1c100c2030340c0b110f600b8410850708611409052040030a44140455100b41b1038841103a00c80d0030002d0400383c108030345203054002d40d04456100143d5204500d00e03403510f5004159036003a131345441d03401800300301242c030038841e4284201c0f4041c2e042030000c10030701c00491a0403c4608000d01301080311569665080c5400e901 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 76225388 1250 76224138 76224163
    0x1021219050105060405011412100512071802030c0d0c09170303071205070c0807060608070512070302060313050102070b060f04020f040b0306010302040e01120b0c03070e0904080c0a0302 82
    0x40c180c00d8500580c48501616040711401040c0380c0c00c203440d01d0b005540c000d0080e0180340035204104040d8003404100c0c0d24040c00380043c544e038030002505020a026100d00320f50103400d401e5201107400c01903000188045011080e0364480581c60f034a03001590341c0316018500386200f03036a090080b8204130070b501c02402d02c1102c1014011910042011035070a4072403109503010320005d1400750703440140c15001d0b0482a041b40395403405412410407074445042c55000307207074110707070740350302c80c8410890303c00108a0310010b04009c48410781030420302e101c5c071541c2e00300c2c0d440028020100800003c46400c10240b2040c13030103800a000759540c031918517146500660495005110f41442c1082c1080307030410380300b80c48440c24603143d01480c20b81000703021942900020300d80c50400d41c081001140580710005901d000382021060f851400c0e40343d242c2041e40c103100908010241600784100002e00b64003880c03440701144141e0340c0c800240c0391400c16071070a108065040045124906006080681c0010300072180c0702c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 76226638 1250 76225388 76225411
    0x807050c060406230304030206060f031c11070f060c0308090c0d05060f010e07020307061113030b10060e150d0b09092a0d1707151b0311030c0912010212 67
    0x4803100c132500082d020603a00078005900410004203681000c22866401040082c1103d01c0241110703103100240c80850079070f0340090480c10f070f00304508204010a402030b028032148001d1660605500400007401c07244090b0800c88d081c0089840d1031028810030410043c080e16014030b0710a142080e581d07070070302a2401684001e01c100005001074444c070b00680079a08550180d80307003c405803a0007000d4182007000c18003000040055005801c21078922178010351090606c0000342c60001c0005030040c419a01400c01d00c0710260541d40a690b46400605d041340032084004d0305c40c0e002242d41d8000740030998800350040100c0c018000803640000d4125030080c00c80b9203c01a480c000b8015100b60110045202c1d04514030705040c1c4000b42e000e5840301400c1340103411040c1070200c203407102c08551080b940c44000c8640e41d42400c2c02d01c40305420001ea152100c80c00d0910030303022110007400003488000c1202404600c085100c14490381c544c4841580c1e40c02e50402551030320144006403882080568801d038600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 76227888 1250 76226638 76226687
    0x908071205060609011809080906030a0e1b010507140f01060f0503072403020304290106081f05040b060906040801021206030f0709020a09090c0f09061701030807050c060406 76
    0x14134118000754140e40c040d2054031480035050320100301a00daa00800c0b01d0040040c450b59003291030300d001071841204103084c04108100340804450604d003034682c0700c0c900c0801106100c804c80c0d8000c801c98488652040301452014110b194060400c1d82030904c43d0340035403c14a0014108030400031402c1540c10850a81d80216a54000c91207036507200e000760b500000d60641030846aa0103907003c1c40e80300c0e010740d281d0800c00200094009130303044204018411300700c2d413000502c2802c0d8055016a03100302c0d103c201800c400b40c1c0140382038003080140b00b00c03442603444038134220440d16900c1c2982e00c03501010382001d0b2030710303101d036001d41c040d40040041100c001d000c800000c3c0140f41c0010031100b00c6100d4800340c240541400c14400c00380d4002c40c90901070082c04440040c0780309462061000380300d000d56032011030040f1440020422045a4000c00070440440480c48010240e42c80d4141165844403c0694a00707483c0780c020309080050755425400071021600103460740d0400010408000030322902e01d81d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 76229138 1250 76227888 76227901
    0x7030b04020a021b01021e0a0c050906030a020405180312160e0a0902031e04080c1e0d0804020a0806161101020708030133110705030705030a080a090807120506 70
    0x201c0c00b4019004005a001c030755030032005001c1c0703208070614080601c1500d000c0c2c13905480a41c074100098816038810b0340014a4071041c40301c0e1002c40d002030a001c03900f030b401d2030910300006030307843c0d00b4100064400d0396110003103041c001401d09211441d5035170005480e01d58540264905061204483d400149001c0250600f040741c070030f07101800c089030300a10280945050401c003400030740000381219845c0c214880110154284030031400e00c140e1240403042c0e56010540e401c6030a25415202410442038481e00100a00368085101c076424552442d24440702d6135940006400c00d50280e02c0b0343c2180c003d15091000c06030319003401c1c1841001c2c58450014078940c00c0760041c01c138450007001038107044003400184404c07001c4840e0040040f0b208046a02c9040503a44802117881c149104040418200320503411004414061100181003c90103064038034500000b00780c48500280d00280101d00001d0602d00301c030700400d20000500b0054044030b49440d01c855440d244881e9080080d1100d205410000e0314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 76230388 1250 76229138 76229141
    0x80105100e1b04060f0e0402040b07020f0d020303030c0703170901150b03011a0d0e0f03031906031e0f0b0c03010611010e07061103040518040606080f0a02090709031a07030b04 77
    0x5688412410a1a080c5000740c100e07441701d11400b14001300a844910001e40d6507c600107480503007594400d00d541c5666a10402c03001102d1101081c0c081c820a002100140e6030100549900080070300441e50747e00100e02e001c58030407050014414151120f1018030201850540c00b2034801001031f02684121a120344a1300c1140c01b0034840c118210304070f010202d0036a009035015100c0305400400218150561114840c1403041e00f8030040b6207980088104007800b0074040010b19400a08401000500d056855192002c0c4450b00c1d00c11001013815441000c1058144010760300940000101d1058200340b00418441d60003031084000003400b81d0000082104c041c0b00784403011000000402d500da103088000d40712541010f00d0031255000038000001d1355150035031000712201e520b081900c4689410314104003100d01c00d4100441c2540f00c0e80c0041145030001824206490701100d91100399a40d1510031035044070350381c02c000d14038081d440c411032504d242c4000d0280a0852900c05000381c2c0400c009210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 76231638 1250 76230388 76230421
    0x203190c03020409020f06030f060307060509090609040813030305070312060521100e010b040c0302211f0602010b01020d0206101a0f03090a0b070201060605031f080105100e 76
    0x1060300080380c10800043c90103030b0109984a1020b020344280840440015140340c000310f6507007007440151400c2000c03510301841964080c00903400d0484c04d211440001c225512401041c01703000e480c10501107030900404200b69011030342d9a584424116440b4540201a50030586085000c20484885908800382a000f1101600d601600d413800c0417a1030600708401400c40c11081049014a5443c054004810300404548044100020400790392483c203010480fa03e49000c801018814400e20003103000050700d010f40c541d5500c1361000651215101e01001c1240e0308000e5860f100e020500090164042d000b4066514098080c0d6600720b160b201c1c243e880b14401c4510281c460b0240b0720074001894404e051004200d844400e1904216061030480a164000ea5071500e49512002d40c10701000780c450303d86070740b180c020300c0203011051400702d002d0710500015003900260484c400d0261280c0d00d181c04910300815001c0000d0000381094050702d03017041d103c1e001d1000900030100000720040740c081802d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 76232888 1250 76231638 76231643
    0x5031017070b16051908090d03030b0603100329070531061b0203030417010e01090305130602010209090c220303090510030b03060705090d0c030b071b0f0308070c0816020319 76
    0x6807810001f0020810090f0302240300b1070600d584c8003444081511000041c46c4962500030780d1959090442c00c01c20306514024030388a6614804180c1d0840c05800c2440d915000b0a060901715141c1e09000813100080e0840380c84520000041c500e4140c403035460131809411283e03e42c450003564030607604601d50b1003d541a001e50143d0003000100081c11710780134020510030703d1800004d06201031a1125095904c9040160001140032401d03041140b0f4275000ca06c028802c0d8002103280c0744c60365011890054000f401d104407104003148400d510461701d60500700724142c090078045910b45a19020700402e1040c002c0324001c07500010740d808814040c1c402c43c8109403008008004c60350320303403d00b00c1d16070780030101e8280c006c20a101c40c00c00180c00d01c02a0343c080c51054881c00301e20314000b400103000940b14841c0c0090f085104646a021540d10f107414405140c1518104a07251f40f040c0c0c06944600c645100103000d850000b4101e814440d90601540c0d40702e1084082e1018082c000046074051884007101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 76234138 1250 76232888 76232903
    0x1051e01022d0a0609050c091608070306031407033507020a0e09060708130b041b0b040803180339090f0603010c05031017070b160519 59
    0x1d100c04002407542ca0ba103618124211031104220b620501d41030128a0f0000c0340e18076210b00e50002000418403611284c05025104030440340703400100c04490300007c048803000c1c002e455000c42c0c125031007a040940910b802c44940f800c0c1902220380d599841d4030a200981e80100c0511440403100060710402c00740450700d15075502c030542d444100d4409a4406002281d101c0311850b400a50580344c40c2003d40b24040d03c03809014949000b01c00541251070090580b0a20b82c040020300f80003d800a400c01e4005821120964101c0400b503000820307030186030401e45200c80045000140200c0000003415180c260b0340203154048114024140d0300d1103020704d4413410002c0400d07040f080e140d44040a0014030f80070a200d81c0b62132022404950030a405840e01c4645070811010000a41000d005088040030b151030900d00c0c4d403078641c003c0c1810300424010a146076140c00003211040a080054102810401a40c965150240c010140601c000311008480c18021800360507a91000400e0b5000850b130071112 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 76235388 1250 76234138 76234153
    0x70b0c07090f0608010603030c17030c16051608100e0312060607060b0901060804140606060a030914030408010507020d03060305071a1b0718050c040e0603030f03040303020301051e0102 81
    0x4107000900302c482c81c07010055503210400200c1000c01d0085400460190b01e0b43e440020640c01c19404086c01c00381c40324500d01c8100107101540da0000226402900c064002d00c030070a15524009040071091054100005011240030641403408940e1071140c02554004010441c080040c840c1c80f0f0044081c424a010100c000142141c1070280003440018800c0900044019030500050001700083e00101b0000703403550104020003915135552800d521030200101040d1070601e0000b4610305c0f4210704101010340f0380ca075010070468001e10701d41182c06198107403501d803601c85007540c0c001d2104954070f00c01032064800c0c03204201d000303100711826681c10401130200c16040804c8040140e104c015084584181080f400380c801c031207450001040f03da600302805400380f80c082070141d0000c4000310290417a240174244051215050122001c55100d01c0c2d40600c0707981d8100029045000d40d0703055140f0038038008100001c059055000f14107031901210103031710103600300301b000030301984100540703015a02010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 76236638 1250 76235388 76235399
    0x90e070c030c0812060a06050702090a1806060b0d06150903060c051b0d02070609050112090809031b01020105010b040e15030f0f24060a090b010302091c05070b0c07 72
    0xa40100516000c2c1c00d000006126582d0b0301d04840d07020580b00508074103c2810b2082501d0b1020a90004042c46d242650414003650006030f401d801c00b401203641c030740d540d400c50300598060b40e244846854000d50104041795031501c607a40d0300d601010389070200ca440c4c0030000c2810984041030307403070340103059070707448442030075a5600340040c091410107009000341440040d1034500c461a0408081410102919400c500008084d01d048040c0c0c0000c01030158516060200d81d9000c00030315540c40311040c010558179031500344a8210312441c0e003000d0b018003802005001c02d041c0c0340000144100281e0007000260380c6c6400400050140d03000d042c0c40c01022001068403020320003002000e101000f002d0b112000302042045180054620030040c1c9504010806d82e403074080f00ca102910221200e402d4032040c034008002032180e2100303000c0d052210b41e84103a030100c0f40c0d10941c195043c0c40009800115810040791090703801040c561401c8034644120100407840100440070749110b400c000d0010010340341000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 76237888 1250 76236638 76236647
    0x3010204030503031b190c050622030e04020706141905040807030809070b0307111501060215100b070b01211128060f091502030301030602030601180b1801090e07 71
    0x18903170480fa000b0030300c40c2e000c482c8912041c00246009544a0020203800c03440c1c10f6007820402410720340d01040075200c425071107148400000030b1542c18507101120392659030008000307019004001c0c0400f803a01e41e13500c0c60f03082c1d0360301954000c00c40c0110300d0202c0e542c01e00c400d2003615003c517030092011805120b10400680208a10b6070030141d0401568cc020340c950f5400e04283e04101c5026000600441d07620140c04424040107100e00b410322043c4440f5810900003946c0e9580342d0f402c0d19039448240c800600c1d8a82c400000b0006000c4000629580f07600e00d040082c10742100b80100300c12170a20500900304407090f0320951403070542c00114101121520300401c4040100300c00c00e190340309040394246102004000110025140300d450302009500d074404020004400c941144512500f441c0e000034816400006490461354010409603a903605c040048039414804801c65104610010020407100000030142481d0642142e0400a042c0d00d1f000441d9010040e00c0359600580342e600c040382035540305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 76239138 1250 76237888 76237921
    0x1080d050906070212060a0f0e030f07030519030b090105040b010c0213020c1c0207050d030801031709030a030c0302060a020403080304060f02070f1b050d0503270307031109060301020403050303 85
    0x50038a030500040340c0100f112404000d03101c2c6019002081000908800c6200b8070200c8c2049000400180322200c2060340d4903c11f1900b4040c0001d03000c5814020548984119000c072809480281d121070304100001e00503203216003055102d4207481c030020455043c80c6c4205056a07070141d440c059040781c0c0c5c0d020f00288145500d80301401940030461303105050820000200814092800e8030300ba0826032400a0901403507410031403281d12541d1544021070f901c0001c81e270540e60050700ba0350300000b0707958103480079214141045800d80215100d6070203041d0850b080b921494040c3c1c081c1c655642d24104403070100d200320301000302004020b20208011803010341c00907002c0b1000820045c6456030781c2d00c0351180c100e0141c404441054081401c9083c101c40d514051004000588217004182000d96071a0340380e01034080004081c2103605000c071101061082052403000d00902501c4c4005e8880c02d205010501050750f290180c050070010030741a0505200710f50171650440082c600792f03220003680c042c0c0b0080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 76240388 1250 76239138 76239157
    0x20c060402042012010f08060c0f03070201060f0608090705040b180606120103121205060a06030c0c021002011a03070503031603030b060d050a0c0206040506060d0804170c0102070e01080d05 83
    0x81d43c102c0d03030003981e2801c40100301c5810b040002c8031296240a02140248504c0c1c1c00c55411a000325051180280401c0180ea14220b440c599007616030f41e07032090890041000303600501e4400214440003520a42140000c0e00401d50b65003030702e6456445030184002d90702c1c17001881b41c01400035185003142e910741d850200e4024000604061512004085c0210710590a0308190f074405424004a0016904030b40310100b0790300c20010034001803a00c5000a0007141942c4251011b00d40c503050707007801240c419840201c1080e4014080f50070214003070402402000410000c2900c03c01d00b4a84810341d16000455100703d40c001001140782030b03200c03865940c01c000d140c54100c0134103481d4250b00b07100c1c0d50788030064100c040341140002040e1400780440b100781e1340c0305c88210041d1742000041c4804114082031240e404034080e19005411140c62628400e28480e9500040e04100300c40301700e40103008045803548042c00b00340c0c01c030f43da400d4807204a800101c2081c810605035501039a003109202e400703403010744803070b80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 76241638 1250 76240388 76240421
    0xc030606070503221e0e1503010f0c02010b040e120f0c120a0305070f0305100e0910090507030c0608010608070c020a03050f010c091703120a1b05030601030c03020c06040204 76
    0x81c01c0920500e0134220710204140c9840d0f41090080c0d01d00d921180b4140710201c0e4216100610344403040640d0030018040700b54285a40c03040c14005e4809400082ea28400e603c404c110200e21000028024641e0340c615a2003a41001300d46208500006900f01d900f40c0525803103860180c2c048111101540f0110050506008118624000180308000f41c4568006910702280741c0c0b5040d07038010000c2040b1070114060619140078413401101d12210f070010345940a64440340b81e22074041b0303075183c00180360250150741d0030302c1000c4c2c04000f00450074a0849104401800c00d068603100103031101c60b03090052400081c81000010304041c40380141c8640d06c0d001070901c035400da40720303141c050600d1803540c04503030325a44484503480502e40c80b07405c00000701828501400c03140a00fa140e5a01d034400c1c0c4003001404454007021800c0560f03154050300d02c89012410340c1140c140d03003041c00f40098000700e5249000c03c0c40c24008509190003402140c3d03101060001074902561650708000007090400340314070601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 76242888 1250 76241638 76241647
    0x307050a080303060402070c380a051608040b1605100506090a2003070f0e03030412030e0613061d010f0915360b070b01180902040606030507030e060c030606070503 72
    0x7486100c02745580188045554243c84e50181032440c1c2041c0008000c844100308075801d517580d03101d4250f41504c008260305014076061810402c641d4040e0380c04c07202c54088002011500c0407041604002214424402e5809041d80c00e5400021581c0841e013051300000c001c00050342c2c104542d441070034030003002501c0154407001d03080052a075800494517180031815900d816003140d608a940249a000110011841e25060082c418180042a1001020311180b1100b0381038580c0e40400351145012011904080700f80d5485006000a0160794100300078403d0001074406548507d00e11000c001d400c0e114092040e180100d085110808078a00030100180d4403600000a01a600384052058200b020079268440c60841c41740008140e601141421904110880c00513001c03912072411620030030b00d41050000240d03c40809080c050070002e50180c0303840008a244c82d01640264013500c03883ea02044841035a0204581d1484280e645c012020700500018442e8070707045001381401441482501d050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 76244138 1250 76242888 76242899
    0x10030e0307060b040b0307030521070609032102090a0b03041505010e0106110f061609080106030b0703110703021b01030e010617010e0313060c0606230307050a080303060402070c 78
    0x6541041e082100c2594a8650f07018442c43c1c1030084c6a8550001c030060308086146a85407030b92900609552443c0c051030325401ca00c00c000390400c1d0f6418a82000701400700c0d4003549001130283c00c05010541d0b210520701d05c81c034a141864804d690304201d020740b0319088641008528605600000c1c8111840200440c034441c0340c807007a01609000b00b00c400f00b402403030f504102018010001c00b82c1310189552080302c20510341c07030f00007a082d60080f211844083c640c601401c404c403215402d542021070302e0740c01c208000003000508031a952103254240d40410203484200d1614010b8468071f100070340140d0040000c1025401010280090b8080c1410000b0700200341c15211030a6440f075030310411411a8104400c0b0700f0b841c00b8040d10441e007115001071454501c0c0c11041c00003100d1a4004c1408001200d042c00c0b04004481d031107140a0100540c841e04510f10508004070321417408840390b80240100880006c16082c000c9146050300d01400240d4210f503111000c0c40000c0d005504195854011003000240c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 76245388 1250 76244138 76244143
    0x3090e130f08070f0507090605030a050c0910170d02010f0c0203070318050d0305030a0e0307020108010e060102010207060203090a2001020c0906040b040518010506010c08300c09090c03060f10030e 86
    0x1364a10540162096603d80704281044a20342c1e032025010f60800c00c000c00003d0000301d000c45609504580c80d6100343c0b41c0080f680c07545541600807017080c40c040100b0741032502e0300045046240220350300134014800196042825103203c1118000540e00910245c0000381c09200100320f1a0007948820080655620001d450141c481e00c0035004110004140702840c1e0341409640d4264103a003005514000c22075000030504007051255a06110340c00e000b0a4540e071007901240c00484d08800700f551282004009140c40380280038046407001c800f01030400049031004548900040160060030300742120800b80030040340b00401c3c490b8001da6070840274041d50785a11a95015009615610f100a001c0c4070502c0c1c211400604001d050003a141300362800959182c04a40e10408080501480761140c40721072100d01e80503001c0300f440103e46a040000000500b4054040c08100701e81411064550038007c000ca440142d42d0150482d1100c05003074050704088008004410341c600c1c2c000361401107024540e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 76246638 1250 76245388 76245413
    0x9010b190608010e0906060105070510020d061403060906010909050115030f0309090203060307030201110a0215030603010c0e0609010e01121406040c08150906030c09090a03090e130f0807 82
    0x3100810190014400c050b84004440d0161a4900e0301807518144140c0055403014000d012a0400400040c00700400c181403004103020081c040e800d548074103604400c48082c050f1409007170400783ca035000d00d000910340061864080e241c1c07840a05003590030704103802f024110800c01910175640340c440503a00520171803c2c4000441c0600c210346400c102c14980100301015580c0200f100c2030043c02400107036600420440d0480e582420002410080e043c2040c2c184000c92402035405480c50209102c10700d91040110300c50300084000304480001d09006903101151b0300d43c242c0e0004410700840310254005c45805210b0700e03050505451403400110701030305603005460540c020480d18070610203075042a0160403484640c90a0071500d614011504401c1e503c541c0b0856489080300e84040740d60b07502e00348400307034450340e001d010f102403440c2410009070f0b9289410b0049000480d0154001100d0000384811405640c400442d65143c1c451034664a42072501c0c0300c03080d85e0540d070400418000520301680a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 76247888 1250 76246638 76246669
    0x130e07081b03070605040b0a0c021f0807110304030c030f0804080f070f0509060f150d020a020c0306010f051005030408040e0412120605060f0c011418011a0607060509010b 75
    0x40620040d80d6003410f0a00146600ca002448000c0c08240030748200d040603200d4030604c600c0e00a00c0302d01140005288003d10301c01400a03400c0c1a000c54891039031200314a44a9101911501ea0000032018515a41c3c42541700c080e050b50102801071000410355500601028001c01c01c2505090300c1e10700d000d04003a003031101006182d2040e0750810a074005e1002c0d403001084100c0d61030f0402e04d08031011a00e201c605454003803150303c00c162460141d04041c010388034280d0700c00c00c0854481000c04401f075a511811a0080c5c4603100c1d0200004103048000c0310202038035005005c00c3c0c20f80c0700a400c291030980003c1e104590004043c0004141034001c0e2452521a41c050203100d44040e0302241e02500320ba24129440401c035040c0b0400340100d072241011607010301564050681d0701c290501003240103000501011078920640ba0607c40d031000201d2103104030501080003045612600720740d07414034020002405820140500c95000130890f030b07601c01c1d640320300d0f91000400c3d403e5040000440d28140c00c10701 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 76249138 1250 76247888 76247923
    0xb03010e030412031e1d0103111303061d0a1403120c03070f020706080c0d11030c0c100209030604150e07030b01080d02071206090f060906050f06040209130e0708 71
    0x2200f061650000e10340c0300e451080c01c0307010109003411000034074000c000d20203503090318000890300e6400d910a51182010036980540039031510080c81240c21640078501c0103a885030309240d0341040d401c44007a030b040303903010501c0000d0241d0b0b64951384503c0500101c0c0351004540c001408854032148201010600c55a141c82445a49181c504c030003900f0444400209011984004c0c018014103411080040d040300d104141c090300c030540d9188282c00b40000003070040308003c0c0172042c4000001da031005020241440829206040308032100b11040380159000d0541c103a0154004c100030800042d4030300219400c0f0708001c1081c480e440390080c60080300d90300440791250190010004e200003407040074040b24152010341b01b06441d01341c424041007800c40c8060880c0b41d43c1d114200c00c202410088600040c1e1083c1d0901201c1d0450401da0020a0112020b01d01c00c120000001e05c9032034203208440150400800b4441c2e6000030300b490740c00404540842505e207200f190b6000c5480c1100304103a0051060780e948 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 76250388 1250 76249138 76249169
    0x40608090c03060612011d0304060e0904050712140a030f020607090e0a020f04170c01022404060b0a050409060204050301060b03072c04060b07020405100f0302040b03010e0304 77
    0x1006260250090035040c240d0000701d03049289035408a0055001a4120b130700c1030801640100d003500500c0c10080e52000038030960100035050078044040e00403100c03036445081e0001d45e04c2050100b020270480b00100a6004510b0600089544440454109003e03036004404000c2c401140fa203041c0d261141500032400041c1036090080c0c1c10840198000b0f0075151440311130b45400e0a102d02c0c0603015040c3c2e0062074010840d4034921110700103a9004003c49001280c4504051a0041d01c0302c0d00c1c11207031801401000841126000742d024510448188051085143d030350340e455140082811100090740703c0c00d1b5030000a961390b40c601070149900e0043e000183d0383e500e49000c040c21521203500c0080c040c001130041168140d041070b0b8405016003040013000034072120846241422904541c1c19900910300080801d0b642d600700701405e82c003803091302c00700180c2d107402c00110850b010907c550106441008020700041c1070a23084640700c1c0e080a07002117000f28580005900716003050700480720809800c03c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 76251638 1250 76250388 76250399
    0x6040503150619030f14060f07030903050f0d0b040506060a0207050d05010f050103030504080601060302090603010b090a0f06030b040e0a03020604120e0303070f14010911040c021006031101080a020f09010f020c0405100f0504020c0706180803040b04 108
    0x200d2e658000b68210349241c0780040031100652940510311030544075000741408181809800c0d004420080c00c0064100803a41e12890301800c2c64100d4040c0b80c02c0c6105103000420014024800c485450100501c0282141c0c41e084010480d030313000104582d0010044500022a407445450f214007034801c40c8c130003242900300c80003884122011102101000d40c850392250010130b4020450b142c0280e00520500c41080e060790340ad4821080700440243c03d03101c0002d00105000482070303601d01c841e114203504003035481084280707400da84660340040c3c0038422041c010056442c0c03503482444910b0803401602c040056420311102140da07143d00c160f80c0f4030b07888500303265650781c0031800d1540a01c42400031810310041d64880300c00e0b8041e600d4000d050000802a00700f025000300320b510050440140144918a0240c8244c551685640b01f56164080c00340c1c4080740d035180a0013691425001000204200341c43c0c48400c49040c004000000b01c119103002e400310303074010140028800b4210384144180e6861a14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 76252888 1250 76251638 76251641
    0x2060307031b05032d010923090a0c05030c10030c0e031015060f05030402270403020706030e0d0c060513080414030c06040503150619030f14060f07030903050f0d0b04 73
    0x30701c07582d50744421040b44002c007489881041750564250407000544401182c0c007a103600d1003400d80c28652242c00e10b007044034a01000905201d12440303681180100c031340d90001d1540c0c90040c1c0012a511120700054038842c5071107580520310305141e80ca860500d240704180804c0c1000b4020741c001480c140c40c0c0280f83d00050311140000001c0c081d40c5044400482401c000a01500015000030712500318241146e005541151008141c002003a0b10083c45040c40c0c50069987ca51901c40c031808607040c07400b0441001400b08040601e00000d4075264150f80081da0303241c0080c0030003007200031401a4502c0080209120502400151040c0c800b5007a1504130701041620340400f00e40914130620003000140220744010030401031098000c003075441c46482d1100040c0c0459081500007070b60103d08032001080c80302c0450040b51103802416100c07400c020728000c282d10390508513407501040b044a4007040d0b52900c65842480b803540286880350034441900000c4000d64000342240d00c010792218465180b0749800d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 76254138 1250 76252888 76252921
    0x1e0d0e0c030304181b0302030a060b031608100b0a05030405010f051b090a03082d0c0a0f1106030a0b03012a050a030207060f0507020f07060c02060307031b0503 70
    0x5800030400c00d00c0c4280020750303a210310300a09010400840b2608410401a081030700c500009074080a81c200350b1010040094004540a00da11420031000240b00205502100e000f58030407000402e1001ca02c14040e108020041d08007081d080201c07200042a461a40280444204544d00d60341d80c2e043c141011030035902020103100e54030745000184410b10740c2d5a10b8071455020000c1030380340c4aa00d00c0001540100c40d030b03840036010b040d0000e10700c4403002e80e80a0310b81007c941180702680302490076882c000240590030a04000750700c064000700204202603025001c052055040000f0381c54060003042d290341003661040c0f5684d40300c002030740b003e01d001e005069240018100203c500c404080c510b00030782c4802c1817002c050000c0043c2e29610940700350110384125401035428404018211020742c0141000c48442c4018041c44002c9207043c10085102005c58100c0e031b0740c110441205808202d070960000d0104000e00d6540c1000e2001410200e8850048000c5603c40720b0312450007864421176041e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 76255388 1250 76254138 76254161
    0x614161a1b07023003090312070b0105061c090506010f080312010b0903070503250e011409060d060c020a03020d0c03140d0608070b131203120504081e0d 67
    0x9072048000451002041510440c6404683c07450803c44900d040300c44556507a000000140030342d00b99100014030020050900c0380c002c2d021030741a0121414001e8050241110045c0104007940040201749055005884104001101800c00e8980c91a03110115441d882c400c98064001c040100542902d814000b40140f04c12400741d0b03d00002c019000c015605d050003100d036200008664040241c84c10011000948030250841e050220382c140100c10644801ca0304003c10b40814001080125103421058103c810340a80c600c1180000d60070080d003c000106001c2e00540a101d9100201703400340540d4080c40440d030050301d07600640d030900038200101c81c6105414000710003103520019038420076000034503018410458459885020300c20180486601c10341c041d104207035010810701c07a400c00030305010951040440030a6035a100c0503501c040c00c040c021b800315106410014001809801407540288100400e40c941107441054401c110030b10703600244045004940c9410b196402d105041203038a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 76256638 1250 76255388 76255411
    0xc0e0105030c190510080406050c0406020a03030905190b041103030306010c06200406050408160f03030c0c03060516030f02040305061308040b0313020f1008010614161a 74
    0x1030504011954850111412601034864039103200c6600441105050161000429025a502405c0c030300801c1084203032810f0765039500e0640490b400c11145000c48046a5050f000381c1803500d51a2030a60007010407032000d03186801110301c58000b0381c0201c030155010791f2051010606c1345c100fa0078a60125a10101d8940c043ea0041042c013085a0b00065030b4100507500c440045802071540003415034800894100480529000c078000c245903402001030029503002c41d0403100c000c0803203050400d91028a02c24540710000c003d0060000c0ba10540c00005158040c545a0b01203175a240c2d100d00481380201c4218440d22800034815001540c5801101a50001150f00390300f072038207607201c15468001c05814001d0303004011340c2c058100441c503010f0f00e00500b2407010194480c03400c19010100215904402c9210b4882c041c0d10300f58a107002e1342002606121541c1d4010280c2c00c00b002a1030048040001001d9a00207000b8806031108810488182c0ca12420604143c40700d04214440b8450001d00581e01a5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 76257888 1250 76256638 76256641
    0x9060a0c030305151c0c031a061008010b0a050d021911010c05070b0112020d0f2102010912030c030b0405040c050906030d080a05071b0507032003030301090c17010f030c0e 75
    0xc0e40d03445050503c0c01e88000c5c0407003099056281c011207191166000401c09680c49031168244c150101d003442c0324035000d5132038503182d81c1102400c40c3d081c80c09000d81103111400b0700503004968880c2001c1e00349000d0200d00185000a5080800c005441c1d11403640f00207800c64100c020303001070a004440940310a420300300d0401c603070340d83c0750b10b03481c4814040e400a03900702d061054255600c405e6400030f440d401c030181403101100f9041c1010150401040c0030311102c42d00081e81105481442548010340c3c001030400001011000f0840c050729407125070404143d107600f07440d440e56545110b51800303030f40300c0c41d803040310305152006002000344001d0015219400140c18105c14980200e40940d00019161000400740d540500640e00380441d40202d80941d500e2030804010054001041c0701030f40c0c050700ca40030307035540b02c2d00507110302243d03854074180c0640042c8010842c0c5003460700405885060740c1031142410711040800401d14500b41d00241d100c80a404042084c40b0040c01d000019126683c49031403903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 76258994 1106 76257888 76257931
    0x3040b0117061302010203130b1c09030c030804020a0306060312080c0306030705060c07150507030e0609090103150908030702010c0e0f03120a020309060a0c030305 72
    0x40546000000c14180c0c840076114420400910003480c1940d030b00301110202070140c1100300e0641c401031000102c0c0c90340705665040500002243c2603225902940a9104030a4092a044007289481200004240e00c403204440e1241c241c14241155141e40c40407810385540d5a0000d40424607111000c800c01464031408039840c003849d0307a452915140c044221000748001e448050b491b42c0b0060b0b040285003440c0014080c00159034085c1d40e071036a40c401d401e611000c000d003801c10002d200001c860080507005110980c1200b03064540c0d0741400750200c0441d046500c10300020300706d020640d45042101e065a00310f0703071045034409035041e00c0e81000f000c00307400f03054021020408261185100f03482424401a1402c00201c02001091a000700c17845098555100c0d80c00c1c5421070004100c4038000d5140c0d40001d040a03840765072a1241403450742401000c40708043c056010350079000815260 = true := by decide +kernel

theorem cover : BRFrame.Cov 76079138 76258994 := by
  have h0 := BRFrame.cov_init 76079138
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76079138 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 76079138 ≤ n) (h2 : n < 76258994) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
