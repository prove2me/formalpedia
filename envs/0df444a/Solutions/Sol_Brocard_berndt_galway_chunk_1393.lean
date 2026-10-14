-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1393
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:45:25.357741+00:00
-- url     : https://prove2.me/submissions/72b8ff2e-0773-47d9-8b0e-485d49bc49a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 250359712 ≤ n < 250539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 250360962 1250 250359712 250359719
    0xb030702100c02011e050604020d02070f111507030518040f090c0e0606040501050f071a1905250215070c0312020703050f030604090606060806010210020f091c050d0801 74
    0xa002e44500700c07040d40000c00101240307074100c090402c00508007174420f0707032600085500c80d01d9130350446800c3c0000e04011522507141d07151909400d050b42c5000e48022444581c04001e41c0f800c5c5c603440310170310a11011140748c02c0f0716a505480e0707500000810440c810081e6221521a222401610010b941e41c49000803074110500e840410418141c01c0710701c00e10304001c100001d0703480c0c1d03108850940f502402c000d510342c0c248800b4084284540000107000c041d200b01e21401c07074504060b8540c00340000848108542072008584c80460701d080f10481d82d00328041402e04d000015891040b8001500c5105558500d1300a0030300c1c04400e002551104006005180000280341c1d1001c4000f01d41100e450341545000d03075039100141039008486d91040e04280000104025544a41c0440b180e15840032050020555800000d0a011021a03e00f0b025004610105403540110300c2104d915503c041c20803802d00a2400c1884404c0005e4000100b000740102c1410300402e604000241d9880d0140d942c10095604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 250362212 1250 250360962 250360993
    0x30809190507031403070f2006030421050f03100f050a06020606100e090403020c0102061e0c03040201050c0717010c0c200613033203040605130b030702 67
    0x406100118900003504841400074202040501c2100d8000c00a0f103810b03000c11241c03904522540d00d0040c41c01c00303034005840800402d44941c03060654854050b5907007450300000e100041c031049900610305140e11001003450f54914600240d00140b038982a820804005038040559000380d480401d002c0003503504200246161140c440508825202e5420341850f21801030f69400c0058038051003055825256880e151249442c02140a8000c080400768105410042e40711055001c0c000d00502460740064a000c034000c02c2144000031380400c0e00c4543c2d0312850319004036000944220b0400c0010481c00b10342100410123070000e4001c240180b00b1142440030355500710740003e403200b002d20020b0000f0710041069120260207010029031100c2c444024100000c5040c8603601c0c00d0001c00041d0b074070210a104003041014006410000c03903000c10074425010003851a0030b08200d01160340208004c4c03018504c1030000e0000c1142c1580707051003054480c1403940c01504100ea24000603405140d80c05000344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 250363462 1250 250362212 250362223
    0x40503190c06020a080d02031504110904060f0b0901110111072009040804060507020d02040e0d080903030105060a120b03060f0601021b0303030106140403051b030f0601061d1903030809 81
    0x43c001404000b0041e501c403102030003035103000903000da170110000d400c00d00c0e5906451110f420080c01042042610203190200303410541c14940118031305200803031120346101e21a025240c0c0c00700c5460510214000448000e080c82074030014030b5480d004a807072034140c400060b2000c507201c0c250b6403141c06c229110004610f1f550380741c0c1520038031509080c800851410000c403003e443c203c0c0740c4030340d079100745001241480c40030300c070029002483c04800c0d90400750041090150083d131640c582c4880e449005000fa9207000a0082c0ca51105080102c0701595001e400615414901004049510300303200c00000e00b4028104c54413010b0120f20010441e00303680c10b10050b070b500c41d0070f41542d1045280c142c01085d0b590205015660038407801480c1d84960500b44001e680003142d10000301c900b801004801000c0b4610a030a04500a105500083c01020b0010072828140da030316958039216076030a46100785941d015200c01c03d400680c00884002e4110440c8c00c8207002e14020345a22940e410002e82e82403408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 250364712 1250 250363462 250363469
    0xc0a140f03030918040b1308091513061e0c1a10030f03021e160302060c0109140106050301110c0607121b0206091014010302060a18091b0f0c17040503190c 68
    0x1407008007998000a800e00c010344109e200240d4100048503d030040001c054400c0e5480788082100d1a0000214298000b541c26040344284650100840c0c0380c84c41500c4120344100001c01003140d02001811004903032503026401098140701e0401a0b0740c1c1d0f25061b84641d80c0590503001600301c8070380e0a040ca0b4082000c54044140d820080c0703204490179150580400560100901c81c04d000550392108a0094014411644d000500025510f2104800f0345c0280714904c41e0030302950902c0c1c015510b44458100756030a9400300b00141c501c980c1d46201c1100d09024100c044400140da800b5100300900110122020515003034004041908241c10514506400c40d100c508041d400c220f240c000000800341042c0c1107030380c155100c64540314010001e43c1d004000b4032101500110001e000203a0442542022004c0f001d10402180011610102124507401d0380320b404000c43e03400c1400000103407141d160a240130079152001c1d8142501d4400003810240c44440203010805000e100070f05101d1802c0122004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 250365962 1250 250364712 250364731
    0x703050a03150803070b04080f0409140703110a0c0302070e010303050706050a02040f03060b130c08010905092e090b010b09040b0a031101050a0c150501080c0a140f03030918040b 78
    0x95107020383c2c0f5039480c0300e1031000801507160368021408002c0a8000c0d03518074200080400d80355920380c1e00e00e0f001015800381d205030031410000440c0c4480e000c2d1003260821260400c480303140c03a440c51010340e081c4007401021011841510707c0020b1501081509901a500c255600c5540b86002e041c13072030603a8000780c541c81c0f43c2841084200212a0490202c0c0c045903804503011410341039120008160b041b240d035a16480900b407111071550700350f120108505a1700b800000300000d40b070341c41005030703500103442c1c404120b1110400c401407250030381298407141c010550300100303000100d40e590b210428001c0c1d11000d00d15001280c1c00c8500e00d010f0107192507445044d40c1d4aa8847d02d9501c0340d81040c014003000d0360511400041c0c00d0740b000e10642004018680002d01c0d001803000000548004003003d12420915008101c58003205250aa5601c0120307881d40d008246c2455250042009500010020550602c010000c035080d0b911051782c0b14074280b0080d0031090b514540750800381904c0701c00501c150303107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 250367212 1250 250365962 250366001
    0xc050601090209091810110d050108011d06040222200901030c020a08090607021503040f110d020907050a0207050a090903020d020a08040320041a010f090302030303010e060409080703050a03 83
    0x100b401780091440c060000080c0003081400410789050603a210350b1103070000e80c03400c00001007124001504000703550681d001c0c180c40a60b200041164895070b040c0d0f4002c0d4481c2c12000d5103040446c0c03e0802d200d50300c4050a0000e040f85602e00a012810581a041c01818201048820f038961701440740c820080e2242c005400c2c8005030b60340301d480b18400c00003070900c00d91012441c103007035443d034101580900384184802d03592030038141407006040c0341c40d00c42183c1a01d110200c03488682815541c442c032480e8090f01200c5181c417604030070388e080d4201485403811485000b40004665450701403040041090007400180c45180e400c00a003049502000c1005551000d0070f5000021504405c032811290086088140030400c008410103140d10b1503111b9900500305004617200020b2400d0341d8005800988481e24500741c0c0c80410342e5908524800030354140c20a100401204c4603641c1051360000c4010300000b14102c3c2503a4103507054001c3c4900b07600181c00420384004141c1c0501c5421414044d1440011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 250368462 1250 250367212 250367251
    0x131506020d0504030b06101704061a06040501080601030f2903010507030c0203041403070306051f05010e03280813080d03061202011214180105130b070f0c05060109020909 75
    0x1004905c018006c01d0003441c2034a194500c040c843c00722440145448803004407582860305000001d000008010070607041882c01c214010b18080e41240d084590684460519580307150040d001008100c0c0000c007441d80303c20250202d01c01da4030300100118a908180079020a22900b81800c5910080c900d00034180b030200a00e202d60b80000c252022a03442d000d240d54407100744008039007041d10307540c00101000e0a04c1d0501c070f5615441d410b40d800c00c0c8020000c51301119907550044070100c9000b00700d10f4060700400250401c54860280d0f580d0326000180410750603480c01c0c2d5400c805507000501c0d40498110009040c403020340103201d0381803408120b02d4240f1506090400d400c548070090392000b41405400961444401075a41000c000d003111050b0320980d501d4007480b038003144401e2120b44401546080002415043c00d110500c5080f038000c25000340c980d440240c242d0715200040d03901002c2c8200c01c0c076000001001000f085010342461100507071541d40030030a00240c0e180140111003071490412010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 250369712 1250 250368462 250368473
    0x21209010b0a0312230d0e0606061e04030c14010809010b01020d08041a0109060501090503060c04050d0c3302030702130b1903050a170f07030509131506020d050403 72
    0x142c207a0384c102d0011810381d21072420a0343c070503c0c03910356905103080e040384420009510704041e050101d403900b014800d485a00000684900c4211209580035600703000000c01c0766900650031058022034012503281030344a40b5015a00b080950208188952244c28503030107580c402d03000b90300402060000e1005111120020b900d075541e28201600f00592040000d0600c104104003107040461741c8580c8019503119030b82c1d0400380000f80540707030200310000400202c42c10001a110b21801a61903102d0401e4140420000d241010318002e881c2442504004142d03c0c440403200814079202c040729641c00c0c0701ca101c40c2c6510300c0c860400803041d50418003102000d6296440081610320346400d001400e844540000f0390700c0709070740c10103d10107800b4aa0100030001c2c006a0300c4030f43c0380038541a840d8402c82520034003840c4075200c0c01270842c0c6d07410b001200c0000c4c05000941200d0b03074010203195100d020b011000c0101c1d054400e401000085982c400c00c101501803200201c2070b8000c1c41e082d450b203820354440c2e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 250370962 1250 250369712 250369729
    0x20c01050a0c2c0126040302060402010818030d1d120903010b060703050d050702011b050d061a07030c030203070f0b0709050108090d0c0f1202030c0d05070209040b040609060e01021209010b 83
    0x140d03414046042d26000702c017030000b01e0135442214000c000400380c0c101424025a240800c50b0100d02140d08840401c5034002041d060040340d40f004401136240c40b200181ea030019041003101881c00d0001c520341014440b0342070100484001449914a44400e0b001040500395089003003140e0241008000503030119501804451032a1042c0d080070801d5100c840080740140900303000c010b149038030805890381da01d41c0200104007414849405105041d147c54001c0d032080170b403200e19144007108100e000d001034050308007000c0356402401030701c2c24254103440303004004c0d04a02c1c003160340b28046130400100981020404029040c28a0320b00786500d0f20b00c2c01c041c2d0b1074400030910801d00c0000c0200d031081140031000c00710f82a50100741980403441c0c803c4082c0d560303040010318070214061301c41410549485007094410454006100320419100c58072480c05600010780103903086c5458200c3da5010910720700954410b489140001661101a003204c0b0080d96006014402544d040803040c001540e204001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 250372212 1250 250370962 250371047
    0xe07031503210e10020a021912030e1002010603030806120c2106011502100c0c0609030f02070e010806070305090a0f0323131404020c01050a0c 63
    0x180040e011040d40004250104a40d000800082441e41c812440301081c0403000381d620500d403981000c0c1c620a80801c028030000303003648001a0b00010070700000d8542810714880a00c0440c04804c0c40301e840d0b0034005403c1140480540c041754261540b114681019002160248000d2000308500b40c05d691f030080c44601c010307001038030407800340c0c40c85444201c0c2031001d60311803d40100180317070622484540f441b801e194100300c0407a501969000142d0f1900110400c00d401c40f280d405800d41104220985000b01403501b469420843c1111445000a00c07a01c030308007400e406500c4ea462003650000d002450080c580c4c0255548281c8074004000c1400005506500f01e80203050204641d501c6c01100e5280c0310309014043c0468118402040900d500903d022070b081002e58215500a0b1180948000c3e0b07103c0c4401100301080c200104001200000c0322801034004010400351420954400e1142500c0d41a1078154090b0fa0b9030f0350002c0c0494100388564604500c408154520a16036a8440c640300c41210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 250373462 1250 250372212 250372217
    0x181d010b1305040c0302270301230415110c070f1a071106090d0f0203120a02030a0e011209030e0405100f0b03040c0f06050a1713020112020d0509060403090f0e07 71
    0x48111300c00750107078050f0f650b440c40905041d070081503000c414041d200300c0c03882d046029501c0c044403104101007003808940c60016820451600d0b880d1030303031030b00c2041c4005681e580000d035840c1c4000e0307240c1440e600146401c074100b5000f0103005003042c103e00c140903c0b5500049401d2200200c3c00c58681128040d03e00d06600302900030780315400d41d0041080d9119400d00e45074006400c041000420001162400b0300701d000758121442e0500e54603081c6003078401c8040840c05603106000d000c030340c10f10413003034220541c0d0185010308442400d402c01500b681e104076000c802085d00c2c0350940442c0d0901303200d07040d0301031070746500703415084e1912481c0c0d2441c080b2400b80d0081e18034000300080501c00c3e00014a0014002c14800f01d80e00b40d91290b00a2048d0015610b10000512095602002c541d030498054041e4207601060710035016079900561f4101c055083c0359480369002d11015543e000244a0544141c046102a014a03d0189401040740d03a507900005002001d6504c2031000c0742d0f03903500b019400700050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 250374712 1250 250373462 250373471
    0x40f0e0c041109120d0906030b0604120c030215090103050f0112080a141b101103070302071104020a110d0507080a2f030a110703051903181d010b130504 67
    0x42c1c012210381c030030301594030780100c0610046600d01398001359070340071403090f559080a150344501d002c41c00d03a40d26400c00d03a80280f003400140003131616480b00b43d5050340324420107142c196503603000c00d441901050a00c005100302141c1c151282d60140242503111000c0340da405072940c1030121800c801d0080c044081e0540314081540c1c000325014013234220743c800c99901c010752034405a42d051914041022120520741c000c82c40003c403da640e9009400c8007191100c1000d0456880480c100e00a4100407130a855042c0d444203070381080c3c0c68074401800c2c11071003661a105100c0600030310520b809660892541004010050742001ca444242940c1c002c0715a0720704440d080b4000c0c4005c840400c80c401c401d529607903070703403040c82c58141c0000f0003400d11203100d03111040c185024076070407501c4005a1202400c0ca4100b4800143e101158005e8107a00c148281400004010400034608141000703400980306408900f402400411000008500401e00c80e80901d1170541c041c045403446000c0e0384036550155844 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 250375962 1250 250374712 250374731
    0x908040816080d03091a040f211d0307051203030108060105011d0d020d0203010f050601030b1801360608120412110a09020f210906010e04020a0f090506040f0e0c04 72
    0x4003d03006100c150300000030341c1f4103050408402d076800602c0102c8226800d8641c24410704076a201c000401c0646484039100e210103000050000e40c40720315060360500401c04082895620359811b140003d410b0301c01113071298142503e0f01c2ca8800181c00060600c0b10950485035803600c2c948082610707460648500500c042d041c40498103072070f0200e200a526500b0104402504c03610f980c01240300e10307426a01881076004010921484210820100c0d014481c41c40040c000702400a02c42c3d503586800720b06981002ca004103102c002c52400360040e202c413648880e81082804400c100510300d20440103401c070320301441e18046040b43e2201044c0100740140d4900f90b0216a03868a21030001013210045c150341e22004c4201c00c046903840b01d1180150002501c0c001e858070002486082c0c0728945000080c0807607400c1801100300400020000c991010400402082003004141c030790009090912011840c2d0416030100415140d00c0c62400a4062500d403506c80c0da039600040d50501ca40342500d0010b5003080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 250377212 1250 250375962 250375973
    0xc0206060d110a150302183003040503030a090f1a07140c03060106030605030616050f0c070513230411060f070b0403081b190e130908040816080d0309 66
    0x459100c02c4840355841024181c0756010b400410a490790190103054000b102801c0000c2010a8006412464041523200b5000b8081c15005001400000d040328201a0b8910010f0b01d07550003082002c001030104401000603d24002c0480041c02040c00740030455400d580c01501940103d40c1c025112070203000071304281c0780060040350354018018050300c44640e1101c50107409070010b0b00c81c00d4081d1069400140841c0c01162a000c20583c980d500c0b40c4c42c003221558030103e17a40184183c1040e50288000000e01d03a030392184019021f6142400c04650850a50843ca562541040010070400750342020800001c1c401907041715101e004544254460a5520050714140510310340102001c0005041c0030074180c0141c00e00e071082d48801d5000d08140d6070b00c0340d081c40c50700039500e21070b802c4040d44041c03800240c010b5613928140300d00540041c84142a0484000541e034141d681030707038101c000140c00d01402d1000d00c0f0010f41d15031004141e00303c0c02d1415059580d034009102e005010103545406000c100b08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 250378462 1250 250377212 250377229
    0x5070309060f052406070b040215030702010b1201020a0927020c030d0c09080a0b18030a0c060b0a0f0b0c010e07061110050105031005040303020d020414040c0206060d11 74
    0xd03007040080052000707405101009000564190140048100803180440200b28009200e8540500024104a201e40e00c0c0c2501110250049902c1000b186483e550550710074051032203290580c0c00401c0c0040c1400c2031100c5903003480140c5030b05900421420100b607402100131801c50b5920014040d40b074103541180281940c0d42c4a494101c1070000464280c101c000102400307106130783c0b140030494955512404c0c0c0d5480035520803403040703400891b01040031541442013207500101c084100250300c00540d030003500399404101d40c81c020034448a25030042c0400c6114a2a540900740d5010310181c2c00d000d4002c1c201101d501c01e402c2003032000262580b182c0700030b4000c544a152038208450b022601d408010303041c0040b501c1c0c2d46400b031040a9443e0f20688603800707118101c030f80140c058122941e015641e00054040100203805242d002c0014103442c42c3c3c203100810041551000d400b110f00c520f08200010f17254a514007008543c01407091018594628540d8080940e002c900d411504000401280111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 250379712 1250 250378462 250378481
    0x70b0a06051e0901060e09190906060306150806010f090b0a0f0305150f010b0414030705090907061101020a0f0c1707110907022109150301030f03020f0a050d03050703 73
    0x5007100d0514402d401000c0d0803a44568030071940000750360f0b21031004580f149803000c00244e0001551021824030010760300c0700c0915a00c0460003051400b565140c007001d84803180d10458600341c0d904d40005215400041c4500908403200c06010554581144104104024043d8000041d5240c0f820103203681d03008800e1005001c0700850003c15956400c0240d207070024480d0450502d50307a44009226030851420701d9040e100344411642c101400c0482e1001691007220b80160184122031021400b41d64844480344200700101c0100003090520000412060152885000b2680180103034070200703400040c14011801f0501e8032840c848010b00b01a0f12000301203a1102c0c00460002e910307400c0c06128485000b20039004ea40601241d202c82004076624020f5104400d00c0303082200c113410030040d070b00d002403049040003044075260b081440f172108080da20030b900c1240ca20314103030300d07103000c02d0740621620000c0c440642c041c00a0b0b11080d00c0345616008880c000101301940c507400561424020307440036002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 250380962 1250 250379712 250379719
    0x919120813080c030a030e21061f2103140c070306060506090f0405060406050301020d0b0a050111120d0e100b09011401050d020a050c0a080d140606070b0a0605 70
    0x5500a05140c000d0354805041c844860034803040c04141c03400300294003881804050014079082941d510100e81e000b500c2074210703a200d0b881d000c11616446c0000512040803010300060304071410092544019860715002c0510350364650141000401c0031005024604055490301c0201c400d402e103400c403081142000c000c05414400b0070080701120340003610f041641d01c660001c010a80d180c0e4200016402a200200e521145542261255080c10f801c42a00244083c2c0003045444c2c4840002e802d98000d0700403442d22664502c244101031402c1c205080c01080207080c800d502500004800c0d07181e142002e9008042000002d036429540c0c80355104652003100c603425070b040c000c1c1107891280900340350b164191241c6c125400100c0d0001c492150b504450005071166861b16808a41001c00f82d00545019014808203200921040d1004d0045204142c0708407941c0e40d5030303d1070b50046401ca405868000b600d0603002810072541351143d01c111000e003a0440b01e0014650340d264403c2c4060700807a001980c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 250382212 1250 250380962 250380989
    0x230c0a18020c01090f120807031a0103090203012018060304050607030507050d050906070908010c051b010b0907170a09020603130f020a060203041d060f01110709051003020102060703110919 83
    0x14001410301482c6d40803120341e9681c0c003684512100310145e80f10b132211244114442e0000c2803256019910203110948047c0001c140e400301c100703120303210442c15102e808501000040140021001ca00d801e031210000b00d8a560650403e40c685503a1040000c7c168014035540b480032502d1980950155154070300911790612040c6455540b1544800301501c140c0040f45203540085101101030280035504804d07541c625050405406400405a00c0103e12600555032018000c000f0307116003004501c60041c1d80c9503c001924031907101c140700712008001038041c924100b942030041c0e80741001c80750000016600580e0707a510714201110a481e409000035030021141c4000035425801001404c21036075100e00c90300384e0010b0b402c0c4000c1d00c0c020845405900c8501142500140d6000324200d0100038100021140135648484c0150105d41c02604d6191020103480e0b0100115070341004071583c842054035050003e143d6821070700810b40644440c3d1407007020108007000c1914032441d1110700500000d441410b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 250383462 1250 250382212 250382243
    0x20d020405010f09061d06041e050a0f03020307030609081c1512080a030207150f09022d0f0123040e0603030c070b0d0603230c0a18020c0109 62
    0x29445442070901040c0d029694002080c0210240000c0300e10a4603a0b0003030300079500c07120055030b45240b40c20b903114105220108561020f041c00b02d08101309442e258402c01d08050030881e461038285d201500d83d40307580f44240300688010400c1811640c2c401800304034505e4510740380c0d1841c06507200c01880781421801c180f02413460754000064010800075041440ba440315803c04d0310400b11500039141040400080c10002e02c241c0c010030265001d0341c8900201c0350a440c80b0b030b050b16a68480d4100480d22181a4002e40c80d080c14050343c0390001c403004a0481c000d0040c00f2040c4500540318604c900101e160b020141e034025846d00324200041c241c00743c00540440030340e2a040e001406000400c044080004a1034240041103070f40d200071074030041040300e02e0448500c01503441405415200e40d140c440000004118044043d844442070004140c03040c1e441094601d00003409680c03501c1050a0745d002c111000910305104405250802d001d80d84403110034880c0d01500716550020002c0e688a030000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 250384712 1250 250383462 250383487
    0xd02030f04031d03060f0702030c07120303060b0306030a0f030e0406090e011508190f1203050403080c03011202150f16050d0e090115020f0d03060906080f060408030a0209030102 78
    0x281c1c0704600c262101d40200e60084048083c2e8508248010703099482800171400c030106080445500401600c1100c0c0b91540c00010f0509040c203c0d8007100803174001002280070150903010324000703041c50000c107a04501c1e190780060360f00c01480401925000c00d00c0000b0087c58450001365410107030180050107095650100d04008014148048200d075181c0040c1c149005e00f44c02106084403000d01c01001c0340d0444100d405541d06540d0f030211030f800c800000003400684401d5115207080110b44000515140c40d0401505d820002025210703401002c200601c0501c84030741040103030a4041d524441081c0d004a5403500302e10510328620318940010034120000c0800e07a01e110f01440c03050007614040e021060f0f054480d03041500c1c8507075100d20200014404280d41a00070001c011f02481207030b40900000c104603051501003a46000000e4441009220792201801041c000b42481001000070120305140f094a0b400d02a000500700c07000000410441c180d65010303038501c414020000c664600b0f000c04c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 250385962 1250 250384712 250384741
    0x106020a0302010f02040303050322120e0f0307080304230604090b1305010e1303020c040f050105030f151f21030e0414010b0307050d0501030b010807080a030e060a050d0203 76
    0x22001503081a001c032039480124021b5900b1032368551181411a216091080014240140a2440708075104440c2c0c0c0403481100c030920400e20a901c0b00f5043c404035400340968880c1c2c080007140668080d020030052440000225800c584145d1358000702d0051590170421480322203100980e008801040c0400e0310602980054070000044442e05420801c8206c00415501d09215542c2040078071800a1340c0000340d030302e941c40b403c0c0c860b2055030f80c42c402d010002000c880e1410b40c00074800c0d64403c018003882c141000030388172580442c0010030308004907280305048500300504a844100030380d580b05101080c9a81c07403d01402500211048217001c2e060b848040000900003600083c0034045540001d05040c441ca000491034080b0a030b00c2603090181020040c0d00240519040100070030a041c3d044580c0c1c03107050301951017076200070000c5d49070a02d5a4a03040441d0040105900301668820009030001240d404044042c1c0304a5103c0034008000d54080c02940b0f17006125a000104100050003140c51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 250387212 1250 250385962 250385983
    0xc0307080403030e0f160806090d0801090b010e0d03080105090a0902030c040b011b0302010e01050c04150806030c040e1b1906081003150209090109060b121008070e0103031103070b180a0b010602 85
    0x84600c103270360b14144240d07200000205c000100c3e00c1c4400500503144181c0040e0109030040c10300300c41c1700b0a604082040364040751011303400110350f080140110314140f1542c2c0e8020b2000c00e81442080c40366000a9240c081c0030582d10300c1385030b6407244101c0030303401080350203100c42000007400200c1c0f183d810064064024866030b00615480c00e00041e00703880b003103010f880582d402e183c01940802c21010040c0c400c48006404141c2c1031013400b2450240d5640d078056260041c4202c00641800103000c031004098810b9860b4141c802c01c28129681c002c910381d0138040044681a117000045621050200540d03180b540d0030241078040070755016035103411960000d040e0b0f0b980070f0f52548401c0c2ea8400200080b500d01c1c1c052603019250170070076401000c0300600340580006449214807902036840300410726029440d072001e03a4011412300100141904401c085580f041e29001451801c01d440c0e41e15000400000c02c40d40040034204001c00d51450100305490740180e03c500d4002c81d6584a54020399180b4401c007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 250388462 1250 250387212 250387229
    0x1050c0d0b030601030c091d0f0a030314011a1605060a02070b070f050f0a110706021606080906040609080702040e161e050d020102030c01020703050901080c0307080403030e0f16 78
    0x360241d0722414000782d142e0480c1d0300024407a0001c0d04000c8a0400790000121080c007001038400c0710f072041c0105102e10060f900c3c1e00402400f500f486c2d490064280c07080d03000c803c80d1244204004011008000a20040b440c0c00d8002c135540e5400350211160021920b040e0240551144008015020b1a80c0d030052010314003484403806996500182201c154407859041c4000800c00d0080e20307120f810020207040c900805003015000790351050400c510700300e040d44c4004016404180d0304a07500c050f415091000e084540b91150b0b4030f1401c3c81d0a140c0c0c407180a070008141c10341e110703c100d00344090314068400305607008005200d07410b10107400e5135691206074104201300010901c0025410410201d4038500380789a110403808529000130424420711a91050b81540402c01043c54482400e10081c048180320f07444650f200d4809200040141500a00e4401252420014440c50b00d0704036240940c040d9041c0b4000c43c5c105d0600d4455401e1000380301c0900810b12503031240034071008022600d08160703039510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 250389712 1250 250388462 250388471
    0x30402090612300c0105070e01110a02091306020315130b0d14150703051906060512040215070602041502060403090e061504091a060901051c090501050c0d 68
    0x104104011244140c0307004658004821840c400b60103003075030a030480c2e02103910340c540500301d850104950321a420313901d43d0b650740c4e170200503125412581c680f0207041c0c00e190035a401e20b0003201ca19078881c005003001e40305082410010340c1000b40500040c0d1a950302080030342d00c03420040007915149007a03d0a05110f18592040385030246072510507500302e040c009282c4c1000302c00585030314401e0b0030915403540b1140a40000300b02d00020544603180211010383e000107051030002049980044540048031031a81450400c011306540038058500250420980c0b8600b500c0b648002940076a81c1c0543d0701060703001040b40300501002c1d6015200b03d50f03000b8461046400305c0d82080b607d4400c221001000302e103907084103020101c001c0040c950300c050041c103401c0381e54003020011796090708113070b010884480e1506e1a034840b485441c0c10400c50030909884803400c00500d503001034017074003515480b520401d004615000402038180c01c0050520b030040c00070403107402d2030301000c2d0082c0d125001c0d91400a003031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 250390962 1250 250389712 250389721
    0x80d090f0b07020c150702042706111603030513020316090501090204031a0a02090a0e040302160f1202030a0c0801060e09030301060503070309080c0d120608030f0306280b03040209 79
    0x443d28100c4c510004199060b401501440294150010b001c1660040da9851505546c1034440050020b18200007905c94144020361800c1802d40b00c9500340b892504105104080b500720900300d03200e200719490b00340401c0641c3c5412107005140800c0784083c2d89403007500e002501050380c505004042d81e08410060004e60380ba800d10400f039204912006150100c01280245810b042c0329603141c10032080354002d0700d40710403140041c0c0c0007900390700007180c210392410501080580400403500c485c00018440841145020707008208100701e03125a18203100c20a440800b1035030103101c8a080301d41d1107610521083c1e15500045d000340600c0c0511100343c0380100101d443c03a44c0c00001d5074103c40b0690384052441d80e0700c9004401928904600b162000801d214600c0c2e2020b0a001041011000d65248450048a50380380d0040d03540c913912000300c5400400444244111040881c1d52180302503a80a9041d80b01c4005001850269841c01c02d041100017808103038010444000e601a0703000b29880c0030162174 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 250392212 1250 250390962 250390967
    0x141507020d14090603040f06020d0605042a110307050f0d0807140d0b0103020f0d1e0605011d0307030c0603060906090b010804030804110d050a0218090d0309080d090f0b07 75
    0x9180b444a095810b1240c243d02e40780060081d540948154251218083c1564510b0160381044104200d6151100d40074001410544140d80c40703808040c0010486843c18940c12003040b140c0103450b4104031841c901e404a5035410011182c00caa801011a014405200d0040d501d0300d0004d40208002182e007004100b40c28030601014008010601055103041d03582d41808000708000c2d0012810b043d000e03c9245000100301c005024030366400d40010070007403229020220440d078800800e511003850200b09000a907400310003c0c1d641c8040b4200d01100380000b5000915007002540020700c240c03d03000000c150240d254005c1000c4403035194043c1301c0241c40d11452400e65604018840c00110001c001074082803207000b0540d00540140361002d110420b82010130703401a00c04800740c07001d62040e94840c0850428003285154075030103101e007a56906084941c0c94a0f1008403124200700b68842c004c4a081c000d00000300c0e00050b000c220100540899803411400310940844182c030070701000f9000506050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 250393462 1250 250392212 250392227
    0x2150f0723030f0301090b010903060f09050d0908030904051e07020f060603030703081609080304060c0b241012061404051014010f02010902270705040602060402010507141507020d 79
    0x38180c5486070545e8242605100100320381e41e8030350f040041c02e28000010901174401c606c40b040000c840031038036010724201b8520300404a048a001c10000300d408200c40310340070081c0c9620020440300440d003500e5134610700d0701d172682c000710100000c9150404c0c80b070440c2d0002015169450345100340c41080d611803041680702e0040399006008507a210380000d00403140d001c04140c02c60101d0602070b03030550b1145400d40c80c42c0c000e600002d020915005207981032090801a1036407280b00c0500742d41c1c0408201840503c003400140807140a1441c0414044a580c0580e08050001004000801c1400d03500c202c40e480b449241c800c464002c030300c0c1c1004a43c07420072442a0406907890304101180d1100200c004640c40592103050000319540e03110003800517039034641420b000404000e01000300d80002a03102402c204003609040a00c031007000300304080d5801107402a40b043c0c090804c0c07034550403e410310003c5d82c4c0500031107000c0c0f0b01558030640101d826480e40c55008114582c00c50348038a101c80816290107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 250394712 1250 250393462 250393477
    0x30108100504050c12100617010f20160b07020d080a09030c0210020709110705120c070303080a06051201090605010518040204050405011e1e0b0d02150f072303 70
    0x2a0044c050104060500300503480d125221041105c0b411044003908604407000b07038202d4000d00c1c0e60310425081100d802d0044048000000904010a400c1c00c1400868501116064000d06d00040344e090400900f1070142d000064000f504c0d03149624240b0002034440c0038003080318001c104140040b0b050200544140070380e556040d100c0c98003119081c0c0030410040d03803200d8294211310030b284020032a0540ca018280e488179880141ba40ca8181616006050a8481007241400d050601c525401000c0005a0a08130b83c0c141c02c04810580302c160050000c0c0001c2e40000781c1090f014138810742500750541c40005028041c0c0300030090b0381d1f2140e0411100e034441d25010b000b205540c0b00446d000d0701c3c05510403138001c1c0c400c000004e03d580142403811281d04a140c1e0100d046075a0f041044443d0f007100f10034110090320031508218040400c4c0003d00c8218041d100a070041440748802240542c46000f2540528603008100b5282d0100d454845031a0002041c403c5040d0881419202401f80010030740303148 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 250395962 1250 250394712 250394723
    0xf02030903090f19140a0b1c050402060d09110f0609100503130c0e040c0e0f0c0c0708030f041a0304020d02010c05010b1305040302150408090f150d02030108100504 72
    0x384110041040604400d043c25140c0c0b00c202c41c03222034094240044050000c10b4003031010010000104104585840543d1050020600801081c684c4000c45200030707120301c0c2503420000e04c40d109c0c6e00215121b40981a42821050314000b40c10701445401c0c1e01e040c150500480702d4801d4030082e01c0602c9800d0003040c0090350040340c100b94520b44603014102550340101c1c54600004012280d0311481191521948000c03503420a1030280401d208840080c84050040200b1440a900f80084818182440141081d2402c4400326480e0607207042401118010303d041c0b801c4903102c0300088460055907125103e1602d44000d40f29906200038064001d8910403038009181c40310500c40b80d00159001a49418200d5071075580e0342041301c959451003150700554180080000d000c2c5884c1ca0040c1c6001038480201042c10b80c0d1108220001e8001c404a40c6200c405840144100d22100049007401d201059400c03040030010031500d640f541158095412135091401722031140408010b042c00f11941a10b02030030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 250397212 1250 250395962 250395967
    0x1d030703150b040b0a0e0106121406010509060d0609020306030f010b0d03140d0e010b040b010c02031c0201020409020c0f06060a0b0f070309030501020304050a051b03070312020a02060a090501030f02030903 90
    0x1c9245981c2d00c03074005440c0161001c60303c0303007602d0300107100b5204035008050070000e5a0300501c1a50390101c0960035401502c5401c100c0c02c25071026000350202e006008038100000001c4159050325054252000403071090024001c1c16142c41005d0080c2d081211031074001d2041d025041800c1c0414003403501c040720050090f002404494800720758500300030400b82d41d050703420046c204d000c2910b441501c84549019000017040d40116042206441008244a04004280300d090f40540c0d00811150b00120101400c1030b904e81c01c41340c0c00d0b4064000c5501c0402540c1c404a00b035584041c010841424a081c0e2106444840d40e0300303810013424011a0081c0f03071741440144003151695050200070101c0c180a410002c0c0380d03690345d44d192400d9030710032101100c65400101406040040401401144c07000c078440c018a180064004a0fa44100c0b0707110182144012070050342d07440e40203114441c55a500902042d03518000716401521058440c8221400039142182282140100d8401e4070b00440c1c40e04041d62 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 250398462 1250 250397212 250397243
    0x105011422050a020714031305040207021807020c280902030f0a0e0114130501051b0d1a030d0513080a0206160606050a081b03030c2107020301020a1d030703 69
    0x10007840300911209025078204402d5005c212665050140c00740444019923031044514140c10048800c1c0e0703c035900460040c0503210051b52056021415815400800341c4182e40d0081704a2916006071500b03a0000c040d244201d04480f4000000302c511040744c0c04043c28241d4500c42c4401324403041f50416844d11000020a2001d8819000300e0402c3c1a40000851280c062400058411074103903000e01c41000c59940b140108002070041c258030002c001020250203440c842428103e101d180940e40002c3d0382e815080c45403188429407440c171300c0e10140132a060704c80b502c2c002610b180d20034542403000c201000c000143c0c21030b0000d02c0c502c40c0b5038003a022a041c0327001440300c44500e800c003090444400740c9400c804501903c480c49888c00410700080100155084004041e0f48241c5003110f0500903003040140900300300000a00c00000149941c040340d00a000e48007403410380c060b80800030744c154000200d00c1029a40258181300e106928086244064022010135980d0704e42440010060944046141d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 250399712 1250 250398462 250398529
    0x30516050a21170a020d08040201080105011115011e09090302071a120a06090f060524040b120a1805060c1b0a062c03040902210901050114 61
    0x102c03240e005542105000211564403107802101d40d00346003400100c04108042d40d07550400400b00103001a040580c0a41000e40000b089001c0500455041c01000f0409001820b8208242c001c90781fa02c0c41f0321091342d6120780507010003040c004c1381685159014070b0085070b2203405e0300c1041542c3c2e80c542c00a0140b02d00d00401c40c8030000b031100c07190440c044140501c0c442c4481041c08941700d4224810009403203400c2103000c030111390b140075040804501d000d81c244816258910080c2c10b101c0c0940450a0300314810120041510a50300260544200462490040512160001d014080e5400d082c0110f0458001c164099000c1403401381c10317648a0030204142560440050541000030103050154003640b401e45490030503664000c4540c0d0b40c2d030f114280a079600d0b01e80841c035504112034a51240b90f084aa00581d640551b005d070b10800c40c1d000070301c41400480a0640d05030041064000c42003403400401c041d000f400309103d03c0c0c5107801c0704c6011a038a0300d000c21420307280b156070029084c40084041e841 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 250400962 1250 250399712 250399739
    0xe2a0301140f130e0703060509030a0903080c1227010302120a27050a060b01080403050703030506060d050f0a1a01090e1b0f2d1219020c07030516050a 66
    0x81d42d00501e10140350340482c3e155029500001000c2c000411100d8614980320044510080a4402c1600103000c0d10310b03c15409544c081c01ca9400c05040f940380c09050040301e04280c038262071842c8401c40002e4000003101c0b01c92001240c0f01c5415400e0202c0084000150305a118407401051741b0a51000080d5108010350301c4907038005180010030201e42504450021110410b0005075519442801c441c02004010301400006483c20701e044000c03401c2942d0007604901036984000c0a01d43c564000825603115070301568018040e6400610107070034811071281d0a1403054481c990384500b0f00500e240b8940c1600760340b00c079600c41a520940514501120340a011b080a05104500086406d0240c04c8070800b001030008151180c860703d646544980d00d405d00801c40c0004100c0ca40c03003045035140300752210403d0300c202c00c01061041d5a566186140101300701884078001c14040d10210745c0c0d00e422000002e1351410340384160104e421001c4901038442b0b00429a00c00c1c160701245c411070a000c1c0d924852207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 250402212 1250 250400962 250400989
    0x14010801060c0f020405270c06040315023a051909020f27070f0f030c020307120905030c010c02030a0305090105120f100527100e2a030114 61
    0x150203400c1150340e0001c1d0513211b06940e040700c2101d80c5140941c0041c0c820083c4000703101d41ca0010015000290003281250060f1b100181c04206d501c41d441c200100d043c0c04032060091030180005a1301d540c11000f20341c94078400c4801e20350107010392800d01c0310401d5115050166140820790941c04800c40800343c064181200201d0300811900f0650710541c50300ca103400b4002003049160452002903011508031054014000c1f4200800013540c8024542c000240d03111a200c5850082000010810241e241d0b20880300000c204805030440c084000d0ba00080d0700050361811804e40d150704603210011030b0841146031019503d0340001000b200041d000d4401000321aa060400d00c1c146420203c51101c42c0c101110f01c07128800000c010041c1c100c4000b03181001811084505a01da60100341c2c0700e10308030441c0e80401e170700843c40001146480d01c00070700c4c4000602a8020340f4440d89800c070b40c582c1b402d81010101030043e400c04040e200745402490181da0580c1c2c0615079610001c1910400c02103032054451 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 250403462 1250 250402212 250402223
    0x103060f11030f1b07080f2107020106060207080304030201050f07030311031504050a020708030615090a06090512010c02060a15030209090303070230130e011e14010801060c 76
    0x110398210030303000c980145104620026000005141c44000130715244007007928411030b00d40c20802d00b000a00380000380c40000d003800840703a07120f214180040058040b101280545032000c42c2c10825140e40c1500b010058407400d03170076960290b540303050f0306540740034900000b800319805008040442d2030003000f41c8540c50007440c0102d5004240b080d2010341e0f03401951000d004020080000400c0c0c241401002e4000c407802d03400b10304d49211512248460300019050900c80c169501c9518030f03127480d807403e03101c1d450f400034070b41c1c120303141d50300405071054a0f10302c5070a00800700490400400781042c4504009100310303070081d100c42ea49212240b401030196184104007000c00e00c0380400540c58010301184101c1c0c0380c2c00296540d080c0510040e00e031005008040342120780e000080700303d04c0404131000150350b00c0410074545031000000c4104007803109801450101c075000000140c205200e01e00e03901d10000419524800c962903003a1010556414803042c1e000c190010f004002440c41007403042c40181c01034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 250404712 1250 250403462 250403471
    0x302040e01110304031d0603070c0204020913020f180609090c0c030706090f0515160507050f0a03030618060e01410111030408060c03101203021c02010509060103060f 73
    0x100302c42600d800580c1c040e00062825220450707002c40c040080201420b00b215240e041d0b24044100425110305910028025900411841a1a00c030354140d802c06040a21055498041c200b80f50081600010384102070322021180c407080300d003080c01c2151074401c0081c202022542d01c1484c088010703408030030b02d011a444104001e001042952041c928503e21510700102e000c415410464640011051494402410030080c4400d0030490fa0800100c80001c0c1402d41e2294150300300b2034180009090500558004c880c0714004059244c2e00030001e13503000840c072a114810b0140650119800740c02000e02c101c0e030440050280341d040c00ca030078158011150300040101d0a208d0608480d25011508500d8034405050079a20784d07800130303e040302c5100464020744c04c051525a00da5542c200c040d100c50f04401002012070410401e40b906400030f800304c0c8100075210354691400a42e14042e0300841e0b6486211780c1c030f91030141031040c010325010b645140020840c690a60b100c41c001080d074600d9200c103031640c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 250405962 1250 250404712 250404731
    0x5030c040203220501060e07030b01020703060b04091e0b07020303040c050118030503120601021009021513051c11040b031f0219021c030e0601171204031b05010206100302040e01 78
    0x30080c04814407481407001044062607e86082c0190201815600c10301d82411209009079074005140380485c0e420040200301d921142c070204d402400389400c0900340c010220b10303010780c203c030b030340d52004c98030340305081d000102e580c0c0c24030403070301d0f400f003170320300a06503150b03601d040109612070b0301203d844a0140b0080d00740d50380d4a56a0514640c042c1c1003208030704039040104200340d0380500c03007220101c0070b038002800284a00d80c0082c86007508880700c0205120f020a001200b0310741083d100d80504030262443d500304114115142884175005402c40305802d074640f11000a080501404860b404068000c2080902c030703a03900c9408501c2844080401942403107110031626801d4064040003c26030050202c5c0001c0c00f80e100e094240d452007207028542004800f070305480001a42604480002180d000a580c01d800b40c10f081070150800c1030a1194041008414440103014a01c5c1060100d0000c010b050f64440c01a03880740411600340050701c411240030005400c060700164901a21711000080c132182 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 250407212 1250 250405962 250406011
    0x1709060412061d160b0d060b040609030b130b01050d030309120e15031509040614011d100305030313060605030d0203071412090111010e011410060905030c040203 71
    0x116510240d40c403c1c2c41d00c0c0d030f02904242c210150b00c804003102d00a07015566208a07418803648417440b40314070101c000158500e40e120349512180151101d20b900c00c2e0389940d2240010407080141c00300741c503086644c03800b085039a6604810f085180e58420b4030701010b68070f04801c100088010983c160249501c0d61039241c0051100700306020503035580c0c0c6441c0f802690100a000c1c004034415070440c030b561020030900070140b941500030601e00c802120000420354544ca400c3c009071a422030400c5031203941d04e0000c40c0050710702d075040c00080c03000100c13800395a0381d811200d6003400940c40050100d800400110b40b450f2445e6100c402c510780510f0000c128140d035800441d284c4001d4a0881c0f005030400f00d2980b080226500c102e2034a218004000c05034543d545480544038072682081c54103001210100d800341d9202900400c12a80f1014001c1255602a4030003240c2447d003200c0d1400f010745070080103d02503018201040c02d0720005001014503004402c20311000790f2014003019090b05010400600541 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 250408462 1250 250407212 250407239
    0x609040906151d090a11130906020306010327110103090b0f0106030b060a0e060715020a110c010f02030f07050304031202010f05310611040306090c050a0317090604 72
    0x3208220034001920b0f040c495080581602d036410300d502000c2060081168000514032103183c0c210000c1c0108001d4100010950302e035807200d043c80c144c2071048032010302003c2da029611a01c003c9e2414000c1600d010b1810044c220442c86030120307101300310b4004c408108503420b554034030310041c1000500d1b0300041e1500b22646800315041d503d01c000c0303a4018040c150b03050180c1d0040f440213172499401c203200c107640545021103203501980240004036840c4180941d0b03c002e402c442000c520115665000b14100501092399172004130018810512080001c2d4410155905882003035400756081000d45e2591050592044006840c0c510042c040030002c65002e14004601c15400d030000039444441503200002e950004100100c660740701b0030350095124001d403000100001a08203101601c840c0d01c4c1a000070003500080c0c5502d0480441c021081004130307800301c2c0344240100c00e02c48031156500c04103c3c0d0000b03103000c010801c0a034034040e0381850000304080c005810000348007c0c20280c8071720050f000070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 250409712 1250 250408462 250408481
    0xc010614040c0302070503030f04050325020a08070f05010e030f0303090607090e0c07020910030b28110901050f043308011a18060a2a020a050609040906 67
    0xc98560880c461800b48600e80b00e19855040940c20520140c07240c83d2680401000e440607140008001410042c040c02191030f281700c43c0b0008003a004849821501c20b10450318200d00501144102007201117002031a4001c8444c905a03540b00d45080c0742c011140314400c107207020f03054890b40c1c013400e000da44140b000c3c42c41050b00b54001d0445280907000140443c500b60300c6203540198490600400c0c1e140312003110200340e01507030068a035868884407510740714607c1d0300103440c1601380c8041c0580c400c840c5040c590000103100b030540310314081e014034200301e07400102d151901400810801b0200d5004401038003074501107254150504c3c0d40c1d104c071001c00c1c94490b072004081c00280200500101816545081d0f82ca446241c00320840d0304265a2001c540c6285101c0840e030100403d8400d4210820000c196000902030100b40e160900040041c02c60071648200309403c0d9080e9889100c80190881e000c208160000c1c003042d0102e1a11082c0486980a400115001071712880b90704c0c041071150040e01250b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 250410962 1250 250409712 250409729
    0x5150c09010212070b0606030601051303030917011a01080705120c0304120e0a09022506381909051503070801090f1104091727060a11030c0106 63
    0x444121034002414080d00c80400381203524180a0300340072806891409074001416120155170703071900d0005890b54025402c9520604445401c08802c1503481003074001103401041e5000d09007140103120700e0a82e40494400d0b802003520701c0032600c40d503115410780c81d0044070034140607141c0100c3c0c00055400d944115002c0b40c60020000c140410440ca04a108004c03540c0d915100780d43d00b854200144101e504d5101c0c06006640201e000f9a42c2c000c03260000030484070807842c80700062924079111001c0c2031402100b80c1130505a500c1503901d40018090f0f9048141443c0841200d50107031010402d038000c00c805620300d2000c0c00e001c0420b08400a20401c5e02400d000c10760014000c1a0000705480e048140d013210550764103000e428000035500e40d82c5d501403a40c0c8000c29026032400500418010314410b40013810076a602043c94000784202402004c82d03000320a02e00c081075031284900030303001d0901030030160403403010003241c42118030581c884040c0306085010340745844807009401d800e55196401c80d828 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 250412212 1250 250410962 250410967
    0xf1407090315020a1209020102010e0a0f0b01090203010303120e030d09050604210905040209030c030a0c0e0903040510110705030715020f01060f1505040f0306020301090b04050f060d05150c 83
    0x10700001e11451010880ca001055140002e244c0340101041c4c0c0314820040040c3c1c0b40e19078501168001e400000c0d0b12081c510458103c45614109510326402da03103825584110310380300103d440000c41c005c4034103898140c2c580e400c84082c0d40e0411001000c10a4180210740401e00100f00b000000c0c3c05003001c0940150010004c0d410241094181d40041500c4100781341d42c81c0c50420402d070340008690003150740032a001070f112442c3c00c0c086030900140c150401e40c0760207a01d80e46000c000380003800b10141c41c031a5000100c65600d050350113589109901034550301c51403c0942d643e11521a9010341c12080007242921045503903940420310f402c856800a99140e1840030202d10035a504201c010007604000c0028065940380178000044c0f0b401d030b4080d080311640d60182c40f00d81140a1011107000300012005803c00716070b2802c00c0402034000380a00d241c21828284011001d2a043c01124080c110b14021102280c46e030744108208054a40c008490501401c084c2d5070081c41c51008a52048a0500e01d165 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 250413462 1250 250412212 250412219
    0xa09030b040b1e010e010620030c0601171f09060212010b09040b030114161103030703090b010e04031d0111010e0601060e011106070e060c01090c0f17030d0f140709 72
    0x200800c0222100d403c1d00c40888004210f0740465240542c1120030a050030500350701c0039071004080d900e8600090030356220004085008200000742241240e03035080044d400031012480041e140d40952070700341d00c035141012064101e9221940311a10346481940018584413407480ea00b204040c2c264403d400041010610324140d050034010008101c41c101c0003045804042c0d0b40e40c040c1c103a00134080c01449295030701032941c064003900391502c0d20005041180c0d102d16105400402038442072604580030490080000344403018260024052945502e8140c1c210f100180503502000c03030740000c00c2c100050004411840710080c450148250480400f40410b0341c18213801900512401e10182e041001031207a40e07510740300100d00c040d00701d4a0340c94100012040c1c0800030710300d03000d0100300c420300b54a4003000f10200305250780c801d01141d0b584108901c8040e43c0300c00441020013004400e2241d90410891102c07134550607400145080708038603001602d0740c0e51035054082150100d44180120341e4180061 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 250414712 1250 250413462 250413481
    0x601030e010204030b011703160f03020d090501051902030d0f0e060709060c080706150605030f010e16050c01062402010e010209010e0907120c0e01091202010c02060a09030b040b 78
    0x20400d1110344002075240c549143c1c0c8005407010148a1441e0545425005c404c201070140100c44003508034400040302d1584504080302810600d2108034050700ca5103900c48112405500102c04880050b101c041c20007100d0042030401003d02c503480c2e021800104900c02d294034052040720f416490710310b800602c80d50072140319407815901070610401d1085401c4104645580b0001c00541682d02480d442e45031030680c41d014014200300c0f144c00302805e441e1400070810aa000c005103100358a00c104821032030340c0c2c0340400300d01160192064800e203080c1b81074450030303a40240d0041c9903030013542c000024001d580c0d4051a903a001a90103a0b1075040680740d618070620760902440f164a40107000851030401020006880f240b21505c5031030241c0b1107100090300c00d030301680c0088030b0404c0d480c0f002d0180c03090050008100105841d00280031460301400410360516441d681c0c10310f0341d410b8580350416034450302000895001000d4600401c001c85002100160000e4205401144034120030001030804c1d0001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 250415962 1250 250414712 250414721
    0x9010902030123040f051204030b060102011802010e060a0909090c05031522050c1908240106050915120a052206020a03110c2404050601050103051302030a0b060103 72
    0x51121401c040c1c10310f9880c05052001c0035009503000f440300c1d55100316072500a08000c452480489005c0002c540003050005c0200d1003845151b09900030015035540108014001f40780c5003010b40000c880d40014102c0742068070042107040418104919031a40d00c1e44c41d54107543c4560703022038032112190001c10a80c01c0400868689a0103000480400d01d010780400b85000c15520b0340c004004034102d20541071101c148490501d40038041c1c0307284841c03940c070141c05076240d60394420f41c44684945500c0c80c075004940351300c0078903000c8611149001a440c08000b211560011031009500100b0309504150840e400002491130f4100d442416001e45170119001c030031164010a60b03c2045c101504011307400d03805280c5a07203800c0c0e100c140162901c1911104800034030900007100c5d00c070040000c2e2959207990008815040010320820000221103981d107410f5820800d0f0307001130440d031001006214541c001d420981d4421602072440c00d4071042c680019203461003601d005c0d9022107038013040c4800355905009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 250417212 1250 250415962 250415981
    0x518121303050714011701060503060d030905040c11071d1603060e01060804050607090b07170d060e04150b01050703031a280501110307060f0914030a0e180f040614090109020301 78
    0x42e41947d61514001411906c1f00410b418404c00d00540c0e20400c1500440f0084c0203000054403c104060410360050903803803d20f21070840c0d0b482900e10000305031856100d04490140c40b404c2104080d11450b000f1103d00003000030030014181c5910000c5020450314008500a000583d0340e8000d50415007005400d14401600178030410640890900621420400b203c0c1c0d0715a2204900c01c005c2031000002c403141c02114030404d500c605007000040d08249002c5914000c03809001061001e0070210203110444805c02101030104200384010300119000c1d44c40020079140101c036800080d045a000503413194092014441140304a02013004000319808040024000030b003010701070504d03501d038910b0340c1e800350031030041203c0e0b10740407641d2541c0541e0300400c202c15400282c070b035031000c42c1c1070406880e0f4000103c1c12000600c00900c6100924184400080c0305108500040d2244c4412040c4c85e1f040d44001d0060300e0554503070441c4100c9529030302440e4411101c06c40009a1010903204141c29950b0140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 250418462 1250 250417212 250417247
    0xa03030c1403073e010e010b0d14010212312a0f080a02010824100c02131e0603050c0103091403030c0d051812130305071401 55
    0x1c055001c8804040c04403500401507082464032181880109540c0140301001a07400c0301e00c80492845107640a100c044061074044020310050451444190894441c1880079030701440e030b0f0301c0d510040752007000200f224802c003900241c43c1200074503442d055400c040d0703140d180c0e504c1c800c0300008100c0801d1b4860100c0c3c2902400950032580707180c83ea101d955000c00d4083d204006081c2030642096241401c480c02410fa00484070311140e41d9089035500c0f5a0822002d0780410380d04000500445415007000c80451050038241d1140c0c080282803140c0d01d0082c0000c0803c0c40256201200980d444a000c1c59680b1895007001c0384034824216180382044102c5842d690060078220284000303080400c003c1c00890007031800140049007800c0c40c0d501c0c8503404800c803c3d180400070621810600d00002000c0318904004144040e441d40104001c402c50340300c1046a10780c20810010000362240c074018080c0010030300c108180c0b1500d9840d02400c201041d484100c2441191400d00459608040200001301303406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 250419712 1250 250418462 250418477
    0x611070b090c09060622080d030e06101202180f0412030b0612071803030302030a0b0d030e0103111b03070204050705070515040609060204060203070c090c0e120106030204020c0a03030c 81
    0x8000300c3d85001c2d0150500b8480c99000c1980703260040400b50848604420310f94181c1003640d0707003100540325000c01c1c01c0030001a0906501a0b10200000354181c0034058400c010030003507140c800d0403544c3c2d46511004982c010250980904c83c10034101c1e002d40501c05543c02162103041c0b0789000f1a9008403072007070f8820b046c2402610a5556500c0095800d00c05085005200710ba50b849011552422003518207160380001180100525a041e400382d03120b403c0e280c40030040d50504c0c07030412a540200a000400040440542003a103502c2500410b2988031113a0741710781000c100300c0108510300141d4191745d007254000700343d00041d49410b00640350021f000d030929514002d02600c49644403281080240480588034000c80c0030403606a1140002139000001151229101c07900252a40d004040650780700044000101c0c01452520441c4601091519001c542c0d06519040c00601d0082c00c2c10380c1025540d1304000000342e103030b0380014020003485101800c4ca441e8980340280454135822064420041c18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 250420962 1250 250419712 250419733
    0x5010e0d09141201180503030f0624181c0213050606040b0703110114010617190e030c01020301121401050601020304050d02031014190e030901110304030611070b09 72
    0x155900c0802c201040e90000842c1c810348030f1450151142849031555549031503d5241400300200c080d6005240040c0300001030303101d200400c41c10a0380c1160382c0310714000c4078414440c8c803540123000340200e4a000306100d2030800041300081c3e0f01200c90300300c02240751034031030090300f1440c2412410300c2015007032800f0040c030b082900c0803410742d00840c014541810710000b540414103018410150701001000e00912540c207241d21400758040b820312409000c80c40020f072050030001d011030700d10b200741c00e00604450003030b810713484035005000019220307021030004018241c0d0f9014280015400307015a00705000c5203454515000105200d220317a240500d91400042c800700340c0e03022003200c04440c021a088030074a112400005d04099203103100807541880c000c2c2480301052005c09040c82500d8049010307402a01440c400c40a41e01c49607162040e0b82c00400ca5812213602512050341e4040b40c2e9030449040c0b41e100c2e510202203440107040740e251071a0200740481080a40502d0540c842c60502c0580311102e10b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 250422212 1250 250420962 250420979
    0x3020d0e15160f060e0c150a0804031b02030123160503070305040227040204180b010b1e030a05090c011b02010c022202031905041203111605010e0d09 66
    0x2940351401e0480b1540e40500040c04074860040c42c0c0c82d40c20a030b08011482042c0d0140750f80c1e048410800d4095443c0400c039020f024400c0042c5d83e990751103070315144041c0d9296074089a42405590340382220007007003960b80c00036031801d10404081040b210b007c171000304100151080300e4a4000c181400b000f1854050079401c40d0b1007020790303402000c5810007107250b48a5100244c4102c4461190418800b40e010002124a080c850703514042c40c020755080242c004004040103803482404006800c40b1450ad00400481c15954014080640043d15020100e0a1000301c50007651050380c04440840c0c8407014800701c418181b0060500e071704242400d003148003440300f15048221b118030010f414045024200ea055456060410903220803007000303401c01104800c040c0e0000c1d001582c40d0402210508908a0360980724802c0354011501700040c80400e5141f44c800328040d00030980025440f4030140814151800c41d25003415260b4030607400404c0341c022070012103280003044080b20302080320142d401c205492 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 250423462 1250 250422212 250422217
    0x80c03060412080c04030812240616020310060609081627060b030a1416050405100507020301060f060f03062304270b09150609180a03020d0e15 63
    0x3a242810f1020350f072140c0039a4034500566001410780780c400503c241c3c014000f6000d1511407609440e000080030095510310940010702d880c3c1942084041101c0d81c2d448090b4030100912610040c1100d540340c2e4004002e809641d03450307014802047e4440780501a084c001d003c025021000035505d60003c82c41c001100761821001c0e51034210700c41c0000c0401682d500c8982020010304400b50580355030313040c0b1002c0700f8000c2c0800c141a400c0c482903400032685062560085401041180da5501c0c281800c0c0010401d0022100c0f00020038010108041001a1002c1c0180d0703004110004921100506d01340d000340c4904d902203c482e0070145083d90a200b070b1914080c48502107070381202c0700c25855039424003007002404080b181c11199034103103e100a0ba205003049074480c040c45541c240c00b03c1d032142d6401c140c1e80c01600c6259413404400200199031818030040c515400f04000c030f0b081d94003001c9500301e1070030007031543c0c4141d0042c3c1002241d206407907080500745114120988500300e0020310220507400d00e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 250424712 1250 250423462 250423493
    0x160b0a1107120509040921020a0506040b1306090f03080f0403021203070903080c0f1c0f0c06090b07080603060601090b0f03070225060305010b07032007150306080c030604 75
    0x115002d01a40c0c101407041c4103945401c4006001004403080c9400c0c01c81e0b51880074a840382d4007821400103460743c02d201003507603200c0960040081500352a250766a0b2902400240280c01c40d0b000100f501000c182c1c9030107a0314010380100e501d00004015410010901d8200515070200410b0b244107106c0083d81c0001d0307000c27101c18440c00d103585030380b10b4079411500f0789481c0d4070203003840d02e0114000751101004500c020f08104c0d00000c40d0900140840d811f080d9143c003607100008107410340c10603d030071801004103030841c910910b00080c407110307141d03680c0720790030b1041c2c1b0b0f10340002c0c44d0901001400d060420140390000740900b8045282071a16014452a01c030364515501c8511012010030341040c000c106100180c040c00f001440540c10808110a150310705100b8100041e040c10000035802c2c0016044421007505540c800c0000d1140341007840800d60b542e48403825911445400149100c6000603030150301d4641e54000c10018685a2810714101d0407041151103600303d01c040c0000140c281d4000f8860 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 250425962 1250 250424712 250424723
    0x5010e0126091002070501061404290120010203060a0902040b0403080c0307050a030507030f0302090f04230a02090f100804120c0812270c01180b160b0a1107 69
    0x207503550000c203d06040003141a1140b540c008510303c003c008064200c0e1060341d0000d54106c1c13641c15080100030940700f0700154008040a5002d011892018140001d0400c54060500281101c045148006564014100f0f08603507540032042c0f004500d007101e200c030000c2802c03a00540c03e081c105030f81000c85200d04e210051084000181c4034500103014000d5030620354005055400728400d5082c0a40703640d00001c02200007ca02e170854040c000d01038402e40704d0346500500307039100000c20002444002d00c4400251441501e1421040d602c0310408030415104001062000d40c440c0c1c003480a2203692170708445103138400c01d0004801122154030010041c0d206070081e0341c0d0320202581c03450a9603448a1000c0c06880c56030005090710b007480c1141c540300d020391601034012080f4840410005418202c00000024982018161411a62140f0006034500c0f0f00c1290946000b950b54595980e0f662240141c0320b00039400703030700740e00a002c1c0d80402d040c0c0c0507400709010300070350212500d00300d000c2c883c25400901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 250427212 1250 250425962 250426037
    0x70201092a0504060f030318152f010209040b0312030403200f030702010f030e1c051c0614010518040504060603050a0308040605072607030e0d05030105010e01 70
    0xc5401d42288650062801900400c2031685521902c109084640400e8000c134491600c040750f449417600508044442844a100f030460100d072080300c0f481032407032404040d030211505c2180c1c0b8203d00941c0610051095000607510152030080c082074030f1804220502c00e07040044001c2c00d4101e1001140c1e881a4036181900301a441c06c0e03c40200000d054109900d00d2040d410f80c9200900d0004c020030219000362110310440c03003210303000c900b81c60720603504d8046038201c000d015065141c080004444d04080341001800d04500021440c1c0003010024052012030700c1b184204002c820132203207440010002e01c1c09a00c0d241442e5020f04a150760315410b01c0c01030b540d0310001018007050703900400c083c0d03920070155040c10440782401868444103803005d90f203103450040400c0145004000710740e1003450400810400580006c10030b100c2100061804041c5078950285482c002e4003407240d0600320f29940c4440c3d4403941804001002da404418000703052010b4503801c0d28003d1407410743e0b0060405811040c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 250428462 1250 250427212 250427273
    0x30d120e01021c09060b10050706050a0605030a0302160801051006050a090b071407060f0210050a14070203180d030e0409060902060c0c010201110a080f0702120f0301090507020109 79
    0x1070080c4682ea07001c2c100085806484030602e200341c0c000e824001d00078042480841c4882c3e00300101060034004103030204a0030040c000014041d900b00e1503101c41c03100c00001c1c9560360f650210741009880d810440041c0c102c0c14142103081423101c4118042c0240724000c200620701882141040359550242c1c03000e01402140d4900702510a140e00f802414001c1c800c84d44404051403d500001d41084a020301e0f030050007008540c1c5403188000035404005617006102840748250b810000b00005000303c821542c9500580c420ba00300c50910703d0081049034020345d612103602011901c603254905420340314070103005284005c1b030350095440c0c40c1400c0c221000a1010214500100207213070805c8002c3d0000c1010620f0814042d020910019070701080c1c0003841407440d842d0b0b030024180729a90072240821020310215010b0001c1006d0140d0251440c0100c5060303044034110f00125810840c84091340600001c01031046030501d008542d08418940024050410150b954851003d124104454000b41012450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 250429712 1250 250428462 250428491
    0x31208091c0302030a0e0d020706051b19020109080601050a15020c12010e070e012105070e040602091005070b0414120d02031f08071a0d0f060501020c030d12 69
    0x1850074040026145115100051001d0b0103500308981c41103209250591502c18480085401c503107040c1103a02401c002401e040d4282c8940d080307400d013409000081800c600404108005e1140200700c0c0c00d028800d9105207100040c60594a50010980d07074100000401654807443d1010056404143e41001014155070040385090900c503400d541c03040c140c2010b980c0000040d8490540c442c40c40054030815901c0300041c1c80e611600780314070203080003140c030b0404131085284030300707103407548224155800c03699034020040d020b106c15507043da0300a90004240d20b5501e840c1c2e000d80c00d09591810000c0c1805260f840d0591000001040503004556070065420b0101092046118401500d29400d40741c0a000c5034072002508111050780c8103100803003e0450250350080140200c0b841c98000b03109150802d1070341904060012084900000140b10144d080300c4940900f60b03a04d4035091000651034900f2000a103004200d018050094210150f03692140740d20058400b0264540c00c40811610074982c2ca4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 250430962 1250 250429712 250429723
    0xe010503030c0a0215250308072c04020f030708011806060e0f01020705030312010e1b0a0302090103020d05040f020108010902090604060c1707030f090506190c020a05040609022203120809 82
    0xb0010074151800041c92412400e244a2a03900072354400140d585d8292003500ca12011600948a013a40703000312140000ea0b910310320100020180001d4180b01481050040d160426102840441c40200c010703c10800d060743c40380d140c44d00150060016928080000d0001e103051100c080c051081c201c1c1e2081c00e81d0003005070b00700808016080300d94501060320390500c0c500003070080031070b00100c2c0808034001c0c211400003900c4102100c0c82c404d24007222010203400035800040c0355410b05070244410000c1458500c07940b4801c1e4002e00015002541c148001049828140c2180e1403280c41072180c1403441d110b2000f0369066400342d08010b03001c04104d081042d03440031070366440c4003401c200280d103608050380600d07482800240c6480f51194261100100059030080110100b01442046405e0190a00c14000740f1620750001d8040c42c8100d44800201c0c050b11000d81041401c190000303004c0380040c1c00701f024000c01d40404050a4060b6003582e55500d103207108000741078208001ca9010800e0607006105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 250432212 1250 250430962 250430977
    0x50d0203131404110f09010215100e090c1c120c08040b0d0603050a0302030909100602060408030604150e09070506031009110c030406080411030a150c050c0106030b010e010503030c0a0215 82
    0x903605c44080c0c00c19414245e001d00100c50041c043d5400001009400090180c00b44c4c0e40440d40c40210b07400c06000c4031800200820401d980e1141c0c0042d011140c1f1210b040d20f240d40c9503100301c0300704100d0f241441c0000e484001c2c010400c0100c890f081601182200040d0f03429148040c1000340d031a841030b60600d0180c641604084c0140c01024894010550008020701c0b030144252081034196807601e0500c0d0260700c880c0b0a60025800540000d000541024002c1d540031030010400905030700001d02001c0296441d800c44031040541205001c2409410000f400060000b1680c1c1880d510742040b00d60388803401481400880c1c1c1d02e41914060300c17007100081d0380c03a80c601070048a445d50f50f00c520081c01c04500b61410703600c00e0307410325502645080104081d00055004180840303040c81c2c0b00810002000d401c0c420031304208081c014908034200a000c0c0a0044d8042c264003241ca504080c5030340b80c10041030340030b28466071003084141100c0c00f000c101040c5594040f25095240d0b480c440044c0c02504c15503d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 250433462 1250 250432212 250432241
    0x110a0801060f0203071e06060b180904140610030b01140f270a021827100b0f04050301060519030b060a210312050618060303070605090a050d0203131404 67
    0x800c0000030900c44c94010011b140240d00600006035100c080f2001845210090300480340c40381c01d968102c2c10305800c00da80151041c03c21011a0240c0030f1041d007012401c1d1855501020504010018008035000312400740450140c5403943c030071000d001820000c0300c0108035000d07400d880a0b40340c40901d40d40b4252101a00d944000120385010030080e00294808a011000c045440f0504210303414028005000940b001701641d800c6980721241400a220041c688845580e200c030b0081203200506018110948022140546480c24602090f00303540103031308520f004030203030003000d01c41110014042d8212a0043c2c03000381c00ba11440042140320b421384d0014a0310700c6401440c08a030440c2041c01c030000b90f0081e558184800344000148090324001d480459104e62880d400001070410584144d4000000504582c0342c0350035959250181c4604880c0030103c1e40018040e6420b210083c011079070103400c648050742c90051100712501c9e0304110341c010103034000d1903542100540c1d201c40c0d01c02d8543c1003001d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 250434712 1250 250433462 250433483
    0x210f0204031401140c0f030a0b1e0f030a21110d05180904020901090b040212070201050609090a0503030a0218090a020a030e0f03071e0c120303110a0801060f020307 72
    0x207003401a0061800481c0b01481e601c2c2080c40d0704207829806401e40038066a2004500e0400c1905195003150006004810035a581e104041c000791340b00b0380640c40c240c22403041051444c0070b401c20480d05602510010b4060b400c07035a0390070002030031100c144100b00d0009031002d01c1d654541400312005100b40b02c04810f01e00c0b4105112210f150818040e00803100032882918441000d0301c144a0100419100203401600c170400600041d049600514807000700688010b0500c405c201103403407c03910036544000540d47da8420300c0801e0420104843d8440d1111008004000b1241e840580c0e920005209421302d83d804103002100301414880300600000003000e130960303401c00d0b49111001358000c01b0b07600b011074909050002c180c2404641941820131035070285050180c551a8042a5503090a6043c50400303864481e07000119136034031110207410010402103c031070340ca00e000f5080355038005822140041c244000342030b05034044100f906403809450301440c610381e00342c2c0076491401012001030221194 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 250435962 1250 250434712 250434719
    0x316032007150507030b01090501030b03030d15030308011e030f030c020d0c080d1d0d0f0f030e03150105400b0f060c25051206091c210f0204 62
    0x2007101900b4080d409001c12007030300c0d10030080d411180c0d010700c940d01142120340b0800035036000358403c04036583c024080d03928084541142c64102c03011485000b03044286102d05001341907204c2d0f20203000d49455110505040d81c0500d000c03019410a2100801d00c42c200032064040510640c050b02c1617540c00340c41c145010020f444c0c00903100c2000c0c000d4200d18861904d9000c5458400c0245a9505071003903002480c076400b860500003070000c4407005862040a21200c070340040c803000c00f00b10078540684d0b2144400e000c0e2000701800c1c03801c40341101014410202c0144440d68130415040c020300ba00d103004480c2e01200000ac20100f00c034140c000000035806030000e0103510781540041899580888030240c0c030001d1582000b205c1e00502020701240d51000044500c070040c42c0354400101801d06514072241c540d94000903d03500c2600d4000341d4541c11800030f0003140101002040000e4000b480c40242840c0300344002000e0209002d502000341189040290b0100303242c0d0700c100c01280c0d01d0034055503206c0c1c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 250437212 1250 250435962 250435973
    0x1205010b10030b09250302090402040f0e010e01321f0201060317070c2306030a0c180e06040906020c0a0803100e010b03040204230106110d02030316032007 68
    0x10490f280c030302480a143c0015a0b81d2400468861200c000e00170b8010382c000f03820401c500a4000c07101440d00554200b001050079480e600c0c584004044080440e40158103103843c0511441c0706034000d04051024070900070a0454201d04079a24241c00a0301804507442800050014101c01028000103a10401d662500a5040d00702e60306903405100e0317014031401020786080e401e1107224409012542c04000c00d1140c6049600038010010510340c0c0d4800324142d04000408607070080c0c4403e140d99544807049070001c2d8000d05646d840c1e410005000d12114a0500c101e502d2440040400341b007203540c0c030040c404000b10742d810764602ca1950b0003154401740382450010b00d80e5005a821294840700708600180030707172580112505a40304150401d065884e03650038040945001800031001a5000e0360501e0300c200800d101500a082d0b950f40c0360440400c0210003400c199000700d03c00d04640041040241c04120120b150062108614001885100350000b610a0754482c12490480000c005500003d004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 250438462 1250 250437212 250437221
    0xf3f120f0f0c17010509070c1a0612030a140904090510060e090604050d05131502011b030209010207030b090a1505060f040b0906010309110604090e01140f011205010b1003 75
    0x1d945060400003a0080101518214040410700000e400e80000500003801c000141503000015401e1a080c0550280d841c442d0002c075003000060400c7d0a201009120705d000070151080310007490186150051f000d2008088080c00301e105402d464000520614640b6a82c1c080c44040d0340004c2542c0c00c014a803e098409401188078a5442c10440000308104180108981d4010b6078410020301340d049450400741d03065003140c0005540740e5100034002624203c220300f98540100180c0c000640c89445803295000c0001c6009032804043c418070150b0f41c01d036000101350301070f81c0e0880b95030815a0345041c0c04514142103a80020031802801d02c000402d0300301c5400840c0600c1086411100010100090004842109110540c01911803001c20800c2d40079600080e04540140000e1500d54088004502d5039849640030b429226070324205030302444420712400b860317107103410311410a60412178880049194180145481c4940c4005948104802503222400c1003001034503491028440040141c01031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 250439712 1250 250438462 250438481
    0x303042406061e050c071701091202010b120f0c01051312031809050601120207030c021c02030610080a0312060e190c030903020d0c140304030f3f120f 66
    0x38281d2081261032180204203480b82c01c0007407001400c050b0714041d82c290208001d081f10600715540e079401000440d540e00c4070020200b80740d4002143c074039000303418410140711410030325a8036084610703180c00800010501001751002481d100c0d45a91000d00c00305407200d80e039401103001645d00034400c0c0c00c140e0003882e031014105c400c0704158802e60b500c100c0e000c11b40700304036440c900244c03d05c80c1c84460305540d070340613000407802031910203454180c0303030302140e0488800d410504070240040701d45e408601e82000002e5010f03da49950345030f49460103051642c0c44c401010010300f4004400300841c00d52002d907024100601e903010b034450150800d42070380300032a05550052200682490110070f4030038003074000d2031f10080c3e15500500b0211450001150f11094540e801c4030400ca00a00c200c891090070000b0700090741c01041c454045013080d2501c4d5140d04a0040400e0800c031040480c4007401c00b41c0604c1322003003903246900d008000d250b228100d0b01d80000c4400c0300e000d1490200b88820b40e4250740c1c0501c020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 250440962 1250 250439712 250439747
    0x5190e030d051f0602031e0a031409010f0e0102070f230610230109031b08010f020307020f060403090303120b030303040c060e04020f03012303031c0b0109030302030304240606 77
    0x4840c4c89880c120b03124420b100720141c180041d00107080e200c0a0070401810307018400c1c60700049034005610f54889219007030301c00400d00da4407144095900c4c07041c4e01c01c00703000040d8100210718010195544411403025620b02400240d501c1081c4c141d40324600d14040c255035100b20039900d45160000941d29021454050100b24050f421502d00c000360301070780742c80081c44058644445080c43d607651340301c40c00300c0070000060b1444210310008101d24240140e103c00b24807460056180c1c80c10314402464500c0300e02100d880c1d136000c94148404250401000010b40f60145085008403007480620000340c0541c4d014144c1610000040100f8002030f826444255040b56450182002900d8204030030b9009031440b012840c1d82c1080104000b00241080321030284041031900388040b80100002e080d0b8000004c01640700c0f404200070316003424188112a8201c04c2424041020b500310b490003507032400002e10040002c0210200c225141c00465a0040b8805211405012841e00c40800a00000045070066176 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 250442212 1250 250440962 250441021
    0x2090a05040b010603060303120c0e0402120612070f1e0509040f0203100b03280f0c1401090b1c060302120a030201150b091005120c09030f0105190e030d05 68
    0x400754801d001c6c0d00d04403500f41e581e491549900c0c2d2462001030110f0201d907018084052141e161030b4a884c0003a244180e130311404000c4510702001448640c003945000300780c86d40c101e210180040244042c01d6015500103001c41044242101e101d000010400e03001158018907001c10442041100a1450543c0d4400c0d8241c400c0c0b68003032901c150550300c0d00304029038550021207110b24000003030106001c0c4801240740c1d04c40d1900d600d444424024a4080c010744075445400400e10444100c060000301600c42813800d00d0700d081c9880c484040a0242141c41508020280170301080c00801e07802c148095a00201206503c1c15003100f4190f0b5020185001c85c055400c00c078400c40000c18203604842100d6450304610b103410242803c0189001c541a64001031000a100c0008041241c014240c0718040c00c0b07074202e50307070740a0b0420580f6080351440d100b9111307070529007040b210030300c50880f0301070803202050302140c0d61a07002840c038118002c0b9411a0b070207502d01010401800074018602038030b107003642002603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 250443462 1250 250442212 250442219
    0xc01110c100c081824060316050a09050411100f120b060301090c02030c0109080a0e0d170a1b06150f0602030a1209060f0e060c090306060d0f02090a05040b01 69
    0x102507904001860011441d100b0000d50f60303400c1c044d208810500030609a503c0500c48506641d03c1d40310310003056910030661800c000d00c6003030402c04e0740f906602d0300140b800207034603080c00154001101d005504609848601140c00c02054104404101c00010302c1c11031080c000110080492a0a2040344000350300c8160901841055202d200034503c0f0260a00340f40d68209440301015140c0c2c0c01c6000110312041041d44820742d020700c90500a2485010515a187c1a089001308420800400c0728402e00c0f02d0301e482c00008518030150222524200a00340d21852a0181901c99a001e5045030701c605c0c2c42034651000700040d680c004102c21901c00c0400301101c0d29020201c8501515000d6400540c1c410401c1c8010070740280e440080307994840c44042150783c0b0301e9071941c0c2030b10314000140702940c0d1140b044c0300d02c1c0c00d0180b196a60085946602504140094002940e20400940028001c020209402060111200700321b00500c1e00640400410704182c2c4140340188406c03503042c1c0c0e02c801d0307150011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 250444712 1250 250443462 250443493
    0x31e0c051c1e02031203060328051002160f050705030d080103061a060d0f2c070e0603070302270f010608150a0501081e07090e0604060f0b030c0c01110c 67
    0x2001e0b068015006200002c100400356644c2e074005803401c0d41c0340c86000032030070155101c16144814402d4150801d20390009a182c0a40b4180181c80c181010500610890300c01a40400d03100d0030311604011811301c00080c5040580c148103664010580500889007070340a00c1e83c00c010500e040340d108a80410281c0d482c23414403004007100ca15225030044041001944841458100d001c03026000d04d000030707005281d015032640e4508100750f0305000c00105007208030104014860000200a001200c51042c901000003d440b40031701c1c04001e100b640b41120b0400103400741c0060f100200100c00f59a110b606106d40d2800d0200424450000040c101c04002a00b052042600f8403c421000d803240c1b61050401c80107503210326008180724104030402d0702a008022041e02d01c1c602844658943c107c145060101180601000a101c64085c605003c402c00c03420400c06105022542c00d421425100c0d20381c21010f107820310828003c401950f09050360034840303007241c1005040340080e5001316403100141c965003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 250445962 1250 250444712 250444763
    0x28030e010c0f110303070206071112042304060501210b060406020c0a060e09010e0702150708010f05060c0307110d0501020c060a0506041e0b03011104150f09031e0c051c 74
    0x203500188c01c40400b003104c044c003440000380000100c0e402c1c0e44000411400e01007568016512284c51a00100da48035608000941000304003203050301c05000c11402c040000c3e2040030310004d070101c55841181c1c2c0801001c490f80c808640007400501a694466561170025500c03c0000384640c8151440d00001403490300851240f0004140500401e0840c0c6ca400054500e08600816171b206500139036003480c03514902d80c9417840c440c01464450a90550400000102d01c468582209005040411040388101c034008180c4109035800400522280c00400104541200e400c1004101b076002043c031800c6601c0c082000307480b95a24400c10070650361400308000a41e50031880382054500d180b1041000080759402c14846c1a030060000b00c1d045240031a207040c550301070350020b062000051214812981d010403035030042c048520704021080c2c10b503101e502d480e800c8848000f42c0c841c0300079018010800020103050041c45d0041c0340340503296012080c0181c078861440d003161a4180400c3c001d6000c03102e0f480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 250447212 1250 250445962 250445971
    0x4030c0b03070f030216150501030b1b1b0f07030305070605060603040305160c0513090605011220011803050c01080a0e0d12060302270a0228030e010c0f110303 70
    0x3140c0741140ca10280544c0254003170ba4080e0100324a41200202040c4c82072000e6408102e040c100040079131441c14034800d0300304054905500c0c0e520721284030700c8228124003a40d4a54411441c0d000010501c03514852500e5a51111541d490294140001c14150040c0140c082180141c6050142e03661702010030040d88800c64004000c140140140038101206007100c0e048188200d001d80303d550388840c00075110100040078044125119002d071002c000320745c01810300402d01c090a08403070342c00e550355103268000d8510315548124a40d240002c40e50b88107410556080703a4526007100031540340c0c01d03d01d0f01c130300d4902c003614040f41c111004034078400e119118503203030361642c10064041c81c40d80b580308540e03100048a0402e000d80d2904008005680c035812010364182400e85140718a21401c0c9040b40803100051008450b90301c103100075034182c5e051007080c220f800d082c20303000045009000c2d070640c020030603841c10000d550320b44051414426044122840070031000d071035400b401c02c00c28402c20350304d100444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 250448462 1250 250447212 250447217
    0xa120608010e0f01050a1b0815120f070806010b030f0903040b0d020d0c0e01080a020c0f031207120b0a06030b01050c0a030e010909020708040e3c130b010302060c010e0105010b04030c0b0307 83
    0x1007161f140d107881205020341004099560041092000e40000c0380e0300046981d10b43c00e80c0060060074090181080840d0041024401400c00d941c5015115401400b00138040d9162840030b10020702030903000d0040340e001e0070515407210344a0564034442e200371b4005040b4088200c0c0340a901c000412700414415100200503510300703015658140e480000780d0003002c040141403103042c2411200d860b00740041c1024186020001d4464501504001d00e210702450b00c44640e6450442200b0054031800d03c11020748290381808a0008404c0004071000c0c401e07859521480d00841d840c40c0c1c20181d00030009140c0400990742d02c40003d8032002002c1c120b00c039401004040310401c00c0304001000c0001c2003950300c1518071f40c5e4242140d41d0044a2650990004a000c1c4000091101e04801800340c081450704903800c2a200d002441583d42c40011180d0107020180c0f20340c00c04528160000000d4200140000b000300082c425940e44450840650700f0900040300c480c0710213a4003181c07401140060300d10403141c1e82e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 250449712 1250 250448462 250448501
    0xf060b061c0c0c080408010f050117070b1e030a0b031e150612120405040f090b07141308030304300509210604020a060809030a120608010e0f01050a 65
    0x40c000c100800d02c0146910610254001c48404035080501800040052900114460080c61541421600143c00403001a1504000220805000a0780c1010707211550700244d99000d0602440410f40103440580408040c000104a14154144c0009d068142c040d03003100c01d007507525030142c0380c140d10308140003403598408540d4035000710041e51095004500904101c0c000c2102e03400391070910080204103052074400040803c01424035120f20002a002904100100111a9120b03042d090001c0c0034070b4100100c45042100c03480c8960102c034485040ca00028120325510f00d01652617030400c40b401d541920f0000c030309000c40d9000d1403010f10b03003010103a10844d181c03503481000c0d1002d1304122080da03000918034008100c040c0c4503501c44161980e1542c000c24591905104002c83c02a586c0c0148080204040610034560700000588250000c6c43c00e21500600150208000600e1248e114895a41c20010306070f61b1507001240d82c1aa9100318002807010742e4502d00882d054407406100500c03086000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 250450962 1250 250449712 250449757
    0x6010e0607021302120f090303070903150f0204090c08100807030201080c0c1912180b090402070f110a140901030204180b010b092409010c08040b070f060b06 69
    0x2000400d040d074401400c0195208203c111a0200d8024000c0c480c820014401030014054032225610b520060074402189182343c01100104600075900c40100003810500b03401d007014181c0e0704074107090311641100315100c4e13547da041c03040071b07000191070707100800d00000c0401c40321511b01d1424001d541c0008024502c5515542c011500342b14000d00759052280d0034404145100e1040c04042c1c080c0031480f04000c2e183c100c0e070414212013014030700c90105100e14089880403000c0b0801c0d41c441145c00e10290305459240c400046000380c4502200280f072283c8101407041040368a03041300450840039620101020380300d48204004290510780d9031740c4039030703814010001440d0940050025503941c81010109011558400c042010f080c3c2000201072800b040309840390134040c15144564841c0d01000101c00c0b032100c007040081c407800da803c604104a240f40c2c80309105580c0125001020f40c100d8003507954145062003420401100401c403481410403540d08010300d812008c0e0340c2c20503622500e100c4035004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 250452212 1250 250450962 250450969
    0x180d080f0a051b0601090c0825020c0310050a05010501050c0712210f1812141c021f020304051906060b040902070c060306030804150e041a011706010e 66
    0x225020000401c401000032458443c001034488a0000080b4001d0425505001d120f2054a45105075003007000726500c200b00c0b0203400070642c1d03062007000d280f40e0141d13148600310480c00c1041c5078080a4261045581380e090140346a8002842820054001c0250fa40c0704c2004481922545003c0705c001e40c045c04041c00243d21501144902c0ca1044103000396491b41318031340640f1460002035107004202110102e007100c2e9003200c50204241142d0f2201c086607414034000050710041103102404a4411011030203000e0001c015103035a2006c010025038200308d102000030b585942840508504492296005d81141410700035280196030250141c08205400d40c10f00303c0e4281c0e15030090300c11540701d420005071102044010005041c0d60500565180c0a90810b02502c10003075104504042c642902007011031259429207007036545400344040240c80500342114200c1c2c0304450954080c0c9000350400000002400c000c804103030a0301d52070200850800b00d00d0318600103d6041e0b0200346c40c40c642c40c01500d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 250453462 1250 250452212 250452217
    0x3080c03090a030b0a05060105160f15020c0d02100c0e0d11100f0e030a050601051003060503011d010f151e1e05120c010c030804050a051002180d080f 66
    0x2092504407410003068000003990400d0550054816040200038008400e05070b000d4240d001c0070030b003062840c00e0f0310070880c4d2540301c5c84004050b0a05c83e040e2003031002c00c00505410001c90f10814029900c030400c042003a03440303c091040300400b61081348105450074000c1d01814021001380e441b01c1d69407881da0303018000c0410248078202ca03e90001c02c0c0c10b608590b503408400c42450481c2e600c90102c8075015401400c0302d04585400c91007036009220407800120000b4100d41590010364020844003200340c410f50103801e050f00020380c10350912110004180c46a40c1c0301ca2078100d01e60003401088461502001160741a01085400c244548024810031402031107041c02d101c5281504c01c0c403165260050300c9a4040d6140c0b186ea0508001c40411081c9007000100040040020190000001401c0080e084a0700007100406214040300010709116007440f242e141150004280c80309055141040e800130750202401c001c0c0e20071410210302107800c000449084443e4801013040c9000c212103981e15158 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 250454712 1250 250453462 250453477
    0xa08070f020f030a03050408010c0c0506040f0305120a02030f1501091509091e14010b03040b060a1508090f01090203030403020603041b06020109060b060a08190f0c021b090702070308 80
    0x402c00003159002d4808010708034100b4007950701c441d1101d007028212420746540b080398104009401c40d01c0e0001c1600460040d4000703030b00c0008040258600d18060310329010342024808165100c03820044219015001903104180c14003804d0025546c2d610a00c0705110310800d100c2c0010384a41040c002c0300c0d0800514456495035080c084100d80d942c00f07120098a4a02140300da402c04002031641070176565010b02d941040c46400705031a10b6041c400c40000601004001800100c0d00c1c40114003030b501c602d003021011302034080e038410390005081d4020740340e03800c191888410b42c49603180401080310188528003100b40d00a000e51320342442d5400704280f0f50405031041e1007081d50707800c0104a020304d20b40da0b2070040c00950000b04104c1010f0404100311900908024008c5100304500e0401d9540009640e911001140f2126140ca82ca9950003000300b4002814131907040c64240008255500020f40001c40a569051600ca00f80e490301805086441900d4010159011032828000607030150082c0c44803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 250455962 1250 250454712 250454719
    0x30f03050112061d0102210609091015030c082410050d02040b0d030f0201060e010e06040f09020a060e03120a021c1107030b1806070906030209180a1d0a08070f02 71
    0x413111814051422a80044580051901d030f00c0084460045c480e00701645c080d00844240c0b010745400c000711a00c6801c00b5480f1106030b66182d20b417000060800c02810055a01f0099003224a5220702d80c155541c910b02228106410b03541d054401011034803100c80c3e00c10901c113085005864a00002c0c800017504201040380d1003074442e400d20586403911095200800c1c043e960309010f58160900103400c4030030740e42000800e80200001401800201403081d6080784040d80c1c000b401e01a541d107568010040f40d040254428201040010350035801810f900c0840c44c12030507a10300c00c4d4521480504c5100382c0d1440d5001d43c114009030a441030960700061042040c9062071451441c0d0400c031079041c018203400443c0c00d49180c40a100340301d003001070164200040c0500508140c10811005080c0c01c0d4248540c0082640004252000761140c1e190b98200303020b4515400c041e0305044407008064108640100040b603100150300309400800036904400642050215140c08800e03225140405510703038003030382c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 250457212 1250 250455962 250456001
    0x3070201150803091c051b120705030a030f23030115080f0606090604030f05011e18120e1f180303050f0706021209162c0a09020319030f0305011206 65
    0x200d003080c802011f0654400503480701a8001350200403100450280c111709036804413000303102c0c1d0f0300c000071601c613000e4050503d1400c100c9d0401040340e032102e400307044408099069160f01c3c481c142500103541640c0d0782c400c0001008104000c2242c1d0384408075800300041c440a008651a428040e0080840d001c001d0b1000c0d04c3c180c1c0302d0700c540780841c4404008440c5a035564102800308513040c1000110440080d00034802c2901007081030b5006a08440003074010385107002e81342d02c3c1307502640304c1c03481801c0d001c0e110301004038000d030400075000c01882903034021030740300d41e00900c070018022170020a50740c0c552a8281080c101006200d103940100c4030490f19517900708001d036100b446008005108558880c0108003001000003005d405601c25840119911847d03002404900c1c41c000b10510030100c0c0c0a00309001d580c4166140c400b412000b040607405004610480c2c41042e0100d401c400501d01079103902c021000894411421500c091058007406441c2040f64070000d02250480130002c1084141400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 250458462 1250 250457212 250457269
    0x100b0307051504050a050609031b0303162306160e040f09061e02040627050a0803120106140a0c030e040501080c120a0b0f04080403170307020115080309 67
    0x415002c1c0380c4007400c1211a011500b00490b10300380801401070301003070311014104646c00001c80d9450810180b4406401c5960b1030300b0340551802c0040d140300c82d182d0400a5003071000d40c00d2100801c02500d01d0300091901c0380d10602c00a240000b4058004d0380d42d5000003000e01d501410456448000c0301c0300641c0161900382060001040d07000740b90303246004d00c000052120401c20b014002000c0603903004061030040c4004c1290f641c120642500b100c04c20b00e840090303158090520903617489141c0046034804002c40c030109445c0070002c01742105980040325a00581d0321040c0a0b10800100c2d086061801e07400c01084401510818022003210311030700741032000c5900e0030005010b454090700280801e51000849000724680a140e00101e465180f02420141d05503803200741c54040001c011310f00c11559940824100801c03c4100d500568100780300c203070114440070210905520070f4910100660070b10070654011003801316a41d0854412400551a1003c0c91013440800c0c10b000303081c0e2401068000307204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 250459712 1250 250458462 250458469
    0x50d14010f050f0a080c060f09040204030b06190f03020d03030e01110c120f0315031002030a0902120c0a090b010216080a06050c0f2a030703020a0b090d02100b030705 73
    0x60301078401180690816810801032000a841e40040c0601c5a0140b070820040f01c0b9000c124140b00981c15107003107039207000c02424008140b10340d041d0aa0064400100002440302c030100c4c05006180480d00321003400600d0b0002035030703010a401004a002e84c0051b0800c01440c10404003101c0b1031190801180e0840954012400c4868062070000107180010740502c10b180d0500200e940034a4403140141490812070f0000254000200de141c05007074000c0c00034501e0f65041001140c2030f40320500940d42c83c685554a1b001a002c440c00c101d00550702e0002c100100903000c20001040710700a0001803e42d4030303140c2c0000141c440e40180c1415401144126840001c21113030700c9000c1c0c403120000300942d00451404000312100188070b070058090902510f2080c00d8071901721003111004080300d4013401d80c50783c0029190114104081010f200010b054001c064011a22180c403502640311051240d07110f0f00030f203403136184a00c03001c801a00300c2d405c40140303a40390781d00114501c4400b41c1140e0b002500c40c07020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 250460962 1250 250459712 250459751
    0x9030e15030f062b02010908190809040e16050a0515070b0601090f03030207140103020304030f031a0a080d021c0c14070e040503030a23010e18011505010e09010312050d 74
    0x3012004c03100c101d220a65800049070001070450b030b80280424011244020400f655441000300f00f0403000440c6d00ba540c1e0350340c208207110b142039070954515496515051940003c60b10696005125200300041c007032034030300800910b0950440480d8036280c5170740e8560502c6000180714038184510050080b541022aa4441c80a144a45c0050840500300b07008078040f0f108100c1c045040500410803c000aa0b02c45100340680c00c8900300492070311090381042d1010341450071420741001c42c08a00103080540001c00101221041d020742d07210745400004030002031402038000c0081403406000c80c002074020540820340500180a46000d15222161030750074100c20b13a0144c4803640003105010307404240348070300d90a211070300105400700c58a24007200d2a00b4414440e900c1010428000100c0010741c40c0e28007240940039100802c21103d090300c032420100398038020a0f00041d85001c86500504008940328180c0381c002600114100c01c400f0100e489070300001c01101c00d2a00c038150750a000c000c4121 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 250462212 1250 250460962 250461019
    0xe0d1416121206090b060f03191802011b0c050607080d02030709030b090606010801090c021905010204061d090c07030c050d020607080609040b0f06010c140109030e15030f06 76
    0x45000420105503009020f0b100143c200700442843c0c42502d02840d6104012245038520483c0c0094884d0340c1c643c2c0080189002880c465012424801030440728140c0c1010050400c0c0700b6212000c074000c8480000050106550f4001c1203078078001000e0280d0b103004009000750a214540e1103291010a80c0010247d0300283c0d01030001c500350b002d0500c100a511046598803650b010002c10051030542c4c0003d0442c24180b14102d04543d54005201d41e80380300388110f04101400e0f8401003a0342400b450418000d50003441541d000513803040200c03034105910b605600081c0b03001090344500392109050750740c040e0310880044061103030002e100c40000d403047c040180c04000c1e5030041c1c40740d4030307100b80003910000c0b005080a101e2525502000f00207444485c409030482d4410880011658030000181da55801c001005001c8003c01100c10b824100c0540080b000f90344207640b120035954030030b014009040c010341c6000c2c20046c01880010781038040c3c60007041d80920004c2446038108005120755880313841018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 250463462 1250 250462212 250462217
    0x3060a021804061806050d030f0c030306050d0b04061107050a14070f0306090c0b091e010210021b070602030c210d0f050f0f15091b13090e0d141612 65
    0x1040c4c032404500c920a110050100351012030002849640c020443c2c40d0f1202420148030048026006141c402e51003440130b4a4007920881c40740d9020306060b84d01d000704881c121ba400d802c120705600c4884c018000d07034012580c410001c00900c111070ba2118401c4450541c03c201da8422003100049070a0f8400001004600881d000252074006080c0824046040d0704420100581044480c00130344451900c100b0403080c19824004d484080d40040742008000a4800720850010416200f2000d90301001c0b1000d204500440e141c1130354480050361207000350141030030320b50011080709e14210321001c1d1040300c03080d1030fa16443c9018225505103084400140d81e8440703055030f82003000241546900c01d2500115089640c0e1060b181844240c2c0d40d006139854400d025100c4900450100d40c000901d0071070b1005198266034490070008000c218690080c03003146120340c18144045071020f004583d0007600256642c81410244c8422107904035680300e44218451402411701c000c3c04914460b010b0418204a603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 250464712 1250 250463462 250463489
    0x9150d050c070b0a020304020a090e07030b10080105090c0a0b0a030e01020a09060e12100b1306060201050610080123030c0d03050d1401050f0d0f0b0f060a080c03060a02180406 77
    0x1030503c1c6807030880003070003620494410800e010169640c0e107203501c1190120300020402c0d201d44c0301c2032418000d6913072001301900d52443c180800d005000f070710700d020358a240e00200643d0340e80c143d40d0750b42c80380340006050700003448030010b0004002400040801405034100401c0074000c2411560899101049540024051079024411b0a17444031030f20f241aa401c4950a520212400e4282d40380c504240440031220340e1102540d9a544500c0070b0b03801e000f8800c6104000303c1d82d40d0b89020f8080c2c101101c031948a0310076184198a03150150314414181d40300200070141c4034002525184d0019500880b455040c450903411078034681e940e469050b8414442c0e550395072205803884a0205640d0b06801c1c000300803d01500500181d22081d8081805030300c226a040c452400c0e904101c19800c2032080e000d001c0740151300030001c14803011091030b0700408068502030111643c4041e1182c855101120996043d00410003152040e82c070380d0080d000070b28603490300c20300030403061001408032219135110a4407034004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 250465962 1250 250464712 250464727
    0x20f100c0906020f07060e0d0b0103060905060106020a080304031d040c180503071d073c1b0b1803040f030213180f0c030c0b03060301050105031209150d050c 69
    0x10212000c020112030008200515161300c2440e01d030304850003403004004c1c44060790150342d07036480b80a800080e0820500302c415616414450701821810704250340b644510000000d000d03100003241501583c000350701d40d003161160794044503a44050500403580d003814801c5a0010f6036580f04030040300ca580d480354122400189010411503010b544642d101cfd400c103010030000d41c2800e10014503071500005201e01695101042580c00040c6140031103102d585a00313a80b2100c1c9901104440540003070741e1940c94910440302c1c00c44003c0d0b1070031002c0c0d084c030301d80e903000900103114004030a4116034003640211480800441852460301f055102c00c4c070030500c0103400c03c20350405251348030780d4035001641804248400c1c01d41c0100410344c040c0042281c240c8c10111018441e0400725500955408003800c43c04545c0c031403108429810640385140b00c1d502e8030f00005403510b40007452038007156100804a0810807010100114180b020760002e00100307003045440d00200304d03440340610600241c1180b82e02c4500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 250467212 1250 250465962 250465967
    0x7180c02010506060309031213121107050a0b0901031d16030b180d120212040b2202090604020703030b0a0e18010c02070504091a0403030e120f0f0307020f100c 70
    0x102403e0305000314020028000100004401c441e4160115020700342a902c0741c1105841e82206a80b010301216800d080e01e2001603440303a0702150600750300040303a24a41e12401004189003041c0709d118405c8104024400c0356501030740054020072840e0003003000344200b0380c00050130080c50310018031420920300401e0081161011401ea042003020b010180700700013050741135075030300100d031450340500104c803101c0802d640c150340444403101c0d640e01c201506d5003041d00d0100d22200e420b582d007810b40407580400c008550000c01d5411f0384280c00400058082c1c448205100c002d51007420140d08140d1190b4011503a501d485c0c07000700007031903a00c0b0f0011903450022842141400079100c81d0003164141001e100c100d40e07000034042c1c181c0b0000c9500003004152807905949901c0324030040c0e0101400b4604000505805d640140c1200006c0d4058408071041c0710503020291180040f0781390302810a11a0380e20f00d0b403d2002442d80300c815801160f0a810005001c41e103807148590b40391080c0e54613030010092003176 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 250468462 1250 250467212 250467221
    0x316210318030c21050301061d0d11060904020309060402120304060f080709030b07090302010914010804080702040e0f030903150702060412051614120a09031407180c0201 75
    0x520300d420400c4014000c8071a41804161002404001401101200b880010310040351144120a4901140d5520401c0940307107400900c60742c0089041060381d40070b245102801c150341d011005281d142c1490300b59540030b0039807041181c0769400034810311000c0c013039403180c0c802540113205102c0103000501d424410400c803a02c10070840303446908103100420032990003580e0410001840d0818058550707d29404650340702042d4006030007981b08005000360160400211000e690007a86d4180350640c66a00b1140291010403c450014070b10400040100c1c903482c024111503480280081a00704030030f00010300d0603410028a01d1550000a510642031804029070412004610300c411000c1c03400c008080d455850040018020981741143d08210314411404c5032030010f4403440c030340c0760098613080c90800503501c1c86d60303d081171152116001111040c07409903080e4410b15a039031540c250030359840d0341c0015800342c0c40711041e101e0340d032001c1131014035180707861408050040002000d8291441c02402e49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 250469712 1250 250468462 250468523
    0x1211040c05090901030311010f0203160906030e1005090705060a08010906081b04050405100606110f06090a0f0510050408030609061f050a0215040302031c0b0117090316 74
    0x6400c00c403401e6207803205103042c0d04494250a104005c2e10112801fa40508985019900903d1001007000800424405900c204455a94454075503d03100d001c240e0484441c400b50f0b290701c0e0f200b1030402d1071035442504610f0b030200d421000d40c0c1b446942e07140421915081544d821001c50204001444000c2d150b01c1035000400d1400020402d02e40b42140c0e050f116620030032110f015030340301c2e4001414880108210106a49401010000361b076592100910250309003004201d503000c1d61038841327900400080c5c0503015030f09035000f408502100da924500e80d00041001281c2900540c0129000c4d40035600c1001e03c039901847d00070ba981e242a81c01c2041d03820f0700803e1544115120400e5148414400e41c4440880c0c905007807035503550403900400c1c1c1c079000c10500501c00c487c42c10400c210806a0101c064580910383c40010310f440030000c90780e00195a01c111a1500041c11256070580c14102c0e045407036002840882624500700500d8006807046007214001d8070051032070099031590021030b81d81e80021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 250470962 1250 250469712 250469717
    0xa11030403030c021017010b0d0b0405090601121403120a060b03090706080a0204080a050a1209060f050d2a08071b150b06160c0506030405060f101211040c 68
    0x4090950b500030340191a0450302030301410107050780303840d51401602d1a04030f0010352001400300f5a9a00c0d02205994004030701841010b0500e07000c1c0e886414540070b040d0062104001600c100d03800e04150b59108141d1800680e00c0001d07040c040340c421a828402440b410316004620390003468401466015201c41d035100c08001c00d001c0081054036400410142d064461502d0302000e203880e0103019030064022a00806507500a4402280c2003142c0001c1803440c0c1d5104059019888000f00815504c003c11485180c0c04200f5410a21820b030303115800811001a200c24002150300b884c103c001d0052800d0132544d10100c0740b981e2003c0302c194004000a0303010ba5280341913091300010742c00c400c14541440f44001e1030700034000b261581a204540004584e5000504090b495060303082007403000c02103504c0103a0340d040011901145508198048030702c540d800c10001c0000340c88440c030b50000280c00038429045509503c2000c90000d900203400390800b802405c250025401000c1008201e4442c0510750b000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 250472212 1250 250470962 250470967
    0x7030308010b0711010e0301020c07080c0f060a0c060510090c05070203152406040e0f04061b17060409080c0102040e060a050f060d0216080706050a0509060a180609080a1103 76
    0x500c4e0f001011900c83c40c2860000c10b4501c0d550b012a01900841d01c0080c0e160080101c041075425000818001c644000c8030f07104070800c0308405000c2d26118940d4014006403580607401e004c0340190b000150011510380d44402d20568805140c811204200d07100300c0080c000044681c01e515080000b1807000000703e00c2d0200c0c505180d454250510b41e8442c800c521414440040241c80e41c40505540040c814051101001d01e4001075000c8413000c200c0d01107030154600300c0a140d440400000c1ca5001d011203884000740d0b640c0603a0300485510000345204da1154075090541c00041d03d4001410902081c00d0016888505003c2e01400c025002850b00780a030001200402c40365603031825a280002d000e40354269208800d64035031000e031080320059a4079800303480805c003c0040f6a801080074900500381040180c54940c04d92041d1a03054920710b4043d8491008190040110303440713916039500058141c1c401980320799a0a054900203102176840460200d0403400083d0800d0380d6400112a2501562 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 250473462 1250 250472212 250472227
    0x6040609120f020a12300f0c120207060f080405060a020f1b0d020c12250b040602070e010806041a220c030506071407030509040b031005070323010504111b07030308010b 74
    0x400d40400306c1c08880811010743c10b00d01596004140103015190022941ca07001600414040e43d20f0a85210350070008050054ad810310074850380c000c03402154024081c011a45500150704080c0d0402e850940d114141004640800d155a4a020141613100d070301915542404074004bd08002040361500c0c050a0b8241804080b01001b04640c5581080c1c2007220000c410321700103c824a807041d03000040c5511000401240792a0001692804c81c1c100d0800c6402683e240e801c150380fa4902a10f00501c0c801c1d908090b01c600c0e00c034601d109a840b45c005801d81c0c00803007000c100e210341002020303400c0d140a07095a405206000003803104541c030030558104007135007200c00252960280704001016042000100d0400c40980e140d4100d901c2e9209c00800b01d5544600700c403070000003080140e404130080384c0b5188009185580c4149480f414213040c0d010444144e1030442131001a080345c0c00712480c0280c0c00c004c9442400228080c18214800c04401055100d007140340c0a8140941a0000d0b03800010511910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 250474712 1250 250473462 250473533
    0x51e0105040b0304030908060c04050307140105072a12060506010f020615040b0a0b03070e0405010b120901020405040e0a03020f01020322020a0503100b010e06040609120f020a12 78
    0x6604680800c101156a13a8440c24200d450343d125821003640d901a420a2044607100640600f003502c03001c805685400d03a88107402080342145052581c0441c5042c0314850108407109103200303d04040300844600e0034540c102051040045801110302e2142d60600e5406200300d51007900e500c1030080c01e003801005078a000195585a00905450b0910241001200c3e90740b00d80d040540064030240c002e4210030b40b40c0f2001d15094004480c04400210515540d07002031a0902440c1d0480707442c1001e80f0b00d00ba204191320600c0c4e40006001c104e81d50740810002540707032564030406101e4941e0b4400341000c040c0a00d402424003404070780340d40b0300380c1c01841480603e480e0440c030305140f86078100c4880d00010243c0b000c54401c9245600c00c5d40c0c103024070000301c02380e180c140d0840300700400241c0e11250308041c0034003000854022030044c8400510415414061329601c40c917181d200c5802521129099074080d03002448030841900600d034020740d0031304000204080b00c100301000780584010324641242402c00e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 250475962 1250 250474712 250474717
    0x23040f05090912030a02030402010e0a06050a0c0501021308030a080709030809040504150f0605040e0a0b010b0c10060b0d0b0105070515070c0b010909020108060a0605040603021c02030f01051e0105 86
    0x40c5480390800c0004241010000c1241c407910512201085803640341c070340354900003500b00321416404900c082044103064034203540050241c0b00262600e03401d000c0020000c85034030041c620202c401c0d641c01c0204400c1d640003090300c0c13030040c00040002c40d62618401d00080c50300034050404000e00482d10030520000c3c85070f90640708900001d5500046595850501c603800307030300343d9040300100ca242184504400720560011030507280180e9050140e1502c1d40394965440e00c1100c400f6020501050043c05040000c00007003040d4070f0080c00700e0709249900b001480032070700c040c1c2c00310b0754120703000540c074010715094000d880b01c10400342421401d00300d5a8a94549800c004c03940500c000d2103030800500c03010701855420360619000501d43c01d80f50b840f9011a0000d010b010780c1a4003084440700041c80b80d141810042007556003030390b6220b08083c0707080001d6000e50071040790418070092402c3d0180351f10b40740d0310240d44070351a0602c580c0c4072940f400051001344030124150051141142c0c12980099800408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 250477212 1250 250475962 250475969
    0x306010b041508010e01050609040204210506090d12090204091502030a05060d050a15020d060b0d0506121005070e06030a0b040b0f0303040605070606120b011e06140309160623040f 79
    0x14030554030010270000800903c140c0c9c01c0342031919440308107032110222361818003000c0761049044a00c00d40f5100500c03643c441e48000301c4000900c0855000c0159581da800510a9500c0030340f01041c940c1d0203a031402c0c000b89000e140031181c50790110400c101c008160107016004481a41c102c00782c04441e8840030348400c1c0001003e0300380826160b1000d141d1179141d04545100c000c2403810408030740ca900104409901004410081c0360a00001c1099880c00e51139008903203440d4402040c4ca5007212403104064480180b0400612035001c4d444480c503110903000354031800c140c050008144000004100458021484282c02070082d000303030b60034684000040303500341c070300c1810100e031298402d240003400b504040c0c011041e5108020f211008014400000c103040c0c4a0022034406a041044800b0000c03541c907214100004003038840d1081d0b00c02441005541044032101519035007c46594074012920555100900207a08408007802040c4154103010213040003807407a0386000c3c900701401c008000c0601 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 250478462 1250 250477212 250477219
    0xb0f01050117090f060a09050705040204060503011503090215090415260703080c0c090117070509250e122b02160602150a090f0b070e0306010b041508010e0105 70
    0x1c1802107804108134282000e200781180e10313600d0185074001c083d1036400e008654078030454501042e64601760003580c0c00e9603240d81e90350b815686044103100210a80d00111024543e5034000314025885507005060718426284040d55075400803820f020498200781003081010145070310070301c50000c0c103035070f21084800c8001000c40c03192220310b9494100000303a0b0004102c154006280d4484600129010240c2c0000700d802000c144c0c0c0c1da110100c1d508a21800800207600240014041807410041c6580c00808403114540980d007608401d01d600c102406402000c80c46c01c0c0c41502c124a411070b0034260207609a0080c02906090100441e0103004030b484115003503a040040c0c80915108000044145c0750684045418680d100c0010b0349072486002e0060200c032070580020280380040c0180c1c144694001c1510040c442c1d507440300200c00101800d0b590070400002c1d92891313503590800c0300034060002031510b1a039952420703012041240c11408100c05000c0840010071865141402060440e407054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 250479712 1250 250478462 250478507
    0x20f2a0121090b0609090d0f091e08010c090303090b0f0d091a061804060e0c060d0b0910360603030e09090f0703110a090f09020a0614071707080301030f0b0f010501 72
    0x3c8d8083e01e050043e03401100c100d00989048880b10748201c0380800884001e04001c10034040050310031240020580005000320340227020400c209600e0400400c44e034181041400c0c1040340d03454145040d210314613003e0311a41c45129a40b0340100300141d400350003403400c80304011281d00d80d400c407030038080d170090014207000c0c0c1d02d00701581820428004501c90100c003d00365956480200f503004000d20030113074084e00611110002610b8400440c1400d01503810b4810f1503900b80303400640b821386e180d030028801840c440000c0d9038031f030342042c0c540100c0029500c6610340c0c110500b003400c107200007000c0040007020700f54482c0101c07448002002c0b41c4402603076001101c500c50340c030810000c568404415440302188610f4000c540070301e80c1480e84000001803080701c00101c4181d0f124000c07121120381502032280f01038100161000903000d0f1218900c03c60181d40801e081c41225151140c0360380099006560551310300601008000405c20035035401b503402d08035050070b941040700082040074000302d0241da18216 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 250480962 1250 250479712 250479737
    0xc020d05071a0406171315090804090905010f091a090307020603040f140f0303150a030b070f081b1206030c0901080d020f2a0121090b0609090d 63
    0xd0024101801c00c0080150048071001c0c0b5401d480d030b1140c451140064224020f00c0816034640303100501030417180141c01c000d0f09403915000c0361586480085070505a40d00140380004408401500c0180001180002d042d4407900b082c0d401d4a902d08086016039140410702e00029503a9240c40c1c6c3c45241141086250399512010390340b45200f400d0001e0b601020201c00c000170030a103601903030071051084001a69031143d41c10000d5545010401070700b1542c0041c80000c2d04580c01003410f8980c1a4024601c42506a0742d8454106ca24130980304d020009001e50300990003542c215030700c40c1c2c00c450780c0c1510b00c1c105031501c1c0300c18030b10740680c80c50549031103022004603a4694080281032100d40c0002c241c1141355a50b01001561010304211007800740c02000380024015501140d04d001a1781c84444076071000006c3c0c049081c40148c21849181440200c0392003094440c6840040c04130540510320002d851003060a01042804008001501c188012002c01801c40c0000c507200c8006241801d003000c04081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 250482212 1250 250480962 250480973
    0xa140604030606080a0317040c09110d0204090204050f0604030503040909060e0d0201141e1603091e0204060e060105091915050702100206010f0e0915150906040c0c020d 74
    0x2503900280c010b50804002080d09a800305071110306500c41d4403240301403080350403142d0401e807023180d02814022001500700101c04403034100000c2400c21020840c54580114044012600b040c0c000410040c0c0c00b04040c8103c0c1000d0002000d1904201c4940b41000d155903105507880c0b0443c00303400a0a900c400069081040390303002200441d4018040c1c5060f0f00399094020300a10460600528440290010907040f140c0c024071545400c0c201901050742d03664401601c400d403021003210798200340e038886c840008585c81511003e00e0503600305d601c0c00c10040c0c5004010a0301c640d60400d84641c9500401c0c801303541c1e040401c45072200d40079540b107111042e9842800302c804e0340700c1c2d00610b0745040c240085c2508540c040001c0150070300c2203880c10001411100220f070340310424040c1c0c440103984a02d040c403005c4016801c07507522222000455044040886840d00d18100c00c0c0c1b812940e141700c003070f82415285403070010700364800d009a80c100502e0400c1034000b03102e1404000040d00a820400e100004c3c4007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 250483462 1250 250482212 250482217
    0x402030a060c051303110312040515090303090d1202070b250f050105151203030f070c050c180105011e020606010f0e15041503060501020307080c1e06010f0803090a1406 74
    0x40b41982c080d004e0710356900301403001c22000c40c48284203000d000c41c5030b041501d4840c140c4060b05d00103468100c0754841c0000c400d940394009039105605100900038001c40d075650360444c1d1103061290004e001d100d508994060704c0d100c00c41c0c0118094034000d00c8008100442002240e8000f644840403106c00d0034907042480d5a00c0c00c03064003030415402d000070018005c56900b110124204141c0d0040c1d107582d600080d413a224007054540300304286000000c120240e1107101603510050040040e50141000d00d400207200c241441d228030076540c14031004010540e0040001c84d0319800c3c4c4a07540c0c0e00f02005c203c0c029101c4500600300e0b810b000412414aa5240c428243c42d1300140c0054012a998644d40b850004030360898071501f03100c96850b801010446200e070140104031034060300110300b00301050365001100e40080d80c50320200d21401d4854070b0001d1482032016005180e03000505000e50401094004d90b000c40d03000500b41b80c1c400c0220051035140c0e80814400c45420f4450030103038440001c00540c061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 250484712 1250 250483462 250483477
    0x11b020a030b090d0504030809370302010e0d0c03030f03110c0609010e0d020a0b150303120603010c110a0f1a070203090f0109060819020f13031a0402030a060c05 71
    0x5500000003200300a480341c0d003580902c580344102c3d94000d5040c94105d4061055000c001c06200d014000540305041036140c1021401d28040e01caa6148100315400d10305100b03400d10721901c1c0c1a29070007081036580004612000080503101c030300346036580b072310b43c80c1c0e00c01c02c2d600c40241080320500460005a100344d01004456410785001c554444031800310390382c1ea034415034802000e5440e115550303180b544001905500c02000343c014000600543c3c5038000807035001450441220100c08000d011075400380001c0005007280104800302e0f0505d174040c10300f1142d041551300300b84036011002c120001350000c3c64821040e804403c0741d03c43d401500d03021680c5c0d5050002000800800410b000c0b07180c0d0044054034a0600507100c05075120107841c01151403180d288220310115041c0b0000c5610f03001d25007404041e142c161a00980360103c0c10707074600c28a0780300c0507040c40c100d03c50b22400d00c01c00c030724400e8101118642c10f01050b0142441d4001946800780c5100c01041a96101c4203581c91078020004e50b20304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 250485962 1250 250484712 250484719
    0xe010822020d080d091a10030b010b1303060908120612031813050403080a05150108040210030b0310061701090b0c0703110303070309032c040902040f1a030f0109030806011b02 77
    0x303170059490070b04041046107142140403400c1c03070000b034039225410918504072a00302420382c4040e441c0c40c00107102235110082071000c41101c400c1c0031012600602803610540d1040311166035818cc0b0750040d11450038040d040b20311860a51518003000d0f00000250b89091401c20701100c1e03540c002e20001800304145910080c045401c00041005154010202a21038040f2081c2482660b645103006c000a00d8040712041c0801d00e02c13004200036060956000980e20311130b081c0000c403c9a0700c07000038034240c10750700c42580c40f9840300300600c024402c414a455441d0480340082c0440d00696032001d8104100a02e00e5510100124224060500c501c00341d20302600c9040039a9607e040c4180010040d22817410f050700420b020010b11002c41c0915000c4a01c0900f81c00e000603601001001040058a03c006059038800d40f240703403000c0900078a11907140302c020010280c0030382c0740c040000e040c14440a40685403142c0d1518a4803400b098001e044076502040929005101901030700c40d401d400000000040e41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 250487212 1250 250485962 250485971
    0x100b12060f040212030306030a11120114090f0102030903040b0705030d14040b0609040b07050d0b060c010b190303050304020f0a030f0b0603011107170a05070f030e010822020d080d 79
    0x1c0e6a440300c00c03280c003660003520781c0104a0f400140703ca030340744810b4400b9a01036011802c0800800d01401c07040b072800c000101058a000440c681c524251703080090241d491703071040014440586002c220180221001c24001e500f1440c1c8915071a442c0d002c3c9108125003501c0001d540303010040148100e074054040d481d0204045d940406c1d42d0101481e04450850790600000c0101e009440c011265a100d2a1f00c0f6520003015601c401c0103c1d0759422201200c1c623016213489810310583d85000c050b148400c042c07000003403860400303020070030005500d04840e502c0b80060601130001c2548002240e511036015215042310100c401c1c045401e412080e070010b0b1006540002e464200440c4685043c01007030102c0081c005c00700e100c8443c041502c5140c0004007203808401a03c000b20880001410740d04201e424040d0821107a501c2c0c010803200c0f1184202c0c00a0507141c4024110b6800034290707608440050640d1081f014071840300004001d804e01d0181c07050000010b8102009450402c4810703200c4100d00600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 250488462 1250 250487212 250487221
    0x40b0d050304030b01030318150f091a2a030a051303080d02090a060e100c0f140307030206130c060305090a17130506090a12030507020402070c06080612100b1206 71
    0xf07002c8000c1c0011000a50300100714108d003104d01c1c0540050380e444900d06030706907080c1e40c01510783c0101115000180301686c2c0c000204000905000300005101005590b56240718410400504554003000d1040c401d103d10300d14045a4000143c429440136424201d560300c2210400002103101680020100d0b900010300360f0316500d030303600130303080100c8251200050b5070b44804080d940d0940f40e140a80c1c20520310000c050003103106060403060b150241e404011240075607224690b14000241060341243d20029040d4105035040102c5540710401c0c461403059408290b5912111403024400d20303081544804c045084c11a05000310401380c1d90007000c1e1004201d804000401a8010031620840905d0307500001916080c103504403050400d00801030030740780307084c507000d8811409048c106408002c001d1100310010b0f295032004120305802600000f071550300c1c0c418014004000149902d010b03140d641421005400e00003604c01200360208008100300c42000041400d0074146403091503284a0b071414003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 250489712 1250 250488462 250488473
    0x7050d0908010b0d0206090d060b090103080714010b0108010302040f021204031d09130204020a090801020d02091f020a3305060406170d08040317040b150102070311040b0d05030403 79
    0xe049980c468000e212040042c020404407000c194406500404108090a6103152000e10700705410b2140400085030548900860070505090300200d0300c104e400280700c01400b100c82c0c111030b0302c60240030003071000d84800000209a2074061000a01680e201d00005e90640e2460301554500c01252098400740c3c6468100100314403400300300c54420b83e0040821030824240200468405c403011001c40f03550300301d95403d10000398010a1074030100b065100020a15a40c00e0000304040e10754101d0240c0c84a02e02d0040206070080141c0e10303050120044644988903401082c419980740c0c105030f222140c40b0ba0194140030b80e884018490404071034020002c40c4903003050f4001c40c0120700981d410080071b81c40340c41c06241c0c815100e120b81080d41c0400e1080289a105101c110b610a10902c1e0208088604008811207160280c2d000c50340007800c5000c00c440c07503c5500e030020000c40248020900c1c030b865600c2d4000703001c0d0114141ca0160b51186086d0a050712b40f0034180e0445503000c82120340e6141d83e41010b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 250490962 1250 250489712 250489727
    0x306092107062c010b0105070f0512070f050105070309030806041a0d03050310080102030106020a060903120e100506010216050405180601080607180e01050603070306050a0f08060a02070512030c07050d 88
    0x260ba40e40140d00c0c3c01c00f0f051814442d1200200c01038540510303040b59a1110044011040b108644d00d100344d14041c20405110f0015140c84c0e4414460b500c0100b0781c500d095420340e03000a02c100101858110800c011030b5200d02020380102e01a1000aa0403400041c6501c008050001c0e240e08901c0148054040590080c02503208005048a00c18102d803a0704000b8280c0c4004c1c841d034001648115080c001040041d40141d11462003070900e500d603043c2c0e40c0c06c8841540c0c1c800c510807d03590002100c540c40e00105005142d80810248041c00150f040140c0500090390b641c020316026035a19000103030584d07180031028040c03034404012a6025a034503031500d650740070b00b162114001a00a10301c14207100c3c001c84100c1c02d03070703041c040041d86036030920040c090f03590401800d0340105522000c001815450754103864001c1d107280c1c52100c5407581452075a42c9001da0182c0305205a074030402c10200403600110360412142c0c2803d540c02da1307030b80702d004194000c0c3c000c94502804a002c1d00c000414880d801103032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 250492212 1250 250490962 250491011
    0x3020913030917030301052e0f0e03010c0909020705010f15081504030804030e0607210906231b101413030e0f0a030f0c050f030609210706 61
    0x3244201a0f03151010b14074070702c010500c0500b1980c0300780018042480c1503054848601f11880e01c1300380942c03a00684003422040380e01d1040114107451941e524140d03005161006401058000b804111070481c0c2c001c2c4141040c2c0305019a40d40c1c0491080c041000a40210b0b07501c1d00e0040050003225903040c1420b110104a00c0740c203409200e401e8442d5254800c1c09040c0e0f02c100d402d42c5812000c0e903aa624143c0d1404002010260300c06000c0180d200002c0b000784030551400c07581e10122038030000c174030b1018103200c0d031a4002000b80400b0302060b1442101b030700d8143c55202c5558001e2616480742d03004003446480c0301e070781708100c500840b00c00c403003000020707801154440103440484005480c0c0003000c0b800040310900290003d001c0c100c40d400e884c14580068000750340c0141c00c41c45815541d07100c0c0407082850b00001c40303010a1180081040e450000544282140110041e00e01070a09014040d5103108400820548403400003000140580000646003d650009018012201d130010303880c6464440c401e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 250493462 1250 250492212 250492217
    0xe0109050609071209030c050a152009040e010902150703021e03070b091c090e0a0e06040f03031b0201050a0c081b09030304090e06071b08030c030406060302091303 72
    0x10000e816407074034006840c016030041d210034001e0944c00d00c1240161408503415418405041982e00000e101000062a2140034000f03212240030b40041180507148950300c28104100d804606103296074468046601440040714001110f5000f00480c40c00343c41c0064019602c002002d220110140801d00203244592190303003030300c00080c0b5070001e06030401080030749062698002e1110b0400a0790b80103030729030040a14030490301d5060002d1842c1203244100a903900000d02848410031000032900000b54110f01806403d0200c00401020386039039100040001d0407500f180c0c14018181406a0b11294510302014858101076800d00e002a000e01030549460b16a80d25041904420394401c045060041710080a4107600b1000c9000b01110345e08034a280c1545400100000640d65400784258001c03013240310098041403034a003401406482ca48840d294100c024000c0314000500c0c10f004032581f14000000f41c82e1240c55a0070410018105074000a400025420a01441440c41d0402209180c4240d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 250494712 1250 250493462 250493471
    0x31a042c03130306021b0303070c03021b0603070503100b12040506070e21030c0a030c0209010801150509070203120106031a030a15090528030306080102090d02040b010203090a0e0109 80
    0x3002080c0e03244202c0025100c0c00b21060418400656581c00802c0c0c85004041c0d940307070b0350070085c0449055600680b140f07404a40840c40400030190184512000b42c114040302041203103407040411514400240000e082080000020f001e5001c0c0c03002c1c42c4054409003400d10b03115074034500b510346914010340e41914188214400905140c0c03061044282142028203610b5440540901c1400e041c1d140d0000c0703509a0105100c01240b0b00c10070030142c2401806540c85c9250103002d401441061041a00f0686031a4180b6800c0300d41039064848180c110340055511030015524980124151701900050f01480d01c1c100d4000101e580c1c1c10b80003425040c100104216442c0140e10815035503aa2144004103414884403031781880c0c040552003200864011001c0d9080e802c01c0350350342d800d11390000107000010002605441d0a159140c4102c2c8050701d203003402140b5220a040000d20070b0010780d00001d11079070b298054201564420710544188280190101086a44500c925421b07000240034180003546030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 250495962 1250 250494712 250494791
    0x10318050703082a0a0b06010207050909010b091303020a0f02120d0207050f0a060e09070309050f03030a05070e0127270f0603080a11070e010e0f0612030406031a04 72
    0x2c0144207013210885000a103060809039850402d0200020055410760040710000180b42c0c8450001500c90f240386400010002030407000c005003200c001d860110b00c0c40350b0020132030009130005003030880c03030b80c003d120000820742610000707905200c110300320302060152040302883c4a80018040b02a201c088640d0301c03d010300300081c8500d14009101e0400041c000020182c82030900c011029004030140c58045100171301034440c54940310420720703403a00a070300000800102071254807419030060204e142c080418032284000074000070140d0b03050740c607228500000911900e240007036600203040240081c00d480321141080421062a034036000744290034070700044942e03050361207a10f013904d502441507401d0111540f02180c080c80b00d405030982034458050003040b02e60349000f855000b070802e44e000c5141c0d403030403401100150030050a01c5000d40c102200510181030040162030076a0000d1400154000a6202000b075040100420310340051400081022103a0010342e0001040004040030108002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 250497212 1250 250495962 250496017
    0xf0d05090303060a031b03021008100911070809031015032603070804060f1e1b020309040b1c0b042307090f14010e010f14060901031805070308 63
    0x10480d2003a44c07000448605000264422081400c55000ba540f101c000c10b032039a010885401809581034003250010303040110907807581d03001401a0034412024801081500000c5141d0b000b102001040244042142080f40d10100803404a11004150901683c40d00b06256014124140410b462014201510300c0c06030304894001c030840b0404e6080d8602d150350707035201118a944c0c007170000c841141d181d40341c005080d03045000d2048000c0180048407103040b40320b900581102c4034a4058011080d028000b010003d4000c17066030000501980c010450400d070b88000780b140c851a0415075001e404a10703100060004030b00c550341c0318500c0345a68210b440142d4500980755088609000c40c654011041404a21081d8000e49000c0082d2040031880c501f40d1510012400e409810440c10103d40100401001c0c900c1c0d4082e000400740028003541c0c1818120110fa42c51251401e01c80c181619248881c65542145000b580055040790945500f107844c3e01e0900c0c030a0780100704440c8280d01c20340c2d00000080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 250498462 1250 250497212 250497217
    0x611031603090c0501080405070306020316030606020c09070302090406170c092203050d0603050303091b010302130330050705010c030e100f021306090f0b2b020702060f0d050903 78
    0x303801203d000e203698602801116001c000402c219103501802000000040c41400618001c0850b0801d13402580b0380005c00504443d42c030b074007250465005c0c400191180e10741007070558100440f85405680d13603d0701c00224020b003486074466400b0b1850200307208400400800c00320b41d0b8090031583d1600300c0c0c8035138030024540c0354140b920396041111681100700103070081340101030b600200c0c5004078a080e1b59850b8141960802c8030a4015070300729918100002ea141800d4176210030b42402d0442c100111031071708030b403100d100e804001d00c806140100c4400d044c0f03c460256540c606040e0702880d04000315040200290400e00c4201e038507600384401910300e0741c000c2c01401103981e501c0d03005003007882145c0c40a001401c0a040300940d500d17800c10050207050301440c0c0240180429840b2030010174501812815646040c0e84150070352a802e0159002c019654044606900740e200d5144030710500d2524040020b104480b4025840780740092500f0b000d540c51400b0f4810302440c2e810421580c0d55445050340c50b407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 250499712 1250 250498462 250498481
    0x903060c040e1503101b140a020c09061507030210050108012009040608122101080304060c0503040e040f05011415010309140604081315051e070611031603 68
    0x40078100040303611224210680088800404130b483c40010604260300b242e05100d031303a003011b6040742210030640d40c1150484c01c0000325541040d150002c1c911000351038000384070350540f1840944004c40c84a5489124210948000e1161103980d0003a91401179030300e055041100041506000001504070410b10908258180b210071404880840780c0400e00d40303520209440e544103a89107004101e07404d040100d004440d14000c4c0e140c0c0d1b2003540001c1d007196450940c0030000000789040051200d68004000c0c2c90032201203051994030b00603146801d41c110f01031508280b904118800401c01480820820294981d021b903008000441039400a803140440c2100e15071210700c0c017202c0e50002544070744e001c1500540101801d9100540407010f103030404034203450a8501881c04900300c03084460420044000744401c04020082d040c001c00090030501420004501c14032612541140000307100080302e428a500110412600203001401e1466400640c1e144406811258003008400d01a00c103490340c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 250500962 1250 250499712 250499729
    0xf030a03052202030d050d0f110a0e0301060f1502030c03220e13080c031204050c100206040c06030207061812030605030c06030411010302070506090a030f21151205030903060c04 78
    0x915031782480640702c135808408411101c0d5600d40344144d03001911f2284d0100038928a0541c0e5440303161407001088403c81050b0340d0f03c03c0e407400004101c803002040c0740004031901141e4503840d88a400345c0c20b900750f000b003503030b50003a500002880c14440c41d202507035403d84154850a0050458460029401c8400222044014a020b0000e02e5010580c220064212003000d4011240b03424462035041184203c01d03501261260310600c1c01038180c2ca400710070f5103d400307130600c002c00c490f15107502d40d0310392258a44a070f00c0c140340e40001c0351001d200e4276400c2000840034602201c0390f07020b61841c00126541d4810012000603241c00d0340480c0514020074000c50341e0b0030061945046464540768000c007480c078803880c40d040c95070030088840015400c3c0305480c40b503500400a0a52074400f814050548031352110040104880010690b04a40304854030310807480b00380000180007054141c03800c5002c616031304104d8000318411044000c1140010003425801419802c2d80c040351281501402c0d54012801031420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 250502212 1250 250500962 250500973
    0x8010b0703020d140c0f010504060e0d0c0f0c2d0609050a09110c010501120605060114030a0c0309020a0f031406090705011d090a05010501020c120d0c050f030a0305220203 75
    0x414480d04401051486100e00b136807401307280f2001d00c3c1c6003010b24554130300c142c3d440f0002c0005012851140c0c0d0000b03011400a0103040f101c1050040c02c2c60314040008005000501841c000c1c00050310044020f4850468815078407401060340e8250706c0c0c108031400c1c00ca612440004652544a4020f82003141c10103003a4000c0142000d01040107481d040035049000352040c08000036000342401018020072100e00b000e008140141410700580750000c24080c18450180481c2065031040c2003140e62055000e60005210003864604801130140646d010b5400f0319828004104503080385e03c1c03601100c2c0b0039560ba0040349100c10303149488820848404425411030641084203500507010925501c0e401902410075909a4000440a0b00251202c000039a41e1380014455560100107403600610111882050744030315010207540e800c05072011100300300400308036100304a401c00503418070744400710039179807960140c3c40c00a0007000304807100d244015111a802c84c00400400922040c030350050301a04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 250503462 1250 250502212 250502233
    0x109112101020a0806130209010f140904051501020708070b0412141002070b090a020d170904050c0c0c01080405030307080c0f0c0606040f02040b03131a090601030308010b070302 78
    0x200c418104192140405a111401203006080c801071800a603ea00c9900d4941030900901a8041a001e000106107104100c040c01580c2c010503490441e00030784c07401c2420390341d840c0401c81c3caa0244204094000d03041c1024000c9007801092801c5014000307a00720b83c06540d0312800d0342e60360461440340c1410400c0c200000d010b009400c030b5001e81001d0190b0f91500441e0030015076685441040407030650800c1e0301080c68820000003c405d26004203055000307090400302c5800040a24440c0c3da0014204180d070032001105000e11000e4542d20b180040c8200820703e044c000c10021640080c01c5030555010307081048071650b020320640d82c02203030440300450440d900c81009944503e00a00349007a4101d0501c011800ca583d01d00040148540340720103440c042c00c2c000140400c1c1d48903103982c03001d002c1c014081402201100340550340c4c481420581c050744001c0c2c5091095070b01ca40981000b03042072006c000c00600003000998a4122440790352401d00b2680d813902d4290441c020168010f00507040501d490 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 250504712 1250 250503462 250503469
    0x91b041403010e070321051c0e1c0905090f07050a0f0c140a030215090a0f0c0e0c0304030f0e0d0201080402301009020d1509060207030917010911 64
    0x1034000c0e140107400029000307401e00c1e1041c948540c50744220380d002040b1807100742403080140e40804044440c142903017418a004103001102d4031840001142d1a581c840e0700e00707491800c005481d0300d00c011301c684492014410704010451901c0d030060a000e1641003020400c443c1100b0034491044141e5950b40d4280112503104171140b54800c040041001007041600e800f003007181c100340d203c01e000100285400d40e05450007a040601980a03091000070000400c40d05880110b107440480b54401803800c0d44c00004d04c0d1000b0030040c143c1140b8801c801210808c418450880000c42c0038500039104e42c5004e0010703c10881784802d6010426800041c6420041c0065004103034042d0028802001d030354180030621135041a0208000d001000d2034000002401a00c1050081440811601500707100c075824075004542d400e0b101c0a0300a2441084802c020003484d0168005800d095211708155941d600ca03050080c0040f011340524100f40a86101c00c01c40180705118100d005503021000188100098003007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 250505962 1250 250504712 250504739
    0x708070e0712090c0b1801140409090c08160315020406051602130905010c0e01050429070f0606052b03050a020a0b01090516111207030c02060304030c02091b04 70
    0x504642c0c03a00c0e01c1c040000120510394880282040b504075039107542402030a005c0350a0180c20184c10f00c07180f40b6403603c40202e00d40450341070313a0280c0c0c001304c0d007000d981c60448404251544101043c0c0204442070041090442459040303038041c000344001c83d20f07030070111303812445680b1520002c100c080281d00c00113545852500c40b0107000800d0508020080c0c00140156150503104482d0740c0d5580c150311088503009004024480302c2032801e2400c180c140f40c10f400500525000380202105440c25a0744d41d06214000c0703404441e0700101d5070300c12154a140100281140e4010f042c031468110340024801c1105014454506402042d0400c12600c01c0c1c4013642c1c0355018110840450080c144141e011940c2404150700808000d140003d240c60000d0543c0a582000138a0f1800c0045107104510440c4000415162029640a0342c035941c0c4410724069a000c07051290080d04840040f003000145a040b59101b2041c1e0b0007600c50855035560480107008681d1301c0b0f0081c800400090005201c52054185c5c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 250507212 1250 250505962 250505987
    0xd0801060e0409080d0501050a12030c081317030d060e07021b2701080706050304030203030708060f1203030601031a220b0603090a110f010801121a0112050708070e07 73
    0xba0351110744d2202c00c01c56104035409500c554881e0010405070601405840041013441c2502c0301624041d44c00605226881c2c01c068030b21000411600d000421a40c40032004021942d0483d00c6075410180d501d44903000143d5401c0103074501000041e8540c1001c40c400c6c4200f00c01d502400e02e110300d04404d11007900403651202e4010f0034609401302d1510000c042c003100e807200c24803030401c40e600d010000c0e072410b6080d410001c1041030a10034440042c0c0c00000f902d8010089082080e1195100004545a0a5110641c5038040c1d143c0c180121035680120055016800a981c11b00009055030b848811030280444c0c002d410905444039098044094003e410f400c28800c0c4001c03e5032030305d00c00010f00542042c0c800080c0d940143c0340741c008004068041811406c0182d0300c1c000215000c2001030f2141034144103213034000303400145900c20488280910000d51612002031034540d61140350800540720720766403c90b050710a0310808039034003d000910360100c601442c011480c0e41c0e1a5141119406403c00c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 250508462 1250 250507212 250507219
    0x5010f1e05070324030b100501170711060c0409050702070f06030b0102030c011d210306061602041a0a060302070506061c0f0305030f13030207051c021f110d0801060e 73
    0x1800380c003076030303041340618080c0040d101d002d011241e06600f489030b5a120042e01c1014100044441000f090360004c030b040075155504048803e0a60310103100b6988486a5089050203004003c00c0201101c9000b003c1d10507101d25030303820006540d489070240d035034072441d020f00c0080c03556103081004098840e4004101c14001032040d6420141400111802e540f040821850b10210484100c9090103041000c9d8840b82384048900300c0440f21003212040d1403101804040c0202d10005490781a00c002d00c41d0f240410303134060020000b20308e001202035107000841003c00d00c1004200d4002504074424026200402c0e0004040d01a507210802089400d1120f1003402e050305443e8031012020034400e02255040c14081c0c0c94840d96450b1058000340300c2400149882c2d0362400616941d00403a40c001610b00035190103a94200300a0140d501051000302846402075024030120b04410012594440340541d0340c00c1a201c20340100448400c0310b0703c030420009120300141e41c40300100319140c4035100004441c41c015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 250509712 1250 250508462 250508471
    0x6030209090f18030403210813020103110f0d050601030b010201020a0203091207050a23010302070807061509020d0605040e1513061e0209120f0d080606190c05010f1e050703 76
    0x480f890a40d000340e8000c2e03c00110021041d41503200760041d440500100d841e0907101860020051600d170441c5400c003904050351190044241c505400c1141d110b20b8041410300d80350740c030400022016010446016000030308010880c1c1255005009490007a04a6000740d824101c000081c0000c0e1080d5480100d003a20400c08000b80d240c8902c21100e01410540d005e4101c0710401c14007900d8070043d04043c45d0b040600c1040100e002c04c0046050315022944800c011814074186031189000200c20b4001104441c40064500c008089942c007403130485009440c24088050b007180342c20340b9691005100c48241e181071000421402d081ca5554406903c42c041c00900c0318900741240b0780d405200a00846290790000340400f85150540c406000001d0307080040c00e61400b03a160540d21303400000c00020502804902103021555181c090340c1c0b410240004000d02240b0700a001080c0d0000358600340e800e940307003500c0300340050568042c0c81c00c644100801100c105418401c0380d0000d1400400c41810103a45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 250510962 1250 250509712 250509751
    0x70b0f07050a1a0f01050d0309260706020705031504050607140c03030a060e0f0c0a0c05010b1503010513022a011b050a0207090b1302160602030106081006030209090f 73
    0xc00b600c03490b107000c0b0f240101c4007440c001114a0030000306803c40d621507902a019000020741c0411400c05590002941180484422004074035000b422072000b5114050030001003034040c0d0001e131510496100b00c0c1240c18649125804403904074090740c014166800000c0003443c0d09000e000241c108503000c145c110300d070480d000c41c0982141c10540c0d6080d107880d120714041140f01c1c42c0101c8150444e039842e116054505007003c0010783d80c03040c601200b0070b0103a4215041b040c40000e40c004001118003400c1900c024100c0388900000794002d0046c01e105030340050406210003075901c207540c0b5142c1e00361405038901d0844040440f0529a0301441c00941d901e406030124000e0f4800e0b902d069100d40e9803030305900c50381440030180c24400ca580242c2180d501d407212000096644018441002d40d4403000140e440d07101030b0000484070841813000c0c0c41c0318000800082e00f240c2c0201414490000b21201510342d0303891307000407001d03031080b200c41c00c1d44403038244003090b0f94558400c55a508240c0340c121102444d500b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 250512212 1250 250510962 250510973
    0xc1e0e06070f120801060f0f0e060c060103080405010201061505070f020a0503012f120408030903130b0a0201150605030a11090a06030b090601080702210d0501120302010b0102070b0f07050a 83
    0x105030048640e09400001c3d483d50030f40114070315026080030700380200482d54075080100700441c400324136000c100e616042c3c100e442d15540202c48911900d05d003560560368585c00d2418280d1301c14402d00d4019860240002604c4085803440d4000c46004e6031001e01c0e01c0c1c9151200743da0290042c1042e81d000941000000c3c441d902440749102404507000402100b1034000b440000c0c115040101a25090040142c03290040c15400b819500582c0207100756241d88810101a00c3c50180000200034404004404030340300118078040c01d00000103038020300220b540e02c1442d83c400c02151084a02060003407000c2041914542c0000580c0c440407081d03141010b5894000038001040707070b8061004241d641c104079042d42494030815511100c02c0c01d0960450601042c002c0d81c440583c0d000d001e900c007403d410302c944588003208403103801074009020310031561500084290001c00c40c0c011005503107068001c1e101c0c0d50020034220102c410245840d42400c920b84070102050384820401c03030341406400c0710280000d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 250513462 1250 250512212 250512233
    0xc0d0e010504150b0303040b0d15290712080a111812010e0613060929180601050d0507150c0209010803030603120c0109020d050f010c1e0e0607 63
    0x106610011a40782868142070301c0c042e040020034640c0da030411041501a03140001218211104d035034125030f480101c0c1d18020000c2c00d0a04481180440d2030200160b000c0c0c98000e1207560141241c403483e10440e0070003c00c0301d1840340f102c0080a412080d1101190f0354042d00c40700342e12080016001c100c284a658444100b90b000e00300215070341060148051350b42c100307420940281d040b058020422542c5c0b003400c039644c2d0030008101840498aa041004c100201038104c0401c0030b40c410020809243d6040694100039070f61000210813801e5a00001d82021201440550b0b081e200f40181816034200020710421200d00c0b0b1041d2614451420001415191085400203200301541c8090400c00e0902c100150240c040e403060344164801c1c0300340103040e600440c6007500100710001d0360365601284925140074280c5514081c0d4030648036403114040c0103002c607041240d141010001c003c107240c1e0802c1510040b41c03900320000c400301c003202008452800b60f0005030700140010f05680c1025201c1d0341d00341100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 250514712 1250 250513462 250513481
    0xc03021c0f020c0105250c0b0f04050405090c010806100908060c0318070308030105041a0301050a092901030b04050102090306010602030a0206070801061704060e0a050c0f0105120406050c0d 83
    0x5801e80022032019a0502000d41403400900c0e10a1800000d0140056445140080010326071040c01221041201246000b0001c11b035000c0d407a03403691744005c0381682c2ea80040c400e140c01a0300b00030000e000d02001003101d07401800140c480e0402901c445d014001945080510740b014008007003008940380c5010800d007403064000203241562886c19401890064400000d640240d40c0800000d20018110000b1b072415a10141d50000b0010700241c030071030072401c2c035002541e0954a41000c0c4484d00031300c2d070001d40c995800344280c17000c0c203c4244c08103c0303203103100e0800410580740c0d0001071001498500413941c01c640110300140c2440714250020342411420303400080036a10004122020940500507147d2002c04e50070f050302c05600d841c001504180740034100d40200344860f0005000c0000b240e0003241c20300b900000b1244c50100303518090b43c0c0c030080240a6841200140201c200030340c0f003002100d40e0841d51001580c842d490310740e40c100142c240500245000d080c107002840c0f440702c2620039407019 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 250515962 1250 250514712 250514717
    0x30d030e16170c0103050702030a0513030f110a050619081009050f01030515060604030f031103040618080304060c021c0b04060c030509070b0a05090616080a02150f070c03021c 77
    0x1800b10b0140d405240c1114020424141800d080801001d00c2d004402e070750344940b150a005503281c800060503103010429403c010020f80d1b0044c0580300344900030707a160581c840e0544440e20b60301c0d10354040003513038010a640c0d007816584100d01c903100648203502d03c542102003c06188013883e11a4884015610115400d20840f070a40e07004005128042281c110302084010b1000c0180c00c0c1034000c10034500c15800701605140000c42c010b000c144c4603050312081070270910305580e140c40d04e44000604004d0b80c5030440d0203103001c0303400104040c07030301000301c42c11120b0f50b072210298409586d0901000c98068440d80b9080c2c540d507401d410100ea9070900081c4158440c0f10f000401214600024003203c0f4040c0103a003050340984414002c4042040403200713001e0803418201d07101c498072000030300c46114854200000c1041c42d030b003071410000f404000d031a01403250713000e03680050f00d00a03407200d10010440da41d4130078460740004a0403440c0a510240341c418003910640b0346040c4400c0144642c40344542c2d60000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 250517212 1250 250515962 250515989
    0xb030c0625050309030d08010302180c19200c310507050702010f0c03080601181a07062004090c110d09172a030705190f0e0402030d030e16 61
    0x1c42e1400740006e0651b1712160412400650668012899014007101c42c910b004248001250403100c03a0415a40014405e00048844001981c0003c1081401c0f0500c100ca007049400c044202103404692070080c0e200c00f41440d0f40440c10152841c4410148d000c4d4096402c42282145c1800451030049621800290315410740e11551840018031650501c0d140310300300580e11041600090340f104106405c08000d1030901d8194240d6461803010b550a507105084428040742584100c14511010f032103458000c900c100410701c940710a41d04140c01d1a0480c0104903400c1100380160003c6600a8903c1a02c601e08815207125101c40e90345014803040724500812240c160802a0459549010b604030160074080c2a078030285021404595807544415440c000c000351020055442c10000b00008100052100e0040700c0240003c200030700f03260140d880b03d0603d55102040240c8050b490314007a40d030140081031010f400d400c04800a144a4a81040d140075010030ba0b10b1360101c03440d980001e0034192080d580d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 250518462 1250 250517212 250517227
    0x90a0303090501080a050c03040605181902190510180306110315010504050f0405061507030c120c031202210118060e0609060d0f0c060503010510030b030c06250503 72
    0x1089100005c0c1411125410201008201d036024819250855070116001c030790358460411500207403c00200a40a902c911800d483c50907054090308201035000340d90559406681d484032041c2107895001d40c640040d10070b018104060303c91f4150115201c1b14900700400c0c0c5480e40e590406546c1201c0303000c0001c1001000307102e0651108900d844941c06e090a18910f4189800b000c2080390f456420200d100303031f582d000041c106840e070b10f8030601c040703059040da685d1b690b01c2490050901c0c9414041621030f00000c0728040c00250240b42c01100790707a0962a03103a00038020310510b102139030194444000c0f00890f000345500c0d5900200c1c1180c041c005072401c8810129903880004112846a404500301500d0002484180c0d03c03004d0040341c10590a54401030040318a050413042d20728130210003404115031400001d80b244c0d00030080c6040e510103d44951860700403800490541e901d003078015134540c200b80e0140926180c110020110441c0d107000080c3c54810b044080301e0b010402010589071a000001c911 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 250519712 1250 250518462 250518467
    0x30d0c0b1e1003110a0305060c1303080406020a0318050a0b0325110c091311030a0b070e10020c0a061805040929010e06010507060b0907030b010e04020f0904020708090a0303090501 79
    0xc228a59040c4c60b5003080d1446c5031503050303507030b10302a00ea070484100000f58041e01c1e083c0c43e42c0050113950064030f05a40d5030390701d18000351380312038464081c0c000070104d8500000e100711421710b5508840c8014124031986043c42103600d000da00c05840800fa407038444c12400000311441d8800c10403c1c8054840c1c6030103070303003a0700010b05009459290511405102041100d0300c0f0100c1c422078481508049001c0504180300f000c00e24101c400744000d4034058420041005442c0e02410710160000d06980c08490800c419000380e0740d90b10802d1401d540a28040d105000c1c251040b80007281204a005900c03120b00c0d0740d174000c10704032255900300b81c40c0010b06101c400340f6846c0c0c00e1455401083d04a095081941c94016584240c8002800f03160400c580024070405200d0301e0b170000881d880b070041c1000003900327000d100035001b09200d05800b4086120710141030321038038261098584052444513150314090403401007000075801440211000d02c024845456242c4506910b000611300ca9101c1b8400c007810407002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 250520962 1250 250519712 250519733
    0x91006081b18010315030b100b0403050c100315081b03030f041701060302061218030f070f050f1203071b030905060a0c060c0518030d0c0b1e1003 64
    0x4103818003400c4041058a040021540c0300c0c0003902c1c5501c00848040012400782451440031600c404d01d9800220034020508009409a14200003081324140d0b9003050346a24080c0307100180080d00f1850310901e1a08261103204210100ea24000825140445c00d84180b081150040c040030352103024a12143c0d00803010604070300504a00a41c108024000e688600d445103000701c07030107901c0404c107455a1074400d4000d000a541d0040c8007607298010300c2c01305401c070314040b540780512548040503a10f42c4c002c040102c414004a9100e07541c54103019031182030707080d0034840003201d45104404c00c604024205010083c499940d41e2030303140e03a03400c103140d00616070043d42030000c42422155120707500090300080d2020444406a41c0e50ba2034545c07001003039911140300900a044103003054010b0895940c050020204414490101c16544440105256031264200741d984081002a980e8401041406c0031042d4814061081c1c16082c07402d106003c460071344141c4600c0d002c00211417060003000440c1c000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 250522212 1250 250520962 250520971
    0x11011103150406230d11040f0c03050a1a041805060f06090903040503060403080a0b040f020a0f03020c06060f1f0e0906010305042a05120303041a010e01050402030a020909100608 78
    0x8021360481940780d6880c007410040d0414810101e501040040010034000c888412800401c104010304515103108050403803000c404000034544000100c44801c1403280661000c1d90301c1125035208000350603c0014a0400502c107581141801a0f00008004000061154420340c01c0103105003000f1302401018400541519402c1e0407e11060009407000100e1a81c016090f03d003280864880301c40c01e00046c40c6078000b031504642060344440d810140f0303400904076a5459600e0508200c030442c03044080780560b003041b200d1070300310b5000304036507240007200c1c44400c6034024030300352840c0715076803000700100c84000d40d07940407030341a0031441000d24001542984c8808282401d1055261550300c107682c2c1816111110f445c4c0741c0c007800b44108649907407103000240030003a180d15480181809103a607203420440e411205001c0e0307280c0101d1400350f0400c140e412181d200c00244016400c0008010103134000803c407000c0d0507402c0c01801c441e651007248150052a0186100c07000904007403004106240080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 250523462 1250 250522212 250522229
    0x1b0c0109060203180d0807060606020d0306050a0911040509040606090f0b1c0507050a0906090e01020a090902070206090603040605090105060609030a080708040f151d0108010611011103150406 84
    0x40200701154000c070869501c15006180315640c201d03040000b980710b07a107801000d0322114003c500f0300c080101503805501600d00c42c0e002c4800d07014040e08101c040da601e41c0215500210124020400b10455800200c1c1d0283d4135070600c1d00300303a15180880e80e0904c1c22602503074030b41d45400b000c001c0708066210f10381c0300032400c1c031050003005982c1020400025414560780f0140103103001c6003051040c00d0000001404c00100158001c0303a407403070502d029100901607500458604412200320758814403c070303025a442d68413621030a81c90618420b000350040f0000b40e0300440100406142a41d411005510031482540001083e080003181c20b401c441c0b0040c01d081c0100b40030023884804be07a00080071142641d0000c0241c0e80d5115628140340640259840080055159840824203d6181c03910295580040e44c3e4840f220744e0900003c07402c04144000103021601c241b00502500b44100340c240c0c2240c504400100e100c401d08201035245910440e480d04510b01126800c0d0181e1070701d4003c1400070a6001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 250524712 1250 250523462 250523477
    0xd060506130e0403140309010b1504261603200f2d0603010909170f0301090e0a051203102702031e0c070606090507080a11040305031b0c01 61
    0x80201a00180d020b0242c0300078140840001000c151003141c995407903d44081016440c1d09040820070b01034418420103074481d0003881540c60f4041d0802d0141c0e405c03103e25224006a65940060035503d61040004202c564082c103121154a048190310520096108415006040b05616080080c0e0364445030a80d1040c952105001141e1b1f03550244503510310b4a0020321000d0000d0750541c4003542e805000e40b90781001c03000c0000901a81d09034022000301e4001d10300305018254203514102584071f48000701c49001d00610060140d111107501070a100101c01c1c0c22245601e10a88801d45000c1a410230012184400400c0010110290002c00010050200100c0e0b00c103400900c14401509214440782d03440e079002c0b000540307042c054204581c0c00f8041d0000030006003801061300603103a00c6400d050318454206000010064070030b200e070038850381c3d00f581c1c0d0401c2601c514000401038945100c04009010092001001244082c8014010492401c0190b25807590403d551800c05002c001075a040c00100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 250525962 1250 250524712 250524727
    0x311120d1109010c02010e010c02151e07120e2d0102100905060f071709010507030507080708130c0b0f07020a0f0e0406050603100203011215051308030405010612080d060506 76
    0x10701ca080113140e09003090740200d0648001200e095003031447c0654400c0145200784040310540b4000d00300400a0503810071014803086040e840d510130248010718480c0c0d10380c3c5980c6650300c528400d03500d80030001e08410100c2c40b100c48000e16070025055002c5160000c00c00c4182c59a01001001d004824203030041c02040f03030740c0c0c9032151a21401454079208401c0703400002d0000d4031440b14042030808021021049050821a0600030802110301c0b4012901e81404240954020034000f44140c8603035980300082c0e82c9a6000782603000c2c0746241207903d0301e8840f80120702c0d03800910241100d07030f0800706943d03100c41541c01001841000356002030700c00b007070401c3c00307004440d0700c0c000c42d50b84190408008220b544445000c03d1078031028403000e121071031010002284000e1981d096540850081e0201c8410075103845200c001c4800988000b0382d403c00f40811000000c40100185510a01075400040c031166150500d5040f509264003c4030b0181000680c4d400e071401c0c51007244082c08043e40c0781c40c2402da0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 250527212 1250 250525962 250525967
    0x1e06010f05090406080d0c060c08010506030103201f02070f24020c190501080609070516020d122d02030409021b10051506071505040311120d110901 65
    0x4000d1210400c0303400208100181c466070081c1c0c000344002e008407015940280c50042c40d400744d003442120518200078070310740300070b00c40c10b07885041c1d94000340303050304d1a441d690b542100e24800026107208001c20941500c2207907a010030100a0102c49c00301c1c81a50041808001e007006d106803c8a0a4010003000c04d01c03100b04911200510b907103030011403512889039840107910b4000d0300c00c581a8803980203024803a8421403030819808840702a22280200c4d1114004c0241e40c0404039460710000d64107100d003031140c02ca00c0010705001800608006120725030f03901c5142e8480010800381001c100c0c0e084076814070f0f0524000e041454058403882c0041011400c600945a01c00c9104d60049580c002c61003003034008030170312851051030050048444000300001f407603010b8a0201c45000583c06884426400d6051110807500c4240d0b0005151a6402c41107025400406001d40705408012072a40c407050a00e1080155807050b03440e030582c2e075848010040e4a401525a000410701e030506040c0101c0450f642c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 250528462 1250 250527212 250527227
    0x917042111091b030709050f0414040602030703090c09050108060702030c0615130203090a0203070b091309170a0503160905030606090a1803090807050105071502070302010f0f051e0601 81
    0x5108030b82c4000c06450300c2c1c0903100320959822421031a0b00d0000300b4031016030742040c600411544c4c1a94040101e0321f40c0ba04200031200840405c5102814190010b0006403482d8021507000e5035608001a098020b078903440b105a500390004244a5655401030001090400c4480e41c0b000f03040c4021842c2129916035907407944000b40c40c501d400c41400070480340313039910050303443c5200c001030108646070f01c1c0c8000c06943c0d401680900341d0184c05a41d10200e01300c90003034200c5801075005421030ba852501811824004d16840300c0580d54080040c1a21118807006002042d814032656140b9840342400d800c40b000c039200281e04034090200d01c4508028640b408070721594418804c4641039a1541c031003201401802c0c40400850103c01103501c00d03010540c00c030504800b80d500038400c0340ea4041c1c0340da0041d1003070b105846016048440102c002100301e080343d00142100d41c031a1001140c031148829a80058890301401d100c0303050340701c104108981e021100321a4003241101c10040300340c00c101d0b00180c00c2c2c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 250529712 1250 250528462 250528493
    0x303030218060d140f07090e0c090d0506070809010501032301090c0f090f152706091a0d0201051605161d130309060f0309170421 57
    0x940c010030441004240e1410080c445080074003040c1d5101080042c072070040520064a02d030305822080801c50b522000c118851041c207513600d81315013690604040c4030981000414000040008006054298540802c42c45e90b1b01d10032001000241048040a025000002e141c0d1a450785401e00400115802c3d4240b0540740c45649030a11140e21034107281d60150001c0c020180094880c03100005040b082100303100c04892140804100c00c0c48004008401e642d95405c4155848801100c18080507941400d0400f2044d012001240c4002c0078071301100588001d540800c40d07007071380c030500100300c0c054030601d0020b007600455071448180750350b0b8000f0303069003d003a448245008071494448204401000901640102c10600f018041e55039220440c445030021014003849000f100824502c103c541d98900e41030398551500002c1d142030078411101051404038090405031a8002c0f80c01003030403c0c0700e500491a03861055a91a03084c403043d450703040400451200f10b22440091000031170b1400100e590070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 250530962 1250 250529712 250529717
    0x50c06040b0c09090411120f06010303050c0f010c0903150c08010306180506040506040203010c090305060112030e041a03060105060406091a09180702060c0f0d0b2403040b010e0108070303 82
    0xd61600c5122403003038010f800049411400f42030503c03061089183d1201164a0111741d800c1110806180d035070b44803061515141c201d0382c440c100510009000c1c4024200c02c01e088030844480804641c01c55081d01e0740405018041070350064248203100300d440303000c0740c0605d060710140300c0c41c1d40c0010024202841444050155540c3d10300d4014050306000c071320303841d540e00203040352401e0402d820010740f1010191022403180d80303001c00c17004106000d240e09204072500b080c050302c02c9170b103002c1e000130b140210f0700f80071810070008600d109001d50395031041c00480c01340840b44427002c0780090306040c5040c506803c0540f00302c505220030800154046088010b55100d003601d0344113000e000308469214040c5258460340205131604e44450103201103203a81c403400c407540c22510305031902112081e0301d1154410841142c0c0041003d404081416000b40d9490341c405440403000c154844c04102104d4440003c44849031800400d00007404010306041e0b024214440f401c100d80c0d45440e440559900c43d92100406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 250532212 1250 250530962 250530983
    0x100509090a48021902010201090b0405031c0608030406031d030a081009060515030711031903060f0803221206060918111905061801020706050c0604 65
    0x5140d000c0c0c0203500c80c114440c40c00e4030020200700c201064940c2d011100c52038154030007500d000d240020b00b040c04081101c2c0e000303084c6407455404d5507240b003004814243e06540d00c4409210000361500102e42c481d9000700c01450301c0707000d201650071110fa1002c807841205824660b0603c4030b401e0100442c3e0845016080001e54042c040316058107540703c2d00000c0c3e03102d00010403c101180d4200711110b116001c014552003129449049100440391103002c0c3da0b8004420341041010300113070b80f0045422600c030742401803110045c4008a0f107158422030f0b14003032a03900c5d520000c00e065010f01030180a0280c540b06004268200700c001903503030081c2c034080703443d00c10b2400a001d08102141d103c1c1029064210040c2341c10300d0581032420103841c00d4800c0020320346c5000381c1101503020314602c486c0000c3c2c0c05226608003516040030880b10540060141e80540410f0800041c1c40c5c0e1180001c24901d0b00036200c1c2a940c50b4a1800641850a554001018020f080290b000007110229190f42d01c954044000c2c80e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 250533462 1250 250532212 250532221
    0x40c05010c05100515010f02030f0a050304060b030607030b0a12110405041416030b0603060714030604060b130602010b01020706050a050f190306030203160f03020402160209070306080c10050909 85
    0x14544481070080501141c03071300044c07104464010b811504108420f0703d80440c00159164120303920311034207000590469007482030102e0f15103c0e10055400c1030091002040350060b040029052080565603900480d40c1c5404010844c2007180b0a840102201041c0c18441c40d035507260030100085a180b403c3c801c6585100060402400542d21740d01c142100003120084d0328090684801d807611404141d8000c014800020110320300060305d248500c2d2070340c2d0350445020007501c0404031600080c02580c0d10945802c00400c200d0076510240c00c400142d0100307924145d140c400c0c06400c40b1080c150003030464000b07a00a000142e04002110030441d880c1c030709156180350540c404a564025001810306e0942c44070709440b01d20b60305402034016280224107440d0401c0c44000c450400e010b45100b40f0004602c05c11007000540341940c041c00c60419000d001f105920503a87c0081d25032a001c460070b0001c0381da80c0301d040c08240d0040108034000903095803400302000701000041e0242c018943d1480c442c158080005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 250534712 1250 250533462 250533473
    0x30b040903080a0f0e06070e0102100b10180504090b10090b1509152703070f051509150c060f0f0a0b01090305010501080c032413140d030b0f0306040c05010c 69
    0x1030450148500681b0f1090802c4100244065600044030780140300303d40000c054003480c0d11403141c1c1310074000c6c02c00c40d00b03152100c2c0540d00426481210010070b03031b880c00d00148686583c001c000c0d00c18882d040c82e00315031403d0034240410b0300050300a1060b4524000091003551609174080056415400c482d5803181c0c900d0340010240442864092103042021030790312000d011500104040011614140e641040c0e0303c4d0506a07140c403a44250094091404000c001d00e080031054154030382901d1490501e02103030342c0040f5401030308084048070f10080c0040c95600780720062008a030480c07100c07024200da80c1050340c60280c0c0703003102600c0c0000d51540c400c00f83e441c580c010a0344800440e4081c0c0213201c05d6a41c1d401c0d090b1113015003cac00e14000c1c000c56106001440044e1010380140024049406007922540c2c6420041200030408503008082005880c0c0f110008100192500499a0700440c20704846400d10007003050f040307070541c020381c080070030702c40000c0d03003806200240d403030070300c1c14141c3d042803801c28 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 250535962 1250 250534712 250534721
    0x6032304020919090b0a0e0f030406110f010518190c0e06120109050319230c0f030d02090a0b07050a150f0203041202120403050303161e0206040201030b040903080a0f 73
    0x2c01d210504d022a004204000c0d00703d514420011044108001880c0c00d5110751204d12441c0019880c3c2c00270401480914040c0b800c20740504800d50454440f035000401603421550300340c800c01803440286402e51061a0b0030091030f04100302c5120100c52941107a601d80200b68098081c4140f00d002400c0007419541f22920351700500340506000340001001810700030349a90003100340d000c00c8070014044c00040e0740210620300815003003981483d011174141c4103400d05d03600583c01022044c0200341400c146100d040014140c100c011090040c1e80318140010014400391a034400030254005007c54404201c011880030310407600605080a450005552100180b504041004071a032020046c030040c031a6410604840031307182e07000c032482c0304070001c06080305006520008005900410018506400011840c0d0b170741081030502041c0f00340070403c04180220700c40040c0f401a40528208011b641c0e26025550703000e1426a400c1151004684000349407040050580b8520f0303498544941c401c00e181c0d0f10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 250537212 1250 250535962 250536001
    0x602150a200724090f080306031f051e0103020f04051f0e01080601080a0f1403070c0303030f0b0402090f010e061315030b091312210204060323040209 66
    0x11202da4480c80c5107404050a01104031500e0b56400119150f20302c0707036062080320b8001e6001700d100445403409a070345202c154401010a80c150007841c01075000e02c80c1c00440302e4000d80c003010000c1624905522001007001c003c0c400050032020120040000d615940300940341071405490110b015901c0d68004109103125030b04103542141d5029001032102d050003c0d060517a03290509031038076a43c0c1c5000c12940d4186011000e02206254020301000440c540401f01d2a5002c004c02d59040c00c13a2034440366220801640b060380030980340c400c0301c0d202607485e12031400ca40e9000c540850401210300c0100d14003d01a00001e41030000c55401c03d202030b80e94030180c80b004084070700c441c0340f61511140000c00c10031200350b044000c00d0810104540b18a40042464810701c8a00754081ca803d44981762005084840c1d2000700601c024010211009a010700107204804406103000d69560710745040101102c05004020103000c00c0da10340d01002070701ca005040c3c0c00903012900702002c2d46030100300c039078820060700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 250538462 1250 250537212 250537271
    0x1504030624060302040f09020301060516030311030c040e34020f0f15010605040b0f071a010e0108071a04120203031611010e060309060103021005220f0602150a 70
    0x50002412983c0340c0c0040c03040e94004803d900155555190b04402c0e408207000c0c4001080051195803030000301c6450402006002e4600890f030548880c030042415841941d100030030314800074050085141182d000cada00600124110341551201d03d400d01040045044445080c002882c07001011901c2000388100c4800c5400590300e03d2891841966901d20b042458807040b00e2080c0000504240540262821030f00640040391400c12810088400b07a8825101110144005800d102c070030111004030300d011b4541303070307030b000d200c0b94145000d0b5032801491750710001c800784080340b0206028110b41c0a440840c0c0081690400ca1840c2c0c0c400a070650240c540e10301a070420100714241408198840002241d50a0300c0c0c028410014000b80700c5140700848045c0502d41c08100104010300b170041001d04503141c40d20b0b2450070a41803070b14110000c03041ea80c070040711034030012041c041c0001c041041d80042c1000d00050a40c00000100401000c3c0010706007403100c6e41d00d101e4900c01d801c400c42901e105801d102e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 250539568 1106 250538462 250538531
    0x60623030303130b0601022503111c02040b13020c06090105090a031e02070b070b010f091a010c03030e03070303050a0506040b0312130f080609010614010903110f0a030b041115040306 80
    0x24814a074109a0002e00210381181d030f40302030001c47001c18002410307483c103008031403900b5140b01500b0301201d6001074285c0e2001a801000128402188403910001040000c000303908000c41ca50001114060024000040200000c1316505a40c500700c00ba0b05400e407640c1005013224407000c00c1c0c07074000e44054011240d80d8000e41d600400c47e403007468003107024000d28401b00c1c01c40e04103903030840100741ca94050000b851000c1c011641d00000581e001c0080c1000d28000aa4078a840340b00411001000545180c00c00f25003004800a044954150200a6510540c156682000326848a0554078003c00482c40000200d066030420300160740310960b090071916010003040c2c00840b542d6002c001c80110114030303160000010300550051400500a207080c2c24441086622075000e64843c446200e10b20700c031600c43c20207a406032604400d00051201c5c541c03040081080725180c00c1a00d8110340d = true := by decide +kernel

theorem cover : BRFrame.Cov 250359712 250539568 := by
  have h0 := BRFrame.cov_init 250359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 250359712 ≤ n) (h2 : n < 250539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
