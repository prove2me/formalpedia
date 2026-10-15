-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:25:32.994759+00:00
-- url     : https://prove2.me/submissions/a8aa47e8-19c6-4b47-8e9f-6f155ba8ecd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 899460431 ≤ n < 899640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 899461681 1250 899460431 899460467
    0xd020703021e0d0c020303090d200415050603280609050a060803070b10091404120305071b020d05030a051330050f16080106060e0d0b1012050a03 64
    0x40300040ca500d0740310145541090b00b8000090f2130b4000315241813040d14003040c80101070400140c014103125100488070340c80514074246130722814805140911502c0d94040100d1130340c020f0381d810a01440195400074142e040c1c1443c1c0b030700000d0301446100f030f400c002070504d6a4000c1502440d1250030425524041c042110301420803c0900160b5400004c0d41c0c652a0001c01c86211a200c3e0242400200a90341141c1c1c480380c1029600d00f00031040d001c0380c034019440f034072100004a0fa5036008404440007952108006800d5280d404144c54011088480090000703040420a01c2d095031090300c2c40d8040c44501000c604049581c500d141c060041103001000c4443c81d034214100303900314081c14804060706901110f0410001c201c00d00034108035031843c4a4842044030101c8140c0c22140e41e5848080c17140b404a036080c901d012410610131b01090943c1d800140c01c0b80b00002880d9030350903120320024503d5030182a4840c000130304039032040d150000c40c1d00500c0500050003641c00d00400d03041585e600d100348 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 899462931 1250 899461681 899461723
    0x403030f0e1e040c1b030f09150801140316051011070e151503041b03080d0509010e070b03060d03022508100207030c06110d020705010b1023130b0d02070302 69
    0x44000e50a01550125526160205c0d4507020000c06985124230b5030403603034182c41c0d010020744480b9004203440b8183c0e05214a5020f001f03420070304069940300302e03541c51440c0440c170083c01c200c503040c405218104400b56003054907104103101c0350725141089070b910601c80c4500c02c00610004103152103c0900c80142900c118021802e000400c4609110140005203c003007181441d42c003041d03141c5841d10145034031420b15552140710703028490282009884506c025441c050040320a880001121070490300304444c131500f15a1040100124511588400d9007940590b0240c0d06502c00301065841500b040381c0ea080005505002c03100c1c1c0f43c4403003034200300d54582c41004203002003a040707040c001045a20040200728034080c2c000b104058095855082900c0c0e0011402404010064101d8219002c0944d260050001c01400c00c441c600895444404812046c1114141c4004400001c098003120429615079159443c50700482e95030012441030744003070b8003003000b204040e4180801c9548000440007050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 899464181 1250 899462931 899462957
    0x2093307030f0f1209080a0809061911040e010b042405030a0b01030902090a0f11090d1e0203100c110705030d11120d0603020102071203050403030f0e1e040c 69
    0x200c411901c0780007091001070341d04428640c1c03243c0d52060b011013500308140103900c0c0e40d00d41000c694025060840c003040c2c0450010f400101c0001e4180d208070101400c0d0800581140291001014102d03044c103040e8000b0007001c180c3d08000c40c0303094020005828541c0d07441d0700c1d014080304013010080700d91000b0f0050284000c0c400d64090256504003030303014000684802c15400680090400c400029048100d0750b0070442d414086a004080d0194000e4040c00302c001d0b42000904ac5114800707003140c0c01a40d05e48500c0c040744044a042c4101181c0380712803480d070031541d00000d280a03000d032040128151141c010305041a80007803030b20000c6403101c00400d5050b04040c0001d03103e0420700c040c0302c03c20900805061025101704511145a85101e614550f140c0c0c02541e444050001b500041c0d02520503036400055404007100742c50035a41d01030399158205070455600719011000000c01c030080110000c0f5285055030b41032500c1d06203d0300c1400e03080c0d0b140e46000a001c155080d0008500a000422038100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 899465431 1250 899464181 899464187
    0x70609020a030b160f090b0a1e0503011d01030b13290a1409070302100207050a0f0617100b09040b031e0610241413140609220209330703 60
    0x40241d42eaa14030387c5c0d07141c0ca9070150485402c55480e018500715803542411058003900400214161030504500242c1d10142e40c1000742084002c1c40003c01101e0008009954505960148882d092040100c0342022030002ca5410001c0e00b0904035071090140c0d01c0900c40100410310404c0800624000c25504924203c440251204002c1c0b2001e8051040310364003004a40c400d03c18680580001001000416183c2c0192246800c00e0302810f004110108081000e103004025994826002080c01c1c00c02e807420a030f684002c42d004118030641098840521321301e2607806101c0304441003031131003141484041c0820300da07162810150000545003030201d81400910008220801c0c4100000410350301c41c02038030002c5074540c0c40030444048401012039890201144016034030100c91f100d1002101071030b595010010a4800c034440540d001c00c009824182c1c60100b80301031036103143d400100509000b0000c01081d50030608140c94903400c003248036407800c8103011024001c104400c5861442c03d10002e9030300a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 899466681 1250 899465431 899465447
    0x1230d0603050a030356030114041208090a03030b030102120a1a090912180901030507082b0e0409020a080709110c062e0603020421110402070609020a030b160f 70
    0x3051502d02c07802c001c1c85698a40e504000b86c44000e4000c100014070705000e00c10700b00003600c080b14121690300500b000240701c1c0308254090100b040180c0740801c45542d0a500401403808502e40554003030100310140200d26030721034403800240360046414402004207503c6107060485e89842428401d043c0301d0b40f0a400264403040140c0080130380d41e01d41e0071403010000e078000c0403500d550240b80e0b1400482000740102e49402168840001c031a180303000240c0807900100c014036000c1d01c07a0103000e84160044c1c07181c12000240c1402900c0050340c00500c0c2c0109940d19038903000342c0310550002d1400c202e010035038410042030b0300c2684911820700f181c0e003900c1350b00c42401070324032035040c3c4030000d8001c010301c0c03c4924030111418440521031040c0d42c5842c050041c0d0000d03c611715034030390514000421016070100c5680501d600048103c61101c801c0c082100039003100c001170300e0301e43e92000038000507201c01801c9800f550040c1c141c4521403a00e010011840001c1020040c01c0092030b2000c1043c40340c101c009 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 899467931 1250 899466681 899466791
    0x10504020c070b04080c091b090112020c1c0f080606032706070206010e0601020303040b0a0f020403060914070b070804061d1c1101230d0603050a0303 66
    0x160351150307440407180c030300100350300019020000080d0024200381c0c000349070b10200d007007626030705450b64800b2101c001000c0303550108082e10104101c070300c0166200301526291407840410060610f011071110918002d01e242e00d00c40d40244003920050a00d811050740b101ca031806280030802e61030605e010504501010384101700407090381c41c022080788541c0700305401c80120f0000311515490604002540d0398401e2160500501c1c500300400c3e401d500c003104403803240d83c120058041b1500c8501001e40200f005a00704000c040e424080800054003900900010500466074065070b0743c15520140e007020216441461403010401440c03000802142c10740b0211a00c80c00d060035070440c03c1f49448109038005000650200484001060b4060403003800840030303024411a80c2a4006440150f40c001d03a0210001011500c040030034880c021110002c2c9400200f102d808110290340c1d950311483c16008200440100f9180c64400b2201c1c1e50301610308941c160600010b08400503503040030700382e503056191 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 899469181 1250 899467931 899467939
    0x80f150a030f061b05040311010309050312250203130603060501090b0304052d01060b1c1109060301060f260129191b050606060a1e030f14010e0105 65
    0x2ca180140311095003c10081c901c2001070a152104d903d4005040e40c0c403500049600c10b90403c80381072254802c2c401c100b191303980680211700e410051030041081a00090070200c44600d00020300c00d100c1200c0c0d07032110102e045900155100c0508288101c08200c00e03030040d90400d4a410301c00c2102c1ea91004c981000c8031b0004640a55946070390030114200030034441c00301410b0045520200c41b000d01d52503000710160441008000070f503185c5200d80c5680c81000071141d200c40a003070075040355440d80d611103504d1514a4181c24034005039040400c103140c0090344007001003082c502030011030a4200514030540e02d10000e694020040130100090490810f0068524034100782d03070300050b120071543c40d0007008145d540720a45ca980c20069100e1103100404003100006000543c1322481081c200002102030f42d000d0050701d0a42e8440c0d051140d41c0c1c1014900d0001c01082c0c90761310f180c0b03510f18030a008020301680e501040340034941c0b000c0f00544a0309560b410b84c840f0020010403006110f40310700c90549800311 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 899470431 1250 899469181 899469203
    0x906060d030c06270b06151903020405041104050319020d2d060b010201141009050405030d06060228170d09061b0e100906080601120507080f150a03 65
    0x414030b00d0041c0250141c1c1c1c001042c0e01c4070000490b04c646100e00603403601c5a28009201e6407184140720790401c00b8207200500110510180318201d0060712428440b83d041d10700113060560b11400101600d000c0c107140180c2910010341408681018003980ea00038000d0039014401000550100d0041c2c0c148107806800040c40c070444201007110141c0814801d070030903080700c14610b04c908240005001d40d140460140d881c080c800c0c0760400e5000710152259203c0c10316064014500900d440240400a01c21502800200080d91200440344600d10290503940d008101c00e0083c002c0c90404050548940036846124551030000140c1e030b06031306440c1c1c1450410301c6449603001c440074000b500c64038074020032240c140350940d4a59040340350302620511880c4d5603101094084401e003c044a0051f4852000500101c1e0500c15140110881a00540185040060b11100b9070300300044580a03120000000d001d50706000c04a0710300c4181c581c2016505080b40700804503100028410780072480300a0840041d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 899471681 1250 899470431 899470433
    0x20a08030f271c020d120203100b1303020f040b030303070c050f12130902070f060902010e1309140c0f0112060e0f040c060302030c040905060a090c020a0b0906060d030c 74
    0xb0904000c41c28180850140c0c03515003581240303444905854000035a6080700406408191001031040500041c640f81d102424410078048006544003c080f84c0710408000e100003240312000004004032140b0482c600c400740d0442c8104007a44544590361807142b824000c0d90b0225640100c1100e82060b041d003040b902140c5a032402904040c0340b0750511006001d4000000511030030600100310030103070303180031240240d11100d01c207040340a070003c040d20100002d1b031001c0004d5016480503d106005040c5403c2000c40c000c0000d24120901c20038440e296281c884443c20091400d40c42d03101c0c20070560240c1f9406010001081c0b0043c1e0107102c80e4108905503a42410352100ea0384100c0151041b02c12003030301c503d07200c2441b030010700c8151000c607081e040703840d4006003051181c400e480c020704000742c8491516180500300c00103080301500c2c03140d01c0104810001800c01c3e1512680c0040b4510341c0140131140c0a5061a00090314002c000c50415009442007007000c0d074501024414060345800d180c3c0040e581 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 899472931 1250 899471681 899471701
    0x30801051027140306010f03080d02070f0f110103060503281208040c080f2d07180f11070201050304080d0c0e0423011503090204020706050610020a08030f 68
    0xc1080078840c411660b50002d82c0e2102481021007607468200482c1e00385480e100c249944c4007024440c0002d011200b1005100160b5440d004040d401190700000d81010340c0398072900f1214016803012101004110a44010005243d80c90806200242400c00180d46003801094840000c145076002c000c1c2c111484403244040c4c48810900d0396080101c00341040d09418014040300025641686c031804d01440c0001c210000044007140d0000c0c0d18003034000e6043c400740c0c22003c00011009021985d8005c55400300240b0308010f01d0000701800c0b2120312044181c05008011180841c40c15120b0508007411420110f04407001c40382903580c2842c15903901d958500b80382606014010b0742041642c00c0821240100c0d5014008a0310900210340400291264490308118404154005807202e6071030801005005411a404a1280765504020552802d9640003c00301d078040042155040c0c0c2d40c2d400d21207030b03041c240f000e1003000c100c2e400148414021070311400094000180300c186050f298000042d002c401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 899474181 1250 899472931 899472947
    0x2060904110301030818191505040302030604050c010305150607020d02010c23060f1e2502060a0e1501210f030302030603210a0302250c080606010206040308010510 72
    0x70385480c0c1d003600c039612884c1024440d800799000d0110640000d200c0c0800d458102446e204007000b10f00c0240301e0303914001d0b80c3d0000500c0d824040301413000034407002016031010700a581c4101d2052002d0304040b04030200140451390080c00c5001c80206001940070a41c94042c1191030a580450310500002e0300c41c0700480c0c500101c0c0c40010121340e08200801c0d10011241c0b80e41e400d0f01c14407000e4400d5503a8155041649000490705020142d80d800e910b5088403903a140f000783c012036511010844554040700381c4402c4c3d10721080c1540140d110034104a91840580715015841d048000545040090041d0581e00081d040c000c401c9a9026480c56105400310042103802c440e1748801d01c8030342c403012030502400940040710030501031300a4601d400031070032100c0f01084c0404025000541002c0114038202e0081d0400c0e11800e4500300c0e80c1988400d1085424041e00c00c13144140018405103080a40c183d043c100d01500580c1594030980c103000000f41c100c07801a040d10000c1e10300e03800c9516015001c841c056 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 899475431 1250 899474181 899474201
    0x301151b05030c0d08150f09041109310c0608070203130e0114030601050102060c180d0f020a061b0201030b030a02040c110d1b02010f0225030303060b130302060904 72
    0x48000512541401000314900302081500d80310301496664103008110700a1b40749410030790012030000280450314200301c000ea00b260040b1100003000a21002080c01413400740d540c081c040c0384026544c4807068118500f40f504200b100180420305001e5a100403800d0100d0003050240a054000600c03401e00c02c0055508040c2c41c00d220024070f0380e603201203041251080c06081800c40780d03c070342040d982c00d000070312074102c42c0107900501c5540d8800c00b65100713980004018106440f0609141c10703441d81c94644c2c0020903805040204000741803481000410540c0e40d20600911100c4400c10340c00091001c44004650b4080c200820500403500010303080c0040c0d101d0096003d4504424417840d2540902c40c00e81c0c90007101d088600030700e003454054820b070126040746090f03a00046071180c0154801c81041c0e2801449004580c50700d001545c40c841107400d840520a840c030718010082050640c0350181100402c5007002851404a0000d030380c43c0ca10b8a2800701a00607100000c41c4100f82c0c80b554803600e000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 899476681 1250 899475431 899475433
    0xe1911041113060309150c050a090801090309060f050c06011d13050d0c06022b0b1210020f0f03090c13090b0f071407050f0105101805090703170d0608030301151b05 72
    0x105041c207030123005600b065094400040c03003070300c1c04641d6050502c0790b0054581c064545d510b5051908100301c401100215a1f03400b0400d0501c50500860030070804580680b100341c1c1002c030700400c591a11407245900900c1c2e180110f81d4a002000400c41c0820f00865a0819140020b08410076040c890060710038413080004c2c810f02d000c203450302850700d6050b070301e03000000803c00d01000c03145e039040121028501440b032003c1d0300b100300c90081d040c0c01c5600801148400e44810340c02c01203d110824101d1300112400c1d0060380015005000e58901388027a40c5032070704000001c01410440d6200d110302c9120052000840c1500000401c0c80d1034040c136440c0c0320340b1481c0002685d4540541c9003060301c80c0800c0d60030203041e600305000725031500308252005080d1048003e248a2550a9030201c07005000c010b03044071080c1c05891408804200c07512000848041c0ca601d01c241d031580141400c1040f04c1880c0c0c81681d10307410600041c0301e481c52a9800b140c542ca5a86051001d003036000440e21410303694410b00410f1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 899477931 1250 899476681 899476691
    0x81902150405010b011116050402030402030a0c080a0b011d0a1a121608010b10050a090504090c030b06010305011a07020a0b0403050d080705030112060e191104111306030915 76
    0x8000d01500b00110446083c2c0e42d5002c012a18850a030751014842c0c5414107004c0b501f14140894141035018690050008040f00c051503116110005002c4c00d43c2c000140682000c50b001041c0500480500c0c0102400c000031100101070a07014209050050401d5a50700d450740f2150245071110750580c168403100800903115851103142c800c0d41c41c040208100c4400303194000000da1a134042c403c2e00d40750b01c4040d2000d14004c0f401042211140e00800d22174082c004482d02c0032a19850380d111341c410389803041c00c448800300d0450424403600e800043c0f03898100b6090030f00600082089648400d0405c5207840f120f03845441500c00074200ea029034024400310600814004144800090700b0744644000341c861040d03940319004220b80b248006d01a4405035030f80e400d00500011040d5101d1007110242d40d082d100307605030491380903a05404211060f02c007411450302010701850544690702c42c141da0b40300140e150207582480341841011501c07c10041c150744494850502041c4205072138689060302003002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 899479181 1250 899477931 899477933
    0x1202060a080c220503250621060801020318060603100f0212160339141b0706030b0d0210051606140f0103081c060504020c03190305040819021504 64
    0x94082d81403150500c02d00c11040c5009500702d41209010586d0318200c002001d850800c0300658100b45594860f03003501d08a0300780000c1804c418410369000d0301c04d001c00960359040601c00d502c0c4010b105081c00100b60000024400343d5600010707110441c0c01c24502c041108144201818024081c4903414641d860101e0108602c0c0c023201114007506075441e03101000120445102d10303641c003001080740c5c0c040b214807505a4000303010038110a8050b507291314001c507000d4054010490150070442e400e9052418003010004031150601000000d8400c900d010020029100009410823205040103806541c1c41410a000c00c0d200d0b104440030740d4458460400c0d4009a450404001c0408054019102c142e07400072450030800984154103c0750040358217803c01c0c0800f0082e80b614601020000400c65581000240c55280c03400504082c0d10141d0155890321040a100c01445104035503a50401d8034220810001413100019038000d0501c403551500701c403020810603450200441c0c4e05600001c05042000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 899480431 1250 899479181 899479237
    0x527040302030f040e061201050c031f09090302030d0c02010c0507200301050f04060c0305041130030c1009031422032d0201050409150b03010e010f1202060a080c 71
    0x600850382907c4188013820802170b1b6608a96007074400140082041010564801c1d00d591000740c102c900780d00d006141a9a403082c03404881035a0400c4003d600042080c85c1010b4940c032038403140f4181d5000030b100310050b90b18014403d1140401c000d09084621103a00041c04490382071051078400900204000e0034989003c0d410614102c070f088030700f141001c45203140a8464003c0d54022135000c001c0c5080c0e004104204050025180d0380010007010703815a40b0050304d80307404c00c0440610800043c554038071f81c10214130b040000c03075442611b0f034900302038031070001907030103860041140e1410602584a40e1466010f40b45190010038000c0c035120040000300c2130201550300100101d485024010960400e00a03441c11031440c1031000e0b010030002d2004001d0b00c41c05402c103001c070699006442b54203d4403000d4a60381600203801c03201c42d0701141c00040c8901510880300d000548208450f20040c0308441d170010b00140b150340b0100b420000c1103008a4038100592055940c00d15209014048031201303140c0c0e007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 899481681 1250 899480431 899480459
    0x1e0705160b090109050f030901170a14042a05030307030503222004330e0f0f01081f020a0e101101060504020c07170f03070b01050a0527040302030f04 66
    0x1905d840c002c1d42e00f0030014150002c12070f2248203060310b622210303005243d5080704503180200007403169515654903858070400d90000754411840380e902d1080b1111203a0403500581c0407034010030322002c0742400500050380e0001c1030b100c042d0b52502c0e016559945040505111070452101007140381c21046014040005810070081590072005240852840c510b04110903103580300d079070403001d00115a0840f41c400781d991792480030300c40d114040881d203990713210680310356042215180030103a80401800000807c00348800d00503c0110010700012500c0c01504811a050755000070340799500148000c20f050040700c0c03055a08500074001c010480c0d40c2d240250084803101442c2c49117500c0c3c900042080d190510a4441c05e004490092100314140240c1480800c81401024006d20944820281000c0c0800061480910070010300a50b07500d0501444205107007a003205200d24110070b5180c0d614a942c40440c00030a02000a024603a00c0390304040c2c0c114486d501240360105400180854400c01040f05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 899482931 1250 899481681 899481683
    0x1021e0303370908041a12010b120c0a0c0b13030201050615091e09161b11011b0203010e03040f121a0c0408030415081e0705160b090109 60
    0x400c0d018a8950900c1c20a40042c0142507a1220125146003802400c680c802c1e104244a2070710313149010380741c16465003d4550006c20141141000600e800c1d003d01c0450614014624048113070700b4a483c0840d800c500388402462000d10031350124050320400d105560000d0f0b5507800101a6140d0304001d148030498420800040c1d0240d0b0174080418004c2c14152103503400b01c0944001c2ea0b080501e2181004000d9501040c00704140d0030a2064084642d5036003520307400740f202e80b5820200c1001000000d020109440c0c200e0b0000040180c80c074020402000d0003035001030003440d01100c0007a1080c0200d8113101f051801940661800002108803d0004020000c2d03554079954100d03080d42d1507030040004100b266004240d10076041c1305001c0c42c0a01c17100c0c1c580040c2c0090500e418141c6a118051a5070450350110b06941c074001008440d4035044001da58005020300300102400381900d10003844100050400800c101000817020254144070710b00382130030307a4822085074003818a40d50850280407500d00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 899484181 1250 899482931 899482951
    0x2007110a060c110d020f10030e030412020102100612080a02101d0727021c1422200d020d0609020f01020a0b01051c0b0a090c080705060405090601021e0303 68
    0x14038481d4501e4135aa5044640390b001306054842111401807104c04e400c09200c1d4014140c944035822000002030000d803014029076021409466104d0000902d081c80010780c01c01d8240c580340e024442d201003170f400d5900b4660001c401d00e95481000c803049142031a01c040080006142034024054590744607030b0880c08034000c2041351700141d11117401c0e0481c044e4000d00c44600740c494450707a0040c16201e170060701041030303100b5407003440803601407055081c0d400414000305c3c40310951080107500040c405010b815a15101c0c83d0f1041403107560341c0c1140001040b5030002843c0b500e800070020300d64860081c4241c2030380c09003004035220701d41e1400b88050b103040301c42288a0340b26014087c205500c009803c0481030781201d8010b1131a4a00414040340ca01200821916903440d01401c5001c502e08544003800380c40e92042c00500c011460908500719284c0740c1200826800080c42040f10755a02001d131010f442040703800500c0c40d01c91000507860310a140c0c4818501039222210b00d81c9860012010b188141c00140c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 899485431 1250 899484181 899484203
    0x15060203072d2102030405060316022401030c150c030e130218030607030e0a0b040309030807030f140a0c030e06090a1706090a0f0803090a081309060503012007110a060c 74
    0x343c0140c1c2caa000d14026660050418000264160700c0450019041d04081c015107070424180c600300c0c1d0b002e44603c003034048800c040c00c0040080080200380358005058241e200708450701e45600003080d0b000300305809000c0004184051010369504c12512001c903502c15011540c40000103520340d045010f4801d807034440d024010018207002c1c06800341d50181950034000d001c0b940440ea8540403101c6001d001a800c03c800460040001903103c001040d600c2d0207a1102081940107035001030172842d4491078460340210501501c11405d410000111322b490707040c180207910109a1001c81e059028038407600383d010302052400280382555550801040344401e05480700780d078403026a00c2c0c3d54140c0c04030003822090110b03c034802040041d000345400100b00010ba8241e80c65a0b00c0b8a28160400407060904e1b00915508015107100361103500010f0005400034442102d108000c1c105103440c40c0041c01081c0340001e0200c04200e0142000d171505200100107007003140c0c842000500e083c410b80011601d0b0103080c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 899486681 1250 899485431 899485493
    0x12120a18051503060d0c0902030c0408011a031b0102032a24010302010c0303090b010608060f0409150506120a0b04110915040f180f0615060203072d 65
    0x20702c02c00250550805650340c42d544a003400c1c4080c5134000e84043c1c0344625003078400700704d140c844e00065004031740541d00543c880b410040e13031a003181d0b8090a4a80c2e002d00761140803495840218900d201c210742603000c03005ca050308000503408c40c4200c003180582654203400010b2415000307045101500c00d2802110001d0341c201441208412042e074010704000000b8004100540c0305003603011170940b1924010504140079568008004400c0c2c2110300402c034030328100081030400381c80b81c5046410484081c0002c84154413036550f000070542c043c0200f1a22100050156140c0a4030044041e00000c229042c00c00309040c0005403a03c16201115240c00c104c0603400145819016540202c141c2e1500e41c5d01175490f04100300080c1400f0020304222a101d20b00520740392101008841e40a0256121014041042c0341c20000c40e00b40301d465145a4014580522542d82c2c00000e462036140d02039500001542c0060240340d5034010741c0642d00b41c80d0401c60496007004800030f604422008403041c045420341c0c0c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 899487931 1250 899486681 899486689
    0x3011a0403050307060f140906060102190b060d0807050a05010b010224060907030f1505030f0312041e0b0702010b010e01050a050717090603040302061501030b0109030212120a1805 79
    0xa074400030b0402e510900000000c54403540c807655506009100001e0319045400d03020a240d081120340c2800c94100c1001c00c411544c0500130701d010115024018051300540365640c001e000b9000d881240035030049003200c0c0800074503100b1103c480b07400c0001c0b42d040c070078545002406084900901d0b40180109032400059880d8104050550300b02b5644200c00c907690344060108241c0c00a10b00b80800d616001c1415803908544280c624a0044698480d4001d040000f40f51400007101d90b50b1081e640200300800100440d0200f0a8009520803541d61103842240c04020300d6001032440601000350a40c180311009405511a0b10042e03800c0e00c0303034425201c8100c0151428010a1444400328004001810000b6501a4000c9078412040300140c02d01800501140c0c03960001c0b034044016900403418880700b05c07420034220310001001d190510403280b41c28002000343c900703480000c0c010041d104102440303020500c002c0c4042104004115114401042c00510b8410b022003101c04d080c007111408149414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 899489181 1250 899487931 899487937
    0x90601090b0d1211011d030403021512040215072f09010807120302031210051801080a0303020a020c12070515251a041a0a09420203011a 60
    0x140004000304010b8098005136009a0018980c800a55030b40101c218400311211540b01c0c803520a100860700d880c154410f0000490354428907040c41074041c014013148803020041c061348680e0580384803006140d0415078800030700925400401c0c100464004e4502c0050450b400000180020050a14200a84280020811b0270700903540540c100800a004641010704d903816003e2191040303d1a03c40a07036283c02da8200e095801545000400d0410001454444558100070070f03c1010f40015525200480b690345446c810002c05054001c00c04070307080c900a2142010010010340000900e40c400b50300103454001d14000c60780701e290406a441c0c820039000d800d65840c2859007030341c07045c9a610304455802c00411444112107801070000c048819440c00041940a2445040f5501e03c0009030660b1a0350303028018106c1c42114506460b600114074034508000d03000c0380f0701c0c40342d02c9080e00600b80c1058040d140700b11070031083c80765180c510960700554000d50403503610400a00e85012103025180d040d00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 899490431 1250 899489181 899489183
    0x3040209011409150315010f050a05100509010e01030b030105071e0306030c0315020705100501151707080402041b020a051e10050a0f0903050903010b04020a051c0b0306090601090b0d 80
    0x20a034100003c03407680040740135a142c88002400c4507850400c00c26801030041c0242c02180031191a06001c00450418071542c0d00503010440c3c540c00001d0f141c18004000d1b00130b1030310450410400115039003441c3d0003603110040e410b60140080c002807a02e0103001d41291001c0c3d0784214504148501d03984414032070701c00c4800342c80d400309413414010300d161903110f4510030507116051103a07801c200345000910b0401c03040c10308005010700416950b00d01032021004042201441c402c0c4040d4005031400c443c004660991b100f0303001e003442c1d6030719200c0e80080b50052183c000a0000091303569240b100b2180c0005540c940c10f40b2841c01c866089606000c1d4541001080c050841c01e0b5021000c10b01038080c46400035644441003030310000d6400c6034010b801c810785903c0f42017a40481c100054440c40c909082c081e00c1050002941c040d480c220702c00400070128400c0180340c00440400400f0203000c000700717422000e0017603001012505c07282450801691104001c3c80303a00c0b8854030317101078a039032410007528013480c00b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 899491681 1250 899490431 899490439
    0x50105090a050d1401230703110405040504030e100215161b0809091e09011406040f021e041836050609060a0e030910050c1f02030402090114 62
    0x4145042c050044211a481080b0780c81003400c144046805400d100d0245404000300728202c001803000f0000c5c0b80c0002c05000748042504056140c03900200748400c0360100e420503030700010259240c2c00c04450803542d410788250300c1561100d045004a50000d42e1211420070960342041c2e949881040c8000e4005003e03c1c14046070040c4600e0040454500c4401203080c0a43d0801c0d282c030051500003110700008540c121411108a0702e00800c000a05620944c0010030308000c004222180c3c40421250300001c0000e8451394440043d4100c004c000d406444808010f00030b909128a6003125080094000d8020103000e078640c03085099134038506000d000ca20004140008598501c546d000410080008100010041c0003685400c0010820003a051055000c1409050b060505850baa01511018001100035500601080485580394540782036241003a050181e95107041103600c41c241100009a08904d003190500071200c0f010540045220380c4c401c03240c25480b603132a041c05140d26401491002e0700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 899492931 1250 899491681 899491699
    0x3060501030e070905071806081501020a030c020f06040f0b040302040b090c160f050d110714300d051206041e11041203050705070602060108031903020906160c05010509 74
    0x190030550110b41c100030345152103028024030301f4511150599580c4050b00181090080000c03081214146203d0740d50244058100700480740c40003400c01d016150040d00c540f0440760f003103180369038110817980100098050ba0724107a1746c864505041d50001e200036401f4608141c00300c2e10a01c3c0c402409881800759041050400404c00302c4820308200c010340403182c100c020401000450020072500e40d02707010300d0ba071341030b0320f25260800d203400c0c100c05510500303003650b01c45031b08005943d07803020301100c09112184244081e0000640204c01260900203040513008914001e1407a0340d0000007000f40805110390340029803100c5060000322190031341d0070300c02c0001241c00d05101214540110810300200640706060644840401034819850381c41100814400280d00081101c1404958000c11035800585082e61410004503128071a0b80f80c2d8030310821026070b03044401e50207035064840303014005c0c0c81c1940780d000821081c0b6410444a009071075582c1c0700c3e000024190b10820403110380200250030070300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 899494181 1250 899492931 899492939
    0xa05060a140121150f110901020705040b04240617070806040e0f011806050f010503250b0d2f1b0a06181a0f01050d1407140103060501030e07 62
    0x14410f00c224551080816100d580306001c0707080402224a019260880056540a1500c03c00f00303c81001e152800b03122001d10044140760f80208038401182c1099070007050b610801c03c0010010900d01032031140c62a407101202e042c030898000340400f901c05c26119800d201d5035140c958aa0000704540400000b46030800003440b07428550444001d051100c8104d0750701c51501400d45003901c000520b03201400c034501c80c0660610105001c0e854002c8071307031810100c0950501010a496a980291003a4080751066111101c2003c00402030010329014825035200c0319803030300b00c1000d401c00555880e45034080c10950801440300d480031000620180104a20340005c01c008096218800548034841e4020b8030146c1c00402c626020f0501d074030400796500c00c03482c000c0d490408081b00c2d0f8420ba10342c0c18107290042100c04440b003680d217819580200c9113249510b00916004404801c0c0e11910030a60140712400184020741100f200c81e0350400340c8082c40b60907182c2004608032030032200d0044066000c038000704 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 899495431 1250 899494181 899494199
    0x3100b07030216060f09051801051c050601060e0a0501020f2e0608010b011106071b06090210090503012018030c0a0e100f0305060609061309050a05060a1401 69
    0x1000e1107100380191801c842003400e00542c09005076025002041c403810200940341c0d848000c1101401040b10701420088170405500e5005d0014020a40600302d0851084a0480303c1e00c2085e0815074014201c580d10f40c0c603140d0060a00c02000c2034103000c0c00e218000450300d0741c00410180c07600b50301c500080011742070001d0122008141a07901e010341c0482c4c3c1b40c60b030b03288880a00503000a440640004603c20105100041806002c010050755540100c2c040c4520941c0c00002c50303900c8801d00024021081b61418041c0003042184802544103013820b0b5080c042c0c0fa0808148012140128001c020035a1403559054009000000300e5001440070082c00e0b02d1040b144451100806016089600f260090404500e500005402c020024140368041149165401d10014050100031181500c401d145031340d0143d880502a100314411841c0c000062903507124141241d480f9090b601d003e0080780d40c10308081e0744580c1842d100750341d0f07801401d0003e40451303414000c0c0c03440342c19203600b21215a803030301001c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 899496681 1250 899495431 899495437
    0xa030b0a0302090f06040b1903351804020403031205090606031f20030f0c0a05090d0204092406091401030209090c03060c040509091606140c0a050d0f020303100b 71
    0x8103611070707540c0046ca610342e00c5801c1904842d807031030103060842504500f402105036078000c0c01c482b2540070001d6030401c1c1c003544400281d03a042d025100281c1b01c1d58400c0c3d02031000260450081d40040c40460004103041c0e00410702c141d40d8280481c20040c0343c64480d850341e2a02011298aa00b540c070582120050340e03421300320010034950124000511020246000425800090251a0910f40801882509c49017901c000d03800012420175585061001070026141d0702400858074451080304042506544807500064001548061051013072002911910aa0004c08010321403a038908400030400b10141e05c10700741c1e08214015620303101da10796400c000407800c0040500009025240d641c01c03242c1c07400c01c240c0d4092548a401e250321542010240002c405004002003800c3d44001d180c1800035206043c1c11090301c5040c0307024081c0b02800300a2200920400eaa100110b201d42c003181c106100700800d01180b401e509030b403010900c11151030201d0781c078002641c541c10a8400d0410400c52880c002000b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 899497931 1250 899496681 899496691
    0x1e0c0b09030703050714090f01080c12010f15060201110f030f0907030609060b01170f1501110a050703020f0a08060708071205100810090c0b070c030c0b0a030b0a0302090f 75
    0x865401a440c3c2e50b85908204281c1c2c01b44407056014010019145000c00344d90390710020386940d1185961400415960703c40711507201070b000d901c21051110210101707400034451040020b00c140540658102240180d00c1c1c24401c1c40015440c0012035035a9115200c201e03401900503402d01800c0d9107541c101c900c000300003e0509003a0707105501c0008002031140c0104285503010b00400951904400005088821404404000360b0350702010001e1098006440350340048080e2812100e02201d000140c51414034a020408035100304071001c020464001503060580303100303039504950880c500d400d100300c140c42030181c207100360021000580410700c101e48140e8008020328025000101d4132043c1c40460380107499129500041b8403081c00040002c22001d070b144150302100b00324600302c1d5120304407002010700032107005803000524031051016041c440e40c00396401c00507003164940e444c2441c480eaa031016210a01280c1890ba84100c1807900e404164100c1e50003904e802170aa45260f803001184900a01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 899499181 1250 899497931 899497933
    0x3040915030b011805060f011b14070801150b0702060d050403180b090301050615094c0f1403060d0602031e160f2003161e0c0b0903 58
    0x100000114030181c241e0380c000c007040100c511074441a44c080c01c3c15078100034483c6000301c446404030340d050f036400f1807208050050f0b40c00d00150030b44a8600008558141081c0400511442c2c1000c0340301401076014005134000280d400b540d1640c1c528074040103000b20040030394010001c0c070055041c070b05d244d0000c80d4000d2080c074100e198208415580c02c0f01e104550410141d001002c10800070381d060034400c0a401620840b1140d0002c25043c4640d9018450048550b004031014801090740c4001d03107002000c0035218100001c025216100c510800321071210b10440302e01a81c2c0081e00140c1e004030f0b118504070459a507403844401e0315201400c180e034005444c10b504061003080f07da02041491029602650741001c200c1060102d002c401d40c4000720182a41501440031103158218581160039006182d243e41859035403804400031007044042e105a090b07400c4e01000842c545030ba124460011565031080ca0320403000c0500b02c9c489a20001c0340d01005103e06410142444452900c401512841030014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 899500431 1250 899499181 899499221
    0xa0f1406010b0a3b130f0203100b0307022a030a03230c0318030307080c01060626010618180f05011a040303031d0109030e13020903030409 61
    0x28101840d100e0240e01240d0b8214020488803166584003006448081003040b81048244451034001e4440034644444202e05004542244132610740b407042c48103410034014100402a4140100d00207540100d450705000312143c540402d0400e0010181c80c09042680c1c000e004074bc440c00741d4103040301d00c00038403a1151034080d0308148259404001042c803030b52003991129801d003440c001403c00c2c2030300d507840503103512014000002210000800c0d0b51400f085540d500402c110740c40046800d511a80f00041e00020000440c88040003054008800b122026594581400d00c8000c4d034540f03a03000320203402c5004a91070b0040205c43c2c4200080c82c103c00c80c41c200c2004080d918150104640c111880150010352510818040280725110b00d074014040702c5040d200b80011000340900c148102e000040c103250760390044c059080611101140400030a5008200c1000141006031a140c400000745100329044564810102c540d4000d43c0e404050140083d8245424505100050080c50030541f41582e002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 899501681 1250 899500431 899500463
    0xd092f090403090b0c07090c0507030c11010903020d060504110603090604021912050c0321120c1b0a0b101a0717040f08010b010905010905010e032a090108010e0a0f 72
    0x4d44d00910f1a02000c400030101c907803610824106880e401c1032440c0c00c2c040c06101580100c3d0300007030f0700d0100c0e5500004194002c00042d00503100d0070500d40010b0b4002400d40800d0040103460340c0601e010303078000c44094814101c40710400400c0d1200b00c4034803201350070100c04240141040f0f4070070b40031100f03030000c000b0790a6120210f484000301c680320291030951140e96540303220306080c0306a40400c03001003c180c02050302c03110b03104028810b00801540c440d00d1007002820718400031042e1030302c2240348401e11170800b8403070b1309595490104070300035a1028414008281a0f614103030070401110b045119145241d18a041c00c00b003580c01400c02514030030300c8180d11309824498040180060495280c184c007280342000fa165007142d201d401d9803410f0041d4100240090303130300310071450b04840c401d107002c0c16010580d2010906011803c1c160311300c02449000303001440d980d9680d940b07402600903142401503a98650301c00c2d0980d5490100c158203030b00541d940d4004100b0440c015100075025131010a488418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 899502931 1250 899501681 899501699
    0x3011202240d020a030b0f03030f03131203060501020d0306150c02010509060309060f1308030a050601031b031a0a03081210120c0e091609200d092f09040309 69
    0x4150380b01c11540002d003103400c99014800da9685c4c0b1820780c2e40704000e810345000702e55a8401c0c020b4140004002000040c50160780b44c0b00000495800284580108501a40940980220300440d8058050055041044c0f40300c1c2c85014110b404151004002098905040d05c0f02440007030160b042000800c0888110740f030342e4004500030608080213100c203103001d85c801c5104401c0500444605c01ca045401070200b030001054a40068120b0b0001540761140380059008103042c1c07400100e44034042d8a0150340c140c040c0c1c090b201701c921080300002544011810410004c401e80801010081e0501c07100b2890500204015444820f41022a004c207448078400d03922885580011904103041c2c0c0c4003444a0076500f1050b0790001448401403040e140e0712152002e1002c164000c0c500040d07511602c4845440a030654859400c0500035255902e607403494a06d4081e101981d0260f42920006c0b40b2145440f000b5200344010303079822146540d540c01a1820094011009807090701004070301ca9012407100380d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 899504181 1250 899502931 899502937
    0x13122303151002030d02121806040302521e030f0602160b04060f0603050d0f022a030c03030f03070c020315150f011d010c05010f060b130b0301120224 66
    0x20306036401d0801fa18102d1441c03260341d2040c0380d0341d400d1600f000c2c05000000b600004c0b815204000b01022040452003070b000c02c62034a4000045460040010416103a40c0c4c603460800081d1003001084034899946600e008403402110b264403202001c0202c2003003001c0362111400140700c501c981405803a080ca510f200c5000d0320020207040e28161101000e000030410988a6080d00c440504400e2007803900e1034540381d45640d083c0000d50207002c41d150207026075074400d00c04401440080245140c3c5158440745c0503040c1496880110300030301c1803042092075032a0000903a24464032042260386141e07510901192040821401203816104280390914861015803046100b0801e10480000b201518800c000c500203000040505003c542500c0107014040c005908403108028207101d50003000d5032411900400f502c0e204000740501d85032002c030381d0708080c80080001c0d510710941349091a40380c40c1401d80c00d01c820b02c50800c1c1c0c00c0800c0070580040c10700150b40c10100410300c0844100b0340c0e20380703c5400b00398 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 899505431 1250 899504181 899504197
    0x110702030a120e0913060203070e10030905060c040b2b050717100e150a03020d0b01051906020a0213090605150a08010b061213122303151002030d02 65
    0x110b0942d007a9580c0c50742c403030901040982d0494101011341415802c4c4070106a08880c003500050700000058002030040e45540103881010b02042080c0e03110510040c001c040c1610126000c1c005d06d4082004000c4040c1683c064a00c028001454000c1d81a41c1e800c280c41100c00544601074a0511003250b01d03914851184204a00c2e1554410590a002205408100101071a074092000039040c040080540c44090b880792101c55650b00d111085000245402d52552000354070000d203611401c00c201d50300480d1030494400b610380d0040316440d0100b00003031030401d02410700168002440c0c2070142c81c00395168200b00d1b44e1110001010183c60300d481d0140c0d1011540d0343c41900c240c020580b11b605150803003c00401240c0000c0100300b141200040c02d1b40b107405103490b4000500400b00f18211715120900c8a2542c1c070800390f08407102080d0b009800b003a980e11000340034450200070603900003030700e1045038030500114101c4a000f0318400200007030541c4130f068040451009011014054043c1d10003042e00c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 899506681 1250 899505431 899505443
    0xa0209040f09080a2706050d05061206062713020117090604030f0915020c010f03150b07080910020a020406150c03032a0306030209090a02011407020f100518061903110702030a 77
    0x8014023010a401d0351800703000140505440c815091038900f01044c540e030004d5048401444070018580d007282159071071500c0c1e000750510181844a0380c4619518041c20034401c0e2502440c010b1500b5400b48908000c644080321500007900007000a0701c21200e04d840e440c1c89003011440c442c0c44060500f10f0000d881100d40140e8028071034a40c4a42e0400c40305c1d920000c8503c0c0600c0000c0501c00d10070b030700c0e001c103101d400315000000c200001002018010f440b9982000381c42c10340141d13001c0800954800030041c00740c1c000c82c600701010401d0500da440b2400000f003107442e42e101484860754110020241c00d00610005968000d0660724500d820016015100c582d0764042100c070b00354010401000000351806065500800d24000140d801c06900c14842e240c02030560f8681c03440f800803407054501c200d80613900019602100c690190403801030300c4c0c4850010450003841c280e060600010b441144003650145190181a0102611035002104c4202038441d92604001c82c40d1b02083c500b01803000d0407118 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 899507931 1250 899506681 899506687
    0xf0a0201050402180705040e0a0603020607150609090c0b03091516110d09030f0c050303030c03150103091509062c0609030702010e04090206120a0209040f09080a270605 74
    0x19482e04071504448940000134030709081c01c01c24005003552045100b801c051040d100c0008a04200ca50702010046402030a0755544411032b107001c058101c02400346040043c60038001050244843c416052940e9001c010f807018103040c61012069a0801019501d0910415040e40644d4181da0000c1d03000701c0003022554440e00414001504250441e95a0030316540030612500205034003145107001c81780c000001c840040741d0303130500049d1840341d40c011a8061200106100014040400843c484c0c801110303c500750b400c1c4000118261299180080c0030006529041d4a039004903a001500c8140b040b940010640382801e043c60a180344000c032840d51480103000d42924035020700020f9840503d130302c00ba41c038281459001030041c1c071b0300e485d107903016035640c10040c000c54503007100301d072170320140151424407074900408034002942c0310a45050081c0d040c45512024120a4059056000d0b48119540c0c1027030b04240027125061030107144440e03800305016201c0d0a202c410505c48000d40100d0703865541d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 899509181 1250 899507931 899507933
    0xf0f09120e09060f090402011e050d0b040b0a0e060415240f08070f0e13060603180201121107080a0309031d13110c15011d06061c020f0a02010504 64
    0x4940038200c0c1c240d502a02d8110104000d607501c0182008540100321804001a01c4034001240c0c40c080d0b0103120304001000150000ca0b413600500a000094101102880415a03003002d000988410220303880c6c0120010a082c0644107280720040d50100e0081c0c00040c0a090b0f17440b58540e00c41160b03012521170400e4001302d85100c0807040c0c4c0085405447e040010006c1d0003800c4c02801106c00510900802c5112800610024415003030713042041070041120b0007610708640f1002c024105485039001091801031031a218407109030030041c01540585856511180c112182006001520162400110200801400164484098008010b00da1b900185908507480c0c050b115880d408441e4101100103070624150b0f613155406003103000920640862002423500780306c4024001d52035032240f00e00800c001a903070081c0c0c4440e001c0c12036262141800800904008080c11a002942c410b9000361b42007040089030a00300110300d444000003c001443c0c181a104160f440c2e40002e03072404010303511002808 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 899510431 1250 899509181 899509187
    0x1615080a1112180d0c08070302161503050f13020f030f0a030c0c1a0d1d1e1209010212250b0405011a2b0803010b030718060903060f0f0912 61
    0x1007050401c0700203050102e0740604c060404902090700400c1c0c00c800140d15010180709000d5a00b03012890f01d005c4000e15110144280e00400d520050b00c0040e2402c0300081c0201202a441401091200c030303800c400102e65020302c51208148003181d50517100301d0031920040e41e010403803001528040d54410b42c00150514241e80388001952003540840300e40b45503450b240100d00125824003400e40000500345045500010b0482801d104181d40f60054200c034803c820358034400d9002403e4880d09842e0881e2058035102035a010700c072410381c0103a0214900f4600700c03c000b40105221302d82850b812420302180740700400d9520002400316690382559050008100c070034004e20b0b081c041141041510024a2404218442050100402d240303101110129549400c104c5807030040760004841070f0750750784407011305280d6441a201c0130700181c244843c1500050400c07001a0030344043c0d03075416094034a035440703001c003610300c0d001c1b0412907541d00c0c1c500317619070306951160220f2030f84584803103075507034800c0b182c06 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 899511681 1250 899510431 899510461
    0x11031b06010f090e03250212030c1513060203100e07030c0912170d0609021b060603060705070b0c09060711240d0e01090c03141615080a1112 62
    0xb0100403820007141c0d46004101109494100c81580b010301c00d00c1c6060070708280c6e00b5110200194100072420102c481c1e42d90040005c280044880c412150072002080382d01c00000e10448203550301e4420100c0040c00580e4070340007941c1100c480d8503a01071050f152051041006410341d2a4000310707136111501849a50410f011000030b01c264011608094450344a4020b030814000340810101c00c002150710707642c08541d0000740030342211202192220b5110300301d035129680b05217080002d4840c00c0c000600380c0c50001031440c490201c2d651400d080c440240e40c7c071402d0b0f00015092229500041c4880544c9440e40c40291403854001c075810b045403400c3c4401c3c48400f400d0358616158414580e900021400d036005c1c2241e80511250700006000d5a214400c1401820403100041c042441120008103202c0c01401c21000c8844075070a0342c540c071040c007004040e0980d02c0d00c185a8004801800c000b41640140841e81d442840c0c82404240f40720544042c15250307020020189089030240300b0f0040b8421100a1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 899512931 1250 899511681 899511689
    0xc0c180c080c0d0914010903050d05010b0324040b1f0e090106050a0e19170c03031312020a17070602010b030a08040e0a060e040b01030605070c0c050111031b06010f 72
    0x244000c2c2440200303002684a514003005074030303880700c07000400c00c40103440f001c082021400081105499918008201d9030061134840200b174280b00012645011000c00c481c06000070010850380b80d0382c0351a2520541401d6040c0c154016510035401e0402d4440c00d18009442a0452034215400002c680242420600b010010b000300b201c040184141d0340c0100450701c2040080c1014641211210000761660000f1170450040600e1008006003001c4211f1403c41072100c02c0f000e6450501c0381c1d500740b69580c0035294800882c3e0701490010400d03000c41c03060103808140003600d485c1d0455110120a1500c1d000c4840c1d2075500c0d80103c0c4104089a4203201d540e070340d018100c011b04900106511000c9280c0514001c0c10311140039140483d0035000079030311110080000c042a440700349460305028074141c4007403005840d038500b05070010f46054416501100305e0780d4000c20b14142241000d004540040726680010407502c01080300444a101c1c10b9100c02c40c0c070f02c132400104040d6042444840c00c0d14100c1c0c2c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 899514181 1250 899512931 899512937
    0x1207030e070305031c0b0d06290a05060903010e15010611060c0a0f0903050109030504060e09041203050a0e030721090e0f1302090709030b160e0603070c0c180c 70
    0x40c140b0014001104941d0080c0b005501d40900186100c0780b02c004080c52074405a0291a0743c00711810485550000510301001141000f2102240345512001002c0d00381102e92004190303800f03000034580720001c0c2800c603401400001d21150610222803402030410302118448172400d004004003a4024900c0b010034840c40040c00c858140014400100d0280e0307102c2d40b0030b20401083c41c0981901c142c4006d001990000d009200e0f01105081c050300aa0242c054040058a0394000c04030600f041c02c803d0380601e5000017088503410201c1002ca00a100162000180c940c5031040700d2071404080001d004242c0c01950100d1055041d0303184154000c00c0903140b08240581c1c4c440070000314034180f16103640800102c072804025541c0c1a9400d0b00c00905100080d0b00c04951814480f0150f8840038040c1030301d11031800300949071a90348134469a41c03110f41d1240c00188103100030401c00d00f00340c4050740d080340203070034101705140403540c623900d0b03052007504803116108403040081038110352030064a8480341c00d41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 899515431 1250 899514181 899514193
    0xf1504020702090a0c0314070503160908030711030309150c0601150507120c0606080c040501060207050d08070c030212030319020403020d0f0c0305030307091d010521030409021207030e 81
    0x29003c503404450050114215039501c0700300c008401d010345c01580042a0f00801034081d46445580a041c2d60001d9501080c09801c40c80d0f100161402030541c0c00c00c0d10312003001507082c1106552440c141e00100600b01e40c25000900140e020703510344800c4071692040344141a0348642614101c5e45c034080c0d059002d1041030305d109902c03045103600682200c0703103560800d604e6405901200c0d015078008030481401096240b034448009441240495541c003403c00c00c40b02400305036682e10089035230b8007180c040c0c160b11007003c03082e001c005401030000703005d0240b0070a08060304540e2a00013810910700200142d4503a04008104103810084200000400782540c3c0110306160850300800e204400c80c81004016543d000380b0300b02030082c0d0021030001182e200048075034070714040d06c1c010408003191041c40c03124282c0d444c0c45480c1c03103615140075040c1c8001501840f400020800b0f00f540c0a011f01d80050b00c54001044081010301a90000340320115110700f4490355801c0010000301180c02070341d0b4a13030080c3c00c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 899516681 1250 899515431 899515433
    0x4080c0f0d0f0e031605121f0203010806133504120b1806070f11101d0a1101031d01061203080f0411010f05090a12030305280218090f15040207 63
    0x41e11131703030061319816a840600d6a080ca48118a0708a440c2c004408901c1c11103400600da015940085040c0c40c4c580c425a025500c07000e81000019910a200038100c110f0b80004403603018440d440c0d0703030540175600c5016508000001c07500040d03a000303412401f1512100c030500c8bc01e21903900711168004400022051004c0130b10580c00c1d40b1501c0140c5050104011031007035081c400d00c50079482441c0c0312a4000d6640450440c14118014400c1c00b9241c401d10341c812031003034404203001c40c3e130095040c1c01510a031803408114004400400c489440c1c018040c0e004268800749070800d110300300180c00307801c140c44048040c50601030050f010042000e908461070000f040001079032500c43c031848404c01c4c20320302100a0034200c02d503010300500c4140b40d00035005e010002004e0144001840800d4001c1e00c080145440304400300d01d0609907109400004030070380110401c403043c2640100301d039110700b075480304420f40c900b03000030172800781a00c1c0103a801300200c0500005604420143c0481442101d0031440c03c03141e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 899517931 1250 899516681 899516713
    0x901150f0b0a0302040918030e04090809100903241104150f091d04060f02090a0e0405070b0a02010c1206050a0302010c0c0806040813090c0804080c0f0d0f0e03 70
    0x890701800840c400040351000b0140d0082c1c044e50003a0038101420300004000c48890100503071161019130005020104165650506200d01400c6c07503005a0081d00d8209210180101c0800c10340760f0204004003120b00001060b502c07030026000c41c4809a0004442400380c2d050815180640c40c1c1a070207180420040050100076140d034000003800342011010032440a9041c4d40c04034a6078040640898540110401405a202d12511540c450b450400c40524418401004c80c0030300c071141504981820f809001c00050b0076665a4000d12950480301c0040c0c40c0d07445000c40da084484141c004d40c0d11103101510342d070340142d144000d102040b42d042003410b20385000200d61240c240700107414450110509010b10082d000508081c0003888200d030214141803a184c40d4540c4100c90f1034401c4103c02c4c07000300e810403041c002c82c4640d000e140e40351400d589031a00c5d40e000513400421640b9051003031500348458100c044c0810a0320381200e0701c80034226240da10300a0302e24401001802d220740c00482480749030b100d17 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 899519181 1250 899517931 899517959
    0x3021c05030414010f0c030609150302060913090c0f0e06090403082d09061f03020603280c0203031609050d080702240910170c030a180b090115 63
    0x1070000c1081003025000c541290040440724042c650761030404800250701b5805030028022150742c01c070101325524806140344695492070000a501c0001000303107240c145040c0b000c070940408012000124401c0c01d40c0ca10400390b18039400780a0f6180b0782e01c42001305c9403070b698140b6480380d02501c04010524196400412208008001341301c2071410300d205034140340c09428030620351040000300c180141031032034100c1c3e17070303640e0845400c2050f0200403202d81e161541c1c401c8803801c0760342c0030b0b200c14196212010744502c40300180c041c0100b0f200c2580204120f50f03c150041c06000102600519541d080c5401003407043c000d1070b6905414480d059004102c0f984824505000140e0445591030f2510038a10009200850300d003452000400c1119040c50070054150042c241400110f41c8511181c020729020341e03001103500b580390300c0c0e12003150001c0c1d0062a440000c580c400d601100025500d40007003e091469503200b00305503414808141000a102c40c248110348a8005040e4a1104c0ca4607040807803100003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 899520431 1250 899519181 899519183
    0x15031e0f06101805030f2d07090902040e1f0b061303022103040806060301141303030e0f19050c0a050901060c0c09090f0b07030510030b0405030702100c03021c050304 73
    0x42040086a1201c100d44408034004d0200141612403946200340784039a90040700340d410145030f20320314060b10024000340800c01d03102600300c054401d01380351451207002040c012400b0398002c1e440c1c3c1c079102140041801800c6007021800d200041c0180c03036994010441c1d0102c05c46a00943c0100301e031244900524652108896040345ca030560000000300498a84182c10208156031202241c04245004041980f92080b00150f008002080c3d81c0d64a98400700802e450031054251007041400c0407920035001440c2c1450710b4030488041200c155a501d26161480c1c1700e0607210340760101420100582800b004940c038a049403020241e5042030002200349606103c1c103010b12515a49034410011040c0742c1c0c50003050304a00410160445082a1541c02c100316030440700c000110780000d4003503000c0c1c40707580d010f00e0030340703134590117040c00d5507141c000e00c960252098416110030701030280141c0e03c9010250400d81c0d584d4030032494848614000e40ba285501141c14610750b2100d1541e2005030b84203042e20340c09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 899521681 1250 899520431 899520437
    0x31003060b120303090a05121804020a140f0405012607260c0406031d210706050c04080d0806090a0902040b18010f080c1e15031e0f0610 60
    0x1d01c06400c0054028503950400105601000c0f04000c6280f0012460b10182030190050303034900c030021080071060380300b81d6800100c000300a06408209050580c040d20554141c1e042c0280141c1c0030b41c000c5465a0843c5800400401000800f842956400f42440c1c03c4418030f03c0b80148040e00c203d03000029010002d25000c20400c080110341f640c408108924000e01405058407401d40c1400c4c40a2141076200780600d2020a0524804504113940c0c504550780952495014084225500302070b00d83e540801c0c510b80a040000f44801000300711980306050241c40d40056840e40c0394600005181484130800c1c101007030041000400420782c07621300045a002d4450321000600110078030001d80100000f440c41600007502d052804000890003460905135403001c41c101901603664035041d9900d41d0044c2d01190003000c0c0c07018100782d50105a000d12411400140f803004003a501142000c0140c10031110b02010702000322420041075452000b20740c104030a01030012032454401e0100c0d5040225004190070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 899522931 1250 899521681 899521691
    0x2071e0302040504020612010e15060a140d20030115090b04051908010c08040c05030f0a0807032007030b060103020304030c020d060f0903050903060c070201170901090c0e190203100306 81
    0x215564202141c48101a02c822124156102e00000727051381c02c00c58416109a403215132a40c0b607031030441c041d9885807103969a6a0b0f890031f0b446007541c3c2c6940180d84a41e02907526984c01c0c074400300c80742c0f1000007680584000b0949a40c9041040300c0e120180152110500444000600051f1010811101070741c0042c1c498000b10201c4003901003c1c0c2c042584101c2c01940790012090300b25900c0044940145c1c050116000c80380d496100b00f50315002046112407460f0300407810140040c42c1ca40141440324001c0c100340c540700c4072054401c00380c440090680c80950700016024010021f0300a406500703d00280fa0442c21460240d40140008101c440064071511101c0701030400c21803160009500e10745165401d00c00c565075441c02909542148100034801d00681c03000514418000c000c0c0d078006034059442a840142e2000451038041e400340c05000349548078168200400e40c8020700700e00401d00c000c0924a00c0c9000c0c481e07010074511554000040303d0042080c00510000c150031002941c2d040078002039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 899524181 1250 899522931 899522933
    0xc0a0f0b030739030305150303041a071e060c080609040f0c0305030f131a0a0804110904140c0f0f01030f150b090306090a1e050307051c02071e0302040504 68
    0x264014560808010400007a8441102280c4125511031051090b20203002c59147c6981911030802680c2400d80c15a0040c0020012600c09400d040b0b0070b9980c404080346456415110304001e1408a0079410300c0c0c200b4140e122080098074070a4000724680d0f8941180f16081a400203294044090406003d05000320b10078010300c199000c0303c40083d40e00804591380d038048500d504103680c10a44100700d00c2e41001400082110840b0400002c180d1040c0d1240d1405e54881e03800e42c0d40100180054880c0584000d07031003400d4540344a820700441c007a05c864030310782e00000c003428909801000b0300c1d4014050f0040c00ca03c5900d8151242103040c0c400d01300440c044100f449420001d00340c000030b10804000c0e401c0d00042c204010f0f00140300c8640706806580b595a01e000c105686d450045600400000503d044074900210903881544007034400c5050b01e1409900b80c40c0c8ec0c1c40c110307182241c2000d1004200c05600b0460701041840001c0c6a01024592000d5070040c0e4580b0701c411500c00a4052521000090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 899525431 1250 899524181 899524217
    0x200d0f050304031205090c040e0105010b0d051801051906170619290307080307200103021611040b120a26040f1a0309031b0319020c0a0f0b0307 63
    0x42c1e04285004c508201c540b412140190362080100980c0d40114a030010802002606004540c10b81d0060303002149008942c010b1200205001000886045204080c507003081a0070b004035400342e80300c1c1c2c0e050f20545205081180c200d56641d8014100260303900354403480604040340d002da0120340c0c40030310012a405040ca6401410a16002001c0701180003070549045481c04400c4404440c00d8080391105500c0d03243d241e03564031070004c020f03007048500600b210f46000c0c01c0c2032407215500180340150604107620000d45000c00500e20071075800e0644882441a82807602c02c0a1b208541110309452441509100310303140c102ca000c0107807040b40ea48000c1d19018614035060850f00c00c00c6040951f440b59107007010444100c0c14050f580380703040e2581810303d03190781000541c1d00030030031507018519040c4a0b01420203043c2c000c0c0e100f030b401d80c00180701e00c1009260200c49003030418040d0b0060301001d0901010000050071540120040c001101801c2c48210001c9095a42c000d5007410041802031040204c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 899526681 1250 899525431 899525447
    0x10c030c0c080f0f060703060e0c0a2a0203010507092d050627010903120e0103061806080f0604031719020304150c0c081c02040510200d0f05030403 65
    0x101ca16101c0c40d0f40034030000c2000102c43c26260910f805071180358a906800b2016a00c451203208144800b14011a07411848080144070f9440c55003059031019040b2000608082d0703034128030210740185000b0304030070341c2028090f00303600014030b281041c14141048149101407200c1580407204402441885002c8c40c4080f8044001e401c000340300301d48031a0442c286843c0290480222408507000e801c1c101c07055400f481a24081c2c1e035009602504103030445c0b1003124000210700c50300d410941c1314600003419882c6500504444800032802044181c10300600a03d441c040e41d07d5803010f544000204008a0340c03014000d445840203150b108000c0e1a414000101d251480b81c0303054079a4800814801005401c60b076080349014214001d1044014a0704140c4129a48040280001c9000c110782c80451b003401d020b503060825071100060034180c540022460b542105450003001c00c44407043c0104038020003280c6c0c0310001d0042c00822401d00c4401c80101000c41002c0c480f800e01c000400445c003094000d15070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 899527931 1250 899526681 899526689
    0x10c080c04270905011d1b0d150501032105041a09030304150e010305071803030f02100906090308010b0301140402031e0901091b081518061302090c0702010c030c0c 72
    0x105222085035414500c1c0241404490408520b41d003411b61500741c0c00129002a6068410581c01a60300840c4140540131500100445a80f640c07480c080d40c04601074881d090186020b003503c500601502d80c0d102c1d0b203007030810b184001482000e0204100c0f0385100b03043c12001a400c180c6003912580b007030011030728500980c1c200609008170030410049543c2d110043d41c0b40044240c1c1c3c28403503034440fa81d098070f091002e08400d44000c0e64880b810300229020b007500020351040e030310464501462030312014041b80e00c1c81204440c2c03580c0b1090600c0074198030500f80d80c017410b07441080500c0c5503d4085071402c1041503050003809940c011000074407a4007038036181200a02e14641009940c603003080c1150080c44001401c440d550a002030f130760780f080c810041318000c0c0c030311800c000c01101c40300e080712400f2900002c000044001c1c8118006510345014030000d4000d020302d08401445602d80d2042200f4a01d0050607180321300b00a001701e034003503a80800ca02c034040d42c0604081484080c103041c001c0074200c580d08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 899529181 1250 899527931 899528009
    0x6091e030409091e080d0c030209061602030f0316060b09060d0f0813090516180e041110110105090a02090c031f1511070e0415020d0609060602010c080c04 68
    0x140d00340c05d000c100e500400c40034601000c02c00031f10160032025000c0340121100117400c0039013440380c1c100303400300300b191500d15500042c01c0700d10b030001e030302c100c0c03441c56004e07600844116000b43d02d52410008a030144494588084407680b80b54034003140454400300041b000542100c81081410080c450060f084840c4031119a0400c00c9142d00c1c0e202e200094039041d20242c0311004081c2c90a00000e101d1240c1c0f54a10322103000007580c003450101d502101d014050402c1d06c44a40c0c1c0d1101d10f100d075484030345400000c0c849071138120101e44010709050031920011308151254002550010060766141b134600e90061266405544035140c1c81c806050b0030319901c0c0f03030402032181e0110126002007828444060b01e00b10f66200080900711200b460f8036241140704840f4009203550214002450040060300415a0300b8801828400001074a4050b03075401ea00900009598800a00c4418ac1c28006c00003031030340703d0a05d10564244a01603452a1007207104900e20300000e00c22001c032030105809080c0514007510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 899530431 1250 899529181 899529233
    0x601051c1b0e151e040b072613060f02031c020306130608102415080711060a0c020109060e01020a27050108070c0b0906091e03040909 59
    0x104103962001d240da00011030403040741607005142003518501d000314202040f84c1000e0100c0c04403000c1e0042802410303e0f880007404041403032490300001d0030005001e03540595a40d003500c01d2299aa10b1031031441010103204101030b07040341015240d100201c1711140b07800102602510800c90450240c2c5103900e05062504401d500c6261190700554080c260440f041107004200100c95412150700c1e02c00c5440782d8020003040c00c00680c5990040301c44581a442e0100c04801283c0d43c420b00e207026403c04030031380c11030044004016600064850740b103181c9017400550140c00c140f41d581d40b0b400c0106580401a25800003d05162003134102c1000d20303901c940203100040c1c005d40181d000c0c3d0001c0e03808000252801c140310021070500240f2100000d00078a20503c0385003041e004440840d401880101480505100d1f400060440d000c4c443c85140740f4170203000c1e42c3c10800000c0b0b043c1416402000150511344d440d000e01e01c0c03004021101250b000f5140055103060030f143c9008000486090010303214104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 899531681 1250 899530431 899530451
    0xc0818030312150105042603040518040c120f140f07080304170145031e08280e0102040b071502030412031d030316091d0601051c 57
    0x104011a005a5150f802140880c03003400045480d80190311441c001d101840342c81e20b45980c003244820f001900342c032007940d18050f2284040794070300c00700d15000341c840030705e0744100b0051255524407080500401d24143d0110540c81c0c680b11a50b04a0103006407040b61240110183c01c0b0b0100310a0104280070810741d01816583c00d280c1da1250030911440c40c400e04901440150750406110780070b42005005108410122460400314a5508000c0e801074440140310030030310508103a292074025030f0f10a6903440f40c07084500d5000003c000c034070300f580703014044541d06100c25407900b81c0070a44c9510440e02d80c0b031740300c02c01e0f88070300d80140080090400c0c0c554400103010030000540401020818090511380c2d00c1c9840c00c2084404a1000701e40151280600320a801c02052080c0c00440004c0c45a19642d580c0300f94038280f883c19948156407542d5007591540514407041c2c5c00034103480081804000c403501c04081500c10701c0c0107040c01056141040301c00514201d0300350201c100c2d5520503259100c100901a0a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 899532931 1250 899531681 899531707
    0x40605070210052406120f150604090209010f090311010f3509060405060f0402130c030c140304020a05042f040513050615092409180103030c08180303 66
    0x400362070f10401d01013a080030352824228100c48414812601408980d900c1d0380072642d0242001d8600d040c0400c00d20442002940c87ca0068070103040c180c20010703641e1a100d8000751a005001d000d0100b8000880c20403c040f80e48172504175010202800d0030b84c000c988000e01140c0c03070601446d00214122200f681000000080c48010780111032a0408103d540c69510807142d60320411036004042d1f5200d0720000d2114807012240681141c130203061481240c01f11008402600d0302d41c1003510000b5610103114100380d40c851040003011504818062860810b600031a03145c1f01c060003064000c5496135150500d5025002c170150503001107000900704000c02c4251025207500c9032003164402c45c0108604244c0c100c4522074140a03100050503005461102c04014443d0342100c03505a5000508036088000c00006258500b0352000d0085090b0b0354403100c00400159541c540400034501c440e4500502c0003d4000c1c4040c0d81c400d0700240c030f081d10b910822040c40c5c90790300a80300186c2c040c000800da4100700b0403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 899534181 1250 899532931 899532961
    0xd050901090c0608151c050102180306010504020a050904020a09120302010509100c080f0705130b2104020102060f041e05010504230c0103021308032701030b010804060507021005 78
    0x440b8a0000071156680e00c412600303501c00760f4400c05450800744d907030541c40c5072120303501d04081c108011070083c0b0784072900c4860072038120a280081481400c48074623030700d01d0b003407161030701405040380d003103040c10180000100b4900541c94a54002c0d0342c001440751500340500450700082005c0c40006080200a00d0001d0181005466480c1e0a100d00b14551030041502d0088544104595039422104d540713042008988140252000701804000c01604000c00200b04854020706140400305603902121b400902100b203c0c5070628142d940000e047c080180c1c0e000c11031580260000841c40070a4590f030900c00034400c3c0c1380340c1c203190007034001768040c1c100070b41074100c01c0c0708030300407958143c15466848003042c0000c00c00066003166085589007014540c003a81c054a0211500d1b607201c61620740320300c1c04515590102e03203421103c180b01c0c2184508a0074095070361b45400d0080c42d013401070350040e40c0080c06111003d08024a17140d1100700140c001e074420884a01c03014960b02052002d41080c03150082686 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 899535431 1250 899534181 899534183
    0xc0b0d05060a140105180306012706060207180608010903030b1809060615070b010f0e0a0b03030a050c0307050d0815041b180e0c03070f030924020d05090109 69
    0x20303003010009000352a010550800310f51010605444455111004442550005083c1010195070194840464400b04003242c00390216000d508807101800042203103c03800c040b0010001418600180415940440c0e030030300b2a40074640c5210202404080d03000a41115000301c040c03036203001403d20506602d6004101040d4003601c1413510269070104800404800710f6042c55035921460114805040c04c1e04580d000d826074003110340c1000c0031580c9040102d0b0342a4428101a5058403050100c24000507103250040d840d41070410010078040c000c41d4480c0034074250b00b4180500418031202081c000e00444040941c4142911050008502c000c0c11040090b20440072854062407407000034246441113150604401d1051680555030305011a044501c05902d2420f440c580e00000a0408500a9003401858070a0049460b46010311004104100285191742098207080d0800049200300d00c60941030314000040e1110501c00c1910740000e48100c10158000c54605010084590010351207160301c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 899536681 1250 899535431 899535457
    0x10c05100b010e120606090a020903030f0705120a1d120f070612060302010e060d0605090403020f060a09021c030516050a1208010b040b07030c0807150627020906070c0b 74
    0x20404042884809a8a03c44e040340a030f01c2200841c603035180402c04607901414205001d0720781a175000201f070650300700c0840c030b002880e40403500b04204441400789050704d4000b01e40083c14000c00c04e10060059000307801000700036003111214806a100c44021640741c6400e5002c990f1450078140c1c220f0341d120010312414001840c0c44561640880d018007550089236016909c81e5085050f080401032294014224102e000e03596103030014136038803008611441940a41c001c0c204403008041031a0500d400103001e045041d00d802402001039440d400c180c0c0710007540041c0c211188105213410350b003a01c00c0a8134617422039590302141c010020005101c0202034070178a0103d84400d684401524401004c0c02a031241c00814003080c04071180b00c1000d04000b500034540368180504503114410703030f940076540550300b0095a0140007203c0f0180d000700c800030300000203020001803d002e54046108109901c0840c2c454000481d004c0030f5860909a540e00d41d00410740d441d40668803104100305a0005102e10382d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 899537931 1250 899536681 899536697
    0x14030d0f090e06190e0114030601030c0b090111070f030501150b03040206160f21170c0a020708060a0501060807050310030201050306040213030b07020f120d0b010c05100b01 76
    0x2410312034600644590500d446480800d4146191008490750080200d41c1080c541a0b8011100e410810007000074015000c0003141541000c60f4925450160340ba80382c082d0340b080c001040080c203103040c10803c90f441ca4402c20303103c0042e20b0040b1100e401c21a14246644200d20010847c02060100402181d104034001c01000c80c1c0d40e000203250500d540306040f903412041c030000c1c000d414903400505641c01c03101d45514207800d082c2c1d03aa00790000c09401c142ea6070340c480d00c1001680c0130702d8420483e103ca8141441100380c0503001d00d902052000500b20304807240041032000c0720700c0c0200f10f20006020400240c4000d0713b007074504040240024842c0400080070100442e803418080c1040b203000e11000840950b800d0300f142c0040d6250382c1b01030700a9400682c02c00c4840040c1c0c0980d142c40e0043d5100742701d600c100d8204520000e1600b0725240210300355402c110440041c500344134045840300507084101040c00206880180c866a000c0c0c076000d8103c0c02030340503100141c0519484108625400d0322000c0e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 899539181 1250 899537931 899537953
    0x318020a060f020c040605102f010603110d0507091802031c0f080c04060c03050408100b190b03040f0302120c070302030d0816080c090a030c0e0711060f150405011403 73
    0x21b441462064075000611140813928680c4500164100c4016108155030088420b1030504921000400c100da4a80d545a030f040c82000b41181540d51010030444444030300c856280c843d01d40340c1001d480342c42105a52401043c0d07002c03c04030601488941c00030107954454403c2b000d81900d4145096a00c00002d03100f10002200c50b0180101c18010b508140100f8100303814040291507180d144481a014008184000607a0010400201a5010700d0142c04200d4a03822000d00c54102c4800d0302101c0030003040d00c424040c0c000c460041c1d90348070760040b0010044d000303641410b0b81001784032403001520050000d060b564030600094140100c80c400c5d801c40d02078000c0001c04580c0d61000303603500c0040c15043e42040899078440e0140e6a04113160100d61440c01c0080800218207816039442101c013420480c1040090b442d413071100d5948810b5508094034031a512000a50712140c00601c49202103008030b0220300b5881010646091030407004d07008100950310b82940098104458000c039100e4401e11070241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 899540431 1250 899539181 899539189
    0xc02150a050406030b0307090e0c0a090b011b0204140c1905030f0c0723010c03060806040f02010f0e06030408190e010530070305071101060e070318020a060f020c 71
    0x2410040d035603031000c1c1030606000e81180941009003006078540314070180450140042d200d000c1d2064a20002020300703015035400d00903540b0050740028122490820825401e9030880e21001d966007219022076101ea03076500c0011700420341c1ea80d0f4071103038404a03010003121218500042c40c3c2c0e9041c00c5081c910381054403504a402e071008850101e11002c104010404401852029100c00e1344542c40c03042c04031080c00c908000c016841420800669188c5441e00390154052207150094504840600f4a51078140c0710316002c201070100c003d040104030720050380060f1082c2440c00911074003c1c03240b90341e4100380c10201c8154001e40d0300041c0c07002c2400c0c0220940d82c00740b045088841d038182c42d0307070f8207200d4440c9521100c8410f034841680e4000b0395425282c00c4000c418045442a51144c0340002c607400c0210380100030b521a0f2000344100e0385001814805441c4c407001259120080d840d0100b0300120111100500400b0500000e400c115148400b25106422000203040b84019030700716860405440100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 899541681 1250 899540431 899540437
    0x110109020102030a1b0b07051306080408040501210510091b170924010f0e130b06011b0302070302030105131509110d14100c0806042007030c0215 64
    0x2805680104134414a05014581c202c0000803000e2800a84500d1078560308136000003251508000344000070f00044181e1840488006400649450000d529040e80c86684078441d901526040c8014400c044064001c21310420800010141c018030943c180305510380c80001807401440981d50425084100717103c80f1501c50b1407132541e940d50782d230568036205c41440312100c0041c0821480b0b00400302180100c1080b180d02000c141c419100840c2a5131601c51001c1c0c4c0b00255401c900f03e0711400d407044c0230500140e540c000b94007540004a2000e0342c3c4800d40142d40c0760b085030041044800701d415192092680105213002264000d6000388010b5591f00003404e040d44070f1701c80080c2000a520050031881030182d212040c114400c1070000108610207000680ba4a2026400c44902021f00020030320a0010b0001c140102e078a0f00301407022300281c00003c1c00d40480103100ca402903560349040030710343d0800007c0c0c0c1c40d03690600800c0b680d100c219003002401c101c2c82641c168002c1d04d02c42c240c1440c1d50900303c21 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 899542931 1250 899541681 899541683
    0xa0c0501140a1e1412010e09010c0206070305070c0b0a050a1116110409140a0317160f230c07080a0803011a1e0c010b090709182307110109 61
    0x80e8825018010751500031218a403141c2c0010413a0740c2801114507225000104628403210901c1500c0307614010b00d591b00f200c4010030f4005203904185115000035000100e6a802a145050128150b690424100c030030100d400c80c09440e20354480d0600c0030b503056030303031240e401566180010301c45c012520301c0a0901d480f0f0310540e5000c00f01c0b440000700c0420180c1060019512008002003024220f039254a84181140c60070700801e5045089140b08064100311742e00c25905030b0f414030740180d190414030020001d148034484002c0c4010080d800042074425040b1244d8000c00c5086040340c000c24007032944240d000040c4100040c85000c2d03020440030300c00074a54031840d510100c00340c6981c0c00d1070108040050000420460540c060114001c00c01060a0b0b40414180c03004d8040d031520103406119080d10340d1042d5060050b0f80c418180100c0c6540030724804156605080c0c03040a0101440301d4000801c0c2d840640d80a242c10402408140d00284028501641003991424010322030840e5032400c842035140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 899544181 1250 899542931 899542937
    0x5160305031c0b04020c0f0d020c010905150c010f15080a0803040311032709071106010e060d02120c0114040b0a08060a09050403030c1b030503060607060e0a0c0501140a 74
    0x4000e141c200b11000d00c501208a00110114041c840600490140e8000c0b01c407000060f007001d002c10056103000c001c25100801c0b544020f083c009611000641200d1542c01031030700400e491a448105004030700d0403501041ca8050003080440c2598078514000c00f0036415086200041b85070000d000200043d124000c96080360882e4516100c80e6000e840652540b034046003540401c2c80b0380011404c00360f8441c588210f036041d51084112030b103010000e54280040000d024042e1105942001c07600024040341900c802d0071900e205925a00005105889105002503000c000d11096084140c00400d044244030300030b803184241140030210710044c80c01180034403141c1c00c90500c42142e078948503500241c0c11600c050070300e0100d29121401d01c1d060701c03011a401c1d400f00f0388540b154840640c4c8004200c2c2031081c40340c202500c1c2c280664009100e0f2001810036881181c011980308180201a440204540000011901000c000c2d29141d800c101040c41003c0c00700e12500442c91081d0300000460f2510883d6035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 899545431 1250 899544181 899544187
    0x6070e010815030109080310030302011d0c010e030712060b040f110a0f050d0c021b030304050a050d0212032b091109070207150c050f010204030f030503150a060c0516030503 76
    0x250042c080c10401e1403654199210712282e00031a40b140001e5006407040e200c0480840c0c11424040c0c25600b80315a107100c101046403050130000d2000c990a210b1010918040e071612410000081c42c041040e00441c076900c502d0040380081000b2507001d04030115064800307008031000a02880c04503031240010100200f01004968800c500c605c0000103850b5160030420b0501040102c030300202c038158100700d00540c1c00502d0a001d50485294414400c0b40c080700154078140c245804640c2100d40352040c0341c06002c80454910840d80d50b000c005100d07140540c05c5030380359030340380724803003200d80c9481c0040c000c0c1480c201d551540f030b07c01e90061a0400d40c12140d10182d0b202420240a0044070040c0301c01c4c214021000c01103100c41000104c50719400d055a1082707007104550800b941000c41103508400c15a02c104800c000041b007035041d8801450b0103090058032607a0790b102c00f078180707144035074095070040b500d510111f03081d9000f40c40d80040500800890340400c43e1104001000c2483c0e010242c501d9100b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 899546681 1250 899545431 899545441
    0xc1201080105101a040e0403030207032010020d0b0319020901060801030809131e0501060e0105072a090e03071e0c210b090c01032414040b030303040c0806070e0108 72
    0x10480f02c91004e00c4030345124506540e8840800313440c00c0685084000a4000860805055218540050000c244440c0360405079482c01c0c82c690b100d603810703a215406034020690b4032213040300d07a0042e80303011000b4080e1108206a40840510001818402c9100d04884800428140d10075000c1d5416243e2162441e454910106c0400c550f00c2400c032603e0704140c1d11101d01c0319070258966901e01c50189810780c0031925504000016016031400d4000604112080c840c44000c1102e030b00804425664180007400c0e500001d62500004800580114000e0b070300300a45400ca01c070001000f001001d02030038a040f09510b1a40410b038a0a22401c409002d080481405114410907000144100e00590700e040a600c1ea4a96982004e4002241c0e220520b03084465100b0842d6014041e0070000008620700d204411a013040078249421980034010064009020304589030b1110350094030348100081c100e035101d00d01450108880159400b88000030b015960105080d0b0740502e079080c040110584a00c11030355a6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 899547931 1250 899546681 899546699
    0x803160f02030a08040f02130f0f0903080f0621060f0c0414310b03150103031709070b040909051b0303090603060a090c110d0f0504030b04031103030c120108010510 72
    0x80c01c06e4071480020503020380160790303441c58017022414181c4042000a031110b0b42e60210382d14031001c00101c60800c1c085000282e0302000c0e6036032083c16000c054095480d0303400450004414008000610501490788810200d8001045481511000c040310b2141d51101c84440d16401240f04158516210010003019403410b1821a844803107003402041001ca6101000c2008a082c00c0b0b400c40c1c001c0c1e85010003496400c0a03c10703016080c400509840f0254591340d4010840e01001c20400e03120010700000c110068020b1000710018209840c6031621180c03214459801041000001c44441c81154510085400541c088500c0c640c00107010b181000101d1041c82580c0e8402408aa8002500130000c520600c048c4a90000601259981d88480c00e0494402e403a01c0c1d2070782140828000c025505400720395000c000ca5055950010912299846526081d03d800c164040038a2440c0008401c112244010310040c000c4031800c0c111707032519641d890203000c2c200c6409a034582200040f0007030038400019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 899549181 1250 899547931 899547947
    0x31b03090d110d02040c120b121f1b0906260109090203070b0703050a1713060b13050f09160807030305072409020a05030c100f1b0803160f02030a 64
    0x18001402c049110f500041c12980510b41c8500440c1c1c0041100728070b81d219205082230400706454584660605680150b55000d490400d4846804c2010184000c40020b400482024000c162110404c418400c2c02601400890192000284843c5000c0d6105c00181a52604104040c4030b8020140d00381205400500421082a070f0548565000091400f941c1d42c0201340c558003940d9400c2d100d20065000a01203011401d5254800c064003080c40361054002c0a0078129a5020f980000d84134100ca000c1400ca140505000d02441e1515042140030080800340601c5000d0440c25154540642c01c405e40c00c00005000741c200a034421031040c0002030264005110050240621400700c01c400200c0c204d0540105106c1a803050700c40902108508110002d20060032045010b482d0380288000801ca0340440e44a0034030421840080c03801d8490701440c4404030111100d0300e06c81140d40d00e030400c6105680103954001c9407440b02003c01c07040c28410844400000c2c0581e01643c40d11909560843c2d40c52 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 899550431 1250 899549181 899549213
    0x3140a020a0e0a0501082806091a0912131208040803130503010b01091503050a23150103050105030706051c1e0501050f01120504050307050f031b03090d 67
    0x44101261200566580e0402100408000240038410300d0003080d5601912010307406450694402c203860300c031869800007100b01e180a15010031086c0000c42c00e004014269005003d07020108011400c2400700407289200e125090060848294108260031b002a0788075605280981410702001070260654444040361698020040e560405c0c4c0c544400070b0550340310201701c000c2c3d800c01a4080010341400e004400c400b8009081c2030085c2403405005014031541c0d090380008041c3e640c00052100c1081d58442c8410034168001c0d0034440d4220006d01a11180c261800c10101d51100d44009856100340212810b0b00c5010340a014960704c0c214060301c15030030a614440c3c0006024201c0d96010b030041c4100c0c440c032074030f000006a04000a86080c01201d1041e008240a84020488103585d03036000600c0080d41544160000703030b103a540d824868118066858014214080ca03401c1d402507075000070152481d10342c851080b9840d500500c400039564821107441641101020641c0c101141441124060f18 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 899551681 1250 899550431 899550433
    0xb1305090402031612030e0406031a07021e0102120a0c2c190e07031b0e04060e0c040e090a0f0204090519061b08060a0e0c0f031005040e0303100314 65
    0x145842c4520724034071303282074000701c001a441c06240c10515601145044010b02c0c140c070708001460035522064020100ca582c00703606681c03034402144081d0f10820085054066001d010300c0d045049008540c0030b980501c074038035130070007094012800e00035031303441911400200340d29208050b5002d141824152096682003048404204000c50700e9600e17034400145424212140d0040c8160900703801484c02c84c4003501c4081010701d0100c0803000e0740411640890007010fa400c0c00d80340040010006000382a0030303082190007128181c00c1c000c0c0401104d003d001620030380c20301c041041e6207010740c00c0e82c1d40040902c0039014201c000342080c054107113980b2085a050056050b613100075142c2c64032180d50a40e180084440d00e075a0b0b220469081c50008a484102c04649014007450070142c00040b881107503401620f418030b100b01301080e0920f0342c1004855003603a800c840c0f01e890b40b60144101000a8451081d940124107000036800415004001c4030b2250704e002030319248160840d101c031503c5103505001304a139 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 899552931 1250 899551681 899551693
    0x6090405070c0f0302070905070305041709151c0606080702060106081b030f040204060501020f07090e0f0a0c030204050c0f1803010209150c07080a020a18020f04080d090b130509040203 81
    0x3c12108030154910354042d80040095074070f40841441141c2000300081c007018500003e0000160013059260182004098041c0c2c03a00c1408000400120448142d200340b00030005120300300c51100d180980030160761000070030415554240607201002d0803039040340180c000c40d0060246c039004e046495000035400425201182951252044640c0161142c0c0401c0c0d0081e0100021460305000c1c1c0340140c00700b840a000300204200d140307580c07a0590300840c003030b4a484821595401c0c0040007a4610868510220f90007604182020440401c035130000368015410000024007100300030044a1000904248491521144500001306040c42c0c0340c010341c1c10f54082201c00460707602c0307564004422003100030242c1d5640801100b1464420709520124072074201044010150b038071300000c40100c0369218004500c80421300c0307820b0020b101c0d03840e0480041c0c20214010a40300ca00045e520313201c00a82c2c640b80c0c0401e440e4040030296010306007140c0000c8915400038001410140c0540350002c2c4041c0444030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 899554181 1250 899552931 899552933
    0x70c0510020102030a0e070f050d0f05070608043e040b061812060603121e07080a0305060906060915040e09030304150b010c240f200906090405070c 65
    0x6a24480d00305510050f900842800070202c542d2244100b68102540184511882d0410b51600b402c8148100d5129580408016040c403980c00c804401817980242036422280c0c4480000d80610001d6130150740810840301803c1d078a080303100365665a200c1000300c40d07110701c40000054800f02c0c020802c20360001d0702c407815034003251502d5018020f400d000e8102080c803100c6002c00d101018a0584440403294071440034050291030105e49502440e01151000365a250450410b5401d488092050701603e030000440f0b00074418140044d240d00e6281d580c0610080e110303002000540041681e400e544400304012011980c500903c0c40c5082112040940d81803a54484c804806a541112441000e0304000100010441d030321840c0c501c2c18030801400c0008178042c10009000a191800050008101e0100d090303500300003c003112001c0b80000001d020b00721907205c540d40948101406080c5004501c41080104558a003e8030403844010384281d04050351541080042e1801401c103034184500c480f0040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 899555431 1250 899554181 899554189
    0x5040f1e05070b03060d050f03270609010311070c030501020a2d0327060606020c0303030709410f0d03080a0f09050307030e0f0d08070f0302011d0a0b0a09080f070c05 73
    0x140841c102300060340c0c4a04c41004404c40e2064031542d040600c43c00c0b444440c2580d940c500c103881003520207283c0041d00304050f400b880d56030320641c034018085091349030002007001015002440181c604c1c0d60740d00c2200d006030350200040d1100000d070401d81d0321041c030503024041c4680d00c000855030001e2084100d040b50700a13222003240300d03a8420f8070400d490310300c00c0c005103804004492108005400451a6261141c402003a0107458012155410314075a6415209418030103100300c1c03411a00a00102c1401e60058915194507550486d0b000e030800540c000541e2a040d04024003441d0162500700b020b56401040c41d00529500c2c10f101d0900360307143e0001c004183c041024001981c800d840310b00c111245c510030080046150001e451141101d0069000003e1000050f9140300d580400c01c0e010b219040c1c5401e130b001d080458142041a5914a0501181c1c0000a11200ca10b4040d494042045d110000c014003921070b00301010b4500c003420002862440407110060204500810300c4240181c2c60350001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 899556681 1250 899555431 899555443
    0x30a1209151808070806070c020a09020d020318010501050d030c0f0f03020717030f0f0c011d0109110603070801030308130b010e0f07090501140f09030105040f1e05070b03060d05 78
    0x200c00002c0141d601d0200048400c40c195019000010051810a24200380580e4500d80141440100404000c1400440d201c2c42d0a40000c4c08980381d0542d10b5544450280e4005d4100311180c2d40c803a821810061078800f418421076050b58006400607a9664081c0c13000d550140c0b250800300d4081c41010150000300b508072040000051096000d809042d140076071607801000080c070400a42c2e003040118061070382c1031a00325903140701403900f5140c0741e002c5502c20500401550400d084104506540e00411100651143c10b042e4072444044035182c2582050117070b1b600046403468040b85c2035000505c08240240c8004e075000b21507989050241c002c559a680c50746600380e004910384d820300f0007480740000f000c0d2003041d0711000c180f6269007a2490300000130010f038001865004025000604200b031a566481228010b0102070000d00c180d0519140c02e440c4101030007805e070b0350311203012120386003030500031600b0038041c0c1c00c50b000b01004d50501824402c9a030014180c00e07071000104181c0000a5418810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 899557931 1250 899556681 899556719
    0x611030c060c09130510052701080718060b0702190b0a0206040c0b03280e120406020c09090601060807110a0b060306011a031b0f0f0301061805030a1209 67
    0x161a800f400c2e05110125040c0f02c000d83c03180c1d080208000014111014080490b030044440304100c650503d41e03015640d030b0130820700010604020010482000c0001c0c008101c480324580d032142c0e0000c1c00c910008684440c0110307420010100240c40161070110780740031108000c618520302042c0d0b1080800c4d5603600881d00c65015030450f0b03007048140464030750040024048040201d10b540340c00b1851442c108015203000c0d5000345041c3c00304500c0d12066101c000a02c0c030403000c540c1c8443c0e0410704000b45030440e00c14000103209181019015040c00d0312680e0250744a4002032076142d003000c02c00d45803114008c0200c41003140320007040250400411443c8096802003180c40003d01317186091508090050b00711308400b001401417850404001c204803680480f602c120307a0800c0c000740032018440e11034070749648480040850b084e0002c0d41518011343c12901d40345c6585c5800744089100304114400c5101c0ca5905400a101c2d0902248820b01003003140481441c0c0484401d48030b01110041c1c10002030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 899559181 1250 899557931 899557951
    0xb0a0c1716061a0d02010c020120032209060f03060e011515030b01180512030403021002100c0314010506071110030b0f040b030604140102070b010b0702010e09070206010611030c06 79
    0x100304400800002c8403c2c201001a5400208141c403034002a01c50840070b00020b041006c020b0001200f10049a2100882d117152025030790b49a000d0a4000447d807480a82c5505141d4907450005440e0b84a00c2080f00712880406e9813260031313145417038200080076000d9040344d40355214840407400000901c07000010388002d40c0c000341080e4500f031b801003c54616910300382c1800030400c2d4010b1085c444000003021224116600100d80d11600a401e0071030040303500c029000640310b060600025008107618441103103080040110004d240800c6050311029120002206030070f078010310060501d00010090035004602c500000b000e4900419061610f0100002c00a40d407015010000d107001541020030a0040390240155904140080c0e00d4180250000388000080c02541c4030f811005c0d010f580350a40c02c602100d1032917a451060f80600d43c000b4074120300203191400e10000b1481d11007000740c019002c039401481c1981c02d01400b60342840040c00e241100748400c1c006804810303000c1201c5441945054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 899560431 1250 899559181 899559191
    0x5090a020d051315020f040302060a0f11150403030b01050c0f010b030c040b1528030c08160f0302090a180605090105030312061c0f14070b0a0c171606 66
    0x210341e100c116030024104440c041e10188140d8042000d02d464041ca5a030f1061005965034542200b44800b44a50b40c0000d400810125810414a810628408d9401c2d05500d40c20100c908074801c1c50b0b02c40285404841e03400d80094003240211707200f039010100000041c1411880c002315030401d28a012104109140e9030380d12054000d8190034140084080b00c1800e5505001d801d241000040c402c00b410341801070030050104080e0061580408402d040c41124490072000700043c50000b0090700ca139040110100b00e0610120b81040102035076007800ca4a1030b07583d800081c14a007800c80c003030b6000d04841c543c4906000c030041440c41c0342d64520000c80030301850001d51a450401800040380051340814841d400500c4050590034169040c964445401c852007011001c0101007005072001c944005004c0310380c51541e80e410810468002145600300760122003081340d440410ba42140b103155012800521003016280004408031f440c0305107002518082d03030616185150401d48a0f2445074191050758a507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 899561681 1250 899560431 899560447
    0x210e0c0102160e040602090d1505010b0a080a110c0f030c0715090b0a09030f03050d1a0d170d020c06040311060105090c070c090c0e03070e04020d12020705090a02 71
    0x42004090040007030001d408141c0001d191054508500d00c9241d4002e602c3c5000641004080d42c1101d001100040940508810324100761117070381d6007240803400c0d483c036140010441c520848280c41c0700c0c810540d581001175442260b07031170140014100e6074420304014400c0f148800002c0c0030720f03140b0700c02c103d00840e1100d81d080b500c140f03080070f940e01c11001c80801c07820111200d030b417000e03116050725804d80901e9aa0300140d00211151040c0d50300190602000c1070242040641c0a8000c0400e0160b01500740301c80560b0180030f550b0580205c441c25404aa2400c04900244030039131400703055003030503a20604004202d4000c205a038801c00c0601d030540c00403800c1204040c1c011300b011f2000880480104160743c100004111030040243c00117440c0c94011401004000014503c0c901800c1082c2c001e000300030054602500110507610101d00c03d008603c0c003c0750300501501b1003885a0707001420b500c3c5050082c0c0325103000710f80350250102103004000c0041801d0301c03840318503406499904030040c1d80b9821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 899562931 1250 899561681 899561683
    0x30a090215180108160207060f2c1009050a05010318050f150c130e0a0b0a0e1005120a0201030b24030609160801140301060f0f0e060303070302031801210e 68
    0x100014029940c0100c5c02069990028a400648050303042c81107018800044c20b480c580706852441c4040840d03126420b0b003589140b0b2003d140343c201581e002c12010480001624443c1c02401015002030b00d5940030082c661280d00000440c00309800880040d030601d0b103415042c001e072142c4418542e8043c06c2c17041c117401003000c80c2c6a0710110404c001d03401c0448014049803040498030401c60545155400b041c0c0303d4901d0340c410130300c01c1c070001e00c1c41e4640ba81c0d81c81c16282d07015048034400b400c0d4038008000106810802e240c55107522601c1e015001c521400c1e8015002007550b00801c94001c3c600c902d40800c0c1b0001001c0d86844030810180071034891903c0000c020300d000c0001d122058404829034041d0f4003607040148503054405024980380c1c4100303544013090040a42d03501991102c03c0e03d0100184000c100c006070303000d4410310641e028030b503550f410600d41c0d40c1c8078400008006078810003812044444031400c0c82d480c8032051400911000456240940026402d5452980d0780d0f41c0d4642c0040c00c0030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 899564181 1250 899562931 899562947
    0x504050405101a0703020604030309080c010504050706030c030b03100911090702060a0515030d230d09020a0b1e07020607060e03180a050616050c10020f0f010b06030a0902151801 78
    0x1c0c8a40f292034421140d400035210000a40000c09054450703802c1c00c100207041c42038940d90740d9030740001c01c040d1030581009981c03101c0078810080440c0c50011610440e61190080c003000d884080c008107020034903455017000402d20080d09851781b83d000030118000d40c0c0c45000c99401504154001c1600e4109078281c0402c0741c002a210120007060340300f41500780c0d240401c00091188203400d110110074851511a851107412a90008080c000020307000017281c2a948650b00c000d0094400c00390507500c03607030305c01c0061050802000f04940b0b8001040c1111324000b0007020301e603201030011030401c80c840c0d8680050b03488954030441d26030030200740783e035484a080031081c1e03d40804450307100343d0f58500800326401d842000b8041000d807000d030155a00b404402c100d031140c2c121018060841a04003c03100944660090103952403c2c054a8121490030b20140907684110038002d0910b8070355101e411881004102d035640881c0c201d001a051480c4401950700a8000b414807600c0b080c0c440c410000c0010040c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 899565431 1250 899564181 899564219
    0x80d0f06080d081038031815070203120403170a1e110313060912050a1101020f0301140f0d080c0c06030411190b0f1c0b1f050405040510 60
    0x403149101046100307101c032262480113245482e20706500180212040422184403403044031214000140801d441d04d81c07030400c90340341e6035000ba5000d0035121810300b80364230003d5075008010380c01846015401e2070905107007904144281449400c01000400312610700708100c44113084030390340f6120680072417171b0050308030202c94003030328100031041200c00000d65034000680078107895150f20034810108441c942c0b000303c4a6400021810402c85505801492944080501d10004800b104030b008120f205000341c2c0e01242441d41c40609503800d002910291101200c611580f101380301381c9172b150030740758411030320845e5002e40002036540400c1110103180400088966000d203500300208004a218400428003000e000c4500040344032100119000c10002c42c1c101d142c1110700002c0c546003a400007801082078108414035440ca04600d412500101e070041c414880d0003114420b00c0800d004007008c241c0e0000c1403203003000b41c14191500c0115044803011100900d503580018801d0090079030300682e4043d11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 899566681 1250 899565431 899565451
    0x50f010911190905120c10050f130b03090d05182205100501020106120b1503030f160203060a091e0c080304060e1306060507170d1802190b0403080d0f06080d08 70
    0x19000c00d06c04540300070802c00960003081b00c0861590000301201c0c3c02c5840505040250200080c2c5030030150b0f181b9402686c0b13003049481400d170340100c154060819103080e0074640c851880c0402c0700d002480f5025503140d500000580128500da50034210a22640d406180c0481c0724400c518140302c00a821550241c01c2035030b50f2002302d0350260000d02002030340c5078080ba1050030b05000300d0205011030301c3e6006040007041d02007800304a007298070710180414050319000324100c90690329240302d0b81c001c461307807214084d02c140c5400030a282211504440600c60b0b52203070604483c085e944003c11400c41d04103800c42c00025035010760520b0300d484d20003d01d40c44100c2d00c9404210b560b00d4541c0c054040c1c0b242503030042c81808c4c805c0780954881c4405064580b0700b0b040c82002c1c0302084650101440038848039100724800c83c2198262148228440c42007810354030144141c0b40360908545400c1d400e40c1003070880c010481d440d00b02c28442c00b0b80c2d9004d020000c1c00c10400030906070104810207801c3d03441c010550340e14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 899567931 1250 899566681 899566693
    0x20c12100908070c150311030402100302090d020a0b07060f0c1e0c020306011805100b0322140303100803070c03030c020d020d0c090f050f01091119090512 68
    0x2208004a00c862020551890001c1c0300c540a241980042c02010070140110002c0c10001903c058034900a01090a00340e404220b54a140042d400660009036000b075000811407082c07421030760003903008241c0b04070001c000c0b0b583c0484560018003848003035008402e200c040031841c1410003110b40503040b100c0340c10081c28004040a20340040c0130303c1100c10454016410100f07800241070044001985494003e804d40d2210b40c0c6884200984002042c110400107280a00040300e4000340201c03403080d46c5400080514503200d00d020091070034114001c00d6254041c0041c0840080c0c0081c901059006416002d15206e25111003c40700f420190b60194265420401c2058001540c030440c840c240c170762508000003d0b000c02d0000c6200904602c00c000d410040c82907450041c02443c6e4103030300c111080154140140000756000a095400c00d84265002e81204001402500030b80d40081c0071128500a199040008150b44240110903400c8148007145580000b0722541c203100300e981c03041c901d44400501d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 899569181 1250 899567931 899567959
    0x20f0303130803130614100b0c07140301020f04030f021903052116060f05061e13090b040804150e010519120603150b09040b0a0b040b180601020c 64
    0x111030310340c00354002d290250000c000351040c11458410450309810442c10001c19809a00c0304034503d1080e503410f4600c04603160002001c0361280c048444503508400502030340c6241103128000c00720350354034050703040d5028880030340b100080001500c0110700861414041c0500e900500a042074200b509150020500c18144007141d070020f6210090100031012891404240d803482c0154040c00003c1e03000081915904400e11000750006400c500c8030840400150300da02c42040320344580346409000440860688018901c1c002c0106521050f0400000c42c0d010442c0c0e82d009124a030858003120280c0c0042070600c203c2c4040340000f414903640b03081000e462202140040e0040c0035540c4601d0302e0080b0082c0c403462452158050b80042c0a04500c10301000e916407070b0010781041e4900861107114a40095030415140c44103c490055810141d85803ea8541c0600310303000e040d00f0b29030b403900141c59085030081c2d07841d054100044050110982c80344d5040c0340000a00b0301145085840c4038500d8410ba509c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 899570431 1250 899569181 899569201
    0x9040e030c1b061b060403030c0305190b0f04050c04030c09020a0507020603041a0c18060307090b031b070c030302100507052506020408070e073b100203040501020f0303 74
    0x3140b1281c240c00b0350803030040900d002030114480d000420488006194680ea0040d800041841c020b0707100c1c2e1014044004e0841044040b154102d0b0305a60f03031504c3c500c12010500c4954815000300c1800f41c182312000d014903002c5020390300182e442c83c100290001e410400c0c005500d1441028018019040d49002c071026070043c00d6000c0c60201030300c02c81d00000407404200440728185000c07402c407100d003c105c0c580a08003a941d6040844c51041c44940082454001e140c0041101c0c440c3d20291600004181450710344c1e0304c2c607000204900400310040030303460014a01c0d6406850304074421030300300212504dd80340080c1030425144021013214103000a00407115041030541d010386418001101d90503a51000140300c000b0040c038090491440040e010a10080104548041c0c8104c60028406500d501d5001c41d000c16001294070303d00d0302158000c9071088084090854403800c00f40144544203080800201d4410b140201c440c05603000180c10812541c0510803034140b0b1340310001540c11481e181d6404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 899571681 1250 899570431 899570443
    0xf0e09010b030c070507080c0a06021c030c0504080726301b0105180601180b1f020a0b0109110d0906020f03070914040525050408030f09040e030c 64
    0x50600d07800e010000800c1542440240d0340740b02c1e0840c0c02c4640150341c070307940c0c65200c002080c1e0b0540201c0101c1404295a800010114240075054500d02a249250380044005009001441c801c00004010006001004101c1c410140648002801941000740c0c4500342480d41140314041c00e0b040203035942e02c40c001c03408161042d4070000391120400c00480c8000f1060b813158003000340b42c0422403441c0c511402c40540c0702c240714100110300743c2c01e200c58030003a01d503a4123824800c190305042d1b40080d24640340640c5e003008072407030005049000311600541c1904001d03580440c104c00143d1001c0161028007540401c034a00404940d10100403503500d01c07401000780e101d0314050001f07540d00c41ca031940c00c0004507812201c2603c404030039181c40342404e5100400c0d11a052160080001102a2500a03403030f040c481e050180208500f0941415044800c4012600d030030305a00051200611000841c1c40b0180018495610510609951f510544007040125600c0c4609000f55500c01d0003808288940090702d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 899572931 1250 899571681 899571689
    0x10e070e0109080114010e090102121302031c030e060105040b0a060305090a0b130308090d091e0302040e030903190203070522060303030c1b0506150d0b0708070f0e0901 74
    0x282000c98014001030b2207020003640101840e620b40500162200700103503004e4140c0e4110707010b14085444a580a500740c4c01250907503c401c2c25800e010030421010345401c40001480501507820308003903100003010f100c0d01d9128440200c0e40b0f03440d052070f200c4000d0003450b001d020101d07000c000480c480000f107010b4032520b00500090640c1d1790081841e102007080169510307940700e102c0c28214549103510b40401141c016007240400d1051020490808021881c19000340b0141d4550103014a0700c4179900c045107c89080809010304c0c824040b001d03887c2d1b80122459154a2001544e540b0a0501854a48010684e4502da1490010103c1e0010f0f0382c04202c000c1110b80031900c15046003440480c44449071000a00e04c100d4030701d003820010805805400160251400f41c807100c85d082d41581034228100301d00c003001040d6400017800907031586102d22000400a902404160742883d0954804407070035401c1d521100407851200030081c40c19800304181c1c85c1444c45190000320b041c50000803c20040701801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 899574181 1250 899572931 899572937
    0x9250507110a06050702030f030442030e0f0c0604030b0c1603030902040c0507120f0e0d1407150206010b09280504110f0904090f02030a0b09070905010e07 68
    0x210a030620034800346081036028024110000a41d031914050542da10100e001c90090260440c0c00394060000700503102100c000c01a0206108400740c2041e960900c40042842140381c0001c1120990f50b41904075043c00105803000074182003401c0e8502c0c034280b071000c0040c0455000c0c580b440c14689403a030580d01100e6000300e100806855000100c1018015001d980c0052804882007006155140e00018030f43c40c0203a07400c01c44454481800c5030344d441814030240c1126111010a4101c80c0314061381c4c000b02c003143c80d01c403003840c030600c000665400c1801410388800d00f20084038901050140580d40040c10203c0401c4040f0384010000794540030144165402d002000c1181401d40e00e40d003221014258a504122126078107001400321b01c07c0050040b640500d25120202125154150444d040c5040001c4810b081ca41e00ca01080058402d6400c21510080c60494210060320100700e41d008181c4200c41010091070802d07001c2d85010f500e5803044088908020040021407810b00b81d280d000801d900d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 899575431 1250 899574181 899574187
    0x3020303221502160f051807030b04060f050a090c020613051207081206121f0b040e060106030b0117040320060109060f080a0206041206200306092505 66
    0x380820740e00c2407540c040d128010311081d000340030390b5000c20350600896090072135661071600d81e2003406801010b4003170b071a00800780b0345102c04166041200c82c0da00c9440d03442c1c0411041086c0780454242c0c0c0c05513014400340e049840e01481985010442074000c3d01c0e1110041140c6140504020360780c42025001c185181d0000400d181401310a02c070807120b0b803869078506980c4d0603092070501c506a000348183c4a1201220000c54050b2030f080c044842e40d41c0502004280524a80d9040340d8050880d002d40307029207030348806460030341d1154000e402041201c1c0018050940c904030b4080d09039160f2240190405c032160241d2030071054102038441e08140c0603e0440705604114540090403408540400443d100c1c54000080207011904100b00341e801c1150710001c65940d81c0a026698129088000d501241c14401407180d03090b90880c500d800740c01900e0208a02c0641800c840780d800c8420984211900d0001c00c011007030a15442071138114003154072142039a070610301c1c0f4840c000304100810017085000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 899576681 1250 899575431 899575477
    0xc080c030901020f0a110d0206040b150a03050d08041205032710050f1504020403170a02030d020703031409060601020a03030b01030905070e0603061b0f0d020408030315120703020303 80
    0x354151813144040b0549143d8844064030064444850504405054440d1b846a00c80440c030200e142402160b101400d81c0554a403401c1c40d05c000700700d5141c01a0041c403004000030200e8401c100a1309000c1158564806034103103814104c40c0c0c48401c0f03030740c641030000810600c44100c003000c4010100c10940c19041406101134034009081416040103540300740d041509102d410b442a14415000307400310800540f00d41c1030720061100b0707070007035100103004000286200202e500d5208010b0210300051300c142d0385055805406041207070044142900000d42c3d4a0052080044000800750070000d40c00c020801850a003000035a580c6030502c00404040c0c551580e0410b0703034040d400416a03250311a040d14541c1d41c0740c2c0350060b5201022030f0064460302c075000100b104510001d800705020f410240ea068500050482d801c0101d0b402031060880d4181e08001c005a60310f020301c0518043c1c105645550a074114902c1041000f1140743d000041c5a00300100400050b500002211030030285407505001070300070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 899577931 1250 899576681 899576683
    0x130b070c0602210105030f1c020a0c060e030607110615010311040305011a091608060a0e0c030a0b03010506030c010c060b10050a2705061c020a020c130c080c0309 71
    0x1800c0010312880c0046001e8144030803090341c4039055100c800000710380da80d07102d0800d651168900011000c075000085080754440340d049410500c4520390040f40c64169a542c2ca075001c20046900c00b40000342706c100802d100d450b05100e06500449035240284903d4036840ba000e031900005000ca6640000c03605014001d640240c000c031095049031a81240c5840c3e690900340d02070510b0004a4003118540350442c0c1d030f58034000244500844107541c0c103000e08404040c0a807040107014103d5039120004010001e9902e42179844039100e180b0f843c01c10b540b40c0c24116005003c0e11900745000c0d11a03414141040000d440000350701c6c0d04c031602440e142d00020694100fa000400e40c0410854100103005600100e41d50040c00409810400380d480c0010080040009045208103070b0075084144081501003107a4030308800541038441c07000514410030031401102030700301d0b800701d0011000360300003840c0302c00c65160003509410307440300a6030b05010010010200400a00b401000c0d88030101c0084041848400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 899579181 1250 899577931 899577947
    0x23030c12070b151f02070f0909050c0d0519031d0406081b0105070605072307080d090618050f010c020712080c030408030f09040609090308070f1403010e01090c08130b07 74
    0x1c2c0c4d003802503e03c07400e9500003e484640b0f85c003807603580c510218400540f00d0310341c0c46041c120341d0b0030801901000d80841d0402100300404103068402d44903540c420fa0100c4034210310310110a1098a501451400f02d040ea460420750440581d031189242450403c001800880c149460002c01070151400580c403400694582c016454042c089510f80320410210303540002580801100d001420118440500b00382d02143c407a00c08010504002480b11448140d9190060080a0b119240c007040001340c110000788140f004080544280e406001e10301034041d070a2054401181041c409441d04900b0115804605054032100030009100014041c0c0c03000020700c1540c001e4140503080e03e036500e00041c03002c1c00c50740000851621442c904400040d032400e0301c2c0b01d01511154140c84511003179480e800c0c2558030113804e0242d0302c00d0102e621050050105818002c40c082e2220f0b240303284165040c41801000c4031005400001400190303014451301c507034802d44030820382d0b41c06a4000303510f0f66418000c5032001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 899580431 1250 899579181 899579209
    0x20606030703026a0305060a0302060a09030209090109030c08221202040b040c080f060604050a060816030e03070b10090501031101120c05041223030c12070b15 70
    0x20310140c031001e030720140381d82c403041d00b040c8413210380050f41c41000300e1080042a10882070240824100740c0081d40d9000c1d07017180c1e602c84002825100800c3e66500401c801d07500456800c00058a41c0d8414021480c1c00d0101d02e4100309902c00800422034907030b0f400307001140308d03481c0500783d034801040d8400114200b201401080410480810320565180d01060a03038110210403440780c2d0800c41802c40b00d040c20f22a146485015603515241030f2075108002003900c001400d0280c0012040001040c0742c0c0781d0761804402030400c7d0f0f075030f4040da1510030f0030884449200860b50003098103003010507a011390300201740e0b442d49401250f9880c080d05e54401c11140c0d128540c0c0180c0606081c000004140402c90341d02800c451002c0e25502448072200044508442107a051a00454000d00060007420000006024030ba4031801d400782d07840c04200c064083c9540304a071000c0c15540300050140018005024690110464081c400d0510b0116940c050b401c22004010103c008104840a880c036500c04602d4400c035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 899581681 1250 899580431 899580499
    0x6033003022d091c0b07030c0e1003141e06030615090a0902041515030e10091415010f0b03060105030a050702011b05190c020a05063007030c02060603070302 69
    0x2040c0d0722404c01c40b101c1903140c1510703018944000030b045140039026031281c000195807207181001c02c2c9810050104d0500d88104100340d40d4110030210b80e03a841174168042e040d11000300030207407003050070401c18160045c5013501a03085081840010401c0004134820148111078040055440c104107200078080e804020358414100a55280245090f420290a58031049142074400c0c204241c1601600d102d01243c3d215580149000d801101c034503440b007500c451040e141c0640c1803048859203413901082c2002d500d8800c100000401c035581c101c10781d4000410001c0b10540c2540f4000c80082c01d02d000c000c100d5009162a2000120034034406c7d40081286404c0390081400d074010b1640060041e00460010b06c7e18403c1c0340b4020000f180100f40c1040000d5000305050380050401080c00b609400411440400d0000301d02c0c0013042e55800d0000685810985980710400d2601c00340040644009100d9042550050b8040c4a0161800300d07024055a80580340300a10101041c440e40d08140b6107210040b030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 899582931 1250 899581681 899581699
    0x1603020609181003061b0e150c060f01170d02060c0d09020d03030b1009050a180e0d0e040605010906080f09191a100617090106033003022d09 62
    0x40c00c00400030001038900401080080e01000c014014952048418046c00302c0c0c0b00119440c500d2401140b0b1000342c183c0300f071015041104c424160b910302042580e5a81540142000500c540c403a11401c1072545182a00145a080131a0302e000e074555070060504051603200040c82c03403644105422032107001c0c0c0d0140c1401301c00e807518100140203201d1800014800c9007143d44450700b46105880180c141e50000f858440c0040c83d00240002c040c0c042c841c0c5041141e12007400344a049002c0c010760b1003401040d00c0d401c1e6440000c008003c101c0e0103c3c0c10007410f01500c240c06002c1242d10100346030f0b00c040d140c48002031036110307190002d141c07001c0c1c425008018a51000c508040020f00e45018541109092814006032280c403205901010b43d80500c0c000584540300d40c91011141c4440d41d40c2001c020b0000081c1107840b80c4035640c0c030109180041c00c2e9503068080d9201c4c800c00c250307145600c9a0311840c046061000c42040e007880104d48000d040045803684850b0003c0302c9960701145c0f030b1041c00400d00b141c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 899584181 1250 899582931 899582941
    0x72c01053c040501090603020714061e011a0d0f0608120d060f0b0a1d090f0103050c1509010c05010b0a150206150a030308090f2b02160302060918 64
    0x25600640890154401c0c141c5400c48040c40c51410a40e001c2c2c5005031600c0c0801410040c003240217400c8414142d90407860f15000190800c01400b0b450b01501311040302e074040280c40c820740142c0e40c9060f4050210079440e901c10710680600d0a05651140004800214900800303a030410050710803608515076a0040007818410b00104100070302113043d2006007449001d603940e100103040b110718403c40300c801400300614403005200d00807d0904201028586001e102150041080e088044404050310719040e0300501c14413000700241d21000108030f402480540d800110314420380a109d035018140025042d0400810000303400c000d00300000900107080c3c15982d2880324100114401248016018500c041200d108000c038078440c3d0383c00040d052000491440e40c013241c0029004100800344d0207071700704041e01180107209480e119032180c0304245100700ca6109a07201407000e00c0b000030030f652010b4226111070b00d0605d105001c030f80c0c0440d4565140c41480010071800c800c0c92466000500c04003007044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 899585431 1250 899584181 899584237
    0x807050114010b0d14040f140f010c0201050a060509060102101d06100302010e18010e0604020723072903070c05070e090111030411040506130c03090b072c0105 70
    0x6001568014140401701c981c9406844c0200b042c0e40290451022107442c030086000c00800280c0c0c0b01c428811034562440b0b080469084622900e01c2c800181d44074001e000f03080340c5c50300420f0301821048411844504280c80083d668581c82d44182d01c2003515020318550400030a0543c008144120043d01d00340d00d000740d003180150020713010880c0481c00c400110009420710300014101d03078101061a0304582d0070414264145070005002560054023040501c0010ba1110a228a4170710001922811303025058081414400190400c030a100b05103805401c1c10b401800c0c21028410040480769602c0c3c84050045882903c91407010b080f0380318440d00050a064042241c1d40303d41c00b008001c00843c1281c5541d46032500c41910084c10480200280c82c150349003e40c030198124000502e400b00703403190115070200341c400e507a00140200e47d4400c917080a0040e040c20040d400030142c94801280b2800c0100308400c1c2203e00841d18440503000c150070300c964002e01c2194803440311a04005840c0404401036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 899586681 1250 899585431 899585437
    0x71202211308060f011703092206090e0d18050a080303090f01060312080601020a0c120c0905130f030504030f0b22080405041806022d070f0807050114010b 68
    0x5000400724550001c2d1040d0007040c554001c2a0341e408800180c0d10f0308006401091041c0500d0100340400c00c20103480b642d518108044032400c4220400f801c44c0030303030004c03000c440c1d041d03110700400f80c109144119100030214a8442e00307402c03410280c1d4139180140d10308103500416004150003061042000c40c200034000091841000040100c03082080009406403e0398200d21001307080c5080e80c3c4084400c0c81c0141c000d01c1d400f001c10302c1250041c0030340340c0740c3d504850407039400100c0c0b04003c0007200b41407140c000d80798005089100c02c103210a040524540c3c0440700b0418020b0030080d0311510740c808052041c8100d81c021900902c4201124030f0070700f071554120b00c0a480000c1b038603200c02c45940c5013207a184103103e8440d420603403250a10b890030301070001510000000c00c00118a000c0b1110000d03100748040c1c0a00c0e59402610030306540401c007000b9a801c9400110784032414180001d40002d049101c05440480c0c0c880621a1034811078a06180900b02d88600f100e01152810000305128181d5405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 899587931 1250 899586681 899586697
    0xd11031009031b03050910050c1b090604090f06051e060f090114010e0409060b280303031e2310060935070e0a060b07120221 55
    0x80c0c840000003408000304854040e00c0081c00f04000303048030320b811481d541c0c0c00b001060007801c141e80b400c0503000004a01c130701c0d81580344001c1040858100344112080046c50091000d00c9104140e0600c024002030081030b008100c00e2041d03440d88010380801100008852002ea4010740c01e00c16401c00c3c44043c0404644185843c0c06545204005080b40c07070314100124040101409000c0c142e401d002101c000c1032a5000307160b0600603c405030034802d443d28403d001e42e0501079000011a880800c0c20003008042403100010040c03240116105209040003020f01202c3e41418001680454004200c2000409856031601e441c5401d0b80300c1c455a0f8003c40300304141c5a284000021aa107803c02c10140e080b01d4005c0000040c0081002e0000322000b06104a00080c2884003e500d8240e400004400800c134201c01d05003508006410011840074041958220805c207074284010b80c208618542c07540200710018203e05408080b075000980248181e201c3d01100e2049581c04484008182c0203076404644 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 899589181 1250 899587931 899587933
    0x50d150f0f0515030106080411280e0c070201050406030b0301060323070603020f1e0f190801060504140d03090b0a09050102120306030a140f07170c040e060c0f090d1103 74
    0x2038440682481c1d0001c8078140c4031141c4528245441c0c179109c91810041e602440382c2c001d10060302036079010104c0b0030212604490300401d00f13401410301020b911031640c05001140c0604042c0003c20060382c21000303035000c2d42c0141c600040c08a01210000e405032207282c1c000b61003c0b40350b090400440714915a0340c0d00584540040303980b240c0e0b40fa01c04400324860800d2071024180b0500480e41d81c0c40440d03103016040340745141c4540c281013200302280c015500400002d1010440e044d071910760180c01000060040c02d01d8204581054035000708402c504078032000d103074407c9a85d04140b40c2054007908004c0040c1c10409482c0e621090700041c041c0840b4400d0103100c0c0548034100c600041d4418120407607100340c2010300685a468003a60385c2c000703480311640d4940100d019020b042803400c1c00130000d0704002e210003800d80904a1007a4001801c0008100d1000d000f40d00340000e40d40030b03013000a0010381000c280e1a07100d03982c40c00520002a280109a030b826400312000039040c050119407002070300802c800f14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 899590431 1250 899589181 899589199
    0x30106030b07080a11040b0d0b192114030901020d1707080903070c1e050d08040308090d050a061b081b03100801090f140303070c150b0d1b060f050d150f0f05 69
    0x4010444107006126600c484c002000809000300d0bc410100c18507807040b00140008100d0460b602d102da4078516a201c492580d002040070301c031039a0b0420003001c101445050160b0703507402200040b042c10780c0003001902440300314000700305603003400c200f102c4d900c1d40c202c0d005261040d1030380515500d41d005042480b00c8001150404110b42c9030410280324040e03031103690245441c0c43c540d500c2205401041c2c2d803680c441d10b041199408601d0a110300f802e014824140000c03144508103984014801280744082000454001c10254220441a54152140080c001ca803250380e090343d500b120042c50b800808a40d401e01000c00c04000504541c082010300c2030361203640800c801030842e40d032030008031607100004011240c4400880c142400b2080b6003d030019000c140c402001c0c0c04100c0000d0003102c111350508030304900c01000d0003180714400240105182c181e031807900d482c4000348240039080e0780c031001c00c0da0f508800302801d000c415090700503c4460302078440d50f82d031041c009180740da9905c10f041c0259804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 899591681 1250 899590431 899590451
    0x9100f090b0d1403120411100c050312040507050d0b06030c06120411060d0204030f050609030306150d0f180c1d040b181911030106030b07080a11040b0d 67
    0x50103a5400c4074405801140001c2c003540f18031500082c080408001800200400000c02c04400105031040b8001c09847c2000700010f8244450055410110b20130402c241c05000700107440402103503c8110039114540c982c2d1101d08004c1d080840c00c0c1d0106a10108900c44042004000c5500602c1540224251981c602c00c4109121451003103411045c612240d030b000090000342d45161340c03210003001070189800c0001c050b5041c0120307889a041520340d04d10310284201040420058141d000c01052301550071801c013040481e2001c0d62444140f90900c5d0081820100401d643d40f11101d540004402404600952081d102016030a95010360b00c03000c81e8000400c2008040340072041c00180f0400250355907035280c0742e42d440b10001030201c0c0c42c044c6991b201c42d000164100484030b80c0d0b94103015030204003000c41ca0100e20b4020000c10301030082c0d041075010000b00c0c1d142001244c1c08180c5050140041c0d540480c1003005000c01e80b902659101c020402242c001c40c4200508a610300700c2c0001c01c0301c2c0d204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 899592931 1250 899591681 899591699
    0xd020c03071203091e08190221030f0d3201080303070e011b02040c0f110105160f050712020307150e07060e0a0e04140d210b01090509100f 61
    0x1800c40034002c2122041d0400c40d0520f00d20034001026030b203805c61000c89880d41100350500b0900090f0201001494000c0d0313055142030f1101c0c04211041e60203031003441100101d0107450307004a0301a001c080303502007010305084206e82c000c07185a034002c07210b11070b4110380d4202612100021006a02d03140200030000300314a14000216070041c0d0140c0c0714600d41c04091001103420368841601c3c4100711203100e480e4001612103016500d400101c1c0e8440c4056554482001011051050080b01140e0304060500201000c40c00703551602d28858540340b641e6079208102a20180300d2074400828a800c99140745a6081e80440904400b43c41060003c2d01032000100030000c1c2c0b41c45019032040c0d900130f800c00300700c481d01910910141c401d0280031000010b03511039481e0300c07422080f81e0696030301400e071203d20790b040300c103014104080300181071610017600e0710000d18180d060661580781c002d90b50b5000c020701e241c0c0070344071100041400414407092898440d113034a410800c0c91103900c0344000f01c15400314000741d07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 899594181 1250 899592931 899592959
    0x91504022a0d080f150f06190e19060c02090606040e0103080304150b100f09171b0406060807030e0111030a0c03060e07020d120b030a050a030f03020405060403060207020a080d020c0307 81
    0x11880a60300440820800c00a40000ca000c0340c0d5801941048880d92300c06450705040e40c600c50301c0c0caa40071165803007020721103081203411b004038800940e60820b01902343c00c141841c000980554061302199144c2001c50041d200d150080040e95100c81c0000041080c42802188201d00c10b050010072030284444602c2600e1100b00c2142d80051400c2d00201c5981c8203524150a0941c00d14051070107d039038403d540c1080c0820f1300e05982e035410031405e600c2018a18007041c003000c03006880401c8640d02e40400180700803009083d00c0101a00c650713006180610940022414000303849441d580c2e070505070f040b04010099030264501003400c00c4d90010b0032102492541d48600150380191011101c1d50508841080080f500c0f55070591740c3d08040040b80e14200181d40c6401d110740c006020055442c10003408035925142c0b00d408042c0100018407150b1504c80c140d80c204d80d8481c00247c2c44052a100180004500390001951489801408070103d640010041c0c01c04901382c00341c61503280c5480d0300740c1d01e002d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 899595431 1250 899594181 899594191
    0xc030408211c0912030b010809030316050d060f1508090607020c060d0e16061710060f030902031005060f0a0311091b07030903060b091504022a0d080f 66
    0x101c00340a65001d0028942c1070940141e0702c510b0008600c00656500c0e0342c1522510a0340c00003036074941120426507004089260460350910046082d440e2421031845c010b50b0b90500c0504000005c80c444810300203642214029042400743c41100c0ca071100c0c01c4070783c002041c080c0c100000b00c010000c922188808200d0f83c6c002c001e20b81c080d02c13071b00c11230b48203000e1182d201c3e03a404643c59645419640328500c0901c4040c140d1140e004d900800c05142880080c0403001010603203600c5000207090081000300800d405003118101c0c01d0881131030f4000e48064000301956a0060740501540d5003400d0b00310301c540d0000b4410720b001c0743c10b540603141c0c070018010a1401400010000d192007081c007801850440042c0f0340c03158542d02103000c1c0700a603400f0f0650030317004440200c1c00303d50813400500c10030502d40100c4038000c0c0709a94038070f414944400b08040807458403602500442d130000d008004075044c003035440d10125a200320380c2d00e04415079140c140e494180702500c100190105010501003660102d100c1d001d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 899596681 1250 899595431 899595493
    0xf081804230630010209010f022407050d050f01050a060203070b04081e040905070816020c040923031206012105062d011d0d0b0c07080c030408 63
    0x655606818800c00342c415090a00b102d016080800440c280400c1c3d0342c91005032107100142e00c6045000014085500082c0d908040d900550054400d014103082003400e9694002c11440d000d4403802026211445070200f603040d00c80c201020480100b00101116048410903529091080ea80b900100d07140c0c0a06030000b03024004000205000c514514040e103c910b25a070080d50604144181252455000d071b0300c00a191602c0e0000c01000a41101002d82e0014643d203400c0c4110380090b10094462107405400c038442c030795904900c800d1004502460076100c860b88052400070700c910f189503a8a411210540c0d4058403208001425544a0160214540889180c0c406040f48800b026406428020701450b0810107040058402406551403035280d800304c103c1c3c91302c490311b032107000516250100745004092110700303080982c1c1d62594a03116440c00c0d0089a90706d91a210004c0b80c51252141c0b040103000f1a2021454140c00714010005000303c4840204842100c00d80010285190001d10704000d25 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 899597931 1250 899596681 899596751
    0x507090b0c0c190510082410180306050114030105090f03040314030c160314060708060d030e0303033909010828021e0f03060d0f081804 60
    0xd0704103800f00040000801d1820400c0c3c07a10343e800f24001e5542503400000183c0e090043c403081c000148400c0402c00c800480c0418901c80740c60110701108440c0c0c14400c1004044000d030000900c003216004051a407104049c4140c1d43d5401d0f50482c0740040310545403003540713044041032a854001650407240360901c00550b003000e02c4d54032241001030404000c00781c24001000000080d003c01e102207018814040d10181000c0e081d4100310315540000c2000c59042d5214100b8018450780024038144d100d07104403021071840c685442e007220404c00c41072600c1d40503c408400e01148103002c424070900c804002c1a9141409a40c980e078003252910151500d440c114100711b110380039480703410503da1103070382904803801c0003030440e5442c10100c141000c1c030b800459000c5010080d101c4001c3d14904074400b07800301e103407d081480c00090180e00c0064200f170b03c5404030f104501c08004180c2c0b0600b05091308000441d848400c11480210300040340c107422407080341303004091518815404405d00d801c4810040c9190 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 899599181 1250 899597931 899597953
    0x215220503031e0112020609120d030c1d130506030c030a1104141504270f110d032c060c0102040608070503370c0e04050a09020607081c0c030507090b0c 67
    0xd802e0388404661600200340c5090009c005030200071540511045603400a884064103800812500345080c00700030b80740030b0410103203545d92a5100c5c0d0b03100804604002410340c9650300064509200982c44035018080c1c50200e60900a400030030045802d82580c0502c00c0c5c03044e85080e82201c140407100801070811600b04980c8504156001c090074009401000344d038245004041136004141e071030304a030803111040c10f600802c420312501110b0031509a07521040b503060b03541c0c040e110702a50070500150318201d241c16050343ea03c050031002483c3c2c020303015940c0c600e4441500c0d03010b5401405082c01180001001c95a054402c0080720300c40c01c01130420307500c1d440c11502c20625a10700d0440107444008108201b08402c0241d110b90300c040c040740e0301c1e46e5019508010501055650041c4101a494500b245e80d0003d40c560074120303078000b030340a48000d58840211407a2080018420342d100b9219281004070710f1800d4041e8040b6026802d04d07250111000d507200c0e00c2d0b140301e102d04c0004507403a40200640f40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 899600431 1250 899599181 899599189
    0x2a030c030503191803110304061d131113080c090a021305120703150903020a03140d050a0203010302010815130b01090801050a020406080108070302010215220503031e011202 76
    0x1580100400c20b0540340211103111202c01c0d00c03540000b59100b550718107070b00002c05da0005d4140c041802c1c2c42000d18101849e040d40a0052806132201000410f0a12100740380741d0b42d03081c4031007159004200208030b007000c14071000c0d00d180c000c203020010300b01004601007203250002903442000c0400615035407169035040354400207034204694001c4a801c62440108484d40d46408016400103500000c0080d98034500f0302c07a00ca850b80840d10881c2c1443c000d0500003280d800b081e5808800d8050410180c0c2890f540407112031780c491200b25501003880d190600054602607001181201c0c000d07600d031005503c817100000003680d1a10303805540411015a07902001001e90048140e01c0014148002243c0d5201d400d60b09440044401c080d109a0004040c000c0c035801c80c004501400c007100003806207904550000c2e5449800c961842210032080d00041c00f45084404e0040c0780510360750b8000e0701c0b8046450426900d410641c0d0f01aa080400c201803030180d9021040305040b5041d941c1c000c6a1007826030284 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 899601681 1250 899600431 899600437
    0x225050d150b030708280503030105090c1201030818060310050909010b18040c080d0f1808030c01050103050c01031e0f14040f0b0708240406090c2a030c0305 69
    0x501e010b403240089101c2e40c1c1c09001400040c000d140c042c00340d80382441340003c01c44250042062201000d2100d0380d011813400416a0f064841c1601c2039041034030b44282044203405140d81c040f00d00c200210000c4200850803000e409410000865250011503550401a40b80400c40340402c3c3d044499504000034a0416041034201c2c500b0b100000d0450031070740210b07811140034200e807101c6c040e1030070030302c010007800300202c030020043d0034040e0a01d0084002c008100e40c204c00c200d40c040102e80680425442c0e180c0941c10000d100c8001141e5403021010350640c0030f06002d2105880d94007484021031202c0d4082d00441ba03516040d851b16a0707a100000d8a004010045d490031480720340e0755001a0190011480589401070780603900d110380c4845240350544140b10001d0034202001061000e2110f588a600f011403400c441030080040c6480440c8080f4004020a5211030307040c0d070801e1b1018429540240b8520990500746109409041342030351080210f0b40100c1000780040d026202183c0840c0c418806 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 899602931 1250 899601681 899601713
    0xa0b07110d0309171b0f0105060607030e19091508010c020a0f0f1b091a060304060e10020406030e010615050702330a08070216060c020d0b070225050d 66
    0x100f86031144ea02400f00c66103400104c3c113010f4851420300740e100441010089182d840400c4402231045103003960205441340a4607a00500b481110420808990340360f0900c13404050740d09039181045a0f850308600007a04801c2000440c44100d040007040200c418003810440740c1300c640081884950556500c0a441601302c001d0b240580c0c00000c400020380c4a0015540003400e81c0f90020804d400d01c031300302c0100e60740a240310080024030560b60a00d038130740f002681e6015070018400070324440074050050500b040d118488820a01c0040d02041c0e25825511405010186400801140e42c64150302d1030380704a0001001c011071401d0010100502d04429660380749801003000d03100c0380c0c940201c80d0704030050180c03d8040613080882c1c030700384156001f0350700b40d0706c07250502c000c4c02c10380780c2c800490f14421a140609002c00c480c05030b408066480307601401a01c0780e4407000007282413400e000000e40720204400c41c149036174250303001c00c2c081001c505241c40541d140104107011000c85540d462011256180c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 899604181 1250 899602931 899602943
    0x11041b05071112010c020622020607030e0d060c0912080414010c080427021806030a02070b1302190308030c18030109050a0b0901110910020309120a0b07110d0309 71
    0x3a03440d00ca5114500f4805484480c2400810041300606001e418400c0007031074641d6031001d0007507655000d00314925920109806450f003651f5039030341d820203c824003540c208813500a00001c0c030107010004207501c03c500c200c00542d1144c3c1c0d44c540b07818101041100030b101c0039061b804140b109012a0b5070b041e00742010400141041c20303549060f940c400101c2c0d04680e00111007555000d8a041c3c550346100210191600c420074210700e0906100022100c4a0400c20308030302880c8003000160720a0040d81c12100d140e90419000105480c1001c1c585042000e10082280290700d401e000080121140c8004800d40f540107540c0c900355030b120003100180da000700d204d4405480b10400560316540302846560702140c01500035203440d2146041c103241c01e650103060548541c3c5803481543e081d480300c034141d4402030401c5a40e40d8403007052a01c100e00c0c5005200160b07902c65a80c41e06a014807800045100100784110519a080d548070303a0281c0d00200c404035003100d00d801145400e00d030300344258840c4290a110700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 899605431 1250 899604181 899604203
    0x609070e0d0b061207030b01030c05150a08090102091903021201020327071503020903010507090501050f13150c050105100f15031b020c0f04060602070303140706020304060911041b0507 81
    0x3034000c034601444c540c802c0d5070b0071f038480c4018002d010000304030b440a024142c0324410303241d5800880f40101e109a00180003045540b401148071203c00790102d401c0040e0041c21001007090f50300504000004900c000c074440e00100002c50403404060007500e00c59118003900095121380141c04288000d44910039003006d020302c510108a020400c600400100c4080d82d00503100c00c034a000303240c210713603001c1c09907400c0c0040040d04000c107a9000c421664203000070340000762900c040e078540041400305030f08600300e41310015103500d1140e42d010074030815650094000744042d4a070b42010401d203034011301984040c0c44110406200c0c0721358020b520508003030742d40350010700240c001d00c01d0303041843c810a0301d00c0180c102051109280c60002289000184c080b50304110551509030041c0d6140d009120007000d11030103030851820303400101c0544040c1a00309009655901d402e10f04403000380003008045800d100c0e0220000c1040c2411b104807114176182d131121200000284005803010b4010210450343c80207d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 899606681 1250 899605431 899605459
    0xa150e040201081602120f0703030b010c12030c051c0e1603020607030509060d05070207080d0206010b0d091b08070512010e060103030e0303070f08031605271201140609070e0d0b06 79
    0x6e64000c00c41100e240300010340b200030b02d180c0141a210043c1e00c03d41040034151080010881007049821150414100082c0d10512540262440d0040201c0034400d2601a584000c3c5060aa0481c800b17800460081d01c00482c0802c0c01211150001c2c04080d40001044c840350b00000d000700c0051201500c0142018100420351201a040ea00200d8410005800c00c030002c00440f90200a02ca1901c400d500142c0300f150704040388861103020741000d0350002a1205a500e062203051003400079202036041180b010a40c580c02103599500a51003250300607020710004c0b010078a0103100d10004030581d48050031a80c0d203140c5007101c050f00615000e607403500041040000080b92240e0440c12a441000e0643d1207150400580c1d02c101c03003036040c032410300100f041548400b10003007105036810300e80c6069000106603e0004a00501d5540da2161060b62810541c0c11415050b490041e1085c4030031070300388a059491940c200c814032150840d203900f1120342d082180c0003070324400311036038041400307030110101440c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 899607931 1250 899606681 899606713
    0x3090f15030c210b100c1a18060103050f061b12072a140a0c1a070c0b0711010201060b0f0d0e03040e24060a0c060e060a150e040201081602 61
    0x80c50900f010030b0741d81c40a03507810a081c054840004013006042148041d949034a5050002c10601c0c22003034281012070003c2d01041d400c8000550840400c81118025a1a49422a529681400703d000148107810000c0c560b82807501d172480020004001a03030806040c80c0c5264280e03400588168140300030044120000d80150070070103a4402e0600b4620b80c0341c1507905009140807032260900b95141c106259200102d005070222204031510704100c41091100d000303c0303d10078003c01800406070021101e0000d08294500050f00f2110700810b203100030440c017a801079088960500c142a124881800b80d02c451400450240c11400640e40c0d01003001c107032803204242180e001d50000c1800148031014401008140300440c640309840c08030080300c2455000004000d801105050310420148594420402038150031040c0300001242c1150640e0800d90507440181070441d40e8016600d0b100400024610361205100d405950180c4603100f058540e81000503600040441a500707600c240300a508010707072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 899609181 1250 899607931 899607977
    0xc0901061d011e030903031401140603091002032e0609060320160c0b270613080f0f1903030902061903020d0f020702091609030b040c0303090f15030c 66
    0x44a5540002d003541d2a1074060100c401d213440f232a40c0c59101c480140820914000b130000c0d242d07012195161696034200c0380903d00264013040914260000c0306010b170745d10803e50312035079030b007050340150192131400c000040d4070310b403076200c0c0e08002844281c0030000315002ea070059405603035a001507408512181040d041651108400c10042c3c90104034400a1054141c0c455014040000d005860000c4019400380d600e0f40311112100250405100c0803540c2d03403034004407000e64802d4505840c0c090703a5400040d0700c400026071207600074010550a8441004082034441480740708200f2581c0040c020f031003c4000f040c107003408981240b400c00c0340600d001000b05590700c00c1c0080d594051f984d0320400d4400c0c0c058541c00c5038030b407803e24010310002005907a100c0380642c1c0551f00c11a600341103240d43d401291942019070024101581c01c60511080c06002030b080b00940b800794981c0858580d45448480400304c45200700c02101508404611455219070407089440e001d602e020115141c90503105041d02e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 899610431 1250 899609181 899609237
    0xb1305071403010f2c0103021504051f12060e15010302040e09011a04290f0604080c04140910051b0c0a03030b0102010b0105071103150f01080c0901061d01 68
    0x510703401000c120f90690391041da2540600840015064985020b1617140e2101c1070100034440c081f102203851100074068203036801003030000e01410080400590301d44400c80c810320300c20001840b00341904610307842c03402114115041c42840d02c0740ea686402e0800c40309050501114101340d000c000c0001c11900c0c00051500a8407a0000010a8042040e031403951005099107140102d0400d9088240328801e190b100344200c550900101e1060910000078541c0402c8500040d0300060200d4007181401c5d00082c9542c86d00000d0340e0400403071500e8900388180403011285d005c580d511042803c0c02e41c0304d088d004541c00c102d1501003800c2c003100501e99010f1580180f10201941d038800240c0000385580b50081440c4480c0a0000300248640c14000902e1407244060181098a60044810107a141008400000e503020090000e05003403a400c0101e802c442031080078541e1040005200c0c0302e20b8a444007504030b8200d03490700b0209003004c0340041c148080c5140901c0c18000b10903c20900c080940e0303001da01c06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 899611681 1250 899610431 899610449
    0x30411060f30040b0106080106140f090307090608010212010504150b0d09060c0e18060a0b091201090620041d2a04180905031605160e04030905040b130507140301 71
    0xd604006c4014401c1300164000000c11811090031130312801400301304d580c00e405070000c0503900d124000102c0c0c0f9220b065440a19054501030000841e01810342c080c1c03e01000078501058640d0b6a00100800e42da503d0360711074a402001c605c108403100c106e40040c9480d4441060114400c41c59843c2d40003111076204400000c03c20360a000665813070000541c4a015007410b0142c01141401400720340701c021180900c00d500341001403540100c4d0b42c0d0030745060110782020002d0000b00038600e070003805403039600b4150080081e4407402041070b0240f10245c0b030648102203265454000001500700100a024040d001b10348804400c02201040c500d00040c40c6130036400100d942c42d490180c0d01e20480b50300c9030488040718a040580b90006901208075441600b00007460003d6065a04040e03081c92690365025601100004000480e0102600500d115500945420501c030380d840c002e000a0300d52032000c55074800300c220010912044143e028075000b510b503207008006100c000950312500e0f4401c0e00b201c038171 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 899612931 1250 899611681 899611703
    0x21020a0f030b0405040302070e06060c0f070306060605070b0a0b12030703020610050a05240418090201030f0501030b1b0c10090b0610200c0411030411060f3004 70
    0x102034050107501c501daa000d96040004e482d098600946407a80c6025032421303100340302c1c003299007581d4101c260744901c0c80c54010781c2c905c012915120383d694600d42c842190380301e041010004141d80124180c03051342d600410b240035640e07992250300d03009059a54030182d0000032502e0070b2102c40c4e800c202034103546100341c00411090400c0005071040c0c078610380c007252144629140500454884070362400d80714444018100310388000c0f09102c401ca008035040369001c0d045100049110200d00d400c00d01919000703803001c01244c0d24407111903050b03410034040030b440001c003840452102002030110ba01540c2040803450308100c03401c4041401e1904003616a07815036222444d540601090b1420726801c0203048500c0003442a0b840405001c4048200d80310300000010b516040c503074030040c094042608030041007003000c100320b607003074480f42e400640f03050783c00b0900d056011120b41003103411a03800002c00d01d6094106440c0c6248680e400c01c850344000f1740d50000c0b200b00c11902280c0e02c000750203035204501440f2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 899614181 1250 899612931 899612957
    0xa0b010806041b29040e0907170706090b09150a0903060b090103050a150b030303040303051f0305030f1303061503030206090c090f150306150f040e0d21020a 69
    0x58080f0b40380c0030002e1200585010000344c0308440d103001c500c41040310b44049034100002880c4141c0502c0c3d00807845241c0c60010080c0540d0f01250000a84524044824000100301201c0d0b603100344c540100c00202c0ca8042c000c0c402450a90080d01e01d00310014061510035000303114018958010414401c00314030310301000c0c010031042d40030340f070348160050350132130301540c5107031540c0c0c0d51000141000303040d004034040c4c0c00c240d402c03840d0850840060b003d01280e81d20304040c50010028401111a00c01d0901b910700c0c0040b030f0107801200c200c103c0782c000e40150304010240888c00265840200000c109000c1030000100080d0b0700e0007a5091007001c4002c200d07005165050107800e06500401e81d5071250440301c0c0c3c04107103680d404111034108581954010055641c1c85c460500405a002881e40c90f1284404000804030018614018a08192001c460141c9801c0510049d00c03d81c4c1000000350b004000c0c10503119108041c4140420810000b466440c40800034003401caa0012440c03100241c56018500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 899615431 1250 899614181 899614193
    0x30c130e2a03070e0307090e0a030905090609060402030703061208041d0712090204090b15030f0706021509011808030402010f110303040609110303040f051801030b0112050a0b01080604 81
    0x810020000101c00c450140681426121880000d101c40180030601c4010002514200b10010140050318800c006886c02d040e421035880c82100011000248002030219180c24003a0009008420181182c425600c07000104406500020101e00406682d644005080340300306d2451003030580160641699282031840c80c0e9403101e00715090392044a101700512401c44e601c105e0564007401c942400241c101d01602c0000c000d00803a40d03024250301010000e002d04520001c4181c06540802c40865006404004000b0f44a1040d80300d01009030b0014003800a515501350f0b80580c2c01000e8500009545401c1800c4924030400d00705e09585040c1d0100c00c00045580207030b9014540072242c10000c0c15004808401c035540c4c07100410080101d512a03600100308010f105034402c00842c01400d50361502d031a41090019620b040c0f003440c0c413640585503603555003050507985505076600303d00c0b000750300d070708281c1078036500c094140c022550751040c0394a04020580255659001c0c0070300744044d1005080a0903d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 899616681 1250 899615431 899615461
    0xc0d080f0702030903031903090f0311060601020118061d0a151505101d1c0302120901050403200a1d06031b0f012102031603060812030c130e 62
    0x14103652013002a092180e17000802c2d00c2c4402d90115036101c030042080b900301e0141c40740d500d0003414000740314404410582c020b2901c500b854445000c449803540c444c00120709866001d00001d00c1101c880316000007040310390b00f03d0303000700d9601440210700740040754290f850010b5004058650700c08000390004800c0c0c0e00c3c086c070007107254401c3c4102215414000001d00c41c03c8410001020b00600b0002c1200e040c5403850888021031000b86945441c0d0f44a001c0d40400041c0c11600310014001c000d041400302c0b6120054411461043e507030b460030301d030855032030324610b40c8034000030911070403400221001981e80e202c4c0d41d005040608120000c19900b901c0343e035000c55000c0c0200740f0035040900b4008141c0205500c2c1c02c041203048030859401000080161000d0516802507540c1c17a26060b9100002241900114051800500410f141001d000d03011000c561050160300701d581c1082c41c21441c10074600d4080c5410001e00915146003803c80643e1503500ba5107503021216000301c47c1d0411004c68015105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 899617931 1250 899616681 899616691
    0x90a0f0618021c09080306010c052e06060c1a0702032205040c08040f060f0209061204050d1103030106080a0b03160305070503030c030d0203040f080c0106030240020c0d080f 76
    0x24003d144d8665210606130000030521410403410313001c0801070040800c0321040350807501c6102c00c1000d07140d4240c400380c80e03003024007400741310f08000000422509c0380210781410342e000400d40b660310311034840140e120f070300140c8840301710711044c0800600c1e07011445007207100e94503007681c3c03991481c40e000030310003640e000000c82c10038001554200800300741140c5076201030a50110340041d8030060301c400900240510800190030600200d1003d00031782c052a01240074600603412034a04e0700d4607039801c85041c40c2001d20481250410300040040034020800507400078824400454282601c40c04645004001e0080d020340903401c500030014444148081800b4200a0380030b54074000c1203003203040d540e02c14900c078414441d41c0000003c0502260280c408041c0307a2141180e6074a80d604036215000c0d12480c00107911490811420b41c522111503000b10301d00d280c43d070041302841100d810b070480500802c0003840c5031a070380801c2600a01d000c107000d082c18000040c1c948150707034240220850f41060000304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 899619181 1250 899617931 899617987
    0x91314060604200f09061905091e010c02010c1b06020102071b05010f030e101109010e120c120a1410060506090d020112090c06030e15090a020910030c12030e0a05090a0f061802 77
    0xac0b005a940c7d070b011500d81b18050302030800f914400c600d442c12103456500d13110060007480700d540010400c0c681c190020b001c1c0b00d00810181070580c1125026400c11400d61042c203020030b4180c0d41c8540180d019401455251022105a0f19002c0f8161010f0b42950440d0001241e840e5000400744110368012501f80d8030580181c4484284d40b00207054699030704a980d088500c201c044c03200c04014988200413070b034001d90744044102c900000c600003035580c0f40c00f12444004028100341020070142018030a8802e0390740001d056075800c000035001914284c1182c81c0c0c41640c583c41d8607000d000700f901400703100b00900c2140c0c1e0004070205814049410440c02061790482565004240851610005150040701e40c0440d059012902c0c0c0c0804d1000c500820b51008207481040f50300091480005144804824069103800e4a10700c0f0300c40c00c0004da07200c50b018041d440300000c0b010a042c8039442e41700d510704181d84400003484a803240d0a40940e907846075510010035800040c20801031050120700d40003c06900 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 899620431 1250 899619181 899619229
    0xf061709071a0c0f03070605040b070e09010905060f1504050117040c050111150a050106111606080a0914030a17040f02091314060604200f0906190509 66
    0x440c04003082c0e807000021000508000ca15000e80c48000e2001030b10f002c00d48012241d840d0b00d90710704400a80350882c0c0613584880c1c6000015101805003842410f1307481e0040c1000026800c0041c00002804060070903034010580008034482d40e00c40092803901d5000c03164480c0e440b40c1c688800100420810050108580d0030b07902484009401c1d80b05060a4803c24288190100c10a54031913183c9520051072801c1045180107100e0b001d4455488281624100d0342c4807403d20f01c1c842d01448d910b840c80101d06074120f244030303410800141b1038049070344c002c24000380c08600a040c0d51600c0340b4071700b4182c844403801e41000820b0004140c001e00d4480b5050140304081440380340607192601c4031000e1b4030000e40100ca506d030001d400001000101044203500c9000c10810483c026844c55507a90111000d600030b80c038080321140f180c400d040082c1ca0640103007800b0b61601c0700e0485c2640c801e810191007513400602c02c1c81441e50340c0502c0812004280500c0e69456202c0307020701c00b0003039510648803c0c84c01d030103009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 899621681 1250 899620431 899620439
    0x21b0d031418061204030e0603150915041416110d03020708070b01091b110c010e0a2105070603020a08040b0402030703080c0313082b0203040f06170907 67
    0x806103050504052201103a01c90210b021120056424940b60561081d0001a41c4008041c500740781c82c080d60003035036540b002a00e64030074401e86c1e100c15111521009003104016003503161040c1203580c06150015400444d50040700400c09590030000c1c01c0840300503643c10042c2420340b41d8040d0192130401e10301054282421a45142c070748861800d032230f04150f0000f40100500900d1021160040c0c1e0102034a24550f82d01c602c2580180080d44541c000c420030300501100c024480c2c8418503480c500d21019140300d01c0d82c2030041d102d0302540383c0510b070003002602d000240a00c24045180ca03801914070b210700d6101c1c00c1d203846801c10400ea04076000b41881404400e00b150743c090084c55026501400c1d81400b6112400040c1c07506526910090464100040c0307240359a2011028000f0b080d002e031036511060f602e582119407a50055400040160b400708440703150a0881c0015889440b03d90054038942074642035440340c0c80e00e158000300085000241e5450081010b408a40c0d0b0080445003c2c2c00d4003818 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 899622931 1250 899621681 899621687
    0x4020c0709181b0f0b221403010513020306180a080a020a0c062613051c09171213080d02070e0a0b240904020403230d020c0d06090210021b0d03 63
    0x540c0aa100c2c07440c0d02081c170f42d0340110341a41440807a46003e404807031b1a039a6104507840204111061030003942802e011464107a030301921409019801005044155242110b00c4400761580c03412400343c2c4211950034000c200c98500800b124242c940c0945010305050900c100680361540c481010070548200355015648994000480310801c00060341c000d85841d000c040346030020001c007906038052001b0000802617818003030040400691900e26506036a4155880f01d074225070b6540700f4135009070542881c8111490000c00740702e007040c006038001c15250641140f030444010303400000351784101c005000b006222820558055240902072005054520114108110080d8001501c3c1e810401007401e00c002c3c1e205480e86098094411500c8980d0703803c00c041942d03035140c1409080c90b003200d1052541071b03000c10481c0421450350000c005500c5160144030744024140d070195042c5945000303210041e03861801103105135000d6402807084e150050b000e1040a00825042840740d0445140100040d030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 899624181 1250 899622931 899622959
    0x5010c0b01090525020c01020f01020a27081519050702150601050c010c210c0504031b0f09020a1e020d1d10110f0a020603040204020c0709181b 63
    0x11034010200fa036454600404100300001c42122404100002070980d0301a030002d4045d444100c01d03070803100b20075406100d9500300d204811485c00001e54555285402d04031602d9641c8203890101400e0b2015a83c55024900700f0800c3c50000d071b40031034140300f80090203141d650408803081103105c003000300b410b1200011356288168108084941098800904581e0003101541e140300600c0d00240301169885000400b001004202640b04240c103654500b0403070018868003612034040e440c2d80345090f081d030301d07007854020200d03455245000d551100819484100c222510081000040250f2071b0342181101a01060003201102d01d0040e82c1da0010034115400117078100c0000f501c2c18080c1c0346c0031114000c00d5046645540c4242c000050343c80364105190f00035000c49405d41000d02f60341005050390615500d42107440800f942c0071100703201040140c6880e07070041c191000350b1070845000e00d558103040401d079440c201d0240c808140442d004400e00509000c20380c0c0740401c07054001724090030071008401c022 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 899625431 1250 899624181 899624189
    0x3060b160f0203030301290a05031b0403060c08010501031a030715020a0501050403090816150e01180f0f0e010b3118060533040b1204030905010c0b01 66
    0x3465450349014010701c60340e1598055000780c1030700d40d25a1200f0072062040402d440b1340021b03610380580b10781c41d6425441596034071000d51740c41610395111240c48910b4158280c0e00c00001c020f0402000000607040d1082c060001c0301506d07030908031341c0340800160840d500c0030703005030f540300a8620000306550301262080c25a40b409103080c6601e05031b500d0407490040d030709000402642c0b03070800b80f0081c9a0005808c030300310389440c0115031f95004030600c0d01003501542c1c0b040b08a83c41c624040c000f40c00d40200242c403c0c51b0b4040c174190206524810300c0d1240010ba0380e0014160807600d60040c4002c4201a151b80c3c00741150310b485c0e1504d545400061000f03485028403071200c0388022206c0030104000010581c40400104410002d019183c50200b20f4402078105c20007800d914040380000c082c01d043c0165200100c1c0b258107901d088001c84454880254480c0d24108465020003010401049250142000f20011100c0c3d604600c0c2c0742c42c4c0038106160301c1e007015040c0110345081c00006030610859906503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 899626681 1250 899625431 899625457
    0x415050103050705070218060f03030a0e0607080c0d0e010e01020102040506120406060b0c010c0e040e030702010f0201020f0409021c0501260a0803040b25121505030a0b07020d03060b 80
    0x582e03e03c04110380e41e0041e100020b504c0b9006980d001400b03d4002d00c460b00601003200c207a11464591001c0642d01e12034248044041404400303010008d01c1d09401401005025070040c031b02d0500d40114003401e102081301c4140226102d11900110b55038401121414a0000c1c0000c42c036045c20100080c1c82d5005010380840340f0f0840b0800141045110b410803002010608822620b0b41e50041c0c126000c1c05440a11100045519005001d580303018040c110300040c0d480e000e1441c0890607001151001202c1741480c00307543d000c00255a021603c03070010700080002000c0180c0780c1015a0b0081c20b12516604070703085140c01c100c0140300302c00c030b55202e10460141403080d00000c200030f401d47c3c0e414804035000181c0316050110810050052940e881031003036a02d201e007000400a100e800300240e40340c50308210000b551032002a0404c04c0740340d02c03402800c01203002d072644460352100080e19084c480c00b000c42e030312802e81007440112901080104690300300346c00c1c203021142c241045c112550042c0d500c00c001d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 899627931 1250 899626681 899626691
    0x4051017070b0307211109100315080c011202090303040605181905030c01171f0e04060219050405010e01030504061503060218120733120b0415050103 66
    0xd2a0020808003005120003070800ea224504150080c200b0042d03000c11107420304d03459684003602111071041c10f031203040c1c003004941400c0c000c5050016403e0320580000525076269500140110250803901c0248540c40081181e0141d034000145080342740c16100c0c003068014011080180da001c01500c6c04e03250303035140c006c0c1c1f14082600460b00703150342d042d501d6400c001c200c5005e6101c8180341e50000140d030001c0d070440e44581c035104011108207000600724210a01148017083c00040324444a448000e25000a070700c0c0d5946412403c0d1400800703950840e6029800158140c002c20a2040b0994080c41c07401c0c024101464500042d0103001c18004060415546038006000c110150b88100700c481144201c3c3c90903640c480c913007a8021762280b03843c8100a8846a024021440c1002c1c10441c691b00100180924501d0303c1c0c1c664024004180c0008410580289004c641803410717007000c181d03604940d03034110703c40c2c0d00d010704182282c1d4648070040c000c81c208400c1000c2c80503104000b10882e032080c0b8001071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 899629181 1250 899627931 899627969
    0x150903021c02031606020c0a061b022412070305010f06020c21030c0c1c2604031b05190617070e0d06091a0405062e06031406040510 58
    0x41810103003820b01064a13550800820780c0396000503500c42c42e000c2a101d60340d00503102c06058801d9940103055109038400c0502540040c00d202441c0882101c00c1d043c60289002c3d44039184040b03070130070000040070700004c00420404c540c0c1400344500405100312044121400c0c550000e4480c4140034080b8022007280d031030342210840c0d00340c0300107625900c0381c196500c48800c070a20304d031102d50703030801c541c4105103005000781c0007060720740d10016040d440505e00004010030060b600c007016845100e00c10b00c880a100000100b0000941e2040c1600480c132421501400c007420001040011000c480351001080c81c28048030f60040500325105444c181e00c000e0f9036481107400c6a4144100c0d4103942c01a0f100b1407281c081140fa60441c10060740300d0f00c01c614440b200c640c4940e132800b004480c0030704190700200109001540100c56a041da02c50000c01d0501031000340d80c6120026002c0e40110000383d6507d20008154690400341500302c00704450a010034201524130866055045c052491501703c41804a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 899630431 1250 899629181 899629183
    0x1605061e0f0406051e01080604020108010e01260102090a0b07290402040905160b1b010905250b0f030405010c02011b030b01021f06150906090e0a0905010e07150903021c0203 76
    0x20610002d082485c0d0090368445100340d84851003900c080b400714040c80004200900c0c070b8000c807410f0fa0304880c04900d603034001150b140701c0340380d1010030105c107175500300042d044d11344500e1500005040c40d054095559031a03890701054141e5401c3c5410254800f4045034294044e046030301c10340098044802141e40d01c1c00341000c0f8286031104820b015280d046c0d917400104030325404041c0100742c1d4604030407070203000700d01a40740c2a1101d801006005411040803c49410000d440406410b07034100003640941c2e854040e4009154421011070080f22008001c00042020074003a85100030325034402806941c2d091103201d00f2082c07030141c103081410744400d00c24203a64401c0100001843d40318164003c001d0070031003903000401a0340582e810003060600401c0e8114040e07070031710301210110390b02e039074451389841440302001001400305100f00341c844461030042a0240900d00400c3c00c504085c0c07142c1481e01c1144442038000d9003840c8144418040c0410142c0d588103171840300328003013241c5040702c044d0381d100017 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 899631681 1250 899630431 899630461
    0x604150b0907022401140111151302040b0612010510170a090506010e0f1603091407080c0d0213020702060715242303031605061e0f040605 61
    0xd980040a4904228016900190080c2920541c80081510345a2115200c0400c2000d014400060b43d0301c52025034030394030512800c00700f540301400381d895000162076413032004501601d0758144a45501207001c06d42c13500c2e00c29102102000c8540500e4001d45c0003a010a5034814890b10340318030f070584c0300d804035140030380c81524600411501040b01403410300205401000504400c1d030701c910500d0008600d81384510002c1d800b80301d503080620455900c043e117210110040d01040f804054071400018005500b403000700000c0440000a8401d01d41081082480d089035144c54501c5569001010390140e1111407048003408100a00566030b80c0c202d0010540d135226880c070081082000e0100112095a01e511007400e030341ca000d44880702a400a072208240007034501a1540a000d030030b149075552400601c03c9440108080c0c1660708001c0c042d0038200004804401c203036401c0c1c2290341041546009240100103074080c0d4059010b41d0306000d4030401c5030440007040145419034500220744140100480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 899632931 1250 899631681 899631701
    0x1180e18100c0809010501060f0c120c0807150f0b010504030209060d14030a0e040506011209110301020a030e010b0a031a1012030c0201120605240c250902030405060415 74
    0x401d00c81d5080b0010020078040c0c04413864140c5502e0320b0000304503184a440c007040700e04100d98551003100c43e65211080003400b044110010300c4803864800000807001000741202c81d0207111013001c03407803102d0310b6030b0195141200c120911628180d1a00a16078001d0709850640350140c0b20000b580d5942c0d004501c6041c0300040180c1500d0010303446512050001006001c0e02030740d9610359041200010520069a805681c7d0310f0114840c1554010700c0c03030440e4800c820081c06401d4080700c5c4221040480d007264084236104000944404003c0d004500901482c1002d802c1502c07051601450740e150320100f01c080f2100f440e284414a808103644103426002c0101400740440040780d00e00c11464064a00b4a480d6070807030208080d068810966040b42c8501c2084501c0a81502c0c882c124483c620810440801c402c0d650b410401e10035004d28003802c12000700c2c00c01c0061420101c120321403000201028003a440340714010300400c02c0000095010031800c0d0050340c0b01c60b10041c1c0341016211080a0060700308 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 899634181 1250 899632931 899632963
    0xf130908041e050307080c09040204020703030b0d030809010b06030123010203071a010e010920032e06081014041a04021204030905120616020102070b011401180e18 72
    0x440e80c808482c1100c1200c11940d00b10101c42c6076650320a00242c60302e2025071142c0c0d005881c800000c016007003940091045034803070b14000548200140c001340200400110590002c0d60003401c11450074801d11031045400740844049042d0341c540b525410f00c209400589174040c0340b5080320941c142c2d00030000e42d95000d50100d0107440410700700d0be040f00202d0091141201013054007000041416240c0b15400c200608944c580d03410003900200d01400350700160a611901031b18148ae06046809098600075a07180784050340c00052030110f004010180152290014200040041180200c1c00c80e449055480c02da8011652900c0c107840b10614070640010513400500024020301542c00d8000700702e109500c00c0c1c5581c4010368550040c0070740e85042c6904180e46a1025021034401510607038885000310352031001620304586a550a100d002c03007a8044100100c01c0f030718560203581c00c403501c0c0080c40f85070713003e8101c03030f528042c0c02683c6001c001c1e241d40170500c3c5d007020540080c00d007840201503a0022203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 899635431 1250 899634181 899634209
    0x910020a050303160f0518041121040b010b031e04020d020628180b1c0c090602100216030f2706110a11011d0a0b0c06060f13090804 58
    0x1d080400c3e1303008120300030f0000343d800e00e0170407050760046043d0703080751781204030701900703407085d1000e0000414501401d4940c12001340600c3c170b2100321080300c0d081c169407441500c80f014180391030421002401031704403815558091041189440100904c00208401c04500300c01c00e48843c00401c0e00d0301119074010b9003101000443d0b404001c2107401150002030004e0000265140070501149c0225095100722913801001c84200181780c00003028181c0210485049102d40031400305020489d1540211800411642002049455018052020354940030442945040503201c0c0d040b544c1c24801030700070148090810200c041e944503031044d00d0f61207807046c03045858010f0201d003007081e1070075442180c1c0020314038420300c0c02010000c214070180990042601a004518a0054441d16002016144c0c850b03410101450281e581c49035144c0200500c840a0f5514960252582d04083c40280312900603010035120003441e44604142d0720004034070000c0018100d07443d1900c1199482254072000d04440d00d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 899636681 1250 899635431 899635441
    0x2a0d110a0c0201081b0f0d060504060611060708090705120f0a03091a1207052b02030612150a0c1701030503190807020601051c050313081204030203030910020a050303 73
    0x80030321000304070b000b6202d8a40d60341d00c1900100c0c520560500c2c4c0c41c20080b0612001c8000c1d461308000c2c003424841c060380030401d9034a800108088841c90fa04c50b100203044c0b80510784440c1400d002590b013104407490a05010301d04090340c66a05c503000c1c071031140170f040701914200d10a0741c284006441c40100e402541d01c685614100206070468901034070340900d111a8110880080d01021104400500d582c10006540c4002d001d46c2c1d980c1007181c2c003220006805200c46540b160402020510841c44400140c4a081100c180004250700310320139250b90b03004600c001e02d100030b1001542d5205000402c003103021201d140044072a181a0242074031040e41c8800048200400840501100307600b8071400d0220704018402201d9090b810382d00500940c00500060103613041c041030612428400405d1801c0700c6038195592441c662101d150320402450491081c80801d000703201c0010648183c080c034134206401d50300002e40341e2007680c954078840e0b0034980c10102080d000f40224204e140d084010740f5202e11301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 899637931 1250 899636681 899636687
    0x210906180f121504020a050603010b040e0711151909150b090709060f02031c050901110310090e100501150e15030601080424020706052a0d110a 63
    0x80d44068901c100c680000c07100107400e08494481e00840603000034a0000c52805200e42c499002810998204024210102d03450b22808000c5d402010819010356999140000080d140080035081408100d0040b003c054201c50002c0d600464601c140d40c01e1056403100240c1d10458080070444000850400308001c05100703880c4465241c0e240340340c00901840121b401001001c0c28200d50b58404254456000e2040130302c1090842115845801168903050742c60300d40b00040c2c1e601142d507010443c2c40303604000d0142001e000d12411943c0d030062050950411103404040094140207020400790780b80e5204002002c00c004100480e55000f80401003941c4484e0300040c2c900c0fa55075800d01140b4202c00c24112070600f18421895512002002425521140300444031500082c2058460b413030510505001d00044c2420400410b40034040140d40d441286440d03420751700000c00200b848001c01c1543c2c030a007600001c903c1c05680041103a00e030740d61080c0d900302c00107052131152444c160300003280d041c1c0c030950 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 899639181 1250 899637931 899637967
    0xf031d120a0801050a0e070f030905062518090209030304210b010b0a0914131113080105010f0b1605060a020702040f181407030b1e0117210906 63
    0x22940d0780d05000b036a29101441840c200301c2c8141d42c060701020000841d018866241006240924030b00130500d105561a00d030304c0d2941c00d680c9000d20b103101c103c8034030201182d650704c1c0e0786042590030074021400c441a14a04200305078400d801d501a00060680c0c10303550240115400743c4030004200d541d0141440340d4603c410703034101c01100e4802e5424004070301200d810080d0303289241c456442136211030500050600088040c20f81039081451101c10000e0b5820714000c082100040f24201a00c400080c0c020100401c0f07d580040e045914000c014480603885210142c140d5402450b0640d903100b82c524400c00641030048060554002c1900748403800035181c0080840c14003c8074280001c20745020b12400712b482403440c8003c0c24903429101c0c800110a5000801c80c0c448a8060701c0c1c1c1c555407900e0b074a00280c4212840210500103691b10f12040c08110312040c00750515440700d072001c25a611030b480d951841a464464181c03800441d00c2c3d0020100c0b01211850b00010300b02c5600d420b8400800c000b084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 899640287 1106 899639181 899639197
    0x19180216120809062a21101410020d0e2709060a0509060403081f18050106022413020405130606060207060f031d12 51
    0x41c1d41e806100e01001001d07102e0303070307124a007070b40d40c203420100e00a1000d64480318000303032145070301c5510140c0d61450b50360101d469541e50001e008182080c400070060500340480504024104290f01e42c8041120491b07003401c0e0003140244104140c0200256000d00164444070407090720920034543c1e104a800043c1001d110340c05421514800844945180245250300b1001e00c4903401c001c22285902c0b004428041269042100b12240c8400001c0c3c00a401c225585011036581c100065009001800001c190614190f4400286411150300140d00041e6461700b000040e0040c004580240240703564a40c000b172410b03400c190042d400402a00e080640c10208803280300580715481080d009500032603084112070b486240c00001e070b40301c6d600700c1421508180b170104a80c0c0d4100c040301d2250302450801203601d003030b2120880141d8100b80e440030241d20802c1c207182030b8124420000d201c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 899460431 899640287 := by
  have h0 := BRFrame.cov_init 899460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 899460431 ≤ n) (h2 : n < 899640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
