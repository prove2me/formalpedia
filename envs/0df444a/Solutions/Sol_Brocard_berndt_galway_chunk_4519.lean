-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4519
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:52:47.838383+00:00
-- url     : https://prove2.me/submissions/14fe9505-3478-4c8f-8817-67ff9a01c3aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 812589928 ≤ n < 812769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 812591178 1250 812589928 812589979
    0x1020a110f15010b13080d03091208010b030106080a3e0f040308032e05040605030607020a030f0509041802102105071e021510060e1513030308010302 66
    0x241c40041520fa400c00d00c148103150404070591301004000540440c08000800280d141103600d99070108030030205240045144c0702c215203ca061081c0a0011700a000c42340040ea41910000c0c500703014580d8405c6004d81c05007102d43c81031030304030180901c00c900030b00144452000500159208a000f00c442c40c80341040c5116040000d810080b05000c10300016503114010341d0407120003000e100501059001c100c05100501520308094040f040c0200902d080032700816004240c200c001c0c008920342504065101c40c0c007020000e007008a004841e01d521402181503442004003c0c3c4100407261078409454002050a04264400e88010340b00050840c4035000200d034010002804929036440c0140d03072009003074090710300b00611203080c19403200d0014030400d440c80049264000c00401c8000b4244419654018004c8900d0031640ca006100551b044040810010000d0b02c91400a010300740c2030135a68040c40e40142c0660109410010a01d41e20002d45816240211810031401425102c40c0e14030603103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 812592428 1250 812591178 812591203
    0x100f09170a081e0414030601060306060c32031b030f160312020313150c0c020f0d051507260103080a030e0f0102181002060115020a0501020a110f 64
    0x91440c0000070340702e00203084a8411400c091000c68684091020542c0154004140281d4903290024161900f00517060050070039080400006080800003020102e030302030081c128814a80c01c01102d030700e8080e200800c2401d0889000c00d40203464170170075160f0303015400300881c46d41003010680201c20f000c02111401d14800301010302e8034a20980d4441c40e0300c454042a814460fa14107100c80741015800210b209110680d0b0100c01d44032075140400c101851f501c1440990380c500307021240c0190304070340300190340342e01113540c641310320810400107043c042c00640003041405450049010452070b0100b2038000c7d0050740340c010031002506c1c1039640d5800003d10310720746d4040c440c0041002c01c0c4c0200040c141e01005180104011542e80c10041c0f4001c1c034994541500ea5001554120b5080140100c0c0c43c10902101c2901e80350700f820300002d54900060280300198809180380d1481c1600800c81801f9040d03004000b55100d0490324401381401e04001e080c40d141d402490408040038a011421444281 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 812593678 1250 812592428 812592433
    0x20a0e03070e010501051614070b09090a0603081605210304050609060c04061103070204090b06012a11130507171e07030f0f020708040311060f0a081302100f0917 71
    0x5400301c020303080d00031f0b000801d4403070320811000c65407410b90a0081001030703c2c11204182c0e076400705a05202410400520507021949080400d200146a0701e04564981c51460300b400003400b0325042440c1002041513081c440c50040f00130340c601d041040001365114034014000e48600f55500300c0c01780d8941c00101e45000c140f03801000140020360158222896040d6500100d03030410348140c1c0483e080356015201035400740d00110400c1484e40c0e01076880000d0002040c1c200210107280060a09604410b1000804c4000300142c00892510f600d8101c2c0400c003c40901880750341800070014000c4040030344404000440d0070002600f804180801c950b1100d002001d000c0150b0700d2240840042460030f1601d12032540b00c10104100d040640040d120903401812950f64a518502c0c0c40080c80070f858400b00d000c0c0c0d4040c4510464002140150781081301e85061101540d91200020b000c0c025081400039440b001f0b8008213030b0001e40c00022981c078404140c0307031005100e031110548070a07804907100340c107a136a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 812594928 1250 812593678 812593687
    0x1e0e13050a060518031b010f09080417010207020d140d031803110309061309051e0c0a09090c03050411030f0703030c050111040e1506071205160204020a0e03070e01050105 75
    0x15103903030003183e10410000861968200b8010901c1c2158884034585090358601403d20b81b00305401c1c804d240c168150450300700030b002d0b1103640f4103a05004070310940000c04828200c1d810503000c29011214250350083c00320b03c401040b0701c1d00071181070000c0101c08440c810982c2640320180644914048c1c1d1001d076130405020159339408a400461108039003255010903c6500d43c0b070b45408000c1c01d0101520802d100b00e890030022042c0445070001d2444401008442c4071240c030703d001802207900a105503540355521112075009407008141d41e48885400c0385072280880900c0d40c10703400140178901c41e41d035106d10908440d042558402c070f654981030807038101c0b480c1040080e00440c10005024801c0d8008910400070356130103404c641017a07014412803a1400b040100e29040100c00300040581103422a00740b545603210506207241ea560702c4800e0000006a41c483ca0782c88451004c00b19500410941d03807081044801083e07a00c180c1c0d1598000d01c500c0c00089a401c2450030902c3c1070720010b94a982c01c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 812596178 1250 812594928 812594933
    0x7150804020d0803100512072c011e050618030d030b2b02030303070e1005040305100f0f06030c060e0901030812040c0f3209060112061e0e13050a 64
    0x65440540b1701ca08980c00c4060001e2503444051f400510804448080c1c400a40303482c5800e02034100a410001000000341e4000f80340c0a9031110990540320a4211694800140e001c07804100340250420b50f4071100100340454050070032815580032410603815101c004801d482e003607040c2c0f0200e10900b40d10078100a99400d0781000640d50744914001640100d1903140680c000c02d086902c1a11a00300250340d02c1c210a056080c0070484121030841d900e170091a081c9075072a00d03603c500c50042403d810b00d0b25048000802e071069040003088468200d030411006c0c0e501d2811407158003042c4580c101051440038040d00318031300040e00c28101d0740c2100d006464940c040090b41880c1c10010030840d08036025140120ba11b0802251680103410010400004c0d40030340d440c0c044000c1580014049144800103400c041502d844140f02d1700030400f0308047d03610841c100c0c200c5000d044e81d9042508404440c0c407008100c0d00202e2061000c0740d003031021840b00d0f0380710f28074581e803900356540010340164001041e6000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 812597428 1250 812596178 812596193
    0x1090501051606090f0c1a070609021512060a0b040e012d030609021302160b0c1b060105040e0309011403090313151119170c07060207150804020d 64
    0x100101805070b1110820709648070720803034681c2c8000b5903055603402c1050040100c4400003e02800100d041628648a0f41030b00315002e01c81e00c4402046683c96404140c119100d02407650158421410390f1a100c1107841b010300711107503044440c184502460240010151020021075040d83c40c58880389100b40c2c01c1c03174541c0303407400d8120885959102c04c802d8616010b00003d007658006d03510401c0085040c003244c0c01005101504103180d248440e204104400ca40c10384609402070017a0711010103030181d651558808403c2c0608040400401000708481598040204506050b02d2040b2800c0101e08002e828103641ca00031200300902041030f001c0b0080c0b4a144600140d64800440303402c0728901410004840c031030381c00a500001010900c6503644403582d4200258051541d00074005101014080c20001d00c100d02e91000944500301ca000d072a00c420861030f04903002c0100000c116200d49540d002d000b0768920ac90b126840000c040f41003413448031031140d8629802140c005050f60701141d42a00d450340c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 812598678 1250 812597428 812597437
    0xc03070818071e0305010212010e150a150e0301020a0903050f01050c03070809030c0307060b131506120e07170708010213090b1c0c151110090c080303010801051b090109050105 77
    0x82d0410703143c1800800614240010705c034140407240d6406842d45041c2000780004005400051045280300100040d500d0710541c91040300c3c000f17940101100003600054030700803040c40f1107540550000420b400180e800a805200f00c0384543d0449403441c030100011400c0319000d5a540e14a202c0410100300308a00c0b40e004150050301c800f05992404504007101440c0d948070300d8013114090788417540700000e071600c00c643c4100502910414040100f10020fa200541560302036035062000f04446811214144e03480b1041004415003110601c0751904901024842d481c9580c0c01d0a01c5100ba01041d40e66060099030103034200110342a03030382805d1104c0c200107014440d02c1943c000c0c003a00c0312070301031001c0c01e42e4000d12140a1264000000d041021820102d01005104014054802001d10340c00b140050042154a82e08600150b81d0502e450100144041035000c00141d22000c80046190321040d84080c2c000c0710034048040c0038040e080c044047c14000c6c1200c10780420344100c03080216500500040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 812599928 1250 812598678 812598719
    0x618010e01060f141e0c03031905070c0c41120a030c0308060d06020a0c110303090117150907020606180f19181a060409021c0204060e0c0307081807 65
    0x150300340b1b02150000c5e40786400c21034660b00c101300e5560820042c3c07560f51043c181c0040103890641d038540392a84900848191a2041d80c01e02a00480f00540340381d5100341070608000da640495044e0038100f40c1c1d40c40c01c0030984640a00c50b000d003151005080800152002ea81039154644130346502041c0c0f8181c0705000003c11158114502e103030404006001c40c401410813080507214025000080e080028105200c0d41a29019a200708102d612076a084048910281d11820b59a2082d031350790000610703804030b240c02c0e083c1c000d0206810321072070b42c0d00400c031544905020b4031900d00c400715a11080c45a0081540c1c401c0420740d0300300c041440e0201140d40f08280c07000300c00020507503a4008a5686504a905100351540401c184004120040513181e10b5002401294140848030b15600007865200e060302c6621140203030060302004540312a0440d40040c0b8240e603104d560740c0703420952041d40e81d001300e0380c00000410400002d014076489400045441040303038020012035007004140b00300c42100c130004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 812601178 1250 812599928 812599987
    0x13140a141603050403140d090b180c061c09030c1e02060406031a0312040e010b1e160b0c0d18051902041e1b0221030618010e01060f14 59
    0x350800d0b01300500107000c00c2d47c4401000900c548982070103804083d01601c0d030003070f040302c0300074030116280b00103040814044100d0b00190740c1c210b941c80380076290411041d00c0c40c81d5400c00144101f07040d001911444218041d4800c0f20429169125250441c42c4a06009600000600007407090310700c41e40c8906440c04c08501c8150805140000203458690071004040803013400082c1030150310317500f210090040445104607810669513504d1040c50780e1110f04110480c46000c0341c00404040c0300345109800940040d400b41c41d50a01d1001107000d40c2c811064000100e00b051901d4107445409031092038503d0f005001340081007500001c15a421440c1202a83e1180e02ea0040003024030301d0340001140e2520708140040c002c6207680181c803840a101151f482075400c0408d402c00c2040362220344200c0d0304040040c040d0784c0e5840c040060b607080c0000740502d071551718250001c90400c0806c00724505032200c50b114040d200e031035414100c5802035040b5080200c4074040c070059862080e0354003d4800050113019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 812602428 1250 812601178 812601197
    0xf06080708150411030105040c082a19090609140d03120b060d0c0206091f05040305270a270f0608150a1d060f0613140a141603050403 59
    0x28140c1c2c401c090300c00701c0c104c00080100490b00d0203102e4a01c41813002d0521803070f280361001c0030440c400303001107030079408003a1844180000c884070b00458000e551060060311010382c981000515000e498054040800c0c09600041082c060031050120040383c003c2000c0062580c0e0351702240c00c00d0003083c1030381155440305c451007070781c2d5a44c0018004c0441c203810009555102c0702e500a01c2d00c240a004d01a05400031407100c0310500192030002083d0703102c0d4001041680720361804940602c00e0389d05015500310401801502ca01c419082c0c00c004900486103007803103645407110100752030040c040c03114074511910201038454266420004c414481d03203600180a070b80d039040082c1450170118845541002c85d508001c1095810710986500d06219402804403c61000c529641d405c3c029180d22554030f1034000040380c540d03c1c0408000100d81d5070760b00340b200b241c1240c001c00d6020340544800048600300201303036185001301c54032944181488a4640b03c100c0c240b6105400901002d07000750100250f02c103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 812603678 1250 812602428 812602471
    0x20a170d030f060b0432011e090f0e040c0b0313151418010c080c030411030a230616020a080307090e010b0702040e0c030c101b14070f06080708 63
    0x700030f040100403510b0080e0b03074095082045084011b2060401ca24040550f4141305a079a000c0ca1201d050030038030b4824181501e044100f40c802444a81c00907204101c6501c002c02d5460744510030074002c5100741814403140b0b444180750201400101d864012491a03640d40c08041f40400703980001080061000140b02070790b01d0041c500282c0200c904010407583c035030100c1e0ba1203000344510100400c80745046001820903c01113030b4030f4400a04086d04002c26000e44c40f540341ea05000501c0410307440540d804070001c1c5c105403c0b0075a9203e0158100c0c600a801c005100d685141e642c0d4400007038564040c0007826041e0f92801c0c111b0708043d200c5410010030000c046103c904042040b03010b084401c624581701c04091040105403000c64820b85940d40002007030804a403400074948500702c1d0101c0790f0340c942c52070281e0100c40242c0c4407010881202c044144240070b003c1d07100d03940e2508442c4282618520b94441e4070402c141c840500c18040098000d00c00141850301c6000ca41f078002400c03110240c910314090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 812604928 1250 812603678 812603699
    0x4020f030c09011407030c03110f06042901030f0803070219050115091e110c030d1a12030703030506010522051c0b060f0612090703020a170d030f06 65
    0x21a00c1601001c0000341c540100d60300b02d6524030000c007031074001e40d180603001c0e9401403103e0b4141d0b00c014284903500d0845000c2010031b1120504a864100489546140034104035070700307001d0480d4400040c09007c040c100d0081c2c4515911341a00d40207241001910442d60700c41a00d507000802410850094403082408480c144058048031070240001103400344a24012043c84070a41e80054021780ca08003c84072a0a41d0001d200e4125102810006100e4103580c00161144920140040a4040054540424041c80d0320031641c40c0640020300700602c0f070751000d02030510141025801a80e200344031101c0041d1107500b20582c8518103140040c02c122416502d4600c40c58919001e200740b80c03081d94180000d050100103508030502c4a030b81000613504030707203c00303583d800b020f4092801180041814055074075144121011b50101078000b0000c0c0c039101c0e14554460041e400100d205050740c0c4000540440e0000b41e2001d12025040a0100c003c3c10600036801440448400c0b00c109444680018105004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 812606178 1250 812604928 812604931
    0xb03010e10030c0609092d090203193c06090606030c0801140c130501030f060b070b041403090a12020d0c06110609210711060a1106160e0f04020f03 65
    0x26516000c0029050101b0f56040e5400442104840c408650090241199420b440710f440030649400042d00000e5001081c1000d42100400f920121910080320421030641c10400f412007400c070201d025018000795411101c03040360501d6192000030700f91800811140c3c0d0221200358458a000a032643e41c0f42d5441080b158658020a0241d540d0f5280c4040030002011055210060030452442e11000409a0701c0d59540d500640d410107595100f074a0071010b0b8ae50001c2c010b0050303801e0003601c5896500c0c3c08444040e003150101d824000d542003221907104008191050b191000744495022800d040010b5800760081070140d900800e5070700d168012030342c00c850358000342c152aa41c10f622104410706182ca042c50150804149a1001d04c61003044509444101c0d4480750170f5a17040d65809207820a10900600d2800c01c40c1d01c0b0200090040b4916001a200f01c8040c2c09003091321026a1141c0340b200030b0040c0001c65501258621001070701518000543d5900010010001414241201c039111000d400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 812607428 1250 812606178 812606189
    0x3051c0501060f02010b010905150d020409050103060209011d1c060f0509060a0b0105040f03141011030a0507050c12162001020601080607141e2a070b03010e10030c 72
    0x50407603c0310001513085c082c02c0c0c81c078070084c204402264a04404a121140540e00c1c040317083c003021030074450013078054040b50300420a4400c14400c03541c6034207040b0002d500c03c50030355001c01c00710309007514440c1d010348900c11412001010511101d2034001003240441d21007200715607440d41c03058030001281d5148111400781100000030103883c039006080da411100d20f080c2032810712505000401c0075100401e0b144007a29445810641070140c150107161500080640000e03003203090008500100800700c01452060b85108418400c9807601034060384d4034403a800c0c10786510f0300580003c426199420f0000d042d0000c412035041050200e54544103240e444003140e884c0b0050980802c0400ba40e8100f00c01409040c49001400301800d0120014002945d4170700018880d400201e032111180c50030398280300c20701102e101080e58072900482540c400103141081c460610010181d007181d00b036800900801917a0f4048032051440e4281032443c508910000c02e000c0c11703c0b6a0b02400310011383c1c800a504001d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 812608678 1250 812607428 812607437
    0xc0203100b040b010c0503030604090f0b01030602120a05040807110120010f0531110a0602030a02100204060c0314040512100c0c2a08010e0a1406060a0303051c050106 73
    0x840c40301c20003040d0752002c16554104003203505a0f4010450100c02c0b260002c4040320005202c04540c545501c400648070805000c1480882c000012701c083c23500107242184440e6280c03182c030341d15508408111f0b80c0076200901402814440b6400040c8031344810681440c0504002d5080700c4000c1c01d860045580038004416a51075130340d4584024010700400d074003c0760052402140d1224007010810310312003a041d6091080c0241304500a1081740c0c521884036040207807011200d20303101d01000c1d550364002d0380f101005102d40d110650703c15a441c0309841c01d84845c0d0b40c4954162403203440451743c24283c4107010b81c02100401c0300182d2940e03840495481058108050320110700d00d41c1d5018121641410000d0a02216451200005452856100c041d200c03040340d080c041461a10055208141504030000c90b62074040781002c1f000e80011030003202c502c070f0250300c0030440420841507114070042e1449904080f03486000e00002c1e0007003001d482d00d1046041240c2c0c050700c28024070740585000707034030030800b04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 812609928 1250 812608678 812608691
    0x2100924030e030901140304080909040819020a05060c0903100207050105040b0a0608120703020a022d03160e0c0c060424050906010612021b1c0f0804060b010c020310 73
    0xa40d054052200c5120458026609026544d00042c08454400c1107010400c10700000090421001c5800d80300440c00103001e4908514051500511070391040075060915100800a064024400110350103402d0b4404040c03c02d94561004a002c642c2001c00104d40c1030041c0308074207130a03860ba07201600e00c00740150000b09071420300b0300706810040c00103040440c3d46410b04606201d5014000380c030400c4450202880ca65401d02170504070700b0042c4c0d440d0029805011100c114048081e02d890300111005200040c0c00d03a42e007814201135540e00c3e0070121241c0074964900400090000c6000b113980304103184011880d0990509456041a030304460449030003c40c9844e8040760a204401c0442500c0e55660412482c1800c0d00181d655030301c14440c4000700706840121a10a1003e6019641c00d18403403841e034801090b01c00d503050f0300c0300703a80040f81d214020403d044c8c018a41c0310341c01d0041c84054580710f640061b02c0326219800a0301900098138180b02e44c5d940f4082c016141048081d02d003440080700000ca8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 812611178 1250 812609928 812609999
    0x120a1b0c081b0f1b060301080714040b1801080c04020a09090b15071202070501030e031905041805060418120516170306120c0a26011b0206160804021009 67
    0x96100031404d40602c805000611a40e10700090500907506641060b070400360340c840018000d400003402540d0811800b55505658580040301241039407902d406032001c00301c117001440224001e00d25002d00251030300780e081050843c0c5134407402c005100a03100c04856072003040d1440c2aa0b2010408072446400c007161250055810700c41c0d04050407003403a060114060219400359a40540d9a00401d08000c08244482e00d60003242120010280540c003101407502c0348480c0301c02068211040c50040342420074580381c1c0c1128540c50301c4000e03032104400120410760802100e0702c3c0c010000c0144003541c0525100007040d83c00304281da190050110740340c3d0b43e02d80038041c80080384802c000d420321503010075400100b07640c0e182c0341c1000741c2c2c80d0703901c825003248040c0d0703030f440c040d55000c4030060b035194a0b000c81d01402c90484544100d801050390215003030f903122058401c180307440100000d0000340545000c1401407800c641c00c528198510724003030840d15255a92618481c0b1a00382e003195107216001e00501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 812612428 1250 812611178 812611213
    0x2010605010813080306010903020a080c040f05060315040305090603011401020d03050408091002070b04140a0f0f0614070210091701140601030209060c03120a1b0c081b0f 75
    0x3820003803a050545092088905030755001001e00282403160100008040b40d01c154840002581c009000c003800d1070b13554482c2e58a501d561300c6500d00980c201244000f003400d0314003445004000c060300034060400d2240080c0c10919001c0c104034204001041504ca4503615030010714040c041c40c09201c19080d0f4160700182ca041c6500c0d02210a06041500700700c00314401d1001c0d51007841003510882c6a03091030aa041341801c6003600070030103012000c07801040b00b218095803206640415515041c80d19200c0309035a920149030b100c1c42c56034411000c810300100d032142c2190881241c074103400d142001c1c03690b0f001030101d0760240300c0c0c1000a124100104043c0ba451f405480c1702040d13400007040102e04864420400d104001e0900341890b1300082e031180c4a40b80c5104036000c2d80602c1080d2503c400d001c0381c01100c550803da5040564500781082d1400000041c2400d501445a54880c005225921350f20028150043c1d036980d84140640d205158104800740101e51500c02404041c140b5072494042a88 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 812613678 1250 812612428 812612441
    0x3060b0a0611070e0c0d02190207050613060c060902041b08060d0201080c03040201020f060f100506092110110d1812082203120c0e060d0905210a0201 66
    0x104006040408024103a00403400300203594004000400c25552584082854406c0c0100c1103040351000500000141d200d424840311200c05500351140143d030b443c2000301d9030107118050754445100440801500e40a10f05603206140724000c04107041006800080841d60b0140c105040710000001c03d4015691215000b03510080450704800044226000200f0244004058401005000000c0740c29a80200850b818584101048510616101c10000d4840300d0a0300c56001d81081c91502040524140060b250140e0019000c083d82104600e00c0c4c101c031004848908038140510961041c02c4145030064528900000c02501c1c0d90300042c2c8070307480171521594580101212080c00c03201c00200c41c0d0503d0940140149080d00e59900c40403a2402c40f521035480442445540302c103144101904440c1c03c104a00c020078040040e124064810b84940315588c04099102d88104900d02c407582a5a011030302450264040790081451962020b00a0918a89c861016000464880202c560900804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 812614928 1250 812613678 812613689
    0x15051c0f0b01090515090603090a050d0c1401021c0504020d200a0807060c020105030703020c07120201170f0c0a0c0204020f03100b040806060d1e0629030304030308070c0c03060b0a 79
    0x403400051240014140c500030b001446d4402e00d000404290a1102080203052140e0041c0c04e856030b044500c0c1c1e001c0c000e480c0d0414215030340c10041450030100c4a06100b913660310340a842e09500f00710500f0b50084020131303009004a0703000480318041c1c0302240455684000b03800c0d10003100315441a1410811178040700aa1006000d03501c42c00003482401d40c00a0007030702480c0e080c24400e44a445208040d13029005160415480d840350600c0095074a44c5490800d5035603000380c0350401e40002041d8044605c0004458803100d500b010804516030b804114020060101180780c4846150055800942a64007040352a140c905000c002d0140700790850040030b005020320b6401c01e1400780340450703a94603038900500c80ca1203a03100e138160500f449a5031083c01ca4082a0702d11a8400124034a4244010281101c080d50001a1406440c5040644895010520380010010b40c20207185903801c64480034010320003403c2200600074000058500310b0100301640c0311380c40200300d00c810300c1e041c02000112580003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 812616178 1250 812614928 812614939
    0x10c020303071814091b0c0c0907022b020717241608060f0402120f06040903020c0405042117060a21081e030604060503030415051c0f0b010905 63
    0x300104004e6400d008203501042c0c80b01c0e0ba00d40e4440800007901141c2c14035000200c0d000086c1140c60f09404146807070a04c1c0c1c100c03072001468898203000ca070b569400c22080c5158112454812360900c9009500c2c1c1c405030791a104583d98240c0b980080c2d40b504414091501165201902c44045560940d43c44803070240c3c950010720952402c08030b245200001a010502440043c001084d0103840da04403030040c81a0150040d5520b01c01d01c0c0001440c0c481c101c0f142000340101c080403442600d03281c081c0d4003c03030303400d0342c020201061008100802844081c20441d40d1200214241001450034400711082c8080758070740c0090040482c5105030540b40060126205030010142403010b61030048641903a1490a0403400851382c092400300d1580c4070707020000e1280e407102d40485d268983d010004510818003076400f4080c0582c0c0308189580e0f0300450142d0307070401c4030764076006030058401c01c040c25400700e408a0900d40540c0341000e04c4200c80e114601d49070419121140e0220a58100854600802d0103860 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 812617428 1250 812616178 812616227
    0x140901120b010b16141b09150f0d0c0b0408070f0b03190e03030118271203110f0301090e0a03020d030c02150901090309082418010c02030307 62
    0x1034411101005000d01065008082209840c80c0d40e1600070b450b00c2c507030003140c00c9059610b54403440e541d4440351492204005c81d9054555041c1817a0300407078008d401c0d1601d07020103100c600d42001820751541c0302c90342e040f1103d00f94606c081011481c40000900305030741060b5035141000d9050303081484541111089404040040200c68402c0303003120342c00700c0084540008682d013a160900a0105500c0c0f2080c0b40c440800003107031684002d1156903610103a000704010400c07905681c842c907601020012428002d1086400003c80c90341c4080c0c4401c08164900091440c61084903d041d980240c0c410b02000c1402000501a9600b18810340c80181c401c00c00a03d0342d2100c03694001e6071a81100320070000c050f00d4183c6079007054020812240015240c040d021103a1818003807450003821240c505900040220f4400500c2e5003010441c481040000c08410300100d4aa000e250345484028000c0006144400d80c802d403424000c0c0724030701400d94164051996410240002403544100c5404050008070420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 812618678 1250 812617428 812617433
    0x60311031203251214010501090602060912071e060209090609100b250f0c1d010b1b0a061a10021b0613080a02031203090c0904020f0a14090112 63
    0x1100074620303d091104154403c80301110880f010715038200d04244403401d000c4e640012503400030303c0c141650300c00e0381c1e00406240e4a15089036501c009407000d00064100318041c114a01c4004002c0034150301910031209401203106004081e0b903141c14042d940903070b000c180394a0501c1c001202c0360308400100c407103186a06112a100039864501d1240d0200030100107240d80c1009070003140202c0e8803055000c09800d132621810880344402c100e642c115458141c0440120300c81d413040000c41d4203950640c00303502440e07082c040700c401030b030f4045811003d0f480d50318000f00c0040b007070801050300840c0c46a5404540c121003038500c0c01384100c01c450a188181c88801070002c1841e40003424080c1c0c41c038a064403e00e03102504010400620490450030b440304c001c1a00450b482d40c00050002502d8030a604885070400e15101024072400305881700c050642181804140c1403910170000c40d00a0300007440c0041c41c1c50480c000545172211a40115102455130323481400924020440f140180859070a400c480085903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 812619928 1250 812618678 812618701
    0x206192615040e150604050901020408031c02040f090e010c0813031b02030a0f031d0a030f0516090b12010b0f1e0405041a1006141c060311031203 64
    0x81000120030391064607442641e490b600006003094011055a26001d081245120320041c00c44180b406582440042080124140700f103a0449a120317014509040112078001c16001d04c0141070700401e5020302010500440031251000100701d001d40008030344681019950070754101e1a10300080c040d03175a042045c00e20503042c0c0d00c800790740e0503c1c0100142010403145103405500e03000283d0544200c20512040082111000d0091030003525410043c0d4000c0c0d0041c0852182c1c0c01c4a0394009a20340000c02c0055915103000c2d6506101301c082d01c02c0f0b850301d07003010414031078280d0100c03da41c0d0315000d519406091040001982e00d0707500d002400504003c9000c02c1c85007490f5042c4a0254500740000c0b20030300c8038500c071040014402042803102d42418100100042280b036054501000481e0120701c0c8031040215040445826444aa007a440b4001e5041050b4020450031002601c5168060300c0c1c0e4030080c400c2c04040d5100b60ba47c101c1100142d8181840c0051a0002c014801800c00a1200f14042d0713 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 812621178 1250 812619928 812619931
    0x90308070c020604030606300203070611100504030e1509240c0a1b0e09060a020310080313060905150322050f071403011a040906060302061926 63
    0x16410800307141c404a10100380184103950001d0140c618081c00840c1320301c80401081e0204208140c810315400d8621007103904c00c1c0b00140020340c1a80564000c0240e280a81314031800d011312241510203402040740d5076015980100c60880000c2c100b102040135529044240c3c0301c40f2a8030008680c1048941c001150000c0c86194402c285006001003507882c9c1c9443d40c0072a41e20510941c252010131410303142c01c840404440c1c00d6403842c2050117802094125801010503c250280c0b4000c11080d00e500b00030310020f62024164500019200c2c030040b0719130008000404070852411045101c2910300b01c802400c500013600824419107440e10a8491500114150380e0017240012201206140c1405610f9404924100060090007071a51030040d000e404142c04044502400120900203130f0717001003608072038520b1041100840f0765040b1001c14107156001c60003461040d10300142c2c1c6a03d0360009807440d04030300c0540c0761b08680000e00102042d4031070141803050784010408004140d9000e08005407440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 812622428 1250 812621178 812621191
    0x4080348061005031902030a08072607020105030a0c0e0a03050604060f020a051b03281e0c030320070813060e060406080703110c010b091003021c0c081009050c04090308 74
    0x10343e901742c19964140100101035500558541c3e441180b03103800d583d014070b00002d19400c4188421a40c040c40f2078a011540210b034143c0d2050324558666a8000c001d0100d207040004000c0c8203030200d03045480300d90204000e180030340010310091900e0b00d070407006d5814590800a0040c0140032903603869030440103544d0b010b03220012403150b000586010781d10b5070103028041d0000a0500e1041074800741c00c0b0003040b041035451380d90b03510141c1034400e0404109607802c9058000960140035000401d229500500c4c182e8001c00e60400d00c0800385000218640107a101992100000140d003100c14403180310103c000c000714245210b081d40301c280000c2d0980128810042031103130f00300c001215548641d015104902080507850b44489039904001d00130400403c2450082c00220042603036801200c10032400c0300d83c014001106096210240c20402c48800811036104516440120700c484007403204001001c411400007a8021050800c3c6d85841c060360002d9005130300d0040d48001280d4880d400541c0301a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 812623678 1250 812622428 812622463
    0x9090201090b1c1b1710090b040204080105071106090a050601060e01050c120c0705040509031b190b0f061f05030c130e0a0b060408034806100503 64
    0x180c01d500f03d160350050700e1a001140d203103000556110a0548610803030100500c0e036500400300040c0200c04c0f184d20094400d04003000260340100b00140d0070341c00c460140b0702d02800c05820300ba56901c4060035588286d0359040814004400c14000c034400f00b004951104041c03004292103030b00c80e00c4440e25000d042c01410100141c200b245100d03030f4040d2044610b10320300c04045402840011103401e0a9400a417038841c00760081c45000580c501d000c0c0100b9010b18201409585041135403862005030040406024001e40100020081e880c4034a464100f016070284841800c58030701032618005801c0e00174219842009108003800407034401422240b42d003d140e0900703e503280c648000703d0703003140100400c90594411401e0003007407111001048900940c0300620910900361440e0030400280a10f0141c454198024008002501e07481400326051308020501511760305401d02400f4080d04190454541307134040c0c803d180c0c034032613001c001c80380c1e0007041041c64490140c02e00000945416500d9040000c88 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 812624928 1250 812623678 812623687
    0x801140105090a030516140a08100c1407050706080106111e070503030403050c12012003060d02090a09050c011d06070c1508150405040b180a02131509090201090b 71
    0x9840f96100342d400355801004542c02c3d03800c007190384040e0a802d80105449984410840701c5035040c400740b01401d0b2a18a00a07015030040d20741c128005020440a030020494400344032024601c0c04402490214051009818407a007000b002900020040c0d02c5a000c0000000c24800e104038045950007024803d4686407103120f01aa041d5460f05c14540c00142e414003000030004200030f00040d401000325001d540d21800c04100d40316a031708917680e1450344002d02d9074120f0b109161403400002150300c0071008207950011030154022514800e1b04640c9030b1070f42e90340c1c0c03040d041c14458100010300c207803882480c1070702c001c000714104040c0d4010090b030450700441012604c0d604001c7e101750460094011000c0c0c100d4000ca59590041802c40182c504860551700400054494149070054611580e004019a202034481d00c10240c1540340300d0707445071401d006142413940113903a15520107604043d050300204a64031441411200c0c004680e1003540070610300305e035a4005036044582d80c400ca921207411103455 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 812626178 1250 812624928 812624947
    0x140a1707110c030a0210141306090e0a2d0221010f090e0c100507050703061a0303040e18031b03120114091810110711010801140105 58
    0x8450402480106001500104940168804409584060702408403440e680e81c800905032500d10524010b0340044955043c1a0120300842a04180c0030344d40b502140740801444641130401595049030000030341c2ca810800c06502c1da0102190000d20007001005003200c01155420510503440345a2090384811990003400c00103541501d92101490001303545015a5031000300382c0d17100900891440843d0404040b83c1c031005072048240c0010001c0080042070049420020202500b143d80c900b0000d003040000c00103001030002c1c0d4003c5105480104080803a1400001516171002d03110b0700940c800e0208102d1b602500c10034580002d5a0030300800c40c00fa00060a0341135202d9400d050394502d004464580520b8800001400c09000d030854090569807a41504c101d821381d0400200d41c032510240101d210601007a00ea05125417040c0112100600140380d4002a00e0701d4000c8030f500d010012801400340851540580361210f024600307055558140108c0311041d1660f01c2e50320781002400702c0c1c80540c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 812627428 1250 812626178 812626187
    0x1003170a0e010e06130801021e0c0c04181a0109061403060a09030e0d0c0504051806160207080106080a0614010e042a0e0a0b0f0d0f0516240503010303140a 68
    0x144003040d1000c0e17802c0c603150f482550103540300303008290768060440084400e4440b50015a0040d0400c0c5002c0d00c20b507210101004050800d1124540885c910780c1031220028641e0b1003115500690300d000303507040d03616243c400ca04403500c6a02600708070707140303c5040082e0354020500c1c030352003000e04100045c00045070a00f100c10000301034140d074011021903186420304c8a144604012202d08a4084c0456a1562050707002c480500000d00c41c2c6500c00c1000c28555400c1520361a2450079038411681c40903503a03007041e0700350f910b19841090306030415510744003441400d00400394500c01110707201030194541640c84c0e000d8480244094201d0403caa050382c2c0003850340c2140782c0f115031040c0240680d5078036180f0826980b20140e0340b500b02d491816801c01e50600f0a8007581d4074401c2c0043c0801100341441c0c98500c024042034000321080d00541010f2a41891031050183c0542150905841c21044860316042403c00341540e103414032606200400000c0d5210004c201103800300040f5035110101000d00341c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 812628678 1250 812627428 812627437
    0xc1e081305010e060f010603090206070f030e060a110c0405010b040b0d0e01020f04051c020306062803051606051204120513090b0411040311120f03031003170a0e010e06 74
    0x8001c1c0d42014411a282d600005185008455203103030100c860b666580250100d60f15030500940059003481443d021400064190841c203010b0308100d0000f055102c001f0304940d0103840c109020504091900300405001c0100f90200c100a503800c010b20350501072520082d018600c58040c01110000b005248444e03e0380101c0241440f144c02992194400340740001e1075002409620301551941c4201050701d00c03618240c80c00a40c001d0007800b0241c49030002d200d020704809075031186501ca42017581c843d070303450b41c000c2d0802103001c5d0000c1e049130040004040b40396009680074508000c028800c1c41d5014013141060750b0000e5000780030030081401c504003650140940c55054003003614450380055006c4491b0003c114010b821642001001d10490500405002c3d40c00090070a00c0d00b160b481c916400c10781e03400c040356400141114202505000c103d440e59004498100803e124010100100032101c1c046156a105c03000c0716900300b0100c60002044e80595812803810000306036560704041d121002180e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 812629928 1250 812628678 812628683
    0x309041113030b01090c030218150909010b0408011407090510111603020103180c14030313080d03150311100e0a03081213030804080f0d0203070c03030c1e0813 70
    0x4000055590814550000c001d10031702610a00700308000c0c5040c0e04c00d01c215098540c0d41c040c1d4084044405081c060150a80c074410510207400700a210003503a6403510590003804600c01c0603544a00f00228035003900c0380005200c080030b4041c0107101119803c0705043c010b44000781d41c0715861903800e050858407000d01064101a9010b0a1420a030004c40c080010040d24001e0700c0620030300303d409003403400c640c204c00c4002d442d00710000000d000713070040c1502204030300c20000d048a0502d8403105981c2c070413500662004110341d003d42d003030088442e090300620800c40107414940d480d2501d15111072400f0b800d0b17080641e10a007009621280c500340200d4221034a007001030a03002a050300c0f442c000c0025803100800d45c0f41c1c084500d0018014040d81c101148000340d141c1d07140e0700262919500c08031150401304170540b80c00300510185480d82c0081c4061480307800346940d141d0500c80e0904010302200c440c1c9904104009808203007903001100500000e86052003441d0041190799004400550302c201d0700c800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 812631178 1250 812629928 812629957
    0x507081920060702070803030c090405100e130c0f121103011401080304031502040605042303100f0b010903021005070309051005070506070f090312020a0c090617010e03090411 77
    0x180c054880c030000d03402d8807402860302280c0b0303003607200d00000d80e0321701044640c3c04014500700868030081c10580c0200d9049100a051500203544070107121506036421100c0d081500b440303507042014011803400c4a0010080e004210110605281050145054001e0054544603401402d000e0946095100010102c0c100c1c0071030b0700a584440300c450703c0e40d00500c401d40f41e0f45001c2154005540140c130032a1b0850740c854407618985440c04200c03030310b000c0c40d040080203504078401d441d01043c2c03030622113140c40c148100307400a0b0142031a440d50b0121854055414100860860240016107a44000300b4041c41581000c4d074640d40140340840c0d0040319504400d81001507200d0341c02e800c5070081c020b070503240d1180041d00e083c0d0b1340385032003111140f000d9007602c4006619400700b00301280b11414082c905602c10302c1070315011213954882101d00e441546c0881c1003565a000300b004101709850401000c11048002400280d40842e0526a44d02039803607281c0c03145a80340f8104d01e03030310f5100044803007441603c0e56 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 812632428 1250 812631178 812631227
    0x70c03030905030d0207050f0f031c05210601021002030604091e0507150212030411040c020709061a0f030a0b0d1a0705032503110408061605070819 65
    0x40c000d0184840d4480e0310300910804152003245400440c900082d200058a500e00b0746110ba01006081c1000c1e42006406000754019100d0000501070800c1c000341403a00e48a513540788032240e0000c0d4110348800480e00804c503205126441c2c3e03011030301c141450081c8a0168603a1140c03800078008040c50354008000c409204284080040b000c001c10414601403c05d0780c44140c1d40d021403042020034440b141c001a00b102c40c2c100000186c500181d40c01034001c00844640c85541400725040320b00740c1d241d80e030141c1d000a10400002e440d50081c100606060150300e2001e003001600321403903014085c41d2000c4008040005004c40c030160303102c1160800024440503102030641400d41c014a044a504864046000002034143e401581124000c62840c40403110641203040c00c040c983d040404242c003056200c2c1c201050520200002d0300140c0b2051014118505092200b801401d9a4020030410b00000380600000701d45801c0642e001c0c500c00b01050720112a008004172090482410525484c156145 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 812633678 1250 812632428 812632433
    0x1803032c100506221d06060d03080a0f090f0c1509091e0c0809010c0503060112050603010e07090c17060a05011d040f0b0405070c20011206080303061c02060708030c070c03 75
    0x1045170200000141c42171040300b1740c045030320b40c8840040703070141d4205041981400009124890707155010000701d4002a051083c05040d80c16a00040710580d10b904c00b844141045c01003c0030160f009004145050850100c0040d020340440d00394807814800381d44d0350101e0f03c201c003040b40c1840c1811400520400034144441c40283ca03c000a9840a841e0361030080801e20b200d00801c12070f40206816140c001032000e118000d89e0103001c00030900ca406540328048020401c500f0002100a00400d4134007240d8405100c0000305031071f403900c60002003628802c06001c125100c4030894400e40c9c9003880c014100180c000611459480c8040007560414a046480d00305003117554010044414111030900903621201c8045031503c00404014080445119005c4000251102d0a07400b070345060420f018214004451802191140d07441403501d60400020014079280078455040541d84c56106409800f8094000c01c68a0290281c01440400008045078400481200742c4800642c0111414904c903100d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 812634928 1250 812633678 812633681
    0x1b150c0303011e0b1b0312091b0108010e0f3309010e040c05060a020703051002030108060f16080c040b071103070b0705031801031803032c10050622 65
    0x91003150380800f00c0e5001040c6481c801c1031850121001300c4c00c80307800e100045c40020115940714880348480e2108001804007641c06907042842203004030098001c3c0c031002c0f28803049004110410f141002143c030010b010600080901ea5003048510462030056074501141e682c4411402902072100754200b00b440d000898840400c0700c6a250580f030065280e40e07140f40e8518000c5040c0c0d8010401c4408000900c440d08200c0c002d0400c440c200d204407640103580b034982a05000284480d1080c0c0364001005010403001080b106030003800850441440d454054000c602a880b441400410405054045080f10803003505803000b620500741f11507551060b0b450190325950600c09202c0c0280503c160002e0010500400c2c1c45445800c003002d18907100070100411400740313500400505060f03649282012000388160612815803094900084e1682580c00e030b154100080701c54100500e01000a04c05041d001240710f69076034802c1c0313030082203d45610000683c1c80f2480502441100c0482c171040c80401842d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 812636178 1250 812634928 812634931
    0xf030b0606041d061905090a0f1e020301080c0a150e0d0821011e091e2f03130204090302070905090d2a0201351e06031b150c0303 57
    0x101c4086594103c00760b60303400c5c051514841c0350f6000c0d80c050300284c1246100d80062102d00d0000c98001507103030300000258582695980308407a0f65074048014011341204002c15140e003d0116800d030303202450030444440768810404094100410f514100f5815106c5400d48016940d1003190243c68200340d40d521940701070310040701d03a00d0011220002803032000404c0c003024000e48070313440425010300b00103200000d0a070b62100c80102c001040c1c010782c01c000035881000ca40d0714110016110040c45400910301100039040a141603040410030f000ba00c00405080100507076041c1e030042030346101d504059080842c0b0781d2020368402d0400f4200043e04001040c150003488090311a020040400058980b502d480a000b04000c81443d0b58200b0140d80035031403400941c20103440c3e00481c06c580c460284c00000c8a000c60304003840e4200240710380f062130010640926484103c034644140b801c94000307a07945000405201140785120310380768054071034003c841151801800540d64a8290400d6030341d0302d510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 812637428 1250 812636178 812636191
    0x112061226032509060503010b072103090b1b160f020405040606080712020303040b1c060303030c0905011e120e07030b041e03050f030a06031203051f0f030b0606041d 73
    0x240c000c3e2000c4050041114800355406642d420f4110383c2450801c05040d4003042007540c40c03034085001c0810321601c6085030084080301d40d0340411400511b01c0e05010000c0003402500355080c050320454000705522056811008041500245e0700c8070030708006400321840c0401075089410003041005018003500118111102002290b101554030407a134803201c40c0a02d0001e5050f0010042042201d6072040640206070b00c0601107844210520095421142241d008a010a45800d216103c0a0300011108001e0400382458071841500301c0c0342c040c0004002c0341d03100030306c138010340d1200c00d04015904c00d044801840089840003616405e01200f03203442201c08a428500408214440d04050049034005030b0317168032114200001800744200e580c05c014140305000340c2c0c0301c0c0c000010882d4094030001d440000d4500259606024101c81440582c03480c10b1501d041ca0304c00c04000400d03060b440700c011240c20140c00e00f00d03030319010000341903842a54400510324071481c0512241e1417803032145c40e01401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 812638678 1250 812637428 812637481
    0x9050c0324041203060b22090207030206040b062e09090c02100903231e0a0804030806030a06051e010503070501091202040f05091b01300e0d05040302011206122603 72
    0x2940c41c8d8008041c1c4c410340000074016003110011070300003612003030b030300390450001010300c1c40710740ea000d4120320004040c000c1168801551540c824049422a01c0345000c0c2110001c18441d1090007130f8042e550300c0c4290580d40a0998800c0b0300c0c0d007854072846c2c0c0031199281039403007010300703510100b042041c0b138116802c80e094008a00000f00035411442c011900c680c04180c903201c0f207030b680350f807020707100400c000b4850341d00b501842c180480084c6861003070502c600c50b9188500580440414081135486058100a0081d404000b0920041e0381004840d0200c03020741e1003812481050b0b2000c68081c000021144c3d8080d4100750501c0440c1c10701042006501040d41e02070310640c580da000450307060071111f10000b224800361000824003180182032104045041401286845808000903d00340340303400040d00042004c0703030034400c5607071080c09602c00000418060094070f0400040080900e4030000c0146400010b40c002060180b02d40d5407403180c44000c88141d500c0340303410803802c83e0a8800c40356500604 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 812639928 1250 812638678 812638747
    0x16180b0d05103002091311090603030d0b030a06020d140c0403081822240b18011107091e02160303150909050c0324041203060b 56
    0x91002844200480c0d45901180182c454000703000e03240d0394400c0c50004044100f404102001da10f545942c503001301c11800c561810502241400007001980c51140ba02c201c0183d02405000e95000040d0342109070074204c0014400620340010303140034185180101139500110b05020301c6800342e40f00722910110408141e61558410004c1040c134492400001d003001c00900181026660b40300300810000c0010f0640d407141c4940700c000c2400001c400b442010100d480e0158a0880a02a2084200f13a01000e015101650914014101a02524907903607a88110140c01000390f81c85000303070001d030b12144004d8519140d1079030600ba0182400c181804216100240380c058600018400c0b22040b140030f00f01c5102c0111039507400c074082d003501d005040046080700c00c0410364149610039a42c14612401c014003894181006041c100300040c0324504501801102c584401c8104210b0f039580240c0c4031070316000807206a44241e001380784a40009520010200e0221440207044c080342184031307205816100e0300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 812641178 1250 812639928 812639941
    0xc20061501140f0a03020919060905040e06131e1505010b0a080417090303161b2106060f09020d150f0e06061b0d11060f16180b0d05 58
    0x1018910424902d4468104070358000c41d100c400103420014881d144c050701d001140400900036556481d0381880130402c18204124844c2c2100b1404020705060b00e040c4078400381c0580e03486e01d1300303001804085580146d00050040081c003a0440c0224251200d072000e8020f100d0070b00e00b074010070200011580520745400031969584802c140c8008642903506e241c0c2994803680c690107003500382c4080609a0500340640900b60380c00340301411202076101c4403090401e80c60300f400d0749040103007034550584001040041c4051480d02d0008420030b00103004440e40782d203051409200a0829034042c9209459258010962450031340007488060300c911424400c1c0042d0400912a04080b0720030014491400101081004001400e407076005100600c4141011403420000013040603840d40341c101c0d41c110406001e0380740e03000301d07070059103d083e20010b010a180c1b00d80a0503034010003601e50b000200340c850545100900c600940440174410701061007480e0354581d5808640d03001100c4009100e8103160001d103a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 812642428 1250 812641178 812641187
    0x30212011d0607021510170a240f0608072c0f0924060d030509100e090a0905030715020912060615090907030c050c01110301032001120c20061501 64
    0x5151b8812184145450401c2040b00307150b90422003003290065a80d0040490001030b0100c81e50441c0c2e0f42d079124503070400c10101d411914280200c9001e01d14280b03013800841070015105082e9801d900c10700c0c8020840402c0700c02702c1c460700c0001200356503c0004201c1c002c0c580d10b00103405000180c046503001c080e403c0340d42c0300b003010808103800308108280000d0300a1a10703180c0d000030240281061840c00c00980003003a010a0151001400304406a2000f07180c2d003800805c032544503901040400c00108503541d4240c891144e0040502201184914065220500d0341181c208200040520750306500a40d2240e480d4002210f0749031068945501e0407120080181c22940151001002c0072010f50314240c3c260001c00c40d42c1005806c03c0410701407440180030903c14180303160b94130503059031a50b14514041038a1301001e4464031810611283c3c064099800c104601c01420a012010500402ca24011a4400c00104144103941100000600d103900d000c5401c901a680c2c2203d03000c0103400fa2401580d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 812643678 1250 812642428 812642431
    0x150f0501121a15040207050d02190b010902030705090405070221070308011e0b0a09150f0c11041e02090a0603110d0f0f2d06050109030212011d06070215 67
    0x1002c5140b03054149960000001c900359101c00390000ba400c02e4180308001c40c0880c2c019200c101c0329680401101901ca540410020303038000c41c030703200c0640841c10541d07030190b034544188188594203801202040d84540950240c030307a00500a00108418602204003d41d41e825084450b45010000e04041c1410b0001d0350440d242a50103803141d9900d40d290140941d010344001c403500800d24030007480443c04c441c00c03400600441c54a070b902c50b502039090800e0401c0c0b40c0482c1102005002d9500992000c058000e492030446a40020140e60141075800c0070402410b80f081e00c45140c0c01030303e113000c202840c0c40d03809494808000c3c2c9070741c0032081d1625010703001c89009041000c00c11200380940304424000390480700c030302d1105103c007003240006501104c081c1c1d00e05c040d86602d50110000640807020003420a0803074006000b0090220a240c4000608a21041d0202900400840380000e446d460250840e40a4100c281864201402c01c0c1010f2526600c040e02d0040c010b0240800000413400142c6049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 812644928 1250 812643678 812643683
    0x170c010930031112040618030c0c05060301030c060c030201090602030702071409070203160f0b0f09151006050c03070210030617012d150602030307090f031707050a150f050112 77
    0xd902d1304c220014880300101e801082268040c0d25500040510401b8113500c1407801e109848240b10311006160518450200350441c500529061004201007420480d0590445400b400d04c0b0000380780c242022405003070040340203020240000140020194005081c0381202d00c0b1040b1410040c1d4401d040010480003695030318010303401400300081c090001008600b4042c450420302040c030a003603481d10b000f03840071110f01900c03110000c00c001c03503940f0a020020003104060501b070140d150031400c940c4105103900032142000070106401007400010030880d2030158005142020102c001800180a424540204040b4011000181c014040140122100d1403025450102c81a8101c0da0311489114140680425036441e801c1e200002443d940c0b020001d040b465000c1d43d600d10702403501034009110b0340d201c00c92001100d80100045040c2e19035002200642d01c403034554a03c8c060400b03914005030120060034a00d405120480624180d521002d0b0300352014200b030150740e9076018600000349464002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 812646178 1250 812644928 812644961
    0x5090406181d0304210c0602010c080c0a0807050c070f090e010c050c10020304021305091e071d0414070816060e13050408360904170c01093003 63
    0xc0c01160170706102d900403540c0d0305800914038501500d43c03a43c4c88140c0d41c442000360b5503400140c48003a6000301707440e9208440c080c0607860840d6000d00200840c1d401064207040240104950240e080107000360f02c0280f0030001a840859222801c100040108903c100d00561074030500e42d0a1900800680301c0c111526000390081c0c450009444010f90f2000304100d0f03000032404180c1780107451611400380910b5412000f094080408c40c0d080c40e512402c0d61000f41a9840780e1001c204610001c0d6200d0400c40c0c2e114825001d603121468140c000903a9104214040d005015003c03403030074400a210f880d0b042c0203034000c1c1c2c2e0041d0f51305026100c0d50100c684054002a0100002105680c1d070b03041241c100e0700c54001d1920b00700307910034800320400402904807215919102c030ba1f40e855404882c141200c034403c54510616041c03540d58034031550301a20076000041000714003803000742d20a40c46501001c1c0c001c4100c14074920400c41c1212002840018080381c07015006141d5145840b074440c204020410084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 812647428 1250 812646178 812646187
    0x20d32090d0c0f020a080105390906090a03050f01060f0b0d0903170a091b05030d1112070c03031101092003120d0b030f0c090109050705090406181d03 66
    0x845000a002c001980e00050900c840d00050702c6110204000b01000000001e480c00d1103410b140711259001044403a07100149000c46240118032108411306104c840c0541e59011944040307440343c0614850b20764070181e04140082800004903016184d8641030008000d480c0d280e402c541c00c5040d150240070000f007414000074580808a81c0003d0809000b41006502c108075a00d20301007441c0c08a901d242920f071100b03a03140030812181550f04030300710481203c809040c2031102007039507042c80e800300c8401c01540c142c1586800e0000c0c04000003a07511100c0083c0d4074010780c20442408110740c40110002801c42241d141145010f2141d46401e030b0b071000d840b071101410715032501001c44c243c040c1688d150144410100000c2090390007004581103100300414000300076010141004881c0c42d6240d400e403c207e00b40442c1c0e5842060042c15a5180440025203840d6600c0c101d555004090b00342d50418600100800c0c6a446400e2030b258029110109000c000054580100c0403080941002a250310610 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 812648678 1250 812647428 812647453
    0x903181202010f05070c08010c090e1e0c12130c050d15020c03090616030905101202030a0b0d1421040317160605011805091f020d3209 59
    0x5051454000c02440c0c1345080046544400308425800ea0010350269503d2242e0400c03241c000d01031800400700380b19aa10f007403a110703010100f0b41c0a16540001000b01540000d46a19242c0003034030249400a40703400c4c024030b006003807449080b0840c4d07003d0b1240800d00200056514241301c2d20720f4290ba00115849480c80110400000703900140354a4019000070700c18018141c031101c01400c891191001d000d80741546908000d441001c07990001030040181c0f000c0895610340000c01d844403800000c1d00107a076940e8204003440144044080c01354089280e44550b8144a20010300008605070340044d6010041c0e2080b8403080800c00d41e94b4894000707404e10081010401031080302184000004045141c0900341442d00982c54000c0d10407150540d9800c0188001500301c01280800b40095401b00880e04000d0182550741c212030030840d6022850b03c608103080016501a200c408108003002c0c0111085003008509005804402400782c0460142c0010f80f0310a00910a0244a1380e401500403483c065 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 812649928 1250 812648678 812648687
    0x303020a2310090303180c0504200304080706090204020301030b0f0c09030a020603090115080f0f030a05090405040f21030b0f0a15020708070b0c100c02030a20070306090318120201 79
    0x1020709070241a030340c01064624050340c203800c080d81445624091411f50510080000711040b08404100d02c20406200b00f88a0f140760b030071281c000e038000d015145ca450304c80c58890003030500c604000307400500100002003001303251a02d07540154000300e8401c2c2a5511013414645500034031b4002545940010342c03800140c140103000f160014020300004c42c444c0403190342c02c01c00409a030700c003100d50352101003104c1d0200e00034894850041041c0000c5d52910010744c800804034040e064040c0e1041c0e0307072900442c0c1013010300000c0015165100c61000c000f40c050792032100b074442000e414580400d0070482c0310302d41450144c103006041d50b80100841e0016090441c05036100000701e00c905c2c20744c41802008110700004204440040081790035a03070345c039104440c0d118105401f0209404040303080c00a40c840c00c2e030300802070300ca0703003001850424031194032910300b0051204034814031040d0780200f5501009001290304200c1260303000b038490005007840c912440004660754820410140e020085090040d0b00ca03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 812651178 1250 812649928 812649941
    0x30d0e010c150e06040302070e01060c081b12090f04090c03060e1207150b091e071b0b061503040c180f020d140109090b1f030c0303020a2310 62
    0x1d5400c0042288010045030443e020025005040c1c1e100c003040104050303040044802a100c5013202e001c4075450f242c00540040902c84008141c6d1801241c040d9414890254410b402e190501c221079a007107000d40c01c118907a001c61040740c003549858030400303054101405200030243e40b08150b1741c1e001d442d584410703000f8003800381a00810b000c0c2851258201d80d044001d0441103000d580780300d15003440380e040f500880d01915412806001c00500f00a00900c2401c4e01003509040c1c0044e881c105c0d0b1f128482141c51004a14a861090800d82d9100003804444080340d84207107401d0760484050525034900080c0c074081140e00502000511005201550240c0e150788901d10500c0c5010980b0940c120b5200166000090740441a1307689400c41a00f2001350340ad2540104100032003000440b0315070300c0340c2910410041c03e400c3c1140003010512012030704415a24021a0000b010560203034680c03070000c0d201c5c0710030310041d90740c20901422443c43c40d101c00002061078800030010705020140141c150007a003203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 812652428 1250 812651178 812651183
    0x807020f0a02061b03030f0114090f071206051002030301090c0305010b16170309030c071e060c1103010c050c0c01030c0c1b0509090f010e0c03060105010c0609150e0c030d0e010c 78
    0x1d90340804d48074a0010405180200c0000300c00b840c0d0b5604000d00c101034020003181251051207c08180072051241c1c071a2141c01038100d240a0503645168201c0202400466200d580c10040101c012600c2c56800b101031030583c1e1180c0c20600442c40404001c41c103469082c00b80101c80441045404652041d520b0f10300401c51180c55030032400603103a030b41c0e00b110390001c48803600d40c0d401c0003400071081d18081c405680079040e001c00c0060800b82001d001d031805009030080c0d0041c40407081e00d6500340210b043c0504081a801070003400050340c4400010034540001c0d43e041060b02c2106c50f03241c2598003a009030b003c01c451540c1d031403608000c592035210124240e40700c800d42e080d02410020a031a2201751a0602c05c9c2c55000c0241010110400d105003110403000560080d5040904150a150790108046045400901e80940800040e0074080020200203c009103100d94400c988880080e840c1c0090344041421020b448a50103040c003850340750108000c5d18400200780040794011980101d40c2c0200c3c950 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 812653678 1250 812652428 812652457
    0x90703060807030317070c080d15030b09070e010f030b070e01030e0a0335040f020112050f061206091f3818011512051302010807020f0a0206 62
    0x140c1e01c4004604003001c0f900140d0010310b0401054005c1079a11808541010b12460045142510358490100600486645d00c0d95240c86030600b00f40c41641c1000303000551741050700348a5605100b402d19554990a1103000d0416505c1d00c0006007214100713039030004607134012418200f10f64480c802243d0644428000d01d050595034040701820380d00421145000510a865500e0700d03000003500b51a2001403c485122040d0181c005d48450020104117039800c19400b00c900448043d440c801170355a4540407082403a044d00d002e0802404c1d400001002c0c2c0030380740555032440c00c02d0302109482c0e29550102c034044100d6200260040f4041840c8103001c503007414446000415849840c440480700030721502c5052442060b140009451001040380007440e03034100c400c1004482c1640d400e04055405110b9403407901880a00c5141080c0a114140120310199808100514100c441e2268a04070460141d00083c4500000340d4200c0c0002a10200c1644000c0100784507001c1da400c1010541c0322441404108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 812654928 1250 812653678 812653691
    0x60e150c09180f010303080a0e0304120602040b190806090402011e0212040b09040b100c0303051b040b03150103150e18011103150301090b01031506051002030a0201050a1406090703 79
    0x11000c0281d914012081d01c4a2440d0f9540746080050480101501d4840440e1170040407944584002040b281150390842034000041514123141d0000d00950b4000d440ba210005114015103880401000c0405140e441e07288203500d4100a00c00c9050040700c0003404580d200b44001c21803012000f422810400620403a04954003140302000b040e0003d50008406107004658044d05242030b024010781840301f51703000c9055014035100184101810300000d024195603001145000f8640c021240c80d04c1e05440403140d840399960008000740e03104494003d81807031070710015525980b00340998030b00030000402020003941400408000c0329006031110100c03084820250300401000e006010440f4400300303403103840e454041e016109104400100c030f4441d9140100410001c1c50302c040b9503041d640c014140004406c422403026000b003180e40c0016034031940f145131000d0340903400401464a40300135402403045449841111003034441480716500d54100c5036000030801e040c02c540d036681c002468507012400c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 812656178 1250 812654928 812654959
    0x40e19151403060c03040311010f0207081903060806060609122b210b03190c0513151401022806110a360909060e150c09 53
    0x2100d2059a60314040140800d0030010724010544011031a40d040d80070740315500e08a14a00c1d04c030310000b003006050152551003145a041c003580b00e0359504645c0d40d01103560344c0f100d04001710103800405659510f0080c0700100c101c50b9100313025010468003110000c0485031515401c001098001409098101c1138034107210905e0340041100607400300f1500f0480c105408900c80c00ea00900c84001d40354140250009a4400c0080e051031907903075045c907250000390141164001a09100c2c14104900b1220550b010b601c00f80200d0310b40d0001282c85c110340744403901e4510461682658200c0c1d505008a900004e801c00c8010a060b0121100a1051045e1241d098804004000803904644440c020015039005039042041c00d2281002c0c3d6010407144a0501f4041c090040c03642901e00c40364624060000f00d907199117812000200c44141040d5100003c0075219040c000040100b00070569815040003e98803d103880490400120041d0380d8003158182d451400081044c0e22004607243c00c0580303c4440c40300e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 812657428 1250 812656178 812656181
    0x30312090213021b1b0411040e09060f06030a0309030206030705040b0d050618130f02030f07090b1c0b0103141c02010510090c0207050d08040b03011e0b0708040e19 72
    0x701c45042c242c0043e1102d0b031111100c00c1698a000080c1c41c1e80c0c1c0101c6540910031a480002d280046046070081039160019100502d02c0c0103a509c5420100d0306102880007034000031030b19a116075a081e440d50000d545070410940c0e80e40566101a01045484c18244050305244000715444111410001d150a503500340d0401c0651100c490711002c25030361000e0000c0c034544440344021544080d074584035241404001d80f12645840f0100904090340c00464070210348083c411440091160070603101d203103a88102e08400b81c2104030302280b01d804109007a08100706440c0300c4003081908801c2518040c0c0c2541d4034811812075040000c1405d205602c0c8030181c41c01a186000c9807801180d0000c240b60801942c21040000d403078001e14945420401c1920303000c0c0c1d000490f0350460348204d0742d080209803281444030fa10b1003207030040ca010b941b0010021a1406c80c241c082c08000c0824a04050000d58a21142d5024092408010b044501c1004200301d0b10844100c01600100446c2d100003031003184030030b42c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 812658678 1250 812657428 812657449
    0x150305101d0901060e06060306040e0f24130c05100306050d03200f0d03020702120109080c070806010f0302361005060f09270708011a130303120902 65
    0xc610105141c01c21401c0e0200f805010b008084910588100b42003200c0091024040240000c0c0100d556140c0c41c0d01c5c9202c00c111502e0401300d00016510140030000c140013000f1841c000000d110358021000c107002c000500e039848800c2c0c3d084080300d40d5441c20001000b0089001400c003038105611440d01090569614a5031a8198840c0d00d50385030a158010b08440280c3c0c1c844140750681c0c10225161010027004034003640c07120807a203401643d8100c58400035142c0e14009503401c840350304e0180c0441c02c1007070039001083c0c0414040d0032202a241d90702030580d90350341c0034003800d000400d07000010001428401c100040880001039407038222003a6464007a40000034802c0001501c0400c0c0c00d1090340d01911070414040d00003516104d00d80301c10b10b10046820b109071144030b80126003100c1350039800680084580642e45e02452072440070708003d04000c001840070b0080c4022901c0507681d91050030b1241d0221024911150782480341d02e450340e2000d035024602085003604158440300c000006035190710458 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 812659928 1250 812658678 812658719
    0x105190201050a0b011106011503150e04050c1e010f121b030b010e030a1514130302010612050c040f0626010c143c0a021615030510 58
    0x40d4601e0f014080b10140c440843c0c40505018100c04200c005000c0031030204d0540c0c004201444884080b03030002c400030800d01d0f1606c8004c0100766008184070041d020000e0155008104071140d2180395400c01109440c00065804904c0d03284605800650084101a0500006041003910309601400403010794000e0058a05288404031070407460a07003500c503046e11a5001e1800c0341707080707c1420100e90780e078058000242800780b421481641ca00c00c5900080e140802341c100e03000361070900d1012410011140c5204038095401c03c5004200e0240e07114030001c41c05d03041401042000280c1c42800000c0c0440c55002e6003031600c40c840400e41d021401f80107907007020b03e54645808451800e0119084a1401c1381500030800080080c000152441081c1d80c00c803145008001c0c44c04034070113000c1d00300c602968414a4107d038400c1c0030303050003000c58001d001041d0b45078090f50505942184010f0300d015450041405e01e4505402030300c1e40340e22950110b640010550303910340340c0c20b4590f10006800f00c1034112a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 812661178 1250 812659928 812659931
    0x501090b09010c051b07150203040e060d03210f110408070e0106020303180307150b091621090803010f06020d092103030f0e01050919021e0105190201 66
    0x50420404140345944070050300002c010802c1c0c6000010400d2050865010021030b103a070340079000318010302001000300314100181c3c0c0720002c45240603442c4e8100e8072a04907020452800a10f01e402c00e01d11403242035605580b0010202e00c02e00400742101414a101c8680aa448445442ca07054520420700c001c1c03000c21540e5141d030328201c0c502d0f26140c9640c010f101400341c0d0380c0041140d107400209503a04099210b590030f1840032000042c61840c0506000501424009540c603c501007003644583e1003010180c45400041d602e81e80c206900106505541002a0380811031587d124419114111411400c1002180d03c248580301c0e05996000ce0700110b1340b00c121501c00700b008640402c000b428100c0541084100c09142c0700090703039010100c007001c40c1c903180c1400060040611030350000c891586041010401a031441c40114000d1138104c98200d403501c5030300390305542078505003c1c480c0003503801040320030b11411003d144002e02da980f08a0303d0500801b07008401d41a8002c41707200d010316050350300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 812662428 1250 812661178 812661191
    0x9020706021c0b13150e06270a06080f1e070b030f090601050a120f08121302090c34080c03070c0b042409090603060b0420030a09021801030501 63
    0x7004104104e880c91942450302e00440c00c000000e4a042e40030445086844800a03031396400085a0030f0090401841c113074121241240441494000495014074640241085102e48822619560340d501d000544c00f1540154403054100740040c00e050a2041d180c0245c44620b5907441011010741c005860750899100c0e250300308100d2502c100f2104d401440d088030100300c098680b10742020030041c2c0c86405060705600d01200c00521401c032080303440d042049440c00c40b4038a8900881c0d01e49244948007288501803090104200c0d50ba42008e903191206182c04500458109904100c1c1c0c16002c11304043d034000c00d00c50040c0200d00c803600541059620398002d503a84100301d00d003440840381181c200c0c40249805103c20f21a004c038000140e00c1843e900075141880410f400015100f15100d54891040c0f41e042520101c104038180d0407024130740d4000c1d10309010305543d50841d001880171044414101201c14000191901d4450b0805051103001030035240c00c1091712810000c0041090f0001c0e0760582d181c48 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 812663678 1250 812662428 812662451
    0x30c06041103010209010507121806020c041d0c1306030b01030c080c150a080a06030203060a2003070c1b051f020c010f050d09021f1e0201020405060409020706021c 72
    0x220300c0300460703408800851a061845001034202d0040e072002034107a140b040c01030100305010f184504103045000b082c4119850351a20002c0d91401d110000d03901650400d20080c0700da92802c034662146131704160140040300540010702c8541c00c092041c0b81c140c0350310340400201190149000c5400380d030044100f45403160030049407034901406045030074010703042815036021001c0010250f03a0340ea1003074a444400d40d12a444141c000e012103410103581406010103010300e0303c17140c3c1c0c0300210010501d00f583c0f914400e446103c001d14001107a0b4000419078001c2d820000451a013036500460040c2d10810400644a10200d14040100015a00c1040e48682d44940c803070380410181148940901e044c0c00d03c45284180200b01d0301070010107505c070503200c010b54011035a032411040030125800070748418402c0650401010f00c2c1501072262611524403148111180c418002c03201a2400a41744070b00d00303480c01000500035440440180c0721590300f402000c503000c3c3c6508120180211000300450380b440040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 812664928 1250 812663678 812663693
    0x9090609021909230d02150a170c07031110050108011409160306020313140a0b09060f0c0a031b080405060709120204020a1404031b0b04080303190e030c0604 69
    0x401081d4140300c2903010400007030f640001600e803180700c11300c0301024401070030010501880003540e00a41c4862500f041001922001000d092072409550360254010405505c600740b00d103094034402c041e070704100201804680030316180140d00720440200d0300700f901d500c0026401c503170081e000021a6510383c0001c1c5000310001030f041d0341040164010700403454081d00e101c001800d091000404403a0007000040c280b520384400c4101c1c1d541c100c003606510048000c04141c4074500703828101c484140c054003007540703250700049203407290342041e4810394692502000445070760084480d2000b0980c0704e0034034095003240c4021082240d58913817200611400c00d0310309241007500040c4101c0c03c00800351810006503407428046401580c0545d00141c0c1e0300362264045072500c80350081c00300c4940000400200300074079041c10401020805804400c22a11403c10484a1140d84101100c81d0b0062000c21309070305c1d043d00e401c1080100d6650000742d40c070320401400d0541c1c000c1c0030840103075000700041009100a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 812666178 1250 812664928 812664967
    0x201110a0b1b0f07030c0201050f0a090801060e01050319060b2e030e030d020d06050402121803130510020c041a1c0203150c0d061203110606100e010909060902 70
    0x401d0b1020341000d41c1c880c40709120b800b07105800b504000100b80d2440c1564010070843e44250707039050b203903582c4202d0008042c100030458031492009600c0d150340000c0c010381491500c0d040e200d009015242c02d000194130a000300040700b8003940c005c3e554105070702c013582d6050491305900303003c1020761a84500340c1042c1740240a921220109050820805110200c400300c1103c034030080030540103803100000c82480d4001c0c085a04980d4110713200140ca845c840c0c2c122101d4a01c07500c5080754003030f4001e1701701d00c003281c0328055450003548048401c9801d02031440e01407007460b1038912600c1114503491040c000682912b1701d10601e8807104a680402d5043c07418030004e02401c048050b059440400ca036580400d503503400362407000e0b00c542c07111030214501c100c3c80d0f000c03038003000f02060040c0520340d1182e04813090a080140110089928881c00c1310003118085050f42c440c10780200500725074040c50b503007600c000a1110710700e810446000742c086824405807080c2130145c8040040140c54454980510145840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 812667428 1250 812666178 812666221
    0xb07080901050c04170f0601060215070512040206030703092102160810330e13050d05090117010806040b0601110705060d0e011e0b0402040501080a090201110a0b 71
    0x180020460f81c840c070b42c2d00f21030031200803501d8401c11140d1582150704212440ca00d60240d4050300000041d030b598005841885446202480c500540f03c1501c2520305204481c0904a0404124000782c0549442000b8640c0903c07207090100b0220300c503a0301d1060a0004407803d02c0407040800c2e13a14081c0d03504100003071070310700080c4052030190b00340660203540d00009000640290303118282c111018003421001544101e10b2401104411071110305031445500ca40904550640e007070b00001c07801c8600e041c00104e0981c00c0809041003c00e0103d040310740b9800f00c0f800c9814403003181c071560003078018000440c3c004d0450102400a40c2424541000354400c09018181005410070180780b591001003510000c0700c004480081d660310b420701403d40644070190b0075101d603510342000c240807003000c03102c0d020203550406c900b009162813901c01c00040b40107900800c1c3c0000e003c0700018445852640c003c41031a07005041400780500d001030752910300494410302f2075007102c91a0a101d4214103032516080b640300c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 812668678 1250 812667428 812667431
    0xd030c060b0a03020f090711160e060901031208070e190311040504050304210b070215010906080c040209060f0304050d0e04061d04060915060f0f0501020706050f0c03070b07080901 79
    0xe03d0341e0000f030b00c10101a0403007403040e400e94011404d0389010f100342401d191035002c1035406501c0070742c0000748040d4040c82104030380401080002d2151a0480c0d00905036179014407400c8182c1800703071003161b140030020140c0d03090100d03012122202d903880e200000151000180c824448505501e01119541e03210b0003d035000328105000d001c0050341c08810b071001d0f80c24001c510550328540c401e281d0004059481e0140203a8408010310000d241d01041c4007090754a94510351609990700c1ca5030000704d40c814803842140350860b40150381d240c60140c005000e0711800a020a05099100e405070459901c142c50880700c070ba10403850a140d65401c14007044800c80125401c00080346480e54907090314550014203a69444a4000502000711a074400513106400c10b41c1c00d40c00001a900c072100800301c0b4024048262a00200007c00442c1d541d031200c203440069000d41407862078008141e580d6040b0b050382568000040c0b14503100c0c4072081020b03100711402074400010034100000042c0c00000090b1000c02540d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 812669928 1250 812668678 812668699
    0x7050106050915120c1003050603210f09010e0a060f0210050606030a05040f0b0108010c0e121209010c0f0b060f03032107030f0603080301260615040b0d030c060b 71
    0x81c0300e080d920740e036003690341e0b001900105801505020210071406c0d4040c2001391481100c50b030690003d44500030540c00c0b200c1002d000003d80c00039a51220030000c1686c410008e00d5188440c00024028140c1c06041c00305070481c1180c0001c1d03c103100c980080000812a0343c400c01401e504200ca0380960315401801c20040c10850b0104030140f00060600d03a800c0d441c2d01c0407904024541c602d1150041e00b01a02c03210741c0d40c403a11100e010b00043d080c0d103000500ca040c80709015152021040320750a1f04a001024500021a4070f0201c1d60803440200341130050035101718010130030303104c840d40308907110311114041490900200060001d214840a0080d4410b01001061030a80703d01813a040840f604440300d03550302c29408601506110080c0780d40241000800010000b00b440a5030588950b12115554414081e1021000f074800701c2c03200469620803404294610603013900025205000b42010030380f51001e0010483c06e002140044001a507511680001c1c00300344d11580980076822031718011391 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 812671178 1250 812669928 812669941
    0x1107060516080112030315030b090601080f15010510021f0e0709090201020a0233040512210307030f110d0b0108160e03010b15030703060501090b0406110f030c03070501060509 77
    0x1c4583d80100a061544d54200c407144180d41f844040011640544c1c0c4201c240303419141540c44010038483d40744036100380c0d000082034090100700e0038520b50300f2541460741a880d1900300b2042286600c0c80c0000d40c02600d20b01c545015481e0390180700000180300204030b00302448421441d040060b4800c0b24000c1c079000c800c40041c1e0b80854581c85542d012038401441c401040c0c1901c40d0183c1d248021501940101c1d02880003221140c081c01c100d800c02c0b1001c9101c1d10062038220b80301e005d201d810b20300c3c03081e42d1b5030303c4641881144069a08148146400108503200c43e02107401c8542c01e0040d40c00d02034010582c5099181c05004041e01c9400a280c0018039041500111500340a030f0b440c08400d0108004005c200c0d52002d60180035070f0080106440c0140d902140000480d40c415502000004d0800760089200e500850720503007201c3d50b403100c1e91b10303151610604030303440c4020265a1200d4010040c400310580c03030800240000c1c00c070090203540d40d1803051805038212491607104074003a0035014201b020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 812672428 1250 812671178 812671199
    0xa0b060a050a0809071a0d0b030d0201060501031406060324040204060e0907021f0c0c0c0605031b030f01210212031902120f0c0a0609060b0f01030b03060a0c0311070605160801 77
    0x3611b614000c0701c20344a0f800b46803030102401c2ca0301d8013240c06119024041c0c80007a41500841c085503401e0700c3c00c00104409a000782d40040b411920117400180c200046407030030554101004004488070f280c1501e035280f80c00000e080e60700a40c0f15000040d100c42e04c15241d032a1080d050780d0003c0722070008041c080c0c41090000c8050501c0e80c000d8802d9651749680180e014011011200e50960043da81080262030703000140c01a00140c0c0c4040800f0880b010031000c0c284480304881c0030704400000c0e00c11031fa281c10001d004044100030164600210100c1500058407107080d4029800100c5014545481501114020004448801100b150f00c003040c20125241c2101c2215100101c440c039280e5200c500e51030301d034600004144014903492409841da002e21010b980134000345c520460340308941d035003204011070903118041007440c0c0c0f5810520110b0700e54850b6500081400401c1d0034085040ca100d03481035400350300202d10a4842a4a4504010b5500c00b86082c0290350307440c030300780260194140341d074a44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 812673678 1250 812672428 812672459
    0x801090302060a150b03010902030a050702071206090303020708181e15070201021509010e010b060a1715030d110c180c03251e090b120a0b060a050a080907 68
    0x220155035600f0b4413129000000c2d4108050514213903040d640c7c1d43e442002c1402907008580c100070040c90072011441407440800d0000403583c80c0100700c4620340064580b2402018482c2d021402d00d5400c02005002408400161483d00f5122400c0101e0f401180240644000c0301c5250302150512101e0900440d680c0c40d5071080041c140d0f43e01141c44d003540c2e100503442e20b00401d4050b4042032248040003108541508000401030400000340880e00c21981407015900031a20040c0114260040d50b44813032007403800310380e404000300394900050400040400d0919150018560014031a01050751500104000d10003600c082582d03003a00b4640200b03003030098007102804001c0c50b83c20000200c0c80741e00200005a8000c01d0402910560207041c050152043d000440f131b508a00c90401c1c0b030340120303e002e09044400c03a602d2008071307442c16a03820681c0302e6400340140314421081d0f0b590303120030b01600c581018003454800b0742c844580d5500036180c06841c2c48002000900700d9030043d02c1c140540e445401c0501d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 812674928 1250 812673678 812673691
    0x80115090e0304120f060905160b12010b03091002040f051207030803280c0e10030e120708040b04090921050f03130f0b0a1503080711030709090606050a080109030206 73
    0x54002041c4ca2a000018080c4400043c01090400c1009000d109010a4900da8018020820080320355601682055401280c409d0710380c204104004000d00e6415900842d4010036400c19a04e003100c00c0003d1100b00e8000da08060300481d01c80d0003c0c40603060001241c00f130040000b004111540c07859503a21a50f00c8002d0566600c1b00020384032603850041004001e88035910181e09128042da0070740000c110200a0303400b644149901504082c0103030007481a01142400700300500000c910020310524640c0c40043c0854402c042004001246003100e40584003404442c10302007003290b05801d118007846400103010840c0341d840b039881c0c070041e904041128440035100b06605e499075918a64400c076080d41c030f000a440200400241400c101c00d920401e441070f130781180c08101090802a080420703c416020041010030304002d0710f80070070420401c400b10500010119014181c80781f001e01e050b01c500b05000c036901520342c1c2c0309000d146000c500c1c081c041c0038610f00800c031520507070310025503550028080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 812676178 1250 812674928 812674949
    0x612180206040605210c03062b110303070b1305010e1b0d020402070f23010c0e042a0c1104020307080a111e031008030a020a030e03070906080115090e0304 68
    0x60040c02203a0784610007200840307017000c0561800b41c001110a0b481110001e105d01ca4001e00800c0d02d000d03910508100d1a1b1410091100d0805690b0701c00e5000b0400107915414841800440b001030400c4401d14806d1841d03044103030030040307145460382c2581d600100b0000a5041110f0416040c10000c00900081c04211048000c16800380003060082c400c000c07000c6c01c0002030240c0345042c0916070740e0003403007a04c0910346006164210004942214041503103800041c240e0301c94a040c514003908859114040f101480010300140302c000202c604182e40c0101c0402c0c0001d50040c18449032080806040c44292010b501d107161180d0000c1c41004014112240e16565504a00a41640c241903540454600e004070b0500c5244401c6a099600b08071a4000180380030180450381170700102c26945803032002d80040c61403240c540e031700741c1e0502c0c111580f2541507c520240040c103080e10b0b0241d400200f104900001d07031542c0e0004111071004d9250040c03410741d41032110142d120b101c0041105c048840500c00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 812677428 1250 812676178 812676187
    0x180705030703020f130b0307080901020903101a040501060c0309140a03150e030d1d010e060402270406141b0a030b041d0106060f0201140105090405160612180206040605 74
    0x8140b00540170340700360a210668410030114080a0040042d40100002d456100e00c0383d5800502078242d20403452400d07056040910344ca18501c840b84c108010108000005032803010301da81c080f0341106c80980c00400081c00030b071009814142c004124001505400c0c00540c1510074281c04100402540c0c4170007000029081c1140c031201030319500c4203a4106107801902d41e00c0b842d641d4000054180c8110454107048000e00205200c031051080f0901d4840c80c02c0608506c0c0d666170200a241080340c4000510321030000d0714680000d43c00754440388900e00c60344000984084c050329030070007010300401d0700d80d072002050001c80c0c001d50f2510607504985124980032030220799030408507014119401d000307041048010312120141006400c44070659a007a900d0003007105280108909a80000c0002e903051010080144414181075108a40c0319025000701c8103102c40c0a0500c031788142c003c4d0b0100c0f0000e4207004044900304454002c01d444141c40c0c02004842c68544d800060080c815032042d6000e2110008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 812678678 1250 812677428 812677447
    0x40e0709121104200c070503160b0702030709060b030a0605010305070804080f09060d022101030c0308030402010e03150402040b0a03080301090209011b0f050d05030f06010f180f030218070503070302 87
    0x30001420320303644c160f1142803d40e40c1c2c40c4611480e008241c0070642d078010800089910300b400150010708000107a00c0d011444d00e003502d1000240d10022007643c150103620004190041940a840c004008021802d5601d143c041c00744400c54559400c82070406003004240290941e0001126070000d400c1514959500442060410b2500ca601d20a80d0040e002041c0c903100c8180d43e50240000060807440125095240244015102d8003408010700022141c42e051001c21510000ba660003131060510105030781100d40001e240c01813002e80343d840c10f05828200402c500706401035150000058403000302250459450000d140414060002e181d640400d0011040c1e00c5005034216140d20440318284040c5681090308048100c0441620940704a01542a50b00d10030310460b84580044503601d000f54035200d0044492100305101041000700100d206030941d04c804684c2d42c028542c000715141c0003841e51041c00795041c04400c2c0b41e85003010034000c000c0040c0e080400c803075120149190050356104c155 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 812679928 1250 812678678 812678681
    0x6040b1005222304060e10060513270b010203090d080d1d061e060f121f0f0b060711120304080d050903010e0f1b0f0d030302040e0709121104 62
    0x75407082414401c04968003d90701000c0002070340004054030140000b40c0c0301c443d40300d80c100050358940c5490b1520101085000d01c100301916054410fa203810b80304554070300740310803e00c6417844e0403408480a01c1c032040c00740f4000e100e07003c43c0c0c640078005181070000820000e0b4080b40544c00190640c3c1c0c00049080401d212680020701d01810702e0b0941e103041c9140e5054581c2d400c0101c55881c18200c590213240c0145520441071841041e000f0102c0d00007090881c144850600440c6180c4001e00c14160b403500311700c41c00e80844907011039910001800c034414012400a80700351500c0240944d20401040012400e60300c00110341644c00d9515510340c0100740040c502e140f0a0b50f01020090203081130351841c4035801001410340701401c07402800300109440714035850310301c101c07003008c00d99001140c08000651100011051944010181081b01100341c005c1220100d0240d41240040d0740094140490300c0e030402e074a9005076581c940840c2181c2040401800084d16110141022070103082405a03952103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 812681178 1250 812679928 812679997
    0x100b10031a030f0f070806011a0a020c031b0f09010e0402040b280e0609091506060717090103050c0f0a0302070f050307050c0102060c0c060a050a060f0e06040b1005 72
    0x1030121100440f408104584451101910600901821000007900c1d8030028105060300c07a101e240405510f02c0d404801c000341d001e944d130300041d8024107001c500c10b80d60a01c280208102103008119503c1c03810003c100ca141e9038180e0032407180020b100140007200c001408103602c83d5059400086201401c0000b8100207040d548111454000140000419050030341d04000c58484104441c9581c039544104041c0700c2c000c640d04900e03907012100b401010184980329580050010b00b16038074010701600c031201010507051840880e524002510251940e062040308d910616070b880c3d0606180e0900c200840724442c241612042580100b0010144450350303900c075030031a50000850740d940c0040d15009803106a030401c8503016004450006035070390324080407281c06040d008080c2c6030070350340d0b41807420040038040e0400a51598450010415043c14000c107009064010190b00e1141342020821041d56601c0400c81c1c018890820402c0320b064201c0b0035100e54181c41d049811419a92030502d100c140784 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 812682428 1250 812681178 812681231
    0x4080703111504140a060c0510320103050d030510090903020312011d0f2a0c030703050c060705070807030c03030905100207030201050f151003090c0b030702100b1003 73
    0x800203001440d003074a06010b083d064403d8035014110b503940d9500740c2d04443c0125001c8c000c0d03000400300003411421a400780c1c000001204102c0b1303840394440b00054900c262006081c4040545c00014010320008200259076800146002c2c011898840c0c4000388010a03403040705030480d00c40380d44100300350007402038030340e007e07103112403c01ba545e519894220256007403d049100c1c3c06466000ca0f18650041c41d2207441505410f100b501d8065242e00e5001403254001c800d81c1084900b4410142c0459050000301580c902071354a0035100c03222010740c1401c011019205d1b5060100401c2100d0002c1c1d00181981c0d042900350911061000f454103066000d00401ea40041c801e0254664048041d40c20b9070150420354000d030700030001381e030f59441039014085060300c482d035160726003110f80c1c2403d10740381c0d03d000d02c00c07186485c0100704003450740d842808083d03051301700c80c0c3c06c504c0c08020009225810040c014503400352080c24061000712202081100106c04450030416490b07612000241c5d1448031602c030f0900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 812683678 1250 812682428 812682469
    0x50a05040e10030b24120c03010212090f030a3c05180603190c121a130203070e0609040b0d0822030809010c031209030908060c0408070311 61
    0x14001502294000060000310780c4e403c000703000720704241503240d80c101c0c1e00e00c0c955202c40b400c01c2c800c104203c0d01190310040d0883c01d00ca8180d1180d080e40702070014210702d8580320920003150a0001d525401c205600c902c0b50100d40c8280480031007294461059060340b0070039080311060700d40714502410307001d40300143c074001c0c0c0c12042844c20300c4660041c0108003104420b040c05011007419001c0101c2d07880f0130380c0c0b2464030a4501c004400e0004140d0f005840c06507040c10424240f803900c0030102c0a03120899603220303440081c281d5000c8903061555800340120407400c021440c51a0008002d0080750381e0380b203010702070100071801d003a144d280d0b9400301400c0c2e80010040e00300c0d078509103000c43c103561101c041c41c2c00826031510002d24a0700850141d0040d2a0301034045400d00301d80d400111400c0720003500030f60420016800c80c2c085048103200300c00900b40665140175a01d4284203c080c030b003010290001d47d0303030a001c0004000f10240860070030192980424100100306008002031240c030f085140913034802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 812684928 1250 812683678 812683681
    0x130b040803060a08250602010e070b031003021e090c03040b0727030b150409020102060a020f1315030c02061512071532120a0908030a0207030306050405100303050a05040e 75
    0x10301170400780c1c05600e0b22039240406113446002c101c1c00d0300e1490030400d1042c0c1c13144070240301011003800510340c000780e05580c37514021340c0e035000104603849031400c28003542c0c080104461a0f040c6140110f074800c0d90600101e24605180d5961540080018240381c02c1160704815600720f8007814108590044200d808240132075102e060100c1a0b100c02d554040c144080080000b500e424980248074885d030b0160040c020301d036102000d800195103c41e003096244242000000041c0c442450010050020300c6504102c4184450026084812000300c0e20700303651000c410416004550803425180c3e000076503201602c0b0000500803490700741031350451041003c90039186188540e0010310388880642c150000381000c0c100c00c140d8444c0161410300301300345101c2041140c50104a00d149141c11a1a680d0009401e002c26100c034a0180c0094403052503540c1c0001e00407042c1a03041c0681d0b8040c2804503010402400c00050390544000180701c0102070010100f20000c5542c0101e003a14010314102500c2c1091707 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 812686178 1250 812684928 812684953
    0x717070c06050c2d0703050f0708040306090209060a03170919030f0b070c0b2706010902041d060a03060b0604080715200c060c010b27130b040803060a08 67
    0x64100c064000e608019501049032085419801503450313802161071a460a2402d40701103600340d21403111010b0010301002614005001d04005100943c05800c0c0080c000d40540704102d5042c2e00a481c140c442d4a2142d428030114450825004031069440d03400342d95140c00030301003440c0049062030b115603108000c4001003031140094040752030600c1070620b14110b9984602c280c1d840c06007404054048100e036800244d007115000010120700040a0071406201d410140542c50144240c12407040c607034000c5010065500da00c8100c1c9216440b00d1001992440d110340032903a000362034031018001a48a80d6134202945840040f1000f4105a40136200c1e500c0e111102e00420a0000085800041607400740680d02514084e21104800102001e824a1950b150400c00180c014441103003a9568822800480ba07440144460503494130b007010108424800c4809a10703a0070040c01c480f0082183c0c11048001854002c1144d8001d5202502903141d80b81e40000c91071054107900408020700c80d1481920300c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 812687428 1250 812686178 812686201
    0x9050108010603140313121a091b010f0e0d020a051504080c040e0a0f0507180e16030308070c08130b0c010b1c082d0c0f03030717070c0605 61
    0xa03203005013801c50441000318016980d030702c82d01c002911051503000c2e00307114200c0c0c2900701051031402041002900510780c0c682c016a240261a810150b510404800c461000c1003801c5000f103c0c801d0820400c0d06d1041040540101d2000f2000e6205402103000c0748110b42e00c480c2d8130f1010b071001804400011039803800d084455442400740340d200d03125042a040700741c6040d004030301055a00c480500840082c990740c0d021003007580d100c21511030042c80004620b02c4000d1442c5501d900c0c684001003854020745c51034078184440c5c5600d03820700c10b07110301060021980000005401c103406180c8052140c10ba41480d91450103426402d000d9806030010004036500b11402502100500034000c108207101d0100304004d204960141214608151034041c010a50200c050480c21489035240c207402c0c41d141c111180d010000f406040319058002c1100241d442c0100011030301660b109000b107165081012000c3c10002003061039100d0341000c500055002d622840140e40d49942c00746d0184010f0a08620001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 812688678 1250 812687428 812687441
    0x41413020a12051f05040b041e0902240a180b03070e0906040509060a0e071e0303120b030c100e0a09360b070c0506070c230c090601090905010801 64
    0x1003180f070518010a507140c10b0001c40f62080d180455950b52142c1ca03100c00e1201a04016484035030295a400b600c2e5840780705400003426118420700001682d240510401400780c084210301c0c03c103607000392110000f04640404440c8048114200000d404032801c100c0340801c0321a82020f20b206501109200715250002d0341c41c1c149480c119141019a641d1009201c110b582c200c80e10f000c0c076400304c80462450f9400c0d90214900380c0c2c402c01030359001d41d01d03090707000140c00424003810303010451040c04105050307021146032217200c12114144104214400001d6543c1001100345114011011420b0b804502441c019800f00b18060106c0a60350340d540b02507401880e0100051180100150010005c0a8000e601c244510b0640c44944601078880e21340d000001d900a03d0001488103080c0218041842000703002c0c403591480e41d40341242034181c6401800c0b140205d00311780c7c0c0e00a400c0721108001201040d1003541d4602a213101900b9070720040102c880c038560380e101c0c0841a10309000802c40840640001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 812689928 1250 812688678 812688707
    0x141203010f05040c08360c09090303070e090a0204171e0a08032d0c18010c030509130b04180203011401050901030602070312050702010b09010803030705041413020a 72
    0x340c1d481980c600c280020349400310307019000500420000341c2c1d82d10002d800020a500c4e00125003840802e680b9841500c1540741420310b40d01d500c40780600d030301803074030a41595010101c00050750035030030a41c4001d40140d40c01c0700b007180700e4003000740040e00c0d4510560680340180708c8580b4a055a10040084a490300c4403002c2200000c1d00292004a41c2000000c0c451900c03a880b9002c0e51440d0348031032a4400d40c800c4481c01c03154080c03a108200450420b48180180256004000d455542625088412400d141c16803d207041c0702e00181b00d0707070110350040195000484107440d03040503208041a0b6000503c0c04624441d801443c0c40f140201c2603100c40f080c0c2e010b2a200358001c0110b000300c08501d1701c10700001d200d082c0d0b12080c04001400001d040d034001e070020034400c0c00c00009000740100502c00342c40040303601c140180c0d90317510251824908955403900501c8203901031032441c01c103070b48001c085200360700402c80040d410344901c20140c0c441c15500040001900002c5482d03c10910b40101801c4450802 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 812691178 1250 812689928 812689949
    0xc1c0903090509150103110c030703050d150e0a05040f0b090a0c0e0f13060603050607053a0c02070b0a0503070809030a1209110a030b0105131b030914120301 69
    0x120316410407143d00c5004580310307402c40e0702400151004601802c5031903031030984000300f40704400d0114010405850034500ca5140e09413900e17080301d000011905034002c80004c0e80c42101d02002030401e06041141c00c50600c07600454540d50340d0400204040000500406101d118010000c54400c04606030071054842e80006070002e607140034400003031a00750341d081c0c80e80640d000429440600d45101056151007440c01043c0250f80317450305424403074220342400c0424000586c070310750502e5415001000350140760312048185010a11540c40601c4104030368540c03507486010b00e000c2c6000700404001071120086681e91440100c1c0c00a149070000d555140204050801041c8882004400e035800b4201554440030060046400c0001402e46a001610b241c80f01210040d860345904803070002a5000e00e000200319490074041c030903032420000104502520f8910021002d030524408440c001c0561315008c1019803190500760300c4e000044258811622484150303240c00f46810380030310b0403103640c48003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 812692428 1250 812691178 812691197
    0x7080115050304231507051e071502030613061214070b030c31030b060321030403020f060a0b090708070c120e040606020a1101030608150c1c0903 64
    0x15525804292001854080d807050380c1002c0480d210600ba2840001000b00c5000d00070f18450480c641c01d046d14040c0c0003440014081081c0c41071212480280340341d51005500d45605a2a00d010740c0c040c2d01c1e5003441785900000814040c0c0d40b45007001c201404010400c1042c2640c450203d0446248050111442c2020503020840400702044440845008004442c81e551f111403168039541d2203070071411090701406421101e95400f100290412401910044114900f5421b100200d814020311592180e031103520403104c0b821f103002300d14510041600200c3c0d203e4440d85002c0c0d08019080c500380c4441d00c034107001c200480302d03150401d801a100544011030180ca40d01011500600b003103500e800412203409003100010a002140d4000f142c041c50a15900c18045000038140d131095400074006900421596003403000000b05c201d544082420304100b10b43ca8280b031161520b510244031040c4080137000180c20742603540450311485500082401701040c2401c6001c000e107100e8000390001108000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 812693678 1250 812692428 812692469
    0x1450206190c0c080118080702190305030c01051b0a0c05100920040b101b0b1f050604030f15140412020f0d0806190e0103260f040612090b070801 64
    0x8500010304c2e0082d40001e25100700fa071211304180e4040d00341241c20ae004c1e1040a07845120071300e040409107224501440da50003980101500b92440075110f90180e00d0540010b203100d82010303084500b400401d0500f80303240c42050604a082201185000320b105080011131800c002942541105210a201c01081e81c002400c003032004840b80b9031111030708030020702150418240906442402040c41c0e03035258400c02c13019a00c2a555210988084007024030f81d460302d00c0c40000b940c0c1084050042514440d0400d451500d4001d910b2004000c086c0c001e481c8070421a40040140d00101d08881180b0902801400e041c503001031001c2d01d40b400000103001b03040038030841c06c401241c0c0e8200e0441c030b0364421840d91581d0081084908a15a00840c640c14100001039003000c00c1a500e4000c40c002c81e1405007801c1401903980111801c555010f90900301008000e41e496412410750342590541d10304240082e5080061000034003251202400c07192411040044c0b1035400010385050355810260a00100f503500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 812694928 1250 812693678 812693681
    0x228030501050f0409020f0d0b0717040f060c1403010f230a0b03060607050a05060105090f09120313020301140105030106060504081209060909040501450206190c0c0801 74
    0x1e0003902c0c0d100040f080c0c41c82042c40c0c142c0210055900007000520716500500c0041d040303080f071290846a000c401d17400c21445e02d802400311f280c0c08000150210072803400d5503a60b44c20602c4058001c0000340d8407481c00c0d045520880484400c80c2ea0480e00e195a561940307600c19010405206d0b2110f40c41400031045900c50b103594aa0342d00c0000586104040c50401c101c040d03081d0802803007103401903800d01403140480c50400c40340e08600d000b0b030042c1606504140c184900c440c0001c0000c081844d0060030b0215282e00007c401d030f000d40e50501c107103449488002c0c42c003802502110010354198240701921603140905c246581c100e407011030007001030959501e01650301d0300031446222104d400504080301c4800b0036400405126600a06c40391030481da100008110000c103031000d5455a40da00310f001350305811219080b00358140c452114084103a0641c180360111441c80007a1000c035101e443d21030031901e0307080c25510254040b28044030321441010f40104004001901528040760440e000100403406 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 812696178 1250 812694928 812694931
    0x907090509040f060b040f0f0e0f1209030705060d0e010f060b0f030c130305030d060e1510020705040c0f1e0f140d0f0203160e1c060e0102280305 64
    0x90109a09942c41e41c40c0d0a4516001d804181c51094954043d6104c650743c5110300018941e88140000d0528100f0030000100c0340700f1501031155500010a40310b03045800140b03241c0030350204a401d035032184004042820b00c441d560025030041d0340070402150340034041d0801041000782c200200254558180c810080e40e507136120342900c51000704900310002010400640c1e022402007011480e00038145e001c1c0d001c903c955130050381c46400124441c004000d09000d180c00411240c0f02103400c909200011290100b02c41d1707822441841c514041c19140c600a0107640e00034103000700204034508615501410201035454800001080300c41034003004241c1041060b2404d0781552002d460700d56000090364001c580b480289490b51043c0403003881000280101c80300c1e0140c5c04405a2a0301302101d004180380c01140f00401886104140103140d9103c0a04030460060200c2428400701341a04010009011000e80d105c45940001041d00f56121075075002d031110441300d400018402d40214007101190300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 812697428 1250 812696178 812696189
    0x7080601120e010e0f390d03030b1203091005040b0a031d010e0a03170417180603010801060509071403060423040b10080a020a030f03020f060c09090709 67
    0x400000e00e071980145501102e000c5a0950000411411101070b0710b00d041c2680f09000e901d40c1c0f0103070f03115010800300ca5610303401c21861900003a03103000d6a5a0100340c44803010200703014496441031641450f1082c0c2040c1080300010f80071000c180441790555071030b07900c0030078007601442d111601e11580611482c00c981c11140c8000034141032000d190421009440c2c500740c1c2c0d10303c0c40820914501014000e100314200301c2080d03c0140018041443e000e415070a403498420079000101c020070021600017150122480844c14985507203644560005014030a40071049801480c04030000c110400154400f005071582202e07401050744d914581104c0082b650006100c140314280046480e5090540140d0003c00d000324008500c050400c02e080c1ca00317101204c0c01c1d280884014240072640840209013409061028054a103079907090b00400c80503440f03880001c00c141117000c00c0b10141882404000d864282440540d002401d0001d4804100d0700039803601c52007554420b02107400c0901900c0d03010101c58 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 812698678 1250 812697428 812697437
    0xe0d0b0115170c0c070312180f03030203071131050c13090b030312151f27030507260a0308010b0a030f0204090f11030723160303090201030507080601 66
    0x940e03d00d0101d40980003001c3d194502e03c91640c020001404c11505118460050ba6614407044c009401c0d0140d403002503030240c201a981000e042c0040380d4044101c031100741e00324031030311450506600403511815100d4515000141401310211101894503640c48440801c048184101e40314a03a40301a0713442405800440b0014807402008a2030180c1c020881000d80102501c0c00c00301c281d4100e59046a044030b5025002c0241c249102d00303460300801240c0c110002c801d405501c010380880262800741c1020082020500144100c802d92458410002c05160310406440c0d40694900ea5040754a034170303c040010b90014400c00c41481c181c001408000d003501a600e07041e0b05d17407900340da0040503400303146400c00309908c07520b40c4c00e86440b2600041c0010900070b80e001452100740940d40701210085284d840008101b00280b11101c3e80c4480140519045c0c90121301e61540c051904010520415691a04114002c030b035031424550540c1c41a200f240c000e0b2024030803070307944000803512100e04035403030790226 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 812699928 1250 812698678 812698681
    0x705150f060d080405040c090509070804030f050d0e1006050a1e06050c191101020c0405040506010b0a05040321110a02090708090c030703050d1707050306100e0d0b011517 75
    0x340b401080340503405004150b03051074a03031160003041c195540b00035000c01141071741000304060f003450014194801040d142603803250a180d80c008146100707a144000c104140411100c0c02d0130300d260300c4016111105070894000c0f903031146a010180c2510f200d19071180386003180000d400b01412944082058140b41b40c2e418903810b062341034989800c54041c03400385204462011343d4090715529520300349400740440c10092850000020310b08101c0480c1940641d00384024080098000580365040d1003044000356102c5030410400ca13024080e82d40090080072686034a01190074016405100a00440e07869185220072a2143ea03952000240000e41110340c0a00040800d841440d546811803143c40076140c0418440c000280340440541007a501c2e600000e03840344031280c01c41c104240001302549090540c5c64021005040d40c04000c00c0e5070b000c2c0040c01e9104601a20980b803400307803884002c0142607182a103080507c5096070034028110a1400316106907203c9006060403a40114207000c0410356 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 812701178 1250 812699928 812699941
    0x17030a03050a0209120105090105090a030c0b060114040e0718030809041e0204080c031e1903170c180a120201050d02040b04061101050114060702010f21020705150f 72
    0x241001000c2d50a0b090b4244031404095403140c040e42d5043e03102000101d11810001401403c450001e015002c1d1503014041800000342c209048480c115004400c10400d030359010010780c1c01c9403030081200312940d40054003003015a4840000c0e4018120b81c1d071112614103441000103041042800701a20b124400d0000481900c0c00340c20100290300901c070f0008110640c008108240d80041c0c128104030f81180503a04564201000056001c03004d80c40f0000c82c000c040010244c488146054581d440c1c400b182240c41418080c6014140d000f90b410110480d80c68504e00750307182ca80054200b43c9101d100c03807021342c01178602114031405540031a492014280c010781d0054403554001d1200d5a1801e030248000075800c0c1030039010384000c0c02c3c2c41d1103200f05800d590030118211401600090000002c45441507103e44640b026074002aa0a007880541030400d0007080d602c0c0c04075040c100c0903a0304114600e4500f4035a68028151316489141201c0c00da0760034604902140001b00c88114100c006180003864 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 812702428 1250 812701178 812701181
    0x110603040b15030c04020c030d27080c010207150c0206060405040305180d020405070e12030c060604022101030c08010606030b0d170c0601090b09010905070f03050601180e0f0117030a03 81
    0x18010004041340e5448110700041005c0e80c00014034190b85030004283c1b8041145103002d003101400392240c10004100002c401d1b000d00811018001e454042c0104903800c08031803d6040350302281d0009503c00700003000380782e4040909402da0f81640103019140c0843d400341003600820380a260306490b5903042c02e03075011601d007e030110008003030340c0112182c0c8c0c4a0007580762403203014000d00d4070f40d580d1141d40347c03100c051204c40f118422042185501c200180038488102168840e0800000c41d009680c1d41c2d120520000026620003a81009208140001003003108028000d811a02e041000b44002d540d0341d4015404c4800c407a901c00c1d0000307943c070f94060001e91240e1107210444041c00c00c15081c01c589106052921078242c00002e180c0b9550341200f005450000f034a0342c0108001c0380c0601103864040301c010500d41140300d014081c56204c030042044c0ea80221413000b5525848415a8141641c07444c1040b0b08807010358489200f0060040040b80030081a20005640641c402c01503140101d6820100c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 812703678 1250 812702428 812702461
    0x1406010e01050f04092a020c1c02090709080c04090507030f02060418051b090303071b08010e0307060b041104121109070203090f042d02190c110603040b 67
    0xc0c10000d0800080c14070b221044060401790034200c82c000b81d900510383d00302060b04400c1c0c0c005208007680c4900010703c90350000e04100030310025105080e104c104050512499806a40000d51002c400d45c200302100783c0c442c195000f00d07400f1000315030141c0340850a0104803090000c0242c501c0e048408240003259024440d01040c03403025280f04d10300341d5102e120228606181c0e40988106071550148035005200b9010b20394502070380c0300d82070b01e00954400000d59911440d1002041310850302030740480001d000c44040000c244c000000e201c207840709540b030742c0c503a400102c0440c0c0181c6444410b82e100e041a108010032861a10340780fa140c242058400d0b45690319081048840b10700d0210800f020ba11480b64403802034003190010364452030b803071701048000c1e0201c15180340281c0c81e10003c1007045201c940c1c0c9941c00c0d842a01070004003a085801c2c0006885056144103000c0040d440c0b252050b0341c080b880061041c002c00c1d02040c451000d1b01000050710059038060001c0c5c0c612404901e07501d48100010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 812704928 1250 812703678 812703707
    0x14070b04020f18040b0a06140442081b0d0f240e121b24010e01080102071a1302090109020301060e01030905120c0304090603050a02040f140601 63
    0x51851442d000300141c0540e26000e000070030340c0514010701041001441155401603107a4100384074540c00c02d840c1480607480300e0310040c4a00d0b2524180140aa500180c54048910b001c0034000e0700409084056403070a0101420750b50383c030862034001034104001c549910350080b1882c40c8003a05a201041221017204641d00352421800c0780c81001c0090011079a404424032603000811800701c041c01507804035500401c044025400c03104090720706d920513504a804001e0840c0c3c0c20021603445000c00c0b45020b920718103007402d101c2c0c01d003216107000b4000c042150483c2d01a4070000626a207840e800f900340e0241503001481039034680950305c85c1c1c4d0f580c20485c82c1e100d20112044559407800c1c1d0002000120207038804111248d0000051182580c84a00d900c5072140070700702400808103a035074880c2d44011400a01d030151001284207025081c0610441e00106440c503401e02c100750300d0f420704c90f0b184c1c1c010304401c07841240381050961000c480303030050544c803803005030301c000c42a5102001540d1042c500c0749003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 812706178 1250 812704928 812704939
    0x30b0105091b03040c0e0c090d1b0305070902040f0f0303080613110d0e0f150406050a1418070e0105090a0c05250c14060a0e01051306030504030207050114070b0402 72
    0x80c0c91545909000307144034170301484500c019a8545032108090000c040c1041900c0481004141900c2d103071203601958184c1d20154041048200c4400d1001142407030308010048e00070b0601c00100c0170101e40191041c0c5440d0000c40703580c0f03a42d0700300610080200b48001008102c00b540041c0d00d070300e0301025034041027003031039808980c4010341c0402c1ca9aa42c0008810220640d50304605250701c001001004e040607003400040100c8820701ca03900380c41c0540100010301c0f03a6140c82c0080c50520700741e08804043c000340c0c0c00c3c0c4201e81c02c1103502040e2920081a14010900c12a5070000d0801c00b100c240504880b0050f100c4000d507280c010006018200d82c881c0e030741c00d00504200d40724007100b918141c0c080e0f240b14105442c00e02c0c007042c90164003102560303000d01240f403040781e44113242c1d43d660821110749107900c0c00c12002c030190950040c2c41c2c500651000d0380340f9000a010014071107805400a6100d6071081d030070b40d040c154581005541026440d10b100c1118203080c000e41c030000c0c1c8508061a08640010b04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 812707428 1250 812706178 812706211
    0xf0305211b0c030607090f06030519050406050f28050c0c01140123010c1e0816150203010e06011209080304030324060203181914030607030207050c09040f060f24030b010509 76
    0x1400e0693310141e40c11208117a031202080600d51141800940105800c0743d0400f1080b0782031801c003041c0c6050758062980a031b0710400b09404004d4801120740403541c800092002180801c02d03994071410912505030f038070300b0556428100e1030302652103141070300d0161189010503026417102c2400d040c800c02c520040301d100c140200d0100d01000003a0080c07201c920308100201e0304526280c00f0030100c3c0381040054600500041c014003032000a0207a001d002882d11400300c00080034014080c0c4880400581b060318008240000c1c1945074200c407459810080e445000b07a00040a20300803646035105000058001f0b1000041104000c604124040e00040c0300b130000c1c2100c5840481d04010542c403030f20150700403030000505428207015140d031141c014241182003000310f0310f88640383d4010030011031151004500081c01c0009a810705000d698000740b0412484103804083d00041602101f000c05001690040b0300c08056180e001c101941e6000c0001e00300c0c3c0c0d183c01c0030710000100107041e00059a22001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 812708678 1250 812707428 812707471
    0x411041d07080706080910050903070807030c030815010e040515130c020f071802030601050f0c01050901061a12070903120f08010f0305211b0c030607090f060305 71
    0x4028400ea4203420040c04038145010006494040c1c640e00c104140704440c3c0410810f071001050800307904030514030118032540c42c841d58034254807810000030469100800c0b8001410383c080003224045110341c490008a8640702003076408050207540d218009920301692007002d0829030030054101480c102d880b843c1140020014507040d861071407010b101c990700e100e170325600b55042203e802290b5030b420141c1381e040d0511003010702640001000303865440c1c0010114441c1d0348a4000c030fa1a481c9031040103902d8003913014075180648020b0342c121150b50308043c0046015491134011201d07a1040b0410b4038606490421056080c800007400302c814400071142c004041000032508481c0181d46a440540c000c00c04a00540340c0c602c107070030050f034100054000741300160001030f2185003290354944c0744507442c4482c0d1400703d007403144a28040390055101288210390700300250500b03441c002102035902964603050110303007096580c4540ca41d0f8500760442084240d000c1e9104542090b8403110000d070304c03800b16 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 812709928 1250 812708678 812708711
    0x318010908070618090605010f1409060a05030f0702190f0f080f0301062d0309050a170d0b0d020a05010c110d030815010216060302130302040908040302090703050609041104 76
    0x1580142e0100700d06818404280c40f0040c60f800c0504104142045904d04101c0004d01d19440c0b45400170600850790511048030300207500355085cbd508010401c40e5131781c0c1403d5009242d900150745180213090414040f07070129001184e400c200c00c860301111400300c0c02c6900c80400140c180346054a99001e906d80c150080b400c050010006608800c01d902c1c2c0d40d5241040007030400414552210b02854000414141c06c01d0040101081002515022404610500703100c0d08000300c03510300070001c00c0342410242e9400450005070400c2c02e44034500300000380414043c0310038410242c2d80254000d8000c0c1051143c1d42c000c0d290036070081e0191109034100c8440708086410304000c0d50081c0d002c5240c03a4100050b1007410300143c00c0105c0300707101410510402e42c1000441145034041d41080c10f4001c114400c1c03c54110b00c400c401150004c206000300405424540640d6016000581c040c90550b000505154024082c0a006820150a0a00390b9450b6220b8240d08008a820135074801d0711596104000348a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 812711178 1250 812709928 812709943
    0x7081f08010f051f0303050313051c03061404060e04080307020708030310150c0f03140c071d012102100309080d0606090909030219050703050303040305071704080318010908 76
    0x4402c0001c0c041c00d01c0f04160191080303110f0b403107440038a00141800080da01ca0280e90700a107512041c4450744149242a03820a03181850410b0b1100c142003080704801d071b040c0c10000454080700c3c2e00850441e00c0380c050000b540d01c42c0c06690640e0003500003003000560808001d550150082c8142d03040c1e03644840c0801d0540d80140c0b4600c41402c80300d0740520005e40103d60040c00014581441350070100180c1c0d8014056881d038074003400b80a01070205526050540044407086200360040d00c51003074032404060134600240c200780c0c1c0d6540501c0c001103240200408101011074a0401840401e4410b508212248051080220405d81c8a40d180400108a40050000c021130001301003107690500400400644440c2d0104007858109910314002c01e4000c2400581e040000c41c0c43c030300303c1d0000d05281c3d2500c060760340010000d01c000420007092682c804050b0a16912843d0540454040a481005a40158090300744260070030896600108100781c091600e4110605005c240d140e982c00146040065 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 812712428 1250 812711178 812711201
    0x8070b10031205090918120c0f1207150e010906051905060405060f011404050d030206090c2e0c06020406050c0f0a121404081902120607081f0801 64
    0x2031120140108242c82401d005000d100385080c600340b4000074001000c416003d011032010440055015800da01c05010600000705140d224660f1040410f0340f80b0390b2640c00100d0b0010500951034101802851003080303c5503079400900511281114110f07600080c41000507000707480d9641c51100001036140d000d068410000103031480307002d030340380303460fa1056980c020b00c628812131800301000314903500c4980900e044002840c1c0746d24074012508541e07942d03100b181c01143c0c4c032080c246d480c0c2301059800141c49100d85003a0b025100080c9a00e82800071007041d002c0c01050000365414500c100310b5036030258070f101030420700d45104007451944800080b03a100b41c100d030000920002c0d030309508079010005071245d415094010840340c501602c9102c000b84030000b2080401c0680000c00f00007541c200155009008204141ca5482c8859100c24000c4191201d04a0241c90440042d56242c030010030914440d80e600c4e11481116640d1401c144a1503030103c1c0e10a254042100020600c940c0900c508400ca07003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 812713678 1250 812712428 812712451
    0x20106081c0f020c090a020d021c1b0804051c02101a01020d0509240c010f0506010807030203040b06120f03120106110a05070509130615030b07032708070b 68
    0x240411001000030b0b0071410910309643c400001d0600c80c3e26071150a903445a03070b03240e005031140d444c1c0840101903c10401c01010107100302c0c84c8103005005a85c040301c075059011600004c0c1c084c1200f82941c0e032282c04c0320040c1082d0840406080741c00e14500e9401c00151b46403058035035200160490301c04030340d910500504803c110501480d80ca50701001061042452820900d082c25039120000d20000304598255000340c803040c0300a0400f911744030560304403015a20080c4080c800d504c442c503005000c11100240010880302c0401c1d0503a00a200710f170301a035005044411250744500c00e100ca0001c0103e4450020310075002c0c11050a00241f01600c0100302c0084051265458070100400010b4000400d803e070b030300401c10060000d0b40006285040700d030240e03003c185556a4041c0307c21840c55400020304614203201e020707015040300700c1c4a103090703a01c90f81329688207483c0c1c03607404c030100c40003281010051403900c6201621040980e90707456a03907118070510751030560595956403080400740c03641c07170b0002c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 812714928 1250 812713678 812713723
    0x10150c05070b0c0304090c09050904120f17070c051c02060a0c031401140a0b04030b070f020715080c07050d090f050103021e0c0a02030d02030d06090504050d0f02010608 74
    0x21050007444001c00c820032145061030620741510340ca07442a0300c80c00300303000e640c0c035401003020b4015400c1d42e00400000382284402d24141c204031000800640300e800000346442c00c141451070281200344203101e104440d00c0740a5130741038026942c1460203441503e0f01c3c0714074612140411007c40d4200c00d02c5603141d025200380d0900f4000c1d00161040d422001d4249410320f40401400380301c104040381103c0c20719890031201c082c2007011034a6030801d5002103c03460000100441400501c88816019915a0351b0354502080382c1e040c1207803504907030300424015104070001c40e03019070320030305c03030250000004400c0354609445130b901c1034504040311080038040744548030204144000d42c04004010036003030a083d407030091113000d160320703581019140301c200c0704020800c0c40b482da0301042004441030303000c1d08841c170900d01007401a580c3c1c0c00000042c44201e0400c140030849565501032580180e80c090010289206101c0c41610b17021066070014003150350b281c134005207040080240c0d541300c0c44201032240c41c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 812716178 1250 812714928 812714933
    0x1511060903040305060c0a110106060f080a2a0219030c15090302030901050f1e0d06050a030c0603020c1c120507050c070315110714010b0d120810150c 66
    0x10160010646030007508144000c002288021030115440744c4200300e0566503180e690815543c80c0d52041c80402517610345031010440e2600a000180c0d200216158000c4645d40c450102c0c040d10401007548a5050f0046a002902000c4000302c00907e0624010b40e040062848808076443e0303c078a80550004078002da2400c00e03c40d421a9039140c00c41c0030b40040c440300322282ca0103503403403040707040190400000248102c80030300c40c003040d5601400c00307290000380d4040030303180c141064205a04071959149000800207070b502e0700348000710440364409410403180e40b13010002d90094200c103940403180d01840c0014810107100ca84072046508164a50078104d41420b038003d81103a030024290300c14403034100f0291500c844000b4030b40040340c0d445801c504040c131800c01000090b2031005079104c26543e01240100400c00c541001080030b08501000b041305a2307040c81000001d160800e006010f112040000780030881c4940400c3d94400d400b481c0039010166a248200841010803442c00000798100c40407208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 812717428 1250 812716178 812716183
    0x8030a29040c0f05073314010b090f06071e0501051906031a100b0c0307140606090a050402030111070807060c02010e0d03091a0903041410080414071511 67
    0xc50702c0c600d03e00b000c40c1c841d10031405002c500c690322000d0f00c1c41c0245003c50126503640782034500440d030100e01d50000c4100501c812006050030305039100c10800380f00008034100131890107032a07c84200401d0f03000b140e00d4500a0000d2640403040640c0c50307241e04000010f050400011031007c00348107200004980c0340000b0355041000720140012042810141c0030008600303110042600911b00c14200e50a548440d425900f001d0b40c141d0280003a090040f03003080d40c140380440607146181c052018440d0403005030445030340782c00080780d803540e1001001e4007103200c0e10002c4d848240c2c868409800002c1009410b007a18070580c019001c201d0b440b000001d03e01c030411136136000f201c00600207030000b4003030220800090703a120a207020380b035009c150340c502910f014484101e440d03e00c10845018080d8083c18401c14064903548540222980c4142c584140c88e09420a085000a029078079603506c0e445807165919100a588103210740241c900c05d140c0081806802c24680d05007540380741d16503400d810705030f202450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 812718678 1250 812717428 812717441
    0xd2d1101051e0f0a15060c020a0803040317070f050a200a0503060a1a0a1202010f05040e0406021612030b1c050a0f291015020a08030a2904 61
    0x4105184910888590300d815002900020303c101981e0103590f40002210041c0b118083c408802d03882d1010004a0326003100d0b00c210300c00c4c000d841c00581c0a03141c64509589201e00d1000404009410102940c1c10860502034000c2a10605001c960f04009844491030700003210410744482c0e003c0000326010041070700d10820b49100c2503510f84203040c5480006074036484c00401e00e90107640ca030000041c01072084011903502c04401012050708684440d071050b00d903480c0100407804074040b41d8500c0181c0c0d009006a808480c03210b0b0980d00c45070744135503944019401c6209250701000e1849610400038512041c0003203140c649640000f010741d400340c1001400034050301e41d08c1c1400c550180c0f400118401060f043c4605801c284407100e4a5001d140c08a2400c10421944000640310005c0380038104151250780d016101440407440216207800c81106032414080107100946e005842d12070010b860302000d99440b441c00360000450160740310030108510b41c004441c9034003c0c2501c05400c1245460721400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 812719928 1250 812718678 812718691
    0xb040602030d0507031a130605061201050f01080f041704031e021f0504091a06040e2403030d090309050604030c030b010b0301030218090c131a090601020d2d110105 72
    0xb1b00c18100d684001c0d01e0b4002c2c1210300c65000d581070340142c104003101c54121070000c3c2401f800041c0c0e20345070b81d803407500407407020f008282c866108907410040642c85020f002c2d01070b4488404c087c0c40c6448030368801294a000700c8208031104014040000419600402c26110501d40c408420810f4401e10400c18600c4003607962045071242d43c1c951a4080e0b03800030035501524801daa0000d0b031480044900e41c181c80e80d1300c500b584e001e00006408202d103058216501d0003400202d0b449000c4218082481041c60050440650554001d0001d00000c400340e0b00400240740c000e0401074841c54a640c08600d030740c0d001c4d070001c0c2e503210a00c090410801c4082d40c11075004015082e10b00303045504550010b40c50540d408184111120001c000c107a07081c00501111003448801441500d10030807204070b450183c107052107464540040100504011308181c0c01d018881d01050b805071690021f81c902c151081402009502c64103600b01d13000302c0201c4a000c22141507040c070f41c1c6030008003010f43c00d525400e542000744170 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 812721178 1250 812719928 812719931
    0x4020d15060504080d030f0f230f060d0f0311011805120c070329072706050904090f0203060906040c061d01031824061703160c0b040602030d050703 65
    0x2000341e04008517004580360032070f24000c02c01c1e00713640c001c40010700100100b0009840c40c18943d444a01e4000f24400305aa0300d1404a4440e9994605c03c0c0c40b0280c400c8a00940000c01141c0e4070000605400c0740c440b0507842420803d5001300c211088608466500e5607160b4882c3ca22070840083c03140c01c00402505c40440e005851510382d40b46500303500c0d4602c5120082080c001d2902107140c108200c6410300074200324401c2d0300e4080c81c15100007802074490386036140d411200307000200c031002401031043e0301380c49c9243c032a203150100030000c0c040103010742d410030340704140c20070301150059230180105805103851200512250615003041c0d0000e484070b43c0490103000c0340740c0e4007040050700000808440182402d0002e08180d00c581002071401407400d0083c444030140441001c40b4140d4202c05007216501c2c01d080254135102d81001104803102c0c01c00030307850b50060000c0c6001500c0c11480c074075114400c0104203003036581c440d842c0a0030f411a40140025800105041440d000c031440b9003503104480c0c0c0340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 812722428 1250 812721178 812721187
    0x1803050a1b02210f0d080a0f021206060306061c0e01051602071a0c0a060603050c240d0605090702030301032001050711150a030b09150a060e0d0204020d150605 70
    0x10701c11103107010b041c04005507182e00464244106000c01e1500300004001d17a0a10b4254880081095008584000f41c003440c0c22202a114082c03842074440c072011480070015170f6100c80080000e2a00300400700ca9200d0401c003c0c0c0038140c174080d40b00d0240c01c6041c84001c02c43c251070500850a40d03100800101d55110200000f90070194001000c0c800c035140c4903200a080742c00c0c0e107684580c1b4450030300107103040c0c0300340000c84040040660040301200e0085007510074040e03114080044042d0704c62111859221005401005072651100800c85d04440410008886946c0e001160f64541c003180c03d04056040800100140200d40920700034241300d08000300300d45007030000060094000c00c1c0b00501800c00b00d580c00501d50311292810b24400c40140c151a40b145540000100500704440003507005d00388610210311100c41785102c103200d01200800c582040c6007024001c588a141982003540c3c0300d040c01034a00e015031158402480b21041510010488681f01c07030320920110819400b500c108141040b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 812723678 1250 812722428 812722433
    0x1804290f061918150804050f0705030a03110703050607080a0b06071a0402010207031b0801140c040e0907030c150338030c13020a08011a09131803050a1b 67
    0x211030030b41a0390300d09000c0c28071902d507056000010701035080415070400d003c0082c2100b90300000c08921592160040b03620100420b00880d0f00c0d001c10b03201d11074040c0c2c41540e90800203030090b6999010550500212030007590b49444152500340161031080202d03000034244541c0600b80d000b10f034285030054400500e020004d076185004050b4541d01020391910000205045a03c00e0000000850b00144948210f9a50392030105d0352005510614400c1e41c64010040149201c0d1170f6103030301c200c001001c124245854800c98900d440e1004020901c03d000319080800001c117010303007030f030050f2441713001822803a10500c0e00034040b100401030854400305600c2d05d040c03d182181351882613040d2280680c0c99964000030119240031140711000e9030001c4002107410541446a0140107488415690b0f46101d90b0b0300c0301c00d42d2017841e801040d517001500800005d0554240801c8101e041840c2c810006251188131003011003101008d03908800041000602000d01a889070f02101074520b00e684082c21500f0b5507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 812724928 1250 812723678 812723707
    0x7030b010b030612070308190305040c0501030518010c233402090406020a0905010f05040320030f01090512040f0e13020a0806060918031804290f06 65
    0x14441c800381a0000000a405915035210840b01c5207100c0d0101c3c2c59903038903403903c1800384c2c1012391381200351041041081d042c24480d0059078010b03508582c140985905140045010b480c0c01801d071480200904c560b01000c0c4030900c1038141e404555a00e0700d26404201d007900071581d03250140c08046907400d104080d19901c1148401d083c1c0040b032403542240803010190043d01700802900a50702c4070620040005201d80c43d0001c00b420401d65a6070810592942e00560b2030425414412002500c248410300c00100001c641c400b0084403103080d50051412440040d140c80e03840f0043c04026511841c0d808200042004129401c0c00b40144280c2846d0401c4c040100040c1c0a02c00c010b56911030f000400c6040503588001c090040c2c01078031201c00a912051052340e1a80180d40300c40c0030305448000122041c01ea1500c49002401a102030b52a0002130070100f8000209042d000364019900c03000f844c103089a8955403403a00c51080d0030080d014145c0003c01140c403500c240d006008800c100000c1140c1f9001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 812726178 1250 812724928 812724931
    0xd17161b05010608010c080412080f071b080c01020a09091116060b0a0806100e0403092d0f05040e010c170a02070c030b0405010507020703020f060901170115020f07030b 74
    0x10480e024424400508220380541290703402141135510300300c0542d80141d030200a1a01c218010700c0240d005081c6110201c5e800c1c4d600300d8600aa46070110081940b0611a150030701c440c01002c03911601013202500c0f5003140b03038050ba00300350f40c5a42c00600301000300e400a095500828544030100929100e00403070034041d21603100707004400d0a09810050801606d0360083d2007d6101807c0c219403262142d54465598905444080c1c2c40002034800081c0c0900c5111044e00c40d552580e1410034451a081d0340360b82101c450071030f00b001d0b150a0701600c0c5456074804001c10080c41d4a00c0445095868541400100c0f0f00e041e183c000780e641891041c50340c031034120509640c8000d405050707a0741039031445034404c001e00401c0e10003040c04000d010000140484100307018040c40c007900080041c3d4a902e441643d442c0390601c4029000340849520a24510308500545220301060502d01e2000c55080100c0401d04003d0300407400b440007122340e10b0f0400d070341000b41c0800001c02000804007a400c60701ca10040400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 812727428 1250 812726178 812726207
    0x100e040f0b010e0f060114220806100611060709120203010b040c0807033b1c0309030e1804020402031b030916060521070507050303041a060402180909010209030d1716 73
    0x103140823401c0003c1d0034140d2040105040c1c000e64413103040c000d40303030b51030840380c1d118400004112103070301c10301200301140d028014034aa8a4040388240b40c01e0b147d0140f4003040c00c0a07a45550f03581040019601d6030300401c1940c101954689070546011840070b01164494404659205912141311020681d0075000500ca1040740c8400d24117401c62208003483e10030403a0f802c05072030502140344500d1541540058024038800d449005414403058207200e01010b014074002100c40350040802d015050542c0150740050350480c00004000302d040000c4104c3e0700070b48500c202c503400040304140060044d550607000c0c041c0341c540f6900d061021045900c2c550381444413090713180410404500e110f0f0080c02251102680402a6501c0340380504000303500f903d0107030100c0502c010040004215107080c1c421100520445100007070901c40c1130050000c40d800040c030800066500b000500c03426901002031a4600b080c079a10b040305928102400d404c200c50240c02605284400610010f0301a040000c0d00412103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 812728678 1250 812727428 812727457
    0x30504120c050604021201150f030302060f04080a0815061602040501120503121e0a050f101505070f05010e030a030b030d0c08160605010605040801060e100e040f0b010e0f060114 78
    0xd414606e064010b1403880c0c0c040c4000b40e50f06200088540d1703a0304454003141e00036000d48510f0794072484010a641c808030f034020180c0c1c1e001c0049410107409810510b80107018400a40e40300c030b4a000100751941e001c07199400e8400041084001149440d001d4070f409008014a185004209952920f55074080c00c00411110188003002803180aa01d2414120409180c40f9044482c244004410011701003914050002d0315081c0024010a0110b001174084800540c480292005480c1003107d603070300300319021110050f0000158021070800d004429a50b01d500d0b001d580c0e560845600501202c0c103058515000b0341200042141281d008900605c05641048000765150765407841d07000312034410740c0300034107080c03802c0b002040c0590b01401034025100032100070822940c03110078100004204072051040d030300d03114109020240300c161180c0d420a20840e0386528654066031a010422426040440f5100210040215595560083c0d9400c11021700b40480003003502c0ba06c01110b44502c6a00b841d03201d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 812729928 1250 812728678 812728699
    0xb0d0f12050d090804090b1f03020f0c0f010e15060306060f0d02090a0b2805060a091205151317130909050a0201031103010f030201031109060307030504120c05060402 73
    0x2a004104942580070003103030800951101d4586074a150300a400354401c028640001400b02e401c2c48e83d04002005d0010141c038000d1303420000c04802a5200c0701e450002c014042c800c00410040820440603d0703442074002207014545030314401d1a100c17034107502e2040c0250120500110b501e0119109030810811394003c911914108042111080b007c04020341100010080000800701e5502044200404a07500700002e0300700b11124181c050040c11490600b4100c1504000c83d151010051a4007001030411410b11507030740d41e034008811000e01003a03507141c2010030000515516904e0300c503402242880309032550207032a1a80210308541c0700341d2840802000501442d120b03210001100102040c00d024001040d9030325000c3c0d10b42210b6803080380840d04000005901c80a044141c074140c508441203031426615540044000d40740004940718000350410a21009868200080d846940b4648002c50709041618240e0031864099444204101c42c108040c00095004201d050f0015011204445036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 812731178 1250 812729928 812729963
    0x31305060313081308060c0a052502090a06090f060e06040c03110a0c1101090503060f040201142d0915091224090105060901032009010609090b0d0f 65
    0x10500040041c0c00b6041c040340c445641820240000180c5d6640c0003602c00702d454410342030070740340242130800001c2002481502d120907040f42c8401c0c49158a00000000c03402d007038000c00c240183c01d44260800caa224182032210298500030030940302c000d46800c000540c5020f01f00d01038104c019007032510030754580031401c00e44e5200c0e400403510328030242c000c2a03440fa94400050184042144115140000c4a208803595802881e1400803628058054070310399641c800c00044030038004008034140000d03039140700881d04c046805804200807501000c4080a042000c04180c5500c0100710340595100b0804070406440381c60890f07a1007807880e1003254440e600c0702c0004940b01c03014a1450464416010b481c01401000c204514842c045121400c01644829000d1402e9a00c1101c0729900001c034800100006003110800001003605841045120411076000501d017000c281c0c0103000080a401c000d000c0d4440b280714440003103804590441541d200c83c1d44500035918500805001501e001100020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 812732428 1250 812731178 812731201
    0xb120a0b0a1427220f0b011701090503090d05030f0d02090a090903081311040e030301080f1605010c15060308030f06101409120a0501050a0e0313050603 67
    0x11141009151408140c1c0b40d81040702c0300308032825200c0c030800040d0074034144031030350a000400303070203807201508056980c08880c90503134410782840d07041c6a108440d482001c542003003a2140301e5441084610525450200104606115440c0d20701c0c040c1d151801c0500018400411241c030308a0945031220845214100141180648603a24080d190001680b1040004a038001c0031000000c40c3c035090f495403214980c00032600c1031080140440d07414070128000555000034541c030140f1503881d0380c6c0b0b0030012001007416580200481c2d80345070b0000c401803054400030303c000d0041c080c2e564010001a022601c1990701c10003a4032506050101041d4103105104003001c04030035000c000907007803120a41d245844009503000703d0740030780011603540c0440c7d503078500a5140181e40030700f84c1c0d0300341a116540603030140f036900000040364441300920908503108410321034420420300039400020146800071800040d1009000020b80725082045400001d1801d20603050581d031098408503180e0751600c11400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 812733678 1250 812732428 812732441
    0x30e0a0b04030b060a150c0f0f020d0c1802090a18060b0c0c030717060a0b13090501090218191e0204121104020a0905060304150e030712090b120a 64
    0x1103103032000100031081c0803034048030030b0280340b0607104659001c0e680d0025003108541c0c543c0c41000201d100050002040340c9280804001c0c0c000c42c0c03014460211540040c050020340107085a0005102400300301102c65000d40503d440c0e090242546000d03402c40c0060145240c5000e41e002a12003941c081d800e001c030641c001c00280002080b070f10b030b40d405c41c090703075503a20351115091501c2441074031008102620152000b000000585006103901d031604481c400190440c89215504136100e030349a60000441401a584807070701176400000e08800070300511031036501868204a440024109110b000c030307000c00070000c84101e20000041c0100d0515000501c0b0504042228040350003c5404203280c1800d420b500f10301440344807102154203074002800241d00030300c07410b82c003c510340e03200c108403908158004650051042c42d80750481444c0480b0001183c001901c100050381c0b01059100800c01c030341c000b100c1000744506000c84400d1400c4d541d2142403048036a01c204030314441d40490700e50001030704004d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 812734928 1250 812733678 812733689
    0x304050d0809060406231e03070c080f04030314030408030c0c1515310b010504080312160206090a020f01110a200108011a0f1204111807020a030e0a 65
    0x2561545c0d07910005102181000c03400c00b4903200c0481d03898140014100712003074900781011040701031813000c4030000b442d00014050030a100c182a000c6001a00e080c00800301400b009041c1c40d200c504604000340811811728158010001c10410310001c20864010389505c44d00541400740e0321009540c5441c20242000a804010484078040c0500c58854130040e10380c0c0007098840707502195a0032100c000d1390b1903401d4849807207106080034201403080d0b03801c01e024020b0107040140c40e160366605c0c800e146034800c6107881840000032090040c211100c1140400901c0103100924407410880f030141d4948944400083c4540c59083c86141183d00070000000103203551b40540c3c05c0c007442030400d00341102003000d8401098154540d030420b25801010424142c0d07d10703004003409840310074015800d0743e01030b40c2654000c04003400b40700a42d401d12030f0b00c180302c0c0d03104003101c40c3c3c49664401481104611009081c0003004520108408168000b903881502c030f4041c6001c42111070804045050004140c220 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 812736178 1250 812734928 812734939
    0x70605071809020913150303051e031006110a0506061c0f1b08010c022a030d1d06040302010c12030f020c011d030f0f0a1206062303090304050d0809 65
    0x3159016a800b600c0c0d080c000f80c3d0400000c400e0355100e4801c0300c6c1115040200c3c0900c640301400031038810405084070b00900c1c004d000d0018400f51860855030001c41d00d42401d148a0303031080c0300559006001014103500e050040c03a000c00b441c0e459035111035000b0800b6010343e03101184510850090424041c070740e0381164080c1420311240c2401c0114440303280340d0006440c040300e0f0024441da014032455884580a5001d42610305402c0800c0300c50440c6880c191210b1403090000d00d03000d68081c80300c1c180c0c500c2181c484c007105041042c100c0007901116501144149418801000580d8001e058401038a0780311040d080311070000b020070340007440c92150703013400d00c0d10101d080148041e056100e942510000700c0c211058401c071401c0b0355524840c80d4200d81c03a44000380406079841c010240a08000343c13860410007203c4c042c084058045803400d5002400090b10b030301c40740a00d03007e1400c2d020310f444058850203156281500c00b243e600d101d507108150140d403820304a04148803209095640c01e00b0300910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 812737428 1250 812736178 812736227
    0x2703160915150e090903040506070f050123090706051c0c230904050a0c0c0308041403120106081f1a0906030c1209160603051f0f061404030807060507 66
    0x8006200281003e030560064210a000c10220382c5d0000a6070204d400040046190245995a4070907000390006c2c1200c80350f484140005045082c640000c0b0103d030314101d5404245410700909203030991981c4601c0500c80100090300803001540c01c1e4003103401d0800008075480003840421182c0d02141c045003c00b0000282e178103130f5103542d108010100e1382003c560a01484d1201c1c8481c804175070b6004e4045001c10401c800704400240240c071140d9000d8001c0b100b101d0303206200c80381182940e201062010540e01c2e41c0b00103001503034106280540059020241300c6c00200e0040c0b0340e0000190038020440c041d10f0305061450481600f0341141c030a500302500321034a908000390001801c1c0c001c410030902a00c0c000780024a0b011000031049100140c00d603c010a0a1074044240d0080501514144084580d11803a00c8000705803107851000b0140e800c5690748041ca8154000d00328201500001004142003004101054855040c0d44d01c40e13402580010707060715007080644805501c81100802c140d051003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 812738678 1250 812737428 812737469
    0x9010302211002030a0c030e070504050606070507030807030f170a0f06080115060207050d031d0406320a0f09021305150a0305100305030307030905030f2703160915 72
    0x200614011178860005000030138806c0da00307406503a52a10910490383c0451b00030001864240c01c080d40040000d0312307061400c44940c49042c00c10056410035a5840c00014601c000c00d43d11000101414003145400c98010a4081849040030b401a0151054070740342d000d841520491a40101c00501c1180c3c001c0011600c202001a0145102d22941d00540500c1d100000c8a04000c0001c22180d036060340d07520682200d02d050316130903040c1928116001603485401040e000c102400e04400f03040200081c42c8034038180403a654010709104062030040d10a20410807107070b0040e07040d9200b079440c40307500507072141003203406580c1d00c100960105038000c99084a25145c3c0303000e00010715041070607503424080ca66031004d850005a2640c4001801603200b0400038000e188070790f1008032801d1042c1c003920718000c10840c250130b0300d40009180c002c818060220410300e10a01d00c40801c041c89d41500600760750001e22560000d003211030703c61082c0307098039200c0c154145001c1115200c00750000750030b0a42448603c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 812739928 1250 812738678 812738681
    0x9030904180c090507050316170114120d1b0f02100801031101030603201305090c13050c0405120a080a1106100810090303020705010c0206061e090103022110 69
    0x307815521500b5450707010030800407a0151512941c0a5102c1c2c2d4956180d0500071000104c18001641c20410614640034404c2030012000d4024072110290300d440111110410860080c20166096240c1c0100388040100d81c00041841c000307800b03844032006011340313402d02d10040841100c00940c0104144182c5240c2d41e001508203050303c0c010741d90010442c4038031005600310780d0180030107002d00c40044056150410084112400007801401525001103594038600c1980c3c0155102141a00b00924032155401c1090300c41208490410081c81039041800c8856414411401403038010031a07940480c0d202d15081124000b003e80c080300d103903030320003003040300412500301c1d5410101c0c00e005000229100c40c598030601400e450955018045001079090702c2030060081d05030032003d241d000c0c08640c020030402e120300d00407900213801138415807070400200681c50401e071516204d035542640c071180e06900e0707400c00141520350644000e511500e10a48007152107148210f101c0343d52040220500200005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 812741178 1250 812739928 812739971
    0x6220f020c1f0e060a0e010b03060108031804141602030c0f0706082805090f01180512131401031823071d04081306210513030809030904 60
    0x5039403407510000b225207002040d60721103850012580d0141001c01c45603401e03907201015107546180005170310400d000100c0c2c00c01d0300981c01000e060304003182c0003609101c1c0900420030350038200d03000c000500682091071040d810203003110101c111011011580316000304115000b0294140460b0017080d2100003956880c0944c1c0213800004003040c0100d22011183d900c480c52903000041c8000c008040c0c031000b80010300005000c0f4041e803041001c4241811020700c90000e41c115900c21104409881c0d0804c9850100e41108200c203480c1c08109180600d0060303009001545c10403175896260b91000070040707020300319041d2000e50318004081c40f82e007008104525031310402c080880601c1c0e489600340c9190740703480c003a110380000c07205907411600c0500b8480c0c409a030f10602c02c4080e103080002001c40ca009012181c2c020340c1c040b070800b400080c0b41c09040c0e000801560362090042c80340e8034185100c1c540c0d03005103641c003d09016070340e00410f40111003071081e115191009002044104250307000d0003a8100c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 812742428 1250 812741178 812741203
    0x30c030b0a1107020609090a1803032703020703060207020a0504050f06010207090c0207060c0f06051f05040209130c0e091005012607050d02041a07051506220f020c 72
    0x25103205500d0b00100941643c0342c06400a22090900e0643c806202c03829000414081d40f880c0c0d2200303042c11715a01c41c026000d40a0180c0c2c2d0010703084a103940008541c020390303003500008000340e000c45030009078002101000c2d640d01c8840580c0310607281c8041001c1c2d280503000702d47c1c03041c00c140411241c1007000105038411300c030980c00c944040783c0d02c5001a08440525640e10016007000c007041c403816001d40c03604a0050b114403918024295583c440004441041e03400030312960006811081d5541016030b0301010748400c41e421443c00c1318540000d850026002e0b12403040c1c5849801c1981c080c2e0203203410483d5040041c101030307601c3c03030704900c03062a1900071301803540854030811940d04115555000131205107031503244104a1380301c509080e540d40c1c0203850002d0740c07140c00f00808174680b4155605806040202e42000791190074615105003884020780700c0d1019282d911040012a5480b010b100440103400041100d013060040317043d0f0090a400d606e80034040d4000100e00d0070308103002501ca003c000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 812743678 1250 812742428 812742431
    0x62707050d0b0a060e10200c090f13120c050d0e0118051023070b10060c0b0609070203040f26070803030a38030d050a0203041806030c030b0a 62
    0x76039120800804003c107005010003c1c07584240c002041c24a21040a10520386003400340d4440c2e50344455144072020b84800c00407540204441e102d10341044442e16070420728180b0702c00002c0c0340060b04560396500004010f03103e00c1d2915148604035002c0e0802c1d203400d03038001c02624100e0015400103070040b12003c4490340040c075122158805002060421015500018203402c442c8000503011944942110800403400d80c10311a044184001040103210440c4221030403401d500c1c0c101140741a04406610403414800308103000f40004030203400c0c903a07005104564100303545d01c0303000c0102d14601950304000c4003000b24920100e500b14403410000f9010400c0c240700301100a0320613620ba01c032420782c4244800380e8410f0002c83c005c4070181d0842d281300c804a80309044540a425001070090b85007040800440d044a4241302c4c86041c18060842d880c480703420800d24220354284000d41d07c3c461841078a130b8022000f0318a482602e0150072100040d60030038a04000c045e100e00740501d44101c1a031348007541c103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 812744928 1250 812743678 812743691
    0x1011061023010203040b1207020607030902031005101205030c01050106022413020604060f080f2a360319080d060807080309011b0b062707050d 63
    0x1808088080503107003041c20809100c0d14109080c0d80501e0303010103450543c0020b01c00455540f1054026050052203400c85140500348414080d040880251500c0c1c101410f00c1c41900158a001a59210b03000e81d440b00044c8550303070512101d084001e242c02414961404842000900030004041c10481e1241c0c0c00801007a66100c2050b60f8500c88460000d003034070341c40262012a0741c000c8040ca50310040c07101540c000c11100342e0001e952503103d5004031000c11321808202c03507220780c00103407142d000802c1c090b40310715820442d407026200d01c006091503080036081010594521a190f040d034000b0b820028040c210046051003001807611110381d4109140c400700e0522405280c009001c80c2c1550340080e1040d646040e07901d690680d0f40c00008407400980d100c400c0010700000c1003040c1c0c1c0042c102c2d2009591141810720004184030414505103420300d443c4411030010480d04085550070840842d00841031040d01d6400c02642c06186a01d41c030b1240f10341041001686d0418014038020700aa070042104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 812746178 1250 812744928 812744941
    0x210090801150e0c0412140309060d0618142a1617070818041e0c0e091006031d0f1c0f0e060a0c050601090209040b010c200f101106 58
    0x6401140300301da926029451b10900804c1c12514090901a40c21050fa880c0050450109042d54400200c0c030321038a039038200401002c0105652000c682440c100140300c19040740701148500b030406000980c0c9568a12002c0701e80b041296804a101051180641d440740581149008000c812060030744981c80380c056100500c5851400315601a40c0c8101755a05002ca950007024070000741d110501e402540c0c5140c5206500580c1070f0010707010000c040c000c10055503501009042072035807007419000b141484140140c114103080708609444280c0380024400302140a01d081c02d00c0c0210b074140c0325006412281c041d000c0c02245243c03a09110303811249210040d04400c0304c00d241005031401c005036a02611301402d103819030040c020040700340743c8200c02d0344e13298a441b401c3c44800e03804858916400692984241007d006019280f202400c0c101c1c1c3ca4201600c413a014039120340c0c0c011100d10303e055a00b00c241ea551402030f048103032014085115040032001c024200e1280c940c1e20403502c0c4109400a1078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 812747428 1250 812746178 812746201
    0x90e0702160f032a150c0b090705030f030f03040b0c04030c0e04050c0607050c01080c0c1504060b0604050a060309020a03060507030222060c240504230705010c0210090801150e 77
    0x30200c4040c41314070540307454102401201740304040b40400f081451030102000c01c3d100546980124502d6003c1c0c42d10b90310304000c2615000c502c2d0502c158540047c0f008040d5044480300780c039440b0b50000300d49000d40c1c2d02c034071440c5014841c40c1c000070010004030f42e0102e15920030902040c41079124030125901c850100c002c1017414042c400d0001c100da8441c8a0034070140d44103000309604403094105081c280700d5414101410803070210f6a1201a8404104000c288003007400b4a22500c5400d0329441c0c90103050101003840c100e0640a0031040c5606c1d91590310454540d00100700055401800030400c03810b24402c02000f81d4001c03031022040715000828a0026410b20701c81c00d084408507200d40d080701c0455a10342c00b01e030b440c0c24108400240741c60200d01c10400b013801110b01c1144500d1840b41180c545039903008078031101502c103100940c420f41040c0041d0360080e0b0030030b58807501100e00e09004206000c0c216484021a0025181942058040030303d0511285403481078980c1074414001565904c42c0f03601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 812748678 1250 812747428 812747483
    0x40305150f040807030e120d032f04050d0809130606081f061d1905010f0206101211031b040f0908120619060804060605060a090e0702160f03 62
    0x1001c4083c20000703040002e0084001d083d0f51000502400d81c4103c1650610382004140c0f81c0034070101e07440300032072866009284100d5042a10201030340400155004400b0b416028602900380281c030f01071061fa0500020000741c440c1414010076480d100b046450301c060140007544103140c0400c0358440456081c0040045800580b60b0030700070041d510f0700c1c0c03075400c407007440c16040d101d0100e03500c4e6000f6a0058440d0616102e203070b0411040c0b0340445182500040c2028031200004045411a500b80041e0603040700510044500e112204140d140301401e00040340c00c01800c80680c507103d07007120a009031180b5000700c0e000110031034081006109210107241500d90120303005104000c20801090722401c01e4446070380290000d001d1403100189034913440c007408007035040440400c2c2044200700802c100d50240c800940002d49000d42403907800136000e4a202214066640d840c7e240703400041c03400c1e00c01c202c4001c0caa0003454122042d03a5550900280e920000e0005542c0441004102e0210741c0d0615610f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 812749928 1250 812748678 812748683
    0xc06010b190c03080f18010603050609120313030e0a0803190306060c0c180603080a0302070620030a271103011b140705150c031e190506060d02040305150f04 69
    0x2980142d860400022000400414503003009010725903a1a84840911488009d18402c1c0c1c02005c0030704204200c03a103000700301549260110f008204100d814280c200302d41c071040d80d141c02c201c15485000d00004e4000c2d40c02e90041c0e04240302c00700f80d09044c00c0e145da0030105410919102044002c1e11444121515074090102400e4807120300b20821038804491220751440c0e1800b040060030985903910021070360300c00084040084e03000b14500081c00602d12542c990a044600c1090000c040d1004110990000600414460740d42e162a001821541c00103040c099558030028040c841092a203040e80148000d1218001d610344098101d00c0c000c40ca8100400a00396102c00c01250f0060140e59416441500c0445250003100040d11400310004490342c041d21035032440341e44070701c0d03d02c18225000508a011f025803030071300002d201c001403030031103d481c29a03000040840d560340d5000206c6c0f950f224100c02c07a00342070700c0010000207001009c00c80900c403249480d21488903860300e80400c60101429a0f01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 812751178 1250 812749928 812749937
    0x170a1b05362e0518040e160e10060c0f02090702160b030c1c0917040302031c1209031e0f0f02010603030509040f1503050102090307080316170c06010b190c03 69
    0xd00ca4103600541c0500891340038000303c41d4102d40400042000d07240c440f0b030724640e25481012a4920150204080d0000d09042c07085410f081c80c0010320750010050714403d2005000c1c20040040510445250312018207801802404950404020081da602000c868103444425102404070314400c0d900c080703902401c802d145040c01c221040040001c0d10800c032002c000c1281d9a440078a00081307814500201400f0550200c644071850760042c103042014046100303510582e030041002070036400402c25842c0324103861000529502900e015140502840c05054514101000e1480003c0d80701e1031039961130a40e552515030366219010280c0c00d80703109010060200f482400400c80c10304140d488040f65441d21381000c101c1514155900400e1140b81d003050f00c5c40c0c3d40000b1181c1050500b08210b500501244000714600080c40200403c46001c10b00000d024032100c3c2400328480301400c00303603125000c0e071030705403280342d6034900454185500034042038003901028550503003032a000750401005075401d80c55 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 812752428 1250 812751178 812751259
    0xf0102011404112b060b0910030303020d0603170304141c1404150e010e0d02090606030a06032a0b03010e0f0901021603170a1b0536 58
    0x8948085012420206820404c0d00e0313003d44040240c01e800c2d80041c411440140e85484050410006640248041c50f014000c0b0b81c052000120181c1010402c032505850b005884907190200c5d04040d060562015011500c810403140d0007030704440040d801540308462001078221526000c0d5101c1068480404c80810200c556501103401510410841d401d1104070601d066110006078a8002a000718100041c40304402141a56040a0340590403441182c00380381008041c1d001078204503009112a000d08004000315211045d190040e5005d558000c2050f50075503603510741c807107850481d11000000045030044c00541407001d00e0469069510300d12040500390742d036403c44000e250000e84140601d40d802c202445207049421445032449110340d039546580c1d0000c03003000128000213841500361501d05940105030004e4150b681107103038100e08100c0c1e01c45208040d001001c4810a599a20f503840e810765260190f00c1e0100080e20344c3d41c2c2200c00650140d07881c1c40080030210000c2000010190704030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 812753678 1250 812752428 812752433
    0x203070315060f0b1327020f0903010204030312060b090d020d0201090f0801021b010c020705120a0f060903111501290d0626060109020d0207050d0e0f0102011404 71
    0x804101d041285910046030255a03040100e50341d00da65440381c41c000101045042e44031000d5a1904014269840d444443d142c03801900c0404a00310400640700d079a0000d441d80584583c1e10640f00c00140040c001c545403a600d08028100d44140d401c0703003168514004000c40c1843d0b01000340c402007000900500b101540030342c24802d800d03124040c05c1e030511860850005081c50351040e000302a151520000d43c5456152101d01598110441490800d905180ca0882d0090340000d00c0c9040b25800c503002e1030f442c21180000c80c10060707516005000407285803540c2013401159002160814800d54512582007015650980c55491500307603a0400450440104440080d0740c0006c84401307504400388414184060050849601417400055100e4a8000c00c129056084030011041c19800700d06081d80007411610135240c8105008802c09554045554400110550b05440b8100d82c4101202c69082d031288014088040a0b40d0043c4901c2016810a82a51040c0602c0d039091400024401d40c0340c40340e6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 812754928 1250 812753678 812753693
    0xe22030507081b06070513080105010b0d020318100207110105030f0105061b0109050a0b0105090103170f07020414060906040911090402010507021f020d0807080a0504020604090f0b040501090902030703 88
    0x100c000092603e001c00c01c4480508042c0102401840740da1900c9946079001c1300c8108501c46c441d4041c2d010b5034076160041164006440807981d40042c0349030700503503940e20400c40c4084240c4a29140d22140300302e003d0101083c5044c2d00501d0f51a028600402500c06030b00c00440301c2d4442200c1900b04072201600401c40c5040000c007400c41e00109003038080c02e801c40314040c142125a04d81058803640d010920748014030051059090252105481c8200c041d811078451801d9106002c09000c050840003803030b01140d201c1c070300035503034030a41c020300c244829406001c0c00a806070040c1c41440c440d138491008240f041ca02440b5401174158080342e00800c01d42103034200f0000306002030050381404401c20280700140d4034245840c40240c9065449424503e01c003200910340702c00703d1900c4062101070350a0020041c1c0282c28190b021804030404240caa4642c800700d02103014548c0100910f42c142040b0b01c00d0088186c200381460001568200300c03e0b80d8600e8000141e03401001e001e074064000c80f130140040307200e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 812756178 1250 812754928 812754937
    0x1a091002070b1c05010807210302012003040c0501030507231b030301060905100503180709020a11010b1c03081308031503240c0c070803040e2203050708 67
    0x10300607503040d9035a0348190902e6034444486946046899100d000b005a001e00c00c503800b404e210b000130075060f420003807550b58428056151f0082454010a1801090710075003010200301c0112581551100580070a081950005d0301c003115054409400410300394030902c00c0c0c9125040070780e280b02c4044805519540e0850b4140052940d140c02000301c55010880548811114002d10004656a43c50000300921400f2150400303403049458803450400b943d80101039070b8000056501c081415a1030038005071a004242d0b0110344240c2c0007142e020103d54002c5140842420084001d009401c3c0d03800c00c020f41c0b4041e890038483d80344814059000840d01c80d010099002c2850302504050310080e1329940c166030000c4990240c0c0740d0060501c04c00605040c00305000c030020b48909420115603251600c081c2003001040c000c0440301c04119061142400c010f2040100764410a603035540d03840c0e140010102500b203400c80120804038100c0c070340c080c00e035000e8001040d030569201c41c14a100c9030740e590701070ba12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 812757428 1250 812756178 812756209
    0xa05011206051f11070509010302060c0a06051014271f0315060605122a21070c0308070c0f02060309011a0d0206071203090b0c0301050a1a09 62
    0x79580c1000c030b0180c45034840c1042074200340208403442e03c0c800c40000c0a030341c4480034908440d006290100640d4407400b010605482e0704880c0151134040c0c145080d480c2446d800806006242004140324130f1003911813046080e00d9004007596138425030b10f4203018000c0180e00c690804034440381c103850a038048113003a054001d00b800302103038108a50004045000480d5400607250540c020445080c1d08505100e04401455542000d40c24410941c00790f0160341d40044c10319500c41108140d402c0f10550030003103541e400700030826464582d07954030103814112134007003801b81c0c1e124442c4010901c4e040c0a000c0b40b0403001d82c90369803402c603a6103c0c80220f401032100102203a10940264140c00141e4804010f5072040000000004d8007145103a0503410407a01c0e181550b00401c540b0b44150050780b10b1070b0480d07030199080a0760000072001050300310300402c2000d2024100c3d007180e4080c0504101c0780402181264422168a002980c84071218071451014491590709120101700e490482e003041182c0c4803a654 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 812758678 1250 812757428 812757431
    0x20313050d0207060f140a080a060b07140f0109050a140c0d080306010f09080d0c0f0503120a0e06061819020d09140109122d0804020102010b01030b0a050112 69
    0x60840c0d454600d0109481ea07810050b0f0403d05050080744c5d44100340080c0c0c0d00f060b00e841c000251034000e41e901c0d60722074000e0381300130071440c80005880c1071560b4125100a210030390010343d80d900107084c68001d42c002c4c001504020300502c4078041a951050160b004d0582c2c01ca005003110310710360303135a182d4400380c250450402801141c0c0c1c00101940c581884070f64060091044035620703d0150001404d1010302582c450078800c603c10148000705000941440017006400d1030440c400c041e0404c0080d1130320000000303003244000034045810355442d80410b402030740c03505400d100307a4200503111900d603002120b0264101d15940d55040000b0914244940c1008002c0c42e80d045049184200e00141d0307002054100c0b4071a2180440e00030030150008200384046500000c105e080043d94031a0b001e0706404013202c0c00c1103203403a08100b41110702250640003a050100b2502d06800c0c07004050185001190181d0155181c040780e8a5294017078007a40c0a0780e00c00402c912802c0c0d0074980195800000ba481110005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 812759928 1250 812758678 812758711
    0x403090905070914030d021e0c0409081905070807080d0e0609160b030c0a0e0a09020333010e040c09212d061a040c030b03011b05030a0203 61
    0x244165030246010f41d483c81d80507810040d003c01007900200003e800b0f5403144018500e0f83d6800f04443c80c0340403800810390104146d060030986007001340c0d914503a00501e020014002c00c0b1071380c0c009041c0c041034000d44ca1080e1110040c251030f00e0140322070150030003c04201400c001051100140ba107034402013400601900e00c0441e06140c04021242000e1030b900942d020030304031020682500c002d1150f03c000c9480c502d8690751522039801110700c2c000a2002d000d604030345070382d00c3c41800c2d000b818000c5011500d926004940d4014180b0b980790181e01c42c1c001d41010084206031059895400e10f040e10346910700420f8005100082c40c00c001000c042000d900804107503003c0350054942d003a090f61055842d081020305212450340c1c0119210f41040085212904c02c080d11451204100e941010f4006440050769121800c400b8000002507405443c0c41c0712110030701c0e01588000d40c41c103c02e070003c2000d40400415035010140500e4040c0115106200180014803950029039010f002c20100d040035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 812761178 1250 812759928 812759939
    0x20040f0b13030b06180a0e0c04020a12230403030b040c0507021e041b0309110123130e0c0d110f070b0c1b030d051e0711010e030309010902030f03030c030c03040309 72
    0x1010019039030034400300e031182541c0d104000200404e000900b03045038210301d01403952001800341d0a800388105c14254841c0841e04000708010080d6640840c01d403e003c37024501803500400034075542c9403d030b1080385000710030f4502c0351151068400156015161180351649040c90f50000401c0d07510b0039a000d070f100d8024170080b03050780c2c0500e40f8600d050707100841c0702c0c80b452a001c003840603d1a10a410401002e40d080d9800c013801c3c1100c101104015000782c1d840e200c4402a041e040d0f0144c03c0307000035050750818480152109401482c07200c0d0b010b20200190ba50700400490248103413100070b0421407090201c0380100c0c16000b030640d0000c0b01c1c5904149460f101c0124803d4024041141c40d072903810105652280070018002c1c2940104d4513008041d200182d45144500d822000c3c14881c1003100c0b40d403108010007025800034142c024130400320307620b920b03081000d14060035200008a000c1e015481b031000035100c0000a03240288566681c441c1540da44800007005604010030940c1000910000002c030b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 812762428 1250 812761178 812761219
    0x103150f020c0c182a16121101140109021305090403080f010b070201050403080309160b0306030f07080606010c15090b06090903030f1920040f0b13030b06 68
    0x1003100c0d100700a012503c107038004014040400804005254282e541044400e4070203141003100301030302601c604810040349900c464103000343e8603e034600b480c04107441810701c81c4503c1c2d41c01e0901034076919801800000e60100e0b090f5544401110428144200107000d1032051f80c001d01404000900d521034815900e00004002180550f07094001c11022800c2c0100d940e0314054407030140c0141e20180e07241c074440b03a00003000c0b03108501c00a00180c13004408a19040700c1071003200200403110401d040495129091060150310503100541b00e4801d20517a000d4043c0c0200b0034808030b8940d0400b400d40c50750f0b0032005680c6400380500c1155455001c00c0c1200044c010340c8607402100780245081c004601d80340d0113100d484040a0021080d540c0706104000761011a065100d9202e910704480c403107840c1e034040d1041c1c050b00101f100c204004040035000341e000081c1001801c00c8401c040c11103000f41d5611000b0040da480f0f010034440f00014825002c0c000305506008490700801b018101d1050075200c00711090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 812763678 1250 812762428 812762437
    0x803131d1602101a240403110402070b072001150e070201060b160201030c081335070c05010e03060103060e0717031c0506010c110a080303070c05190206030103150f02 73
    0x150800c2403511240e00d61700f00358030b001e14070401001c0310010840c51140f94043d5402039101c002e240e44140000f800407525150140d914441c1c0c8984000198100b00d00c001c1c12210310300d0804840c1440f9144400d0070880d05010799802c1c1c100a00d02000c11504000380e0b003521100051032002590340f104000140b0014100c000e04a01c103450b42c0a04c0c1c1c1c0c0c0400e00c001010758031900f17040b204201e102d000384079038112440710300c80500da40590010f4443c0300c40c4d00190705000c2025021460a03d001d00780d0301000343c041d4000e11400c3e00c90a000014645c484d0015512503024020254040c0d0042c001480000e403640c1c17089007415082000c031a0040c0d907645803042c0c82484003030910090b800105646000312141b080c03603040f010390b0300c0b0180b08915045000030100015550054142801c480030002541c035244092400761410409490b43e0303140c05480074199000071401100c062140302c072045007200020b1050616298020030052641c2d107180ca80b4032046c12030329615004142d83c4e54502402240c1c600c000d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 812764928 1250 812763678 812763701
    0x20f12090c18070801050618060a091707140301050906191506050c011a0f0f0d0b1015020c031002210708220515090a06060803131d160210 61
    0x640030b900d04594018444034060780424083c880602882c103c60700010000801e41e24291583d90300c401c41e0341303022201c004140d40109240040006800070060b13021400070107490210080440c80310241d000e0500320b42084940024940010010605160401030070741e10b09082d500c00801c0044030151a02c0b801c11f00c690200002c43c800007034114558800303004154600e003620360742c405410002c10100385400400003030940f1850100c0c0356458203079aa90f41a99034180c02840c4e440c20b0745400c283d050140b4003140103040074412070300000d6a50a00c0000c1c907021142000c2c02500b1a544004600d0002e50071003200004c3c0c5103440c004071031a4030000d01415104a0580d074a0443d5801e21607010070104690340701111448900c0c01914001c178600103a000b01d03400b00802895030560303682c852030341000100100109040d040c000f00059445001010b01030310703a400200514543c0c0e9074800840b0450728042e0030060b64010000040710210182c1083d900f00040c0e00642e00d06005030031240341201ea0400d500c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 812766178 1250 812764928 812764969
    0x24041e080c0309010e01030b031c0309240e061b030c1902010504060e0f0a0213020f030103030306050117240103110a02060406050c2113062d020f12090c 67
    0x8030700f059a401518015a0341d03003800e04010011900d00440c0e214075002c08004000300d0010f0401300303035900c00c0d401804c400303800c1070044260150b4000316402440414040e00e414071b003803050050140d1030100b01c0300d010300d040130403850f518a040c222180880d00001c0c112030039258140841d9101801c00301c0b0846c1c1300026071b030002819181c2441c00c2411030f07000c10007103231041d03111105034070052100103041840c09030111030001034904034941a030041c1c4114100c0368001e0002200000405030590410320564600340c85020b0b120180040007046d00e5003c6443c00e0351401a8082d0011b4034403c004044840e803411b00d00440d651000d01ca07040c0f155401800198016031055040009000c0b85104d42a0000126003400f407070001c800c0d0303203900355a1040002c0481d00c0601f0000c100d065581c0e20700403215a50040c424480180c0c1c007514408041030036140d44180444082100081c54454401c581458900c0240d150501c1604030401002044c000d004410714070458088510035074480301d0101405090030b55 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 812767428 1250 812766178 812766187
    0x4060b040905031e0f0a0e0d02031e06090d12020a0c021504090b06030405030910031404150e0f102c0a0c090b030316020d0b01060203030924041e080c03 67
    0x30700600c002c042e13071010a101c0c0e002d00801c1001922482140c1d00c0314420710b08101d40401000020b000400051402035040c421282900b2214502c0c04044800d0406134007960708690301c06c1c10700380c3c40d0242c00c1403450008103048840400b801103940640280c8420380b41400c0030301c60307aa0100d40a440e00701400604581c1c045000c01845407a8081d40060b22005c1d1115802c1d0b048c103985107070340c901a08941c10303c0382961607440303d4207910942c40007006040c80e005800d006d050070304000540100d0801204c00540c00c0c914420811900054800e50b040401ea000f40300c22904140410300034241102a1048640c03161505640300e0f0311400c0080f950700c030380c00203420321f10140d2500400400c4103a0240386602c3c2001c1c2881c0312a6004401d460140c1c0498039050811011440040d00403410030900070403a0014000104107981d001014501c102d10300c0c421290042ea403441e151403502441148005502d0003000001c0000343c009400d419000074020040c80741a2880c0d80701d401340c0e000300704400042d40c40880c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 812768678 1250 812767428 812767447
    0x5011506091a040b030106030504080c070605091f0903020127240c0b0604051b0d091b0503070306020c0307050f0102090f0108010803070b0601120f05091204061704060b04090503 78
    0x20205102e0341c000c015000c1c40c19103446212049800144540814503684030f00190a10100c40c1c101d481201d22641900d0500e80c9072070000c0d1051f006005198040c228071080d505006101205080442042e5201e096405145500440e80d0300441c1448189010402da00e031211411400078000140c2002501c080710070403031103e040b1200a481020000304a807a81021020900b18034000d134006806941c0469299203c081101405981205641240b500040c0523044603440790311000c03a50740718221221103c80306011044210040c0d0107059030541100e0f9003040007aa19030f0052000350706103c1036a003440041d49544e4100154480603a8407039400056038001d5107802c90411503041004d00b005e0388a54142241c155590040b0307500205840030400200e0351a03030192510b8840342c3c415003001e000d410030141c03207030300500420755003008a4815403030023000580d020020b840c203554056442c01c1c52100c22140701c524040c400351041d40c640c1d644e00c440d12425100c40c0242549140110004c542e0780401c6d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 812769784 1106 812768678 812768699
    0xb090106030b1f03020c211602190803070b0708070c0609020a031b09180b04020108041704171603080a0f0e10020a12170c070501150609 60
    0x100c40201015416001040e0101e6101d09a50300a41b45c41d82c080104010040381d0303403034881f050107036030700c1d00318020340358010360b80020000440c60714990012903829166420107a141d0f04005102c0040c4540000c07619041416032620031402c0c41c1c1040002e1425101100040c4119168800031042d50350704980c444c09140c1052116401390020400d401034224140725501007039080c800038100c40075802c51562985038020314129001c1c1c0d5281d004450b07900d802041219075000c030303044a0391001100405070029040070b400d04914001030f04016417802140e011038203880924000b09200041004e001e4522424180c14800301919040c14185c480c03138201c00d02a07400c024180400f0303842036800100409038034040e03402c4810541c040d41086580303824941c82720740c02030300e1940400d015402603c000c00200f80100300028111414080d1402d00d14070b15808800000c1c98607a0a20616110 = true := by decide +kernel

theorem cover : BRFrame.Cov 812589928 812769784 := by
  have h0 := BRFrame.cov_init 812589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 812589928 ≤ n) (h2 : n < 812769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
