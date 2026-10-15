-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5477
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:33.183537+00:00
-- url     : https://prove2.me/submissions/b9437e8a-0a47-4410-9f81-c5d652982fcd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 984892086 ≤ n < 985071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 984893336 1250 984892086 984892091
    0x506180a06030f0f0c2102010e0a0909060c030c140711120f030919080c010836060606091804230c040c140a050f12070807181d1009 58
    0x5024000c004d6401600780740b041c44030a1285a036202c0600000030f0114004002c5000d103103c101c0503500580804084500050203401c409445480d1801119440141640c100e59900185000d86400d807040d1242c8041d582400d041480007881400d0041c8580d10dc014038200c103039114401162509001c901540480600f540c030351480500c1c00c02c0e6640c0211100601c01c4451504040b21520703100b9021042d04c0200e1b01a0840d030b4200c0d8010b54125078042c1818150441249a0613030006418102c86100c40b20082007141c0b400014074254a0020047e1496101d034004100c44411551001c10312050b4031141200615169518103082d0304091380c2c019200003030100400f044241c0030012902c0340949074112810001c08641d031804840a640d403900c0e80d80314100410460b200c0901420181003241c1078100c0983c80d1004c80c45200540c40f000380c50172400304009105210030359402c104960290320481e10030320f83c0b0f5454034031381800004014912002c6800140080f980288440880c0d0000e0200c0f400309 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 984894586 1250 984893336 984893363
    0xc03010f120c1512060509040c0608070917070612050105220b0303370206190603021c0c150203030103140a02120c010908011b18090507031508010506180a0603 70
    0x10304078481400c0e004c034030107240c250b000c64545440070506001e990040300d0300c0c0441c0e040010030b4407801400b5140c902031203144080001c80414403450700a82032017907006440c0c0c07540340503070280a600305889001422414007006122503242c03270140c0780e000c00f41070400c1002e030144601d006006083c030003240c64050000150851a1b040001000c20701715007014690039424444014403410320706007218180043c1c1101c000304805040e00c04000100c0380c403140740082d4180c3c2e00d42c00100c105588000b4030340342d808640d1a180a000d4a4200e440c02080b612850030304d04205140025141d1105000051080381d40c001c0321030040004105014110342d02800328030b0000d040890345591030990701e01d0680091a04813002c25242c5042c02606081d400c603449607404071000c4807080e00c1610310010040828802c40b140010303071115030f0045a0182041740c4002416010310b40415481316040d8010390502e0781000180207030394507100000010002b54184014aa444015000014244a900140010103200718 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 984895836 1250 984894586 984894629
    0x2b0909050406050609061c0204240e010e07020f0a0803100e042315060f1f031b050408030901230a02030c0d0206040b010e0702011506170c03010f120c 66
    0x3155000c0c140898240f103d0b5a107410804c4101d41072403c1d982810314000d00700034014145038105500340c0c01000c0c4140b4002b5500d401030088500d20782d000c01c1c1010a8100100071251407017800710341101c050320141008200416a40e41e4465096100405882c000000920034865002d2032401801c0640120081402e2501f008068600e00707040d00d0502035680583c501e80b056002030700001800c01c1009480060303480ca02042106806c8072101030b000840c5421441070326044203541a0002241d0320009000540748801c0e4600c0301d215071000c0240f181c10041070024600c0041a1034942e5404d01c0d0003030b26004039000900c050001002c07103455803070780400c94000083d00407014140d00400802111544001d4110407681ca5806407005040c41542c1401482148100035199607c00c41c240004514104101c07c0c0c1c0140a4040e40b106001824803141e0620400d041c0f211580c0195900b01c06905550400703000520110381c0d880350783d02c0b01518801000400c605698071600a01008084c09101e1a0102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 984897086 1250 984895836 984895841
    0x3005030c0105012420032a1b04050901060302090a020417011a0d05070f0f090c02060f07030905010b040603030801030b0a1a0f01030e0f1c022b0909050406 68
    0x8010151542410300109119180b02c1030550a41d1408400c13134900d0010700c40503685410310702c482e800f00200d115101070100d0707810001042a04800f0302002081c07058004111440382507a001d103485a00010742d014510386d03501080c0588643d0032640081c20f40c8403408882d004180c1c81d80003e400144000400c0704c10f84003580504200c0d06c1700491000c01d18401801c1c2401c84131160034584924546c90030141c3c0a0030080c510020180c803031780496400c240c40342d03600c011002c42e0394001910401100c005200c220541e01458003c40c109000402d02400d003c180c00c540c5200080480007015595081700043c84130940090100300d0016108001c0c003901c80c1001494400300b404295802c8003030201040003101c2d244101c01c00d004183c200342c6120f441040801102030b000030900c0c1d0401d5190841a000104240007a50f07044c7c4060004000c110a012030340c559403868656810155080001c60200c6030011013a101d800041340c0201c161090801c3c80296500303a8a41c010000c058034110802013040000d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 984898336 1250 984897086 984897097
    0x130203010f0e010b0a050604141201050f01090c0f02150a061a13080f0c040f091e0311070b03060d080c060108030c101a04090212030705070f05010c0507300503 70
    0x60081c040718007910180f024031013441c4512501f01e1400c010030045840c00808034000607200808031054405800c84250948400741e40e1070b410790340184010041c08411b8401c2c1802288107050084214410300340181d124005804c100403541020800600103c00710790162020300f50000864442070f8090245034099007081040c0e02e0340914502e40400c40c0140024041c216018010041000e99000360610002d812180c08400089448044101c006040c50440705601610a41c201d2409041d500f001410890f40482c82c001c1904600c0043c03100c085140304899000e2019103d010580303000d440c0c00c92061065021a100d280a43c3d40042500c4002000500641002030216000740d0000d503a03110807120040c030007121000c12000c100c1c04608160b080130300483c0c0001d11703250394000900c4013541140d2200e201245c407504280421310810a802510a001e080d080c6030400180c049070b80c8460307447c4e400e8051501d0418042402030040e0301000d481f0b01c680c02400c86804c0c8030754402c0c03822a030703a50040b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 984899586 1250 984898336 984898361
    0xb0d172109070f08070603091a04080702040b0a0501020712020d02151c0b093d08060901091e140307080c010b091b0702040227010906030c020303010608130203010f 72
    0x5840c400148188095800d10503284c2caa0090009146086000d400411440008451460b86540302c4014181508080b920907030180c402980d8a9505204001c105c404100c030340d920404001c036043c400c03030740e00281c41c000399805258888000401c074000107031911010200254401d010509041c5a5001c5801500c240d0404003400300540541200c02810b4800545400d030700800d2160000e459906044504558004813401001800601e43d806a40480340e49045a101801d20802041103001c1044541d521000850081145a01075515400884080000b42c0c1c03900d1404c0d0003420621103005030801c0c1c2105180c048a60f500c01c54a014450fa400240c00c001c0103500c1c0c0400c3d001141000600c20703100303074800b25205015118045100700035030098181a43c001d40c0c00c2c02080300e0103818103005024002502540200e1190b01070006010b002d1a8003c0000c150038a8070004540d5000030507241518500e01b8001d01595403208000a09620900065490741c02c1c10012108000d156001c120303108203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 984900836 1250 984899586 984899593
    0x20715020a020d1515060203091809031602060f03130309080a020d17130b25031e120906060f0f06092907030207090f0b0d172109 57
    0x1544000d03610381039580c00203504071a2442c8507100280c0410301580ea104100c0100080c0d01c1190710041c2108249a001130026a0001810703e1132071803c604000800c4540c8080d1421034540701c45100d8aa0295a0066600c0c1d1045c040d400d085590b00410780c0d0402d02d24a0380c0640b00d1910b0f01001880000640c1e003600412021a8041081c07000401c504600980203001414041000d03a5031000303440803014003001d0132038180110300035503000040020040000c82c03005501c0720a460100b5081008000b68543c00b8001d003002c00f000280c000c80443e140252240308240b03110581041900c0400803951060800c0d49061084010040181c1c801000d075210480d1141c010354582d0340b0078001c242d0a0240c08041201400d040100c90003240003408407401d040d001d03503407208000060006d0790b040707420200c0143c0c102c2881403210382c2c0350b44204d0120100c03802c028480d0071a101c0209041d140e540c40060320545066030f084a401742e85000700c40034a0038000c09001d01e06800c2050112903802aa0718050500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 984902086 1250 984900836 984900869
    0x40b030a060609120f030e0a05031e0106170601032406030605090d050405030c210a05030703030b010504050112020c34050d050712050a05030406050d1b020d0c0614070207 75
    0xc0c00e944804c080e0b071092140b25441c401d03407000c1c0d03111100c0010803a8011740e003210100c0e0a880a11032011451240d000c940c03070005d5640140341c01e4580c40c3c1c2100e03140224503005441659400140719044a80201c99081441e02d440108100359240d0011202c40b10708050001040182d9948100c1c411030b14501075900b00c43c2c14070012191889103115040c3d00d540a41414001481c0c85a80b22210030b502c480c468490385142d050482c00c3c4183c095043d135035500046091410315405000e00e5070508001d1038030b113260078100000a4000c11603a0b0000141a6002c1203441e400b080410040300c030b051b4866402d1500c41031074000426010100c190503485070048500024050801100c03c0310307259032010281180d981407007820000c140780030f08196030031b108501c0d10307101145040c80103202030f108503520190b036003000c030101c0020b03070710201c070254000709450320000c0900da40410301d5461a6401d02d0070800e407e18908020000d4248441d007180341d008400107220000f070300010080c04940c2c4002c3e8000009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 984903336 1250 984902086 984902099
    0x210212040203101505060d061203020c180103080708031f0f06030e010513080f0d020a02070e01080a0f080c1002190f0908070614070f060b030c1e060d02040b030a060609 74
    0x10303200032501300c400c1c0480726804d022600d00400505a4801452000140b44d0f80d95598a003010f8002941134016801c004001e20103401e22220180c140565031004088952455a0301d0700700b0701c1410805010f26034080040b07151107100f608100c912140b4005107403c070b039898101400074008075200c1d0601180c500010031034090011300a0030300c209a0360006a01140094070340c40f13201d501010203a00e02d01d60403ca450307640d52040c4040c0907607000d981e0080040034141140900d144906070014003544d8449050030000903684c203c4917085680c047d103401d8403a000c000c070103454000300ea410042d440340081027200640101c440c4110003200b20b950352440030003c685d000e503940541d5009884180e00034541c20700141d801418a8446020f8489205290040d0b50721008040303964440c0440f8603584580d40c41803649810070802c030303c090044030140f5203d070301c8801c03e0041c4101c0480e038901940d808611001900d219906603801080d02119840d941d00d000009000108058056000441c44107100401c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 984904586 1250 984903336 984903341
    0x60906071103030105120102070506102916020102070521010b040e0d0507170d090b010803030c0a14090307030b1b09061602123a0c0321021204020310 66
    0x1601c4114040d501c1c1da400c10342844500e440204000c03410399020800c00700003940400080e441101510f1082a0042c182030006070709001c020703043c0c100300b5007042d2220304044001084441c440d9584264110705c5100d403005074144541c07580456804516684140c5155a0f003212141c1d15800ca01d008000408202e81003200703e4001c0e100c5903000d64004000d06840c580282c00134044e0500030703180500d0b4011112458031a95214150140280b0707190002c503001c01c01c41591140c05006054043c5085142401485a40d0300515410204001394201042588a01407049074590300300501a00c4009071a4100240064415914114460200340e044160404c3c0d58055803100305004200310304d00a1800c1401080c2c000415003a0392264007002e0f8010a10001c01c410b08003416180343c508000089000308480001070710740b404d58000c0040c0400449140d001e04c2c0383c01c11903814140302d030008107040b0340410170a803e4501801c9280c4001110b42d00c02c1c60745038146224920271001ca0360f01030b180d075074003105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 984905836 1250 984904586 984904607
    0x60a091515050d0c0b190807140f130305010c0305071407020a143012180108270c10020d2307020303040b030103030e0d050718091406090607 62
    0x1400c80040e0400c0c00145402c002c0d0744103250050013030b40c10362500e41402d026654016580c001514400302d60114450350030154465001740349044c059880465103801c4209882000c90440107480e0000320b41d8013440aa0382480d0186030003d008026a044024015004013000e13600200825402c0c50292440549032007100c030041d030b024101c854030f00d20740412400c40104500309558080402041001005501103614203034074002444101c0000e03c41360310a0030080300c4024440031100c1003124041c0005200c503580300751034003072030000303259919100b101014500e40140003000448105640714010702c00501d04210000450f8055041c03000d240d401e9a4562a803007445010900c005200b0f002000380040c1d0310b01c082c0e07003440e00c1440c010380c0703500203806d550003070300180720905c00400180f041c150b220381001c51341e02055a1000820172a0388645545003210310940e803244d07200400b01e480c1030345260401c0045550145000101132924000300d80c03030300800c80c3c10101700e120303c000040c6000c1c0f00e50320030b03003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 984907086 1250 984905836 984905861
    0x140f0411063c19030e01020403020a14010201090c03050f0607080f04020d08130e0f0a11160c0909050c0102010e0d320c1e1b010804060e060a0915 64
    0x120414007078240e80191580010304110a50800703200101407808450090030042e910f4206070a810401000140480e89202d095a103660310602050005840310070002007505c0148048180019078400102d026003011580101500d01c851000010060001002c3d8280f014807000d031141da0f50b840100b240d01003401ca8040e18034025510109015060403039003288554014410145016085120407419840c0b5a010640d40391004c006c1104415203e98050f0f003150200000b48a10040444030341032074000c803220f094100c03819600d090100086805880010801804c00703000000090400765118148101ca15000d035082c5002d408a624010a07100f0603407509403a0620740c48101008001030070403042a0201003481e042c941c0440c03441c3c2174050320340b032408040100010003440c11501e00340207048101d00f0144d13205180c3e0201c120604001c602e2030000a10340030b4803036a03d030b00b4031b000504540442c1c10007a029140c01e01003801b01d42d40059048034081e1709103040001d180641c103c1150044022070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 984908336 1250 984907086 984907117
    0x220501170a02070302070e0903071b03030c0b0a0e1209030c090c1c0906020c0d14031b0a170a0c09050603040206040504150906141201020a0c02060d140f041106 70
    0x1e0101c010740d405018078a000384101d40c4010f494940c4005030420549142c1f40303503407011425108010b100380040d1200000302c0f1200c080d09145643c0a4a85a1130480007003a8407802e80000d540e44119512a08910300003204884410f1003c6801c1545c80c0e05c4858128007038081d0603924411400c2801c003503801042c6403402c2e14030f04480b02820b01c06140c440212406102c1d1501c4402002c00c1d114000740c100c0a10b17580c09444014500a40a01686031020007103440020600c100212000300b610740d030364030540c1650283e64602e03461038101c0380000002000f803081c010000c24015010f42035804140d524000e9220304200c0b5407a0300030030001c0d00003210001e5020382700300401d0209082540207000503a031a01c00403d000307500c1d00c881d402903920a400280c41003003a40780c0340c01c26140410071035030100006402140f4120140307030014034240309020301a02038000056407038000c0c4c0702d03a406900d00700c0301041c140b500ca00b4036040d048a01902520240d4a0285004c0c04e103142d49400e07001c5a20742046500360 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 984909586 1250 984908336 984908341
    0x120d050420010e13090212060a0501050d0b0103020f0a051806190b160204111b01180302210d020d0b0a09020f0a03051b161a06210c030322050117 64
    0x10080c8155518a070361250300c5d210b00400c17005840c0c00c070400c03048400203806400c251031b29a400c023046410591100d44901ca9801164012501144166056940550340500458070300004141c41c085a0b42c0701c40d8010400015440301450705c0507815004500c2103414050a01c98482c0c006c0028003680079580500ca8100000800c00e20300b82c0110b03204510140000c15490030310701030881907030032554864481c00506800881080d4003032082c0f030b0003030300d5080c035000130000c8a480080d510701c2052841d150038046101c2c1c80f0140368180c1c2c01d8a0451000e11300940d0b842d511128200c0c00340c08000300080c02541e46c243c011894540d64000e07515a0780d0f018a00d030381024050013040f0040d003005085102c442d41003034014032251168400502406095a8007403001800700d203001c0c103000b41032a21403c607aa034840140009a0351303a40710b00c0011030101c10901500102c0004241c2480c41001001344d2503c8000703a030328030550212070203050710150740a80040b070b5030703076403005607a40c09013908030014281c10f9100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 984910836 1250 984909586 984909589
    0x20312072c03030d0203090717071a031302090a15260732040603080406081807051504080703050606090a0b0d022b030306090e030405090f0702120d050420010e 70
    0x5141c4c016000c508480016527920002c03110550500d008403910b4001000502000d401d04100e84844003050394405c1c914540515031058161200f80007d21803c2e480010412115458001e03100d50020034100c8801c80da560805000781e60400d004050364104403c8008140c0c12010600c07a08442c4905840740443e05508102c034030306000440b01340000313101d0b8064a01291264440c6030040e40c40b9100f11aa60360030404e001c2c2807090300402111300540080c00c03000e40703120042442c10490303405589031110600041c1c21004240210741205074a4800c04030300205010001134054051801556401007588900003040d060710902c003032164000034600080001802c00c0181400300c0421101d41000d102003148510440d0007040c031050f000603458070001d00c8140f815204e07409006075640700540c80c0a04d090017040c860b010007410280740a03036142c00502564020320142d06498060f0b141c0e5a40c602ca001a00001004207580a803510034101101c13240c40c00c005016695507110503190031400860440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 984912086 1250 984910836 984910841
    0x5060c0d1110020d05060906030a03090501050901140c01050403030506092e0e070809070602150c1602030f011e0b030616020f10060513050f16020312072c03030d 71
    0x2003030786405100392906450302081030701c05041c0501510001040714100070041001d40301001d480d46102c1d070092003034840041c0d081803609084a9080c00d015840d65420001a24401c0c050400b0302c04188000441900304201940141c1c450fa22944040046407102c03030601c0888032003100c28054000500d00c0400d01b8038604104403900c0e072503040b000c0e414123807101c4155007001c40a81c0c1c1c0d1404217008005205030b1980502452003d040148010084030764950041d00c102d2a001e01010070a07080012600c0c12a985413070500d200f1900a0101c80fa8001103c507801c0c000c0c180b600824400c003503030000f182d03100d080c14040c00740c040e2070040003452241c4624080700d6020019401c3c4500790b101b084c0e641c54000d0410302001d01c80e21048540011010302d840107000201a540105000b001d24000c10440d910014544040e0400030000b4500313030301e1201280c00e9156200d02c2d04180c00700b102031010048101d034809a07800c080052401e600030400d03502d2041603c04403400c00d54542c0b6400501800c074200341603a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 984913336 1250 984912086 984912107
    0xa08250309061812080c0712030504050d0f0509220207080715060311040b04150602030a110111190e0307090e100519090f02060a05030108460215031005060c0d 70
    0x802c040f6240460588e03801800070300300074400c40842c0d1200100800c1c01024000c2501a000324244507820760003c3c80300524510074880064851182e41940ba00146c00401c0703c8101103110307500456480002e81000c00300e6800c0007208580d00340724541080c2c0d100c00c0500540d421070303a1050b018221114a2010000074001280d80391f600581c4d2020850706e0036003001d132000020070507600515520849540d000b0b20351010700c070301c50501342e0500c1500030125400b0012102c0303006a5007414041365112540446800384422700712a890300c50310070b0100d14000e00c1e40c0032120700744000c011208100c04076000201a12030031501d000f061702c01e24030110981003603600b00784c5d007052080c00180407035401640000c0c655000381310084005100031005101c0c00d0010041000019040801240c0c0b104ca1408803044814260341c0b1501c840c0c91001d05030000e400048c90b03101c80c0580c0100403003a600d1402c6a03075441a003085603507694010302c250f4005914104039080b54640381404028101d00301784440c041e03d0100c0c0c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 984914586 1250 984913336 984913351
    0x31404062403140d03091205030414010212010f120f200307090b010801331e0e0405010b120a0506010c0f14010507140a0825030906181208 61
    0x7071103807071115007502000040c40c491202c10724041401d001043c509044410650705046c5841e58900100d4107804070084180482c0c80d2030f5070750765681c0c9841c0d00c1076083e5000c1c0410a40c000b045d40b025840e18942da09050b210400c408100c143c5d980d402012444141d144007914402c400001c25000c510040d55181446a032007955000710462480880c0c5098091f9000b0300d9134941d0f5012103103c2d5a8405a0756005000e484201180100030308a45c04161700c6084d034100ba9201c403648544d2009000b1003100c42e1071201c48841c00900e90304e552000e05900c005070380c05445a881d00c000840d1041c0b000d8142c883c0c42d801000100e00396980e40d14118010318000d0501818441603050780000102480d000091041c443c0820300c1c00420034080a5094a01c080c0c0b20b5418072a601c03448c0c01030014048152010240740c2e1500b03540f00c0d00e81c5031251036107154400d2141d61182902c041c0a540507015003141400c2c80c4190004c0000c108580c0c0e02c180d103210b80200040c0b070840021141b801d5584181480c6400900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 984915836 1250 984914586 984914621
    0x1f03120f0216120209150102031801020109142103090d050906070b0c0d0c030612030c261206060c0c1512011401020c0103050601320a0e1003140406 65
    0x3100d00312405032005684001000480021100f0440c02d00144540e0081d5420202400000014002030b4a030b009130204603c2c91403080300e40e03010b941c1c402d412103040e4540022003858010345030807001ea1100c546010b0505032306030452141d00d44003144000c40c0e11503495080503200407840000101e5081d8860816280d100d03000f4010040412240b8424a0252010541c1d45944142c1d0b64038084c25208100d42c04418549014410007182103075406800000340c1c1071520313400d100701624040035030455050549000280705e404405080070041c009241c0540020540806642c5040c1040360360320418000810540044805414600301b85804408608418a00d07508043e06160000000f203804d130311103030050844a19011b15560107010b02c41484000303207800c0c000c600d0b08138006098040f4042c0c003000404d002c6203180b181841548014000f01d8442103401d0707039130344500c100181800100c0040a03c504110743c45410258001c0c41058140390b844072040c00b00750303030310784603a801084d000c0b80c020309111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 984917086 1250 984915836 984915853
    0x605130b0a030603140a050a1113141503070b0702090c041e1518030b072705030d08040f080d060b0a0305040b0112050a02090c0f0c061f03120f02 64
    0x450540240c41c2540076035500086a600d541031610107140060609a5281c20054843c0040760011a03400d800a4000c0003401c44001940082910019412044207201d440c08000c406e0304189604440c0c01000d14145041a440c0c1c006d041548404a5100b0b00c1c5414104001010040c14125460b40e0b1008a08905034140350fa102500d090101c0344d5a0004180d0350003c006104e04074001a040c008080340340f5294004003010504014181080d00026081d04070810003d25071900c03c45041510741c43d00b2040c112092030103d07581552101a00071680b09025001d5403440325031082805c2072049d034104443c604000543d40314105c42d90b000074012120303603032241c2010428160003001091944034544d400601c0f45894100406480c6061304a8101c0024040980001c15030014518014070b404452061030b50b102e46418601610a8100041c1c20700c4000c0341310080c8410124580d0320803880001c000801e40d0042c01d00014221250100615400b050702c4000034051103100d00d034070414030500444501c1c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 984918336 1250 984917086 984917099
    0x1020a020909060402150313060b03120a0c05060c0f07110f0a03082205030706050c0a0605090a03080c090901060810050a0915051503010b0711150901080702060f01060513 75
    0x104102d4040109501c0402840b0450920f210003a101001526100341941072207405d012208201000150501d074585200847d2a6414000c0381070003200080410344d26501250003030920000140180ca080c05000009070380100e03000100d8a12400c070383da0319407805c05c040c0c1c3d0300d41c0c00c541280007c4ac2c100d000340c00380744210385510500c500614001c0c442c0d29102c1c1c0e0449103111030035400428000309800442410003c68400107403942c295141e81c28a0380e19880f0340d403000b600d04114482c0107010a03050006000c0d5480b0040b4251305013074007075500e444180d500c0c445c4942c005c1c814442d015030000000300041120ba4882c4a029401818402c03003d101141e60344005210709225801c414030440c2c5c0c4090880e41301c00d03411000d030020310061f14402102c1c840c800001c9498001485041c150200000b2000e080100c4108075554480380100524007048101455990301e8001180040c041003000000c45c8000e0700006526104441002800d010380e820140101d40303e40200e0510b0207106261070012540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 984919586 1250 984918336 984918349
    0xc1e05090a0f0c0c0309060507050f03040609052d0d060b0310020a030605090105130c02030403140303101e09110714010c080c190507150504110901080706051801020a02 74
    0x19051040040b81c10403551001c4821158036a0307110050180c200c3c20440041c0d00499100e0440d03816007005a21002a41407041c1814070b8020001c111340400500401c4050308059000c0680e10b0030f0300d101100104054004c40c441000000319030103078090320310903c481c0c50220a94520030b4403906011070040c402c10003292404c50240c0000c0c42098001c681c5200c0b9640c180f1404005110440d5911405e526000219028800c0d800d04000364646403010548024000c20490f801958400403101e21030300c0d0340d405943c40ba00280d6005070074608102001401140c1a003500307070161241c00e200c807845458405d000e4000c107002004c4e200d40d54801d110b50303000705d0032520700c00e11003c3d203120001ca205c01c0d8844004040d044000e010b60181c034028840000d101c1803101e040c0281094500302035a03070f10783c41d00b400c0b0360f501d560f41c00c9107540d613045c00c0400003000303000c40950010050580e070b820754a0342c0300c1c001107072514a503014a900107032041c0440e0200c500042150f145a01060043e42c29040359034010481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 984920836 1250 984919586 984919591
    0x50601170c040b0f030613060f06210609170307020d05041412100f050402100314040b0403050d020d0f0609021e030402040b30010219050c010f181109040c1e0509 71
    0x1101f240300584024443c0c603004041c000740898030304008080c20b003191104250300d01002201c401c590185400b08000c2640d000780070303490700800d0701680e0402c08806c000c4941d00480b0400014011500b1020315540154143d5090710031040442c206040000c0c00d01010700542180c010042c42075000480403440241314103540c1c100e01c031001085c0d500e00740c0180400d00082c02208803c06141c4070860790403100d070004854102390701ca10198000d0720307642000c980c079000c0c410750406268800500c60407241c074143e21800c8040c2c69100184120303031b900c6550314200c0c016403d01c000c4da941c00d080300c0d100090802e8000c5600920007440000c03004642c001158100504ca1074004840700e100012499010158507542c6298a0242c029894207005882d0508015a00b16805081c03000c08100300c400420290030078100307114190010420501040d2108240c00d0380c501e402d0703034400200f0f00d17855040c0c1840c05900d4401e503004190300e952645080d0300040300c041916244001d01c41b4841012596030b498607003150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 984922086 1250 984920836 984920851
    0xe070c1704090e010e030a080f15100305070807230c07031b21021509010314043e10050d05070c0b01091b050306060702030a0c03050601170c040b0f0306 67
    0x1a04528142c401402c545c02441c0d901007a91051004000c0d4039440311840368005283d11140300d41e5110028840150f500e000c0313051b42d0040c404441d000c051581580715612500361035a80f00c0c0300c2d8031141e10541301c2621050700308040c46081a02d41d0340ca08168402081302e08003000488007055500e85030501c00c82d1413014945e20b51080d50307800b041511020a14404040400d000000d04c1c01c02030380c00102c1c41c68015840e00500e10011a02d02c1d840ea003c0d6101a48010a542d01e090040c40e00d403030074569200000b03559030800c00007075044c124941442c6843d403803d0104150303441c605480100820050100c0c0c40316603410091b04000c1d504000c405402802d001e081c1540351000c4044481c50840070b0008140c002140701c519004414410003890100d44048451138203105030344e0f03103c13400441d0a6101d410f0000e501441000200c10030408440f05c0342c400c9034042c0b8141d03071050340c82c0c0341f001d050880708521403401c645c069003204485141c40e40c8801a441402001c0440950200000c21300b40103085401340c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 984923336 1250 984922086 984922091
    0x1051e03040f141f0b0a05041505031209031509030f0c0d090b0c0a02150d1a1003020301062304411305060604050d0f15060e070c170409 60
    0x30007042c40141035103405058081e000d00c00c000e41c061241d240d41e820300040c0c00707070703c52045100e03030b1b110100400d000d4040074005001002c00408001c17a1011144550b070b0091003100a80c208840000090710b90484006010307085070403200000c0c1e075270600060704695444c002040b040b10180d89074002030007124500310181024034041c50000e0a0f50409912034080d2060800240c030018001081e841c480035170403030300440e43c018600d40c102014000c4120714403071a407606100382e40402c80c0401600c405030301201c0004289001c82d000f141640002c1c4922070101d00c01c00318440c0c4546070ad108031451140170225450400b0741d5990445c0780f010f007245070312540e070a0703959801461400c0550f60700484400480d0605105a001000c41c5088049080c9018403d580b2004126503940b0034085034000c240041a101209001c1c0c20441d5540520b85000c88910141c049050b0142c0c2c0d050140004803024986642074681c0c4088090707075601208003049507941c0740401081102c41c0000c0213040075013800d4000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 984924586 1250 984923336 984923363
    0x151b080f120a06060207031518021c1506080604080c030d05041212110405130f05090102120a05040c0620072c010e0c07080c01050a0f110a020a0201051e0304 69
    0x82200703c3d29260051011508000d5007400401d4500c0d00c7c03600b00495401c40003540700e212000d0003c0c16185440000d521946800001904031410796610901c24021256030001812502500084807880e200760f120640000d80001c3c0451310f0000940b6902c1800001e6070314060884401900701d070011a011101e10101c060503032401076000440d103a00d401000c900300144141450f08080d180950f2191510a0240c01183d800c41d05898203d1582040c00300b4080c0b00ba81485031005010750091742000d0303900d1401c4000200b01d9880b034094540210303045020191800e0034158229809591101da14413040d13285040c0301c01c000010003a01c1c008099942890071000c1ea500c940500b140300c0104801110b1080b0380040c06064887c08289402014007414269074151614110315240290142007000b5441c0008000b505080c4d60090740440284000401004000001540040c007850b2070310401070340000d58540065011707900500300110743c00700501043e07101e403094182a92080358122541d845a500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 984925836 1250 984924586 984924601
    0x727020c0304150518040e0c030a14010e030a140904061503050402130209010e0603280603020114251e060902030f0601061209061b050a09151b080f12 66
    0xa0f00088841a403820b645418007a80c0403c00411549030114811543c4100040c21180104000718900030042c007035580107030482c149505032070745014004240d942002550b03818108040304542c07501c2d459490720610324103625506500d917041805030350342007581d80354003081c60001002d400c160704449560115243c43c0c103106102c00f070090580e003180d460740107100e5401c281c0e801501d40b2003003c030f043e54902d403259540803000d49000c030300c0700800f20480a44019003000000300e400040130369000fa21010030210411811103800e2055841092481c3c0130040132001e01004046140c45050003000820036441a0b900c3c0412032444c540022242280d441c40c92204605040c807980b074010901c603010704990b614182000c0c0c2550105503c0c080655502d0001004000c0d035503005485040c3d4201214000810081025000f40d101e40d041c1c10104a040000041400017a80c800e25800d101e0380e0b4003480c7c00314000300318051340240281114440170601c84400e2007940c201c06800f0801c10410003d000d0300384401c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 984927086 1250 984925836 984925859
    0x306010f050414010c0f0605040f03020705030a08090f040b031c09120b010b030406140f0f091f09110303131a09150c0f072c090727020c0304 62
    0x40865081c000c060004201d03880d00ca14a81a0044003030034101c4a13504c56140161a200007000f005041d5860300081c0000d1010361590509020b10907000c960600b49c8070010542e4078510104001d0841f402044480340c141001100d440380190b002c0c001259454032200000d0600907021421303011608020200030107540c0c06803141000300380c855010101040745807108044108140030351643e499000011604200840d402420610780c1d10242e03055034104804045040e06054481d051b42110b15808110304c8000410394049400012010105804052544034050044044203950090a8858027100c0380c800344001c1c41c081c1c080d100d8040e41701c0e06204500f9403200d0681d01075a0b0040c010310070680d240d1960a03002d06401200b8104a4580305400982d5142002c1c1d4000b0071640d002e15000010480040f0148070365014607504248000360083d650400d64000441d00c101141e8000b0a04000d420240003010035824003110800d0b0038480e2890000042c0e9200c082008a1607000103010440303080342c0b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 984928336 1250 984927086 984927107
    0x80d090504060e04030c0c090e0105010501030f23180f07090c0c0c03020628020a03022a040e0f070617100302130b0a120b091203060a06030e01110d02030601 69
    0x1120108036542c1402983c50281000400040174080002003060038008904040c00003080b8000f428009002c041c4101400391400b8030806012904009580c03504c0b941c680250fa803403440b0f00b6840440d80340300759142c105007400500500c00070f039240c0d0038210f8000d0703003400b45106d9000c1c090003d045091a01c4103541c00c5498914040382000a130100756800521440034880817a60101ca00d940c07501c206181c45400704005484580d080c0ea4100124400d030340d004900c0303451140c081e13000d56401c00303e00607002c1004043c81c5500c04901d112100a004546003586c0000c1010440c18101c4e00c0c0c407a0308a10161520800d13800180104450030b03d40c0c05050120501caa502c180c4110f010780b0650324650106000c02c0f00116814400da848049120641d29010f500c503000f1700108001100c446c1031403d0404075045c003500e0103104c9008064101200442000c01c903030242c18041d0000500c1071415800702c0040030340030448800c2d5500c07000441e01c00701c03490025044c1500008001a038038100b1500142c12015803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 984929586 1250 984928336 984928339
    0x6143f091903051204030509040f0903090e1b0f130f1a09060f0904110a0903061d0c0108130210080a0f050108070501120213151b0b0a24080d0905 64
    0x81c8511600080d40c03210544500c0e4150f9400e00c1078586851a05030341c01e0140388a00b0760400d2070f10541811503552174003d030800c0c40c0a40c6580680329202d81c40007650344400c88840300140e11410303111118000f00802011010b02d4141464240320039424001c1111123f5800020504000001848020a880034151a502260801e00d190048610105805000d1320900d510b6070040480e03440500d8035140c00035140200c3c00ea0b401c1d90340b0030303580a015003055803600042d50240c0c07418501c882114014100744c1c05456010700200140a00d801c011210840c00030602d10410081c2ca0b000d10050312800c5c0030012172007c40c0c44140e114507054056100308d032841003808040b01d04001c01004400c00c0429040242c45080c42d00f01c00300090001c100003c2c0c070a00141000b1050241030020f2105800d521507807040000d6500d104c5401c82c100104c0790102c041c500045c00a449001c041510501560b0056000c920010038600e40d15048a01080b0070726060b1340b1410300c0d500220258075075264030001c0c00015010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 984930836 1250 984929586 984929623
    0x30103021309020a1401030905120d1401141c06020304030f170712150b040305010914060411060d111602090108120f0307090308040308070c06143f09 66
    0x18070f400044041c00c0f01d124040d00001030301442051644070350840000560010115080c8800042c0492015403005a00c0114030b4030303110300d01c2c0e010484810301d0342c101c0b11a0500140ca8811100030021102003607101855031240c846541030001d141030001d03600c2075020362501119884180d002030070b000004081014001c0c84602084559500314030f80c0b5028180350440000c40040c518030001299a280e080320802510210740001000b40c150422212288128075108843c00d41e148020b68480c1d003640c0040c6000c903810040c001504246014180303c0010101c0410a060845503807490303544085406840c01c002c100141040d03040605070680100003c2000b04680f03191149015103c0c02840c505580101000010604c21440780700c00070081c6802482055a139640d070b1906030b480340d01001c1c040310a288003110000d081801400c1134000340d50858111803030f20801290310b000c145a041802c010700212100100424103252024000704030041c40d48a44500b002c1010300d140c82c210208c10560241c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 984932086 1250 984930836 984930851
    0x501080f13030f030b04061e080606010c0813030c0e04020312040b09011815020a06110304030504050f0d08030c0403261917070504150c0c14040e0105010b0301030213 73
    0x400405454021074251420940c4650088401c801420440d17003241d500c1400e10801003442d0340141c201144001e070a0034001d88459440040c15184c2c002294034a0102d43c141900c80c000c40c40c02c000070324400e85803600302c001f0240c4941d1000c6000d0301980100b03583c60030420400c021404e00300310442c468622269818101460080361503d0740c402c80001e10304001c1c25002481007120006070740806010415070701c036041205000c000703544594082d8155843ca04141c001c03442c4580003001c69010b00e0705a907400d4a01070a00c0244040e20080d0b0000507080b8001c00071003004644180090360040d0402c5e130756556034500d1810402e040325034512038055030400b1000e4488010050743d08a4511400100e840c03160410703a0750054401d601c0103a891881440c0f5942080038031607000d4010000e5502c1651504c01100c503e00e0101e0b0410006039000b0a14100d41806000480c1007540300025508010b00120345e807607001c83e00c142559000c2c1e2210582d02c0b0040014001c41c541450141c101a248960420440c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 984933336 1250 984932086 984932101
    0x4110d02060306040f09050d020a150b0f120c03010e1b0a0b0706050c12070f1d280b04030b2205030702131410060f030c050904151e0501080f 62
    0x5110243c0107502c11907a564400d01e459280340c0246041030340040c141d51038900d004002035165070342c0c0501200d200e12031a1030903081105501c5400807401e805826003c58110a0741407041003004120407503013900c0740580b4441245c1e0240210401410204090150254181c801c2c01c0c0c0001e40740b20f010700c203001095050140303000000603680761580203900400c803900c60003d03440300ca12030000d40c1c1c2d101c0014101048074482d0002c0340810010780a60b11843c603068035509200c4104503010100d035209010f000c072608404c20f101c038170556000402c2840c040050359030b185105d1503801607004442c0300000d1b004000324408030004411400800c1c44000304140216a80c1d60340324400c0007002441001c240c501c4045200340c1c0c0e4410303e41102440d2492000341400d11030000c424100f8410040043c44d4041c07000b0f0342a120303014400d41d50754280c44281c01c180b034020400010741245803010700107610809000400c0800c402d14802d602505880c4a404d043c1000001864014010829075007180c0c5c040c00d11810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 984934586 1250 984933336 984933349
    0x12020d090e04080703030204051c1203021923070303050a05010b0a2c0a0305061005010f020705041d160626010e070c0803010f0608100302031c0203040f0b0304110d02 73
    0x2090f031080d00542d8500013490158001e000d180c10858100b001a40041a030505841100f00d074140507803c4540c00c203901383d50071400d0b8480c00d000e14203078000c0d2501d40e01c0c80381d0044004840107070a4245284030805c015044544d290003040080c0c00180d12817003070180603002403103800d01400c01c42006500d00308003120044c12021149415248441c11640300301c0e664486842c9501340c2d250000e21041d4401d0380d9007031595868000361280110b440c2c04440c00509980114a1002040390503005071145c0c1d0300d06810030004040f8021041c04a030745081c4048040503050100c0c260402c241c40308401c840342000401050601460182c044204000512540ca440210752180c1111a609480350341691a640c0c00c4580811514005100035000310020038081d40070141601030b11080d035a1818551f55058003038880010398440650150002624040560603845031840403180e05c0c0122440c29541e2050150010002c1e840280c00d40b1010061000304008500041c940e80821128401103144540001702e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 984935836 1250 984934586 984934591
    0x220602030a050315060403030c03180f0b0d020903010e210703050f0a120c0e0102010b06041202040e190302010b090705180f030a0b040b01050108090f0c10120912020d090e 75
    0x2400004400a400c00c3c1e081da145200c4c006000c1d029580f0b880e6a0306e8050040c2c10718180c114003040411001040a8a4101040d0110340c041c2d940c56148620300465101c0c140d012500c0c00032601e40030080d141d21500c09004160324211007000415000f03560131890f00070485000380e40614440104010f002090380981590312030010125507503642c2ca080302c1d0507030f40c15860340c1c43d8078070460030096402440d540100317440005203001e800078455001c14200300305407032240d80140010403900c0d409034005414160f005030701000b0002e084035084c000c11110b04000c0f07003031500c0860050707440d00f15024150800c1401e41d034102d0242e0900600b00050500c034a0b0118000b0a142c81c082d209180d00841030756410400082c04c0c54000401c2c82403414942001540c2030400d00600340410b22000c045404030400042c40c0d407148075240041c0c4840700310304c010426400b281724503040070003c0262840e128000d0911441c44142c1c03007641480046403000d50040e040c420904020000d21440d11410402c02071030f1510250b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 984937086 1250 984935836 984935857
    0x140a0e0f1302190e06060c0304030609050a0212240606030708071b03020709061a040303080c0d0e100b030105070f14040b0406020f0c09150603040f08030c22060203 72
    0x945507034400c1d41c00d5030694428040650f101c104541d00c00c1003010070b80040401c0d1506950313030780225512442030100ca40315885040ca080c1e0320801c8200701051203940f2098102d48590207480b910704840d0001414007aa211700d034400d940001154003c170040c0180d0740210440c8100048032a407510400043e42400024a40340500142c00001054103124245400d210f1007001c10305112030303000c0e0800940c0c402e140d01407030860301e20b050004101032079040e00006640301303100b011500e40b500f10f41d000c482100000e0504104010700703010300c01c42480240a05403510301c0010003001c180300f0003900d040a131a00350391a80e01a0740b4103024171120310f0b40000d60009003442401d20f2518002030540a011510495000a495400c041400300c5c40716804141c0b43c100c401100c0480d60001481e004100601d0020307101c0038603c409403401900d450400c0800745520600135070404013403d0303c90721014200c1d030007101c0803082c04500040081c58051210701100003441c140c50040fa1450131b00b0030180d46d80c807030004081d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 984938336 1250 984937086 984937111
    0x7080a03120e1213060207120b24060409020c0607081006050a050c0102030a0506120607081503010e060108030a03060906030c0e13120509040623010f0201090f080301140a0e 76
    0x241e00c1c102009a01200c6050f8400740355180d010060a190841c01405410010b018448002031194030b440c299800e01034000e0850b204c1e903100e02c3c00707048008107060b103c1c50181413403950900c3e2039640d41d400351008100243d00545d03100304000c5442c1c00c1000082c1201c1c140001801440400c00349041c0800c00d9032503a050940da502903a51042d20b07940209400b4041d2980004100445040f00741c205034083c1c1c0040d5400d14409100740025a01c5841c1120f81900280031400000e0042c0180b14079450f5100028000103124140b0070071160810800340c00c61110f40e400050303001100d90781842480010172407044100305a6046a42c1c2c050300024903ca80c464005000300032400302021034482100342c60303200c524240c48200103c0d0181482e0000c5050754801e82c33609400007903010040c1111040c0080c196845030300007aa00c40103503002c42d00849074104541d43c0e0031a003000142000e00c401c090500400c0b0413a125031602c0c00e00400c9261406485014a9000804024103008230f03036039980200d03200355a03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 984939586 1250 984938336 984938351
    0x80a0c0c141002040b0409061a070b10090e0705030c010512040b070e030d08070e09070c021002070b0a0e031908030a05150414071710050904080405190807080a0312 72
    0xa1882d01080d140540c01d080d10000300083d402140c00c3c0100304a40b8170810510401c0d41e500200000008000e84800c1c0064042002c40e00007105c0c200308981c4400050760b001c104c662140e100310112415145450720319440148140311a103000c10020824076001d01c6c0c030030b01d8a0ba030004901d0a0100240c8020540d50580e00401c04050140c3c0c016800070501030101d0306c0f65402001d00520008081c1d032540c0c041801403400030114103000903028441c88840e2615015140f050b030920080c03002c281844003c5025030880410440f02c1b80000780034480095442844c5002c3c241e0400d42010701306014500b511101c00f4445000030001003d43c2d0303000d65805000249940d6459950b200e0780303c4d9007441640940340a8900c8808444118194051040d944d80e20044000b0007051409114060720524100900c4010410131440c00c4000035034020304c144081401c003a540c4003c56664501c2140000d030f1500700000c18041058100107180040c000e9030000d050080150b1405003800215504e03a03464180c65489 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 984940836 1250 984939586 984939623
    0x14030a020c03030408100f1b0c20180414060108070501090e040c120c03060f23220309051504080d0813020d0212070b0903010f0209100521011203080a0c0c 68
    0xc0750786965140f481140c03140f000f21005010129841c9c044840da4100112102e5000848520701e0416102a082c4182c0ea4841da802070501c840040049642580c0724502d01400d007418001e4a00030305400c0001c0140d03904081c0054041a5680c0041130b01c616003504000200d00300025603c100c0b001141c6400f00d40c101c90906618543c5540c0000d058030f814004512075585040d88071100d000d5400900344c0d80e04000b6680040825401d40705d00d04810480c02035102400329035031007007016038031905003803000765038450100e243c40d07048451512103524081410082d81d1000d021103034240002d803922010711b107400d1038844041030f00e07000d0182c0140c012101000448d21801d000e010303011001c4044820b455503070001c0d01095801000c1f4a8083c2d4203013600c10100c102c8a009a404190f80104006480c180400e01115580c000342600710140d401c400142903068074014009003e44525690b03002c07581d016080c040c1040d00058803190741e15290044440075254440000c10724903901c000d01881c407005404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 984942086 1250 984940836 984940841
    0xf010203190905030d0212060a06110607030b010908010e0c09090d080c0f07060f05061e010806042d0e0607080c0909181e070906050d06020f0714030a020c03030408100f 74
    0x85103d0901c80c800a07c0110400411429620507403046880429141d2a400100c0b0000751076840001d1a5001c40d011139806800f80d001035405490614200089a07643c032259429660441a08601d5070000d0f0400d44803070404901c0180d1055140b4000c00d060014648004c0403c86c0040403540f00102c007203900d8402d1100368003141c0706036412000c00e100c100483d11a650041c0343c03e032209071062060b02d400c040015030040f5060b0402005842e035510540c0c803042400040c01a80e03140b612501e201245164042050340083d00e04d41721880b500044240d0341140075850484058449028032481c00c040054203a0076500b04c5941403002c0d2090750594a0740450f1201d5041640c02015aa008100084d080d0245c22070624518902c924101d6502c01d0b030315034416084a01030f0003a150401c101d2615031000c10074039001404a140990500f516140c8161104222086858140c0100e5000000c0182c81707260b0402464140c000128040d40c60300780b404d03260aa6880b4810001c44201b42c403550703007604052669 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 984943336 1250 984942086 984942097
    0x503090a090c0e0102010c05040608060411070f06060e190207141b03010501170606120c10030f0e0715110109080d060305160f0b0f1308030a020f01020319090503 71
    0x14100310615a01d0300380c240007070302e1003030000c0c000920022014203040d0300c1406101d0130a5825103c0038942400d010b0101eaa103840148071541081d01c1b84400313007094400c0340042440700c4c004c0303a041075240828505202940ca195110707a80d940c0307040040c0305d0700c561004855400302c1d1b071840c1c006903501d09600d881300510b140f00c1e81014a40c0242c09185e15207088401c01c944100d0403c40007003149a890758101c4200c5403a4086a01c03443d03200000150090401e911b406000e1140b1004840225044100184190000c00d82500c00a5101c0402d4074030a541c5000320150b130301c51540601421410128866545041888000100312130b01c250f60340301407020340c00741518640002009585680190952000d042c0900c8111950f10074a00002e03920400e5030040030a5500700e01c00c111f1042d107448141c0c4016044100c000c02e4000b0104520300700c040c218250940100481f03005503484144020307001c0e0800e00c812111003160f900420412681050301000d2902c2900c6218001071940c2040c1459490341c043e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 984944586 1250 984943336 984943339
    0xa02031806160e010201020c07050607170f0703030b030c030a0201050d140c0a0e03060114061305100306030501060b04060507120c0516090b1518040b1005130b0f0f0304050309 77
    0x44400740442100001c0d10001902c1c031030344550501d802c0c2038004900301c0c400d500b0444c1d0319810210090003545400c4005045003802445070b407503903c03c5c451681c0c0c4660701c80c004010340070b440007590404041d014000c01112550480c060480d038260a40460f8a41107003640c02410040c0001c2e00e000008010f621400001002142590341c074070740041815035a600c1170340f000f40414280100702c00035180000c1d5040c142c809009240300c101c3c0d16101031001c82c2c0c02c008040c280c0300c01c4514001c14a519403001084112101e9500030174039510b981130032030071555940c1215200c402d0420042c0701e00d503005400c0300c4a0329407100709800c130070340500380c00c440007460070100428030301960b045500442031240310b98065654643d41080301c0e000003000c10590045e180704c3c1c01d45400c0140a003200f21503054209032028100504049090700003500091002104c232003001300840c0d000328041300c0c00c04080140801034544a407100d840c1140c8502c1c2c0765442e0099045d490000500000020308001041c0700765600110f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 984945836 1250 984944586 984944593
    0x4030206130c080d05070b15060f07080702090c03160914120102070546030c060618060e01050f0604120c03061d15070806010f1b08091003140a020318 66
    0x3481900200341b82c0c03055109852106440020a80384407000044031030400d401001d0318a0012800011072168120007000da0700e240c0203000050142e258070702194414100414a9640c0740b620ba034100d1400d24058280e601040503540c1e0034800991a004040000042180c0100300c0d40003c0410f107000e44680074008106010360f15144004032140901e00a90484071205080804001803040011821000c0300000c0b0341d203d0404040802d005440303504019000c1c040c0410340c2601c40b4000d40f00c08034641c10300035241e42e5a031320400031104000e2000e40074140484449070080300031000290b450255003c1c4541e4034005000704402c100c0c2100c80b6100039a4001070503c81c0c034143c1c410300c07a008854181d0202d428001c02c0c41030000c4e00500400548201c5035502c5e00084c9032154001140c41040c0d158082d0f080c0f001c040f40310880c68204860280d1000d10680c10b10b55141c4640e414841c49101510fa90001c0c90300f84403080001c02040003900382e010503c18801a00da94075044103145080000800b00c01502 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 984947086 1250 984945836 984945853
    0x10504150806155104090b030307230706030506030a0602030702030c0714010305070203070c0b0c03041206020a02010e0304060207091806140a240323030a2604030206130c08 76
    0x20039810107841c184001c0b070b124210103040a0684c55000a10403000e203424400308070500c82031750341d94090040a40301404070b82c01d02440b59105100d0120000c404260000000b0003081202e404024440280080d0b107401d20803401c10b08042980d690b48544000c2c201034011002400d010300c03c00940b40d411035aa070480e0700c250713a1405030850741008169a21b0020341040001781c2014000403c8030b00c0550302a161071007051074030700c0104943d080549800e480e8042003100041c0044080ca8102000e030140c0d10041c1d0f121903070880070342110005059a60b2a0300305010410169402159420403500c021001065591201c24602020000b20a009002d03525040c1c1c5403000900c90500c0c0c600c101c0b0354410400440c00d840780d0150b00c040e6600d40d06041c0a00e00841440002c0c200f00300d410150b50551009141c02c000310368406d080d9000355071843d00041c2c001c5040a45a80e130300208502440e00074005404500380b0ba14001c0d1101d00042070407a0600d50b0750517071420000320320308000042900905540203107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 984948336 1250 984947086 984947149
    0xe0109061a090d2315150d0c050d150f060e3405030a0c0306081e07030c0e040303050f150d030e060f1810020a0b0a060e04060501050415080615 63
    0x2403000100d1131082d0b208105042003200107043c2d200740540041701141940c1d044a800308056080c0301c400072680b07821002c030001225107484810380d0001c0d2051a02c0d0610700d080d0300c1c0180880300c0e40d8401e81c00e001c0c2001010080c034420030701c040740c02c021310840105180c00c7c18940c24080c03500941183c150001074070412100254010003960040ca0070141c2800004600c800031019943d250040c003203603400048080200155401c02501da20503210b0654402c1552611340c8156282c440d4003096010004804003c101645031103400e80c0f080c00008400f107581491840c0042500162403003d02401d04881e0303a4040c580a040780490480c0020141c0d683c07140790020b00c2c56035070009282e82d5003400100c4c3e0101c030186040185030350a074001d41c0c0200300c1800603885007840c0c40000703008440095901c08000c10003a101c600500c0c807030350040a01140e99417515003407008444140c008075030300c840c01c1c91051080f0803000c190a5040500602c0140e510228100011260b504a4192030b80085e140c8035924513a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 984949586 1250 984948336 984948383
    0x5090a1107081c090309260106080322032612040302031b1911120a11090109050f06041e14061f2304030803040506010e0109061a090d 59
    0x280c03450032243d4451603102c188480503101e0f440d130020081450b00006020005107401d01c10707049911241151036040380340d00350307034210351307868005130017680002440260b114040c00d802445882540341d913410300e83c03441e01ca002c1c90510000508100c0c90601080c0d1052070000802d45510054104001e41141894075002c1c0d070f05d512107081610120a1003000c52030780300000c40d07881d00001c4ca81d8102d600c240d5459071244810010104d030254480790300d90700c0d83c828140400c05014054400c519140c9031400c01c400b04401c480307050380008461820301c41040504101d40c000d2030740241003a50003040703107034035003101000c911800381c0d041c40c610789401c103803801120041e8491400fa00c000e6448020f51074407402240c00c6600c462414101080c1d4070b4031414400c5030301049414500709416941c1781030076200d44c1e030040541d000fa582a90150310180040c0f0840c03400e019450700400070f074902000030b5448d144091580e003002e240076850810010840075220b031030740030040d20100d07401107400f16180070201c540d484 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 984950836 1250 984949586 984949597
    0x70516050310020418051f030c0e160f03051506070606150c1a0613110903010b032118090c07170304030903020907030f18050f030a0905090a110708 65
    0x10910032407102004102580c821030b01605c200c401000041004100103d01400003e020400802501901e600c81843d1020000024500c9003020308001490244000400e41010300b440c00c2e070081c0e0852040c2c48a0f00000100c81502e2603050218444d81c0f4590200d250084a48045401110005200b010411a90700c40300649050941c8421901001c01046503c8070480400404600100140d01c5c0300c0e00701e80c1480c0390702000003010754160784681c0502d03400b694001c00d12001c00880110f009070315458280558100c0030000d90080c20500c1c0314140045060800c80c030b046050ba000000c50b500304050080710004400d0024002e15501c1c1081044c801c02c562200c40c1c00d50704030303168949184061900204590142d50180d403603151482c02c5030208841e11a0251010090555840e44208504503900424862001207142c2c113101e44000d0070500d090418000350042141c00401484451f01d801001c000d05884007600e003082181d5070001c0319001843c08545e88942c000021800500f003200d614010007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 984952086 1250 984950836 984950839
    0xe0703020a020715140304060b040c0e030d0f230f040305060412030506310903020706090f1d09070b040b18040c020601091a151e030c041401030207051605 68
    0x181c00f642c0e107000500040c10211414000920340e481508151741482c8059a0018051540096048070308400038046820f0340d060400400c000035020003040c641406250107003400c500b0315404001114500410342e5402c6503680110204a040d040321440801040d11440004420342075595512170412555a00044404503007910300181d5942803a03220307000c0c0741e004a001500b29034040200a9a0002140c9240c041d58402c200d0790109070703104c010354010300403c10300039005000c0c0182170000041100c8602d0b004002c05c205041d004220180f507000fa1035000c040c0481c800c0d1050307103620f20010b091a040350f00400e84002c0214020840041d580c0041006080400102c01180a000107001c26924260086400740e0001e20041103031f101c0c281c020000803828400d01d11880d0312140700080800010b0248080c0c00031000c281402c882d00514001403001400c1b106003401c5282c4030521619501c43e03070141031010080010741044990098060702c4242d580001034807201809110b052115205504c1040e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 984953336 1250 984952086 984952093
    0x140c0d0501050604150309020d06140624070b06060c1f051617150a030807060c020a0b04170f040b0a1d18090a02060424081312090e0703020a02 63
    0x1440e840c001044134101d810f11400b9030a0541c07000c4056008101d13000b4107981201d900d07030200c0f0003d152803013404248203080303050720803604140b41801100424845040074801d034100b94101e040000606803180164002a1182107a07205401f1441318044c28074003164a203d884603503112180d1500d104040c20094603800c004a550b400c00e101e20003001d82c031051003c10f10a0307550a0305500c3c50200d003030744299107500c40010440c1c0c071800710b1609021540150350b0303080003003524001c210032806402c1d841e254510042c04044940d403102c040d079045c09440140860341c0e800018007504800e5040d1182402ca01c641e154490b60b031513a81c040e480d80450740640000300e05001c50380806166402c4582c0350800070300b41030480310b2038009482d0807607400340070280d84d0700c11110a040141c2d0703140000c0001e42210f00d441c15801d10b000c0507221041c81c03151141c00c240060340003005101c90507000c0141c2644d8000701030320482d040120056a80a01c240c11200fa1518120308100751a07425400401115403a40d084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 984954586 1250 984953336 984953339
    0x80a080f090307030c030e01092301090509010305060106050a022b08060301330b0315010809011e0c0e0405040b070f0509030c0f06040909060b04180314030a140c0d0501 74
    0x1c0c0703860344140140103010032008130032580400d104003c03403104e0903030606000191540b940002c80043c03240580b030660b0b03495904003180f007550340841207034020141503400700c1e40365045a45041e210b00050117407c003006804a202d1503003034801c0000c0d0402d2401d20b10081481e45402c0b41a0058a540c4407010010a001c44041481410141b00e000100020402442c00d07004241c008088044040042c5a00603c01e81c00003040718070902e0300550050f034007d61310003000c0c0710301c100240501c40002c01010040e450300b0501255040c207060110755407140001e000070901040344050fa287c40707080041d5032308030b40341404200c20019015000b47c001c00243e01d40d0030360076040780c00440356849803d00783d40c1c0503005041e030f6004509060380100303090480202081d06007078070381c0c04200071682d040740c0685845890700d0b00012a81064410700780482026120030700d040a5a032405000d20031031500fa0016101c2c0007000510510707140d4071100a400c1c030940a24076500346100d5260594000f440012001c0341b030b1400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 984955836 1250 984954586 984954601
    0x42307050a06080402010f0f020c120706030e0316020d14010c030c1d01020705100c050d03020304030306171e0c03010e03090a09140c07150504120e0307050d0618080a080f 75
    0x3d1262159505030340d51841da44214408843c0c500300c200e051030039881020846211030303032000a55481d007510040246481482c103c4005e059070042150140c0030781007040390103001d0000b419500ca0046c3c055a282c40b00c80c40300d250a803030f100c00c0130107004055442d049440c1f60040d80341c0c102900c50202c6554408900c80c082880b89220b5070480441c50161f0f020f0007040046060201c8a6122580e0f5404c03c9808100f2581340d5604124188601000107540001007208064041c0b045e44060318040010082d416500c1c00015650242c2d600c40000c091103082402e0701c1d5801c00c00c010741d660407001e402401030304401000e15699400c000c0310302d40b01d503000311004225040503100e400004600c0c04031094041d03c503054101d03030a80c0520320a40d442580800c4408121910307000b0f9030b00492082c89204040041d60b90000c0046240c850401d10036000a9001c00282d9100d1f002c07102c484c0e80000c1c0c0010394140c004e0310116000110070004001e0301000c80d80c00c040503002030f0721610800c1104c4000c80c0d1a80c0e40b65 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 984957086 1250 984955836 984955847
    0x90218010f030303090f0c171c0f081801060b040e0121031404080703030903022805011d09011d0912030a0c03090b040b1501020105040c03020603042307050a06 70
    0x19544a1104910701000404d10070b420600310a80960918100175110751140080c00c80c4a4000010384c22480b2407401c0c10880811409040214941001105146c018070040046410324101420050780b20302013483c038032400c602c1091402d92000208101603607004280c82d980c0007881518081c0e0980e07000000c4002041d0b8000110747c0403046a0040d5902d9580d0a44440025071030480c1c40d07480a001c0451828070801c1104051030281d15005603080c9144104805000810b080c034418005514140712240705201030030040e51003d09120241c078007002078030300140044600580d03010744481c00010302d200d15220000a02441e8490325040c80e5507800403560703030300c2806a80d0401030308100002044a441e0f98000e04510780c1da890049102002da0322440300240d400e9905940b281c0500d8103000391031039a084440c4000e9801c1c0001e0041d07162a44907400203508c03520001e802481c000000030100202d50142c4285401407a03c0e108554680c4664190713103048038000c2034040e1142480201e88240150b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 984958336 1250 984957086 984957089
    0x8060102102904112508040b07060e030a020606010f0215191805030f0f042c2d070917070509060d080904090201020c03120903010506010e100e06040b0c0109021801 72
    0x3e00d801781303445c00e90788190340000d41c8880c201008102c1d0700360700030000c0c80d02001000100f240103890758544100382010720481e4100881200d0741c3d071080120300a40c41c0c000c2640c59210303c090a2480c04040c0440043e0701301046007070224102064002003000d0804aa0586032580208010400105040c1c0100103444e01c2c0c41a005002a8400e02c00420780702c140b40020000302d400403070b90500300790341d031140d0130302e80c0125070a590102d8500440082040703e280c0020780d40504c03e1740d2011500190340c4000c512803400700100003e455100c00000e072001c0c0c0202940c1d8000d00722144200c45d042502c6039030580b01c8450b0b000b030f10301c40c414600100d041d40c41e1a2003846961504403004511708407581c02000014038000c1012070550040c0c6401000c10356050040c1c3ca03003e005c1500840c0c0e01d64803130080508466005000906100f82032190504586504a00030072040346418104044000707100083c02c40c0c01143d101c3c400300b030700018450b0041c04041d040310218501c242c1d0f98280701c10a2061803481d440d405d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 984959586 1250 984958336 984958361
    0x60504140a081801020106030f03030203040b100b040e06030a020a0632092103031305010f06061422260a2a0308181f020d08060102102904 61
    0x10310004000e280b910f50700d440c0da260140000a00e140d07495a030300c2a100c260000075030101c1d0340803041006000500112907480342c401350307a18420504102c0d00c04d83d64003c03401104462203900c800601c07242c80070031040c54916001000049035690369040148140a405501907018a500c6034041000d0812058801c600110504050500034100207001d110801d0581c5021000000a0b2240b68000240015401030001d181080c000341640c3c00c180307094030718110781445094031703080040000a40c80710205202c101044142c070799a00e81d442200e01d014070344c00c03078007000740d0707540e10340010f48030814103243c00300c603540030b520100620b45a0603068440031640700c013406075000c50780d00840d1a0800e01e0485030850000780502d01e0746403a80c450441031381020600e40d240484048481803d8600a401032800301d900f10040f10009181c0f080081d1078a0500880000f440010380110b03d40740e0003030100c0012620146802c00550100d4071203044c04454180060000d4200000c550805041501440100095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 984960836 1250 984959586 984959603
    0x15070f060f0227030c0d05011e0617070311121e01090201110c15030a150b04060338010c02040912080702160e0c43150b03030c0a060504140a 62
    0x280f450134006101000e580841d41d40d50790749103e0613009c114416144201011120000d00c486c02d205812580e0781584d08102200e6003c1c503402c00c00558203c1d4410010391042d02d48020001c0c0011003180b905a1100c000e126203000280031980f0480154003c20416000740d844042590303003111001c1c3ca034540d1414840c0c000b5018840041249803400085820008207000050b04003080c0105c08000c3c0525044854121000034040102a070325010345050000c00e00018406140354056580340b480c00f8240700c0307840080941c0c40c031626030300420381c148007550094002d210700221854000d101c0144002100d0100c1c841c080819081d51000401d844911441706200000ca800c100c18800b514100030010350a2100401000c500c14004849040040d10309600081c060740c80014001c6036962041a4016104070340e507842004070310642d4810302c1540800900203450114503007c40c1c1103110304030301d4500610990700464100070150340810b00c920b000e000c10014140c00650540d480b056002c070090b0a0b1203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 984962086 1250 984960836 984960853
    0x1d0901080d030e1e160b0307020303011401120624020102040b1c090515010603051b09040216061a01080f060105070b1005130b03061515070f060f022703 67
    0x601079804446009080f030708607807a18904045544045007030034907680254000701c0c2000354030010b0803200f501401410030058150701c0d00c110025507078081441281c03100c22501a243c1c0059006440c241050b1041075001d00182d922012004280d400d05500c00034905d10342a0b40850303e030f10601c00d80c0d003564610044640b03040d508805950982140001c0100c22640d03824284000903c00c2142c400d0031051104031044d19890004007804035800100307041c1c080013094850104814480d4102c5485e4402180c0042e124000040100054815910000d24461030040c400c002c0070701d40a584800c3c0341003640c6030708142e030b1038065101c3d50f81c2003900d000c1e02252050004000058003200c0e501c2c5e201c80107184035041644d0b41c600051001642c06503160545689030741341c41b03050405105d103907400a4510070b031807008904240460440200e100e41c00d8110500801e40504014180c100e000c00c141d048441881500b81038021040254810703001c112405111805400e040c2258000759001003030001e003c0c20030380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 984963336 1250 984962086 984962113
    0xc0914150d02031b06040b0408010c02071e1205010b04090c05040c0e15090619080105040c0c0201140c10090602030a2304150b0d0c060219080d09170a1d090108 70
    0x6100c801e01c0d04d54007541c1403001080c1400f0844c060402011f0502c00401c01980181c0e020341030000c26009000401d1300d401001903d0510840790380102c0c0c01c80210500c40c0511401e00600412500c03c1c400d80c41070500c81c005e4144052140c44606171601101c041200325600c81c030603540301403407240b8141c00c5200d1603811080003080b100907216000d0040d003a24903007240c16040b00190001001c00c48049680b040c0140203d0403d442000b50f080b0719800c100c016106140c001920080f030160103207a201c0b60010709091600018004c1036007840a100c02441136040625009000c0d4008546a403041890481ca071000b545180144001c000b0002245104507242c51f16888881d11904103612003150f160b910b401040c1c0c40c8c01d601200e4982c056011021402e0618000904002144682140c3c00b00a040c1c08008900d030503003100d0340880880c100040401c0d5600e00781d2081e800043c801c0c10000400305046a0050300b021030f10036590341c0a210766459080b07a504101900c10b0a000c0c1c0300c201d601081c44424031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 984964586 1250 984963336 984963373
    0x60601082a1e070303020c100207020618010e0a06050c06060d02100e1813020405010519120f0204020a02061006020a0c0302041e0c0207061206210c0914150d0203 71
    0x1041c04241c00c412949045980d8403038150f0000354100c001940c00104405080d1040c4030311120011691821342c6041c040e034002a005000341c1c81c00d20748800c2141c3c205207040e8052480303010003d00180c41d0941865565a015020350480354403140103000d658001520703494030708031498449a008011803881001c402c02119a0b042004000f03800c0020555000b070b15440e080d500ca803080c0c01c941070b0b071611018144184811b50701c043e03000301c0c020342d42100300c050481d801d07002d1001036402001500039528941d050aa480c0302229401942051000813a840c1996011452621035485c0070206189a503945000300d030f465265610203000034a0f5403806000501d000c1e000229448000e68a210300c1988426250044603904c13481500580e00060302000a903801c001c1498081c0c404c0305041100c58036094101c00c5000580500b4051031604515020030000480f20241c0a09a861005c126000404c2e020425805041e0b804100081e45007400c80d00070b14100d0b51881c030881d8090b010301040c41c0c075101038020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 984965836 1250 984964586 984964597
    0x230705031005060f190309020108060f0303071b1a0a0f03021b010f33060e1201020309010b011101151404090b09031308033f09060601082a 61
    0xc80c1c00d9a15000200c40c2e4800014001a0f041c1c1d4500c83e5440365100100d100e400311600c0c481c400c2c18113000075600940c2c1c12000c4ca80d44464156285440018464000f900b90311071120020840085803080040908020800710241da1151079035027400300803040c454600b4040d0005c50800101c001d50300c180010310940140007801070000141d48601f4445079400d0039508030540000d103043c1c1d00c0924040c40b0348101100a4401002d020b4241040800031004030b42c11018051401804460348102c9800c0d100c01c003650700350500032130085480c0d0504400c4503010308903a8907500e0008182c0000002001010f02c214840400801003004000d45000e29901c0054001d686030341e070140d6110094000f1400704444a03100e01d2409020710741c0c4a007a440481c0f07440340590050030b103d50003441001c00c000380500801401c11018005a030b101803171008407200040070102000c0812021000340444590b000800c2801540c0c2622900055620b1070040301c407058174111000d804002c481800909407100100400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 984967086 1250 984965836 984965851
    0x30402010c0606050d0b07090605070203070915030b012403180b0606041502060901111918091b02100b1809070b03010b0d0614090c1b07080c01020123070503 69
    0xe0319036896000039240c02c0e00000a94154103140c0800c40e1f8164810300601c06841e5604005003085074a40109036110000e0050085081c1c0e14002c070040c40355130382210402150f1021041210750384402301c007941c109407600c00034000403043e03070500486400f0b402501e005420045000c2007442d6940c035078010a2102606064109000b000701090544000700300703814200e01c0e5001000107041c40443c0c2401c49031246103586d010b0740305014051a118402c04041120740462402a141c00d16201e080e0341c9820496000c56000c40c40c1140d0b41c100c400403002009103443c2617400f034408003d090074030402540d00c0304c0b20032940150b0b141030000e034000c5510a450b809c0341c4420100c524094540007980703c241d0003078103c400012004154010600c8150040401500d003144020300c803150f5000200e046c8050140c42c1118007800072450442541030100c000c4500030042c42100c0895603035840312a212683d804400303006509001c4040425134034041c26510368000700c0c04a44640d5200c03907040358a230f000509582c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 984968336 1250 984967086 984967091
    0xb07030605031b0a080d050712050d02040f0e0601080930030907080610140609040902220f020304150203060604120309260616020a06090809101103030402010c06 71
    0x116a6481c100401c018030303c0c24501c801c1e00d01081c4010440c0d8041990320002680d0704c2060404840780d030100c1519405980000a140c4000100340c09507810302880107220407103440400c1c002000082d003000c00e02260301014141409813100030045481e6503085540f594558022241420f61812134440e01c100012250303224085010349011010340c50380140c6003c14180d2001d00c003030040a4080c003029800641d458942d005e01498403809060708100c11040b6441031300003244012460b210354100181031130f4002c0144c00700082c401c0e440c0c82048411610303071407c2c9280c9583c01d00724a4240c030849000360340016003020181d170400c2448021b5400100807a40010040c07000040c1da800c048150403101c2d00ca030b102c800c030302424034000251007011001e049421f001c4640019440481c04105c640e00301c58a4010142c100036088800c0e4900f810030741c8018403032407170004107a007400103110142c4031440084411807050f02c0390080485420030350610840a5805c2000807800560007a08103524403485664003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 984969586 1250 984968336 984968339
    0x170705090a0b0405030f58020d0c08090d0311190b13031b0c1a0403050f0303040804060c05120a02010b1008190e01140705040f061b0b070306 62
    0x410740d0815694000980e15034003240c00d01c903078902030011502a0603190014080229880c3e40080c1100445040e20440c14a40c4812221966400308011840380c0c040e062080c0303061091072002100c100426100d00500500c0000c088507031045440345e1015411800303050030300e8505820066802d42c5500f08406001140380941d400240c14009000020141440d8080400076420704190044008000340000f51143d03003160002030304100e000c6820300c5044841840500030303140a01d55169a03400c54100c02c0348017504407030720001c407400403c140d80c40303902902c0400f1800f0340901e95a01090b00d004102d8401408140100b500c1075000400c4140a041150702c107000800c1800031035803000541d20011b0b5141c070903000701d43c1080d00d40066403969502e0500d0051401c0360481a806401200801c001501d40c0c0c00c0e03050b0131100350040014405070240030000380c10890405000303907001e44039158880212803800100d2038040e8a24001008502180c24a542c40e2035803501010301c8001d0908060554070b150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 984970836 1250 984969586 984969589
    0x5060607060c020303010303020c0901032d02060d0e070b07030f2a0f140604022103091c0209010906060f0e121501080118410312090d17070509 63
    0x161005000c00382e00a1580d1b5410342c24020708261070008600d020b00d8489004000182c00d070004807504880c0d071100b16003040e00c5054900b107940d2408401a42c030400108000c9103000f03003507000b510750040d0b100413103c1c040d0f40c8280f40101c0d8000e482c409030118103441c1e50424218010042e1014090b00241c1003000e401e802e80382c000d04020384040c290b5408030135451103c200000714003115002c030103a4001704054a059800225908244400c10840c19500f03020b810b00907800700182c55a032000141642d10003240d070050303108210502d64043c0d01c10b4030034200008400c00507124a07010b071000c80c1c0d42c04c001e0722481c02c030507100203000c190001d8002030003400500034506d06000310503040c041420034103842d5140c01241801c0d240b190000f244030221000a101c002907040503003030704500a02c0800f06024684422004848004201000e40d03042c2d0080c41144d44503010000f401c1c010b14003490176502d920790904050fa1410711030b9400e008900a0081101d4806109503095400a81450a140742c01400c07070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 984972086 1250 984970836 984970841
    0xb0409022817070f0b120714090307180507081e1308030a06051f02070302040b0f030303090303041b06200c0303070309030c0801050c040b0313080c03030a051b07060506060706 77
    0x982c0400b140e0003401c828008400014041001005460308950421184a00780303030800c00003402040074001085500c4801c0001c010540341018401810b40c0ca420380d0b1200a24007078403403076080c1c807002d624020010340e11078001c01090707000300502c141480703003000404400000035030b01a111103803120503500200300080c1004004c0d0321841030801c003c00d120f40b501c4144450344144002c80500e01003001d03500d0803d80d90014a890891381c040350b000c110501c0c000c0c007081e08807080a03c907580501000080046102c00003005600851080600071801241c90385140501107842c001c80c3d0006805e04d000e42541c91010a8041950092109554040c2c0c072030000a844c41e4070542e411004204102d40400500c11040240c01c02411300704000e1085103005070840d07085210728064040c0500022012880004585888500c00369216110665900701c3c0025240d913504120303070f8801c07241c0c10140000c01c030307104080610040c40031506050b0700f80805645c070381000c2e10f801480c558109000740548000300d4401d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 984973336 1250 984972086 984972119
    0x7020103090c140112060b1e040e04050604111801050409110910080f0105010b091201150b04050915030d1d0a0e0405100902031506060d110306040b04090228 69
    0xf4010300400e203c1c02c0b4005445445c45404202a030342c1341060800503403011004a540703025076034035400004c40c0007025005039401030360010a01242c01e80200420064000b80d443d00441c01040d90500305800300c42001118640c440c0c0300707607550310520300411203403e207504010202441122075080c282c1800b4081a001d42c000c03107240115030342928003080441c23000e104081c0444500b400034420340d818102148514450800ca2a0150000d2507104860501c01c1d0b12420108401c1005208a00d40c1c0e4408036102ea0054041c2c1e500c956040d03008038a01c034000004900d00c10b07030080d0280c81c41005c615000c1e45ca1030300c020341e509903a8a000d0b040a0450383c1c2e03c041200603004d180902002400d082c2032880c64061a400580c903140e141c0650040035030340c00a01040007031500c418940e200e640e007001207810380c0181ca1001140f80e00f4000040f0040c4200f101541c4514000e4600300100703a2080108001e4440c03082020750420100362410b00f40c00840030500c2d02d2103c1c0b120010070304950342c19aa04100466 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 984974586 1250 984973336 984973349
    0x10504050402070f060c1215031e0f05060f01090b060c070b03060a0f080307031b0302071a0d0911010e031933050406050c1207030c200106090f02040e0c07020103090c 73
    0x4904081d2140300c0341c407a07000003c0d946e03023004055900755541c1c24041c404002c1c0b4005448500350180c000c0100c60388480604503030203020350700c141c1003150481403003900a0107040301385410030b2003c15241c141a420350760307030040c046c00401201d803400044070410f900181403035030011948000481d400ca115041c0d84000c100c200015641d40724a42801090104114800b0342c40e40701e02d0f0046404258001034107001d075004115002e00c4031a113011340030840c2c40360324010b41115042c20518014400074005000c42d104003030f2940d0302090108010180c854030600c100da12801c806112803804521404000d01da0000e01c109011080321500788030985003849006443c1405807508100400c210300b50290b0340d000403070442140d060008000c2040210f03e40100b10000b0599141d4880c44072038810700e02e6030303206c1c0c10381c016806910300407001c12030182516009443c2010704161840c3c10308a1540708550032503a48140486068540c0b001c9c5042541c40381505074100340c4c4030308110010400c2c0d005100003e106 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 984975836 1250 984974586 984974597
    0x30102070c090509010e1506040603062d02190e040b09040b0411060715090f1b090e07060203120403021018110916110f010606020d120b010504050402070f060c 70
    0x94040d284060b540000c004d0074160b4100210200a404001425800300754030802e00c0a0750754521000c00c00402480d44040c280380e080455410381e006103560004403490108201039140003030940b80209078841c41c41240e417640c45440300c0700191132003002c0301b25600710001c0c00810341110800000d1150038060387d0035909196104184000c1212409418482050580d00c003400c000c041d03240c40f18001944007044082e035841c0d0200f04108a4441031039a400355002c0003240204003521507003d041500e50040c00c2005241480b44071144a00141e0601150b050f50b00440c5480d260084281c510403002d0421010b621445a03081d42c102081d000350401c2c840c0f5401ca074062002a403d0800048a014040d140030300b40c15014040c0660103030000c0d05140800e1300b04040c10040c81041a4030348210044410819468910041043e982c046031141d0712200e5561240881c0c05189208c0046030101c541d1180030074010482000107080c1794024099041c041d8480100c81001a1945400d495100e60100c00180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984977086 1250 984975836 984975839
    0xc0507081b011704030504051e04050411030d0206010b090d03050c030c010b0a0504092a1d0106030507053a1a04150305030f090f1323042f030102070c 66
    0x5030f01c2800591030802e6840f034146503082645000d0042d1240d80261400780b00c0d01040582040c1441c0340050810b040131b00200180d1416051643c0180f0f112401148a4080c00c4507102c492440060724038141d0304400c1406150078a40e9040010000a05404030244401844040c1c68032106102400046071404004074840c42d4040c10015043d14a4019621551500d50140701286000c100c24241890015004080c0000c5641680c2c907000306611101080e002a40c00d00700c103130240c100e042d040311131a480070300c42e6880c3e8030b0082d2030f10b000c0c5442c055101203c000140340d041c002c42643d00d400c3c040c2076141c1c81c454244418031806a0711440c071844510040b090107440e0314207045c89150305034011001c04600d01c1341199103c9440e40307d91400c81c242024086001c050943c3c0e104500580000c0040201041001240c02100034000c400a20101c5030441c802c1c0848030b00282560500c03941e48454200070841c40050f00b8054600440c07421a2400e001010450303003a00c091008010301c40c0175644020806 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 984978336 1250 984977086 984977089
    0x30d0c0510020a080a0e21040512070b072a0306091403180d15090c030506010618030b1009050126071d0c090a06030b1c11010c0507081b 60
    0x41c0950846841092041050a00340d40c0d000000b942c0000355100e0100e110640455001c0c501070905803d0041d460840f100418020306180091048410a40c0c80041c00d898009210b03458038818413481b1841c42c0304101c0100010070f480d40780010741601000c0d004000f0017001050444c00300c0c0da0001c070382c840d503501036034010300a60b45c061210718103802c8001e501c1c2c0a10340c0160000c0b40c00140105004282040c0c0ca4810016150034680080c0941d1004100414031410172510044983c441907400c0d00501c0004190302d4440c0e0070021a1682c01001110014078590701d41e10400c400030010440e10f80c000c4000f20310003810380601c40c0240744014406001c881c00340140c02144e4420084540725034444102040710110100306461a8115040314042030703524910b03810000e1040c040903d5015001c840c0115069406501079032000c001a600e404400e264810f05c40d4401c02c5200014042d40c0c841c2e0030b0b03490740b036200d2005004500d1140d02600c1050365501c1e5800c1c5002d1920b8440e00f03407440549048000b5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 984979586 1250 984978336 984978343
    0xb0f1201090509010b090c0d2304230c060301030f0602090301050c0a0f0509100503060a15030504120507020916050721110303040c0b07080c100522150b0f030d0c05 72
    0x1200c05c00c50b02c050702c9090000c10000a8400c810041800540701e0311941801082c50490315044082950707000c4072403030700703103000003180c2107485030070501d41905600640d800354006902d40702d221003d40720520b146d0a68403140c0351040000000c9481d241c080003e0000ca1710700b805010300400e5030864113031319440c4550015003242800c80c454410000140310a400a0f500d9090800c5503000600342269207443c1c0b071011490001554101c800050b08240010102a900d94412481280513241008030520f08070310803101c5100e4104040d62041990300810a0004154a45a00c02c0170604043d031810015a0b0b41c1c5c00c1c2403103500911f0103600542c84001c0d072000c0d040080c0b9803400103000e01851452030b069494440f00352445c00764080c80c40c4045400c00810110741704803032005c030003101250b40800111081402070602221102003405a22100945882c0c14580c030300140d0740d00050303000390702000541d0f5100030441400f04a42c1b00b90300580c11030040d1428000c40380903007120781c0c03000f59011903030800c1840d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 984980836 1250 984979586 984979601
    0x3160c05040903120e0a0203030a020312070e030309133201060206040506011e03060e06090c0a1d0a110a3504030507060603050f030405040b0406050105040b0f120109050901 76
    0xc600b455110b0340003940c851219142061349950008108003040505454121400ca0082d090b100006031400000e8001010b05400c400180c100c4e24203954400c02110a540d0390508103405503c1801001094684942100302659040380000f540f510401ba18407940c1042a610301b00c03e001c0020950601c4079030320600341c05420240020810350520f030791400d0380c500f4140b042c0702c084100008040519a104485540215007245091021a0284c42d02e9601c034171040c0c8604176035201d00c45543c400b9081514540303040302c04400401030691a4103070b80c401075400080030405525501c800754505008800054000740d806a6580031001050390050544200b051a48400781c10b0f80c91625068031526070000c5070f0040c2d15291140c2c5520041c90900080c182e150001025401280030210303c06600001400c200c0703c0881301840004001c50500049501c035000340d90008800300024403010204c0001428034883e1a803606141180c100c04018075240e0030380082c03201c2500e803820b000340380304240600403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 984982086 1250 984980836 984980839
    0x121a0109060306050c03011a0d0b101d09040b1612020a080702060a0e0a0210021e0d0e0117071b140303040312022803060807080d08010f060c15060803160c05 69
    0x18650b504250464148c49846032070f004018200140c0090142d0395908002e6040300c000d400003a0f192094400988034140b91142c0102d0000f200484205910f4402442070281c1d0704100301d0042929032440c10043e009040e41c00c02d06205880c0121080680d01d44028015810144e0381e0203106e0510b0400241007540141548101900b0325010865401021614a01c02c80c0e040b030312042c2d003003c03600042c1d007006c900b208051501403007803a4411005101240d02181c10396070340d40b080ca4448a140064600c0c1244607205520400d0b4440010101c5009401c80d1182c41e50401d10840030b04030b90352302c0c03220007031a410402c1131981020082c04201078000307030680ba10803500c400a601b01030b550001d90211007e40c0c0798200395207411400c41504a400380e4004030203000c0040503101d07070640350f200143da106a02007a1030b0014092400015050510010082c1070b5002340e942c0c0a541c05880c1c899442d00b00134000348460841e5214000030f0f100c40200001d01e1010308402d00c3c0d10000f5050f04103940c404040b0341c0a40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 984983336 1250 984982086 984982111
    0x30e09040c14040b06191214010314070305030a03020d050c0909070c23030405030d0e1c06020f0d0f0b0906010c0201080a2c160609121a010906030605 66
    0x10020700003a03020810b40b044a0341d149020600000050041c049500000b80c01c0140040c100004500107a400628580c10343c40f12500c544501d10710404441388030007010901c000103401840016240019401d50124000c1110100d645030345840e41113511450b00040402d50010b415034941c01d06000e4690701080c0c8114060409196002107074004400605038020002d03000d80c0c0c80c3c10072402000001000c840c2e030a22903140c103e00100142d4a9100e4010240719125084e00c0414043c0310382c40d2081003110191031400301001031f06405440c620482e40840b00242c081c40303000005418100640312190b90441e01040c1aa000c803c06000c0300c003145041405100d41c0400c0000d96600100009449039080c0303080f000130b94520808400410303030014184552509464500041848205039001150805041d140c0114105101c00d405181c41e00c202d20100345807000400080443c003c0d9560702d94024503030305444e029034441c0001d03401b07800d03000400d009a8410041c01131105070700c5403031303407110103120103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 984984586 1250 984983336 984983341
    0x3031f050a03150627060b0f0a050309030715050708090106060e060a23120901060608010e0c070c080609070b091516060c0804150504020d140a020913030e09 69
    0x22400d111000e001c06050000328503e1100c0c410a80c1d03004c00020b1005c480440d003810701c1030a02445000c0e940c610490021704069001c10108000d0044802d8021042812441c100300f00b20180da090b040148803001901062103074a010640350070300d2084440114034000f501d8a40403c01074a592805002e41045a15001c0140841ea8200b8030010030b000007102c041e51114407100c811100d001e4002110403082d61820100c051900340f00e0007515500b500801c0011059881c084403500702c81c4c952003104009044900108080703005021516005018500c4051a207101a10781070803034000b66000b020ba41d4031100801450440501445018041039a492890a02940000745481c0105d01001c2083e05000400c0c1c022401c1103800c0000d035550206c03062200c441c80100180c40b41c0b20481d010b9601c040c0300584505142943c2c4500e901c41d5500416541480700d20707480303c54480c11072081c2c0100c0d5208119100c80985c0e24401034902c00c6161607510a0507684528005006c0c10300c000100c0d000d040e0140c00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 984985836 1250 984984586 984984589
    0xa0501151b02091f0b0901092108072a05010e0f18090715020f100903050d050606091305041202010e0601290307020c01020606030304050f270903031f05 67
    0x69481d00160111100c4046481d40d0303c400300d6a014404040c2110a100c00000a041078800e014006d40c40c0309032075120000b0b60303c40441e40a141b10800803c3c41c0f601d084e56490000700040d0240100c41d0003941c00f48014481c40b1044141d2219440020464020143c0104255a48140c081c0c102078415103035690004950700100e0b42400210b00902021465080003031008441000f00800921810702a81404612000040c3d180c000070b0110b8000e0b80509070700d0b0f0724a0b2100d4014817480540c580d8a1600c1d10480f01001c41c000c10020301419072041e003c00c4007100076a200030001d1480e1180010004e658107251800349104403074868030340306590505402007541d070400f1800c07504455032070403150041c00f01d03072501c0311141c0300802ca0b040003141d010060201c11640013545030b45202081c0c00321985a120501050340da4080c610445a00202010034847c40d401c00d1400c929192496103031019104c80340c500010120007045882d000143c2c80401005080c00c1210b4104002c0008110309801d410b06003030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 984987086 1250 984985836 984985877
    0x1407030507060902061201180c0f03150b040f140a060806150702150316080126010902090c07051b1003180b090f07050906060901260a050115 62
    0x11005010300002082000030700c200c6800c6001c0865009111603698098640d1440020030f0a00881480d030303510320006410100d103071243c60b03250040c90f11840d848420071802140603010030001c206035850640000101e0400c85006400545940d1900c2000d250804c444078078030b0311071804590320418180d5010060141c11120417078204209483d040040c241c41024400c1912940301e00035007010400001404003007403400910f024001c400b152003440581d54504641c6e2002c2800340041c5031a0391034000d104140e14082c00d4480204100003c200e0002e03580019820010440c1c1c0383e00910000901082009402d01c0499112008900c4201b00d0303c09480101e14000120b94603078042c159103009000c4900b03064420785a01031b5100145400310b19058000c0b0f903d461004290703001074440c0407000318251410350f120340e12403030b4050445810703e0020801154000b80d200d1164405c280b010b00004020303440150702d54825001e040e1701103003552500401c0c001c400301c0c004d0244100890541d000d40300c4444072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 984988336 1250 984987086 984987097
    0x5060301051c120201051e06030d0f03150e0a0b0d0308150a050402070312050114010215070318030f080a0603081c06090f3306030c02011107081914 65
    0x9581501c210702820034008031030b542d048809040080700d0380c20b40c030a0940c15080700d4401e0810320b081020040c480e0302d03c01c3c003129041e11140c0c0d05822010b10411305a2262103001036000040c0b80204695514035816200b150361038001c540340440b00c904004004407580500300b0840d400752180a20082a600c00800d4100003600042c507210141c5070b0100c20340d0b5032080540140c1001042195104107a16026200d020400407a140d02303803c2c00e00004080712560b03581058072006802514081c0060b0101c101600d500420321010b0507641c1411108001c0d1415640003071500c00c2d15400040c1242490141c2281c500a01c510501400c1c11410f1000405075012340d2034151202e03e0303103006401c0000140010300341d250069031070607107445c80001c2e540403140c02c8100321250303002d5202400003c82140c940c20020288507034200d105403203404c104c102d1199004d80c0d600480361000085e00d05945200c40e91581c0b1241c02660050004140703802001c1c13400c5240303070145500e4106001e030030510003000d4009000d1f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 984989586 1250 984988336 984988339
    0x30917071203150504110a0e0a05010504140a1505031e060a0302041d0d0c111008060105070c03050a0609030e032b0c0f06050103140105060a0e040f0b09060601180506030105 76
    0xf500c0303064240000d0085294081c107001042809250781400e1040c88075001603090386c00250020b01043e06c907092030141c103801e40d0b80681d242483d15080104d00040300082183c8680c100d04c0512002910300a0110b021101907800d940f441c2ea40c4c20001442d01d4030070b04580c030020f421000c010500689541d1105178004483d416100440c1c0301250340764a000c141c1c41c880c500d0780b0600401b48140165580f080440700c01c0c9105003100c900683e001c0d0280304002100c030f494030001c582810301003205503004a020345000c920400f440c4100f00c4d2603a5070349040c4804280304a030900d440f5203903081010703041200803081241c01d400401c59550528860302d0f00c049820f40c0c4c00c2444c4000c043d201c10143c030500085000c19080305901c090003070340b460004003e00c0d00348801c1e1130074000c990215441e00010b006881c01000700411001003c0e081241403170700030f100548100e40354110720823204001010501000e118001d040090407076440c15034005095030a208071171800100c034043c014003040d900c4100b52419200c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 984990836 1250 984989586 984989591
    0xa0f030b1f021c050406020d031a04180507030b2205071710060b180d0309091802040c110c0604030203061f0b0d0e0c0405130b060f060a030917071203 66
    0x260000241c0c1001d82110000c10704481800c02104010381000040045840703c1c7d0841e1000342844100314200c0351100d5240e1081c281c4200100440e14094100c801140450b40c101e0300781d480c5503540c0926001090380116a480c201004010020501001e050403044021a101d242d40c0e90f40d9451503180d0900f0700602810040900e280110003e040000c0900704940002c108180f50b19002c1d441d2440c1c1011500c0d04001d400f5680c100890308140a019107101c0d0305480f214034bc00e0038042400081c12001040300318108000f044c002c00f5079502d00800c40380b001240c1320103040c40c914074002428040c82200b020300403501040100016200000c0f240ea0001d07502c24024550000710550300c0065206a0020703840c00000b06d4070242859099102d05500e03030140c000c40d80148982001d010560350201d035212040d0f180720726100d021825510f01c0c9a840100107000a480d456a640050301d01e4024400020000b95039121040170010154007084041140300c0c1c04a040c18440e5580c7e1440c0c8030511400c0d0101074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 984992086 1250 984990836 984990889
    0x90218060108191503030806102c010c150b030708070b070602030a06080601182a1d2812020906010f0e06030a0b0103151a07030c06050403050a0f030b 66
    0x2500f542c003a040c60101c9907002820640d0780d0800400f00003094842074440c0d80c0316002000044e014240e0841031000b4160001ca0320ba0019104191081c0c0c85200700e1306200c008145513001a0201d1602d0b0140000c1600005243c0b005509041c42e02c0516000840365521031039007800000c03407600640b82c0496100d50096134039540e0002c444050a050f502140c5c0607c07a580021a80740401880c0460b070101d200d03400c00404580018902148101c4d9103011040b101003c0c4c0329103030601c29500c14500300d9001c1440200007401402050010327203410f4420074921a00350040e0599145410840028080d03c10740303000c0180b113900003070541c600c0902501d050203140c0307001c08042c5005030040400201c1c0101134984a150052102020303041c80c10795a4002032400e18400380310f14441c0c032940b05031480c82400d803248504007482c50513144e128074416410300c000600c00d00c00007600780c041ca5114504c01c0d91501d07181c0c484800d0181600900c5034102c0d00745418002d480307051303480d040c1d900d40409030165442d082c44d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 984993336 1250 984992086 984992131
    0x2160b0d0207051e0105090d1407080307020c1e1206061c1a070c0606050105070f030e01020c120307020a30080705030d0e0c010302040b0301050915090703090218060108 74
    0x811607481804c6007091884181c8032840040d402141f20f12410000d5903c40f040c1440100c0301c01980c0c00c03a01d940e11405015070804110900090341c1c1c490600d00449011908590008036000d400d80ba441041d610702d09404034080c00e16000e070307074881600140101200d00b0300d0f00010381c00c0d06041010800f0703120510321200a0000c180c4811202ca5045001000706042001c0010039084000006031030301e034241000082d40c1c0d44030b40b048410064001403045620070b00d942e4201d49040008055034114072521404000503901c0c041c4c1300d03848540d002c00940c1d90b0300b034901c11300800c3d01c2698040704210442d910b079030090703d0003c0b8000000310084c03081400c03148040d241603603040c01031000151051001040d40350350310100780c0c85003400000600444040750540401102603200303e0084a407503840620041183e0300300b5469858004070780d07140c0891507503100700c0802d406490072034009001980310b14107001541082070000f40701506443c10300d856407401c0000070300b2220001d4006810034039050b03000d1200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 984994586 1250 984993336 984993343
    0xa08070f1b05030d0801141216060c05010c090b120606040e04050606010e1c020111070905070f0e040c0801060804210509090903070f0b07050d020d060602160b0d020705 74
    0x9041e0301000310060341069101c20503104841c1d0007101c1c080e11400400c001c40c9030241000504131000f0f030415441b0745000000307104d0780e0840c401080401c1c4c070494800c003000010014031540038010b66603544c5510b201c103042050030745500c541000305000c2105028009860110200c0340703808908013084119480d040f0100b042d62103564020702d101291401844100100820000d00880d001d03681c2103002450041002115681c41c00150940b220007510b4030b0040d40980e0f03460a4110b5480103841c0c0403070380c0d05000029a201106c00702c00060130204900647c80d00594a05c0c02084155400c0005955900002e400309034107009400c103100c8040c00150400c0340d202d90390180c200b080c0348000b10384443c0304c80140468000b056010f10914061000401e01c910000c1654903494000842940401c200d483e500c0c0c10020107003100080210411070040d0009140c00100544c1d203070080001100740c0740617802410481c0307445120210b10314005081101079602c2042e42c810035011540160703942d190b40380c0b0519 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 984995836 1250 984994586 984994613
    0x30606090c031b190c052a0f0d021c0b090d080705030901020705100203011d1302010302030603150405061506030702122109030d2003010312031d0a140309030a0807 72
    0x80400701305030070005550b8040b4001e84420700c42d404903201d1905c0305040050030070010031a900c5c20400300880c103c8620308034000140040300507000b140c0c2c0406540100f145e1003204000c400e401e0304101120002c02c4a9010b04550050041d0702416101141ca03800800c4120301820840c2001404004200420420350444400d540d0280c100e584041c4408002c01c043d410134031039540e01c1100650b440c3c1ca05a1040c40c540d00c41d80f150000442205c02503070040d03000b500050440394141c81540306283d43d03000701018990045004200078140e0f4603220040f84010071748100401e005006c02d20501c6005600001c03070040144000401548030019404a0801c1a048101e0280c8a4140c2400d00110100200040c075584036400000d00400032004028000e050b8860444100c1c00720070401000820507602003454203803114070300802c0940c058403120b010001d01700200c600c250400d0b4600002c1105100b03520040c4d0b060f04002e141445041000203440e03905520024040c4100051840200f0410103020705 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 984997086 1250 984995836 984995857
    0x31306060e090706091413022a0f0d030209100c1b03060203060f0301180303020a050f030411010206070e100c0512030c0d06080a0b04060b030703120509030606090c031b 74
    0x1c1140c545094200ea030f0f81c040b841040c02007040e00c90041260f03078112242e02c0c41c1d0040a03100d42d00341100c982c1c03140300a40c400903ca400450b5041c0010549080c0b1a03698908560600d00030104011050040c2c1d04018001c940724041c10300c10459150a9290740780d10303810714540c5040c00402d6844a0810032280120242440200d00310200d01008104c07240c0d001d5070285809440031880b949604051500f20744541c1c2d16000d0508592003030400003480f07a0002c210fa03200b6881c16a01345041e03d10040300303d400a440403039a02264480626041d641040282d40c070600d80d16152403810140c80c0400d9251001d00702c000100300020f0303012414803c04000e03006411181e102c0d15961380c1342a60800301e0f10340191040e4003070741d0b052070400546038070300282d50010250000010590b94685544500c02031003041001505401a6030001010400c94010300c240701d03c0940b00c081d83c0358110420541080801803415224071081000e111500410209a0341e101400301d00d030107003082900c010003d0a003c0c015145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 984998336 1250 984997086 984997109
    0x21e0d06020d090b0108070509160c1203060311040506100c08390a0812061206040605010920030408130905090d030e1f41061503130606 60
    0x6001101e420751142e03002c41c2c02460401d0700740c6d80300c44a02d516540c0b14442d40340d2084110011405103c646a44081c007a6260300b840500d500a071380d03034510340074428107181d0003080c0c0c2d505040090002015440c030440f40219400c00852810702d001855035101e2031680300030401141805c3c403c00c01d0700821145104d00c11100e400e0f02400041196982a260b40c4020410001e02e014042040400088004049070b000b04450b05102c0750004060814000410003944035090031510b00220100744203a81c05039000c1c1101140d55070504881c6010703600058520031600500b80c5190b0040346204080d640c200e5070040c5040c3e0f440505495990020849400600400b480c010030300040e40b500003215801007205407011f01115102122454403980c04a2000390b1554802516804212082c1e2001c403076504a41000954811210703180fa0301842c0c00c110701d20b070381d80c0003050110301c404201d5a0140d010b001100c01000c01d07242c4e8020721080f80070280414204183c12040201040440d801c28000f60902c042d03038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 984999586 1250 984998336 984998347
    0x3030e0402071b061b1101080423010606020609070501082a041403010c11060f060a08030a0329100302130b0304030c1b08030702060304051e030a0801060309021e0d0602 74
    0x3005420220fa101d0320011400e01c1c4061060002820b076108440ca0704400400103605d042c000550b44400014821602000403901c1c42000f0035540c07003c641c03e54040d0300002400f505203200a458602e01070035607912075100c00c40400203aa0b021341401c2d031050302c1e00e40e265000360a10300f1002c034140001c82e031825102c401103030108843c1c10304118041c1488084009024491140d50700365050f1601d40790100143d0482ca00258101da000060260410806842c1e1800c0302d690304181811500030540440011b03031104843c1120b002e9606e005290002604001036007000600001910300310451601e100303045d000700b001e9800c40d21903203828008200c103c684660f40d01d03052030003c203000c00d480c2084030145d84490b1602000f003103040c040f4042c2d61008008500c1c0c6030954007000300a400040c01101c007446804103c00c4903030390040b0390803001c0d2464401140c6078003000034044c00c0440160842c00c00c0518200d4080c02607500c40c21036989203007136407418480081400d0f001c0780302041c11140c0074010900001d0f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 985000836 1250 984999586 984999623
    0xa1719200307080a14070b220209070905131512060b060a08040b0f0c040501050f0d11030708070305071409031603030e040e03030103230a0c09020414030a0c03030e040207 75
    0x600c0380207040e648003174101d0044d034240800e500420300007610f80359922000441d90000d41d01030304030682d003082842481040781d0323002800b401401c4a10f800020806441001a402c0240002c14004001401400303c086211190300386201c2900c80d50b40e02d0b040307074a0381d082840200d03804006051805031882e0707520b402e650300140c50842e064904850441a840004507142c50322031100d0300520588588600e4245004011189a00f01d006056032040042103016402e104510500308120031000001d0b031686000040909201c000500032400d2606050030440f00503448456080103410a40c00d02e9101c00002002c02d20b030401c1c0d40c8020a41c0c1c525980007000707041c0c000111800202d4201c4041c010030a4004010b0b803280000e01c0014503000341950720303034140301046807454240c0c3c032440304a541c00000340c0c4030580381c03200981c132040c02c00350300060038020100680b800f1903800348141d0003000418915500c03c01281ca0a1001904101c0340048800b40c81d951901110704403501700c50b0003c0396112101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 985002086 1250 985000836 985000853
    0x3062e031b1502060c18130c02060609070e1c060e0a060c0306030201080a09080903071d070c1e060216051c02070b040909030210020c0a1719200307 65
    0x303800c00c1e001d03180c0c00001a84601810000c4800141d98050500360f2920726182450f038008850020b0040900341c00040c043d11009084030039541e100300082818a80d01602030300302480542514040da055104110040c2d8201d1980038130600c050391300e004490100a81c8840c00c02000c00300401c41818201e10764407121001410001e034500800c01000b013005142000e8044880c036100007070200d000b6000003401620303035138840d0014900841c03010b8038242c01c2100090500b10507822518881c1e117400c003d1405900c20032605a4000e6103420000b130840400d07140c452082c011101e010700c2031050401840c040049030f4060b68140600002800d006002030300c0e0403900c407201c1c2264903c5003034807002002d030311900c002a01400c0303908082d80b6500d444c1c1404031810107802030f04800d40651094107444081c52400380700601800e0a000e0180c00f554102e0300d01b03000e0310b42824075418109001070040d540826003030b401d07141e201d40090400b144940f0343c5103040c050021103410403a605001c081907800a002c0001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 985003336 1250 985002086 985002113
    0xc050a15091103240402030106050d050a0318120807050f011d100203010608042603041a06040c080a15080703030201150609080a17070b04080903071403062e03 70
    0x41e804200700e004102e0900da035404c58441d4149020104a03000d0301050044076010b908203001400100d030240d03c0b48081071440070111011207007548030a506106041e400010394001001039010802d14900c0c10b00b21600441c240840500042800240101040010480b82d105d860219009000304000d0110f60b407100d0340503d6076001c003406030903616440074020303208503030680d0039549034507240e81c690380c48045a6400020b00301004000740150f480f01c0170184c030042d5220300e102d502118400000704921441d1300c0301c00f400b8103008038180680d40190740c0e000442d4580c00700820300300082141c010b103c2a00000d03280e6100c032805024845004c01899810341143c1c0314220905041844660f40742d00403149401188a12541500302e044ca4400050b0340c980b80380402d80600c0700c0c040c20154283c595404000003510115030f004000510184503003010700c484030003490310b0203800d0080510300000c680c403404000c20040090004880524240700c02d090034607400252800851036064403031900851000c0301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 985004586 1250 985003336 985003343
    0x40902090c03071d030715050f0309010614011d0103150906080a050105090d020604060537110703080c03070c0f08120c0c150712020a020604021806100c050a1509 71
    0xf040f60f0310b070211540b6804c0560401001d40103041541c0b404220242c1a0fa070740e1640f0080180803c11850600b0702840518000c00c01c0100000f50a0f203040710040c11403003080541ca05000017116440c58411950860f481c189000b820041142006888840340b409019000001d8191030700c81d0104100c0340014900d0b500380d01c00c80c0204415265110a99030344c0c121022680c0c0140d10900000300020041d401880c0c100e00c0202143c1c0002003245240e0362400319000e1042200e00d5418242d1400240c54002c2c451401d81040400b40741880076140101310b4034009245514080c0d00001180c46648544100e040c85600064002c00000807803902c0c03036895110030305e9004021038000205007902031b07000484068004110080406010030100030001c408011700e50014007464030b0f00501008080e00041440d80000c4d0b020340507a00d042d204008900b9040e0241d0902c46506504100e00707a01c480e1180c41601c015030412a155480c1840c026190181d4008002d0000034001a410100d404940000054520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 985005836 1250 985004586 985004597
    0x3030212010b09090a0b0f0d050303090d030605010f0c020f03030403080c0105010501051c0f0b28080c010f0815041802011b05190f050318090c070b04020f040902090c0307 75
    0x340d501c078800740e900403c00055809000303900890040155175001105003e07010f0070318491160300c4c17000680c10a0700c140d42078650750070000c1080001e80050103c1160940d960804100b582c0c1004d000815041b8040e891609020740d8070300300f0b000e40d42c660070300048621000301281e135956281d1900c00e40c603401501501428fd1b08010000c64590b0007041030311350a8001c51040301040d50740d01405c20140ca8003480b10302066580c1d01140c006619104000c51150341c0304908401892082c0c030032480e00da903031607100c5901600b0400031005940c3c3e01c00216201d54181d850403503500c2d202e0004506000d0745008190703034010724000c01c410b400c0600c0007101307203041d000740c85068003090003800128020b410700d100203150741c0109981d5400d00f4450207079001000d0050b000d40100309c44540d60145503520182d5101700c541c3d00304040c6000c51400c48803841d4000548030189081c414540d860040c00000a030001348900c6c2100d074140c3e11525103501c088426a002040e010301da0034a8910b90001d5402640d0040c00282d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 985007086 1250 985005836 985005839
    0x102040911090a15020606040216050a03110705180c0c0708011503060b0402030f0a150302210607170106121107110109052d0105160506010806060d0b130503040506070303021201 78
    0x204103528140c42e130f481d9500030f011030360b9540c003c20000303502540308a451420b1503045400130640801202030158030035120f54802a03564004145810301311350002d4072030040303000c02d155a0340002d8103007a0011030a40c0115112800001d200703040194941020301c80790f1a01010704140a0000c0c4d6a070122130040104002c1442180b041c042648002c84000001e40707100f00c0454141d030710b180d002200142000e2034289903141c030703540000c4a11909144078025a00c48000000c0075410038400f5641107081800d28030880e03200c04038001c41450052040350240400000c21600c1a5419002250020300c84042c0c2e50b650070b45483c2030b00b030044130829030500055455801140f0f82c1044031609442612000152030000c0b06c041c2c052200f03002c0060301504100090000c1c0218001c200700d0014402c1c46200035103c0c42d8106090240340000081c80d1070722442c030346404031000c0f5580e0410685c004408810001100c0c0050074068075512403540304d25082240001c800090541c0341e0301400074240a001e40344c0171079 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 985008336 1250 985007086 985007099
    0x3060609180212072c070207060804150605060705030307080609090304030f020303070606030f20061911031c0b060703020304230409030915020604110d050102040911090a 75
    0x198460321500007003201c000c0c0640c026151402d65688415501003ca0340300f191030303401c0c641c1c03804074070b035a40c91004070180e040c900c5100ca100400c59110500d84010000326140c844000c00d840707409840580007003070900c5000b2141e00b50f81c0203000904030151855990749054a4500d41d00c0d8800c450b8040043c1401c0c01003803461401c03140700350040d102030380114100360854031800e042c0d1185840c1260706200030070440340041c1150103503c00550140c901d046650b030241c10000c4402c1c01b1203181c81000e6041410100244e582c1009458641210320b441240110540302c09440110707034082e404001d88408291403001050a50207000f810000b10000d12244002c0c00c244005030189450060140c3c00501061103000c14480c1600f40d102c166240c05c0320810b80c4000440d00f182c0d400f01081c1c001071464002403146511914616a00800d907200611440c90b0640320600b05503c0c0740c1c5440e22a1414101200a111094041c0c0c0d0103004111810808150b0003604046140c0c001307030016000c1c0c0d8402400080c60b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 985009586 1250 985008336 985008341
    0x20d03060608010b0d06170a05121224090a05060411041d0910060b030f010605090d0b1504020c010903020c01050c031930060b0702030c190305060c0403060609 70
    0x2100d5481d11448466400e112010760260480c1d805d0f9025156103800c00199880c0039040c8024000d50030010f07210040e420309085c5c0c18405586043e40924204014107610040110402c90b40b140c1040d81320600e492881e0505540c60904101440d400346000742072181c2100c0c141e0110340980c3c006c8030704002c11000340c0c41e18240c600891154007102c00c0c121b101c5003d440d5207000116030160252040d5031100f0050100a404c40d8010780002c1464800030040002c1c160392505d07000c1c050080307130406c4c41c105502800010a4040e40c0c00008240d1424100030846480c0055040140e030300b00140150340b292840c80300c0ca402861320742000e0303005204001840b9403550003642250b03a0b240c5060007070b514007841e0070843c2503103800994074003081280c8402d82c0b809081529041e200074600c201086540005c524181d1400e0380c040b90080c081c0750104101100050360005808141c41006030f9001c0d0000c0200070140c0b9103041c16500143c6140112010012041480700041003a03a100d81e404222903501c48030720804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 985010836 1250 985009586 985009589
    0x40c03091104050618090604112d0303090a03150b1c030f05070c0306020d0c02030a050a0c020a080610170105040b15190f05031c0507020621070807020d0306 69
    0xa9509542001c01603810315030411130f8403100140000242c200070a1540c1010081100c0182098000a041c0010440c184400c001018001c0329042020142e60404205159184a200c40b008400322100d95450710140182d40714084d00905134160242d890070b0982940342d40ca4051400c4502d8802c858810b072a20300d110380301d12070071a4102c1140c0113103a501912028220500c0409000301400810002000d20184a000d544509005030311800686082c80c180c44845c60f6074002e41d0810300040c00c520394418156402581c4514000107a05a6030000c686501041d8100c5201c900859080121009100456404480c20340c4450990300402c10105803c0714000d5500500c0b0780640e20226000c0940d002d82814030f250300926085260b010304544c0818030f0b0381a44007410b1009030403820840c0385402c2c018191003e4041c1d04865010046800c000c110b0302c030b1554024820b0741c003c2242503100400c03881d038400b000e90188000c1c0d2641025940680b40c103508560300c000501c2101c1c00c0b5a1903d209025200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 985012086 1250 985010836 985010843
    0xb0306040b13030504120c030b060108010e2a12010e0c0c0706030c11010f1b03020316050f0d0e03070b22080a020a051504170a0203070f14060a0605040c0309 69
    0x3607840d00d580d1a8010246041507055080150611001c0b906200307190405002c6442207c4214105246160030080b40390020003846c1403005010041100c0441d160403c0d9000203100030350742c3d04201d24064100e0512003030a12903e00c1502180c11810854505d80403410394846003512041550b9229071007075144120361408802d900030034002c20076640240c000c078131002c0c41c07420084190f10030b4031501400c46010240b2400c2d40d0f600c07180c1c6a010b546410001418000e402d01d0107510b90b140c051984240c1d050380301510340402c43c001900c140c2407404c1130151502142d06079820300041a41c22006666500200c40545008002d4408240f80ca2110f02d042400c0c011840e07052000320400b034441403865000310000f00c0c29400f4100850000030000e1184001e0351082e5405e0311020b040a04003038003103200615100c0040d100412250080a800009131120b640d4000e40d031440b0f1980510302403000d66901700c1031401510401091100b605040d1f0480c1c410380700103807010803640008503000c509036158100040d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 985013336 1250 985012086 985012103
    0x4050d091a0405012a111f05030103020f010e060c01062103080a09080904060f09050c2a15250914090a06052d010207030b0a020c121303060b030604 65
    0x1040f455002d81c0300381103504004030344006080b90000a6000354601c403181190080700d450306a05080c80d26103c0412030104910102429414048010b0324600c418000030f0f10030b0003451034080b00e40c5c2c40b69000592254002d0500303511451051102c038007a2042d4005c00000048450811400035124403404807290380581d504505030b2a13210f1064001c2174819010f4522510801403200e0949850040381c004040c040d00e91814a45030262400465801800e4a428480704102003a03505d65203130300b00320740c1c400c040c941400840d91003600d5618200590f455107000c04003200400c0120341901c2191034550301c0341d03188c000e0303801a400300480c7c86001a0181d0384040c11040c5c054055800d102080c1a40310039854030003d00280c6982c0001c0038100d00700c8546c0029818498071200c05010002041d124030803e00060006a04541e101f06046800500380c82003e680071038906005881001070312083c12541210b150303500210460140d01c6403c502060300c407d8100005030a032030900141036031186410681c80d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 985014586 1250 985013336 985013339
    0x2190c0b090c311b030f020c0a14241f06020709020a020a0b01030803011a030c27221d0c060702010c050706170c091003180b04050d091a04 61
    0x9865503807003c894a6414103803007041030503020b6400c1c441c40071800c0a41104144103a580903000702036a040c5a4407080040c0184160101c1000001b050100d49501101c02c00708681009403091800d500880c9140a00003409002c045c9a030401c40d010303019180050b061fa071020b00c1807645041c0905584500b4005130b110280400c91603145501509a90300140f0541c0d4189c0496110690701c0b140030b07002540d85036000401001baa165019000441744001040c280c02c502e082c0c0c14100c0b55000303000002c02a06400001c140070740343c3c0180343d0440000c0003881c00c01038003228645907203000340aa891011480c54071a882c609140c4000c0e4029050386150005c0044804400c20b00020307030080034080307051021814a000002c0e00500028000c1e2206543d00040441088240182101c0c00741404402810070480700d44161140540212100311604000c903003107441107282c6140f210000030152450740b06005010030880003007035154481610781d841c115065154021090202c445440035550800304000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 985015836 1250 985014586 985014619
    0x20d09050907050408060c0c1912030203150621060103270302011b0809010b0105030121050c0409140124030b0702120a020a120509150d02190c0b090c 66
    0x3800c903800300701c2d8035285090640d0385400c54540324080c0c440100540010441d100c081004129040d4210704282201d0420100d90b151606c4103030384c0c01d502000300750b000030000d01101200d0404034402031014000070b40c1d842030346141881c0e1210780c2e0620078641c807500c400f14203198807134080c0d040000c0c1c0c0c1c0c01c00741e00d450f00380703070740c407200005403074404400395522048110b82c00c06444441062084258070b840199141c000d0490b0f08541240400b503052000a100600c540d01e1a4460496031250075290b41c09500c03854207103145025841d40034254450704100344202002070402001e41c040301024000d00c2a001401351480c00c4080c130038480b11804a0b604410008280012031603034000102d801500c0e01040008256600303179001e9440701005d60b025850810812204108140c40c1a04034500f0300c0c100300312030b8002041003030f0408413024104400b1500c600d070446254100d800103070345100110940082d102c405441904440c00595042101d50002401114045070b14200c6a1700100a00e801f26020301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 985017086 1250 985015836 985015849
    0x91c03020309102a05100c0c050706090e060405090f06070203090108060a150804031e09051e090c250605090d0525030e0a090e0c0307180c171f06020d0905 68
    0x90043e81ca610035581810007413031b107a1203110300d042c1c0155110140300300203090245c508500384e0310080070004288010000e40c03200c0316899411100880300803480351100c0c00c03441e03d001c20a0010b14200c4c003600080c4000c040d0004000d0220540a882c2c4142d5541e80c14100800c1a1051141443e40105880328400143c458a10698020b21130b0501d00c0541c2c009007150001003035880a1750f004518544c03024009403411890801310304015aa02030174610301c03040420b800170005400c880d83c0302404aa00c2d4078440405121030b00b8400b29012880b103684080c101030340580310a4440d5081802a21100c0081c0703442241112150195402c510308804840b41a03003113050344807001901004003407c0344c40c0c011ba0303c01003054003c011050b07004c0745d41d8510301d20340340c10440e85c41141c034803e0748a4a03041299030000f0030500a0308102c4040081e201c42c0001d070a03241e1003020302c200e07d4200040c50400c0340c28403544031094104400300c40071442c40382e00e981080c1d941e4460a0301c42c1d00420040301c4204945e00d043c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 985018336 1250 985017086 985017167
    0x120f0708330708130f0b1b0310030b06030f100507090b0a050a0c060b03010515040c02160504051f06020f01050109050f1504060b1209060702071802091c0302030910 72
    0xc04c40d40c0b64070b6245441d44040040d02141c2103901c00c14030b5042c814003502c00d292440340d0300d00d0340c00602c0c5141010601000610700301e110003003441d40a14000b51042d074041c041c0142864841c0150b44034850024030442c010401100c019009c2a0580030208803009060150303105410147c403010314001b1703218019108124151022100181c0b61030b800c0400d514203000e410b0143d000e0241180301540124100b009440010452404540c0110b04a44c0da9003130390f50072101202c80680300010035444124040a0885014044041d02080a80000344082c0c0c000781080062500d07000821130350340c85080803016180c069031551707805071290f030200307170107c0444200c455240001000015141c0d42c1d0201040c0356080070800e020310640740d00401c0841c481c180030300380d03002c0b207940f004d050b00509009540303411305c3e070b50290701601581c0841e56aa02da200c820445101d803090741900340013001c441c0b40003903403a440310b034100b03006d8034043c61607404145c01500030480c404031641d1030303511424000d048102142041e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 985019586 1250 985018336 985018351
    0x106050f03060a1212031a0f1302090301050103080403051c050d02160b13140c090c130b160302010b0406030302030a0c0c0317040e0106020c090105120f0708330708 72
    0x340000022200c01101c150401c1c944100e0310511540b080c20409002c4900500e05c203a040b040107e8070078003550f641d020301c40c03030307400f085854003020100c50307861800178000c44011a03015807034240007005004d460320152084034420301c1125451031404000718a95054004100301144007880400880304091b0050302c2c8940340030354140c44a522035181c1617508001996226185812a20048144050134964001e40070b502401071058645146c041440c0c030b0350041281099003008500441750303590f048010700040c030f51049203584440303041c01d40d0301301b4170113501d8110090361070000484280c0c10180100c20441c0e406230003441c144181d510042d05c403040110bc2c1215103c0144e200400054402c5040041850400110729241c50400300d0386800c052060f0000c00965014801e0004107540e483c0d8070f1810b5403010340705800800c00c2101850310305007443d06000c0c614007540b1070100b64203000054410b080381e180402051030140380c00301d080c1d107201d0044803003c5245a01001600a41c0030302d80381504000c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 985020836 1250 985019586 985019599
    0x30d09080a14160906050111030301051e13020301031b09180b071404150206010f0b16150f050412090b1801050723070e2203030e0a050c10080106050f0306 68
    0x219039480c0959100a4110307004c225940c401c240180d580c002d40d115400c05200004625650502d4005400507040120310546001407080c0d5096980301c0e5118982e0003010100159180d507182c1c07900d00500050310a0385250401040000111605c0d58050304020050701c40e00c0d84814076450b1030b00041540001c0001081c40f0041840300002c0d16136000a000618025048400390030802400a0401b241a4007001d03046904180c01d100d0b13090352100f00c60701041b05850340401400e00d45840549120000c0003003007941c4c5008010840540c1a400c203a1040e440b0326880000c03103d9281c410741350035040e405007100500c0306005c3d4095840091010500094050411074200b074503e46d01c260a1023000d6102c041c012050001c00004410200700ca100030300480c144403036003494400480003600108140c28103c440c688402d110a26010754803c00b000707000c1405445804000c0d05041f0ba071484c80710a09802041c500150481c0783c0d103e00318a83c10307901507950f05840d00d169a113112080b50400b5280503030059 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 985022086 1250 985020836 985020853
    0xe0c0a030f090f30050409050f0c03070e041b0305060301060e3603041503050702061509060f04020c03040501021e0d08091906050a0e0a0b0106050f04030c03050606030d09080a14 78
    0xd0401c0302e14550b07525aa44a1b0f81c0c0e070b41406041c9064800150040b400d0542d000e091116904400003a2030b071001480c506105169440c0000502a040b05400c1d090800c580d04806030000345d040d001640300d40000c0e0000d1110f15604c080c80246608101c0c0c0c66500c1213852210340c041e91800c5544000c0f071003407541036090700e110108621402c5910903032100d0759440580e44200d038115014000c55911a006001502c1c2d180b40c4030800081e861151400f851003200d107200010b00390750344c00d0303c4a00032181c0a0001c6450f01f44200c0920750b203500501a0341e0151080500351404c0790843c0006014040c0e0440143c102c074139401c1c000341c4420402a02e00c444070300501c2d001001c0410481c0728424014020f04001c01c260038440d2018080300c4101100400c650040321200000c10700c25240c1604460141c42c110307550b03803030300d00300d82c2c0413800340740c0005094811410000041c0000054258001c02c41102034400c00c6075441c2d429600b131241482000000e80080c542c010205210422070041030039417105440316403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 985023336 1250 985022086 985022153
    0x1d1e03180d080309011521170d050709090e030f04050d0f1b051c1a06030a0c150f05030108120d0912031508030a1205060a0e0c0a030f090f 61
    0x541080700c0210190399221000002032082e80200402001c1000d420390162031101001d00c0003440606c00500254003248d0040b04800a0800725846007241940400403414401d600810103101d40c071a26102c5402c140500000790004002c441b00550390070ba0032132402d0300e040140014801800070546000d142c8003644408600c0b4031246905c64145600e02001c1181801d00b01300c0c0880348020300752020087d0000600000325151448540340108640c0400c00c2ea4500f40020b280c80c890030030080812500200018000d05c46002e50348000e841d03511020558080030000301c0b0786000911610480ba888034035604400001c03a00140a545c101c0d013800f240103080c98440003030458005210f0400642d64a00a5038209940b80901000c1e050742400340d07242802e400002403510b504418140d40c09951a00807601d1381da240c0c041d500007040b80c2e42d8862280d14081c14015800c0d00268140c001180c100305d00200403e00502c100c1d481e155000c0d03a202001c122640700c410311050000240c08014261241d4580803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 985024586 1250 985023336 985023353
    0xf1207030312050703021908040519080304050d030e0a14010204030611090906012105060d06061e090606050f07031106090703150b03070b0313061d1e03180d 69
    0x145000340c540c14031500e010b06808046540040001081610511000c0d000c2030340211440e0300c03200316207002c007074a48907030402c10b0500017014440080d04c450403c51104000c0706201039841280244240d400000c41d0013001d034151180c24010480130380120a444000851000c258041040003500040c1400c2d182c0c3c2e25075080b43c040401c2d12125000c0803442001516017031305c01652006c002e01e4800d90019906c5400e072200010180001da025072035400050090302d42801c03040001e904240e041c844540e54910315a940d0301000001a0842001a03020501690b240200f204032002d0f80d41d05443c141c502c0b0502c2903039030050f910071070070800d82e920084580340d401c204460003030042801601c50b840c59454040c0c00003142c800300c140818240060703210b40740d50200340c000498007084c4006d5540d0781c2d440b46001042c00407410040510340b603c61165051201c0b0000070248003800021508103014090190002c3c00c580005040241d01c10405030a10360405400c41c01d009030054074408004403682c0e03c08030b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 985025836 1250 985024586 985024589
    0x1401050d06113f1b0c0313030302070e061f0e0a030b0118140106030e1501060c12230a020304092405120c06030612340e01050f1207 58
    0x1c0359260f0b8000303070303540f201038615049040003401003c4140c02d4400715407002035000408941804800c003050650700c5441c20101d8210800b00000d40ba500e11486104656400f01c4d408160014450402c002c514010480315050151400600204103801c420101001e0b0102c110000e00400c03035015180e00340c689440383c014010b144100142086981068031580992900c100700c0c4610f80e04140204080c101041c05580c1901c03554907010800d000c020038540d25201b000524074825100c0322000082c29580b0804401c140b500c81d0180c0450200d0025089803480000d005614080d03040340c02c4860720202c09401401311b05254010b070b03420b06585143c454216905280708009252000c002620505071100c49607020700b1046a5500c500340075900744603610000400303120b005803070000115031240d445010820708a0640011107121400e0501c022414101d004070781d2900c1e500610813403000c0440401d001c4159407142541d094940e203407000f0005890f2240d1140c1d074020741c0004000c00c0241090102d0740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 985027086 1250 985025836 985025857
    0x9030c0828141c090b0c0307030f0207050616120908030a060503030a02121309230f150904080705072405041214070506041502101401050d0611 63
    0x1882129241203501004031400181010400c2d095900d00d001000e02080d00d02d0444464403c010f8009a060030300010021200007074441103014007040780080c4400f00440c031a0b1490758092044e41508510388040c0c0c028600e004081c0d0304110001007504644600c0078200c1c00d0030340341450070340381f035210f1900850b001c0c2201600d0304500001081400340c541e015610060005400441c9003045100c402901ca80e014544044e4800300002d4a0441d0740324014040e015201c5d0b1502040810441c070f05020a085030310955004282c07201c000541c0c042c4444000511500e0360b40301103c10040c280c0d040181d02200180103d907030500500028021a0040148501038040035007600698052050160842074041036144100b0200704402e00c10086680048a01c1c15440b240c0c40128500d481d410300c0c1002e446800c0740307070820000b0030b000400c42ca07110210620441c0d50b400b945d202c0c481b010f90407804c0c2c1e5040b02c044032019a20500400090501c0c1914207070050140c3c50015503c6421160007000c2e070710101d0200c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 985028336 1250 985027086 985027117
    0x30e0d0c36060519030206030f1b0418381f0206180d1b051504050601090b0409020f0919060f0303110f0a02041802040203010b120105010503070c020409030c08 70
    0x7800682440000e45800c40510504c43c4007092555000a180307220052080c2c0c0d2003d880d0001c5544540e861003500301e801c500300040e40d00c2d1500e802400d80080788081d2150030490508503201e03200f10213130366080c5031203e100d4840c1c24880850505c4030740345c0420310040da0700408014150b00c800c5200b044038520920b41580900624146200354103000b04418003881c08940000e2100c00b84190402d0003140c0356000ca03642d0000042043c00e2442c1000c41d1080b080954007402d4041004020380030886a050340d1022608011200c00030b4207000444075104402500810002644006071401c0412580e21104130114a0500344d480e5010741f040d10300585c4000700d80b04400006008141d0402e0030002c0c2142ca00000385680741c5200009551034020010181c040d65983c0c0f0a5842400c14800c2100f07107a0700544290344d03959440708007003150340c40741041030341c545510000070410b90301c10fa0031207004880c0750340c0710307040c0b428250200300080207244021410710072005001d000043c480c5010349072020340145d03807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 985029586 1250 985028336 985028339
    0xf0513090212010b030702190c030b15030714030304050904230a12080708181c0810050102030906031b091c050d02010e030a0311091507030e0d0c3606 66
    0x10351540070b4068214024651084c0204010241c1c0040e450320030690018001d00010244e08102ca440c0820b40c101601c501d00450400c10002c21400381407202010a0f0103d9050710b640720f520352118103003040351030f5144c0c00420080250380b0b03182c2c00380342c5c210340103081e000c0d225000c0094009201004110030031071074019421410520661103502030000c405400c0c040030b64500040020454074000701340e920f4041c640540e00707408a81c204401c031b4032410582d00b2070004c0d901200e00501405030842d06203020110705503010515520210aa46820901500184c256102c00d01d100c1c0e4281c400c1c0344004810704080c042d000050b502e0301000c52443e500281c42002003a0503041145c140071111515406580c1003000500e208a000421500454001c1c80c1c0064006c5192030050110302ca0104019808003050401003504680c1d81c00500c0b595219884d202c04c0c4225650500c54051581d100c003907e001c450788001c1001d00e14100ea8410b4400016881440e0714a14460740050461030164580d103541c1e55000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 985030836 1250 985029586 985029607
    0xa0b0a0c0512120610020f0d0908120a0813030318030f0e1008150f0301060b030709060806100c150515040f02040506071101090b03040f060f1a010f05130902 69
    0x441c1242400b402a0036282854207848160312060140580e40218400750100d44ca41c1d10921024280500c2c1c0310590f000e00301d00c064000c2100c1143e0040140d140150b070b52078500b200403801264001d041c1e507102c2c0401980d03851031060700300c40080c8040e02816161200300040c0d9980c240c000c000c50740300f40c88481c41c2c1060182d005004c00b0600d5041800746050388205014540c1142940c1d03800407903544040c0b4400008404514210a040c403106e07019030900c58081007a0922001540c03140c19140d8524401c507a40c0e50003241c90300c0c010f0ba002908014004a0300089034801c0c2e001c0d403031a0340030b1b505440b540010981030100300d400032507000301c28000c11000004185441e000e031000070130300a441903090500700700c00903e191282003030050204000c0d4062020a90045154070010300f1111505a268907060900a100c583c4800c811545503103800f00000c40668903219950703101080703426800280020b0340c019214504059025014071409000440d00882c52104000c05800c2200c005038943c81646ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 985032086 1250 985030836 985030843
    0x1908070e07110f1b01030b0603150f060412030e040e031c060801020406021213030f1527260f0d060f12111f0521160e0a0b0a0c05 57
    0x38540e1215070419140350f03206a400248241c4140100144144200040030050f0700512411000070340140e80801001001d114041e6031045680c41525201c10200c00502001614450b5003e000110700c00d000300f03040070178400c0c034100740c091101600008452415161700d604d942c121200100302c145404040e9000d0703c0c0e283c062179000305007800c0290f040c40c1c14044003a45805000c1050403044e0004611116512620a0100015504034006060716816030402d20b0402c001103507034a1405084c0001c1c0b18001c034181c1c9131080303141412031661580c2d007810b960b50615042d18106108100a8154075106200b18100047c1240c850b8203003626500c0e01440e00c0c00b0300352282036006d5500e00d90109010050352040034500c0d200d00c1e0b44000308140d8000300c400000c114800f03e40000100750703a003010044c8119000801400c40c502001d40106075082d5041c0a4040140101c0d42100e9058102443c1c10300a40600a0031007104402401c00c8081c54844c4440702039504444000c000260030241098148041803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 985033336 1250 985032086 985032107
    0xc071515090608030d0e0c04050903072603063a0507140907050c0304090606050702120705130b01110a03200105060a0312020c13021b010510051908070e07 68
    0x250014040382d840c01c0300b82c0d603e9001d02030030b604505413504500d0100080511001442c580010820415410700c564410b070303240c10022044071b0481c44088d05d5850485000c00802c00303039105c0801c4616540c1c07840f0900241d60380c0d4500410031070414402c801103220202030a041c0c0d060844150924403581c03030501c2403070840ca40d404500f020018803004251a01d40120041e446107007801c1050791002c042c59040d255118651001007910701e00704c00812119481401048d401e80225000508500c16000d06503d031042441020740c001c0d0003441000c4c003032602d600b050f030360b1200506000301016601d60856081030018075086000071200d025400d4003840ca001c4508081900c680200401c0c03034840040740541c1380600000d00300300d18110450324958401c000ca980503140c050071025990f0400e441d03040103500a4490010040c040503c003108403041485441d1181e44400c24958036940313401c0030300c1a5800b6030030761180da18164900200c1e200790100f04c1c4c88010002d0002d02c80701c80c03402801c01004103024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 985034586 1250 985033336 985033349
    0x70b0403020f0c0108040506040f140729090108010e0903070804031128060c0c05040219110111030105190b031302010e060306010f0f05130f0504061202030a0b0c071515 74
    0x4409000101f8400a4425031040e4007821036805c01106090180188007a4140b081d2541320340d440c082502c041c000000c107520901035007180914034807200c800e001401401000c600280c3c5000c010040407485c036030f0a41d04007440c242541d00c0c0480f2900ca40d0342c04d074016001540c03a00241000d05045080902420308140e004c41c4288480108648030380703c8441140c41801c00f0082050400010f00000303a1880c001054004c10031941d9a01050300d0300c1090898070b42d480045520781c0982d00780800103000d1030ba21211340c2c01c021455a820601008a0181c4003641039204003002003000c0b5902d00000011030051605184100302000b10303100040c503c8140c0103100b03000d0030043c01409281e0360000480e001420090910031a45100001d0403542c9009091850848680001000400d082803080d00e90944000381d0b41480003035292030140d4507051a0a00094041c0d001440c0071010844641280750030a0b000500e4918011803074a400300d104078800040041540e0300c0c0d883d951014004050f03500180007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 985035836 1250 985034586 985034597
    0x412110409031b02031e060a0e06010807051324090b1507060203070e030709020d0e060c070209150a0f2607060e13090302030c07061b0611070b0403020f0c01 69
    0xc8503a0010f101c511800010703100e0090f440400c00c00c560f0140000281c2e0901c0000700054070b41c2c240d40316503440009580c8812107900d41b0b1a034502620021442074180e03407600d001004a00d1402c404c0c0440124038150b038410807a501d00b103c60462540320b9200c4c01070f0642c410240f242c1428100c1d4401281c1c16600c0701031083d20740e02d00b03102281040e613080d03c3c03846411100c0143c90f50b48172603003515070203451420385625004850002c40e401c20a81d01030040c00700520010403420002e072072041e0340c41031b05981c5103241d40c1040c00081c4c014600030580903408005805404147d900f94404101a284a82c2000e40303100400442030043d0b21800750142503c038103003201c542c0c043c2004041c41e074452440d030080e402008000d19485040362103140394200070051100080002c0311060034000d480e40c0210794004194041c1c2d800028446104104112524460749610006110556580001032010600b1452007400034000ba2002c1121081024480c0e8000d40281041076400b000c07e9080c88680c0004038180030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 985037086 1250 985035836 985035851
    0x70f051c090f03030f0503090118051b0103090b0a15080601090c0f03090f061a1e010e0621180a050106030c050402040f0b030c0f0c07030c0909120309021504121104 72
    0x9a020b4030020700c017426070802c9551703902c40d4285103014000211000d6452100754803104104100010340031000f1540b200307101d4294001030011000d484045030044d150050480c04500c10044642c80180c01032841c2c03003920602583c1e4082d482c1820003d0744044802e607030b18000d80704190307040503401c225000a0b1400308509000360b0342c0c5400030001c00c1d00180000e552070112143c049840600c4108070b64008269285807415405107074241080304640742d00140c81032500f44000d00b410010f0700d08500300e02426101680b000305848100ca1001810714500070101e800c50010000c00703000f007000303490083c0700101c0d00178210304200300402d0b560750045002e82d10420040050400c4441c20341c080d1510007400e0b55583c0c417079006600745406911f1309409001d200054204c4118000186041100c2c480c50042100b1a9500e001c40c0071a468640043c100314a80d200c0c5000a0b8400d0b40b004140a00c001c10085501e19612070201d16034001da044000c0c030140d6588100c00780f2200424984202c4400c890501c800c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 985038336 1250 985037086 985037093
    0x2090a06030c0b040927030f02160e0402120a02010203030a05070207050a06170c0906070807022806030e060408090d0f060c1107091109060a03060801020304240e0601050105070f051c090f03 83
    0x7007151402402304150107681c440001d100788070b181c070b504c0001003d89034041e441c6e944100b1101d00a0700c08a01c03c2016000004409802084181c2c0c00b5805801440c210350f2446031101c05031a0040201085000c0c0100c04105030303039000040800303843c4580d280f110180280d00354032000e90001c2c1540f00c04500c10300160301ea550340d05e0f00711000301e036004c0c103d95160401440030071041c03060658021209034034280d052016140d103c9101c0c08882180c0d030140a44900c1c1c880098880c41e0645024080c910200b00c0e0340032609050a02c584106d00c07405600e03c101040d5218a012109020341d600005a511000ca603020136081000d01c0103003010b9041082448a284403044480c851104040e0050b0700226404c1800f41c085c0e8001300040158100030741d0303070b40303840e2411031200020003131034009800340c5040c5070300c8004580c800d80c07010100d241300410440e4207120054983c4c1e081000200c5100d80742030b10440c00580e00f440400316401e403000c107011840c4c44070f42000d0b00141c080d0f000b00d038040882c0a41040030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 985039586 1250 985038336 985038401
    0xc320d0504110409050c010f02030d020414280b07022403090c191401050c01090305092b0336030b0c03040510020918100501180e0402090a06030c0b0409 67
    0x101b10702403e180036000302c501820780c1907015400a18060324400300d800a98480c040b500b002c151501101c0190110b205d0040f82d80c13501410b81440c1642c2c6480d1413050081c41450801000340c64001455202c01d0030022160b0390140c8050240501005008000d100340401b04000c0c1d01108241151a0402d4105400b610a07148000c0c0c0326480da80074002a0440660b4007610071221822180002488141454240a000e035407001071460300414030170451028140500898220035001c64560000300c0c44241c030211200300341c4440c43c21401407625000107802101d0307a40010b0040290f8096840f0342d03d14140b12000c20401065480c1e1030004000700400150301203032040c40034082030740050b1100c88501c08900c55a2942d25a891030507000c070140046a1054004001142c2090703850f0404c80b0340324000c242c20000325204030350f90703c003405000c100141750800304164801c2c9061000a02c45550761654005502c2582c485019000300280c14131007101c03103004140c28030709094a034507091049100030f80d0b01b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 985040836 1250 985039586 985039603
    0x20405030c0415030f030215010909021e0f060c0a0c0b0901050a0c03050918101406090f040207020315091006120219030605010807060908010c320d050411040905 71
    0x204950b030f2012252410700b030b6040d40001d9074012000d0b542d0842546401707940c403140c990002549811800000801c1c9515008064001e03a0150892600703e403100b01c40325032825111079065110741c65902e080b80d15101c038409081104403a600501e40300a5604040c245440c90b0f40010f0f00c2c141d0704100b840c0c61660081d040380c04401251405031a4121603090464103401541c1100d82d014110560314105240b81c0c05980d030048100340b80d80590b036603a40401d114100000403403950071660030702042245140810300702c0419140a0405460000b150740003074200000303844c8103601c120041d024030020320403c0055024020a0010400c43c0e00d041c00b00c090b8820321103100c024828040c0a0841071004140310301c55004680c4881d0034489542c560399a2030300c44c0c00324014900042c800c0e010004102505004042c00a210340c0c80d60801301015001e0169001c01e4a0384004903035007251130002c00d18901500401c070000b600c1e40700184c54141441c04075480c0c18040105880b031403e040e5440d012a00103d581c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 985042086 1250 985040836 985040839
    0x30507080c030409090f030318150c110d1e030e0307060207020f090a060503190c0b03100b070813091a09090708070803070203010e0607092913031401020405030c 71
    0xe40740c44886080a146124a802504c2c0300c5050056080400c40b030f0303a02100c465482610140320300c00504030302c503400500940010b040c3d448003e5484400141c6544400c0180c1ca6902e42a20080400303007400f4500b07800380e03000b000010700d42502090415600020508044c80c54130f801d010060b030b070100c1d80740d49014810010700342a82c000382c0321045568900318050701e00d501600d895541d14014501100404c0e943c0f00c1c2c10b004e030060001001380c40e40410140c005856001c12040e800d14240815020b40344c00040000b0101c0504503c0803d072580104050f00d101807041d128103949070360084480e40c0d02c8480c0d5000002c140e0400703a21884001e901507250303d02c4903055650301440e0381c41d402501d00e0030b802c960080003a4007032100045100d680c044000c280d11030098000f403002d0180c00250075600c400481d801c900140d0084400e001d40d20000d149a0a4804100700b41c0422821054500509901054010100b9644c4060805c100241d0000c0c421851102c0c400071801c0038070703100c003117501e030442160010b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 985043336 1250 985042086 985042103
    0xf0319140303070c032a0b09071a070b04030e0a030c0f140607060b040b060c03280c11030a080f0319060b0d0504020d0c150e041b030c0e1e091003030507 67
    0x2207000d0f0403100d481440c40040321b0000f55018070b90400c2c08600005891420f40b43c0903041002c101508040c0d0b07252403100315256042d1501d01240c84000f500c940c0074200310704000202c121810240c2d50f044c407100c0a10f01600801560925064005032484019030241e00d02548104c5075141550354181030b02c140302c2d041440810554900300c000740080c00315000300e43c3e01c984041980c103041d0b4800400b13800c500f07020010355103186040d480c5226140c07202001000c0094100241031001815006902102403800340c102d40048501e9515501640c0211055000006010040051031071840602c01c005c1069204200034003401c09018182c40c2c4a01200e4140b1652108023040031500c1f80072100b90510703040720800741d05580300c50080c2000d800c010038001c0022121007602e00285010308c204600020102e00300324400c40d2201059010b440308410f0b0006000120410981c140c85d540042e01110004803009015102e0103010460460700c003038a101404001d041040c13001a80040c211044e254004044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 985044586 1250 985043336 985043357
    0x318010614062506060807030314040f121a01060c02090609090309011407021203040f090c0c030e040b0901380931060302181b090f0319140303070c03 66
    0x5080d40244600007030106182c200d0019110501007422410b4032700c255107450002103040140c01c80e038061401044544050918100130454070344000d070b00700c40d11942071411106d500301e0f2082120318003680b00c04003203010a80080110324040801d551302040458100d6002d0601b0807035956a405003490130341c1880004c016a048141a050503160000d03801400103002c0c4900da0344158480d0030070311851104600b02140480c245219005003541c07481d803030790340d0110041142c03000c540e4010101607954005030740312080000c980f1420308442c064034404445200400d020040a06042c0d010381101c00315207001c01d10304200201c4181143c00d031003001c481d031040b0003100c200c005088840303c502e004d07050600b803541100c1c01481034110001700d81c02143d0006498110380c0c149004010b04070341c6080e03040070355444c510003640a44003a0404010240c004800c40171010b0100e8a03003110504c1c110b0f80c4280c008001001c1040d20420004070102c50400765082d41050303c4013030196120301ca001001d002540f0385 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 985045836 1250 985044586 985044637
    0x11d07091505090a03200105071205070c050607140f1504080d021b010504030906030e0627101b03090320151509010f050a0302190308031801061406 65
    0x968a00f0b1100400d11124243d032440e00c2d44081c440300c10306200145044149404560042003030b1012540c202c10542048180307010200c070389038000316007126803208040010a10b0b072181c1c0c01410030144500648001142402c0701b06107841c405c856141500d912203000311000703012082e94981c000b6841464642c5454030032141c0c1c000390203821102d80f503080c07060266a020400540207103001b02c0c06a25401b60b10b070345480c01141600c10b10408c180ca1a4024400f1611282400c4003408441001c241d030007544082e8842518240101501509012501c0b400c09032000d600b07000320aa440c0e55075090400c040c00446e80e002d04810b40c0c603100e906101c83d01a9030410080c0d02800f211849018080d0018018a4010b00007151105100c42681c0036841010004c40c15035844003a0000b503400c0241400b541529640c2006890046240c0943c10114214000400600300304082c43c061200c00b22030244580c2d01064140c210385544c0e2080365602d03807204200d003868407040308803201841803046a010b108140310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 985047086 1250 985045836 985045847
    0x30e010515060a0302091f021608070b040e04060b031b01030513030c0b040602120f010806180714060d0204030c051002150a051e07030507030b0916050702012105011d070915 76
    0x41c41c81041500c07c2c045082080d800b20350624a00088000c1d010303070343d894100c40d990714940c0e4007500c40d070706601300414440d9149007014954003a114080200700f17100100007103814400c0c1442c500181102042c04c401a6603054011964031005011102c0440000d640b0024041d110240e0050306900240d000b04040c000190112000079010015032070300390501d019100300c0080c00b4480d04100e801080041044d0071070300d8456030b080c0441c0d035005002c10b50030b0000c13a511500c20200c80030751100c1c1c03c001c4400180380038006480118003500c8140c040d1440c0005002c040101402400c086400003141e01c1031100000c0c1c0c220b60424005940001d1668402171035101c8151403c0404a241258004200e071517903150b00201e1003161180e50510058941da4103100c0c0041c02540c0c0a05030608101e4505103151055024000d0a401454602d0480c00224100c544900301401800350b203070f46a40045c40040d0442d10801c1040c140d0001141d030b54a03000c04000c140c0b20107801104d0580e6803084ac2c0603821480350b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 985048336 1250 985047086 985047109
    0x1090c0312140f340215041809060b01080f0f0c280905100c080310050901030f120f0c062027090103050303041202100c030e010515060a030209 63
    0x10342220f07603e20030218694503a412900b8640660800807025001071a0380d900307421100e41c02d80f040000041c019030300704400418085100d135028103050100180d801c01d004140b010b0910703682000100000d1608004060300c03002490241401220000d02801514194540c0d43c00720807401100343c10344644054140c0d43c07050300024050f80c51500307510480c80b4501560062000040e0303e486051654440511951f00e0044032400b01045202000c100400c255500441d8401c210100c04040c07280c50710f0014020107801c1c0c200383d401116034411081000048110001c010301e9a0410002031130b015100142000380c42a8004c02c9580c441101c90240320031003612058030040d29407010b40320a4448450601c41c1c3c8020b03a840e11044064200418908082d03d036581601c1d0058040c5280d966541c41d04c18040d00c6031207248085100c0d01d03140b402c009034103201c2c450000740715035000b203243c150501646082d200d026000503d4481003e0100c000303071f5102d43c1225000c0d502c0303007000342e10340c1d100030001050004817 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 985049586 1250 985048336 985048367
    0x1f0b010302091012062c040807060617010c030605090c0711090a090606090b06090910030b0103060203071e0e040905010b0d05151506031302030a021503070f0201090c0312 75
    0x70070000d0141c0c6a00807086020011313030518200095a81e400c0100065282c1486000008000b8240e00200c00038403640180c1c001d029010162420050350380d80c204450b4603901c440d150348100c121900070a002809004440130f954507040c41054100400102c00d403001a0050000c140d0000300d000c10403c16201c1620302404c0281040b400d441c06444c040040e0902c8941200d41c00d15007540030408500c50b10400c4200c4001601040c02c010215040c0a10001c02400229846412010020004006002c1d140c06180326100140c4c032401d00c0103020301032003280380805180e5100301d03240c9000c541d400b141400c1c0c038410885020802580d541445070050100586980c1c00100c2c103c40241070000000e10300481c2070024044411560b2585a00c6500f0703410b000602c1d60101c030820201e51103e1040c50015107043c0000c040d42c1a5859a5000031411654540720750507021010041001c001e07003290300c032100d04a440c00203200b1403020b0b50b6015118411404001e00c3e04880070080d0032070522408090310301550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 985050836 1250 985049586 985049599
    0xd14060703060501180e06090612010e1b040b1f09080f010c0f0c0b0f061f090501080705040b1b070b0a03090204050133111e06091f0b01030209 63
    0x100800020003402c82402580d001c680441c507178004c881441718900c000c50b2005101580c03180c88031002c12040070300151a0300d6000030001e0120480000c00c1c401d0302d50322a07441004050080d00e01070701c40c10418940b11610310461500c500001141c43e980d2186410034003155101c00e501d284404246c8403c41c0741c0d084210b2511880d14440c20058055028070005035940c4c8940200c03000d0300404403801c90b03100c20010718808500021605507540340480d46d410a40042c130219064150420482c8100044284180000e034800d100308620b5822a80994200005142181c0b0b001d041c410108050311034030300011103240c4040700c039840c611300138442c400203020010082540c5110302c007802000341212800c01e034030075891701c1e000080c003600c4035a00f51010b4a10b0306030204000420038000c03d00d0034040c4800c4091082c0c404020f00f550340b05100d040c1e07051900c0c004000800c91003010300792414a0060030300782a0740c02405480c003d00c0601d1129240009c484030049802252000101c1c00381c0070340062180c000c034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 985052086 1250 985050836 985050841
    0x3030f09100c080603100606021f0b04050c1201050102210d14040b09010e0d120c0e0a1d1e0402090405030d15090c020c0604050d02121c110102090a050d1406 69
    0xb07611812240c02003a0407001c0b40c2101b4440240501103444c04d00c1030b03001580c420283c41348000d506500f0079001844d400030004400800c00040780c10b540b4101c990300043c80f00002e8541510039450303211030141c00284000c042005080f10511001c140c41818055903140103d04401259890b42102c005110003c242043c00d05041c0307090807030340c0e20503240186c003542080140c03039217034900082c46c40541d40907640f40040d003400c0401b55001016121960020009440c8445002c0d071140d441120003800316807460b1056004240c0340e80f81d086005051240b03242145a059140010011f5201782c0054040300c10500988a41c64450f05e50701c40c01004034000b900700444007034004169040030045586a8006005280d03250008a031a4041071001030b81c80b2200b031106001d541019544200c0f5603201801108107140d190b04030720700d0501c0e04440c941100b00040c02200d0042da02c00844003465005000035400d103100c010020316045140c2c0a0507000c0e28510002c82c0c24000030417000c44141034448161800c9c1d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 985053336 1250 985052086 985052111
    0xf0f03143c0f030901120b0a0e07031808250f230115062006010e1b0c010204050118360e0601050f180105130905030a09141203030f0910 60
    0x25084030725405d01041c0c00365100c1601c80114050003818040007030001400c9400d00c00a0258a2400b03049901015070710541580c07281c41110303000d41040d0141e4580394440014101d100305d0804581c00311512090303400e5a03003000404415a8981e0b259100e0711000c1250340000c00a800341c41540310700d90f9a0341c2081510b03c0c4000980309034101355001540e0b540c02c080f091100e0351521a00c11140d00840358820001048003d2840c00d607550410500c006809130340f051048144902e401000e100032507a5070002e4208459a002401d0051151800518001e07451815000c41b1814030012081c6c0d0411180f00380020105907000081000c120440004005000c0c0c50300c43c0036941d1200b4040c00d409080395940c03070443d42c54001c01c0d8807018241c1012503800f9038244020322115038140017510441c503445441c3d0400240c41800900b0000d0400d58030400f485190400c0042d91b10700d1401418080c01098518a8611201204480d44091a0380c1410100e0b02c584a1642c940820004000e41c0d1900c1c000109030036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 985054586 1250 985053336 985053343
    0x50d290411011b0b04030201110c010f0501060801180e0712060209090603010209030709110c070303081b0702010c02040b2b050c101b03090f0f03143c0f 67
    0xa5014031000c01000d20041c0c019203200c107000c0303030244203264058503500000e8450101560b0180c804d01c0041080801034200d05110342243c0c0344101241d44643e248032504000e48601801801c0c1d914120800b5450040c4a114140001007116011500d030300c40c40c0c0401d40b080041c100200310200c40394811840f5400d05078029000724407854400c50501003c19070501e014001e4138465a002005002051b141c0790000006051924507100001d80074441c0c110b0000303050100320300460282d03c54255900c1c4c210300f680d00208000840b005440e1043c803a03400940d80c4160032180340365040e680000e0301c240705800104a2060010011106c07143d00000b1041c002401c0b9241024a101e102121400320340341003006080c0340341804080c005610b02840c8400d1030441112142994000d041005c1c0d025192202d007151003c4d150421801c41c41c00700c10800801070356072605404604900c010b0310000520b0018070120303000301c0914640c8031002d0355402c07800360004841c03030300c0405050342145c103a810903110040c0c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 985055836 1250 985054586 985054591
    0x106031b030c050906070f050303040c08060903030112150b0a0830030a0203041703100312050703020607030e0102040b1914120c0703090503150610030204060207050d29 74
    0x14035a55498a508540603000b440d0048403180c58140c2048002401e0080a41110000f42d0758010181400404030308180f000f18015805803a00754505400e0ad20900c1c43c20394080e0020a00754020801081411885458a8001c6621040904142d8400201d0402501d20200361591105002100081100e00000d00d0030061400f03241c2181484020200402c1c01c44035601e0a05542100304001199403c040d8025a8400d10480990690855494440105410456207039000e07456680e000d0050003846040140c1c401d00514015107031940e1070b60b0007510340c40044c210500b032546620303030000e0654080d01903c02410040075032903125100c44421401a085501d000ba01250015020848a105081c100c1d14840d10b54114151503440b00061801647d016005c140d0400c0910701010170240d500340b01e00c10f249104075402c207481d42010420407100c0107007081420b047c184100410090a5000f10700581103880480f4a001922201d08260380c0185401107800254140a11180c6001a41021450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 985057086 1250 985055836 985055861
    0x9150315050604030f0204020f070c140f09150d080c0d0522030816020619020a1a012117040609170c060301171c2615010f0215010603 59
    0x8034059039201402441e205500002c0c1450300103030010300140c1801e8000344070f5084070542e0300703140c020f454481d800d03601e1068200704c00714550100050418a04800a9104401d08440301c20550411140b440300051716100140d00807108407890f00b061042004c03d03034229401080c151140299541c8005001d40d01c44ca0300c0c9a0403010b60071440f950131703030502c0d034000039a80d1001c0d0a52900312400c08080e010050020100d1b8008820003031409034100d2803119080c130481d19002040c040c0ca161030702d02080306c14114a8a040e007045401000b00c0080c8580c2140100c1156900480304005800d0140c4003030406955514004c000081c0000e030f603548004a032040310b00c1011150a00c0209605954540b0032203c080e627402441800140011201c0c3d4120079100445d810407164032a64060520b41c4807010b000c1c903007003c9840011146680d02501003805540045031611380814541040c98041000320004900d042000341104540382d01d0003084520910f2011081040c4030750b960310001406412600d0306075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 985058336 1250 985057086 985057121
    0x3030d0c110a121b02182707060c151a01140708091002030d06060315090509071a120906190e0d14040e0f090610180c091503 55
    0x401d800204240529980c002c1d440c0e2030260400340c045900c09a804542c8810314699102c540060303a40f10303140030f001611101101d02500c2d00015600c03c0c3c1003c0481e1145540342042080c82e1000040742c21010f98000342041f07121103001c2d090401c100c4800c2880030b1442e40c0382c6141200304c04403982c524410000f00340d9808c0b5940c0b8000c24002030a01a0344001400980c05002d403440602d004d5903828182d805900c100c0b400c05e8005603440040c2ca00c107510a4000c265903000b4510308000a811010281484e8201480306040402010f40e462580f84201c1590708101082080154503000450b0035058500c6081301c81410042040d5807213980686861170058508584910054100d00070f0100c1c08a403000035001c2e080140310141d800520b0a000703894162400c2001146044851803200c2c001c40c4149603401407860031000c1d59103440405455601d500842a00411003074010f14034014000b000b10401189018281c03105440c6104580c208064600c034400314100e8095044d40300840130708081410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 985059586 1250 985058336 985058357
    0x1608070506090f0714010e0910080618031c0212010b0d140108060f04020111150a0606020c0312090f130504020310061a1b01050702030a020f010c0e1002070503030d0c 73
    0xa43c0c0e5400242520510760000300040041c0e2a5002c4000351145c0181007451030300004800007000d4080c119065000920f0040c400d02c8201410840c0342d5004180b0317034410b0340101c50401c0c0d490b070b640100700c201c5100c0403090720070828064813501602d440c251401991000b03540c591048030714580000c030310111418603100c0300012003c02403080c00c3c1285e00903c06015951940c945040542c00c004106030706000b0201844a1500e000304404580100d18049660181c28581c109909480003644403008651021400350860790740450360328600c0404000b07d6903204030300b0000c21403034070701c480c40980e02c41d420a068540ea0309881c0c00a80c030551080307041c0c80340201c0c1e0842200480c0c0046c0101c0d103510351000b0746080751808040080c0b8449130344031503c000c90b844812200d401d507001161410010f03080856035001e080c0d01089110850340c0500c0080c0441380c292800100414000245e041c0716030709c1d54a4240f2050300078080007000e0030380902074aa40d01c02d04130958000e0161400070b80000f4024400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 985060836 1250 985059586 985059601
    0x305071205040302130504060e0f010903090e15090901090b0406050f0f0708070c03020322032d02010e0d051e0d030603020f010305092e0b060c1507051608070506 71
    0x201d506aa41c0107000c1700681d0038011000c1d0081c800100700716170441d6501d8501c6c030702c0c000422401068000c02c02c0080703481109894010200d0600d940300040412151040c007004030400c4d206540d00400607589201d007031f40e42c2c000b440e015158116010380000400001e000601940c1e030400340c8140003150398100d05032500c5080c0c0030011021503580d4005140e100c0451301441c4030769106400c2602900c1224204074039442d4049000b03068101d003c0d10f007400000700b0020400741c1100c0da85203a90031200210a908030210f0303042a0305203500000d04004003072201c01d03a1980e0380d041004245800c6411604c404080569483c00d00d03903980120009841884450301449109019071820703281e01412492026444400544c0502005003524840e40164071007518103a0202240c43d4240c1503007c1e03040c03510700c122001a0100c4420481d614020001000440c503a02e030300048120340c01c0041500320001c0d558001c821103960107003165104c114080c00500c81c1c107000200700541950741c051010b644c600e894014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 985062086 1250 985060836 985060847
    0x506070308070810180911030f0a02010c020117070206150f0d02040902120a050309100c08030601120e190b0a15141809010f061a0f030a0905010903050712 68
    0x1001800201008002402c1c644901034242d00300c1c2c02e41816081d05912584000c54029a810300380c200207588030580405c3c840342e0080640d80d0002074000d0500d1320602c1e0f125507161a91084041d0512546455903011644101425101c5032008407140e10903043c01c010003900c0da003041e41e000f242e030141c140550f003407403402082110341c000b40242003503000e00241e0b0901020302411039050381c1c401e14854817100c04c0141403007030300358007031090f4080e5642e407103100104014094129800010050194901000605540c0440b5000602402c15001e040c820100c01005401d410400441d140944036005035032921076400e1180c0c552007000c0d0504d00365a031400c82c101701c4440300f03140b29185020703480401a80b0104889a1907099020745107540e0b80000b107060000840381074500860f160b55036200c01c080e0080c18801c51020700000d41076100c8020000072070040500442d40001048a8008040340307002900d54007500c421a0b205000340010309140c240034015402c1540203640c090040c2003c45100c52051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 985063336 1250 985062086 985062097
    0x60e010e06311e2c13061512020a0902030f01051210050f16111b01091a030403020f0c03100225051c110c0411040e0106180506 56
    0x260141103042d0741c1891204682c0040d0100300c503000b05803000c11107241c11540598000e8080070100296440c00382161040301324034000580d071500c1e425071100200c50741d01c44a600080005c040e6040d1100790309022000300701c640c500701032100706600001078004d4400481c0c4003c030300840300100c0082d520400401a0302c4212459a0001d54010040c0310510b028885d003a5001408000c4540340d24912009000b114015a8484a032590107010000c0e0500c41030706500a001e03941c1782242085541420b1240d580b43c801e0008005540b49103a840e915900c14044680180010200010380d1080d070030102e2040e40c0107031000d60041c00ba01c0708140e03002070009504c48545201030024a602c40a500e848002500302d18442640b84000d0206140b40c0c0390181008e051441c080c00140000500d801021824443c441c50400180410b10104803000c05010444d044051411780d004504910030300301c2205144202c0c2c01c170000d42c100c0a030010500c07692008810303090583e418030603030307000b51580c0420003e030048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 985064586 1250 985063336 985063357
    0x1f0e070f0914090a02010f140f040504060902090307050603090c06120603010608060115140f1c0e1516140d05060102010b01080112140c0a060503061302040f0911070c060e010e06 78
    0x1004c40c03500551081200d81ca01619514084c081014020040e24142e07102511100b403100c40403c040c0101d1800380700e0100100f00c01c140851401c114480442c0e1501e5040c496203108410110000c4d401c00001c2c0000c40d0842c400401d216900d44140c64541500442980c00320301035032134031202190705103000a160f8181ca07118610840c00e20140312041b6581e400c08400c0345a104418004502c2c1400c100c000380c1500002d80b0907a8203400d440c00c05640884410840c03d5102c0d41c040047c0901600c8500c100ba5040100807030003003111286e1f018240c41e00800c4054481404a00143c1c184064103543e1142d40544002d9009000c880401001102e001a082c02050805424140e0b00780c00a840304010041c0561504107540c0307481c100c0c0d0002400c21103c0c1d030240000c0351000041003035510b40000b031184a0040010110304003814100c005c03e122896011f91503446984400d8070003002e0900c0705446c0d1a5074400c10030207100381c64000c001c00e100c2c02401c010780410031250304c83d001d61134942c0c20744585198 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 985065836 1250 985064586 985064593
    0xf111c1202070825050316080d090503190503130206180a0f030b0108120f09010c151e020703020d0c050a060f0b04200a14070206070c0e0a0e1f0e070f091409 69
    0xc007035000c00c0b41f40f0f00c00b0001c0311b0710b0344200600080c0b03003068000d482805000d50047e540b581940701940441b110215204000c20504000300440c000130000720003541030f0155006512903512030151200d07a0780309020943d1054075001d00281e1060120b24260a8a1040c1e440c0880e59a0300e030802940c0d00c56006ea95080a2400d02c0b0300807040100001410000005160010a048854882e119402d201200b42c0351741c2c544500040c414a6441080450305c0644070714214546042c82c0c400035100c1120300c1e0b0070820081d1881402041c48010031100d18045d412900070440202e00400e040010000c4405082c0241d090005419503030300d05449290040300440c5441c4d1414260045c02c4030390443c1c0000200405209111039005a21180b02400e42c26201e41d10310700040d030400c4500f20110300e008003044911030601d01c05d241a400d0200b13081000b40c2c5a000b0600408480b242c1c01006009102c111782424492100d00084c01c1e68455540c00407103080c1c40d8104664104004040d203000400c9518032103950 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 985067086 1250 985065836 985065847
    0x10150f05122d091506031504080309010e0f07091d01050a060e0121081b0a0f050105010f0b120c090415050a1e14010c020a0311010f111c12020708250503 67
    0x101c1d0401075640c4a078001b0103841d0320341d50b403045e20005484107540907500400040200704c1e040501748103000c20105144014801c252009501f0f40d961070b6280101d000c03403506c1c0c1944110914480841c070754051984802484649003110708603000b071506114040b11215034000004001c2c0d41c0643d03031811021890380450101d4074980302d414040e8443c60300300004031940d00036038610315824848000010b215054000c010f0300c890078000d094a0040e004502c040118030702c00c0156a01d14812511010000c02421615503a1000340003924068039229507046420011042001c8083c0c240300e0007512000c407540d856041d2034a0b910100300030b5a003010901c1c0891003a050041c00110600030a000c441494881c801d4140f0341d020a01c20509540222000c441000790a8095a003080c00e407032030b00d10302d4600001c8006201400300ea0742e15960002c1003407a106032180a84980c81000f150b188040500d2040d540c030f0308a413401210541c4003d15004056261004c512030306c1000b95624030b07102d03400000850411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 985068336 1250 985067086 985067113
    0x30115080309011e02250803040303080103060c0201111606140a050a0f0b130b0f1c120f0903021c060c021011070c0e070c06060f060810150f05122d09 66
    0x30403103542140006d02c00b40000d400900f00000d1020390311035030f2200195455480c0060984211400860659041450300781442001b00c090314460503d401401c6440c148908024004101404002482c2c0420700300304440c40342c05400c45030051030007480070800b002059030984100c6891800c0250b00c60000403540e607201d43c254021032243c0707100500d440745031035103034001941c1c083d110940400d45448002c40e034001d100b1250b40280402c00d8908000320704c1d031030f0f003031000305a07030501c1c0002403054018000840f0902060f4404051851b03008204000b041860b4401075502c448110f41c00b003040f0f08000c014040e8140f00411388210991024894920605055440f2401c4030000c080c54100f02e46210040041001801804020040001c06c110b1442c14000c00400105004150030f0305407080b05010424620b040f5400080391080340340c02440076000c9001100d4a2060070300c008140e04008060001c0c50004078003c20700c80b00fa001c0c605c81912900b1074000e42d01101158449515000f070821204070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 985069586 1250 985068336 985068373
    0x303010b1b0a140d170c0a02030c1506043b100908070c0e0f07140c0708011418031606020d0516080a0902060711030115080309011e02 59
    0x1405820080700c400c4076100c0140300e2800002c44010f0740d00b40341c6000e00d80302c108000d001c665102991072070003c03040c108040340d90080d900301400c80010700100244660031144240241c0f60075802407001d0714450700d90602c107005050010b8035060300c10b501c1d083e445c0002c81400d407006050b100514032480614070700e1000340705918003507180c4500b5130302035a0600943e180461180d420450b03c640000c6468030407a0038035103080409074001d0b2241164034418842c40b0b41c480010325a00c25240d2400c0d01503601c407010101124015262007000d80c1c400c3c1031000c51142011b4002001c10301e00514441c04a640c2e400590780e85050000c8200c0c4981c00030040a24100c40d00c9140b15005801981e02502c1d0040b010b01e2401101c3c0100d9100402201c3c015840c0703022503200300c5140d04080d200c001405400690703000075079584500c45d0300070000045031405d911180c0b801e4002e000300905450440b59880e81d00d03c042501c035404500000c2c0081c0030440ca031030000702100312031403e02c81f103a80107209003a09407001501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 985070836 1250 985069586 985069597
    0x2060904021803011b0c110a08120d0b010c1109060a0b0c0f0f01090209011707030f1b0f050f091005040501060c060c03051e13120210140735011d060f01020303010b 72
    0x104020003880205141000300900c0c02e10062005c8403e07600c0620792f982e80300321a05200528100900c41c1000c0001c5a1145501018000204e031030159540380c1e00c000807000003560707006640c2100003154840d40c032800800c1040700c41c0c2c0c13041d00340d4110340c1007103010b40d00300c5490340c500275440020742005010000098a021444c40802022140075540f00c1c0c0750b181c0e48044154040300c40d01094800002030b0100f05070030030014506154965442c80c1004d002840203c202c00c0c0c0030303024684060010312170f1202d0880550081501800c2080196195031000300740000900c4103036405030410000003030040c4284180ca1040c440039031086080d00c01ca003154184440058281302c09407640c0e862aa01098646280d8004d0808a40040c50541c400540440a0720201088180f5a051031020041340c01e400c01e010040154240d5400e0702d00c2c140d405403a06d1540c0d07005001d0712003410b40c00001b02e81e5969400304000305078208840382601c0c0e40c031081084050500303540c00c6030043c4c00c2400100060407030b5401428 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 985071942 1106 985070836 985070839
    0x1305030f120307030b03010615020703020315040c0303050a12141504050c040b0f0c0109050106050906100f050d090f05100501150f0c02060904021803011b0c11 70
    0x1a000c001c3c036003402e15484091022076030340d00b9030294016041c0004000500c6607450307402903545407640401c1340a84201d60448070646015210b0034400c50f404001c0c00409815541c1c2140c041d0840102c11003403040040340c0c040c4010141c000c0210a040040b100a45031900d0001c0d69400c0014004c0140110329180c10300c00307440170f6001141c0c00e80d2502080681d503180400503454861165501e0344111794604100c0e201003003419080841250802c0b0f5012500d42c50352400c00c0a034060075a0400c002c00c00c00d41c10b0140e006c4c0114003414a00c41080d000150b83d06458480d18002c01036888211103035001709201c007441a10a1040a016000100c01064860544440684013002a03940d200034414000344040856403800c080328042d6201400c15520384005a03e050885198400030030303c41d500740100c4040e0b940810014201d00c580950710581d004120343c80300c4280080340111107 = true := by decide +kernel

theorem cover : BRFrame.Cov 984892086 985071942 := by
  have h0 := BRFrame.cov_init 984892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 984892086 ≤ n) (h2 : n < 985071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
