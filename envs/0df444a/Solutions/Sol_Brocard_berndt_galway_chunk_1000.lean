-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1000
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:44:43.584711+00:00
-- url     : https://prove2.me/submissions/3f3e03fc-16f9-4e1c-8d65-fa362351a9f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 179676258 ≤ n < 179856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 179677508 1250 179676258 179676271
    0x5060603070c2a1701111201210f08130509011d06030f03040b04060f020604080f0d2004061707020c010c080f0315030f0114010614040e01080304030209100f030f060e06 74
    0x70111138800d4414028007030001d007003480d40c243c0360800000070400021003005024504e08403151100e5400d03007c0c4070344001040b843e080b000c80c4030803c1d01d071f00300141c1c1548a444904c1701d15911460010b19400d02c6c000c094102e43e18013100a43d420aa280c0102c1c20364805842d43d139140c03040d21481039401e03006200400080c004080995034a929000e40981110065490201550400405c000200b00504200c0e10702980c50804140c2d82c10042813a8801400710b03d000f55401c03158117441c1102049a41c0061098504944503049032199581c80e1030200c10701200d40034016080854104070650143c00c01e10030440c840c2d0318031401d064890020a46a40048a202640d056141000d0940703040503c6980c0089483c03100a00540c07080a082c1040010f042c800d075010402c0410300706c8185000807040c0d80103032105c180c60301544e595402e0340a90f0707900640030036071003001460b010841800d84a28040300f201c0e000000b003610316145440c0c0303942d000d0003428103440c82c03502e420300548000d0042c00250711440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 179678758 1250 179677508 179677529
    0x41805071203020f07050a03080706020d060b0901030e2d07030b0403020601050a05371805060405070c050c010302090f0d030801062012070317071205060603070c2a 72
    0xc0007810024540450325a404190742c00082c42440103445807e070444c10b40782c004004507513580c95450324400078410603050018444c501400403031403000e804020201c03204240e8081c81803d154502c642e031660320941c101d007158180c038968010008055a9441d51105078042030390801d940e6030321405040b20b801c990481c01600054018800c510300804120003604090752030a0b03048601a005103464803440f00348402203410100b00c21192620020600d0103014100541c20084980980c440b001d044182c44642c803450a000024010b01c1c4251400305800740c01000401000303070b110006600030752101840f0340d00504d0740307240e03450952900381d040954140305e5541c4002c2503243c52401810340b01040c2100b8000b1550542d0700c00e440100041c034007881b20101c01001d0f81c601103841c0555840307001003251000c01070003204102001e9000300260b08607e0189074103000719980c901c104031084c8402c88186020483c590500c2e80400d400c0034030b64800485460413010300030040908008034413223075844003104a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 179680008 1250 179678758 179678789
    0x105041206060e01140306040b04020a1205160501020c1309050309090423010b060a1d04060b030718050a030b150604090f0b0f0d0f05031312020f0904080904180507 72
    0x1d25840f91540d00501d481210f00155440140020380c540782d0262003d0011001c10b0040340c103650750401004003d000307031703203910f40503100f2440c00d541c031040b80900c0141d140030207060008840d400891082c0040c3c40040c90014131055580c130200051002503c00d5450e84010700800c1c616032034150340301d4011401503081641d6020500d04d2464000ca1100400445d41d042607400d144640b10301c4265081c07145a420040d02003080035601a6002c1d0810b0307051507000d400c2c0280000c408444c14001c6010704203c1d6164280e6130a542310f00c1d520f10286100705034005c56088001c0001c504158000368005500380c00e050603501d0400c0c0003da0310b0304190070210803e5502c540100140e81c65100340411040b0545000c000001e8a6002400c010245880038200070f5003c04142c04000d400e00c01c035400b0302e031110b000c10f803c15114086c0003529504e41000b00c1c01031881e50a0002c240c0f4000c401a84074a034811000e510305114003040c4405070082540184100000e6880200051002d02481002d010400c4104000303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 179681258 1250 179680008 179680019
    0x9020a030912030b0105040b1b03031f0b030c0316020f0f060601090609030b1302120312061302031014061309020a0311070510110409090f020102010e120306040b010504120606 77
    0x4002e044400d10030305140c002400080c0c1d03004426682102c01104086440d910308210740c0c49802004090420140000010810f0000740340d1010754a80c03120b1950880a203840b003680d0780320b40c80306803001171501500707000207444400d0b0b140b054180c2100c031788142c403040c0c556100d0242c40c1c21140070b407501e0703607810420030482e00c0e503803040191004011a141203600c080c59074680340c4801034060943e00010706200142c00940d10b07180d007074100ca400300d5401c6076a00d0010340c01e544860070082da00e591086100c00c110130100d90340c900030b03070780100c1440106080540c03030000c4c0c08145059405969401c001c06201800000184207042c4004203142c0b00c0141c0d4030450b800d00101101c064041036141080144046c00c041100002d206000c9001c1940009841c0300e00c449402d802e008642c8100801030405101b013042150000020524500c00e0f00240455180840101e03100e804001d24190802c006100049161400340c00c030340074100040c10310340d240c15201e01e800090742c1568841515107680740c8808021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 179682508 1250 179681258 179681273
    0x1e030d0c050607021f09030c0f05010e01180506070c17070c1a07080403170d0e0d0e040c0e090a0f0606051809070e131103180f0111040501110709020a0309 68
    0x5103c425032001c5d00d0807545545000142c0616035856040c0d0f6580e804110003054001d03007821104603000094822078240b24588030703020384102ca0012050354240010f003950000d103c118288a01e6010b0040c00c45d0396545c000032110302000c03d005031601010010400c021409030b100504031140030764106c003035030f9042c040c1a206140000e204410042070412a0b400451000030959007641e074001c04403480910b02844004603409440c008410181c5024550940c602d400180040d03039254a4907129820303081e1b4010441160700c1403d442012940b12203400459203003501d03c15501041d83c50b0006280841f22040e007040300c11640020011400000c0c10980404080899510300d91049501c606185011080140a001200c070411701640040c11404642000c81c2c210003460250346240640301e00c0c16030000c0a050444000881a50148480042c850101806102c103060030800300d4904c2c052502d00115070056104807222035034010a4404101010f0a000034081100c003a40c000c2400b51300c81c181740c0c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 179683758 1250 179682508 179682511
    0x512030a02070503210c0703022106060906150901021203040b040b0a091203020d02091f1b08181f020a020405180c060a030e060f01030c05060301030f021e030d0c0506 73
    0x130303c80e902484000e1090302d8280711490110549850360790b03d81005070340e110318144158000035401080301c00c11190342c0c03000b1301440789120403402c1255400d07103811040c1b0200c400141c2d2846e0b049a0203901c00441612964014012044184102c440c184400c10030015142c02c00d643c1141c400d0500000c0c4020300094001e004c1c1c2001c2c00510411001d0704540e142000d0720102c01c0500d090603004110300c000343d4440c1e070540711000006072004030020003081212811012000c00304001c209000410380c0c950b9511051000c43c0360b030100c8010300c0d102111650100000324103000650100c0c51b0341082426006030001880b1070b00c409d40040c002c0c05c01c01d10403c001d8450080224883c400c1081c440028402c0008009040c10800e50300c0c0381c1e6610048800b180606a9500b0085c5588100014444a1640c0c0945103048a00840a0168064072041049114402840042c001940746450107016180a2000da409481001c0c01c50b0314200c8003002203401c0c200d40800c85004510380e00b000700180f100500885 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 179685008 1250 179683758 179683769
    0x13050c0405150c03070f020d0f03081b130509041103070603050105011d010f0c03050d0e0a11040501050d17090901080102070309050108100b07060209060c0a17070305030105190512030a0207 83
    0x50f04105001c2c100c1a580c0c0140c00b000b0340303907990b5400d040c010f544400c0c072980c0070260814501d1098054600300a8a042000d44070f0503944143c1e200c6400f11002403005841c41740300d002c048800d0151515040004514014205480154072207000400301c1c0c4e81080444024a00ca85010515602d82000036010310700c0c4c8801d015180c80d0040c051500350784d014880c0b052060032410110014107a40c00d048985002c0c4281480c48507141c100d0620000700c0008900d04000d104544441814042600f40010703074001380300d200d4004200003c4000000c02141d290600d0310300742d0124909010005000454a400c01c2c1c0c4403001d5a58005129000e050340500c464000d04001c0c02c0010040c103008002e141c8040851250060036480810031404012a90301100c541c48001840140ca5110300003c4a03100d0060840071640d41103c0700d6482c2c0301c1c612100a8420f1503400d84c54003070544e842c0c4814052048a62001400c20410030070020400780c0e1684141c1315002082c000039622010f032040c000e40740c110540c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 179686258 1250 179685008 179685049
    0xc190f180b090904141605150703020d05030702100606030c08060301060b030711150115080114090604020c01090b071806110c1c05030d05150d03090b030613050c0405 73
    0x14042504078034116a142d0704181c42442007a03540e030070305481c1000c0b0340652014500400c60440d52201c2c12007a0754041d900112015500f6000c1829140d086200740e0400401580100018640d0540210090b50380f0020034016036070580c544d1080c24085078042e0300030b0b2000c01c1d81e03100042d44441e80882000d90019003039000700a003604003508200d540c080101450f0400101110703801d9000000e00c4082c49140300036810004558543c03013183c05290400c09000000784448000192110a007a0400380541c0301904400351510742d541030101941c8034900f00c039013564071400000001185040c0b82440340d034803a13540d40101d1814110012158030160b0214040201c000c1e40140c00030804940300701d10400466050090030580c0c0c0340030301741461212014286001c0402d50301c50390000f41e0005441503000c050840f031704a01241c00c0141c140b0030b442c405000a11101c1040c07014240c0ac000850300808001c1c01c40240b40703a400004415200c007101c00440491002c5410081420402051050011000d45 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 179687508 1250 179686258 179686307
    0x1060302070c0302040b0409151b0216061b050d110d020c061204050a021e010305130b0a1a1909050a0501030213020d1b050918010614030c190f 63
    0xd95107000b500b2070101a200b15a1507548540eaa940d81d03025032403566005c55141c0d44490146107510003498a0070710403140011001c0a0318000b44003041301e8a900d40810840010142810403c48085540851401e41c2c8036060300b5040100d1400c025604005041ea03995100c0c441041c10807030701b8440d00c1440501550b1010345544007a07903904017641c100d60a060b9a41c519551a0704005240c0455480040d4215603841c0c60f4200c510948162216512400e8800740820b44604122101802030460013508100c08600030401c0340d0901d4100307000f6054146101051134200c0000610500302641241c1500b4003414400c00c0800d080d40107443c0d00207140c0404208944c950b8010410500c0700c042c00b00d0205c0d070700207240312940300c0702d40c80707074401100d24165410915900d0380301800381c0d403146d00c0130ba1240030781c07501e4000064040c43c4214103882081e5119000740d207012070445c2c0380340c1001d4100c503211202032028403000c41e9495a001c0d02c000903a587e40c003945195240143c102c0391909204986103c2001c3e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 179688758 1250 179687508 179687513
    0x203100f0b0a05190905040f06060308120112031418090c0915040503030702190b0409061701090519140a030804030f0309050c06092101020d1a03060a0b01110111120106030207 77
    0xa4000d046030012003020506d07030307503618242d80121402040140418030307050000c4144a081000750109411301d000d0b0a809903210045049130500c0b01000a00088121000c1c01225034000702402c0040b00c01c0509450881210300002e001110881d8948268180450f542c0c0c2c0510740340d440b40d00c02d20145508140703050b040c500441e86a2290440190240c0b402e03c03000c617240510f802c000c00040c031160480f0741e00d543e02e0b4981e240c00b4016070300c1002c80350303050100c8900c00301a041c424190303030350751080c005c12090308846a41c1c031504011300b4003600d54450140c8605030a007014480492680e00c6a41d94081505e82031030007030b0869003424000002c03d45000341030741c0010f90009100750102c20845596445000d000c0000d4070140110304540030503400c4c81103c0550501c15000340290318040081401544e058030b80c004942003001a41c03681c5644840041a40b035401c40d441614401410302d04500204641f00c00c82d07003507a400404840c0781280024042803100500c1f001a030142025203010751030302d81c9030b8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 179690008 1250 179688758 179688799
    0xc10080103050d0e0d05100c2601030624080105220c0b0f091c05100b15070218040309090b06040501050d0b010201020d06030309050306061512040203100f0b0a05 71
    0x143c020820f102d0005943d203004e68500b081001700551010840c4c0d49154001d5101d0040c058940348a00414400500f50f800e14840f02041c0711042c3c40318594450580c42c40c0c8480c1c000d030218001c0d000b411810344084c0c0041d41a04c041820181c000c4c1400800d450814412401d0301c0d86030030101001c507140900b9944002988070740c0301c80c211002c02082039100c141c081c0f898001403050b8502d45d0760003400160510010b40382801038010305800340742990500d142612031002912112030210f907008845030351000c0c00c0004240030b0140107001405c0c01c010514240f50036817004006481c180c010504940c1d00300080140c0d40200440b4000a4984c0c40c06c2903d44800684030740601da402156403500e468a664491340300354161031a5101c000c4090103c0c5541e42809402d40f0601e005003406401034400003040e86c03d1a09500c040c0320f00b40e003581407030291031030340d42e040c5010094012680750040040b419010030181c01401c100203065540001c001c82500c04006411815900c014000d07621407007450705c0030b820b9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 179691258 1250 179690008 179690023
    0x2090a0303050c070e160f0f02031b0a0506070801090b0102070b090909010e120c060906010b04060c1113060503060604051504090309050a0306050106140c0a0206070618050c1008010305 81
    0x1424100d840b90340040000f800c1c4850394110701404521482000000c100d022041c1481c00303007c0d15505030315850a4000c035940907420180201590007080401d84040d803903182c000d030070704090050781c84800b1645d139141c4c101501620244c0000b00d1110041c441c0e110b01c0c5c0b041c2100601c090005016940c80c2c1011400366000e0091360f40d2140f00d00340000f43e0a071400b0340044885613045004d8900030b0540c2402008190442d040035002c030310400300042c10305840051441d058400740904607060600e0f21208032012000742e481159284185201000e0715110859002188d043c10710300130425608150500d0b2904500030801c51096040a0601400c0c00150f000034000e03c00984000c91400d103142010b56070110113034029a0007403507847c000018004103a00442c181c030100c0e613444240c0f8450300c0009909000707400c100b15007a0400086a001441e0482c018010340b4800e0001003017488c011451301d0b6292400440944003a040f03400501d43c80d02e02004200003c0030f150414200c1541141c07a01a61840c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 179692508 1250 179691258 179691263
    0x7080705030706050913052e08190507182918060103090213050702061e0f0a0b031005040c050a0305060a1a0306011409160516020604050406080a020f0402090a03 71
    0x4001031008030369203030003100c03001980d03480c14140f00d80e0800c03802d4405c020703d92500e20401b4504504c07103903010310b561008e100200e03110708000b8000384414003080c041d8017032203171130455144c411207100041c402c0c001d0f841c0d604210300406000990325441c8001c4100301460410118552020001606169031070100700766030004411407400c1e0a66612005030024011a04084d601c104820f00128082c511070f01310720301c9104a50b0a640498648000c441411440c1001e0100d49001050010700300101411443d0362183e004000420407031601004281031031902c400c0007400d5500c900410050082c60207149004000c1528101d2020745581c0b516512403034040d00c210314803130301d40c909100080c2d45170001c2d80350100c000301a95440c0d656240b07880d800007540c508880c002e421000010349500c50052207843c0601064450724a000c4083e41050004110810103c2e03010b4400d010108894a440c81060060007045000308003254150040080071141c020010f8411401000389003140d1722101c440030b04503075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 179693758 1250 179692508 179692517
    0x51506100c02030709060905040516080a080307020a1203050a06140d0201050304110619020c010804080703030c020708060114091602150406020403060f0f0b18010b090604030501060f0807080705030706 88
    0x651440004e003000e4075640020f046904096000c10844019440280240d2260044810380b00310b840d200145407103284180c07450b0760400e140000200700c985000b594410014410340725100c0f4250b9985a0710680326039402c0000c1e40d07807000c012034059280300d01300181103045030701c00403142182c00080e405808618000d041190100c041400c1001d4000c01d4403821000400c895101c0b45465a40b12065000030004030041c803070320350f0001c490b5003d0312465016030b4000000303a18110f9152000d4018150b5400305a045104011002400000602096020f003096078801d01c01c0d0b03d6180304101c00041c024003c412002c841d00d6500d00a00d0300012041800d00400d00f002106036900d08082d00240603d50029154031f0810b00341c1c44402160754401d4100729000c0c031080010103c2003043c4440707403040c884002d650112100041c05800c2c0b5040103810000001030240303280a460781d41d02429a4a00e43c40340001c80c01a00040c0b11026044c001c001c0600801c000070641103207401e00099680840d4460301c810300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 179695008 1250 179693758 179693777
    0x612020706020a0c02030c01020f0c010f121a10050721053105190603050712020c0601060306090504150f020f04030507080d05130b0f0f0a08040605010801020a020307080901171305150610 82
    0xa3b010b86514500a0385903201000706560100e40c1c0c0700349186085a07144a460700402010350f05010f00d0603107100d643c03c08070055240b0920f8090b84050005a031110301400400c1c44000342401c540d000402c4680301d5400030702152008000c00c0b03600703c115908040e10650040220140c26100042441e080314490326000c81c031522404400e0300c200359142d09141a2900004401803007400014006048403140d541c20060f04c1d580303441038002c13075030159030051880520000390b11804110307800200d001c1040340e10051802d50360700c1008070729078415841107640e41c00c000f00410041c00d090100201920f12407c02a1408005070142c460340c0306c0318010281d00d1007010401ca10803181100070354441c010f800c0c0c55907650b00c800c944080c1c00a041183c044a00900b0b0900124560f4018000d544040c0340540095080400c995242c10103500005101410088e420341c40a4082006031045806689a00400e180e1110141072050a01c0110005422031003160018414242c80d00c84040144580600d0200c054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 179696258 1250 179695008 179695037
    0x603030c08130e011e090e1009020a052206140607140a02090108060609010602012d0e060103140c04050f01210b010602031305030607090612020706020a0c02030c01020f0c01 76
    0x600d503068102000d00f18110380041204a10402c090840c1011381349142d42c3d8560306c008074415103003094041e031201d800c03824084502c00c0c1c05410106000b0700c010f044014040d00c0c1c40c0840c00e022550707001c00e5550440d2229041e90011301e80320703c1d0003070001440307405050007015010810600c1400c03402001410117051b0b00381004014000918440d60061200751203594900100b035642d00c040d15820b105100a900001e01c140c014030071a20000700d552103010019290307a152012f4403194a02e92003001c0e4a88081400341c201c10300034036020314450102441ca40c1c01500030300c0d2601c0000310300680190714000600c944403891010042c116011a5000b03480d64032030035014200030503005030080900070b0440001c90311540210141003590a0000c1141074550343d603042503a6600181d411001080c030305c10007400601c0c4030f1600d50180c144102409031811400e540d03260103d90191080000007901d200c8040114038091180d01100c2c6000d200510040c03040c0208917031107103a11801075060005415a1985 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 179697508 1250 179696258 179696287
    0x151e010e1306020310030201030b0901080d050a021c03061e0e04020402090102190b01060e1503010b07031404080d08091b0103020c0a05060411010f08100909080f1602040f0603030c08 80
    0x71015804031065440707081600301606002204c0c0000c9020074208650018a42090b41d4254100c404690050a01b2a002d0300144c07503640c040615881180030341d0700e401d2003449075034601d2592269590f50008200d86804440c00c0c4180d0264203c5124000391802040f03407005003070030140c209404035001a640c1c1a05c50041c0d25241001150000f900513038420030007808074002485040711500e4030380d9075200541d0001c21018154440007403500400c05d0006000ca01400006441c61034130908041c034803841c920205042d160010f60064000e9401480d44c0c0c0318441c1c3c85213007903422801c09001450404421000b04558142031045281015408101841640c204000100b1001d41040544034a03090604003950f03903001801d0003d020030445000c0d034000c14812140c5ca0322420418131042d07811410040c000c0060001110292401d000a1110305220a82c0310020071a80541c511526461a07140c41408140c5001c00500240036241c04d20401c003103504041e511071201d5000e446595140d540018080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 179698758 1250 179697508 179697541
    0x120709020315180a06080a02061605070302150d0c0903050607030b061b010e010e0f1c0201060b030a0b15030c0d0e070e01270b0d08030403020c12151e010e 68
    0xf43d1000018651081400818030564040c0d1a03130034040c448a511a041ca0359100d243c040002e4100e14100a40921b042e80c003102c55855511a500303035100141c0d46c2d00041c40d80c0b014008a04880f40c80000c0c007490484c142d1281650b00e086074100b191019155413921a00d65034000d01c800c052545072440d1070410f503504401c407074003803448040100c4d840c844c04030340c3c500800751000c030510300350301c5c0400d820740c1940d000600c03000820048000708a20b54a010007444145034440d086c0080d99259071707002c604002a100030310300c030b140c210200052900c41e035410000d01c405200e5000100742020414000d100c6440c10072201040305060713022030b950402004041c6000d007117030b200c03480c110700700b0b400451031050305800284490b0540560900e5040701200240880b451400c80642c0b213400f0015000c001245e05028540c0b0500a0040d68428260100460303520030300b8205002c05034000900140030b00880900890700052012901e0000c4200c488071010804818040c108040c20b1560001e59070700308a41110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 179700008 1250 179698758 179698801
    0x15020a240f06080c0312070809060f070c17190c2102100203031b09010c030305040501020702030604080a26040320010f091106031509070e0604231207090203 69
    0x1c110243e5a1810581c0700d51582008610074015884081b00020816003a5024150001c6800b46400c00c1c3c031040101543c0000010787c2e501c407080c0003240214076082d40c1b18004125a4408402c04d56200d0b030507504162591074800c0c50031440340f583e47c0101c0d028504001c103444050200c8089403031803c0c104410907590036802035014400082144442d64040065801020240c0404080207000200c20702c050080d2003c00740000d80b03d410010100e40702c0c2c0c11443d00140510001072410b0220340100f4140441110160f0300c0b080c0c0001c54808180d809403860020300011141c00b540c1c0050901c604504901c090405003c2100c603050a40c0b030120303600340103500401064020852480c10f0354402e030103007036001b805440d00413640b1030702d13225402c000044174410780e07000051070040c0861404201c1503d0014000a0800c841c001790482c66403601401000034010545407540c42d540c8405481e01c04c650003506880c050700b05403041c00d544820004400042d14510040903849a80718614060400c0c500c1e04107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 179701258 1250 179700008 179700011
    0xa0207090b01090302120106090c050a020c040b01030f15050f030304061d01020f10051e390d39050a050928050a0b0409110d140115020a240f 62
    0x260344d441c0c6c0c150300010460b44400301c01d01141000b450162418003400b09143c001d40c0158004a005203810741c41459811014100022100d83c00740c00031003154105888c0500c810090001801686462401000c95010840080d4545400d2681c000e14055a0650543c2214040c1f10f4010303ea070b00a001d01c0b980010440121005c0650800101c805807500744c4503503a9104685840d0b04d40503811300d110501c24440c21404c1003402d071041d4040b00314074201c005154400c00c4c042d09443c0ca0916080000c142421086d000411002d04d052010420303a000e5560002d951080302d030748030320034620955070082035440d2030401645a0100080c242c2e01032180030005039005600c001081100e225003410104490074002c1800301e840c1c0ca40d400e0000c20340d118020351040b80c1d42444100b00042854000c07208600a2200e0030342400303105001038050300c141d00301000100e5225801440102c0302c4075004994422a03100034440001e0540f107000032444000e90b62521080400321024030b51907540c00251040340c0b00b500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 179702508 1250 179701258 179701279
    0x31104020f190e0a0303051209070504021603030509071a030403050706050c043206090a150305160504030b130f0b040c14010507020307090c09030f05030406030c050a0207090b01090302 81
    0x40c241c4400c40700107488004240c0f4030389912954103001303480c0802d49500d070303c526190800d00d5039000d034900001814640640700f2000042115100c0340040c20511012001c4604010042d29001c7c00b550001407502900394001d2000300580c0445104003e1180c580754201603403615030b0b0030101e46074400c0500180c83c841c203120502c140010140c0081007240c08140301c1058031803120212141420404041001800e002e0304a92030320701d0940010680d000c00104079000480e555181307802281c10401d101c0d80825a40d10800182e1403c140c0300c100c06509a1522504d09800d40e40c0362140c40384050314410424a00500ca0b03410000c8420211011703a030019040c100c940350524005105130a0350144241d07580c040040f8400740d5003e103003a120031950081c09000d040d800c002d090030040c040d9600c44400c11102440c0000450b440300130001406009901541c1e60ba4101074001d01038034000c201d24010018104184d004d00c640c00704140003550842a00450030794580d000485805e41d8130f400c003a43c0300304440d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 179703758 1250 179702508 179702527
    0x2010504030b1e090c0102060f060a0f09020901031506090b1e0327070501020a260706020403051203070c0f0510020a0306150503040512130b04090207020102070e090304031104020f 79
    0xb60b403003020740e5007032200f003180c2c0d1800c0c0c1d00e40e00c400c02c201d40d26007d640b01201086811220214441d40044040c100c00000c40c0d8071010306200404660100f00070503030005041e109941d0501810042d81c4117407418203401443c001004000422074400c142e050b003000714030040c0202ca000b0ad5170803910280742c601512070a0203070039070f200408610000022001d800c03010220002d004543d180031178405070041e1410b006103440e5030720f40648942441101c40542c800c2d00344102107801c083d110950003858016152401c514100b480c010308820b81c1c0d846a8003c0c03041202d03c5a201e80c41600b550b80c0155000b1510960f8600103280c0307460341d018a919180007141d0102e00541c107500c1a801c036660358240c1107001c4c0d16404240d03100e2000303490281594200442000c1600e85400062514000c89a9a0419640e564201c8000303a0096080f595003103400040907020356134100705010281101e40b14001c0e41d0304040300615a2446103200c001c0242580f003846031003694880d41541c60070840054983ea0358520782 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 179705008 1250 179703758 179703781
    0x4030606080c090105090613050c0903150a060b1312020103060801020d0e070e0108030703050307140d090614101401020c06040f030b01080c0904030305180106090203010f06020f030304060902010504030b 89
    0x2200e007500400b0907800020305c501c1c210200c240241d030041c012070400341a003a03000c17000c2c040040c02038140400800207840207880030407480f00000301540754580c40307040c8404080c0540d8055406004521028000c180b82070400009487c201d80303030311110b003c05410510043e00500129070002e840c652000c5071110ba084980d030072100c07000c80303840d00b5070b0b08040e181e00c000c01801c9002c1c0100c200680c018021034001a0082009541246642c10030b840041c080240e4071400da40001040c0c0340003915880030354200a51f90254940d00c011006c00c40c0220b1070010041e416042d10b900c42d03400c410b81d60000540d4142d000f032080038981c10029080720b50f100c0e1076030704008002d06140b104444451840000040c9a84003040709140b204006000c00e403980c031a0b803822809000d02900f40700707a60510780b00303000b00d14209104100080c481003034090b1310b81d89400305480700211258420403d5400001207031003481c001100b147c4c0c1c45035000100080358451400100d075580543e070001000d41445000340031569800c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 179706258 1250 179705008 179705023
    0x607080f0708160f03093306030f1e05030301030807020a050915061b0102041202030c010c0807020603100810050106032409181209030507050f030a060c0210230c07080307050703050403060608 84
    0xc00c00040400c40501f850b030049440b40c5c0300180c100c0614200c0500000c0400c5000c220006444103018040c1000d0385a4030b05643c001e0303000f1140303444001118001c50074200c241c4c100800085400d102585054401860410504420944502800a21080c000030304194035400000341c00001c40d01c1da500c8000721402085000c2c400c1e486441990002401584107102c01c10645521001c45820220180e0900002d600050010311001c0341904020401500c10449007202261800f404905545082d00203000c455071120403891503200440c4d0780d105450b241146100b02c950450700050461505001d010780304203800030003404852002104c800d102d0788030005209507405801580c00d00d81e81c4200b04907000785815417458258000d50300c0503001c111f095119600140a9005491840e450091020704a8518040f0306954441000c24029000b6103100c01c1540400c558901c1e516140064841c2016800010800e0741084000242141014480c0c82a103005652100d0103000c441d440fa81e03810f454294 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 179707508 1250 179706258 179706323
    0x1b1e080c0109050a2a03030e01020a06090602030f1602030912070f060c06050109090f02040f15080106060e030d080105240f120717070507080c0607080f0708160f0309 73
    0x6004101d04402656041d0b415500091a0001000c17640340d0703901540d140a0500c3c415066003d030182050103d8a640685403409200f48030069881c81d02c0c0c01041c4003650058450341c840c0b1480615906a150000200c07140b0600c11500e0184143e82050b1503458075030f40782c1103482c1f03540030030000040c12134000911445031031150781e00380b00036030300d6610784802c442c8400c0e400b502201640b0100000360529034050b0208100c10500405e08800d0782000c60b2259109030300045050b0340d03411080000765841409c29403000001c501500e584542e1a00040c4502818041c06100d01c1080000340b21066041320124035201200070398a40f54003450800044641201d01c0706510513009000260816110340d1101c480d038405803800c100c0c1921005012103070703034110310f008583c1c2070402c00c9002c1d00318504108003441032883d0390b40e44529280070003102d54011f0300501000d042c01086010700c86004d03907040b404d00c040038203880c1130702c8991990070040740503050292005c1d0072180b00c10001010180c2655100c1082d18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 179708758 1250 179707508 179707523
    0x130e01021213050a03050304060b0901140a1406070605090f0a03020c040b06090307060f020321090106120807022707020601030201020d020a110907200d1b1e080c0109050a 75
    0x81d20b41c0d12800407400000300003041600a0340b070a1001a000d040919005401000006140c100c1d000120380015820b800c1f507050016501881c040914210740c0980c09080b981d1a8032050617503440214055000c0c090000b4202c81d03c2e1000680031030320410488420303030010f900f00e80300c49405060213507c41c004040560b00070342c1801103840d158207080085800d040c501400600301e191411710112004900e000c0b0b110218003041003080300e49200e408004400740b4290495141d50f041907007509003142d8041c0e0003c40301c401d207007410101040d003500c01e86074415010b0b20700d0403410001d000403001c10422084000c042500c0071050214003075001803d80c4c1642d00c03c0e022101c60310440035099035a80c003510030042103c9080e120344880da00b40900200d4000c0d115040c900030014100781e541d0268246059030110550256180480e000e603c400d07941814201c0c61901081008236890b586102c0440090760000b0301001e12200f4100b104000c200c403080e18000b402045072000c5482d003a074842010050689201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 179710008 1250 179708758 179708761
    0x15120f02090a0e07090902030c0111120c06090d0c02030304090902011202030901020a0f02030c03160f02040518100231090516080c0301270f050c0301060318020a14130e010212 77
    0x605c101d20503c844140c0040090991355598401191142c09c05220300c0781c0fa008010802c04092403810150181c4031011002c1c0a9a1515500a61901c040c2d90729102c20040c0000c21400961000b104440503504000d43c049200c0040e400144c5544901804403050b252001003000a000d1040d40905901c100c0c0d940c4a44d00e899404004996a00500d002080d080d0820000d40f01940307140c0c01c0e0806e88600c84c000b0702c000903001e9000030741151001c483d00070000c0d02c00705030006800c1060141040700501c0d02c60850078609008012080001c0003000348068800181c00d03560340d04403100ca01002484698010300441c43e00c2c1d00c1140300c1d03107603101b00440030900c0c44010038507003030210b0107407410313258403003c0b081ca4844000d040c440d040158542000032940c1d05c81c003260740075920b4040e2501c01d8140c217811507625450b0880003012110b03010301d081801c50304e6204000060360b4500746281200d0241020808660807503000919072080c50080c0380340f071440e0400c10304c030400c019006000044210380c00e8480c3c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 179711258 1250 179710008 179710019
    0x201110105070e0609120d02010b0108010b03100e071e0302090f04061d0c120a1d1b10030e010e1e0708060f100509090604050601060315120f02090a0e07 67
    0x99820a40e42103020900110034000f103030515074090300e403160000301060400700318521420300302950300e800040144d46481040c0c0b0196000f51600f070041852000c420300d50725001b02e000c200400d050107803000c0f0151003404a018644a14900bca10021800c1c1c00c0782c248964500142c025840b070301885000d114126107a4085217001c1c0b0680b01182c05c081d02480d04014440e500c402e8405c0e00500c0f00300400e20501200c0d90320480c19400314400d0440345c1c030000795440c0014008201401d0050a41507591103481050002c25881c950007128140a440e40b8000740c91540341030b00500000e5800c580c85618190300d1405440c400035000c01005024850b0019642c2120358103911081c150145518039842900030807505160105c0c2207502c000008104c1c4a2591284000380301a502a1102080795100106101c2406801e10106d80100100e0400b0800c00c42680c07008070b01005503116507d180c10b0504648030074000007101e000c40503a40105240d00a140091103440103010303030300000905118542c80401d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 179712508 1250 179711258 179711261
    0x902040303090911040b2106150901030921021006050105280e0603040506043005030408040905100303020c060a1b02040e0d0f03180308071409090109020702011101 72
    0x40e2034140d03032001e14041c00c000400d40a00001220803054090402000503a80a00000f03028411006800500c00c404000564041a40050b011511800c6880e0549800101160844054200a08011950010710700380005101c2c4004900c418105101c4007400d6420750201e0f41000e500e40d1804d00b0400103448900456950280b02c1c0d015411341c00180003100c104c4030200c684000c020481c078113140c142c806000880c403290015103040360958001400c0c4820085004410946030b402c080b81c800000c48004201e100ea0340d5480314220a11038008081010b212000301164003400ca5000b0521081c207000c0400601a907c0e48400d1740140510b000b54110f80c81d0100c2142c0c1d0079062565041c0f0410003508581e4001104044100d038070650f074a0123585140414407451501440d2500c902ca100f602e005000b07030903100078005140e100c140350101b4100080d0401a2142c0201007803030088020800c42c28003048901c11a120300340d0000080000145119440d002441018400c1e694890411220200d150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 179713758 1250 179712508 179712517
    0x5090f01080703080d150608070807081b090301090606030b0702100c02030306100c050a0506070e0f03030406080403050d1515030203270106050402130e0c0c101505031501030c0902 79
    0x1240d000750808101288a5130082d251a015400c0f000422501c455522203450ba040d5008001260f00e1800704180d481d004411564050040c0c1404582490100c145400c032040f440d100005051000c24459503688003540710410403640072904000680d200e051400c0d5250007110342c0d10040c800c1c3e080001100e240b6002c2c1080203580d84c0c0013141140c80780c10400c0101114040c124007017004619070340000c41d2081201038013550080019029500304503000800e0395801c0220240120418072000449490000841e01110300c5450711a050382c88510301168240710b05c03d041c081c0715081c0200d0440d40c851200c400c1086409002d1129621400c106d0250140d0004503401c5403140d100102202800100440e640c507106218000050102d03210700018080380c2000c4c0024900e00c06a880078010000c803403801d642c00c008042e4003203080200010045a80c0c0d0000d00010303208a807203c0c00780e02101d4600905901800d402000d403001003624404200400340309110640300754403c80c100090100442c4200c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 179715008 1250 179713758 179713769
    0x607021603020d0f050a0b061f0c0b0c0412050102091009080d081f06020604020310062106020f0703020303060103062103051b010903090815011202040b0103060b0c0705090f01 77
    0x644003500c0d5400300112420049000d0300c0c03580d800f20441d00051018010382000d207200b08150102402e00d0000d2040440310121071031504403078091901c12042d0014504040c00760b20009290150b61106000041800307640c3c08455002006070b2040100003064014040000c4142c5845203400398400c000c81d010b0800344201002c45e0082a075407240c2d24031030b8204950003025003100c0400741d545215100001403040e400440160420020311007140f80900140000e03011a407800d020803400c0c071400d001d44c00d40181064114952108251040140d141c041c0e4440700300b0208003a0b00c072041424041e4480d441290480e000a28160780402c40ba00c1800d0810050f01114403640c450a441d030741c081d01c290b030042c03251109400351900d030440c50308000d0140c03440e058860342d101c0d03c001d031800e81c44904d0000740c040c031010902503140c0180140d15030741d0a80c040f001d030100d40c0416502404401a401000f0781d401c903556480c400207100c0c0e8101c00000c0e95008607a030a8030f880f00035988040000c42008401c1c001c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 179716258 1250 179715008 179715043
    0x130206030103060e1501081b0301050f1303030e060c030711152811120106030c120b0d02130515012303071103070b0412110a0204050c040504180203060702 68
    0x10b001203802603020b02a6400f1081c211640c0342e040344102d044a41e400da2010106600c0401d000d641d00158a45407000d40400f41d00910807420400d6113600c0181f0001d00241c000740f0b09480b0790341030620a4014948114200f4140e690500340070252406691003102c144000c0703503541100001002c0001481040d141c3c00701042c003415102c4001072400c0d005005030009a0002c0000841541c0b0750342e11582c0e00f400c0b80e40d001507540380c1c4594070040b12280144d000609041c501185640d10321380040050b80c400401e41c10002e202c10701d000004041620004000e03411000c02d8006004e42c040f5540110b01441120043c1c0c2c06a81114004468485441d485500c0620441034134002485480002d5031300898281400705400320740740c0e041071440c0c101540669810640c6003c2c04144802c00903078903a440d90510b0030a8200c0781b000d110aa9440100000a01503a91040040c0c0f00e14601e809540140000030400d00440e0014a800801c0b188942801c1c0d10034007640c00816101400007910308101b5000024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 179717508 1250 179716258 179716261
    0x106090e01080c0d030f0e0909010b0f01080f07050306010c06140a0f2d0917090406120302031c0b12100e0705011b050a1a1e1b031003022713020603 65
    0x401b1a11499501d014205115618240706401c2e522140c443e440342e800d070b000000c2c421080c4001c01072568000000141440401c0040c42846e2030094a0554403600c10b062507a039035211b04004071440d1000041c060f0085103062800911545042c0742d1a0103660150001c0c05422234440454048032856000c10f501c480c0900d407414a00c1c1c0034034081480c01500007400060700340080d112617418411480e003000200c03000141d4028140381600c5080081c0072800c1840c0d80d4260541da01039586d2144101110789180c011315a11561710498205581085000c0e0803581201c404000c032690b81c80b001c4003071209450a0500c1c0f08101a00010000210fd0050391009082c001801d81e00040c1200d841060b24140900e10052020402d250300c03503404058130142c1a0302e64541784064184070301030303034800c0c0304056a9041886046e2650100101e080d06000092950340c1d2034010b40d00c216254075500081d00540c1da9400e050103000421010b501a1900400700390392070b03451402100c100d102241000354024410f10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 179718758 1250 179717508 179717513
    0x504061b05120a0203041a120601030209030c030d020f070801050c1903060b040308040312020601060f110705030613050d03050c040612020d06170d14040e0c120106090e01080c0d 78
    0x41040081d000e80700b650241040b8904018055000e40c40000269000090402202d00d48a40c4901700d0485170044600307248422004030b0301d240001c0c0c0254109078000c035000d400c60360140501042000000c00310b5040819900c0c001c4e4458040c01c0900106000e4003400142741e0741e041c00b501744108501e11201c0e181c10b00003004054101026090340040554485011a100c048003000784060340c0a410172a0700c483ca549000040002c95503030703400c01c40d006400108001c075044520080700c000701d401c1c2201501000e100b00791804245500c515410720507042840f0352055840074103200d031800748003682c004100000040e01543d0080d00c034030501420411040000e81d1040f80d00c501c03213812a910240c540300c62101000181c0e0129000079102001c1b0100d868800b4008000b0120b03000b015090490f1408855023909a00f405035220701e582511524001881040a250440307a21002c4000b07861403550310790000409101081c000c1d030790403950031000400d82050015003543c110100420890b030b05002507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 179720008 1250 179718758 179718797
    0x1090e01050f070c0305071e021302070209010b0903010915020d0b180a0f020408010c021c02071a0703140d0204030506100b0304030e0f0324070e0a030b090a06051510050406 76
    0x1000c2d02002130071f00c0004006040301d035000e03585907000000044804010700403c40021140300450341150b1042090800684039010094110b81007104410789812104010902401612200825000c001c1140454504640d8080c0034045280c071001c10180d058001446401c10022054648561107500000d002c2011a00f003c6103242c503002c005420700c0c1d03641d0b9240d0f00f51007000e9a00c0c809604511044081c88040c90352400c02c0354028030082080d246440344043c0c01d83d101400130211204002068018140100301c800e82079522600d0380c60744e0b41c00800c114002500070340802c030b90030f02500b00800c4880d502003804205450302d109403280742d901d035907505075003040599084a42102c0c0c1003034102d011703640910000b80040700621824401845003032900704007060040c135520500520300010b40064848640c45403e60b58092480e400030340711030040d01c1c508818404000c151074200400c0200000121aa800455805541c912518000e182081d150740c000d6000f0000000c450803400260200070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 179721258 1250 179720008 179720027
    0x408040902120a060801060f0306020c07030b092b050703030b040e030a050c0601060905090a051015020102041806060e01082823040b16050d09050d12020708030a1d0a03020601090e01050f07 83
    0x141811110dc80d030345c0e965a03010898003142c40240503000014010044200c83e4504503000104141c1c03100321710f0303c420001d403d034028488003508155541302418240d48441d885580b882c10950201e9894045503a8004c0450344034096800c804c3c018140001075450203940180c044d140000c1a42c0301c96a13550941900420b07001340840c5403d0204440001e21a035036590002c0b55180c0d9a001503a11424101c141c9404001800502d0f007482c0f920318100b004940c4034401e841408400d00c2d008030247ca804200c2101c0000300d00d620501034445a00200c5801540e03440540c2054580864030b031184521001e50036a240102e801500350780701040020728803041414090700c4400c040c14607a0511441c2c20700358003102c0211404560756442820f0f81130055422442d01618070069040075480c120141d55900d0050001030f1030040955140c480c034001d80140401c1c100b8450711a1011610610300c5400c000b5603d8801380700b101e1403a84ac141c02c1c22401034040c065a44540c04441d0b0099032900c031a81c04940c940c2d039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 179722508 1250 179721258 179721277
    0xe0a030e040b040507030209041505030d111e1c08071403180f03030901050105100903030e04020c0109120e120c0d081201030c03050d080405150408040902120a060801060f030602 78
    0x5a41881c4403450392184502c4d13000381c59950b00181c42e108118180011143c12507880141141145801c0010366000184008169890324052801e1005402d40c5031400381c0780289010000709900840c60042e400050445000c100c41400b13000e640c140e81d40030b80320341c201560551b001401f5042440ca22854441c002d5421913085e00d500d03800d4240b0201c109081c0b00e000740308088241c0000040c850142001d0140b81d016003001c860500c030f00500c41e000a00100c1240c0700040a118541030b54494035a01c1d50306482211003c58004d2082c00b000d4a417803d240c0301070540150216064202ca44443c6c18116001d01460b60f0501c02803d02035802010040d00d0f050224040341c040c0c4c000c01c01d87e101180c03050355250082d403050041c540c0345400d51a090303050001040d001000c0000c03010402020490010b0b0f030707400709003030400c68202c682c0380d03030512201603c100c2c0c121013003050001562a034051302c3c0b40c604910510608078200b00a0f51607100382800e8400d00d1007604245242c2100a0003c940035074000c01c10070f407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 179723758 1250 179722508 179722511
    0x306010f050d060b04030506060315070c020d02090a050a0c0504050f0d060b0604080d0806060306100e030a05030f1e0408070315180c030312061a1b07080105040c08010e0a030e04 78
    0x81c009285800c0c3c4071a50482c000b1280d02103410003c0140c2002500d400200842c00381010407013600a03003508610040840c0100500b01c5822070a64072412031405595401500288603450700d005110040d000690751528558608a92800440c0c0b2030030580f4141e606c01421400d50000b840100018109811710903a4120b5071108000c50341c1d03035080c0040c0b0007441420081c1c90480036040c4c01400d85c2c040100010b005100c1042042025682d40259024085082c01c085031590690301c0400d11784108141700418610000540e980c000d85d021001e4030000da41007410701d014900d4021036400c00e00461242c0307109030307000440500c0001c40141c6400d035410508000010320960b0f02496003813021145400f901d41c4d0f03c82410034001c3c10743c8627041c0d200080300c5e03050a1081d03524103000c22086121989851008070008205071034049240070b42d4003003007010351048900041d2226000c0e8000d200a40e8101c4510302d000d6400500c010040c041d0244d40b20300c13180640511449520700303aa0a6850281655016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 179725008 1250 179723758 179723767
    0x30312090c0905010f030b0106030b090f0c0d090308090c1906031e110d0506090405060c0c0a060e010e0610080606010c02040e03030721092f100c0501060b040b0306010f05 75
    0x4442d03440350038002c104d8071780c014212618608124074802c4060700440105401c0c2103011002e52606000c85400822001d03e08540d9540c90640d01da20740036452043c200c0a0410001d503051543c811045405840d400c002d0700c1e0a980301504000c1c0e0101c00d44d2034141d1008840303c08003c01400b0f41d00c05014030102044042061441c5001e03001141d6400d540413240d004e010460180d860301c5171140940c03182041e03807190140d0415440e6507a440f0b5005000242d480000034000340c0c1260240446079407513034048000e2207096a405000344c0a4003400704081d00b40d1161200251160100c600d034102215082d0020b0001500e500004640904400c9401e0303800948500d1102c0c1011001c000a51040c145542c036400603501d0701d084403100c08203c140001d0440d0034140d00b00c003c070b06010608403c2c8020ba10703400f00f060392083d4092090340340c1c071603c41e54000b01c0d034445c01d450f441d0050a1115810302c0703040200b020300e485007083c00207405117014a43c2c826200340001842c650040c08110001c0b100303800c6c41400d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 179726258 1250 179725008 179725019
    0x80d140a0216090c030c030903020a0b07051608091c030c14150f090c060405010e0f19060914090403080c070f0c060903030210020a080f04111005070516030312090c 72
    0x20994950100b5031460b41e6450041c0800e034988240d1b8041041440d040c052460103442c000d54401240c0340140131303009043d01142010f80140c04580c1940c01810030341503103c050b424021f4050704100740e02c82c00344a00154400241d540b50f510020300c80e515440c0c07074001030a40d4170b82d00b0103040c08040400c160700c90030300315036161011444168410f51541c8003100181c50440c0d0358a0822007441e0b1108d010700c409009c1408240c0c4c000c880781ca81400142c0f8515510b28a81d000202c046100711880c0700e98000d44000402c01c1c1d80e0001000c001c0d03a00c4099030200c0301c00d40380d05015400384100c4028001a07802d002240c2d006c1203003802003a1050045140034021000d940740c180803203000307a00078404104461320030410580c05004d01000008000002c50401441c6440644200341c0141040140d000c6040000d040202c01c0040701c03c0440060071691402c040000c3c0500b05034459401502c5911401841e0401440004908001c0d030741d040d99071010040368041180081d00407035104036275111030b40343d02165 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 179727508 1250 179726258 179726293
    0x13210b06030a0321020c0a121d01050a11070b1617070f060f0b030105010f0f09050103080405010f050c0303010b030a1a010c02150c06040b0a0507090807050607030c0204020a18080d140a02 82
    0x2600d80c0123400c2c4090061880d44050400e466415140e10103481c00140f0094071381c0c1210a403101c2c508641450910b50104208082c01d2851540203040c4441c0c0c0132400c1c00a0740681e09102d4070003442420442c071902c070050f8041d250350081c42c00040c9048001c4040b80001410340e0406c55100c12004000301d404003c040029003920701c00d800241e50005065070400c11103103100d07a03d10050000c07017400c00c21941140c0b11060903124a01a05052003100300c13404218610034401c80d41c034080e10702c064079125616001100c0c1140d00c141c40c140c03481410120420f54500f01040c502c500350f20b05031105140c9580079424001c11203a0759551030307185c0b20203125000e500c08040c04a244500d110303582100341ea14195007420308541300602651300300000c0c01010f1240500c0092608240c0b44110342c16604c0f84800c1c40c0071500d219003000300a401a0020400c516a160884207036001c0703007481f681d0b0802146e00c9040c016521080c0e2000351000508085004000302003507030051294002900c140c62061948059015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 179728758 1250 179727508 179727523
    0x12031b12020c0d05150408070803010902120a0e2d07030501020405270408130b041e050402090105040902030c040902210714040b13210b06030a0321020c 67
    0x2a00c04220008680c015981031107408440c4000b1030b001000c0c41110348036255102086088460031800407000301e001d0001038800d440c00140c0c0884080d0b0f680d030315012000040c0d000380088410f5030101c0d5001c140048003500034818440b40c00e40003401600c44212401484007a4800c111103038a040400314400e94900344000805140180005641c4500d4038080c041207040080c109454a68101c080030f00a8040140c0150010f82080c01c8030b440d144d40702c8529100c0c0b2000c0e804010000000100010065001300d4034140e44250801c815000c9960303641400107a11800b41468001030040000b444203d400e40e0186d50001511022603080c640c442d00c691080341e006a004c0001070f041d54802400c003110b0404405d600683c186800708400c4641e1a070b00003540920b014850b844600400d0304203001d07000f40a010b00415044040e0251520003824101360224590300c00c2d02c0c060307220030000340c49040010700f030007070107030b1680c0c4402c0184059100c5800c005100d4008016203a002c102c200303442c0c0402c20240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 179730008 1250 179728758 179728763
    0x11101060b04031502030c0f03090c0603040c0512120306100507150203040c080d05040501050702010318080307020f03161e0b0a050a0f0504020d03030e1e060702160b0412031b 77
    0x700d90311400d5003000420034208544011840380100100103000f080902030701c40c8200341d41500313922519007222a500f00401381c03603156003001c804400c100a02006001c440c045030001e85240304464160300000c0c3d100c1ca2203444184000104101082c00c07800e00d45402400b0400900d0305c1c1c1c2c1403044554405142c0076a10065000b801c0d000300034171007840045031101e0700a00a617801081c01a45010300078085001340d00c100c41c18403c001c2104015a406500082200d00c501c001d1241462450300d084052604151102c000512034181aa500f039180081221074000d410341d180e4081126560b2421070051298080d074041807010300b44200000d2a0000c403c0c000c50b0b1148021465260111001c000c0300c1d2400d507040794850404040c040981c46116070800310310381611300407604100041c1d8a85c90444805024245a0141403007142d02c6034000c10040e00400d019402d94800950031a98440240091b004907400d10b00101301c204400742c50300300d1070713042c13207209080c0002180851407101950340201c8005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 179731258 1250 179730008 179730029
    0x6030a0501091a06330d150317040807261207020f01050414090405070b21100f09090516120303050601090b1206030304030b07020a05010605180c0901110106 69
    0x10f0105035840340e1001e58401d009980e0003c4a403c1d01d42c0c1c280d21090040c20101e03400010700c02c1135480c800c081d022074220109118050040312400000c4000b006d40520003070b00e2403107107180c5035040701c3d0686007180c04440d9001e005098590418180c51031351780054942a04045040d03984101351002840001d811040c1908800d4540641d80184108182c92882641c10000108014040108601c446400c0140c055034007410b2680c6a10306546448001c0e000f24407100004600100142425148090000340b0742111454580307450b00488044001c0e40280380c501d050b109024171048546030b1100310480d005104480d034801c900100302507070b160150400b8210303d0000c00007105154044c0122504041c0c28039200c1142840c00b16040101d02500c0310f20b1102c0d07070000c000724070547d404109640141d80c001c036159013241408400655101c0d003039201101c0d20350070002c000499140001d2481c920301c8102d401d0240595444c14041002c0d44409003ca050201d02400340a04210034800c20000e080760501c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 179732508 1250 179731258 179731283
    0x4021914071209080607020d120c0c0b0901020a0e04050103170f091009060225050f010c0503030106050301030b091506040c020f0a050106090f0b06160201051c02030f01090203040b04030806030a050109 88
    0x1902d070304105c0c006003490103560040e80c050301d125034070401010b00042020000a04001c21303e1040340c10183c030342030160000c0d42d51001d00580c500198000c1c1862005900c1e039601540c0c03a013085c407082d64400d110182442407121744034803440d003a40c03006040311040c6154252030541000005101d03081c9a50064002440c02101405421380400c290310320b40200420320841000b0403810300944030000e009040c050a100220020035034020344202440680c814140c90f100d68440400030540e410911080da075591080c00858002040030810800607481d046050302169141d0381400f020302509560541144180c005050701c4401c18000b04c0781c000c1c4601d002194144ca040c400790191680c540e040004940f0b00114000c01d07586030f4013143d05a00090540d00e00319440d900069409014001000501600560f01040b0031103084e801988551075400e50041036907298602c1408034002104c1c02022508032001240129000c0c02d00c1e10350040c0c005003215507448465462509494010208507020501c401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 179733758 1250 179732508 179732519
    0x309030b070c0c0b09030a050303011502070617040611040e07030507021c020c04090525050913020f040525020a0c06020d02060109020c01020d020408061504021914071209 75
    0x409550054102d00c0c00d1540e44410391103003803540d8030b03500c500d0440800001724102a0380742841f0a0a400e6003001c03d1b240c030b03584d5070541c0c03209142182a40d00c0060003100c0c008aa11400740c01382c2d030511613480360010120341e41d50fa1024010540100e042c041c000c2c06000004110111000e2302e48925411707034020a150500d44c0000c0d03d00310903615886000d12a40112900701c41d40000d1410101004403004200c02c41d1038100705080259040e10380d81491042c40640c0891245540b1007001c5620550301070310655035011804c450f10703d2424000303510078082080d0f00c4c0107180c00e80109400c0403003030f180c0c200244608404445400c01d69641c0c0030160b00030f2050318090140d603401ca407008020130b0000e09018104000025100c09c4140544a40c05c1c2e40440e181c04060000d6050380c03808601410b085503240e44445a0a98400d01155244480c42c002103145020782482d0080d21180c695814000360300c480f5440040c1c0f041024018415000d01051045802007004401803165180454072070307048850501703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 179735008 1250 179733758 179733773
    0x80a02210c0a0b04140f0d080108011a24040609090608010908091201061a03091b0310180c091401091b0f0e0907020304081e030409051012030903 64
    0x944160602610038044054001d40101d41c0045280e480001d8504a41c0c1e545010f000740000100c0d4907415120703550010030b0b520000102a10303104420340342c1c1c07130080c0e988121040c2600c02e03040d1304800314142c811034000141803030103000302c915107000c2c1a8100c80e281281c00b9401604141c0c081000104000c8080001d82e5051050f24045c080c0d6000900079000705455020440c413918121902400e502c0383ca011b4141e50a50044000d014015401400f00c99002c140003410f4100b542c2014407030003107840381c20100c0400c84000da00c18034017501806420b003038107048c40d00800c5031803c00c002070140d00d20100c0018800100030409010102c200096240c094071075502c85800507005000c60a00c0d203924140b6441000c4d224900240c0d103443c00f100445501780307040380e118003a2034001e60003070004d01c14820f1094000c030291066a0f000802ca45100600100d080c00055a1041448985d0003c2100344030880341030f0805131b403001889424898407959080c04582802000c24260001600c0000c00d100300002d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 179736258 1250 179735008 179735053
    0x5070302034b1b12040605070c0509040302070b03150d050d080912041e12050a060c090509010b0d02040812030907051f030b0411120105090705070b070804020d080a02 73
    0x10701100b40340c205814031010381c482c031812409000680544024069041e401c120313110410041000d46500d0380d944a00103003850b040300504403908680f2440100c2e03241001c05481b482550541e0041c0411440c0205040080e403018204180d01c1030640b1400c500c0744ca8248041140707912400081100c21410040100340c3c9802500b4008960401c0d00d00149040d07241c0140c0b0103a603030000c0801001c43c44600c001d1070502aa0f8089108180c40d028901c062040c00f00d07110303d038107000b01d409000213072404008603010219405416071051a69005010304e04055001d8208609010304c0146026200d1004502d0482c14550445580c0000410801c2d2031006006050003003800f601d0050100c0c07160b964130049810000f103403c0404d0f9403844c4580d000c1e595034100e07031f4403403841400c4241e4034030810303512030703401002409a18000d0b2640404034103000e10030001c480110350005049003040d141c136442102c2050025105aa21203031090003180400c0240000340001e804540042c10118850b41051705080c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 179737508 1250 179736258 179736367
    0x1d010605030c0307180e07030203150105160807020307030203031603031b050703081f15031a01090e0709030602130806150a0603150902120402180103120507030203 72
    0x24010b00c581c440b072100541c1e4000c0d01c50b0620420101c04191a10b0750803846601c115031010600007444691505503000b980100d03500346a0040d0201203a00566682c4601560111500900b07403002010a54200240c58000c0c4020700741c81c815696500000d1075500300950315200006210b008004043d01841f607461030074800403e400d15000c941d903004d40740740621007018040c404505c00068209031010b001c05044800440401c01e195200c44281520001040c4032a000c20f1a040b91411001c0d61f4040b94614010141d4507105041e0400c002001c0540e800342508041c03003a400d40200c002a450b0020704009440e00550050715460f10004c2c0e483c2ca9000b524503202501c860b20b0340840ba07280d034001503080d0f402e18140481c2e000c030004d01c040f41405040c2e0262210602c045405140c0324028240725025500071214903040380e04880c41300244007001e100051030f2802a0880e202c4e81401007018140300c1d802401070340d091181c5001e203807080c140d00000ea00310f41c0f1481d41ca0340143d4104181c9c1d0038000304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 179738758 1250 179737508 179737517
    0x220b0327060f1f050105090d1406010906050a06030b090c0901110105090a020f010c021815041d0106051509010804080705010914070602011a190503150403080c0a020a02040f151d0106 80
    0x614240020305641f05404040303000e40c2c82c0780e1514042c8119a100d04500881c0081141c40940c0c0d900407010060505020300d62088030f002c1c1c1c000464500c2070280d0190034000601020040d2510100c80065900491009050010070b42c01a001400280302e042e2261000401506841e10346104004508400c4501c090601030080c10040268454201041c0070031698180d040d000d0f1030b0019440040701070b408045074418200044852401d40ca00c4408244100d640002c0c40015100e00411541e0014511005901d40040c0000c0410398031420f00940c000c2d00070b079809403920065403142801d59807007040964080b8004110305001074420800007004014600c02080f029030441c0c500c111080091503501d1141b42950151030000140f07040c0003005043c010100c41500c0100809440502001c82d419000728000c84d00091002910404603480b220351a03025003006842a420040104003c15070041b0240e42c42141280482411210300041d103004a0703000c01c10140b45811921044050300501d0412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 179740008 1250 179738758 179738821
    0x50304050106170a110f03070303090305010e0a022b0c0e0f16120902060412050d02010e010207120302161712060a05010807111c05220b0327060f 64
    0xd0004c22035008460b480a050304100410300d0000e243c442071101e2030396140c081c41c40b001080541002c2400100c0744a440203101055030340c108262210030000010303410179a00c1a540e604400d01c0300065901d4610320110008154054032591414101600520b5440204806000c0e0071441c04803281d502010644156a07048020500103040082d240601c002d5180c032462420119603c10050320090b01d40003000a0039240182406596250f0494464015500c0c001000124000600845004941101d902d21944a020400b10000c1d805202104400900b20f540c08000560020180354003030380a403002070300d1707525a02c514248032a0150181e44940809541048140d0b001442e25921811034140513a9924508030102c2c1014030540d580d0103140b00300318403250100d8011001c0c0216070808840310003075400d0080b020917010007602a1480c00d140070301c00200c226554003403185214201441000b42c5416441607a840d00b602603503012199001e010401c6102d03001c0302c4c01c00465032601004040131 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 179741258 1250 179740008 179740049
    0x409140105011b020301110a0302130e0402030303040b06010201020d090309090c09031a06010c1415060301050f010923010e0406140708070e1c150608010605030304090e0f06010303050304050106 85
    0x511000d00c8401e42c1481e50a50f16405541c0c0a511407070418042694803640d5180c1100000c00a50121800c004068881080890034540e6a106103204550280003180b4580b2141c6a020310107100a1a89046640820000700e280846000b0340041511a495000d501800c0c0807504040c0d40c0000224010004c50381c20400109800020b201580521064410b445071946030040300c00341490800505069110030301c506403c41c00155056008221038100903940d10385008150a940c0300340d81d1100c000c041040140906041940024603504000c0071030341e076101c869100843d800a00368005450140d0310403c1101340328060113654840c1d5008600801c1c503292103080500b5149000e13014004202100c8020001510b94006042141844080b06001c140991419100022290348400b103803d060140c002a07201d41401600141d03403009006d141818148001c1c003004203c10600d00b01c0701c0c458002d090381d2000b800d101040c040d501940d00d4030303501e1519003455402d4400360f60103c001c404808010492 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 179742508 1250 179741258 179741267
    0x20708160302090601050403020603010807030506070f0e22110301080d0903080403030e0d0209040f0515100b0306130c080106020d0206070e04021b03040b0a020606150304080d020c01050c040914010501 88
    0x641c0c0c0e049418500c2500d50b003004880c1401680c000035006a000800441d09110010f82107085901c110300315901582e5100080756405080c2c10340c540400c1900c2310311490b03171401503514030f10781003241c25112520390034000d500103944c0369038043c003108000080103200c003034811311005420517910f0508071419407455035195a144108e10001d01040050b6013103100603030301e50001500e4160002e0131041c5504143c241002c00340032000b0b0845042c810308941c002000030400419110700102c90404012903d05001030805620040c8013581c421000540c040007119544100d441300d0100c0c0c0d803421075640c10b00401038030304540b0000e04401d41d131140d4100070056501c5a003d210540b4207a801584484080e6191302070b001d2190b800c0d0901d40800f05002c50900c962501811881700160300b1645a40c5919080c440c810303440c2c1c100003210311401c000083c0030915030001040c0780195075400501c1e00c00740315030407801c5030015540e0540000c40000d040042003214055042281b0220700003200d65454100042c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 179743758 1250 179742508 179742553
    0x30305100602250504020f040e06010c02030d0e1801080a02240301051c0213020901090e0c03041b21230d110c06040f03020a080d05071e050f0d020708 66
    0x80b0f0106518801c851001d0003040050014180035006548401840142180300e4015020b543d015203020310005029601c5040d9481643e078001d00a030a001d841403008940c10350010700c025821010a1079800302c51036521801c58000c003000350203003210310010f104000d49481d410b0091200c0e00400707007a682d043c40c0c0b0304080300d044450488408410788140d8000b044c003901c0e0000c0203903115607181600042821650002c1083c0a4241e030741060140c2c0b00ca03d0380b01d40c0d5a0644440c0340c8610306000242c0000d0507000f4800d1000c0b106900000681da035122002d03403040b08110303250305015480842c038040118881c0c0c0256400021030490030498881e0000c5170351150038000c62020002c104082e1303a4400c3e01400f03441c003000383c0074104c0d90395562180d2888a11055a10080740280c1005c50000303601d520110310700080042603a02c00385042829111030390b040025810300015602c0704420480020b100700104180c1c0c008820141078811202c01d00072781001c1d0382d0b81c0400455081303030149058601c03100c1d042c407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 179745008 1250 179743758 179743783
    0xf060c0d0e130e060105090105100210021803030c011e0207050615132a030203060306010e10050d0317010e091f180c141008040209061201020f07030305100602 70
    0x9407001c0400c8030000303056680d070400640010349800c540525016001c654030341070700d500383c8169000380d07a15420b004141011600300c500680001c943c0c00c00c2c00190340c0003004502000c1c405040300741450710010341184e000054101142c4c0d503546410030043d8041f07003c506d070b00b10410401c504001c1581c60300c40c0c03545402080710745542401c011880b003507a9103240f028014a1151410007003000000320700c81402c01403600a17641900e11480e030340030302e03482402100c1c82100061301038407070f503460202800e01d1100e015004c8141c0e060501c00206039510f5800380142d42c0c5000381d89840540b00107441040f030180040c0c2100b0611000541004625100010b0084c4000180a50601161854100b2400400d580403010b0003041c1004401810701c01d04024040c207644206404100e100c200908120400c0004160701010407403a50015002d40b0b000c4841607408000541005102251140c0e200c2c00ca03407220402840030745011401340f09040d81440780c03640c00300041d944035807002c0c10114042d54070610000b08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 179746258 1250 179745008 179745017
    0x6031a06010201140a0b130903050a0809070b160b0a050702120901180e010503060a02091c150623090c0904020304030c17030a1b090603020c0c06070c03020f060c0d 72
    0x305610340d1003544581021650364403010010706062001001401c68040704510881503d0070036000780300d6511401240300d40c1921020301d401d080c044241c5009100900403042405002000200401001e0040803450640651103a5101c44d03454039140f204ea000e0609410645010100054150001640c0f41201080305902c1e44644000340100c84000f010b0301a03002c0d110302030368001161015110054140d800071415a03c0c0c95035242d000b04120f0140e400100d911010b4a24112005c601300c16202d054140241d2420f1840c548858285058030003c1d800994400c001c081d9541c4030705d03903482049900a40c102d40d04c044505000340900d800d8004d4a04242c812503000001c0b40c1054001c2c1488422583d100a0000641d91014103410341600100c5407240000d091207009082c400716040790300e4840c0890b844006285003451822402500212092141d6100314181e82c651540c40c140541906881030f00001f01e01d03800d510500154880200c45980198801c0c07200845005010880312240030003440c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 179747508 1250 179746258 179746261
    0x31109030d050d02090307090c02060702062a0c060709051c0f0803060f0d03021006050f0d0312020d0f060302040605012a0305070b0f070e0609060a0e030705040e06100906031a 77
    0xc0780e034028419800e85c0c07685485151000074002030990071a03503078402d5580944844d50340e050030030780e10360000702e48040b11034100040800c0900401d00042a8049865070207070b00344070040c101c2500e0520180c0d0f0a10105200c4a82040f081c50041c9010000803145007200b41c00c210256181801961202030040941d0404030024245840b0110600700b070f224010f210010000190034082e40b03541d2024028a4000d003003030000b140d1380c10a14020b88500c1c40103442866840c0c02a24100c41d80214040d10700d440c181c0130007020704402c0c940d0080d00c001205105c0700040151941c030400c0100c40310b5070710550520525003d04840e0035980d030794180d440c1101150b10307003101d1994175040320306106010000b0640d81451062001c86054046504d10490705925520440880030041002501404420aa101004010201705184219003042c55408040c04482c40551510300240c141d54100303c42d001e05500c0242002075482d03500c8490002040c0c1e02004106030b0381151116840b0b40e02c484c4041c42c19240650 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 179748758 1250 179747508 179747527
    0x140f0301060b042607150305060a06080406021605060c0d060806010e07110f1501030501290112110307170c03040c050105030402010c0606090b0a080309030304060309080f030a060501031109030d05 86
    0x84018526542c410281e4480c203840e2484100301b840300154150002c1d04d8100015407606181d20780704261180b50319203e009a0740d540c2c40c070340a540021050510000c02107448000a0410003006008101e49800c003a11032a088004400702c0c1c3c4950302250403507010000401051045041560300400c1920342461f02e50803001400d8035108075401000420301c9040000218001403018030f9050701c2c8544000c1c4103800f000c840c28a1140043c18131240e50302d105000846066010f00140d80c8050316108000c140701800030f05034950ba410484031140030861100440b108072080030b107141d505c504000311071030450405840b1100480e406010b584d0501ca000804502075a02504c41c0c0e03000d05a125600b0f0101e691209040c0c00035041040205000c3d116081c0e000c40c5011020040c2c5441080140c02907082ca13246c007500f1005801e204100340c4070088200300074003900d4a00e0300107520444402c000890424a058001022103601c074112608414041c000106035540104202d0a0402649007180d154803149 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 179750008 1250 179748758 179748809
    0xc1906081f0801021902010b0f1c0c0305060f0f010311010c0303140709080c010504032006090612010618060f1206080307060b0306010b04050901030b04030513140f0301060b04 77
    0x340524001c03264914000a41500150000c000350701407102c000400b111822410b9007030b1703001c00c1d100380d501c081d96800303403e144c0c200403010800300c54079444c0a1500038910740b02d8504402e900c0e00f041c2e07115000300c0f0401000748021648180c10100e2844103d02c02d62658484d611000d10f151281c03810881802903641c241032181d00308010074072428078907440609207040041c20803500c904c03070f2400c176005102d000e200640c082c10949040f03d0704214803507902940483c9021154980b00c0d2030030313030021060100002688030b59010f070007440d03203113a200d4140d5414000c0240c0182000c00d06208082d00200d824081c1e03c0e4884980c2c540d09410f410b00300b414080d080c4162020f00055008120f03d4440480c6190a1241540100c414500190b0030748602d662211854005480341d8024940c10410001c01000011302819120380d22078028500b550600911040e145620030041c0d2240004072030000c20280c080c0303000044140b41503000c034001c0000030700e016000d001c14041c62081c00e00032148d0701c0700c02c441c0394900e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 179751258 1250 179750008 179750041
    0x806030c0a0e0609010602010e120c01150308040906050a03080904090203010b06030709031e030f050c03120c0a0e030c0a050d030207090e031216020606040203280c020c190608 77
    0x70010410a51280b9680440c480110b82151040380094000650107006204103054412000b000d0700d441d1012000f20714040e80016003071681507580c0d8120426a034080418400550300c1000343d0740e41c1e1403070180241c081d1000c50300308a105205e035880810000b0304a9007190006082600c0215280b01c90f40006401000c1d103070b6a10303030042000401c0090455012401340141e030f12440300c210841164103021016200d03c210024085040c03590041c0b17245000360040e00d50004558103c900c1c001d02c0c0410500e40c91001d80c0c02c8200024045042ca0005400c45160b940440d400d50003403c40480c5400000c00d4a011440b07070602800e03000c82d4640a0510a1111101410030350105008003407015050a50b01d40c0a2005c128400110801042000c4110382c3d0715290050a68010000c5885e9102004000c1d400a41a040c01403d00e00f02c10048200c03041021507403101d42c0e9000900c11b02d00e108040c2c00c1112000900c2d1180410303c0c070800301d1044504840041d103206203414015543c40d892400a085003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 179752508 1250 179751258 179751283
    0x19020d09110406080c0a09090c08030423031504080a090b1207110a0302100c20060106260a0504020102030733091101030506010201021b0a020406080c060a080603 71
    0x400c5040014010040306204914034240c804014141d0f90300001c83d100c0024465030360340105030b081c0800284d00250011500c01d40a002c0f0f038003c0c141e03249140740c0f465000303a00150308100c0b42495420428404074006020f0742d0150007170035445802400c004030b5800020070051050364003055031440d55206580d0b0b607018011803101203035182180e040003a5071000840704480003990310440310b01103440c0071491141e03c55042c0c008281c1c800004e5131038400341074208424001c100c5c07a20080801d680860742d85142c0c07884800e0107001c1650400d007005050784112050444114030204403000c0150307020f07030490391082c2071620008803920744d840102d045104007980035000c040a40302c61507082d1804181e1b02880220380c8010b075949402040400c0a413030034071101900310100c1a05201d0154002e802c00e40c1d111505100062521010a140305000f440800302001c0c0d69201c02d080b8070441c10140b0640000c2c256910050461b1142e0500191039441050040810030034004d01040c49074404018245040b003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 179753758 1250 179752508 179752511
    0x9050a1803180906090906051003030203070807061103071101050106050c1e030d1d0709051003031d060d0f05010b040e04030513120308070813050606060a140c0102090a150819020d 79
    0x540e81c078005c0c0003409480c02e00b5501145040082203481d1907180c0781c3c0c001ca07035041d0007840c18100161a8824030360800d18040c3c3d43c080e00da503041001500400300461084001e0340303234012140440c420301821644143c1112062010030041020741c550b002030310545040c4520140021141549511809d60045402c804185030900540f4802c0800e600014851541c480781158140c681d104000000d031070007500c083c024140e5010080c00407a101da01800c00036a414080c000381ca01d140d030086030042d070040450403544c540d030381d051402c004803030300900340100301580e4014200790400b43c036030001140c0600010240200041c0420007036a0807e5a00700416500da50038020105508015100601c01c441b010001511100000c3d034420421900e1729041d070304240180b1240d0344010a000141c2e0159200105001c0d550942882c0c030b01c0750714010000210800009a01c8120540510030546666000050a03103003a14050b007600e0f40c4641e250381c1c050452210600007102c4071103007200078880e8039801e86055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 179755008 1250 179753758 179753771
    0x60c010b03120f0d1a0904050d030c08040503031f0305070603060510180510030b0901120203150403140901030908030901090b0105060f070f030306170709050a18031809 74
    0x400065000500351401542507504030440104a50690b200d414407001043c9403d00000c40203c906601c00d0501c0d141d0711004421280d200c40001c3c404280480d030842c0c00740e1012841ca1401ca526014041d11715015041c20426410031303a5549450f40401014074500307131040d40800ca28954250414402035802c00c0582c1c504503290700c8000e018080f54000d0074021020080000015882181e4900780d14039526182c014080c280340812280300c1c40c440c448800c15444407051142680c03480555402030a01c688000d104601c244149418030303010355409204400b8010401000c40c2d00280094007400d601544140e9640300c420046e00102804040904070240101c104420004154031144a00c2d014000c04240c070781e0b0341c800300324141c4030301c00c0d04003034114017840700d0300014224030000d00c48507104c1d0070082002d035141c18540c10440c600041320582c0b40e2041c241044050a14071039203801c0340e100c0e501409103480002c00b210100803800001410060101441c000c01c1800c0e50621024100e828001e1000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 179756258 1250 179755008 179755027
    0x1050a060e0913030e060708180901030203100b0625050d030b10080705130303020c0103060f0501050d0b1201090c060e0409110d0510050c2809121a0414150c1b0c06 72
    0x12030300309162901a4101c9c4680d107044500d410100e1604995004000345411003820050710301034010500915000f41d0b080c08050309521220b50b440550010010103079100c501c050400c00d18194584003a5801e05107481024012910b60794a0340140480d5402c02c4486030300c0e660005c5800d441200d11007001d401241c0d1010003055400303d44000f003010241e80900032030b034684012400b9200284117490100308100446000d100711a0080d020b01d410081400c0903001c00c0d010302070b082d21442141141c000b1194101800900c1e0082001140c8900030303282084039402a0340c070412000b03060041d0341d104050310001e1204200081005854164480905004904010030320f0800d0341c010400815a05c2c011000071080c140c2210300310140d4181d40e07682d540da1300b8130b49108001e1541e00b00d4000e0b5041e4417200070202c1800c481c10003180c0614802d140764900103604080c01030610008a40780d500d108004401d10404812917416200203003021181d01c0c83c044655485185441c1c6244009500500f0108501c0c48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 179757508 1250 179756258 179756273
    0x5090d0c1208030108061f14120a0c061805030703110d020d05010501060905060f12060105070501060308030402130c0804140c03120c070f0e010b0a0306120b01050a060e0913030e0607 80
    0x100c83d45d0304105d484588400c41150b16102c50040309074241107145504120482a485402900b25005001d002d1710110311b504140c1099004c401c10344a01c0c0e03c8407420425694061078030060f8881a0114002c61410000060344600c460700c000341c204202c0b055000031994071140d000e112694002c0400c400144145022406400c09114590201d186005c00058a040c000c2c200c65030708151120091801d03480134841f01c110703d00900078604000050055a0000e0424850b1002460140285640341d00c2c062040040b9020740341565100681024026408250810006500103600c103141c00d001c4810007100c0f62030583d01108140d414810740108000303040307002c40105030f4900100c00b920000c0e500c4031400707200381101e4410001d010501d1001000848050800b500001c80c00e490b0100720250748400f040d41a441203c400d43c3c144201e040104001c0c81d04070440b80080005040c070280d1101e88100165231224014900184100c444005404043c4224411149401c0c02000d00c0d0716030740c0c2c0d41000742 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 179758758 1250 179757508 179757511
    0x3030b1c0b070c020603041e0c0303050d0f0e03030a091b12050f06040203120a05040e07030203061801120209060406080604030507050c010e0d031101110d09021e0105090d0c120803 79
    0x40c1c49402203804641d070140b081e04100307821900a400c903071a40d200c580e103240314404030000d0701000810035640c1c003001031000140c41004600954606440704580a16401110a5400180030180c68500f036800c0b00320000c002d9039400088400006850307205811304030381003a02c80880c1007a03c0c03030901001c502c0510321a500f0321003601440456404600482d1040e988282c20380b00a075040e03021807080f200c3c0c2d008820061503480041d00c3d02c0380c24150340700002c070080c04080c0c0d04c19010a4010003041210708042c1c4615004418224100d201545800d5507070051103290f4002034000c180d107030b0002e1610303203803600040b0003803801c641100c84916043c24020415000b11508075018010050000310342d44c40781c1c181030b107a020000e10031159aa2207a8003a500311700c0d0709220098654030740310a550144d00c42d0b0090001c4600c40340c004122442d0a104001000c0840664424504002d2a0b000c12a0364420140c500701d41081c1d46110f040c01c8c040c1007079032007001140c3c4400708107104034000b0010020904084d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 179760008 1250 179758758 179758763
    0x1c0617011103090a0213090209010603050402030f01050103210c02060723070e06040c031d0309040f050c03060d020d0503160213090b15040b09100e0c0c031603030b1c 73
    0x1c00005640d1011030741c1a00c020345592001d548100c104c10094500011148171120040d45c0003d08003102e0760220710308200036401f10300401c0d0380f4410001581020701003000240d80510081004c0d604580d101c0e140b40407030441f0b40048500080b46d800c4e0182c002d1403032000040e0001c000c541c540001e4503203041c1c591500d01a050a02c031901e4503000150700c0000c0c205041d101302c034403d01c540f90b80c3c00703086c03000400d02116040e040540711104848403000b1040060b14426240006d035583c0ca0300801440151401c030161900d4091400d800c00820302401030a6a41000d8102e882020300c44c0540001001d495200501030031a000004010a8940050030034956141c400da40c41444070000c614280111512124081c2440c00e51074000358041c0c0300d800039080c0120700180005844980800442c9511030300300c0d0804211500d100301400100402d003080c0d40d0042880c9103c920300034504420300c1d00c030b000d5800145110450341100c401014002d4000b000030880c05009104103402c0303d4261415004619401d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 179761258 1250 179760008 179760011
    0x40311030d09080318030a0c03030911060c0c03010c1106180f070602030304120801030f1407090e10180f080a030f1112010e0105151b01050c070b1003020907051c061701 74
    0x1c2d02c5c031034080152064400a0744070100c89008540b8182c0181003e480115034641c011f03800a100b654501000e05030f044074540c028074082c0303982da090608483c0749815103402d0101c074035101e003240707074000030700d142d0000200c0b5040c0c0d4246d10601c2a2880c0122000c0c1c0c85031030b4024403801141d0301e64004007a600c614052200044581151001a61202420b02010f8480710842481d4000314140341280d00070075500408a64015030f40301105e104494440c4258040c6802c1807041205107101070007040464241800032804070106990782a100e641e911100801e4001c011600c1c1d0080e0340a94880f5191071180c01c3c0c1413015891010440000e070b801042c600c0d9512000030004680803500105460581d28098404940040b00c91a800c80f5604109e481b840741110441c0b486403682028022107015401ca075048640342c401c14a0880e84101e0000c08845040709003010800159640c01000d942007002400d1450f9030781075032200c070719500c0541d90641c51031a007041d200260000640a0408002c00342000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 179762508 1250 179761258 179761291
    0x2100c050d1e030902010e0303030a140a0605100f0912080c1606360f030b071407030e03010902090103030915020313050111030409090b01030303140f040311030d090803 74
    0x341610b000c2c034a40301401d440c0d03080c24218440580682d0106408074014148440c0d881d5a180001e8a90340c42128a0207941d0344030020354030b01203418010b02d90401c580c040700307211640c1003101003080d04500f03609460800070b005600c5010603000720300c11000380c10b070920003144030072140c03d015566a0001911074922700c1408811610413211406190950305190781d40315100e0a0715400307a440304540c0c1140c00e07030394000139054204040f04141141c0100248403c803182c0e1880c600740030078042401894402400703010f148140b0031000010889918030f90500f404070303801e00b0004c0828010700140400a4100300761400100c2499004501e2004403030a070442c02c90861034619040383c80340900810741a0a061400041c48550302a028410012102d1000c5034103040c0c1e50300010042c1e920048090f2010107120780144241940350164210440103403142003d9400c08980c1e2040c1440014400b50400c10406405009450b05108a035a0803000d4003003400010f04a060200b8182e006484071648040350700c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 179763758 1250 179762508 179762533
    0x20f0c010f2705070509060402041e0f0f0605030105061605060405150a09020a05061e04060302070201020d0c1e060e0307140105090c0607060c0c08040311101b03050f0702100c05 78
    0x4000300b03155a02401809a403171411061100e00040a080d20340c1c0940c081c8408505070138030450419103c074500a240c14280d20740036402e0b07110b07030303082c0c01c28103001e0401c41007442003a401c08100d070304540040c1d80300c80e40c981c98503e910001e07000700f0350000d0541c01100c0601083c4070002800c81070b59044c0741d142501c140c482ca200311040310402c0e44000d4010342030380020803880c81c100c40a46504042d00300d8404560900d10908030003540703c3d800400100e81d0201c0c1440545d41e04004085000d02541001d0712012100c1d00c0c0d00510051140f40102d1042206800600f00415a00508060300f0000d003144c1c3c5072000d610342030b1340d0102204810101d0358a000001410b810001940004030680a06118a402010b40311078000d00b00031080d00042c440044007182c00121035000500043d03000c6e9042c440a0b92122081020252a80007621308110901d1403054861000881548409605040031a44c804c18203181b00c105011384400658403228040c6141010741c3c004202c00703241071203901038820f8640c1c080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 179765008 1250 179763758 179763821
    0x9060209041103011a070501150305060a05090c06040b070302010902130f0b0604141c0203070905090c010c020a17101404020a0b1c0b01170a020c0c0411030a020f0c010f 74
    0x1d1090501c1150308404c0c42e174038090844020441580280008610211103040c010b6104400c1d90048895074410400c109174014548a0190050030f0070001d00300b62440040012110700440c051b080c3d0f0900c00161400426000b50b004915255011740784400300d005c5c8114907030050404035071509810f03081c45802c00c014034002084800799480c802c2080c920201050510419100c910140315840d01c0c3c1044070005650104090402001c20a10210311880d004403801d041a450302790190600c0204400400180c1ea406c0d88035094546030f482050015000d08034091a12009000110801d40f0b00441007083c120001c12951203a4020b4070f8450081d44e070341d00e900b80c841c0724007001800035412280e12004c4200c02c41d00000b102c6401403500442101c810400d002c030102090309c0429a81c0c1d0300284c90700c0c0822013800090030902c1c08a030b0402442d000000400c42c1c03444002c11784484a5400140041c81c2099142a00d200810420003040700c2d030fa544031031000901e230f441240380c807075001d2600000031041c50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 179766258 1250 179765008 179765011
    0x50105030a030e0d0606080303042102061f09090c0807081204031205120702071401020d05030c090301090f0b0403021504020d061d1504020f010203040614090f0409060209041103 78
    0x14004011800d140c1e1001c841d114410440c3c44d038440c25100c010b13000700d60940940700c040e040c0c00c0f0103190390b41024a000a40b00002c035021400d92900707507007500c030055000300c0c03901e61041707603640d514442c000c03281c0b00840000400d4108100072440d101c50388080c0305401c48403c06640e0180100c07609a601c5003105070b550182d007041c50500000801c41800041d01d040f42c11030126810b030800609045010b5074800c2108011648880160b10802040110f00b0314041c49034180e2a080c0080c01c0300c401104801025440000c14200e01c07442c001a0300c004030384003503001c80e503490f8100754040c0400140d45030000f00300400761002d07030051003003101d200803c0d4241c1c9040e81c02160300804440540c1382d40ea4505000d0012402807042800c503244041036000301c10700c0310f03221420058840c04500e250501c10001300345c220014150440d48144000e002403908140c0400140d4500035041c1e80711a11000087d000b0070308980e84540042c100941c3d201007011a0f0080c01c1c02290450302840b513203180c0980a00d86000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 179767508 1250 179766258 179766269
    0x51f08250b1b071505090907090501050d05040c0b0a050a080108030f0403020f1816020105010b0a020303270304030b011401030c120f09021203041805060d020108090129040f0501 78
    0x4003000a01c5015a006425800b5854840d0681e1200780c0c2d1040c10740c01c0d000106003000302150000454502920b41880c0c1244d10141d103042a40c0801e00308030008091340500440760840c02d03a00c0c0007107410320422000c00780080550340c955540c0c4084214000741560000b003501d01c0403c00b483c1c00841c903014080300b41c0b0814050f03022094102855030702004950650a0004c6401c000d0280c040307002c1a032225402031050880b8401c0c40a040400f04000b400c45505a20010507500c051010ba411140d0100440c1c0c1c0100c0082c0200725a845103000000d54107007086041806480000707000001c010a0f01020350481b40c00c54a5010035950440054040e111000302e2000014214240c2030f1005240764448040c2c9503444030f0008204005601148011410307080c58070503940045810007030144414420000070940074004e0005040280100d054004c6491307000307040c8040c001c001420b44d1403d600c030040c681010000320600c2c001042e03a0702441c2010070300ca0f500480c24004a15002072207401a18101e41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 179768758 1250 179767508 179767529
    0x9010b180c0c070f0f0f0311150d151a0715020c0a1403040e010b0c0319050904090606050f040c08060f040605060a0e010909090f0303051f0825 63
    0x11220003588044100400c0c01440090511500010381c4041141ca80505081d1620b016005c0c01c00c10345110310300c4903922100c1180d10802050001540020300c010080c002690682c001100c9410103031880e00407000c001d00f4070392411a4441d10811000340000440d039960004c00074542207080b1640e41d84c032414038050008205c070310b00d03e0b540746030503401819820303c0c29040d41c00384005580c61001352914000b028400303620100d4140071040c0000307031b128014681c1c034030b120345840ca400140300c0c1c0b07900440543e00c8080401e80d0072501050f021b141282e1b80548010002c202c000d01a141140040045004550003032504481c2c40006041034402c04000800743c2e11843c6850b40c81404124110369210703030480d0401d884c2d510001c1c2c1502c401c0d0103010054a540c44950911090704001421040c00f40d0041c0d046a061040e100d0102c1c85425180780a02d82503d000304466465040c14040745029211518200703640c14000288a5400300780d070f1012918144007210742d6180d12000301640c1c810f43c0940705019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 179770008 1250 179768758 179768779
    0x106050313020102071208030a110702030d0e0102010209180703050708090312040206040302101e02071505070218070c02030c090f0705030703090503120118270602040f03030f0809010b 81
    0x1240820078442244144112694070b0b4841003080c0c5200c06107003007107c2d01880030051004818460140411200c003051400b414116150006591107401c4510705080c000460400c1925034400e40480d50340d0b02001e003a1501026141c03410821200b0308540c0d05002916100c0842c4101d4496134040e405640c100004608100403100c03a485050b50140c405c03039101404020000058550b280702d1180220f003522402c075206044480e024000e03164259420854011180c24085000800d00d000d9030640c0d90705d4001e031656150300c08101c0c6c0003c603a8141d1241000700007000082c07980000c90300d102d14401d80681d90448456400e1148404041d10b449284c405440002042540300e54003541e401000f40c0f8010070288501c2e198a400c66000c141c0d00b11100c514080180710343d101484c90441010380b40721003000040700714406031030808141170741416210b1024080c5c034144003064040c0d07409040d105170441141562403901030404c02001c25040c0c04980e2080000701c0c032060612420140c24009032808960 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 179771258 1250 179770008 179770021
    0x10207060914041d060105010801080a052a150421050d0c021503011d0c0705121305060c0d080609010f030605252007081002070c03120e1801060503 65
    0xc01496002ca507003040d651084070358250101c2d0350200b60308903540003a11155050000060000384160040c17109688000c0004000880004c2c20aa041155078045030072840788130401d2440b22050261039500450185010540c17440c04c900074022540400c03440010340004042001075940301c0b130700141c407a0704002d40040040d40208030440c0300074030092405103800700c40a1160165042030f0854403000b50607111b101444104403802a070400c40720846070f410b009642d42c0b895592108485a00020003020810369072884040c4843d50142c8402044551278400c291082c2d40e0b85d0700700045100010b000c1101003141400c0640d0818142c4004188203036030181503864500203804050030b0071a03242000e11320f045c030b01c822880b651603401065960320f43c01942c20010042100200140980031a0840101048a0b000010b10801d041d11515009a2560f000f410030710003145490f4405072440c014104e41501e26036000c11600140319044a40150f04110141d40108458090055401040d01000400c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 179772508 1250 179771258 179771279
    0x902030a080309150408040504050a02030402130c0e03100f150321050f0406020606010305060301022104060207060c02030c0f06010e010605031305011e0b150307050d140112110102070609 82
    0x1c0c04883c0d1002c54000c8903c3c5074203d011103808450035211802c01041c01d02040c5458064242c04c003019035030641c20750906800190000d0b100d11a2054860355580b603460095004030003889040500a047e6000c441000850401511144070841171103807605030b02c03040c51581e0210712400d40740c08c020480010359a402628003000d03540100d0b90140441804040c40e846201c1c2c0041c009001150701421490801e00005000c2d80c3c07014103900e2083c1d00603c44a4410b00301416030707503082080d10900703040c19151400c4c64030092185810103031003507042604400d00950000020411800c8003400c4400c016551032000b40c84100c20300960b00118800c500400c81144540061070300309500c44000c21545016986150845209040440e5410103800f03407440400007031300c1140000c4600350340514061207005811080d510001b02008203119000c100d920001449510050420043c1d02038a905561150300244644440101c1146c2c6620b410305110003951022600303004031070300703a294450341500301040720301d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 179773758 1250 179772508 179772511
    0xf200312131811191b020609060a0e0405010e040b09070f0b0a02030c1609270308040c08060907030b011d011809050105010b04030b0709081209040b18010f0503010902030a0803 77
    0x5151074440c19010300b2400204000c4c40c00840d14a01a240519000009004542c0c2c103120b0318901c03040241e4442c05605c4480460307280c0902290499629849048280c6401d10000c42c01c0e60400d251400108114050701080381c0561702860f070b03c070f80ca9550b0090555035407000780a0807182900781001049807008000240c04051800e0050302e00300310b0742c9441203290030164440e0526080302d10004100000851041c601080401c0e030061061402c000800c0007440c10600d8004e080058443c0001d0600200c803007101c01804600341959541c2c10000300701030741c50145000aa4280111500000c0d0708070f0340301503001040381800c40f080c08c607030703c3e000d18419000c1b060008450f803a61240d1115000400a116003400f924130030809507151800e50904034040e000041054051103d4002e00740000c100005200d0080404421002da444802c48017241c040d04503011040d8001d58a89031990383c411040c01c5107410f84164401010b0160350b10300403d401e803450080007030340507040082001d0100b1403820065 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 179775008 1250 179773758 179773799
    0x409020f0d03031515021c140301030803011e03030206040f080c030a03050a0c03060f030b10050603090d02100c050f070515010602160b12060d0f20031213 68
    0x40c0320004080880e4001c410420100d0003e40e5800d001c0d69000e48284005001e0020302040001e008000040a580c40003440111200a082561000070051160072948040c0100d4011a9140c0d6980d151000e2250803c5c0900c108002c150318078103104500c40f548030300480fa099401400280c5440d1101c810900c204030040d296403504000040c030040d07042008150910369550005014076111040e0003c844003004190700301070419208001d01030203e402c080a50b03411003000c3c0440c1d100d03118403a00080301c903446103801c4940072040006402011507029004807043d001d8841040c0861f504000b00c80103100680d011600601c1626040e003801000f0380001442107040b81c640c000b0714056140100002d81c01600140c0c800580e10729005110001e1200401a01050500786584100ca0303181203040240700301e0281481e2142d00c2c05100c0d00c40080740340c490300f0000c07020b41c400d040748102030020101c0300c8450103440780c03030191a0703d60800c10403030342e140c001905084200b508000c0c18520348225000b02c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 179776258 1250 179775008 179775019
    0xe06030a05130516060206010e0c042d030f030e10090b0708040e04050304050a060f0905010c05012301230f0603060d05100c140a0909020c1e01020301080c060c0705040902 75
    0x2080003d4020060b00c40030342054051544510300d001c400910b010070507000380c407441d02e82d2014401c0000c110001d540aa501c103411035008203000400d600d0000007150b85006030200801400014412070703402102c0c01f207000b90b4404118001101c240702c0100b4840c0a49000602400c01c00c001440c3c00001518131f01d482040030078509941e6640f4030141e0b41d02a203041d1040e42001804220515103100400020034490600084280d180321001d00004002c3c420141400a80c030352503c00c004082d4090a02c06518081055403961001c85100c8010424000c002008180124503e862110b04c05201d00c0040020403442020782d01509025070394202038121038002c1e00090302c001c001401408414015000038800003101320f81c0d00c900a092a810002c002b0110340100140716031030f81d00c103020a0580e00034a4001d0b9446000c60007851502890031b038250100340034581c4292000741c0c1900254102c91402049070b0403a5080c0c001c004e5107200b0031034801155400f040040049040a4004d4407030680002c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 179777508 1250 179776258 179776291
    0x2090408180307030b0106021606080105060d020f0a09030203010c02011103060d060603141b090c03061011071805100e0414010f0c050a1103092b05030406050c010605010e06030a05 79
    0x8a4030742000f541040710110b04100050001da0f40c10480e1500e4007803003080f2103002e5854400068043c0c6010300890303008820000e50402e90018640440e03c851210001155861400c0000289942c1c800e0204070311039404d02401072403161050044180c4c00401010151850301d0304804c03c014030082c080c04a03503054a84200002003074031007515100ba409100060040c10202d059107280e00c00307255441c1845501404107200c0740111034000d40341c1c0440d082d103802d2205c40b0b002100351020440c00d19803aa1314400c1c0400801c2e9004c596001d00c40e400000c800034061703034803003600c040d0719035075940602d000615103e00020f010501500c44204000d5001c00000742c0c1d14040b060010543d5010680380e40480c0c00040c21003e420f0f1f10a4107000c2e0703035500b4405981000003c400041c10ba1440604d83c40c0c0d1070150340705000c01e1015035091081c083d6400ba00700e0b41d40b166100009403054104039446501035280071030024895000362294408020010251460341c0d59040e5074000030a8058928158064400e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 179778758 1250 179777508 179777557
    0xa080619050421090608130b01030b091c0f09080f03190908070b0711010801030b0601031a060c010e070b1306080c070b0f0901060603020705070e07110d03200702090408 74
    0x90b441000b00f2010303a19640d155041444c054070034240034000d540044c3c0c44d03a0a10002c544c1d05401e050550394001c941d00765589500d41c080746040e0803601c17041d0808480480c603e10854104584180204260710740c00103d543d03a2410340e031600080c00006455030000c0040c803c0d5a402e18240d241900014206441103d407079290043c980a241e8121148003180001d495050002c403d1803141d050a0174a0102d04560665455003056000603192030b06041e12500d610580302d140030420741c00b10001800302c03601c85820481c01d5020f8082002c0c18013050007400408123840d9503501c22a2180c0c1244240c01d01014903101040302c40302d50051968401c43d03010f01c40d0744c00180d0540001406200604040849810403c0125084440c0b45d40010207044c810001ca00000b40c0119403903003201c1d02e540e080c5415540303402041d140402101100c00300343c000c0f4900104500d405034051442c500c107005981030050074600f1950b00ea4410020040e50041d0074400142c00a42e1103401440d50030035411a0614050200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 179780008 1250 179778758 179778803
    0x20f031314031c050901121506050f04031415240d0c0e0415050603070612090507120609050712021809010f02120f060f150f190e0a0806190504 63
    0x40c4030320b0000590000b11405c00d903178844d00b2601800c10802d42001001351501d4000d24880d1184211400d02c40007003841030012240500741d80c0155001505502c0a548880b100c680314403142d80b8184016002d840801c2e20712204d02001040410107554002c88006140100140c54201c114112207903004108007090004c0445e11083c0182e118025280c0c000600558000c15580000c10640c0264400700f0100540c2c0e61100c1101d2508103c400006424039090400a08118481d000780c1c0360314081a42c0302040142030343c001e08909020318161070b043d945492140f101240d041c03901961160700c00e800224001481e0704aa03804c4500c4400009445050705c0c512400e0b40c1048502041010b460010000d05801441c41a40d0180007112030a65144911001600d15080382c7d002400d4484081403911581c1c03242c0045802241b03541d12900a0325900b280014461103100c80458040d0816500000c2c07403030b800080d401d009201081004000504101d8008001d040040c81071302c20386541d4154807510f4524 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 179781258 1250 179780008 179780053
    0x706080a060909030e1002010510141512100504050402011205071e050c060f01060c0f060b0a09061d090715050415030e0d0509100e12100606020f03131403 68
    0x2a20b8004030303d4021700401c0742c0d00d1002c2e280c150959040030100500780d6041d00d43c0e4415514844903c2c0e02100d00c89001c507010540c401440362112000140505d0800c5840060300e12401100c0502d68041d91a541840140e07a82904c00074041203c40060500c0005160485507118040c0e19089201c900c00c5c1b011102000d0003000c4104c046140001d11154400040c40030b103a110075420940b003050b5140490043c050421498040c0c0b1000020781080b08201040d00540350410004000c0c2c40244c0c2c4450982008005503c42d040041c02d0070a0142030802200a465110f581201c0140c42d140c2d20f00000d260030211485900c0c001c00000300030100b441004031040c01c60010a0790fa0010300011700c10012403a0640380500700b400d105042c48014040d50320000c200542000e45c0c82d0030130b00c1e0100715000c2000701c8000030083e1240c0c0140d01d6071305005030340c0c2e91249040b10181d03422039a05040500455071a4442c000300c030b0b47e21688440d030a014032410301500725003001000d02145e1f01c6100714440703044035282 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 179782508 1250 179781258 179781263
    0xc030d0305060109060201200a0918061403010506011d06040509040b0103110a1a0f04080d0c110411091e060a210509060a050606040902070303150b03040201020706080a060909 77
    0xc1c0c400a000d03455074016a02c4000e0889800200003071046448401c9004082d0220300a00e013100181c00520b00b4403525030600100015600f68100c01480e209141c090081c1c0d0242c0722001041403100c4a003464140600340c041c00c4182c482d40e100c404050032280083d00744d40d0303103d50441020000045c00d40c0702c01c1e182501c502e000b0091a06030b5411032406c00e402103a0411040e200320201401444004d41d076a2502903010001240c213903030303803041d211101880e001d2a031100c1207078001c1d44030511745140c0002c000c00c0d6444c8038651440300040c8410800040340c1c103c48055554501c241710030200760030040202d08403007026120142c180001800028402c3d809403803214005010313104988450030750818010f002800140041c03205182414005655180007400180d90316200c2c40450648c2d11070708111405480071800542d6204070505001d0050142c404d104048001c8000001603085405c0302520f01442c1e05a0107888000d00d4036004484421015045c401d000f03071b0350714000410307105038407034480700d00e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 179783758 1250 179782508 179782511
    0xd110d0b04021504030b13030905061605060a11160c030b1602070e36010f0b1906020712080d18060e070e01060c030210110301030c140108010909050c030d03 69
    0x1d018814030041012079240500d001400344428000580c42c1c00e642c03944400042115a2028011b0904482c040801d6120580291000548401904540e645d1040d841d00820440d41c090326280e89480450300a0b081c20202191b09008101e103400409800803c0c4038000e40c2008039840e201c2c0c6900465880650b01040c05140405205585c50f8051100e1401048001c0020010f0b280a11070700b2010703941100d810200711100400e409400200022407405606540020401a40c044a20b10010a04003d01e140305550583c5000407c3e001a610790064030001da015102c598507086000103407222240e070031a50090240002c080d082118420741e40007001c56260100c0c1c46201d410002c0445c0c0b680301041041e40c0001e482400a07030300c4155403e0445440d40f62561103060541401c80c01d20b200707800007a034268142803840769860b440801031810b0342d000e015909002a0b803000395810340700d0242c0b10580840c000368010488541140d00043e00d01f40201c09a07800358944000007410290104802400309 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 179785008 1250 179783758 179783761
    0x519090c03150923040f05120d110c070902091f030b0109050f0901050111032205010e01170a05130f050d11070303020a0807030203040e0711010c050909060d110d0b 72
    0xc80703040761180080803036250070131079448144450094004100c10704900040200045800c100106841103904c0340c1003c15584018a4070203510780c1940003c0300300700c859042000100c0c0025407501103c02c01d40e002e0009200c07092511042070301a40008101760760011540c2c4000d00484035001d4081c4104440703a8002540b55005400540005038540010740030b442e030a00c8a08494460905484c1902c04c242401214030000c000c4a514610480d1510841e5001d81e01551880d107400c09407200554100362502030344008004011900441708440014200e03000f2404112416070a44c440d0703400c40c0160103040850502525003403d241032407841121107600414010300156403203644c0e21461500d10029028071803842d1002565008100ea001e40001400584401014000c204840081c8642880004035260400c1d01030106181103c46040a500b8109200345461007003040f01c0702404020300843d03003500c9007000c0c0812040c13240750459040f820411103105656071800b00e008124403c007009182c0d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 179786258 1250 179785008 179785031
    0x31206041d030f030420060702011d0423070c0b0103120c06050405030c060a020903070e0a14040b010303020c04022a210a020f070e06060706060e01060e1e03070519090c03 75
    0xd81c40050040300410100c6c031005465580e020495103079580900c8c00f48071a6a9400c0c1c0c0e101e0000940013050f038058a444424040e40c8010070040c03c002800c1c90450909565104040d05d0301300c401d4000400c5a0000b600600003c2c030401c20300301d07105296180c08005030085076942c0044031000e58003a40c5d81c0c3d0020954065040c401c0103a40e901084100065052002c804c0101e41d03100c1c000e00448100151400009002602a0384500f40100c0030182e44040c1d414641854551010300f8003044c2d005000d002541e80c1641868022150380891043c004080352840f07038040813851084144c409800d0140c1c0303a15031030503425115050410ba01c0c094185940e80a8004042c1c079081c24058410303499000050304011980004104a42c00f80081d00c074555504030302d250000003441990800c0c004400c10400204440f944480c1c00c3d203032800c0030751740c100940107010301c000e0041420b00e4006a1641c0721404c140818141032500544688201002d19040c98444480400340d90402c00c0c20f2000a0f0340d140e54101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 179787508 1250 179786258 179786273
    0x11032707030201050414130f09030906030504170702130f0b03070f080d0e061204121b050607030f20191110020a11060a0b04050603031206041d030f0304 67
    0x804484000c141032031840d400038002c0d001d94440d50381410035158503122140c079401010500d170960200c040244940f100003140003031101c4038060b0002881d00d00d0108065020380300342c5000c0c680000701084c0183c6507481030b442540c00140100d81014100d2100c154030305045c003d101142d0136080700499400450307004e042c40c0c80c1c941c3d8030800d00030711241c03410008018041756022200b040ca2808031210114080440c01d02d01c5010914420b04124008001c1845220600010500041e0b582c140c000380244140e900000509080035103035810040205918074003e07400401d030407400b0304008c6485510340308a10140549408641101400010f80c40105005d80c1d03000a20395419081c0762018200096100d43d03a0a061000404103030390014060034514050383e81a0841c002140848250b4902046188060040351100500403420031003c100c1030f01c0d010060780c40551140b600452603540d004200006001d14130440c138803980f0984150400a1410b200405c4401a07402c6415a00e0031b05242051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 179788758 1250 179787508 179787571
    0x30809101b0f11010c0b060d08070c0303030203060307120209130213020d090204050702071a13030b09032107051e090d050303040c0608040201082d10050406090603080403080705011103 81
    0x130704000740c0d03e4a00001488065415400680945440780815940d20702101030340714041002d02410903503a800020180e154008610a010940542e51140d0352203130b124100c40b00028000794041401d60000354038506072a0703240b040750300040c00490350441c0012088101d9000c2407034002c80c0d0b43c0341d02555096080500407981c00000a2004100c2140b60066908500b5642c00501c0c91011001503801e8000c03180087c0d40d40950342040c45040a41009080715649074040c2c4c000c1d07810504540c8921100c91024210305108903c1a20b0720340c901a25101d085503100a1740c010032424540c03c0c0105080798440d01400a140c40c419030045a072807d00f4100003008495640c8030340308002c0780100300001130368451003e541000440d110181c82c450050200021005006c02d040c102c40100d608010703154144040800c11900140c0742005629101e981d00025240c407400040c0c12020104410800986640000c0003182e004000010b8035200194201344c9940c0151102d5903088680410442c5183c0d0901012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 179790008 1250 179788758 179788793
    0x1006090c03050f090d12020f0a0801210305040506090604080109110108090102030702150c070f0b07110c150c0703060c0306030c0603180b070201270b0709030809101b0f 74
    0x311501d0080ca04a07601c140c14846001008000e24180c60101c8887d0162800e40280c52801d944418000500800c440000d2003a544030703860100503948bc0f00244890000090340540c1c038545420b080806018403a4000703a44244c01100c204000941c3c64420f100744800780344a8030174248050900700004021801c0a40020b42591041052255103900059114000962035012800c2a9240b0450b50002d014500300900684000c511000030050881d100900c208610745030b806400300c07142c07100c3e0764848403000760315044000d4030300c44183c040408020300502d817100411500e45075202e039140d200707556811450101090312103000348104480c0c0d103d510b000d8840c514041000c4070700b2200c40d488103540668050000351103035001c103000910030b4000401c03154058803603d0b0344008580382c090344d0244900c000d030340e80c0401b48007240070345204080c85002c40790800c000c5400c144a00c0e00300701200228000d85000c0c030882c10340c0c150f40b4110a05a50821500904507000804150b081010030b400e6484000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 179791258 1250 179790008 179790031
    0x1403180a0605070f060608012a020316150204180204080c060708070f080f040303021510080d0513050a06020a1403091e06070812010801060e0103080d0b01021006090c0305 75
    0x40c030020b0303030000c15030380741c103420080c43ca006018500b00301c0020580c94100200650800d01351400403c00070b0500440c258505850403c11302c0c40b44012a01e80c01600030347c8001000002e46800803c8001c101c1e001001742c4100010b1425540d003003041c0003000d8240014004540101c0d0400c040002400341c140101c07401c0c0d401c2c503d170107444d940c0c1e80340780e21030701d00c004010180c80a003003018440100c059401f80555200c0d4a0354032512420b0180d0b031104a2160411320004800c000b94148500c8180ea408481c0745030024612038a404034203903645d420a4003002001d0201c0d00e0009020b0341c6118025000f480e2903005841b8130489810040344044481024a0584e0f001701b2020301c2a4580541d084101500441c0000e0f004040c800024800d11488a000c1d04250010900b00b0a410440c444981254062402007000302d6641c1c07401c407040d0000744400b4001420510200b080c980650700120703070a007014810b44815a9520300c0b01c5044071560b03001550020f0751450700c0c1580503014407403160010985602d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 179792508 1250 179791258 179791279
    0x3020706020d170708040501060503031c1b0903030c11031b03060f10170c0a03060e150613050402040e0a060c03060803030903040909030207120b07030506121507020a140318 76
    0x1448030703140240158040117100400602400390a5110700003a00b0003e007582d9803034a4072400c400801d050010f03064000e61500810150b80ad003e0440c0117183c1006807681c000e01c610b10749003035402410003c81903a1a0000a00003180d565040c4007860351402d0314088800d4081d10340040c549881e0009003012050711801c0103020b03190701d90400030350482d2042c481c07940d5902c52a03003da41c10320505032112900311a15900c040108000d5030403010000304041e0481e0204100c0c403680d501c2c48942624640d802541001150f824040c4ca0740080303900c6800a040407075600300190240c2c1c50300d90a070b41c1c180e42c069510301c2c809100c2c41c0c0c075004200051003464010341c210f04003031005540320700c5240b141502a958074009402018000c0c8207100080014190a020038501030528031500304040310f4000001e454400041c0017441e006079070000005001005003110001114408032101000d00301c901907224148c0040001441192401c81030b0059034051521820180e80c402c941c0700348107046920518a510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 179793758 1250 179792508 179792537
    0xf0b0402031003021908100906110a080c0306120a0b0f090c06041206150b04180203130209060a090c050c01050705090310020306241c0608070506030a150303020706020d 74
    0x2074079070b0240da030125610301d116554441e05802d0302d80c140c1d20450783e50190700700b42510204540d10281c01c0d1401280188500075000d08142450700c10740e42e02c1d1011800b0440883d801e51404009168030010251030001744000104074285030015164088640311031070760810400300c00509509800c81c1010005103014040c0d64005400c41c05140549031103440148078010910407540c00000450365101c000006050300c0d0004c208040c2d110b8002c180e0207030825030b0308162405452080380d11403895034020b000d07074100350f500b00204010094601075102c59144030200d1002c1c41c41c450185c0c40f142644032107982c2c850441035542942c3d001130500b0148801880707400c1c626100400c00032820700402c1401a529510700c400034803070055100502940c2c030100031001c100c1454600c006c2c0b803a41c6158515150380b0a07482040c0003562040d00944907103400c00303d0204020b04040e0007842d00604103600c0841e0454a02181800e51071040e4001d038010782c400034041000300e405021040007003a652402034171442c0200f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 179795008 1250 179793758 179793781
    0x71218021203160b04060204030c1e0f0501120e0a050d03021c0605061b07030b040f030e030f0d05070302070e09010b0909060c19050712110c0316060503040305040e0403030f0b040203 80
    0xc82000c0c204d110010000780822403c1c0e411140034690207001c0703600840d1039004801c0031806000003440714030500700f40030408117100c0400c0e41c21281b05945d0f00001e88c414013071010241c080860501154030961142000040c8207109032003080d00956401601c814103000c1581c4008000308141590502d0b00700248040e454550465100d0040070a20400d40c1c6103040c1c03581c0c50524a0341c0050700000304481131004006546c0344904c400c50280d83d903e00c8030a0504201600c449a521500e90190701c0207056a11490082c0d010301a00c50183c01940e50003507076514a40003807030307048036000c0d050f03503448484201c41d1a010011540000c0c0000c01000c09103001107607410588078000c0411001c8440381144100e4900c1034085600030b41d84422002410500d0140c0507040000c1452154440c2c0150b600325600380c103001820202070000e101c90340c100b140c034110044c1c0f081d50001d001a810080104008100550011249030089120340c0d0b0001d0401c0b51200c0034411035000b00c52040c86140100140401190308 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 179796258 1250 179795008 179795047
    0xc060302030603100504050102030f010e090a230613060c050a090909020406051003060501020106060f021f06031a0601081014101b050a02030705150d05071218021203 73
    0x49080060392625201c000910302600c1e01240c0c600941010f08010800c0019006940142c8900c51603107400d0b43c843c04086a20138044880a005034031100221010850301380f034400d25103062018841000559280036401d15801300d4005400700458070b00c0ca0104206840b030b04404a07010714146043c80b0320f003403004203107251501c00c81c64041c0e203540c803500565039a0b41c460780c000c00f801040c44514003500c034800360140c445c51240038055440d01d04c0002c1c0b001e000d0303407a501802c4126070260440c3c081c040c40c00c0d80054280e101d055069551094040f0001c0c2c0c01d40780a4046010f510310b900214685800014441c0c01d0060515100406ca01c404000c0f2400170a80f16600b605c0c2128101403401e0310742022620740c4150f04220f1a04042c692220080c01408a140401c1c18020b0b01039601031520b1300309004801304140041008007204001c0c581d164056a800607030028424540b80e10f00b40c0c400500002a20f841501c1e1807015001f40c410700d000c5141014522001c4807020025504115580140b0505081d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 179797508 1250 179796258 179796269
    0x16020a08130504020304060504060e071503051b040303020303090106050307180515061c0f0207020603070c050a170903060603010608060105100c060606110d02030702030c011b0c1401090b070c 84
    0x4010600c1d48180d044541450050b1902410842d1240380505204002d03280c00e84040d41c403035161500c044050701c2d000c100312080c0c600c00c2036518081c5500e09400c0700103000050029074102840540c000312606080c0040c4000c5001e9401503880e41000f072a411b00f1200c031544082d200c0c0e409010100b004503102100201003040c6c01400144542d2480d41628108503800304407544800001014800e042101c1c0c1d03001c44001c6403c02c100215011200201c0882c495204040d52010b020300000d00710343d104410001c52a445501510314080c100d41d24201078a030b0035603101c20304441c00314125915040401c001c0e503000e00120001e01c54107240c2480e0544402040c00b0b4036020f20282d0180072010340c040c002c90b88140d6400b0074104403084e5110002042904000da03840701e640500040c0b484a148000309032400769400501a0241107901001980e1480783c100c10751000f200e241c0140b2010440d94002500244941c9099203886802c040c0010b03e0312005030005020f003401400020081001240754006544 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 179798758 1250 179797508 179797523
    0x10503101a09010803041706040b0406020c030708030a020307170f0117010b130203010617010b0a0f1b05070806090a05061501030e0714090a0228050412110916020a 72
    0x2844141c807400a140200111070700401d10700d0000600b90ba0000040007203030020a035105420107511519038035500190f0300906040ca41c8000b08000c00e8140e4010035031103c0f6801100d1074000c9695800c51907800031910601c03070700c0d408800c201030035402c035842144460035000081070134134205030404090034040c0a030b00c03200f072008403000c640600c0943c845003a07284002c041024200c800300c0c412003e54024002e01000802c00345501c19598607810b400c905989180d81c4090400d6034000084841540d0076014030204020f201c40400a0420400351000c22800381d07000d881c0c0306041041603490000064660595648420742040114102050742d036007244607410181c0701c00d4002d0700100d01a00e0003800c044d107180542c3c880014450320715485001491020760381c814040c0d48401c00f08080340140b83c8210525000b000116441003802c40c0356424000c000d0421904150b11001304c43c000089000b811034030100881198840da1514098066001c031b641781e807943c001d440d0610000c0d101d08001e01c0082140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 179800008 1250 179798758 179798771
    0x61b1b05190602030114060a020a03080604090c09090c0806070906140909091513030806040c18141302090f010f0908010216020112060b03150f06031f090501050310 72
    0x84020300c040d10001c00700c1d6640141481103810300300d000358020310030191410419503020459040040903a081216503402408030924191010303a00c09a00401040e032155880341c45000084050220710003800e040c000006000b03200e442d0580c504440380d04444803a5024904102000e90320540000640e145807804075410081d80072000000d0040185565100c100c1204006903204009540c0044d0104c1c0700102030b151b11642d4054003a4485c408014002901c4600064003d040c2500100c0303100ca0146030907280b03c0300c0e03003040703103400f105a800c840303040a0030341078888c064685030701c00c86941d00032901c00310318118a075000102da0714a2100c030759040c01550745031144001d004501040050116100035907840000580a0f40441c003110000c81c041490b070101d41c041c07080300b84541e40c1542c002180c0d5528580b20a440c14000c51102d04496510604c240f000c04043c0d2940005140550000411500d0031380030000411086c0240790030900340c040c07500004002950300061008200030340c8040020b1403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 179801258 1250 179800008 179800013
    0x41a04090e060c1e040302030312101a1b0a06092603060a03031115070f0f080702060a020c031608130b1305040506040b04140406050c0a2c03060103080304061b1b 71
    0x728000c80c0c0c03029516010108964081c0c4440a1205100d2608500c40e052f840d0f495900303000c45421a61650820072000740310940c00b03c01c241c500d201c00f164000044410b86c3c6403a82c0e0300d00907260015000c0342e007201e8039108803032441d41381014911003c01403034055045140140208401c50200e10000e0200200041d18004591007802000a115059030441071503107010070000d03000034a01d5156000080d6060f4800012500c5080300c240504070035805042a9160780059502a41000185100c58082000069407142208031003000031b40c403400340a9212064414001480c0302154046440c4003001c2160031210000c8020f8442a11002c9800040c40e4954a02081c0244150381c085078100d40b03051405581440707540903161013140b26072000d0100b40c1d1421045826070040044900c007040d42480c1c030714420846801400011113508014100c903880c0840040e18101e07080e4825154000300006004c1404024010188150f100310800d00c004569004010440070710541c2c05484440b640910404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 179802508 1250 179801258 179801317
    0x61710031406040314031e091c0e03061803030f070306050909011a10090512030c072606040804142e1d09071103041a04090e060c 57
    0x185030803110160403003240d040110794030b000030741c0c0a9012600c030784030f4030344c0c1444a00100da201da0b8100400d080d4028910a281100f100301030701c403000c0d6000c0e0350303034204103c440000112003000c25a80c4100e03211101c401450705000018151000b41101c40b1030300680c003980001200c0d003082031600c401071b240c0d413151403c40c024442900301030f0340114045c0611a011702c054100c14a0040041d4016a106a2140400002c5440c000920707020035a4010100b00f44d18003102c01c224050700301d000f52450419800d0b1400c0c1000126084a440c014411a1040c01c0c410031030954894881410b008050700d04240c0c980c0b4078240501d01c01c1456640f07045001c4001a143c0c03414030829054500c9480d62203504094980810b45001c060b804001a0048554641d001ea5110110307401d020180501c002a00d84100445520309240702d08107403407108101c0058803201e540d408c645080d42843c0c01680b150b04081441c0280d072000302c0c0c0e02c80f02d0340c803040c24000c0308805101141d40c1441c1c0c803401e41050718002120f502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 179803758 1250 179802508 179802541
    0x906050307051c05060102011401050a060309230a1e050c09070201020705070b031515190504080f070f1d0105040b1801090f140f150409050613120201060617 69
    0x100d900761010707420080741001d44c01c21406041d003600284444410800f0200f042c8000340b18040c2e000c4101803040180a02036030141420b42d02900c04c0341410152150b11881da1b146a4164600c2d81c0c2c80b02890380148480c200c1d030382264902542c141c2e804080c454841c20f41e6000c82603007181c803801c034000110f40000d001354102c4588030f920000b90382065948900003d040e4004075580901c522102c82c20010514210744080e0b900810446500d040c40b5091240740010300301c411401003480740c00c0001050b400b804001c02907654900708014690a4102440c64000ca400c4c4d51209082200c0c110804416407401055103054600c159000100719016100096108600210f8940200040740010804011035000041c1c03070007803282c1c18000784400c159480415030b03007114012036444252000c5840000300707081c1d0b20a110340c01000418005aa6211107092250607580400602c096540c00010081205802141c081e0780d80000c000d0f0700e142800c05480030151021040840840703030000303521500e0960045c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 179805008 1250 179803758 179803777
    0x402010305100e041202010c031e05070c0c080a02040c0c02091612060905150306060307170c040f020a020c0307050d08030c120c130803030103020d140f030f091c03090605030705 78
    0x2d400c1a090405c050a0203d19540042d4240700c00043c20501038007a100c04d55402036002d071928280030345c41d00300500c0e001c0d10103405c10100303020031004103095032071010190200002914900301944104400c8a4080c0d02000602c0305500741a4056552800c0180d4050604d088444013446030342030413510100702c9030301100c0103031030558040b07406140d0350b0040d8882c0c03480d24034043c00b10362104201580d1b82800c031130707881c0e059000c00c10511201443c01c105603940d1502c0012100041d00890011307040e188007007501f00c1100d60214460407000d50401080101c01d0742900580411401c12000c00c80d00e0303c15031405083c1110001c0440c2d9016035079030890f0468001036915080b1814410361200460344540400d030183d08688001007a2140d0200859049070303402800d20100c403900c1d0344c4612090540082400b40c6015070440407610716020300003001c0c0309190a0206942c1ea0000c1c00b0000003041140110700400014090700c00080c1c0c02800020645900d8140b49840f5910480c04903800d201d0401107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 179806258 1250 179805008 179805029
    0x203010602010e1005040b0610140708030703140408030106050f0d05070801030c080601060e13090204051515090603150a03050d09030605070804020d02040506280306140f040201030510 81
    0x204503906501104440c0700f20070070b43d00305000d41c10507401514020341e001f0740040c0100011a5442c908400a00d4010025041010501e00000c0d02c804051308200c0d0b0030b4608540c0007040041c016414400c4000d900180103180030b8904007a111000d00d0b0105029400500200044d00710304040c20b001a00ca844405440a000c06c1c50080c034000c0c640305003840100c40c2d40c0034a17203010882c03035804909507068410580c8c074425518201030030042500b1068011320360856687c0c0c00000075803118000d50780b00d408120554008118000284400458a55030015268205000314401c50340d9200803a900100002000c90000d11240c0c00100011038a45c001070042c030807202085030721070300101c0c10400c9a014940402040e9119201038940c0d44046500950112100050303c0c011328140d44843e80048c030180c071442c00130103844103184900071005056000e00500c501c04004000d15805644107084c610641600b080c00c043d5030901148001400090505803207100044035a0b60000f0306034020400c000341c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 179807508 1250 179806258 179806261
    0x31219020403020604080307020306070c05251701050402011b030905040902030106052107170309040e100204090b100f0504030609060906050a050f18030406080c0405030d050a020607140703080a09060203 89
    0x22040e9523a0f001c0c4074201d00034020b55000850a502424404400c980c11002500310200c206000010b4615002002c1220f13500f4107070089820b00c14411019140b00e41e581c0002020f09140c00003409500c80d40159000041c2040d11180000750b00c024050100c0b1001d84000c10004058800a0701404468005941200c2c10031031542c484690380c03029806012440f800d4443c0c06494480d04c4002108404240029600130404007107070303041c9a0311030003c50b41c10781c00b9902c0c11402621407000341c0e0b005500005140b44c0300e0700c0c034017054a8100740081c041c950703d003002000ca0a0646014001d03000d03520015000b40c1c0d0798001c0205000e00d9800908085034015010040e514000d502e05c1c008110035079920b07441c2400c03e8002050320a1608039031400140541c0110301f028030b41001181e0306800142001c101c1e0b54180030000e00342c2c80422a00011a2050321080d4481039404002450150024601d01c00c0144002e12080b0400c4c0c8403080380c030907e8140c82e08070065500c3c42d03850000b8006045008090b240b0010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 179808758 1250 179807508 179807519
    0x50909030d0c02070e010803070804030b070e100504080106090203010501090303051305060304150c0c021c050c0603040804061404060c0f02041e150806100608040201120c03020306090108031219020403020604 91
    0x100c00c01603c04150342175403681d884485259983c061010000c0c0303107403403c00c01800032a444006059001246207043c0100c030188802140a03c0d60100c3c580000c41c0780400c003030181c0f4600780141c1c005402d0800d01142598900340000708292400d100c050244040010b00782800c800c210241d1000c0d29000e00459560b003070601d4030588491000780e410a107a89007002d0148490711131541102d01340d4004060003d01035003c840e004043c003030045c040b200c0c1e10850300b0b040a11707101d0001851049004405080d100c0740f5007040549103005945480001c00704c204030910080350004110b0700d900d600020f1000740300900307101090061180e08520091110040f1402403141e4640c0c01c603030350104481c0e030400086a40d400103070350f0303446082e1074074a40b21802c10000d208651080c9140b079881801450110a94080c00070800e00700c401e00003155001035000030400c42c06041c0304000b28010701c21700c4002d601c0c100540d4a54500d42c00c000d00710410741024a60740303010718809501510f0103542c0060856940c0c903a42c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 179810008 1250 179808758 179808763
    0x90606120c0405040e16031104090c090e060603210a030e0303100812070206090409080702090705040e060a080a0b0601050405030f1c08090a060923010c02100e07050909030d0c02 78
    0x144510380c841e07810300d00983c43c2a840403c6c0d004080404040c40100c0030f007107a40b824403030002d44000740c3e04140d81da1902d1000c0f50300c3c40d1140000b040044070001c2d03141458041c1d81d0420741e0081c6a540a41c0c40412401040010030312400c00c000100640e580e20b0b2214600708402414504c521442c8910010050048400d9001c140c0c4046400c144101d0340042095805103103240513514003c0c0d030166051101855030305060b00603e00341481400e4440c540488c0d6800200307030782c6007902c27150009000130405220030310704003a00c260800421560517180318038220a0680c0c80600e404000c0c251081400801c146902980c181c80107080000c041e500141c01ea400c00a50390644061018815900c080d024422140034814643c083d111b01c0c0b014101c4031420f0b407500c00141c0311141d01110806085041030041c0b11541054005418989001040b5000820710080c6000780c014801d510a614000000411100c0012210215807007902d0109082e911040000d0450040490080c415428078990840d041c4d0b01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 179811258 1250 179810008 179810017
    0x40b04090305030f16120e03040504060609031101140703050c070305070b07061802010f0c0f0204060321020d080a0c05040305030c010204081b0a050603060d051203160e030606090606120c 82
    0x24818041a60b5500000c19884100f544001c0c0407406e1100040010095600010004030250f4104c0745030650302c102003001c1710402d501007800281c004200348200b05070a001c0c2d0200c2d8070f007480e10b4103000754000d150780d80d584101e03840241408400241c0c00d0660405000100017180c1220070760b602c2c965525081c15032940803038412034060f840c01c080d0300402e1100c1c02801590b0307501a99552070800802606a4180103082415202000d4010300c00e40103943d00c1c000d40b0059807049800e6a150003c3c071070118000901100b03c42c0a6400c00c0007444000d550003030110b68050f0140d2404108100b2000c42541e0318881c50708050301d03c0c04001910a44440705400910484106904a50302e45084c070000c0e406007020308000d10b510621075501004180b50000103142c010f030008104502d9080030f40d84580ca07240f0922800b00c141c01d0040200100042050403070342d007110107410003110310b00c054000030b82c0310a402001c8070311907100e050108010352645c00945401c6450549408214244201c030401150070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 179812508 1250 179811258 179811271
    0xf040b031e190f030f02100f02070b0f040b0a150e130209090f030a031a0d03020105010806010b07020609041107080d0b03060703110a031e0f0f0e070f090b040b0409030503 75
    0x1850740d8014882009041c40048160000f1030555a88415981200d6040d1306103140400c40c0700d41d44074100300012510514015241c4c001c1c0040c0d88032014a07100341c03081c000422244180c03048108100202c1d85041d60310f03501000000000480a0451200300b20f10941500192405000c58040190010300301401d0701a01d07000f00c0c0d105403140d03160342080b9510a03400300b0701c0781c480c1c10a0103000c4000d4000d070869690744403400c498282e100c90034030105008013280344d0241c00507916038004010484d001d205560140c10300d80201740c6801d80c150042043d038800c00f01c88a0160f41e4a507144090304d203851054501c102c0e400740302d9070b5498649840c2400030b4086c0c54402d51180c0110008982d5085c020300c54122408004c4010a0400c100f0310002c5d40200309400ba00385400e8016103808a0301240c5103d030034400310240c00009912214041003504807061f030b1030078000a6210f800140304814180549104954408001050440000c004a005031213220011a081410010030230304158008014520450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 179813758 1250 179812508 179812513
    0xc0d260d18050307031d0d0b0f07030b0102030403030c0c05041d060105180a0b13051006030b0a0f120c051801090c0804200105071704032a050f040b031e 67
    0x5500c8003222000540c07510010b01a42c002c115002c00a030103100003a81015a0041c41161811003002050b505010043c085a2041500c800c00c0017000c0007110480d00243d1616040002c0354041001035928400d03401301078140302d440c2428008000703121080401801e405001880801000300c1106a04501a80c0c031188130b00070340001180c1410614094100310009068101c0a07842da90502c0b03006248209a964001c104142070400c0302c1c0581c0501d5020b4084024100200d5150a80c003c00329000301d00303c14800c1801c4001008080c001c0a44a0103484c0d0301030741060107060a00c1c01a034800580d5000d01e81001e010312085803a911902130080c102c07071310100180044c92481d80c00300e5484c1401c4400810b2000c02656400204461074101640540f040c182107103003903a6500c40b020a00361100914480200004060080118012302c80d60304d2050009881c24480c0c54803451450801c0038051180604080c081900b03843d9034a401c5400a602c014060701c1318454152001c5042840a0f07400c0f42c000d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 179815008 1250 179813758 179813771
    0xa0507050108011d0c0f07241515030c050c0a150b060304170a0c020a230105030903031b0d020a03060311030f030318010204030c080a050d0f020c0d260d 67
    0x425000d0080c03008215405030b13016072951440c40c003c0c01500682d4024610200a00031280001c1c01c145030000c0701541005250002c6406602c803900307039004000c00000d040c400800801c008000c2ca420311910408500300410410700c3c542007200c40c0e0103040500070041c8a044200070900420040e29010b043c0600d0060020311403031028040c80d0710042e100100b900300000100e0074204072203400b82001e052240741203610090290001584142260040c02c011000d458200c4400c81851750103d481d510300703091150851034214142901c1340130043c80102030f542c0207000c0450741d4807010200e9201c0184104115140d11444a006008080d40d0004840078442c000e0098401c0c5000140030b03403855031540013540746940c1e04411441d20400d0200da5141c0e03640900000c400100b5560011020f041030303c0c018400700c030840c1001031030640120406402d020403034101580166011905202482d0161043c4c10301c1410b03072500c10190100070210a41c1c0640c0003c8902a00c51588010000c45200c58000e0016 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 179816258 1250 179815008 179815019
    0x40f05011e091a04030f0e01090b0c0f07080f0a03030905120a050306010e01051602040902040f1b0201240303050901110304081e0336090106030518010603080406050f0c0a050705010801 81
    0x40c031005441c090041303440c034240c0aa00c07c0c403404d1080c0c01d56106140075218a039581c001045a0380001107070b07419907041340c85490b801d41820051000240390b40001020440c03d481c1c0c4494859403c104040c041640300c3c10b40394103205040103049140004c130b0304403986d0788501480041807070b002070307039014002682450340801540c85281170b075864040295925070002d6456003003200030141c910381282c1141d2592010010031840b84150503800e00e0800b407008020400f00002401c5400b2444004a004207841401d490f907840001c9882c1031307070303410300308951348242d190010f98000d040e141c1c2400d0140300002d00070860310000f1940607107062101028003c0c5480c29103125449016070402700d18503403000700044403001c0d43c1041581b00e030610241e01040c000500008118507441c26000400402d44880a0000d084030003400100501c2002008019035402c43d03a614006215500c00c1004000c000315814008005d002e0440e46412a14400c075086200d080c42c01c1038031a599489041c0c00301d1300b4480001103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 179817508 1250 179816258 179816303
    0x15120406090b1609090c020f070308041508090d0e061303030906121406061309020f030f01050405060d02061b0a0b0108150712180818030c0109030b040f05011e09 71
    0xa0f442020b4071881c10560a15106900030645100d007401184182803000494440c2800240069401019100c1d5a01d0601c6480d03402c602d000d211190400400c002042203c80c40452503800c501d505240800070050702d5000558903004a104d202e01d2920046800010503401c20440302c21141161201614905050295801c60725400301440d880f034031a400080700d6290410050412811001c168a200382e01d541e6000200d03007041100c803d8842e40041440f50020840184600501d8201c8080c0014540140440e141a4088400034040c0c00041044141e405a0b20b8a4141c5583c8010407155004d8050405480c5401d0a12800d243c900808540d400d80254542d95140b16000c581c9544040341032040c0c007207009004501c0c807025050100d01e03403040040c50403c01400709900d540d01c02c2400780c903d20100340c03c2050700d04040303052003004d6008000060401494a5009030055914804103016003011405090312820302c911350294220308407516010356008490043c00740c1c600b03600c07034036560701707401c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 179818758 1250 179817508 179817541
    0x20d0c110411030a0f0531230723011236200d03050304050111040801021803070815060d0605010b0a0305070206011d090709050106030915150515120406090b 69
    0x209910788035206000d2a40d00110781c03180312388200000300f401c0c17044407241c00150a00b281800b0254200c584104208000c1180d914a4090070001c000c01e1300ea00d020001c0c0c440402940701003a1291145418403801c0c0c00ca4a0283e02250300314070200000b80d1411040030b03282a024800c5803000400106800d0340030101c0d10000b50000c1c0580440d10800c8140c800380d81c20b4100a10841d190764031100c035030300c6154042002d0030040c002c1d1000561140c03a0000000c50100708a510140260301a0034104020040001d01c1c01e01452240008416901c40001081d503200c81c0c21400303841c40e400d1000000b6602d24071001000590308980d010401d41d140e02e072040380c441300d0030b210754505c030307480c04000e0150100119a001d13003020f44002103511441d501e440b000c05441c400d0740404003003a41c0d91540c2e41800b031080718014100d107480d041000041d25850400d80804400e0245034014148c10303145408540c0c4120481e0300741c0b0311600d001c0d80f440c640380c5011805068011404c503060014a40800c016480020303403035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 179820008 1250 179818758 179818801
    0x14160501082a1602130b030a0201050f0904060e1e100605070f02120607141204020111010216110102010e010b0310020901120f0207110906010f0806011b0b070e01020d0c110411030a0f05 81
    0x8003111116500112f5598005101c41442c40d1020011010195954810b41c00140400490744049107000c030a24207140380d07007022440c51425104100b00d580b180f0304800c04240c03152400e19079151800c03810180744242001c1d00094200034900c60b0f4410f03410000841903c60300e01c607900c4240304000d511070700195019483c0400441ca10001c041001580581c548031440e070300c0c200005041203481d0101c18103d0400c0c08007916034480c80402c2e080030b564280100c84010805074001d00c41c041f080c001007076885207003040460440303501113130341d0955038803c00140c03184200405041c0f044141071501714009507c40301013220401c00c10440a07002e1300f4444000b520612058654580c00e07015503005071400c036070040505040119110303004014400001c1243c46440c0a2020623003540380800c40036114200704240c450640d480304411060456100c0c92032038030558088a0418150141c00101d0050700b2054101081200003104021059090f98001080740041c500e0500054594505501d0769045440e0720 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 179821258 1250 179820008 179820013
    0x70b0307031d0607030b011805030a08030709031202060129090409060e01061404140906190612050102090a0e0615090f030a14160501082a1602130b03 66
    0x40c880e40e000740d01c00000303078841d0890aa940000c0040140c1422021501180480e0760f942070900156400020b0901422002c40e40301c040301e0030040001d030b44540080c0014000540040000c13060781c0300300500c2004541c0f045150040080703806010b51503040074024806401d90341401d000406a6451503022044110000e2500d080350b000d00f8480505010740c420303100d581e103400b05400000320074404c1e0002081c4221010698074111010002074915541c13000c214032091303605011102002240c49500848030344440043c10307039140e8080011302100d07440b205030a041a0cc00d481071060640041c001800e00b100d00303181907915841c049030840400e0b24403039000001c6172448802050540014612200d0082c0000b29048000300002d02d4507030904821608135040c1400c10002c41d208100400740400f403a40c0700c001141c10031000074002280105400780c04000b1060b83c00780410b81a44000e122034100d0314440d42c1d05002c00044e50344865081049004940c10301840d410080c039403140c3c407d2010028007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 179822508 1250 179821258 179821261
    0xc04050105030403020106081606140c0c0907031b20060910020904090c030f02030709140403050a030b10030e0c0307120303050c13080604020f0d0b0106081b0d0f0608070b03 76
    0x1110301c1e0304001c0c0218255941d400740462070030003c100480f4880520a00d5680321810150b00030000c5042880b01030f03200700c092081681044002c14620740c003400642d080f50b055526414201c0c00381c000b0314180a04a200d051843c4096603000d18100016140c005100030b140301011b10541d583c0104549140c02c1d500302c01e10300d90188005400070080d00400510108004116031a2081c20361001e070700803503014284490840031030409219003001070403091030800100c0c02400ea58202c1c01c41c0248001d00b001800a080b40704a4042d50040d212004094050b5080601260018000344400c81045003d8860040c00c1c0c0703101d142c00103d900c01e440400d2a41154840e00395400d5000e03080c040e03c03041c0c80e044e090010b4043c0300680081381004000503002008213003000c0c010301400a01682030103000b0543e0100e2240030a00007223030030781140c1301c034680100c080d0f0f501d050703000340c100c03681c04821580d503400076070900348071401d0f04000d01059500b541001401c0e0755150040d90765056102d5222030300030600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 179823758 1250 179822508 179822519
    0x3030e031e0f070501110301050301150608070c080403051902010315032a080d03090b0c09010816110a0302010209090c0408060f0a060b0c0d020606060c210f070c0e0a02030c04 77
    0x68890b9000c84981e26061840d1a6101402d54000c580e8051071240f010004004902c1d0034024000c0070301d510421100c4a0f0b00708071005007000d10060071601481000d02c2044200400c11040b5001142c0040c15116002c180500c83c40c4407a00b1280c00707a00280c10040008001806001d041741101d920500c640e01000400c554601741014000b480d240240e41c50303078005080302092021040d040d109941c001fa41256074540358080d1000900100c102c60402d0140e54100e0b40c02c00c00603900b0500e10843c03a2140b800204013184e40790088040c270071840c0140d20101d003c064054010b0006024100c4141c0b000d660f0750110300c40740317020b644991800c542c000c0c800300f1800d1440d0b00c892504102404c5011440e2611480c090350345a101c005802160340c040101090180c2d03043c000a50406000c0320102d151041000d8441d9035102d5106441c45000c4668200400240d49481225820441c6105042c1c6441840c2008007100607103100b40c841c221100d170005101e42d0350311b100300c1c1d10030b0205403082d81c141405e04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 179825008 1250 179823758 179823817
    0x906090f0301140915070306050a03020f03100c2001050601050f0309010b032b08040302120901020106030b0c0406080106110304061b0501050406050601090909050709020715021603030e03 82
    0x103003155099540e5500340314400c81c41074050b900c10340c0070038000e000c0300f080b20903652000440242007800f0546840010b0040da9200b4029000303c03601144c114648042510010b810301c038507201e8000a19241c44514000503800030121105030300c0001c0060b03003ca110f40d01c501c0c244d5204681850009800700811041848448081c6820881040000980302131b00c10100740f03445a450b049065060001e40b100101010300201001080d03840e1825016505040d68060b5541200b410b00080b50000402c00c248540d01c00d5004d10011600a0710582940c2002d2001c081c40d035005000c1d903000641c2900011881030b004500c00b00c0c69080488c01180750a00e802011a00c070608628285170b6011f0000f200d0012900034050030707000382c2c0102c0c00040e440c1440c41c0090b00282840c0d0041c180d55050995910105101044c07040445e009094056a01d4600e458108288080718125010440c408207905070480b07044e4041e10740079480380d18100310161085002645d2400f03154821014101e0300d80b03260412080d070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 179826258 1250 179825008 179825029
    0x20f070b0706051b0c060621060610140706060e010b040b040b0a030e01090510050117100203060303070c08010b030c0406031e02030102160308090606090907091104090516110102090609 81
    0xf12100d8084201004c0f850076540003002c1e810302030388003005100451818941c00c2d113a00e04500714010078810700d0429661114401002c10707100e41d20410340814114000c030100e4520303941c21340010350382e10003d03c3c09800520305402582c105d94161340010803002008400c0b28180c90340c04142c40d040c145083d464422a41c0400805410503480398203a401118090040c1190b051107840684548444007003103400300c80703050f40300d07041d045200e0782c0342d081851000c1104440d8056903140941c0e25520140420303e03600c207e500c0107104000440c0002031055040d40180400c6104905580c3e030681c00307808100581d078035800080c20709400c0c03440086000c0c9841090301038883c40a00051b0502020380c0c410384903000015001e0740420060001c114a00c9014401c1030b6001808541d0329020341001c41c08160740301028060117007101d80d2036000c6041b92240005a45c000d000482080c4502c1ca0030a082c0b01c0c0420078040780c080482e00380c85603d82c900d0818020350f6004000a010f01e070800419008201401c5030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 179827508 1250 179826258 179826271
    0x70807080d02040b030a0e071d130221060c0a0f0302030a060e1005150304080406180503032b0c1b020103110a0509010807020609060705030702151501020f070b070605 73
    0x1001c00195180c15501c2c000f6000410b40880303020345902d0a40700d190156110b2031110402c68110303620901c140c00801001010180440f0b9508401d652141030b160f014600844000e07510806140ca41c0000b55811807038040c01940070b000342c440544a04130700d42c01500800d20b40354041941000b50155040c4281e02950b441415000c0120f02070396946500403070f41000f43c07407005044d60650424441030400756403000c00e090190004e54514581a100c81d0300c40d0081e0300486041002e2400ba08403842c110601e11006094000c2c190303070380c1d040520303c4a0440003a21620510014060401400c034040ca4440c0c0b0724500020380703900c0070604840d19142480c440d9480f04034145a500e0b1b2802028981000c080d2000410701e4031002c1c7d44105010001d480400018801811580a1403c0140c51603022880c2504490982041e035142d446a40c03040e0f0900303071110840c1c582c0406d0700d02000200010b040704001c014100303030250b4914030446801d840d2101c400d0b000b8500c0c640c00c10428900096100d602056102d403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 179828758 1250 179827508 179827523
    0x40308071b111503150d050a170a030501060221090102010204080111030717040c09020a110109050105011a0f2703030f120f060f0f040b0a0303080910060b070807 71
    0x41e25041c1c07003080200000c141c48502825072025120308180c40c01c2d61003071140368071003821498080c000d01036488604075090702a1400c0070318502007203c10400890781c664005003610850501561400b00354002e813207064006800c00000144242c008646950176401070300b20110810f41c3c88801050b954054080281103641c2000000394012080c41240038048604041554034200342100030003d1040c902c02e091480076003410701000600848000d4101c4a00708005a16104144025210032510344104075065090070101420002d040d4042410f031000342001e101400008012065613010300840000c00c044200081c02892000c41843c5d042c80100d10307031a0f240104d10002103400c50b000341c03010b032000d5100420003220400111652540c8140320030114102440d000c00060080744690079498020114a03514510701e4442c2d4014080550b0081d02c40d10485689240051080c0c1003142e03031807080e008801e020000d020182c091784003220624002c0070b05003841034413059103581c09100c045910f032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 179830008 1250 179828758 179828777
    0x9030a03240902040905060103110414040b0901091506030203090714030a0807031d010e0105040605032502070e0606030103021f02100c050c150615090f030118050d0906050304030807 80
    0x501c1610340781006800c03a4880941c4503880c22021030b050300e070003402c8203060500385081041d04511203010358003103030014114901e0342e20285c0040340052100070000d42d0401c1c0c8a10012941e190f540e0000e014000305c0000c4284403940d40d040c102d049002c15511040300f5000000c0820561031000c81407001b02070010256011b418242e40d4590082c0d01c6004114089105488405035a041c0543c05c080304481c00c0c01e1100b2504103400c0028000d1040d4000c0c41c0030702ca80400481c80196181c080104090807003480040d601d0003945000e995541e42c0d10898692058600002d202801c109050300c0c1200c0d400b400e0711035403082042c4014408100c42458204510514039070961b04007590048012028158076120366424081300c40e50309281d0b40b04000110744a804d0180a000e0b1a951020481c00200c440d950303844170303400000540d8108a403c81c4582c1582010481224243d000c1646080203200720202c415880702ea00040d558219180300300b5022540038000900482e00490041d6400708943c6008020b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 179831258 1250 179830008 179830061
    0x60702030f10090b07080709260d0201051b04080c1c05030304030c03080703091109060102010f14060108060d03091509081f0f020c0a15020415030b1809030a03 70
    0x600c10022210706810fa00d402c4070205011248102a4120300b1a15180c03100380ba114901400400642c0704034401e400e840c080070017030b0121070b11548070101d1402017034403003c0444540081c06058141d520320300c4502e4580316140500d126208540403200100b01418091500d901008040b140c146a10300030f040a9082900c0020428801144558841d4444400072041c41c00c0c01440e11034000c1a00041c03615240700320012810300f803044541781c03a08950011640e07440c400100d001d0803495130888020b07403c0541d540342c50080d00c031030240700300303402ea8406c0c0d866510036082205080708610060081420307450180f0420503407035461300c080c030202c3c00c12026080e5105001c3d407403d1060880f81104c0d11000044d514189114022150000a0f600d0154240b00d800d0059a0721800d00c07003030080103500340c0040c8282c0c4034080d4040d28000c0c22084585280c0c0002c4c4035020307000c0c5c042d010000788107152003440c400451a041c1d541c240203001034401541002150042a0000d0a80ca03421304076100750080441c22 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 179832508 1250 179831258 179831263
    0x61202150f0d0204181416020c100e040506010f08010605030402270601111c12200415140901031a0307080f01060909030e010c0c050604091d0a11060702030f 69
    0x20034403030b1070100507540c615020350050642c10481e000001e5a0400c0d960b00321035055046126003040550800340f100101000069140c0100d00c1180703a040300040074500d18075500f01055003200303070f401d403401d101941d03c850045816142c6414208089201301d8014840c440c0b08101442d409032004d441c00e45400e5900040034120701040903a1134400c1640400c0042d2541c1c841400d41c0f48950038001405100d140d0840000b080002039820340c01c202d016485409680c0c0b0359000b0984040d082c5507600032000740c2001c2c4082c1540103004250316030031590500402503101d0042c0358440c1580c0d60503d41031203e5007004601800161a800c07624900014000301155010b004140c0280204001011401e42c0503c01a003503858940c40182e0f1245031a40c1400402d800c1070660f0f00070502403814000041c4289441d0700518140e410141e00554003040102d240441c035400710420700d031881c807090f004451004042e80e40300302940d00207101d0445075841940c0745c10820040c0180703038802015507044003056014140b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 179833758 1250 179832508 179832517
    0xa02040f0b13050c09060a0c0c060c050609070b0f0304050a050d0210060e04020f060702030a05060c0918070f0f030b06030a060e0f0f070e04090b0403021609061202150f 74
    0x200340603a40e4441440c24a403034504004100140002071201c4c0ca4005400034031070040c016010302852000500c98502c0e0300ca1000800020340c00300000c0401a12004000c140400d440b0b001c031a80c3c4134940105040752400207100045550080c00c0901d006485d6104809039000604112598800c4030050300000c0e10500c620301c0450030f13039801040f250000310000e006852842e4802e40b20540c40320140300168407040c1c1400c00200c01903540710ba0f525150300c00321340751042021001c0c02e03138001c00041c003115a24000041102810072507081d00b001000c0b035044004030900762076490100c0e0780740018940260091860f00d601000500b80042d010180401007807040d030040f68900f103a9607445038240100300c14007000e141c010001280c140a103140c41c00707448450841c007410103424050803800b203040e144d5442e005000300b607900c480700c400103061614010f540c2c2c80075001803480c60342070300501140c100c256100e03c1d03040b01c51042203600440120780a020056002e12803a10070a04204034a21083e00c500b0001d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 179835008 1250 179833758 179833781
    0x90f02102d170f0f07030c05040528090207020f040b091501050c10020d15030803010e040512040b120105011407141219090e0f04020f01030b04051305010501051203030403110a0204 79
    0x6141c0b0b403410f2130301920619401407410302403601d80b00300c40d40c2c4a075014054034142c4000f40d40c0f41c1c4281d902107480c41000d541c680c203c5003000c6440040415001503603006420344030f2003a5155900004c00104000580d0340c2c01c000e043d001005603002801040c54541c2071840b820701810300c546080380c1483c5440c24544240c1c0140d080580000d600f00050090348110488011481d07407618202e03007503644000d11880181b240101108a480219040c8081840303048c00d50580030030030a6855a50b03a800944030f4102c404103047e800141c0f800028594020850481150f070648015440c014041d5101c4215000d601a401c00c1c500c62414030004210000d001000e0388a00c00e40900d151903001301000340380004070b400c2003900100f0f1205120900400e0214650480c0e411a140f800418400004070000c2c50040005e03a4428100400e120951401c030700d0b20352280740144000d01c50742e80c0710414001d4100000441a090f030340b04000160100e40318441100500c2d2a503025a0b2061402d0b40005040e07a1860a0a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 179836258 1250 179835008 179835031
    0x1030b150d0c120b0a230405030c010c08060f04270302030910170a0c021906020d05010b0c10090b0c13031a01170d021b0112090f02102d17 61
    0x194810b1020002490341c5c40058180300f4002da408280c485140d07040c580c84003801d03003682c840116081000502c19a07030000c2c282402040400c40c103c6009106110980b00940039021007032048406080c940210707910300c80c4820800784101c07100c0100c1c5018881c46602a070440c04240000c2000da6154090080900d116035100c1e42c0440106007005010800600b02070142c0d45411404091180c01088001c4003c040b0800c030400303455107091160280c8500a06000c0381803601d00082904050040a4607031030501000b204c0219510580402c00c44d064a1409454010800c0009031440c2c0980004c0010018461752681d034150b0300d507140300310010a400480340c4c103c0018014000391044140846030700b00c1800c02000e0192014a010b5241c0c01d1035010409030340b8014060403410390082c64807035903020400e0000c100030081420889880e9282038422846020000c40600320b0318427460131508460611000c9180704030b00010841c05010103030707c10b44248071041720b1043d616003070f000180348260b203030810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 179837508 1250 179836258 179836289
    0x105130302061305061515031306240302120703050706020a060b0a150809120a02070305060c0f04180906020a0f0206010510121a030a05030a0306060801030b150d0c 72
    0x100a42818001400031112840c3c00c40c0081c0810340015082da0045441c0d00416400c80c0781c4000710b03a840b420a62850041000007003400400d0090002505c1014000c40081068421542d0058040181501d0703503c100703040d21505101502c1d0407004044c0b00c101e8082203c0d1940d0380ca544d1b81c0c2c20703c1e001d40d208401503042840c4510520420f8006d0359243c1c101206d28a04140c03c24581078801240034040d1030400c4580400110584420001d0b0000c081140c45003540f2144c01420081d5140d40794041203d150103221f02140840304e0344400d99210a141d5801a4206400c0c908109030300c040c8420f0001d001e945620115000c155203200030036912005a039500440d0041c1c0e580640b41030b6060f8046409002c0e500035450000703038060000c3d03090920031280840d488107005204000303101c10300610340e0715001d6041984204800040240514a483c1c1c4042c07218070780d610070964218100340300180145071040001540d12480c09241ca401e040020101c007540c0c0c03015107a84c078150b40c1310342080100034212103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 179838758 1250 179837508 179837513
    0x1020c011e110708070308070201090506090706030f05061c0f0f030e0907080105090c0711091303020d090810090602070b090606030f060c1b0f0a060b0f0f0d110d0203010513 76
    0x1c0d1854a141c640d400503d4440c8541d070b0014603104000001e01005a18408a0f056030710030b402400c100c907048000c903041801c0500006481341c007148246404203140c002c002405000030301525104020003024554072090742ea5408151442c90101290340d08074002c00d040c00600e000002c0c00c807490087da910080400807509110a42a000c0c010301c0511245000401440d40c640c22066441700400719a42d868451b189040100c1e10041000e05034080d22240030014001c1c01980d042c030182e4000d50844100c80ae40c0c4c101940c0200310b9000703661003504280a426a002016048824011f11804c1d0052074104544c94203a0110f00c02d8410042035040703402401000d01c0d0400041d600c08100d40301411550500c11a19980392141072090b54001010300a454420380d024001100004112819600c401d5481c0ca0510010400c00420a100396005114201642016141d0215506015012940e00c0036a83c0720110040b81d0410910f50118240520f140180c80a0207882d000e4103084048002480703892 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 179840008 1250 179838758 179838761
    0xa0e071e0206010317090307170f0303040b06040b2e140a02160614091002030c0a060b0103110c0d08090106170102070c09110304080906070f1b050a06020709050901020c011e 76
    0x42c803443c02d0115061064446035900400d10008070b42c081440041e02c03201c2e00d0045800d2014920ac40000c07404040200001e0010301c0308203510407d82190b00b04840510b100821800d40909110b0610001000d82c0180d80e2000003002401009410708081030000c40e0340c604030441d68003107180d03480160400885400c1100001c22518003908a07818401000305001d1031003d92030280c8000a8819441741180751200c0307000340112540c0a62040694202100d64204500034080b61112580024039181000040020140540d40800394010207000c4e0b008240104a40902014081041035540e40070001900b003082d1108880210040c000988c450f40c0c5801c00003000b10745680b01a00480c02d1102000303d1614840890742d2103548410b4080c1c507203680c40f000c2080342c02401001002003240340d1704c0300c1c24005480ba000c401054003a42d820040d5440f0310910504c0540b510860b00564800c2c2c00910102a80d504080d0b030005480c4c0c0010300b0a090300648070b0942d25802050444d8036a18214506410820b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 179841258 1250 179840008 179840033
    0xf0516030e0d05071502040510090f0503011a09040201140307030603050606190303080a02040f030804090f0c051812030a091502010216020f0103021303080a0e09060a0e071e02060103 80
    0x20000980080c81556001a090703126100d401420b00d00c01c00b40310841141142c0c1035401501001c1e01201c4203003270341000030b08811114000d104c103403203141c040006e00d468140543c01c90401c2c40760512003426041400c4c014030900140040341801030705801500b41460800145205504503940072805070302d9070421a08286014000034010441240701c09003105560121004980e854a0400c0080e40d5001034103000b030245420180c003503d103944d000014441500d0141056a408060400c00361565031082011070302e0040c1601c000c10414090343c030a4400b130b022031000240c00900142c800092071001d450841e8081c2207100007280e40014103100c50340c039801c25030020181342c0c0000c600e00303106421002c298002090303001384241010600540c0daa4803a40581d50041a050348280d04c207616450b00c50b140e500011101d01c0014400c0b019584285401400c5501880c0054845124241811007105001a0042074007060240030013020949074010500c41c801d103205640541036950551600340b00b01da14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 179842508 1250 179841258 179841281
    0x1b05060403020c100908030304081b030705030403060501051905100903020301020d020409060e0405060c0904060302100f0e010518060d0e0a0308041e050c040c030f020703080a0e010623040f051603 86
    0x3e045c0e0140701c50b02c0004100d80d00b20f500042d4680d203540c00448004040714074050156500d000104240d010844000302803c240d80c0718840501c9583e80303a43c248800d002e44500c030132000300c8010b01c04001505002603038041141c41450100030090f22500401e00b03a0380401001c6203c9039000408010f42011842044050240d5101304071050619460f500c1d60341e01c01502500b02c00c070b40020300c41d100b41d07501e1703012000135580a041c100380103244a030b0140c01c8000410003000801c603d03030840034507903206200b01e41180c00c4101e00228100c0c204811301149401039506100710540e07034030800070344074010801c107440b0b11b10030780d56034440b440c191803d0490400400306120000c00c02011f00800940c020900c401c1c103030030a03074000130820740070700703040380500805140585000d00c0080c860052552181200384a0031202c0d00030702c070b4000c4482c20f481c2242c40c1e510541d040611500c0714401c1101030a001640310360402400401c80480e00502101141c0080d201c90070b901102e60210207849405008044c1c4218 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 179843758 1250 179842508 179842517
    0x8060a080d122714060f01080a0b04050a0606030f110d0c0e0709091b02010e070f150909050a02030403080703050103030f0c050325020a080705101b05060403020c10 72
    0x5881020340982c00e42040d50034010784440035803c2c140d9510400c0800422040301d914030a203102d041041c0091648403041c080ca014050000d01d2a01c89001501c0c100c4034410b001300345121041e01d46a2111101400803581401004d01c400041007190003540c2c040e50281c91140184c403003070301e002d03110031011100150289602d10310601c007140b1111222011980341c845050240e40c2c4110341201d44001c260484a8007038030304251540d044001ca401c808600040ea00200044440c0d454042d55801d564841c50306580c9445009000c800318046c0444443c17065800e000030a6034851011070190746003112000b0000c1da000c4100020b041c0d100c04104e03000245130404004039411610002c0c20003180d00102c1050001080310803041100c10001ca9417003600e02c0c407101c14058229910b40c0e08507031200300d00380c0c0b041c2c0981d04089076410010901104403007000b4001e08011b890030700c041d147c050741c10a94031001c0c990ba10044001c203c1c1400401d12032403081d4041c016081605e410401c01076542000700c410071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 179845008 1250 179843758 179843773
    0x51305060105030a02030601030f33050a03030302090a0314030a030606030504020a05041808181206012106020702090a0605010315120602030c13060801091a0603161103070308060a08 80
    0x40e42c001c1c0403a038020149030000350350782d41c602d00142d024140c000750300b400300c03440c00400c40130040c1401e1441c4100586441c00c1400704620300c01201042c00e05000d20b5900003450b070300400001e4046c0d4010301c03541c0320203803180c50540e99035259083c1220340d4141a810513000000d00e803000da5814407030702d4003801c42d50070200400c1c2480d40118030921100d004041c02a561140325084400d190844400070302c4e1300a519030b075076101d10600f8555950b60210041c3c010510380d80d41440d40640480c2490603070381042d07a021a80404071040201c0110300d21801d481555013003240c180075840d244103161142c1c0458a01051042c502800102254118605210780c555004014070034002e41e180280000c1d0b400c00320143c2c4945030004000102c2c42500d000f040d4402d03408800180d0715810080d454121103034131000700140b91000c800c902050302a141440c0e4088000c0000600324490304514844442c80c41c5041c1c10f16149000041d0310710352000c482507010805e45001c00c221840c2c0494240040c0440c03c000d8201c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 179846258 1250 179845008 179845021
    0x17030d150b1903063b040305030a0902010905090903190915140903070e190207030e010809012d11040501020604081b0106090c020c120309010302180901030507051305 73
    0x101d0081070760055440016a0b404445940310340c010b80090f025130303035a0600c01c810200030310300380e01c61740d24200b42e108204061314507189100d420618819a0140ca6051642e9180c130b106200405808c07808905000340d40328003141c15200d0144c850b02c10a0f9420007984c2c0d4072075481220103c00302d5074200c1002c00544003024080f10388250313110343c92000705060085003915050180d020340d006205045130541b0031180002024030301c0081d018020300c100360b00c651248a2283c404c1c0264400c0d40806801300b040000d24200c994411a0b104c0c1e842940f03280000354001d40c2c0e0412603901000310b2802140412811600789040d03901e44902d8641c0a10750001900d00383c034100001c0d4076503500906c0504034801c0030404070200c0a04a80c80100e00048000821440341c445450100401380002c4403c018482e08151100c9400c02d41018854803440c0801141014900e40045010f90320409042040d05400000d00703110341c440400f010b01841c0315002030200a4240740900074041c1ca150000301d00035040c502807126 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 179847508 1250 179846258 179846279
    0x12030516030c1a0403091512090602070201090f0803090105030a0f0e0c19140f0612040303150801050f04140f07080c27040201030b010509130516020d0203030a050a0617030d15 77
    0x101d858007c0341c02403100c20060241c6409494800b0310000f0303801c210f407090801441d40d00419000340300f40c0300c8900072070700c40d0207c112203500c0f0300039801c0a80c0208001403456026038081e60340902e20440108012030082c1e40c100c01d584441c1296107031980910340341036152072302c2e988010040030203030701c17401c071691420b4480780c0174100c1c90344114011030000d000485281c4910040b5880c0b0f00c076200d4080203504003468010010151510a010b2080b201c410118404006009140c000c10340e068010b1166192901d450080040821918040e8450006c0041c42d99000784004d00017070035510060583c0018500030302c0b000030800c03550303055450321000711000c4420340a403140c3e401540a20300000c14007810001070b80d06203c0d032500d0690041ca1251800c00c07440717458022902c95400b400c213048040034204003c0e40d8401c2c1d03282016000da0828400143d8600060740600d80c48040c15401007801c590b0b8142c61005541071950f40c15184d00000340303484001c1c40398002c0c0c00c42d0700c0c1401c818401f007502e003004000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 179848758 1250 179847508 179847527
    0x5011a030309090405121c2304060f0e070b0909070c20181306060b09130e1207030804061a1c1505010b0c07090c0912030516030c1a0403 60
    0x1031040d0407036408203041c4003040119071901a0600d0b4059500caa07000047c0b5400c202d40c400d4003814a08101c103c1c3e4481c5c03038900b14450403202d520070000b81a143e5507184d4000e01203428000205a94850501442d054100501002450040b900542c1c410802050010003c0010840414065080b81810024000724203400e881c00f02421605011021207001071100020203541d1060000c100080c08400091045181c50b481e204020401040f070ba145d80c051214060f00b060320394080310600031990180c180d078000b010819484001d40300f0102c180c660001481e00000016030005885404020400c400340c8502d0200c1030034051880101e0100000007401080f803035101084100010081504200c1002400310303043ca1107003003d12240d07854248001e81a04082840c0e0041d00c10044009480c0c0b08503c5544480080360b1307240800181401c028040707000003090200d081042c10010394007441315803240041c800c0c0c031075503808450039214288940f11038105400300c01d016000d02d06000000341c0010900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 179850008 1250 179848758 179848777
    0x1609050f04020d02011215090e0d09080706260708010f240f121a130b0f0d0201050403050303040c0e090606031f0e06010e07020d09080c0d0f020d060905011a0303 71
    0x2c111130b00000d001d8001387c001d10540c104a124554408a10813005800082e00c482d030450403595000014441202d8101180c4669402504000000d2000e284542240c1105100f01e10741c03031017426440c0f40e42145007201246c1c00000618440014030292448050702401800d600c2c64120f80d02000c0241040a1219018040240050a00c5104415006400808410250319410020105040354910040c0d4050001c2c034400d20100340c4c4200304144c2c5200741d8540e0310015141c43c040341c140718213101c8a0100c1c52800d905020b41440000002441000158880e521441d42c000d44149400d5480d8440d14010b0400034080c0c11800030009183c0b00082c440002549080301344080c1c00003409900c0040010844103e82c90042c50b00102740c100144c0207960103a0451350172510000c1192800b120800c40602407003903541c00000a204c0c4928000c1c1040d900e0714001d10321040381c250035500144e003034141c1d150121012600e03240d41c082408420312503905101104d5240c0c0001029000009172a4401c20703222 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 179851258 1250 179850008 179850017
    0x61707080403090806090f0c0418120918020903070b070f0201031a0d0303150e100303110c0d060c0311040b0f030405010603020d08130f030b0103080a020f1609050f04020d0201 77
    0x1d00b40343c49a204040102203040503991076051030950140c45045909010855201c0c00c1d090071240d080034031656003c80f0171030203141c041c8803031a5192903140070310403e0300007000480d110110704d40d000d40e6000c07601030301034002c01642c800c1903005250500140d580a030f403200b10b05008950107d00c16440e292080c3d5424a0b00003400b030060446007207821340c40f8224981042c42c030802e1908041d0560f01249450f00044032040c1103035510000030050706402c0b101442410000c0600b04000b900071603100700361032041015212010b220a001c40d0740041d515405991840c1c4500c0c2d010300d040d03050712030f1078540c40c55980c041e40307890b003440c0c0881c1403441b40058000714180c0000c009800d0000139400280035550040c80d00c82c41e05400e00300740d001034200e10001d58240791180400541044000000401c0301e0b408404800c03643e203140c680d0340307440e0416000d04065004031100b40428440504c456000c2c064450350303c0e0307002400c1c01e0801049400c000c0120130084990414800540c0d540100c0c0108a68246032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 179852508 1250 179851258 179851261
    0x9070e090a0609060f170105013b19051602030f0a090306021305090f04030807031a0909070f08031c090201141801260f06030a24050106170708 63
    0x1d01000610032548089906440c00740e0205a100d10340308184101e0301040300060396414911151400c98400303100742c407605030181d4001904070b510701401131040707102c000060a450b030a1b40704540300c4100850b001000906c403d0700011080d04603101e03498000c0c03000c5410038448032031060042c3d03503481a0b0812515a000114100401e14491001c44028550000065490b002012405200ca141d507024452050f04600002240b280c02408503d2280341c040c0e0316030f003450303c4416040e00146503013031031040102805809111f568403140d060728001c841000c0104000d620708100d040881c041504202016001008501741507071805003128012800f1050004542c500b520040e60011020380c101c0c20024004608880c10b1031107a1500d403543d003002e890f0045080c1c501d11a05018401003003032540c40c59000800305d035050b10210f0000340d00c04000b40844500f640c0a031141241110254070191081000c40d001650b00c2d0002e005843c0102814180141704400000900060386002001c0c40e080101d11070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 179853758 1250 179852508 179852521
    0x50f070b0403031416050c070305010f020c010c021b0402031504020a08150f010210050a060e0c041d041e021512090d050918070e120105060315060a03080d0e030a02150609070e09 78
    0x23001400440c2e001008018050300051100040d411102c5020081d510302401d10782c0c041e00100e140668a01c209580c0302025040f502000002e42024002c00b101140369041b0310000c3d101e0384001c00d10a00181ca030708501c1d03d803100480c4440c000c80710b0b4050040208407038082190348c00107518146d52900c0103003c00c59940300c000c0303100201840c0d48211034104410007485190000400180241c3c1c03082c0741083c40e5034114030079080e0026025034004014401030084580720b0300c2001307240754001c0d06c000e0861602c8000760b08800c07581d17000080b4100001402c1d0042c4200d00708104a941380300c081508245003060b10b03c0c0300082d0b401d01403c101c14a03d142c00c40002d00041e1003800c0260a00100500b20b5200007010300ca5103000700702c1140d003180684240e030781000001c916401010321902c002013101c5282030640c0e40e01c028a8215090061a5688a07290190002d6062001c1e00034440c8641c02000b100c0d0314032a404942001c0030f49002d0007400c00d0000e003d074159001c5020200303054261100805912400f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 179855008 1250 179853758 179853763
    0x90109110a0b0901050706150303050408070602070501090605090d0c140a0909050a03080405010b060a0503041a060f04150506030c0304032d03090f0203070602030a030f060513050403050f070b0403031416050c 91
    0x52308040035203941c0f400d02000b0960000c02800c184c4155204444103551110000d82e5070b4407030341c06410f010400e040382c10040148540c00078000804c000d80404a00701c1d0540e40c01010030380c2c43c0c01c020410f2114007148005401c085101c40001e212000301844240859111542c85000ca0343c0b01408000d030020002c0c00b484000d401103000004003405a6503601c4800e50020210742082d030342118021089100c011050000388500c0d07008040040c8590745082c0100b04100080c43e2810001c507201801e01400262a03440e03201540c1b080644008060b070b64502490024018441180c404030f010312183c440340781c103580080d10203520680c01c2c2000100c00106040c000c000c0c801c0d05000039494401e0350f002203803050340031020b08810551510140610b03804044c000040d070b441c03401141c0d0803192003e4012904032030b681129400038040c1c10060724102d0f041078a5111035016103002d441200701d1001340810941d2600c2000d039800d00007030a42e4003505082014222102c1d100304684100800070804070321020f001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 179856115 1107 179855008 179855021
    0x807021203070e0a0306020a020f0312011e080a0c0305071401141b071415070203031602060d1416170f0709030209090109110a0b0901050706 62
    0x1028810030150401070508040105201000c030b03e42d1100307541034000c0d40c0101d00c090780d00d01003180b01031b02d44140816486260b5008004429013030810380c01c0603040d691038904449569010900d414289055a0802025402144040d408021568120008a0b4499400d4949440e40d5581136208128410441070100f91a003e0101c00390305503100611880c5a8001031920420f0100800d178500750681d00000c0a0480f80b5a041900385019041d80b0003014103002440e02d040c1e610f40c00320352680034198808c4406c01001c0d90078003c654a80e01552050594150200448010041e05010040040d111303001441c1c510b0030903050359441040c005c05c00c50000c0803011002e03114981c2204003284010285000c02070400070100040c0d441401c603500502050002181c091120700b0302000c80e002203810f00f44200c0804004001850141050715421542400c10300c1d00c403031107410003c002c0c114 = true := by decide +kernel

theorem cover : BRFrame.Cov 179676258 179856115 := by
  have h0 := BRFrame.cov_init 179676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 179676258 ≤ n) (h2 : n < 179856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
