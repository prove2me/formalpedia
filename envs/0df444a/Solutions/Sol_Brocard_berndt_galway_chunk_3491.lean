-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3491
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:48.855749+00:00
-- url     : https://prove2.me/submissions/54aa0ea7-5f25-4d34-bf36-3ba34d1648d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 627697841 ≤ n < 627877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 627699091 1250 627697841 627697867
    0x50a05010509180702011d07050d1202030405060412060b0d0201050301090e0a1b05030d0221030703090510051906080c040b060c03270108070e09070c050f0d081311010e0402 76
    0x30507261603005079034508403003003076104004050300d00710210b5002d0304055185c800012b10070f0002e02d0000e08880c0e021046807081030b0080040324000c0c40f01600d49a100d0795216540901900900c1c804e036150b80c14121a03040740c2c80d054810015555058440a0550f403d0a4000004105030443c0c00190b00c209107103880800c800d0220480c24071001a0480000c508110030302d41040003151084003554408a445e66800217480412070b020b20807181065101e42d103081007140130f044070070406040c9010b400e88002c3c80c580305030029407007007903120308078100c08100c01840c40443d8600d02c200e1000b034200100d104902e1416400100c1401c800030280c0c0c0c101a0741e1403106045030300000d40007100c085814804104214201007803a40d01c1c5003401c2049080c90a00780107403000d0610381c4098414014a00014107890103001159940c2da0007004980d4080340101c8140d54500800d0004030200d41075000150b89001144440c0180680c0011030f00030b42009140196040014501000e40c03250f0207010014810007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 627700341 1250 627699091 627699139
    0x10212090303040909140d08090c0d021c0f030810050d020907050f0d0b09060402030c07020904082a0105060a03120e0f0409241503020910211506050a05010509 70
    0x409646d080202c0e004410b405032620b21000328001c103101c581c034100100c0c188082203662102d00e084e101d80217004014400100c16245400c007018500400c24690024080013400b005000d0b4425106c1082c191142c001805520b2107900c0303a241e2007000c0f80d600b01e0040c20040c1c4501d030000f2103402c0071811b02400c49400341498100500300d8008aa6441d4510041d00e80a003c142d00000d00303950031841c0d804e01410441e201d1244500c068000c154820200d01040228400c80c0c9455046001d82d101c070342040c140360343c94035043c190383d41ca8560030100401c0c00e130310304540702030100d07039200c821001d00401c0c4900654460210107030650b400b0310015902c014544a0780035001a00c0c0c480d4196410340307401c001c4400da01510982d094002c09103010078001c44021260003d03410341c2d4044420000315912005804051002c1ea000300500e0700d12550040a01900c418090508074450302c514403114080d80781c3d420848820740700b00c682c0700849610402455000f100100007414029248901c0c03400e1110010708089 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 627701591 1250 627700341 627700343
    0x6150e0a05070f0228140d120b1e121e07030b090f031e040b0d0603031b0b130f020303070b010e0a020708030c030a0b040905030a030b060f19020f06150a06030209010212090303040909 80
    0xc8c4401c841e1080940300c0c1c403443c011840d0071135900c941b4000110404141205001440d40620240050755040701c070300b08030300d80100d0f0101113418131544550750229240c018608c802c90301c400d188001308426510214420412207004401582041c101c3e034406402030304420442201e2200811001c1001c0341e0940007807403c02500c0d070b000b2811703528626000346020801c2c9400c8000c86014031440c40028090002d55030480c0c84042011001d41031130414040b00610208000d40c18400080e0840400218000c0f0314120303001006080204e95402c810030301688100f40c801818080c00308005003585001e0ad0203907800c03041034200001c408603200c0126085500407403094800e40d10100340d8944d07031a07040c0600100248180d8819003450158802402280504041d0b000820103c800300042d540c803c0101c07180a2141324100c030f540c0d082036050107468049a42c3e106006a506071804a08240203000700c851604060b4018102c100360401d0419094104000041d4180010000002d110155008001c00c803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 627702841 1250 627701591 627701597
    0x18130c0b030106113f070b01050a0518130f0501050f0a05060406050a0b09010c080f03330904050709020d021c1806150e0a05070f0228140d 61
    0x207541010f0000d84410a103070740c048015403055040c81c000740c1400c5000745160b45882164100c006042c0f05080300e40c403c41c46060402c4101040c4802405009501c144c12103d00792882d0103425112024420020805411002c1c1c6503d200003081011202c403d0f40a02540113100d403c150403c656191429900c0036903050301b0103074241d424080f0202481c4501030300700204407000c109591404021412942080c41030b00385444012442c021164011030221440550000b1115035580d103c01844007150000d03100160340300c0da90503800d0404144640010103d00400f40c02c4808141d00d6410882c0001006004071040e0107032400016882c0e20302d0026001d07102008401507241d0980d000004a19440b40c1c3e03107040c403079040c64140d1f03030b4107107420070541c0b00190080c001140860b072503500410154000e0f8008444502c081007003081103403499000500070072040d40c80054048111604aa9901040720065940c900391002000007d00003100700035103d21a000e0319100f001307500c402c1800c0c00c136015096004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 627704091 1250 627702841 627702847
    0x524062503030c0206090a17040f0611011802060708070320010b030c090103030816020a080403080d05160519020a02030f07151b03030e0f07091d03030618130c0b 71
    0x800d0b805000390b0941d00d41d1440240180d150101c08941d680881c0365000c1c180e0a203a402451800c8508400c4a0103411443c040242c07941c2c0c0c4038030051403400ca480d50f0152030351030125015800040d4039402c1c030416400500d01c6040c03860a0300ca140e142d030b000c50000c03828484040d007114a2044090540010368522100010381c1d642c00405050a00d010301602c41e114214010044c80007a406c80941900500341d10b40481c01c8240c1d01f9016031910140e0345001c1c000c804081000020064600c006000110760b80d0710501298850f000038440c40c0320740041450101c0d10601001210340080408640c454150b8812252050703081c0c1c0100c0e04122200e41d2074000ba8000f070200b030010307a89000c00030140d0a02407509855100911503c80c112080c41c2800800f0140c4070b9282c0030f2500802c2041c414070001c40030954070b0380e644c1c90810f1070060214040e0040c5600d0500002949050301100b0b6a1207664098150203a04550310340810b80200f00401400c2c0c2c9503251180307400070038505003051010f05a4100b116903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 627705341 1250 627704091 627704093
    0x501050102191a0705040801021306030609020a0804150605130207020f0307030b06011b050d02160b070309030b0408120403030b0a0f1202010c11030d030603120305240625 75
    0xc101a1500c2501c0c50401440103882c0c00644100154030041e4107440804015845113282282d542c03040340e100103081d6002003203651007141c01030f201004a801c0b644003000032540d1261840c003680140350305032000c50203082c0001e0104808201c2915496180f05000410a4440c0005190bd200440d6181305050303010440340110305200c507a501d00b40720304400030104035203075607100195408020720070360400603908003101e80082a00c006080091780041910800c0380c80c0c00000303640f002041e90f40c502c8003a40c0100000e0001c1810120f5042c19016031b00c0c910500d0642d1122200d40313402620440b0044000c12102807003008280626004510990b00881c0303880b40882044200501c54000007015160501d0030020303012403c2c0c10fa04004c1d0b082c02d00000003241d9040282801000100306501800b40080542c031566041e4031000c252403040f100510b450307400070320071000c5a0086560720b0301910101320101c0c940d240144581d018805c020001468550340c044035054150740315034000503020000c45210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 627706591 1250 627705341 627705343
    0x50c0714040b010e0d11040b0603130203060106030213060e240315040b06030f090f010e070504140609180a020d210309031d0d0b04050a03080a060302010504030204020d020912010501050102 83
    0x31000302c6091900c02c44140301c40000494140900e1801000402c0f065460501905c0301c0e000043c00c890300900701602c0380350000020f5241c00051000724441c0c0520000400c216010780700340d40c03842d00e203c0340a0030410700b05142640c88800c1c4840880d401050b01c1207007180e40004101140e0b42c00514900c00e600c070b003444010203407070514030a4650b20031800c18160f07403042d0700c2c0c403015607921a05c401c03203048007522050b01c2d1604088039130044240c1c55003829070005080c1e40000d5100225070095508000b0713a0a40e403104e072484603040e60100d9008081d038010680d0b40e8031403010500400c0380c03030b01641c201050700da0015500e100801c42c201c400203005800c103107040207842c02ca03118144841c2418020021550b90003480e0402c000912149200a903c10142544401070400c014580c840345806450405082213a078400510700c00f140040e01c40320020310704a405000e1202202c5c3d040e100e280c103003800c42e802c0102a40192820b260030a0b420311958040b5503505a1038407002c0364441c000645941068002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 627707841 1250 627706591 627706601
    0x20f07171c050921030d092423061e01090906271506140f39070501080a0f1b020c030a08180a03121e0c03050a030c050c071404 56
    0x181341031610901070415131031008000c82c0e000c03500c3c02c0400513400303609181c001c050550001103048640c1319840c40c00c010071030561020380182c40110071105c1e903001154034204064001c51308143c103c0034564a944503154100e5841071115014100002250789521058044644690142c0c0d12424190b9200b4080300f0104034000f1424002c07401070001c40044803408a100b01e851048008000c010b80c1c0e401c61072038485c815102807028603064140c0d55900302d02050450a0313081003c0c1c80b0048403107810b0100014a5110741524840a4003034540145080015640c2140061011500b9501c0d40194480313410144a0065504104031407000e00c3d000298009160110413821140242d014210a9010502c948240e42180e240d00480040a00c0c42c0d90215102c04820360000b091003a184070030306034094201058000301246469451405001518120b0708241c400c14042e011503c00c10054144034426000564031040c0e5040c854035180961075940d245c8a0103511a20806500e82a01c0410f85458000c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 627709091 1250 627707841 627707869
    0x100c0506091612031b0618050606151c0f060f0312080108071a131d041403040506160609020303040602010e120901021915091a07020f07171c0509 64
    0x21083c142e80803568090030355014040e054102080b440389443c00c00505401008445c2000f0f0410b00301d4840038540503544c0c160a0300c100784580c01100020b07034184e1010060f43c0b040c040302c01d000058010703641c450000400ca01a00300720041d0310342c6404242c1c2070050071010011482103440c01300d04205a03070300134940c06068000300003039002020304100e01c09140d4044001852130424456035140d050f00b1340040020745a01040741c0030709240f00951484200d2a130588550b02131030702000ca070758200c1c00b4180c07284518020203600000a100e1016800d0341c0c00307520109140f040c0760006140030983c002a1031900603034001001070303440d10404148102d0910109400c0c500a9010504203020480080d4940001c2c0d045030301031011a2054105100c90384448203d81d1900c15420083c0641c1414020071405803109a0b078510907555000c03508181c400130f4926000700810006e014803600b04260050002c00181c02d0108a229038140c0e014a0802a80100341900e001d4036000e030390758140014444490b5500712 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 627710341 1250 627709091 627709109
    0xa0c021503042a151e09062303042d08180103140109110d0c03020702090105031614060405030f0601090b1906230c060105030118020a05100c05060916 66
    0x4a40854200c0b0040c3c58030580310034031440500315480d2a0101c0c2c9005600003861800e610301007001110700e40040c058025540c2030b41c2c807034511b145003019020f0f480d8502d0b0302d00c10300031b801000040c0225042e580455034405251065000b800325010020800c040460010b884610000035100d102c601d080030104041c400030300f02401400710450000c01042814032500c42501d840d004602c1c0c1c502003820488a00400c039082c200005231420100a00075000340300101d010300768803400811540780000d10300728541002e960741c40200381004400300b41001c1c5400b8807600030304140300c040b80c960780c180143c40c5540720100042c0025850040602c0c1982c0b4500b012a0188600c801c4412502020151031070590300c8600b00b07090f0281035544110ba00e480007847c202f000a402184c0800b88580100d0038071b0482e00103c00a01441c1540c3d814500340510300d240003544950f41b504100300740d00700040110080b940d281880c0820031a20346605090000898281c0120340001000368021841c041090000e040c10300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 627711591 1250 627710341 627710393
    0x203060f01062a02060a0e1f02010c0503091b01022404020a05040e0d0e031c031b02010e0a06050406060509010308030414060f0105040e0a05010204080709240b0a0c02150304 76
    0x5030f02860300703411500b400b81c001c2e600020a21581070150700c0320202c020002e42038440c9903441c1d403407486458021010300001942032082d031841d01d0784208260390060fa0b168000d000740003410301c5500a00c0c400351002d50705500442d416180e18050340c203035010045000300f000e180c1c103150920400503020541d0304014401ca02c2c0100070050302000088001d040c3e40c01d4103004011484075400a813426900c5480c0c407600b4410380c0f1040513042da260300510b801943d820700b5030724034000075541a82a14140c50300300c1e6040d0b0012048102040a036001550440d000b24000580740c1d850703002081110009070401d642c403240c0081400100300c0f07880340da0034403401d452015200c1030070a051034480b150418481c2d98407554a641d035130a00000180b00c000401607000008540c1c4542d20401e181c1c4480c91841482c40161800d0302c0e00c04010440004015001000100d880350182803201c50310003070300101301d2801080800c88441c401a10350031007003113194805140403901c0703113040d15015400140348028044994010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 627712841 1250 627711591 627711647
    0x23120304090204170f19260d0b030a11131407050403020a09060506030a0515030a050d030b0d0b0f19090f02040609200f1c0507020d05070507091104030203060f0106 72
    0x325100382070701074120146c04a440581800e8030204012090f500820011420400700c1f00c420704014440080e12450500401015a04160b03d40d16100c10141000050318514015458104040d00081e200c50800050f10240481030030144030084950201140c400101402580790081c01d20000b0080340030148212030400c00030645500015181440e000e444101107420340400c0184d941c1070b1140078048030f01452680c20026920710200f814200805d25042c21700c4464107000000c124802e801c5403041c02d4585a802d030307030010144010a920703101d50050300d40b140c509005000e9000300b0380c010401c0c0c40d49907101d4010041121f1b0241c0c05100c1181c5001c4406c40211a601310701d40084c001d8400307a5859107141c14409445200390319620381c450360041d0049111200961104e40500003581c01c90710131040801d02038807588580440900160b1191808006100154100744001000280440d05141e178a5000c64a844416100f5000c100c480000500c59542d0006c1c04403010502c800b0400c0d10315001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 627714091 1250 627712841 627712843
    0x10305070b03070c080a0302040b0a0305060906030d140a020712080a0215091009110a0e040506060d030c1415071d100f050f0f0f0717030123120304090204170f 70
    0x71300e41d0000c2c01a600407810f40565801313681074800805803606041c0e920706480c01e0060050004a80241c445d00d01c2c00085852824006982c480815507034442040c607103850701a94006410101d0001c1c2144915040070801c00c0e440082d0701030700c42c89924803540321031009001a09220b01d015120295908000400c82d0042001038081d54440812100080c42c600030704014120100380030826401c801c0090740050051241c04282d8440d81c02002990946c1d00d8100810024209200340900041c4080c10b43c04003242031881400100b07100403084841c503801416062418a80407901140030a60002d115450242403180f00310580d901210201412040c071140034040d624505c16440404c40c011400001c80804034040b9648103541880c4907440d003040b000c000003540d020060444600031001003421000401d80c007030781e05a0b0740741c280200002c848603142c0d92003256030055107a44034141c1d00c8503440000041c0010700150412010169842d820030380280601040258018141c2c0c0c00009001d032a094 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 627715341 1250 627714091 627714107
    0x150711100c0f060e06100e0a05040807081602040c030c080612060109180503070516060c050303011505070b0403080601090803041d091203070504060917120c10050f010305070b0307 79
    0xb5100c802c540c0340c0205814540c0050203955a18020740c801c04040c0105440502030401c02c40b52560340c8086c160342c1c3d0542c0b0400b56a41510014040d1030709000d254000350400c2d020341461301031002060841e19007500094156804102001e011076075a0011100060788144895841401a0b44491000c1c00490340966284c80510a1000071607030381c81103103420607891200c50012504501201e450f40d549091080e150304405104e0282038014010004815005140d18849290080040c5003540c6c40c1880800f15190302c0c2004108100c0b040205c070000503010808640114004e5840c43e049248c00c20014110a40c80d4015081c107510902c0200607040500310381e44100c0e20207400c204071a445014840349000c0b40140b008032044404410003c40c281e010380604212881542d840340380030fa441408075506401c890010354036811903c0021070080d1408003d0031303112007800c03c031600c0070948400e1600b03e500c140e8018240b85215001001880400c100c1100948814412103145040c0404060f103d05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 627716591 1250 627715341 627715343
    0x2030d0915050a051326031609060914091302040e0d030b04021c0b0f09240a0e13170403030903140105061c050a141e010c050d020d0902150711100c 65
    0x90241c140b0b07046d80c50109003200d030303900c0d008103500d40c0c5034203100100c40d8507041c0034042c140c0050383c52040007944c0340c03040703c0e5001101c1c4801244000c0c510f04105000011400620440341030804200080050321580b140316003012070270000d0300300388040060040c2564461103500340b140b40140100308100380c000c0807502104008110000340410380b0b0f408528107800d2000b106510100c000d0030090242c0c1000080c0448003980515030440c0405c82080150040d114081e80000b4121035000031504620034500c03080301d9020f18441101c2c203c0c0a03140401507070042e00100c0005600001c20803c00a4180c10140a0784c841da0003880186000e030b0101d410120500fa4000f112522004a44103120003400000380b255003010410a5a04541590540c0d90070741c04407260000d208041d14588540062140b500c4000c0c8a503a07080c035203280130302680d000c0e401a903041420507964600c1040142d40e0180c0c0c01c24400b5a070015203895982c14100205c040d000b102065020f889507412030341207190300c920022001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 627717841 1250 627716591 627716603
    0x9060f1c02030111070305181903061a04020c070609090612240912020f0604120302090402090d032c0f010f03090506101e0510030c02030d0915050a0513 67
    0x49525800043d0241103805a00720036444001900340a26502400600c05029003860317000c400980907040c0450310a200c00040f00e440310000003400000c0284d0814000b8080d9081020b50744418400007074101d134001c203400e0300c440c0d20a1804101854021445c0e0f0014520340e84100001ca142100307501c1c035414000c0005140f03107800c1c4c10b1103175000700f155081c80c0d0554076503100b04000140c4e490054510a035130300301e0320090321402c14a502c1c412000240c80748915803002d090000c0c0c0398560703000e60203504035000140e801602403110f00b0700f44e00c480700d803045658042c0e9075580400100b1032405042080115000d800c68040303441d043c0b070755121918400d03284042840d28800d1310b4082e41044008252410005180d80560014046800030b13140d140c6060701d40c0079046d45a800015001200034080c00c1c482c09400503203032408099054001e0740403c55020150054030703c1c0c1158a0000001c03140100741c04c030f58012490031160032414052003503a40c01280400e0070401c1c4d051684440300700c400707401002400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 627719091 1250 627717841 627717889
    0x160e0d141e03030421120f05040303140403020714030c030a080d06060512040b1003021906020c0a0e04120903140604050c060a02030d0506120102040303050d0506030604021c0503090d05030909060f 86
    0x182c58031500002c440140901b40400100707124052100c09080251020fa000905002c251040b268003580c41a0040e9410b4006001041ca041c000c055406450082e550341800360901c0c604080e00c050104041d10361191001980d00c40d1401130450842d03200c2e8014a04001d4144844100c552200c8041078002d030b0007241c621113580d610105643c4100b4903800c000e40041d51014504052604182440709550080e003e07036103c60013078401e0012001061040188017210080800e01046400394500b07010500d0346000c122080c0c40392612000020a201c8400b0581e20102c104802c3c40300c1405403101b00c013802c4400341d24040030610b00a42d240900300c40004100d98840100305141c1d0390104013203000c0f110600035500e41d40da9050144c15500071a006034030f030604050010300e0310314012662500c0350790b008160b11140404102d41000d1542240000c41d00b03071004010b0580150388404901c0800e52040004543c2d03414408144403000070003810290003614000c141210580e00c00341c0c4003504001d4001c04403d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 627720341 1250 627719091 627719153
    0x40c090506060403081c060506090f040b0d080304300807110a051f0e03211003061103090f070e060d06061e0e0708160e0d141e030304 59
    0xb942c41113600083c80d041000609441c984041c946c0001808000007080180e0340e550ba05204e880d1242d40308072030307000b02c02600c050160300d026403008086d2034001d01030f0303182c802007036852403810b6205542c2654056581c00b2007011007511030314858000a001d01031003c0481203000c0c080c00105c0054010028800b03082030301c0d001a14200040c0c080c1a030440304941c1c144080122000c112203c00304654403072800d00d800d01103545000400c0f0703200406a601703d0701e5085540d98400000341e001601c0c0c5029503461540c00070105000780a60003000c1200420242e0300e007041c6802c240b4001180d03000b14004e800c858001c0010300e96078004194000c1c3c0981c1c0e400c80d203103c00d2504400800315600030031120002010040c4030184460002c800741e13111007180000540b00c00c0c40c00d9840050031180c501e0050f20b80580c50010b1032041140800d4050003130710f1800300c99130540e00e240c92160422207000c0f8036071101d101c0808450f000030500a041c81283c010b50b2642c203164442e603176030040c5808070f50130401d480030b5136207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 627721591 1250 627720341 627720349
    0x307030605250914031902060a1b20030a0309060e0607060228020613170c060901050402010e01090f2c04030e04110f090f030f031201050315040c090506 67
    0xb014020000ca0605010030480c050702051490054211030a0006040c5025050004004c400440b5840607160400050707802c0040d26030245c4070500401002100f905100a49100c032652064821fa201c40c42005c011900c00340c2a6200c48100c0388240d0141c0b14080110f504090442e041c0ca50f01d01d0302c182c0a0140d90041010740c03003035040090015100240c10455514110381004006880d5002c1d1007098628000c1280d9983c0d0680e4054400e0000038150740016400001840714801800012410301d90f842c0d621a0074208115841205079440790108021583e020a100c04040001d013001c00009082c815a01d90368001400b60b00540300c1300741441c2178a4a082e03030380429840d41804101140386042c1c54010308519500d2100c2c1d00a0b414040f00c5541d40c0c4802007642c80100341d01704203604003030000c8108002409951282d503058041c2c9504040e9019040c001010481111a2544110751402c403e05190102c8405142c044010702c00c1030000050b6100400c1040f0f030300040002c0396a8440400007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 627722841 1250 627721591 627721621
    0x807021213030c080f0304090b040609050a0f060803030c04030b041401090807030f170a0b0111070f03050f070614130503030a030e060a0b031213120605090f0a020307030605 76
    0x14804004607603000040280d08120003580d1044800c420441c0e9a801c401c2c1c1e6903505400f0004203900280814001d000b0f10b43d1100c103015800400104065640d8102c03a000c0b82c0e0280d502c1c0ca080d640300c4c42c4103c007140107070040500800800004502d5880c0c05107103400b50307019500001788407408803c0401d050050a4005800c50341000000300a0f00b2914508481d0035445004100c001c20128010011058040c0c0d034114010000d15180701007e13543c9081800c020300c038001d003990501882c2d00e61000150b9040040c00050454030404000c10b03415818140c1c944102c4120854440d0b00c0700c082030107807982c0141030710024400b40409075240c10044040481c4284250000c5030940f0020540d003075072561580064000030340e03000c01c0ea03e0f1030301c94817168425981410304494056001c08111500150711a00410041c1d54811081012603181c0c0b5048030101c4400c0421b44040b515081404422041440848988406407008210b43d450035030209440c2c4c1c050f8031000d0645640c0d280010008500201e46c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 627724091 1250 627722841 627722863
    0x2030d140f03070e121b12011b09050f04110409020714060903030712090b060105030a0f0207060b090907030f0807030c02041d010605030d090e070306030804060e030607050415080702 80
    0x1a880e0f1034810001014080502c1e4140e02c00c0b81c0c0f10b44641c014400210b000b8400c10131108420065016150521040315541700c0070401c0c940d40c40b84030b0341d64148541684c40700c00c101c695840c0d0b003041c40e190421420502c2d0713201076442686040820382040d1601800c51301150040d8001503191b00c030301d00744003946501d016101001030098104016407444040000e503c00d04841d10b5990b080f50b10f184500c003c03581c14040081c20b2204460104809602400c05140d0011440a01040c008482348c0a00d0503600229130484040f9100c001742145440c010400a0707011001c80014202a440d42e100d604a100f9054009401000001002c0c1c05061042c514912031940103002403040d40c4c0402040e00560000c500b07414203551170440d012680303140105612911010f540c0c1c0709420310341041003408003400090b050400b4517546580001c001a034600140000700040e480e80c1032a9603190051504000d001001002000010001400428000030402c140325201d0300e0483c400e503540100c20f91421f00c821003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 627725341 1250 627724091 627724117
    0x316050f06010b070213020705030a0804080d0c02060a0608061017010b0d0b0a0e0706120e0c12030c0105010504090c09151701020408152a130b1b070302030d14 70
    0x70803c07a0b9000010a0081e1003600c142101d003248071030f440c049004000000300306400410240d5401440341405030b801070300410280d4542941d45031000c0403101b007941440b000d41c001404000306a4014402c92000740b45032f8026080a141c95a140c600f40041ca00480e50459100244001107580952000c4030b000c80150800f45001d1003402c080300091000c84c0c030810300f50305000200041150100e9040110703959500c1c1c0704403000c400303400d11014000640d0082024850007000100d03d6840c06581c03101c0c48401310145640306d00d06580c250960307105030400c0d13003d20b0070001c0c1000001c80c500119011150101400118141b00020400c24241d8036030000310125580110040e88a03819401401155810401c451040c2026890300e4417090741103490101c000718040851903212001c840c00c0410100044a440c40c00d040320003001030700c034101e4104100481000c20042580200c0301b10f0901148001e400601a10303181d60b00281c0e90f13000020189080003203061050900b521000c0940711401c00c0d8207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 627726591 1250 627725341 627725353
    0xa06030906110a020d180305010c2c0303030601030b030f03030c030f0709050901090f021b0d12060b1801020a050a0506011a070c21060911010e01170708220b040b0a0c020316050f 78
    0x100b001032107071803402202e5a403034900007440c0e101a0360bc80200581040080c015508542e109801074004000580700e607501400b81c0241c25400c414148001e6106824502e0403a45a003443d11840601000007440e000c02d005184e8018000f581d10018040d045901c207020215540b01d0700f0000c0006402203881c03c1c0b0075034001e060340b5209110082040f20002c0c0c0942c2c1c803e4a07203540004450251550340c850482e001c3c404100c0c02e00b15041416041c14080d0303040c01210442d0a03595210342c5040d002c1c0105591076040200140a28003000d203030301c5050384d504210704e810f10708552076a4507108082d2041c1c0c88860369101c28a416034040e55100b40905812040c1009400450708201040d0312581250600003080ca04040ca00f6601070050704c004108001100d0b106aa100d4000340e8400c000030305601001c81c00240c07501621a0f1020428164910a1640500d241000d00c0c101d40c4654000e00108012070400c600110500d50010540d480c0e100d201007030304000c0c640c60500908047d0020302440b0035014407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 627727841 1250 627726591 627726611
    0x72009070e13110403060e01090b0c0418090b0609040303180c0e06040203070903031d0915090c03090c0918010507110d0f0c020d110a06030906110a020d18030501 71
    0xc140409034070030094400780d011860442801e02150790a100f01c00c04800140405e102190b200d504c22408400b1102c00000c441216458808a202003140c612002d103000203018408903500c0c5c110034041034407100c018454290650346400140400031b22250140000e000010b09143c401e070412079020310000c0400090010a080070300d407002081c06050591031011000c90210302b4103100712403003207006554008245041d070b60111010360349540301001c900f00d017404100071541c0ba030051a0082007540f001c19106410501800700c4000f006180b45410b030418000c21100280200d248211517404480c02150340d611403000242400500c603003104036610302010000041d03000402c0fa100850321408072a411424100200c4440410001c04030004000c5071450740141000c40002071040c1c070902c03401901c118130102041c110b884c103902080000740c54540107410f03c29207210750421144000070701e038548204100003a548420382a0b0740001c205900c0402c8505002580446010355489002807040a141c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 627729091 1250 627727841 627727847
    0x1503070e0102060906060a06051b072315090d0303061502010e0f07052b17041d010b0304030c2102071701092d0b0c070b0f04030507200907 61
    0x4a1060030780540310700c1000c10300d1140002503540c451100202594100c1e814008200c6107600311909505485400ca61041c092000c14000384000e0800b080707948641079030030207810500b0440002ca090086808010702c2038681480c400300e0344003501c269802504100686800c90007070443c0c3d4441c103621340e951500c00700c666506402042c90004c0e00412a170a6030a61005292179540610405a125041002041c105600c202d03640710401d034180750480c405c6e051910340e03007503c80303c02c85125131600c000501842228040c4007110208513100100d4443c660400003482c1c9584806440074050040d090000c4040108540080030240c140140220043e05003170f102175562003c50040b07100000c0181800701950300144240c1188541250220350004450501c7c02c8105107000c10703032410207141c003000b1400314031040000740c0541a1014440e5a4003454100f03d03179240ca01405030500032a242d02030101182d8003e090f6140c503500503840003004941d20b0030b405480030907130540d6908010000200130703960350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 627730341 1250 627729091 627729107
    0x21204020a0e01062f06040506040b0702010b030a0b06030a0c0e01050a050d02010806041a030724050403030504030605100e0a05040605060405011a0c1e030403030909150311150307 79
    0x8801d0350800451a25480b0304414107009001c0c2d00300064160321000340c0c0301c58051208499140040d4407415660280c504070f0304041040710207891035401032081c4800c10402c01d061356032140082c402040180c5110001070385888156001510580100700840e01c80c5c0e80c00d00180126642c070088003c074165560407402c0e84610b0900c1000e00c200c1c0444c0d0005580d0070f2048840d0801da41c140c2d1382d440903a6640c801c02000b414503030540090440e4007003140c07140d62130030044100a0109680400b407002106658040300110048102c010064240000c00c00203810bd42030b2001e60390301600c0491903590301500c01402045942c402c20000c01048113210130b10002d588000e00407170048000313000d2a9a08420b10099030b4003071280002c544242820a51040030200190942c001000d00740d41d900c0c0400701d414507101c1310340c400d0100b9a4100107002c10030903810200310030090a450a0902550700100c500c420714a1a9100c05481f42e5100c000301d061940d1030a030194040d102d0440c042c0e4480c01c003482c00502040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 627731591 1250 627730341 627730343
    0xc07050910060809070b120901060504021b0c03030403051e10060608192a050f0d061d090705090a090c03050303010603060b03010806131506080d120c080a0209010909021204 76
    0x6000c51000c03410030710300801d021040e10302c07480701d1907e40b85c40249540e1580d0780c010300c3d10099542e60322000c00c072966a400101401c18105107034282c178a101da60100e0800c12202103141c4250310800c010000a000840c031814070301081089c0d81079040c0d0900b401c1d400c0158450703c20f003809180004c003091817504440201c1c0242020044440e40041540c03881c401c8495040e08003010f0240040c03085200302c40c4ca5020f03100940e40b880e2050420003140c4025a0030b400c00d80d19007448e05c1d203800e42402491078054142c2c102c0c282d01c2d02c007411281400714025845503d24055030b40288440c07000a001e040fa01d400411107660b00888444a8076540d00f0a19180d4000380103510000f03003803c3c1c0010b020209401600d068030000b0015021a8130b8548003130680d1032941404407038500800034140d080b03154a220b204010801c3c103018204540724040c000b00511180c40c9003802d070f03d1900c05506031460b17014070100c5d40000401d00059440f202100107842002c083d80c09191001c1c00000c0c0c140f010081d00040500403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 627732841 1250 627731591 627731597
    0x405040201090f1806052e091d0a0c05030705090f0d12030c020601120201020705060d1b05041a0c0c10050f0c1e0729071401091103061b0c0705091006 66
    0x40303501d1b1000c000140100c50410110264120300080f0103407140e10340b0032a8070516003841664281d03121f0b051a03000c0d0040002d000603036290b400b00300e05980307a0b00900984c0320442c5001e615514014002924600580406a000e0801c0c07280400381610f5048259088681000c1240000d11081c440100030b0105000104014060b4200006410000c0c2d94003004056058003d465001d040000b4070000e500100d025941e40c40d1208001d040f00300b141d01c0394110000c09556041c2d9124181b134040c03010b1500340c0310500f90140c2c003080b864004110100d50610800c004403a4540c070710500d80d200300d50601881501004100002500d030a5840001078660281d94042407a0200620150b14041d10358081d84900308000d096900080080c528900001041e11040803081341450f01513104e00c046203440060003990f40e036440c8107601c20301c22484c0f50303007a03031480441c02040d00c1d2074006800341c0304070344021b080645c02d800818034881c0224180710060103843e010300010384a00c0e2091140c40002218450034000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 627734091 1250 627732841 627732851
    0x112230a061407210b190f06051801050d14100303020717251805011e030201091505090405090a0c090e0325060906020d1103040506060405040201090f18 67
    0x2100d00450505407041183c1d45443e11a0030701035545818544181106066140d51003940810030b1b03503011082011351400d80b41c040c45250900c0340a44040c0095001442031007014008040030281044046410901c20310b0320b291641103425040d009010707107507003038040482849c007044a80c00412040b00101c9001303070f0895690903580c1040034012840d400d0018002e40000d00b02c4403140038a0230140701a11450120a07695654a10103800c1407482c00e0152a1101e442e20f004124503100b404603084492500000f0030180c0d85598000390841010707204210708000c0903140508800e0150b82075075611100a00280024903041d03130995211030085000302c03800d41c0700000c081030004891103100345000748040103602d80812a00c208104154044441c1c0140012080030400140c09024240300148a42d001503118428110341805036494600c50075102d100900030070011910009000d40c1201003690000b640341c40c1d900049031406242e4001016000700c400c000980800c102c5101406003a0030f0f03c1c1000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 627735341 1250 627734091 627734111
    0x3140c010311070f030207080109060b100f0c15230a0e1522060f06030309051008010515090603040807021017070810080a110405010b0f030112230a06 66
    0x7046074100e204580800304240080c400043c0712900b410030080c041c2c0105c81c000d5542c0c42d0040e0130340e82042401c5406540b1607444111030704102d1014080ca52990038540351250f040c1c0300c002c1c40c9907060100074002402c14001350a10310510351000f1640218101e42d00340030603035015a224201d80c01e0b29284100c61620119034017110b00070074034031003407021500c80702440c1c2c5481e2000341e84032080c54540141041c0c40c24110002034064811140803407081c0d0070108182c0d285007405803c200c901d600040c05540c025503000f0880d075010488034152281103034000103806031914480e2141c000d140000d50042400014002031000b058007808050f0f2003140c1905a460004000721026818812140d03510b400042c0071070b5204d402440803d50000c10010402a11a07450f5042864819805c80540780042880440d0b00142084c0c05028050003106503a2490490302c05980340c2140300501c51141410314281040d01003007442c80120003c400b01e013809250340b1040074402500c0383c01403030b0212201f5150100380e035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 627736591 1250 627735341 627735347
    0x604050601290306060d020703030e1c1710030209040507141009060804030309061a01120203060a03020111010209031e0d0c0203060c0703030b0306070c0302060112151a0a03140c01 79
    0x2031500c214495000b1040c1003002903654030b4102514140d800481806030000a6809101803c840d40c020323034000c9540308951b03c116003400100385031940d540780503020000045400131281044406280101c2d12b00b95200400980030320f5183e04001c0d803010102e0140014000000b40b106d068450128542e45054055001c012407045281c1082021131036910301085050300030005c403580302d03000c1d0a0200d41c1c0507250b6220b004681c076030707031611002040d80f9449000a5a0141280d41c42c030100741c004626500300580014013010035844000e04000c01ca05000b5440d00c4d0a4040da503500001404a850100c564170b60f00072440501421003585d48113001f002d420b40751041c16041c0807281c0240240101c0d850b00e800c143d405d984482c9003078003419110600c110042d1003c0140e144652041da80381ea90004141c50000d04245e010780c000321594982e0307c0c524000c00c0065101d0345400da089170300060a0b50070030341c0c0ca2103a840000706081c0e106140d85e0002050181850f0a0a103041d10b03031003912180a00c0d0304c015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 627737841 1250 627736591 627736619
    0x61309030206040206071103151501050702030601030f0f0501020d020307120c092619020a06021506190b0711090108011406060c0a0b09033a0b01030b10020604050601 73
    0x140050b848880440d0242c00c10b6002807081c1c9000c3d200b10030303c0c401c0003400b00346402d1010300000706003c144c2080004240c48036200b02440c5c0c80920f8050325104180d00000d640e040c040c04068803407130706c40c4044001c00000d20901f0b03450a50040c002d64490600c02c01420007500115100030200345200d01d030300d01c2840f84d4490005140d01c2500c40100b4207051441081c070103111400c244407454240130032a20b15003010002940c082441e600c0e54081100d00c0d2060240407042940101c0641d40180321606500c8840ba401580c0841c2c140d400c00c41d0f407100104c0418104100303a224600c51180041c460b010b0183c074420b0f01e0707244030003a00c1c521000d99072200302e142200e8181152500036856030300494424034141c1c00610300741c1964401c5819500320368452110440b400d0702d0034402c541c0300103901c502c4070400b1007000e815160b040404444071801c8564025010700300e500a41103c644d1084183c28580c00f030783c010311142d038000d400c9000701501c03007501030340d922005d440c10384c1d45219981c0002a184012962 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 627739091 1250 627737841 627737843
    0x30c05180c0a08060118180b030a030f030b060904090807030216080309010513030b0f010f0801060b12070c1b03111912150519050f04111c020d0506061309 68
    0x800380c40c003010b000044a180c0000340680d810031070300c407544c80038903501002d10702c02400954440d16a15094003c0f00c2c411107020483c840e00030740003410f100010070b4010042000101e82800d020400c0007051002440741d10540e17540c1c0344c2c05850300442906010b804005000402d02c241c089843c480c4800d404140b0070301146c4544043da50007080030303400552040014140b0240320300ba0592b2000e860343d40e071000d0301301e00312601006060381c130004010300a201041c0300e00070050310000304000c9061004115841c441c50900f011303139256103408a0f0240d031007140c400e605143c104403020880e4002d002c005a0300d005512041d6601d60180011201c245800d984080091015540240b4650f00c0d10301c0085141c40c1942c8103480c1042d88d07040c984101c091902816114450352402c1214244d41c88251104545001d0065405241d0100810000a20300c91100c45411402c81d1682644441c5d82011900703a89040380081d0400e60b03140a0004210000a03054010b000c2281c00e06040c4543c003508504507001000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 627740341 1250 627739091 627739111
    0x6140109031115040b031f0b0c031602180405010f0b030c0604150504170d0306090504150e0c1c05011808180a26061807150509030601030c0518 63
    0x2040c0340b5501c0c012440c0c0c400c010710500c625062966941d6018801d8100312032640c00241310480c030704000560703409604042d1056031201410414911600c41e900d0003003c40d07042198076684183d005650b00c007021501683c005084154191600d4501940605000c00000408a0800d494184036142c00b041c80645410080c05c11800c083c0307003800c5014100f03000c0006d28140101000301041e048c07608204c03076032003071400001050340044011006007107850b0f0354000d4041c2c43c0340c20140400a9903080b049082030076004004503182900300d07100ca080001000c00d1a520004607030941c0301035015195801c00e5140644000c0040c0061102102800203c2042c014043c080130030030f0081c41c2000d210700c0842c200d009802d0003019a15040044985080d0a019808907d40c0000050303a007402005502e600800030807200546060b440d040c55907512550140c498450302d14490006164802c2e0140e80044200404540165070f50741401240380c2ea41d03001c3c90380200d0302d00004442c510031a030000350040640392 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 627741591 1250 627740341 627740363
    0x40c030f0f0603170a1107030b010806010b090105090f03010b0301090605040501050c0a0203031909121e03060f09022d040819150b010c02031b09010504090b0103080d060e01090614010903 82
    0x150b5804c000e540602d5a00080c0300040c214030810744410081840910322900200340c1c2541000100340c5040c50507409100141010003074070015907880000e46000c480300351000d102d1550b05200080c003502d208200c81d600b540ca482806814401c4540006001d140a040200440d0300c5174500440f20b8440c40000e5005a0320030000316069030718204101c000c070705d140200002c111085a941450000c4050200000501c0d500f904941c411410158845040168142041040d28000b151040c50503e4030424030115804200c014291607510000d109940892121018112091103055015000b501030041188240e510703964642e944080c2014600360070441012456400045080c007038802902042d0401c016001d01c400183c8040142c2000030350071204541510240a080c0101c03028146d100341e202d18180080b6a002c210004c240e0380c19603401041081d6600c1c0c90100c0440544510707440000c801c018000001081c004d41d902260039202c020081b03240220038007004692aa016000c0505260002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 627742841 1250 627741591 627741623
    0x315131a0103170f0d0c051b070e011e0f0b1b0d0e0402161703090c090c030708060d0c03200402090a0905070c050a0b2217070c05040c030f0f0603 64
    0x20701130702041e00502e14081c684200405580c0a079154400d185002c50070100e104005140030300c0c9062030fa101e10390001c3c00043e00d4074062100044061040460f182520080c41060340070507216040079140d4441c40d00709107542c807101004181d00010520b031080201109401313805601184084001015941c1c908540c00030904003c020360200032a4042420159200c2c800103c01034809002d800050815588918000f00d4060070402c0751031a0912172104001045040b0341c040090f603800152620b00701c80950b4600010520880b00e94102400c1c003010311a0010800040c1542480741d44281400542c03a100c00b80305000690080c3c00c2c02c1984500b191b60240840d2805600096106d2141d00e00041c54a03401e885840c07c0000c00c50055840180d0401040902000c0c002c00c0d80e010342c80701c50740203018500c60704c44514081c40b4032032049042c1000201e010501c215084180301512005004010101c401d402c041d0040036001600345420781081d83c4601d1100c03c905c2018102c035008140e910010540d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 627744091 1250 627742841 627742883
    0x414100e1c05060408311a3a0b1807030b060c06100506041d0604020d0e0f0706020c13050c040510120b030d020d050d020c06010e0405010b030610050105090315131a0103 74
    0x1000c80319000c0e40344c0c103000001031250500000030030520503095082d017111160030799000d070041d00c480051481d03040119409c4107031503034020345100b02404820400c0c0c0d9190782e0002c8000e400481e01e240d6100c1808607c101703a4400120791680511000c00d001c8140a5581c030900400e07014910a84015550702824041e28a80d03074840e06070300c818010001031a019890148500b100d2907941a641e0540c4030b03010f1803d4190041084e200506003500040141c001c002001500c1504142c040b082825114400310301c45d03803100002d5401820380240303452a00b0f25403400003403200b131039502e08002040c149214540c40e400c000c600101013106581c007408041c8078030032059403958020301080c00c419034208804d0704110000c1c41454007a1000780c4003998181010700f40b0b07d0a54146030300c0302e0b200340c010109012003070300c4250310030040724801c1c00d000b601c805000c0000303820176066111b005241001742d02042410405e0f03042c01e803075081c032640c81c402c2c0f1280000b141c00301c1c03401d0901005242c948481c01000040384 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 627745341 1250 627744091 627744119
    0x904020c1c1101060e040f02060d0b09150102061f0b0c0f010f0209091503060a0b01260618010f0506031b0f0414100e1c0506040831 58
    0x409000c03605880104a000c92004104105030780000d401012044801c202c280076000c010180246243c075681810748a00e40d44461440c0001e00c600c900107801a14507500750051a20400024188600e5282c15a420940d54000d520564014060fa000290008810b0880c45900e02000752404102c01d083c42d20744002a0700c0307900b1002040c40355986c80c41c0800400d025141c40c20b9005800561240081002d12101e010301901e001040004030103501ca1940380042e200303910084000e40400c1c80450800181d40041055584114003a080100f18010200c80583c5600608d400da80381983c0d180300480100d10020300380940340d1800c80300c580c108460300d4020003540d08640c4000c1c07034002105040c440b2030201c1e07100c9618500ca0000c082010006d90441810901000c03205481041300e040d96140c00925108500c500c241c4203005000d03c2000a0602c5014030202d5503000c170072108142050b003000a1242c02454031008015008120344003007944410a80304950b00c2c1d4035902c0c1010f82405401e0380360f04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 627746591 1250 627745341 627745357
    0x41a0601020106050a03050d1e020c0f040b0d0606050f040c0827070602070801060b0c06060409032006091002122206020a1d01050f180303040308030106020607020c030a0206090402 79
    0x2648843c0040340c10f90f12001081c1c02140303d00020700e09141c5101d80a40900c80740c260b064180c80c000c18101d101e042d000300340b00081c07510849230081e0850384e03840000c000300507401d05c890b00185001e0007601000082e602c20f00c1a90350460314200004000c03c01c21041e1140200c5030400107101c203000c501c025030003400d481c120b8a88505103050451a070308903e4680520799001d00c0040e80102070030400700a01780b0503980035201c0841d80c0303840c003e04104640e55a000191016024941c0d03090038806061103885260f039000c40040c0702c41081007107003000542d911400d0303d8103021401030407074156444609208552204000291400e0680ea441070041d510340d50340d9001d44070703080f0711078001c40000e4070301c0c402400803648640f81c484e9090b41c4001015444a0740c2c09009052020401000d0290080c0c0006da032480c030400107002c040b03a96080046400c60040307a2004007510030100010035078a40100e07880380700b0982e6500f2141c0d900719400070150703244150000030750000002c11a0500d9801d183d0003c003040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 627747841 1250 627746591 627746593
    0x4060c0b1e0405160503060f041202071e0806150906010c0f120c0b0f0108060c0702012114090105070906110c09071e050f0d0e12030705120708041a060102 68
    0x441c510070600c02a801007224100c07215004001103942c45060080c40710090801900182110302d421403c00180b110080c1010300404010a12090558400c0051382c2c080c10203803112490310140c3c03400c0301004c0e804d140107050450244100245400300360701d83d4052440c030003c003000800d4880000540310a440c445090712440c22075280c0e0000710b407000224400c00347c0160b490404009060802c0d40d40944040d2130260100f040100400880e040011790513085142c542200d603440149200580710201c0d18560980f9103620b080b40c0400100143c0e200c4a220341001c1446401c41d03a40c0b000140c00c81300100e900001050f002a4280011403140820b0000f00c1c50394001c46240001000002c0d00806044600b407000038540700300300459048003100508640c031181489401e100f12a08489242d0048820010805580d0304200c4050300301044085085020f841900750340c2d050440005142e07a01046800c0450031201c80490382d0984543c4000b0311031600009014601c4407170300a481608a0090065411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 627749091 1250 627747841 627747871
    0x9021513030b0c07030f0809070302090c0409050a06091805030406030203060a180f0e01020a1403041b1509050d0b040b06130227041e0c2309090a0204060c0b 69
    0xc0314081c031240904240d140c1e0300d84401e06403900821210786e40d09800200000301c021310985003000100360381501c0e070445031010300d0b90790104242c10500451b8007100905040a0034030140c0480da51144007524250038060148448018140750704041c06800189654420001005614420703401341d40c01010090030f5008090380e410110b01103c6140e18400341040e03640011a44500c0c09210b4112410190b80081d824030410500c0a8508600e944030401c40c5180040000c040202c01155001078030268212440703025102d00c0c500f40b1201000c60360b0004610f0421012400c2c0c5010801040c000e94004140002a03540f640e520191000c094002a00702005c1800031080d003401340040c040c0c05070010031003811010445443c1144050240a042c06946007011418140a50500d41c50381d40014000100d90000c0b0000304442040d0300d221850404400e40c00e07402c02011815000b860740c1601120fa000d01900d9030030421040344258400c071300c08100640c101500203410000c40d10342c07100c0d2a50003614 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 627750341 1250 627749091 627749093
    0x6030c08121b0c0d2001081b0f0c010c18122d171206041a01050f070c18050f09030301060e0105040812030103170c03090409051908031005040902151303 67
    0xc2c0c001c040d20805c450f60300751080911076032121800040100a03092910b80b21508001e00810001c6020943c0c51806c803071700103001c003200d0500748100c54020340b85000070064a580a80024040400e20300f009940305680000000d40c450441d0b40021036580084100594000c0c80d0138403c03803601daa04071104920140c4011750f0101d101048910035404403281400e0799042c80002ba2a060b6000070103080c451890300c468141140c480781c914041c0e1090a0030000d940d1040318030348540b0b80c043e510004140812941d80850000301845000c070443d21790038000e0189840f94078414046180c1100c0032909a40107000400401d440342004070380681c418113101e46019210400350781040d003104210206604004010001c1000b81841c280050160110050500541c0102075883e84203c2042c24415501c46808500380541480510b0030701d0900785400d10030b00243d140c4085603800c00c96044041d80104040050a81480c0c064803460550050402c01c2349260950880d2030782e00701006443c02e0000e6004044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 627751591 1250 627750341 627750349
    0x9080a08071709030a0207080111070b0c040306020403050307060e03030403140a120e010516020706020706140d1a0301050703090203070e07090b070c0e07050a0c060c031e06030c08121b0c 82
    0x43c0102c21420280d541d03180101d2020b49001200d60010509a142071500c429180c03034941070f2914182d1103014860107031079151230345c4641d0180f908042c0c54107200040001c01c0100010041000d0741c402c20b0248a081c1082c489076441e404200c4000e008039841903c16076680f0082001400603110383e040541b0f0783c09409403442d080b01d407000d03006502e582d5280f0620017140030010191180381020310041c080e090504400035142c10742c80c0724640522a25001c403058150b0000161060020710a40c204404059800f107000c041300c0c80f41c84103019501c2d0201090a186c030a000e081c4a140c0c01800400c001c070718002c802c4283c000010301100400101c0c0002003601c908140007405818000c07400d0600e254101812100d8102c0c003c1e002c11706020040003882c503c036410a10394030b04540c11001c00242c00540364020340c0542000807480e12100ea0048030b00e1f503004102c7c1d1050782924012404503143d2601d61011650390012000c3e00b10405405200311154409048a0b1403285500001235402605a0801007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 627752841 1250 627751591 627751637
    0x50307020409050313091a040c120c020a120305040311160302150c01050f100f0501080106030218041d01050c0408150411060a0c1a0105060d020706091a0402010f0309080a0807 77
    0x1084810380c0781c5200c1081501f1900304079141c500f0071182007100301082c12014103042065140f0010f5581c0341d113410900c06000780803c0c0d0000e0b82008260103000c610003001002400111412404101489101d450b5800002802059270180d203900721100350450b003c02c03000e9165030541603c2000b080105030307443d0000b0302826000301020b4149207940e0402811080c42c03040d9035000b00243c2041e0710750402c035030380c0d2188007503044818a080051795010b50740d200c0d2a203500c446100c0c98000d42014882045034240b022121580350070b9030700030069034980000e25006481148103441803075011802d0104a060410603071600030381704541c100d43c880400d1010034039942040c1400404a450f50603103c06020b003118138882e1014101095004640c1020300044060040150710010030358041070303401c04c100361035001a4409421031600d0446001c00f4584030711070b050889089001550070314a01005030300a00404018607809400d882c00e080c0125003c0f690650014051401c00030541d00110300c2e2102c5082c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 627754091 1250 627752841 627752849
    0x2e1b050f0f130509070f020c1201150f0602010f06050d17250303141b0c120c0c010e0901030305031906091a0a0519030b060f0a0b09040f020403050307020409050313 72
    0xc08018602c0e2104008460030000d10356001e2200801c031b00b040242c2d000c1400201d2507812110313610b81800c1030a9440c014040b44c1c0c09141405081400070405840c0c4040a00441d90b15030300a2190443c80750701241035030518424607401800c0450020001002904000d8506001445170303803c00e03048081d1105111004007100060324a010511000c0c560700d402800c000080c540f1642d0814242a580307000d0486000580b281d03444000b00f6440d0000000740310042e4013203040468262910450b8010940341e0088580e4180800c50362840d1a4182c2404501c00d0704982e019140c5500f1680c6480c2d09440070341d076801c00030060b50750b1040f000c03e40c0da00510800c1a0111404019415040c4580030300c10351541d95042144130ba0340301c49111032010303100c0c00c400f001c0d681e001d02e03510507a031115404160b914800321207a0790f002d0039084010031000e90160161a013034a08450604c80d08001c120428101d1099000c0504035401c01c10048001d400c1c950000840302d8402c01c201c92810711310300c8090b1048085a04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 627755341 1250 627754091 627754117
    0x215060d0f020a090f1503051c0306050a0806010e010f06051b0a080319140105100e041104060f090b07081b0a06050c071103010b0622082e1b050f0f 65
    0x3a0b100a00c202c61322a10b06c9070000028080c440c1c9003941c64043e45c82a040c0240c81441030f011040b82520361080e00140c3c000c00300945080201902c41030115200e040034060001e10301c0e00348000291056030069103008072000b649907640f40c07481d40594010030b42c0b4490b405240c0e0b0b101e40d0f8034841c0043c03806801076114519101d11920540000c1701c00006940420110f01941c0310402c0c014005940d80329103005840055040c0343c280c0900b4031f404540940814a100454010042000a42c0c0c540000380d001a10038240d451030304094480c44503e000e400303141c0f40505601c00501144141202c100e6078210080c0440d01195585c1c40e16617120801c0c0c44044031401d6900c000071030300c20304104041c1003014043c5c41c200c000744161a55900807074a58061401c42090394005001c130800c04d00c500102041c042e200301c4041e5050401d007494848400e1070012540d10048079a4070244400f21180e00c1b8912180f0002d50000ba03480c2c1c00014100c0d0300d42c0101c3c90b08144040b0420402d03c5070795100000301401c3c103200c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 627756591 1250 627755341 627755351
    0xf0c091511120307020d140901110a060e0c090711210c0703060e0c0901142704032c090403030e0f1606080c030f0c0d0b040e15070215060d0f020a09 65
    0x2000f400c10542c840c0e410f091002c03510b0b03102a41f0740c1000641d00b1503a420302e007220030554038000281c5005021072010300b0892516045050400f00441c01207001c0109079900f140588400000300c4e00043d072182c3ca4030054011200e903810281c0450005140e00035180d5070241002141c200c4581082110361084411981d1a50f540240f01028049240d0404045905020b00c0d8542209010624100401c041c858614100ca800b861056100b504081040c541d220501c0d52501d460b0242040074440e441c0c4400040341a100110096071002c04000600702a00c05020340e01d8a0b40c0c01d03801b0304180c8400c01d1003406806100c0d40301202c00c21030a0710110305048001003035450241d01170114000981150308401040040015280440a50980180b80310094551300c5400f404081c004250740030004c0e40c00b50030308400b144000c4000485d100c5210912500c09810b46800c07078141d9852400300303100c01c88220340c5400074003a8681003034141d01440c0500da03010000c0b1a01d0707001a04c0d001c0543c03c40104aaa58 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 627757841 1250 627756591 627756601
    0x3020415051203130b0a03090b13060b06160b070e030d0c0605060d020105040b0f040506030405150601020c101b0c260d1407030e03071502010f0c0915111203 69
    0x401000001c03010100c06186021300d0041c10761016022801000b600d800001a0485c5891003030344000c075101d42000e407000c09403c03c0f01e14100340582c580420381d0700c5820030102c4041403506404413601c06110049901031249240d4441308039000040c0740000303110004505c920030f51420701c0402c0da00312090340c2c1c2610801e641d2a040c4201d91002d00760358080c1442c1c140d041c1c0140d07040002c80d8191000746d1000364881c215030944071a64400e5801c860307049a0040184410071200141d180c10a40948c92001d040d40e40f1f102c012a43c440282070f6071540102da000c0d15440e001d001e00754402814803514030751400c0380e080e500d4114600308168010400e143e82c42c075014a00c00d6401e516090509000750250905290790740340109010050790348101070000c00145d0303004040c0a070405081800740a000e5a030626900c0160f000d09071004201ca40155003001131401c042c008074888d80c59007501a4507403d0032642401405410b4269880d40c81060042c1c00860407100d030380c1000f00c0c1061101c11145a41c0c2e1f481c1c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 627759091 1250 627757841 627757849
    0x10203091014010b09062203030e0315151306030f030203070b010f03050d080a090c0308130504060f03240f05070f2f2103070306170a0204090c0302041505 68
    0x8a0109007240842c11005101c2645030030308440204808030b911680f500080e407001c41044175041000c0c0031421380c0002c00005c25822009141d40b0b100700f18107036001589601e00042421000300d4403d6054186090850101c0c40c100c0d03c0301510758107034280020340300d4032075698441039440d45100350003607880440c4807030401002061450140c06203501d2406507a1640e601c0950721302240c0e0145084c02030f1080082d820ba074a90740195282c58120000e0f0215940c1c03401c1007400769108400309844008522404505801c182c043e00d0215626503681c110301c02d03d0f42d1079054440041091291000502e83d0807002100e05601a08103e4546820f00207500d00344000050015001d2540e0301d000d0043c94907a030034288030815510072102204410300440108540280f60601c040c081c0720080ca000782c0030f00c1e054850000d038040c0d44100301603282003000744d0303c603400c03161079034044d120a407010340c02142c2d07860060a02d504440c442c1d80c4913416441900383c403540058151041c109180450840c0c44104003e5860 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 627760341 1250 627759091 627759101
    0xb071a07050f07032a0c03030809010204062016031121031e1603021507030b0a0b0a0306260105221407030803090304090c05190806040b030102030910 66
    0x4098140a4941140c2c0c0d44911680d006241015043c440f14040768103a01e45012000b05030719440080d61034a40c121450300071201c0c80140000c1e00083c5a920000c0c2070010140700311000d9540b580c64150080c1c1e40c50810240c414003483c0307000b119014440518600a0100b82c1000c060f40c0b00e00c01c914899001303002404001c440700d461209240c16240501da02c13940001c0200e503800000d04112440d5042c40540301c40c00c13480f43d40d400813403011110b2100414940d011915103071100101440030104d4440c1d16044058134491584c42d98000d44c805820041990264010140040f00382404618a0756a100908042c8031020303510306490614007180c9801e240a10401d98820030a2201300d0306000501e00c21031040458010090a0541024244000781c0741000312000541d8050b481e0740d070300d15000b00956161f4010340f00b40041c16041500035a103060068058620100c0c156078107a032480c144000880351070034003811081d00700d50769900500c843c1e102030000718807500c00440140a01c07014a100b48040b16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 627761591 1250 627760341 627760351
    0x16140108060616030e130218090108120a020c0d0c03060b010c080f16020301020a111002030702031218011b091220060d0504030c020a08010b09010306150b071a 70
    0x30090341001440e0b507540b002d40302d89002e289042403410807a80341c241c1e0b10805d54010282e0003440c4503d590300c1e00b12140c00074080c07246503144d600b890030b001c0703406c0c812056403e016140c070700c0d004554080500c00c96980a0076544440344101ca8440c0300c480013007204907003000700c25540e075800b02c241401805600e000d6208118000e107001d08048259132181c2c00d4030f0007114203111200d03000262a0609850aa59106840b90001c000710740d107800c0c201c7d000d000a100b0722821160f601401030a000d0032080c910070340e44100d5198000d9450034500322136005580100514038030503c0c1d000d032010024207070244150340f2070100301001c05000d070703000c440090240c85a82c3e001c0a4640000c0d0700000011b1a020356140c0403a4030900d4020b102e2401c1000600b06000d00a1810b008600d0482040701b403583c01362004416500a465000d10350f626544094260b984405074940c010a8400041000a04c503a004075031410805040696060701c1d413001d05408d610071007003540d04800b600d01d9000c0b080d000301e100d95000707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 627762841 1250 627761591 627761597
    0x130f03120c08040507171203190606020316110d350c370305030f150d12030e121b01020307020601170703020a082505010909150503161401 61
    0x15140541c1c841da0340764064011039102c070b6150386030401b04840800032480d0781300c03203247e0f926142c1c03500c481e07150275050700600b4100529052080c0050410300220890780b91034110074010604881c6a102c5596115100004a0b000b205490084011032140300c00e0f60800080c0b140014008400e491202d441d4008170031300321494034020801040d2007000040c40c404419100400400200b0f40c44a500c01e43c0d80b0350821748440ca83c0410082410158000003c511030715801c4500320b0251030700300404c0c0c02080f00115031900300d1302c01039003540401c0421450035258440e81c0340200d566540c01c450681040608001e4101c0c91101080e003800f5190700e034030901d4000349860000c60451601902c020f540300c2d418401c80034a40816600e01422000602c0740c40061074002d882c07004015902c006240d0350b040180180c007243c250142071010012251413400301142e50507500c03003401a0405e0004001040e000c01d1480c040d000302c02d40010161000e0049104000712400c0781c448052600101a000d481a68829410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 627764091 1250 627762841 627762857
    0x90a0303060503120403031101150f0911031e09251802070503030f0c04030c0e06010305090a05030d0b041d0f060711060c070f1515050f03030f03130f03120c 69
    0x20703050b22502510206c07500361801104041035071810703900404034981d501175002480c00012500180481302081142c1c02c82d1020403800c00c4010202c0ca8901055a00c0910204104908182113944c0b00382260024460001c5d0303140f0642c0300c440c0f20350004440301488802c1d0142401000400e520585c00d0058140d0840c0940ca1302c40681d0f0b9142e00c0340b000404205c41c251030400402d220000c0707a4150b41c0956800815004103649940c4404d98401040320101c2c0060305107000140280300104481040c1d540c48401541001c0208402c03101401000d0485600207544003422489000e80c01d40200311014001c0281c000e40040450450400c50014020800c0c0504808280a00340c000641107500c04405070807941c8400341c03403a01120200305800054000c00000c5000d408900039503002103c18450311202e201e50f01e81c2e801c01e01489581034110254542c00c1408400302900034400190350001da603070600d80364503e250b90360403054a0794a00650004a40d04071f02c03240c01c0070074810800c842104c1d04044ca0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 627765341 1250 627764091 627764113
    0xa17012309090c01031d06091b0303090d11040b0d0c0503150919030c15050106030b030a02031b0402092101060e13061a101d06130e13060203090a0303060503 69
    0x941c43c00c40844207030400d0356031207260752120390702d1308204c1440c0c10807415030b03000f810071101c1140d84102c41500300a840664030601c04071854000201d0b41074a01c098001003035031080341c8903d07001e203184190694000391601740a100c46d41c2d4512111004c80e10550112031107600781010b05240c0721000d05021548440c14042c410b07400c4000803100b600090804c82502100902d150444601d024024020305907050600d4500c407031015a0031003410380d02540c1d0204845410601011340d5440c400d90065055004404a80d00051250098076409000608050328250b40e51012484c0142c05840c00d081540c808060740ea03444c5820300414004001030541c81c480c5050010301910400301d009001050295a4040d59444100b200c645040300700b4000c101c281003180d00d00015048a10741c05648102e1002c85901941500d006801e840380d59100e0b8240900960900998040f5002c001d07150703007240d1410100181c0014003034002544078001b040d0281070f81d008a40350240c29580e55411140c4203800512a01c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 627766591 1250 627765341 627765343
    0x10e1908030a0903020309040507201b0f03070b0c060f1b12040309090e030a030609110f0d0f020403031d091b070309120f1202030304020a06050a1701230909 69
    0x242c000744200310004560000d072600360319510070022030035040360900c41080011500b00212401d07201214000581c1d42a00280058603140210103112180c1c40d032950700c18850030329401807132010074003804445ca502d4a0382d29801f01500b010030702c0103040d40060100180c5982c00c0107950741002c00c151034504452103e11141240b402000750010701c03803820000040c145849000304200030131440504020880c603900010303071290b02100c0410082800c2c46070005034a10701d8441e544000c0e81040c001c0e424003401aa2600b89540015a103288198407644401280941e92000304015442511808400c10003d080711445112129042e88208850801c0142210400500c000800d600c1d4540e00c0d602c1e48145400e035484003c81e00200031050843c0f00c0301c1d081000001d00105400d01030010641c050503000790407a0340b0320088400a41111120001300202409140075103550a034a0405a203040300c5d03016410680c4100b41d00c048113070f41401c83c140d509600c074600c0da601600d1098540480314a0009402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 627767841 1250 627766591 627766597
    0x61c03120522060b030f06041707020d06020a05030627040b06190305061e0c070213060b0325030c090e0919032a12030b01050903030c010e1908 63
    0x8200c1e15040041c0c2403410121520740000079030901000101e0032410904002c12226094900070300c100700b402c40324410300203030003885180c0c07010744000141c4641c4c410b1680c5811502040303810101c48608140000c19034006001c3d401d04554a01b81c407031400c0d0042107602100c1440d400704403520880752400010b1f8a01c0711560180d0004414030381a16400c0200d50501c4a0b01040400c0100460b00403003007000c0407404030301170303040e0410a410703c0d5028100c169021100340d500625400c01048800d006050122030f03d46032100c0f00768001851580c8442c0400140e10860303407240110203409605010741d00a1038408156980e030320b001c0003104031540303010304441110b016a800d9900c4200009000020070091041c0c0082c1680846070000340614015184c1030740c540d00800d81e5800701c1100072200d2403111005842942066003e01e00722090041075008004017040141040800c000b51519900c00b08003c014006040d0300001d4818848002207003032030f412680314100e00c99244090004610f0341015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 627769091 1250 627767841 627767867
    0x31407050d0e010e0a120b010b2502010302160f0219080304181503030c060c0807050a0c050a080a0f1709071802120a0204050907020115062006040803061c03 69
    0x2002c000708050500603141110080107560340301c100200080b940580301034046d904184288505001e90740c03904002030300c40c0a41503900000170081c0c0054240b07440d8403020a02140c1c01810014949011014000a15400701c50700b51000607983c4104000c5050445000c86901100040d0030280390401e861140c0707d100f58810181107103d42920300121207803e6010501203440c414034000819681e00d40078042c007804040075101d4034642441250b0707035409030b40310740d2140307416a452030300d450101d1400b500c1c100c609078025030382c620030340c100b020004920b48010001c241c2180c4580108000b0410012f010795050b0190341c11114003042840038205001a40a0a4507818948114199018901103000740911951082070300c000d0001d11140c0000c0c2c0c1e005105840095a03041074640e10110240d09a505000c900700004944107130400285204580503e0404036000000303030343d5520508164030745101510180d661800000500c10740740340c0060108915242002e0b100104c05240d20301604005001903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 627770341 1250 627769091 627769097
    0xa0b19112a1b120d0207050a0b0304020303030103060905100905061801060b030c0a21140a1515050706050c03010630020a0c06180201141804090201020c090103050109031407050d 78
    0x52981940d81c1c800074143c49090081d021590940010b250003555040c02c1d00c00c140c000c403000d0702c0124400f0b12182c1200c3c42039402078011490360b460743d6200c00c010280580107403a240140c0781803040c1d00906000300c203480c0340078800509840c100390305407200368428034078043c5050780741c12003c00014006000341d035480704543d902c55840e080c8140c4155240003400914400700104440d0711a08044070b548200c0802101031010a040e6a440100d081141d0300800361512989403039204015029038002d03401903100407072801c1c0f414070030103565034400c0d10800e032a00000c00002000500440380d0019590b8581009180010f0490100d2940600080f003c104a6424540c00141024102c3c1c00b42e5030440c1c00c0d990181e4104078040741000002030781c0303214403000c07800500c0526031000b0b6001500141c41245004003064400441074a0400c0700401002e44120b042d409098804489541d8451249000354003a4002040320103084c500200004641c00d40c50b03d5036082031290001040000403824140c0081e42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 627771591 1250 627770341 627770383
    0x5040504050c0a2d211106040f0801140115050c0a02120102070606060305010f0504020c160e010608090a0b011e0e010f060e0d03020a0b19112a 63
    0x20910a0420340300b0b030310143d044112248001103d03401ca401c02d514807008145001c800e0205950156080c040300d01c80d001c100052a003850442d082d891107850049445002d84444140d07031440495516000b952040815160b907600c1080b00311003c1c005c1c1c0904106e5141d0b400351713641c10407580c40c0b20840ca8445440c1000380c045001e00d10300320704106041481c1e400030156503218000000d041e0107941f26400440f00142400400550203010780a01c0b4160340c1d4020000c441c85003414244002900100700315203041c0700380c4490f803115209040310f0001820030703910301c0581d079818180302410118018001c2070b032980c49070400d800803810240c00700e81034501079400b0302c000c1e40d459000804140c1d0355411070310920b280c60000046000c250f500f6082121615100d02020040300b404201a0600e200406000340c2c003c4c1c800800001c070581e01c596800b2501840c49200340701c14100c20b1044401c0041c40e46000c480014000c80781000090303506050f2414002c641d250340e000001c100c3d4450030840d44003078070440f0341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 627772841 1250 627771591 627771593
    0x1806070233040308151e10090303020d0f0512072d050712030207050f03040501091d0103030509120109060b0f060c0d030b03010e0a0b181b010f030b03060f07091e05040504 75
    0x52030360035140b10014030038844c0801b8110b16901d40300070300000380d101d06000d0307a00d041c0050240000d401180c2c1c05802a180440f65840e064a1b42c54440d082c090420904000c45040050346a20442c01082c10350788080300030070820144641411a251501a01d4401009408a103a802011560800e600951030900407104001c00e6010340620f090060250140302c202102495002024204980d000d0703035035080d440e581e843c850400d170358802d88080129404000520100740540c00502800c100501324032205000c50011908541020b001283e07810384921613041185007000001001d00b500711202e07850b281c151001107585480c2c0d08a0700081c141c071001c652060fa03500b94050b5081100f4003050b0380c560243d6107060000000110340b5841280001d00c0d224100c607500081c1c00c40c0d41004059007d46d1010021300544100640e05d00e44400c15444112211041d00e0500c00c1e01d0140c111202c540310f0a003011321300500901c1198104a0f85001c09900c040c45042840c40140f0441d03a058070700042540311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 627774091 1250 627772841 627772861
    0x2a03020f0f03150f1203030c0a21061d090a1407120812090307020a061803240501090b13090c1a0a1202071a1806070233040308 56
    0x61106000030304501000704500c182080301c001c60806012104152403a500d10100540384201c40f0811055034000d00004504404080041120302c8c8607041022074540340d01348ac0d1307000b810a4004030040d9519080e0410110035000380c5000301c61000c2c514100d03986408000d6036601c040d0410091310300c001c410720b104880402407107401c01038603002080385001407460034002070300d40c801e1444141c503855680004441940100c00d4030801030313004005a00b22882c9c000120b8415981c000084054001c0850002c0003820714041030105030074403103025910186420b0032408492050340040c03070950034901049400d6950300501c60401040c214006100901414807030b2070042d458000d45100e011013400040180305210141c105090700d80d80e00b000d04103004410310140e0082c400014408012541c0740b04440c040084020b034032001b034288201100004040b02131815100303480b40005a0010604460514010406184104075072030005168480a004c00c001847c002400a010480b0000101d591246 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 627775341 1250 627774091 627774097
    0x2010b103005100503060912040b0a0e041a101818110d050603061f030b040303020721020c0a0308120408070c14040b0f030703021207120c03062a03020f 67
    0xa2041c204024900d0000a1420b501c0414000e8510030b105440000e81c07100c5001505d01d0891102c48840b0303040c0351400b074280c4180c0d08401004001d210700c1a5014485880d5403151040d0018009001c02c0c80030301d070009101da81c9006135006400c21605060f105020364660952104480c40d03200c404030380504100c4184020080c2503064840c81d1000a0448130025094214a024007811419115152240f41380500001c000700f4500c200307141c41e1081000403850600500e507115001c0d0074003501e485540e550710000c001c000c0e200c800c6a42c1e440703c0c1024400da410042c2001c9503d00352203052002c0d0441e00d4000c08d5005035600d540101c03542c400000d0400c0724800503140c030305900c0030009103a15124140003400171848a0f4640c0642c0c60545031110302e00e04001d80a040050143c0500726150440c0c0034400040814a40c481d142d02c5081c00008400c074541c40515215030060b901000b003103045103018030955a40e9030200d01d130f0f4063320843e00040c4a24900c01110520241401039513501c02d4000900c444c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 627776591 1250 627775341 627775427
    0x3051e090a12021f20030a0f02060103150c033b011e0b0d0203060106030c030c140306011416050102040306050c07050d050c070b0406030c02070501030216060f020c061602010b10 78
    0x150016541794001400001b4000b204c001b41c64460f4120703d0900100c5e501d0790248400781403101c400c1402c100b420301d80c0d400789110f08120318012030702c000060081d01030300601c610103401c21700240101c100c11440c020551140842c13070000034000d41d0900000680c00c0104401c0503d0b10658652a014140e9110f491030415203a01605651440d07039241f5014004050310a0280046400d082140c10750a03c98001d0b40c2d030b41c24121280a0a40e1503090045072500512502d280400c9400c0080b19190180d240607454054443c3c00050799450440c60700c201507070009004101c030380c072090100300001080403a0001404095280c000d03166030b10585100d2411b42c9607403140c0700c1c2c800300180c04140130794950050854104a502210401a5110011000ca214407025030744200000c040030300019006400150405030120030140c24510345201041c10410141d4040c0041001d07150342602079602030060f400c110f0802c03640c1c3d02021410080141506c826100c031200d01d440090555400c42d10b003643c7d681c4181c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 627777841 1250 627776591 627776627
    0x10209010921060e03041e0303090303050c0a05070906030528081806042c09061b09040e070f0806060f060702040e0d0503180f0a06020703051e090a12021f 68
    0x200c0c09001250b5101c0c0e109009071103c7c410141491134030303000800411400c60303625035a804e10700c51464074200c3c1c040d00040d98004140c0a4184e0400c0410b00c00c00c045000b601807140b002a2440c81c40c83d02610b800c0c520f0405800d400e085010a1052800f0304181542041d00411629601d42c000307a1259410000b0791055540320401040c04644210034041e000c0d444da507002d1261002c036410301d590007465a000c5030f07900595442074000494440030b140240058609219045041c0980e90f00098103441d2001c4501ea0b0a51040300c0400c501454248800000d04014002d405c1900f0000c003c560702e48012a0b00e10302441c00003480f5000c40d19241d2000310a40c0464040d90710000d5003080c0103100350b10540342c04144070b804007200200c844005c5007035225200f400004003040c81d55a99060301035040b800054003800428000e10f0008030301c10354152150001c0030601d50ba00e11038601004140486500311115083c0950415401030321615000003007414401135144150b581001d007100e408158400320061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 627779091 1250 627777841 627777851
    0x18060f05250605010801022d04030206030a0b0102010b060f07060b010905090a060e09070e040b0c071a0103200108190b1002101407090e040804091a1201020901092106 73
    0x5490038a038081001c0d84580c07002c0c40181d07030710a500b40c02d030b02079000950010104100036210a074207141c20364400c1680001c01c01d040544c0ea4002410f107401c100c544145007502c8141050b030725a420f104a00071590201c5001d420003844115040060042103c028801d41c3d50f083d21100e241c2c0201820001014024420441c5140561010000d4111481340d4000d03400c4220104801c12404a25142520400764010030701d540e407030302c40c407140844c054040d4211a40800041c3c000c2140024000110110b02803032045035407442c50000c4041e591084203020301a4071010b08403540c0c2c0c0c86144960172401031041c1030b0000035804082d800030141c10042c5a03018282e444607801c0300e42c010500310721304086074204019880c2c0090300d455100b01c088612600241619200340706500d04440c2c43c80e000390040315490f01f0103484d504182c0486103940516040707240c02c0b003959503130f0389400c501c0e40204810f05402541403004510010300100040d0044405e03c10075551b03084104100120750300388a0340c0004017400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 627780341 1250 627779091 627779137
    0xf240d020d050a030905040203090c0d171902070b0708090f040f0f06060305090109030503010302060721050c0f010614010e1201020307050c242d1008010c18060f05 72
    0xb69035242803508401007240300030002020300d02232003502e108010a20140c0040141c0404018200722034a80c1141c55851031b143c41004a4060070140820102a014100c00020039203000b0345005c1180e407000003101c004002040008400c03406a4010312829078980c424a04c45400050140400c2c0c09034140e02d514010520321360180341d030003000c112881500d04011685402001074207850000c8800740215004000410050500f4801880154040d10310349948095881c04942d0744d0000d00080e41c002000841c05804081c02403080080340d14080c0020440c031807034a2540c42c00240404501c3d41400042424070f50a51213a4442455420801c1d000315a00d141c00e01000d049a005400301c0d04461007280b50a040b07030300e030f0141c0c040b010200146488803285d403800354210a40440c0346c01c550507240803081d0049030307480850444d401549503d06101c0c0d480d0a0600c0d081c21101000140c6003041840c03490030022204000702ca4064880c01c0c504030551461460050310a44281c0d20000304803429003000d44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 627781591 1250 627780341 627780343
    0xc01030e030c0d0807030e0a0b070806190b040501140909010b0a18152303010506030402060c01020a02100c090e041407172802010e0904050106050d08070b0f240d020d05 74
    0x241c483c0c2960341b42000700d4400b0010455540c1c40c1c01e00000e0840c00d14a003ca4000740c0908441580f01c0001003488626207003102c18840104001c0c0c0c0400b080410100b03040c4965030300881c1060010640802c114209a149400a0b81121041c03180c0803070150005400460984900c007070540c09644448000b00490ba14000e1032943d10480da001c1e0000350b11099140c4580ca032507041c00305144d240f80e12090640e400c1500f009000d17800a0002c81c0e00c40381c20000e269880b5000e0002d84425581c0e500130b80f1001c80c034188840241c80095140604000d0701c00410b00c8101500d68070941c0054000c43c0c04055002015102490110b49821008240242c0c2e0350000c5000304c00540c0c00d80e11034114032860710000008a03803500d00d8a1320360700240456211080103000f03007000b04540d070344140103a00200e81c1c00c1c0d5820104504009a04055800d0000000c010741804041400c0c65044241040b401a55180031450040e1640443c40c1c141e80311120703548001e10343d6842c1c5080080094006005e400f061405190107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 627782841 1250 627781591 627781607
    0x1202090a080c1801080607030f02210a0b100c0b040510110a0f020d0e060d060b0324061207050c01090c0e040515221b2705090c01030e030c0d 62
    0x14511071041c0081c03c1103000d15600541c1d0495030350b8801460503031182d100550140111013180ea0901e13609101d20018210011180c04140e4103808074401e1601307241003500152680300710810301038894410888102c55010036024407913a00480820001d45503850a981007040c0014515806410702e0800410850711400030003598125442d0002045140310003a600c80003a00901c00c003107445210952414202040140481c0c0070548001035003503103445d8540da00d604203494203c1c2d5668039a10211a0102403140d200f000d100c11031340c1c00c0c2854140c141007007484200918101c1000760100b810200f00f0425000b49081e2070348004500d0100b83c030b0f29152500c4c080c084900b501c0601ca12448008001e80a18a150256a1003c241074144862898101e030703403405180f0849048600e0039940312030369480004540a4055072882581101c540e24400191811103445842024a01014048603590004450302c4c1e20400313080c0807450444041000d07046000f2496820694021190000d07096503200c081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 627784091 1250 627782841 627782863
    0x2d0706110f011401050f01030e0609060105210c0415030807030e04180f0201140c011a1912240203070f0810030c030b130215070213020309030a1202090a08 68
    0x101c9403000300480714542602c40b150070706030140c1d600f40d006011600300402e1401c0114010304000c100014444116072404604403080314168015500610042c5868021640c180850084130560000e00401251301ca03549284800e200f00c0d680c000351711440c0032901c1c40000035a08401035548174801400c010380400d120501181c820352801c42c281c030390310081d60b40522456030400b0101002c81120750065031901e1260f01002c4054105001404030700000740964441c016581311000c00f1860742400340008103445907081c0d03051804a05040c449070710408405500c460704120200308000580a070540c4003040c103036035424042c0c000020001c07080e0300140c21006005c9503503150200b541c0c9a00c1101100e912a00005114900c29407042001c240c0d0400740d590400a4100c001400c2c49156002540d04043c8186840c03c6510108200f400d61511800b098021381f00c10005510b1881e140741d203036403203205084035042440017410b01c081a01810394141c60b0042000342c507000040c1c1e12203500380c1e507070114074513 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627785341 1250 627784091 627784093
    0x30516110d051615020a02010e0102030c010c050d0c0e03030a0507020a09020406170108010b0105070219080303040b09060105011416060f0533010f08090c03070b03010501110d022d070611 82
    0x880015450300c0d0200d030700b1010000317501518040740a54011204444a03452450451206105c04101c00100784111b03030f074001580d1038213681c80c50091080b009444402800d1003c0c0813008064401c940c9010044403240c25451426035030382c0d441c3c1c0c4005a018001a085062028804a00402c4590f04503006001c0504103415640f426a03031561114240e803030582c945800141d092202c2c20045c20301b01260140c14012a00e04141661201c21032451030300f089900341c038030b880990244882c611082c01365034050003080c40c0c02941201c032103214011314400d02464103c9200840916028000b6650003a00c0c00403540c2c5040c000e274240509103218085d10b2843c8181003842034041c2d10101c80040e81d00d0404a44103844503203226042a40543d01c680006000310698040c458091090350307010f02c520310141580200140c1c884d41407000051103c071008521541542c0284941c4030740a400080743c070740d03110240c401e10b04285c040d601002c43c0c6107100307880704841d8032030842c0104105030401200140c040e00b0340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 627786591 1250 627785341 627785383
    0x50c090105031207020f03190c0911041211090a0b100806180405070806040b0106080601082a13080708061e0103080702010c020d0b0103020108060607030516110d05 72
    0x10400101420700c10580d02d40e000c8400c406000c1e0011010301629400101480007224007207007c00d0518440c4103541c100701909400c1d0000300110125803001501010364100003c3d11039181138026489113000d03036400e0b8044840d05004110110034085003111018200d03030180c0c10841050b901402e05c1d41c21407441841d003032035810304942c407683c0d010348200002451000404041c0b01d03c0300403540040c20503900c5000e900c0c80032030300a03c1081450f019900c90078101075a90301d0100000e000200141403903040182900501100d2904020803801e2080d40304038501c94000c094a01c42420300c00d0b0031110820325441c950000d092800440c62a04807540901522025034035081505000580c00201c051142e208900500100d013085000d010b00c2e074410305000d982c0b1942c58001401c1c00203a03540850b81c0403a104018411564804541600400b0541790942403034510341d005030036400b60714494648c410310294200c00b4401c2d8604044525680680130031030014550400c20340300c60f40a002d15250400007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 627787841 1250 627786591 627786613
    0x120804062d050c09030a1b030206041d01052d0f03070b03010305010b03010507140703050904050c0c102322150e0304050d02130b030613060f0c020a17190c05 69
    0x203c3c04881500c0c6005015003402d9005550b1214003802c1e07102e461004407080a808801a03c0701c500902c094051582c0212045507060008251140140c10403400f84540b400e00042e4100300020520150345000601d2241008030720206140c4880008030603414842c405000543d4282d103001541030328040c0700240b00c3d03103d4200c01d160a07610290381d040c00243c0b000d1221361000e40640060544030303109291491400e20f486000400356101074a142144003400540c0c8818001c041041c81d03040701d5500802e0020003003842458101c106441b40c070308030b02d108407000a000302d0290301040d06210481286603408801e18107101091548680921481c0c07031402501051541002064030101e074801480c51517000015824800701c20b401180e1222041d071a449030203026602409035602c5901031383c1a07460994072030b051141c15103828144083d11545440266902c4a901140c940030746900300c031a00d101041040e00f00f01f00c6201c2d0060030081c2803515001c165801d94040742c4106d01901503c200c501207048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 627789091 1250 627787841 627787861
    0x220e010b0d0c030b10051e01080a0903050f0f07050f01020a021e0601230409030f020106060c1a070c0b070306050a06171b13081612120804062d05 64
    0x8200000b402d02e40300040100b001450040e02d0f25030200d2020030041d08680d032a40455942da8903c0281c0341c1d03203904012007001c5564030085003075108201c004140188002078501600074848c038003500140740350002c0d001d101c000408044460039580007003192441c60b001005a4002c0d00f180080600500680403100b04030380d801e100340d0303c0580700000a00400e03442c1018036501c9480030844401082401e46270b41c1001c1d1f840340700e280d040a000380c6500607905c4001c0700081c2107a20507000401030001d07a842c18030204940501d860000c14040f2400700d01e40c1c492200590302c4141842004008602c0081089200c980c142c014174100c0b8070540e41e0b128115151201610b083e0884244c0000c030340341000020340c0040c480018050513400b200209407501c440d8814000c03c108280d00544040d03804039040100380100000d200c8020410481c030211841100e5440ca80c2034002c12440004205c03545011500b440f2181e4006032940a6810125646003102944140002340700680199524500b2000038000d4030703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 627790341 1250 627789091 627789109
    0x60c030222090b03062203030e0d11010b04020c030418062402150f040b0c19020606120118060f110415080a0204060c08030c13080703110f0f01030b220e010b 69
    0x141da80f49091402c1003502802260340c00c0302425000c264859020303000806003030000c54ae4807046030340c40454001d99041000e00707603880000e4060180344100103008810310040191401d4903039000c0e503d02590084003c0c6c0740076001941000284170564250010042070341c050317204500e02e6070703020780710380a4404075080c0d00e07110304a814804006100300040c0016803600c05160307000510651490038210318510018555030310240100160f0b00c0a0140041031401020540a100d9218020701100071400c051054411070144010305d5603840740c000301c0100f40d441e082000441c00140905445075900ca03080800d00c4660000c0b60045449400480c0a001c07090007242c0a95540b501c0e030800403080c6a846490b81d503c02403600c4d168060601403801040402800700303004010210081c1760550442c00d16000440244a45c58031070108169064001d8a0b03180399080c03100c000342400940b141c61a4003013a0080504099240d003e8000400c540480d522580302140d00a440d030000c100e0b00307900c0418080250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 627791591 1250 627790341 627790351
    0x501030504080304060b03010905030307022a0117100b190e010801350a060501051002010203070e120c030a03080717061f170c040312020d0903060c030222090b0306 72
    0xd1400c2001030040740c20f5401406c05c8000c0980005090300d22034540c030b801c2d03800649203140160885542e13148080a42c4a1130220603034944000341c008054500040c210080101d003c000300c0041c6c1000641485056800740c0c000d25031035100d10355030f07011070410b540408480380303000c400325104022402c4039500c20080c4506a4420380304940c1d80c11328002482c1464080d0306c105004208081290f809503d1040c46907141180c801d01c400f080e03550504040060404c01e8580403404c580c418420001034035400308000c42c4410081c0c0340a89655440303a21f503806d000c01990000d405225032940103040561101070a4410030140da01c425501105400c0c913008500d0558480394410101007550304490700c2040740c1000c02c0c01c1418144514900589188107070a070454120400e0ba1003c5070400510030007011000d1a461a8805019141d81c1c81d00083c06052071400003800c41640c1c1c40f0303407180290090b4119894a26543c0364041660030710800030903c0032882c0507100c810340c20b18030041194100050820302035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 627792841 1250 627791591 627791603
    0x60e0c0f0402092803050705031b040510270e070e0c1303050a08180402040518040611040801020c010c0f05034b09210c0c0a0f0e010501030504 63
    0x500c90400020703400124100d070b84144800840c2800b03c83c009203400c6401a08007a442076a0b14604005050240039405103000e40c00c005083c01c62100c02606002c290402150001020b031541c01d81c280e001c0100d900804440511141081c0703144140b4004030f003401404110a000142c80d080b156625000f0320b108070358001e90390171b01180c0030079200400b601420040d9040000c40c0f80e82d907104d81d80380016607101500c0c039010003d03e00202140c2d0a00c141011035060340c1c00d52600c0e16001c0400c4900b084008844040c20b010307004201048800e41100c0c62412041140d2900c50340c4403180c01d4005d510185003030501d58a48203103410042c1c0110303142c000045050b1a039170308540d90904c0f9040300ca0045800e50116100c44c0d0710b541d1070448600015400400300211180f4100d072110100d514111004c0c00039201c943c010b45440940711000140341680b24100200b01d134076800b4a414541c5411602400707140c0c0080762407408148042d810140c03104440e4490318010303450366100d00650417036205580107440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 627794091 1250 627792841 627792859
    0x3060a1e09020c121b0c0a0b0306090402130c0e0109050307031a040312020a0504030b06030f1e0a0209150114030f0112021f0806120303060d111203030703020403060e0c 74
    0x424052603001c1d10f0095068001c0d94035074040c03242e242601e031307001c0120807030710368040070815590741000c010b0f402d4100800ea40d5030740f2060030203904005a02005210340d00ca41c00c060001400c5441d8000d0040000074050303020f125410500c0d0002d03104180c5041303907d0020705141c400151520340040d951040b29004079275a1031481214600c13600b190001032043d001e004d1081c421100050302440101903d803a01e0740e03801c1d1618210301e0710303d40800000d408180f0a5200c010740d50308151000c00c0b820f00f911001019190f40030311000195040498410003e580f121005003004403100110744a038044c1142642e4540d003001e900c3c4050100c50000b95000ba5481c11420014041e2510b000c0c035211400340020106501c02d00456140c00d503002075503001a00085d00201072040d642041d0b0711130b4000a0031840038504514002000c10842030703107100d02900100034080000c0c4a52101198285110024000d480d5603240200f000b40181d40284400c4846c0e80c541000b0101e501c03000704000402400c01083c1000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 627795341 1250 627794091 627794099
    0x4020d050c1926060a17060f01050402070c05011b17090301110c0d0e0a090f0b010f0309020d02090a0605060307080717040503120703060b1602100201020f0708070f061103060a1e 78
    0x70b1140d100410998200905410124004800545803a10325007220b004000c107250548203185130030f0041c0d0002d405540140400000180303b184408151070b400c0c6450100e40c040200c400d04070101049000e00318100302c40301008481d00b01c4004140002c020303002403121442a58111f40c042c440e04001c1c047c1500a900c80c0b0003030030320036032b403592105400420082c0d071540c0321041042100d200c40401000a641c41e07054040c1e9507048401505811441c0c101008038000c11340118074200d82446000303208044101c00103400300d01d20fa0064002d04006032410b5100d241050000d4507210061300d1700c1c1c01180c000310060038220f6003038070514402c55200f0b01035400c121001c00400510400034040800303140d1544004511032544201601411407401d034240310418490050140c0b608040001c2011640104402402d01050408440f03c007035026281c0b90743d5507810b080c940780d0355402010052820341054403210300e180d8080c004e0360003144221004d0642030b54900809460340c0b50950450031590b1200d03070800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 627796591 1250 627795341 627795407
    0x182205090607260601030f1b02060c03160c020301110f1b03040510051b0f0c090928030c1203020d0e0105041101050c07050a06020d0801060e030a020f04020d050c19 72
    0x6508851306040104840e1651041482690304660749480500e2121280d014070580c10883d054010004c0f00c031f03442c41c508007240d03d600400d940d26500018800250411002c64500350700607610035480481084c0c80d60700d2424010a140d01502c0100d0080c03c0c150310649200c03801004440c12101c008007901d210081184d8141e03100d030070000509803100050803644103030403024415400200b803103001a01d00044090104054014084c040e168540c0c002d12040f91128880d4858808004049144400e445098070701143c44c045180001400d60700b11400403110b05d6015000380c038840391488810320a9441d01e40c0704600301d42007100c026200c0f00168980401e1540114014140080c80710140e4440a031218003241c00400c0300e40c81680140c1c00700e04040e00c0380d40d03c00100340c0503003130614240040c1c103901c100113a550305010308040d02c81d0b07074800803880040d40c41d507045410607900715109120314a8400f0505990303412140404441c03611940180c1020741c07003524050342440da500207424072415120025 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 627797841 1250 627796591 627796667
    0x4080a0f0c05120306031b0d02130e120307120207050a23030406051306020606030d1b0f0b0a0e0a051002310e010801022803020906070f021c0206182205090607 70
    0x322b0310b0140d403404601a0003c090008030540840e250072155242440c080081c040201c100c01000b9162041c41014001100456a1480290000c00c0341154050540500152511091040d0b0052000150026010380c00c000035008200480c3c031400c00e0556111000d0382c680c4012190300d9410b8201408200030a401260a8582a000c080d03031005020799990703500c0e2a074010740c00151414040b090030805c500d403443c02680e00100500c2e001d4030494000780d540079a1b41d550004510403403500400c41c40caa03441004003171940c0c000000300c1d0360641c0420421210240b20640640300100c004000049240f040500880340311550a202d00d80030307a0303d40b4103005055456100344004151f005c01240d00d05950b5000039124190060044040010071441000101d2848081c41e00b40c8265000400002d40e41d50015107154040c2c02060070350007000f072400560071342d027105e201c4800b48240c010041050b02d0960b00c118455690102101d406480304101076038034044406258140004066a58864042c05002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 627799091 1250 627797841 627797869
    0x100504080d20030a0203030f0a292d090a0513020111010603020a03081b06010308030c030907030b010611010e030328230601020d0804080a0f0c05120306031b0d02 71
    0x54802e079414842050b0956128440360b44c0140c0c008020300c074910804845454000603111010081c11015407150207050203c50904030b03014010b10003000940e2a60307154100c1c2d006544415000c01d03070681c401440588002c039061070040748510006034000050388203450180902400f9501101c81940c01101ca24810f045034a4895486010000058461903408005144242c55043d1a0042242e00048007829000400c1559008030700420210b092401100c0e04409074a030300c69036075035820b4000ca260007055071004000c088090000502d0301c0d88a030448030900d09220081c07240d00c0034003840c5503503404142c4440845554460140b00c6484106040c440c422000d402e0208403000382c440b40c00e007a00743d841c80c502c144c22440c500304203056a05100041d0b5a4050b030400c0c038014202500d48882034003a0700300c07910a00161203008240c840c003a100700c222040d070040481c1e03003030440508030003566081a1050760283c4180c1c8000c131a285000001d202211102500c6074503d4109602000000388000c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 627800341 1250 627799091 627799127
    0xc1101200c210910020105040f030c1103060108100b030f0c0108071107150e0315040602030a021c0b0909030304150b010903151a01092306190c02100504080d 69
    0x288200d04640400b8141c4080c81c80c1101c82c644900e600014011100c814000d40310031645000e041000103400603680100c059003514008141594928101d05d2001c902c4401e07680c10311910000041490303002030b080e070550403c40c405000c02a259002d055641260002c22082d41d04540205200d03035114100140c0d208000340f42482e540054070341d41070f051071140d802c0f400400140c01c904000741500205400354012082e4001d00d004007020b0792040400b1405440104682c0c2c0010120b810140d064041c2d9826039920700c502c000890441074800003c100102c0403c0c0a41582c1d0b001900d10700020040e24800c0750080d52802c0050704e0240310340000d0040b83c00c449d044c0300c1039010110118104000040d00c1308000d000000d4540015003c8080f81c11030703400c07124104003030034100340f111109820881c05260380b8603052582c05441c007030000d59603000e0403d08001c3c245408031141400359201502420300c134000d81c1c56109500c910b000880b201c0c81140648901d581c0096211790225108a901c0041100340785 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 627801591 1250 627800341 627800353
    0x40f0e0a20041a040503190302031c0605130204080a080a0306180905060606090d0303050c1b03040e0f130308040f050f01020409061508160c0b04060c1101200c 70
    0x12040c0000000001c10a1410011505200e042001e0400190640140714001e050a10b400e002a94903002d5a1200a50f02c41140f200c5c01054020015603100c4240d111601c11010f000e24100c000130304481c861603219107803081510003201c0031171084506460821010700b8042d8071380d8441c6019030380303c00055020981c0c1d421000907103004016514140703402000300030403407031903506085292900141445110b82c20810082c01c883d9640e0400c000c1ca1541401c01241564610003404418010020300318030b02452614004101c1a0220042050302c07900c91030524aa01c0c1e5400e019499202210440142417006030548003013401290b44940c094840c0c40e1400c40108565190341c2010b0043d0070703044180c2e4001c54140b10700075803401840041c0030612110501c0140c3c46100500170f08000d003c4c28841c001d1811141c3c2424400e0300c60880154002800018604192811030000d0039103585c89030014513003d69031035038201c0c180541d00f95134881500e08110548840e4130000d0607403241e4012040c41c032a84e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 627802841 1250 627801591 627801611
    0x3090307020d150509152a1308060f040b0c030606090d05010b041a0d060b1201020c0705011b020a15020f010e0f160605030a020318100606090b040f0e0a 67
    0x18a50b2260440c86080511a00f402c02c0343c031a002d84001401c0c0005135044001d081040c4c0d116041c1d0503610030540c2c04800d5907942c1c092050310000d00381090000b00b2440000c0c0b5412404d450130040c00858640b0412540c465580d01c2d01244e0307415050328001c103c00402004620a602c480010715040344005154034605076900c0e0014550280702c241c01c9855035128011500d81c0e00d058455040d40c1c0c00f5590f58242c14600a00005140341404070b4010308aa070303500210002500c1d119804080c040c03003030008640e50003908a090750345180d11301c282400101c1202403004004d890400240d5881d03805045480440d0030020f44403840d010085145046100d040b140100241090007150002c103103000203000c3c0010340803081424100b0180a56024080b014410045680c0c40012a91b220240100060300d036183c003000d103408200c80298980c118420075002c82c2c10700206134029821940341d611401a45c0da40d60640340d10a010314800e0100e0700544c9d52007000031143d010b195550200740341e00c000502c0509 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 627804091 1250 627802841 627802849
    0x50310290703110601050103090f02101b03121506022a1903050105010b1303142b0305151003021804021c0c0504030b0711070f1215050c0f0309030702 66
    0x404a0150700194404070400c1070f121091280324090402840d00307118034010b5840f000040d0040c480000d00441e100e81b010080c1502c00d040320340001260114440c40d1140600f40141107210841c00c2075a218981107000e016240d407010074a080350342c2d980107004069503541d041c03100740041502103042d4480000e004403450381e40b003c110600552440e000c071981400d45c200f9508440e816001000180781c1000780307001201821885d641100e510400403141c04650399000350500804010307038501000c4210309004003a0004110302c3d155803450307601700402d603968180300c440103141e0700a5540000191205040c16032003500201105175410803818800d446400100707080360300844081c1c500189804281c0d100708100d0040f0b81820126140003801c281c21a151010740060181440051018007949041559018031003880240720159031884515620159440b0441d600c2c84e00300d505000d2512540d03001ca021340706190007903180c500b0240c1400610040d804035988098800c500e44d110500c020700c0183c2d0317 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 627805341 1250 627804091 627804097
    0x70c08030712090f03171b010e0106081605060f13090203040c05014d0703060209090a0e03030601050c011e05010f061d0906030a0f060b040f09020f0609060403060504051c05031029 79
    0x3100d8000000c03040d28207005a800c1083c00440b244dc01c0381c26070fa0802580d40e550007030b24005402002070790f5890b5445000031101400c5079204100081c0040101700500014490070b40848400380c803408480074540c2021110312030501c1c4400340d41e13000f0000286420500c0c000d00091080f0811142200c84004003003240341c200f90354403c568043c1c00085a0520703003081d060040c1c21010000091101c4410054140d40328000240860704009011135800c10382c00b000d400042000b0a03070760b203c7c0c0c05841e0030001b82002c3c4c5024012022041080306001035580c1c4038020141d001c407003c10034203820b2034460301040049100500b04c1c60f030521402200c00b0200f1640140445940c2c070683c00002c807408100300b4001516860110740481c5803820b030503a80540c4130b4040199540704112110342e074134040d02c1c0000f80f1300d005031f4002500d82440d1201304002c01900041852807803161007081411130f511480125101d01c0200c078951548200e0f9881041501c210078450711420200d00340320007035101c41c10b11850702a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 627806591 1250 627805341 627805361
    0xc09040609060e071208030a06120c06231209071806080d03110d0c030f0c2102040609031e080a0f0306080601050f0105070c08030712090f03171b01 65
    0xd41ea4410a4042040303510440c0841d500c00d5000e884c455250106448490b003020700041c28040740040013034030310205548140094140c050003031500b03030b42d14105840003903200e01078403020800307100194a91001c2070b41481300c180c030400707401807505d52a0304441c0218a406804070a040c0700d080b1000ca42e48250b100d4003134281b43e5817000060301134a4440c0c61450400a506000305051900000c5281400341600b00d03449841c190394013065000440000f1401004100744645005181c01c17048030056071b220740c229450b50800c906c84914000040c6079001244034510405001c20032403c4100005981041105040b400702103210f1040000c5840e01226a8440e040d600002036991901406842c1c0510550000c1d0200c00000c181d80e60600000c1613120310352591482c14001c0c0070501804000707045030144054a000303070641e611307a00c4924000300c820306994401c80101d2415a400300703041c4000004602100e820038106481e0710500300c044086540070098200c03c1041c100206401c02d402402898600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 627807841 1250 627806591 627806603
    0xb06120c070c06080c0f1605030a020c0a050f09190b10030e1e1b040f06090c110a0b010605030c090306010602070f080c0d020103020a09030f0b15040507080f06030c0904 74
    0x680261500c801c07442c006030040c505010264040c448030400d14816a40340c009404c81c01640c407032041c000d0f41319012089900030f00750302c000103040c0b042c56030105201140702c0080c0c80c02280980c42704100021409503402031a0064510f20014801c17441440200c030360544400720004003604500c010460902c11040501c0c08240c98468070311058804000d54045c81004005410340304c580b85c201c41d910f440b912800f10b0b0140c0709910a0300100d0b03503580d114241140070007104100c0303076907104258006403a2100040000c00c5000b0a1410b008d000403980311801a44001e1610f00c1c0d80c00d040c400e4402d0740010304181400c910901042445440800103c3e029062940041c0b43e810720307001918204052310740240d0281d422030900540142c0b01c3c0328442c80c00c1542420017680f1205840800c0322144903503400980007050707074881f001c288049000018001d04041040d40031000000c03003400181c03007058402000098280c0002039182200220300754000700b004080d0b4030f00b14603150008207161400d480c00d44e44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 627809091 1250 627807841 627807847
    0x31e03140d0b010e010503190b190e07023f2a0f010905060f092a1008010501122c0129090f0901110d0e0c01020303190b06120c 56
    0x125a0403103008130892100b460811300d14500360000c10380c001c0502c0340011200d6101d407000f0507180d4030000a190741003080043c030030b00e041d40e510307003440c0f8107405039151400b5008060f104010b45403c2104141680c0c10000c04504104400000141c03080c500c9100c048000d40030301c942d00b1600e20142d00741d80080e0030081c0e145044408030030b11904000c40c00d804c4a044ae850411400005034000c2041ca90004500c003c600450b0764131400941401621030000180242e0701d0f01940740382c00081d0825640f000309a4440440c4a9040b106464040080c06982d020a034014048642d00700300d50008030034454800b40b041c2051544031000c40384038031111504d600e582d45800004800f9081720391110741d80384105c1d0004480c241b0700400700c1e071510409002c2c45400906140010304802007500082c405401040186a80e03d05104808008081c1d150340f0359100d00925007040841d600c00819607010f00c13010940560707282038026031140181031840a0b00d0304085c0038000d24081c0001c25500c54440c074216824199 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 627810341 1250 627809091 627809111
    0xf04030303020c390d02091e131a090a0b0907050103050a0b0108041509051c021c09061b02060d0501030b0f091207020f03060907061701031e03140d 65
    0x10410070803100400c0180c0c101603a01001c03000c108010b94002007645200140b0508050105d4801c10b02803034041d400011034401d02c4480c94051440303405007080003039042e50a485560303180c0c42c0c48485000207080d500c010048d5800342041d400720390303400ca02d1741c40440b0010641581d51007600181240d080003c2d4000740390403c415600360048641c0018000402c2148030540000688000c002600241c9244140500305441019560000d2a556006000c480003580b842140308001b104550041d801805505d045008040c0c0d200c11564000c045a01c54501e000e050030011500c180d00b114155203804e0030400316001585a41b0300a220094100c84089003560440c1081ca03242e08000e000200c61202d00c0702004243d80c80422590f400b5402014817995130f400d070f400020072031203024102941c9070244030b003032000e200d8002030103200700c46642e140c1c188030070550050100e503944244000362100c5c103010013221764100a40581c0004600ca410200145100b46c50950000c1d0800415000059501c0c24102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 627811591 1250 627810341 627810343
    0xc060a0e0106061106010e0403090806010803091017040314041d010302011704120e1302030a0509060109060b0702040f06080a0309140603040f060509010b0402070303021e03060109060f0201020f04030303020c 91
    0xf07040141401c00d071103070107200c12030b955801c14401c0c1000f0402010105003058071030180c0c038000f041c2403002c43d030b02940c440810300e4980d40414041d62045c6c40d5050003042c82c0303000b425420811036458800807206d40c1e4649082c0c42580e016000c14221810400021800300722449a28460007850b080300c0010b90704604c000b400c201074000d00c0c034845013504002c1200040d50341c1d00184031003420381b60080e46008890f002c070700c005111b08a062015400070003004041c02a40d0f12082c814044207084031003030307680d1360754000483c0c2a03800b51980400040101e1009410140c01044030092511400101d00d079540700d03024140f5040c2c0804500240c005034003000071418010380b450340c03203c00301c1d04907143d800c1640c0c03180f0b4082c00c07101006044544400004180e0002940140030000001e0710a558844613032500030000d40c45520354950f44944480d800034540705039002d43e4803c100c1a12103c5009062900a5600d40340307082030041159000c004410100600c20b0203080218881c1e200540c5076541c600001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 627812841 1250 627811591 627811601
    0x619200105010f0801021201060509040f0504060b0109090c14031f080a06060f0e190902090c070b09030c06040311010618020d2d0e01240e070302070b0601140c060a0e01 74
    0x300030704e84c0c0180704140b45084000705240c112003003410300558410211001c6000f8001962a60318518502410002400030503001003071848170981e51201ca881e246c0d0403a40465503590600c0b0002102c002311181c405048200071034104d680180060b18545911692010404954005544540269001004101da10300501e8041d0468070011281c0a0800d0700d4030b949031100031300c0d032180c0e0a403880303c164002d01650b014421aa40261501c2d201d494030f03590b020303903940c040d62049640c00702e660001150500e01005444c441030341d0a010346142d40f10b03928202c401380049400102d1555072500c00140030031820039810883e4a1841015032141c21000384501140c0301c800101c003070060041c540301490821039035141500e10012100149860410150b02d00500540442e1001c03140f04070303042c00540d400c8101c448100c9881c0b2040010b69a2440400c905900030124010628040b40001c502e145d070060108d50405071000d410241482410025a03140800c1035400ca044a40d031940f500075071081c21b0140b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 627814091 1250 627812841 627812849
    0x16140d080307030905060c0a081605191e0309080d05090f0123060405100e090709060f0305060601021501090b0d050102030f04020a080705010804080a090b0d0e0601140619200105010f 80
    0x107503007407a100000103000c0b910000c1007540c1c0eaa0452b0a0880640d00510a45443d50139540041c0b03c1c01070941009811443c00f41c44981b404143c40d02990040c922a00901c80030590007000c03941080e002d070741800045d01010f410365080c1e00620300344601d105800d1181082500901a07800b150901c0c031400e8102c86400900560700460500b002c205494441421540c221014600a0100c40e41c9140d082400e040c460703007190458a04000001540361441e020450540703026005881150f103d9400580c2d0b1800003220000c40d089104004100b01e0712143d10800d1b5814010300680800a5956621740c22640121005003c00310f0f8403003400194284101030358050302413800200402404d1400180124100a000a04204001600c0d03040684100c074008010700c1c0700402c25031944007080208000d0094031440d41d6062003518000100d00b03041c0d051030101004081d00720391030720590300345a04c492545010070794280324014000340070070302040d491006403a410000010f015410044c11110100503588 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 627815341 1250 627814091 627814111
    0x2306092e031b081906050d0305070c0603061a070213061707082a03120a020607080c180d020a180c020106080a0c050d1e0b0106020f16140d08030703090506 68
    0x40c40c244454001e40100c3e0454844071010400b1035181c0190f002074170135500001c0e00001505144810983c20a0203401d029104103d8400240e0302c4076001c0701104c40c03a220702011141c41c8503c00d45110100402401518005400701c5000c6a510707580c801035401c1507224800c01d01c44c040b900351526109100e00800b81c00840f0143c00000b49928041d0803489011040380b144490650b410840c42d0303401c00c440350140700a048e025440b43d840c6000a5240c00c0c0454031603000c5141000011361407100034081710300035000b0350b06500520350484144030320425584022602f001c8420800301d00c1d0010320140c0030003001c0a2101242082c002c507402402e40340d09500403401940000c0000002035100c1000304182d44c41070301c500c14602128241600f1105100003000340d100e021001c43c10512400c901d802e07044e10074a408840d100c811420109564051568208205a0104005201010360700e11000450240200100c2c9890610345a07407505c3e60054a07a8000f0941d40c13045d81007085014050b031039010800c48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 627816591 1250 627815341 627815381
    0x4020319020a090209060705070b030601081b040312030e070305011d010b0f04020304080d1503031403160f0302090303040f060e06030405060703230a05102306092e03 73
    0x1e404036501034200d000c0e902209030003003207031092030721404241e40060b90801c085445540c0c0d00e80c0050010380c01521814005180400061030400039400c0307541d07007550001c4203941ba003803950f02c504e8051200e203034024041580324410424450010000307180514081e90002681c407001c200243c00c100e10800500e40301d42d0411030321031850307032b6040300200c840d00056801603900d41d038a02d040040307403107071030b400d50103017440c1000312a00c00a00601807825240b0070b460f48940000428044400b5006c01c0f2581c2c0c0401900d04944d0420a224001c1100c07811003a040240c1400b00340d01c000307030030354015800c00b00c00c1c44a4500100000c5900a81e20400500c0a0300c0d45403860602d41c071860340344d1900400000c141600c41e0b10441a000c2e80001031100c070340e49172000c0d05460420440c50405000d06507000b000c0044200000b1581c08040c030307255429a800e502c90710070708001c0e40c000d02000e070b00001442c5510001c00e0944c011400a1907038110070320840c4000703021202050300c00213400c44090780d04481001080f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 627817841 1250 627816591 627816593
    0x1140306040609050f16080111121303180308281202161e020f04050907050409110d05030d061e090b12030d0b011b052e1404020319 58
    0x20400a81007900000b0206030740310541132461800c0340300648410288900c0d6840f0418034406940c0c0c0090b184031000910480000140d556940c3c001d00d01d150308641500300118203040a02d000000b01d06219017403a0029440222416058400075841642e0581d0f000403c40190421030181d800c1003103509400b51004402080000e05280f09000e0b081c02080c0d0000e8854400b00a0081c1841d210ba0700409601c0040190b806c00d03902032010302030403030084181a01028451400b4014684034140e114000c000c0d2a00c0c2808110162041c9802560042450140c45109485001c038092005004600455071a0b01041c02042226810390101c160b100e1003800da061403010700080b446c111114000c02180d002a1103002132070300086d8024903c040d12000403c400600c0240c3c1203418503050903200c90441200380319686042030f00005c4010410b80001d03421005085842e4080c0c6010005682c01c8407004603485142d000326030064281d00320b0580580304100c210718080005c15420b4441701c1c0c00030403903412 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 627819091 1250 627817841 627817843
    0x110f12162001060803030c0d0c0914100912030e01080702070506030403081510021b011407060203090319020a020f120705060306040e0a06020306090606041203080c04170c030105011403 81
    0x1c41d50901d40e14480031240840c0701102508400c015052203000c1d41d5490800180f400010b90040e08841c7c070040c01c110005522170302803041d0314129025110141e00750b855000070040d00c4a5003510381e0040c06010a00420345481c2407142d0000c00f8071944070b416040002d007001400c5000c00511000856114450502003501d0b0300040d00d800c0781d81402c100c46152030324000e28040e101d00c4100244c100c0040f66a0f84e0406600048a07080107150742d038180103961010004444401e00c4000c8124491002c01c29180091660383c01581d000c5a020181ca00f40100c4110020f031004400d180140141c1c0300d195104107614144625007008401220072400e0394058150081d15850b40d486610b22030f0710f01000141064031350750480c0d90000000025201440510310301742c070080d0010344681c1d0049266a0002d2800e0800d40f0441d400c0c2c1d8034442080b02074550f42d40d0200da40d044000d2050707050400034000014032281d03407000000c0210b40b65000c0c204021140c0203050840310141c0c170500300400d134200c5601e06a20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 627820341 1250 627819091 627819107
    0x6041208070908060915130f1e171c050f040b0402010e03030a051b010e060408030a060f08060a14010518130803010602060709050301051902030901110f1216 69
    0x503090486607980c40c00c01c1520030107025440401079014550070041008004220610503010107074220505840e1880c542c20350406044009041040491004001c1084804030003024204041b04800042082c1e8031014400c802d000060281e14000c40c40d81c64501d00d003825410110440711040103203240a00500c2800c0708081c2c0060309088681001c5800c0d0391081c0d0700340d0000c42015046a9072800d4000b070080c22a401b0b60b88040b0070300c1d06030003800c2552030306000d04026090006c0040103183c845450f10096640050700b02003900b692100002200305004481341d005001610180000d464038a9402d02a11030000402d2103d042020060107544e031404421062003c50b02d2450805c3c0e0b0b039142d0826408003154601a2074072001000024460368000b52040c4a0030f9143d4522080c00d0352482030509a038802d80b480c84115036601a0840014001c0e8041c603440b036280000407035a4605d25074050182d502084519450401c0091040400741c8030740115508840502d0040390380e1140f00f20b000700001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 627821591 1250 627820341 627820373
    0x504021602090711030a050a030b060301060206280606050403032303010b09040b0a150207080f061521010203180304031101030b0a1a0702040c0e03060106030b01090924080604 77
    0x40e0071400310790524400c04c0712100c81180042100c3c1d035030910600152040e0071000c1d00d43e000030304102610445040450a0740c0c100c90316500140420344860907121032a8201102000784040c003200050080b03480303400744034010100360316121fa8490a42c00e00401c90807801d0b0036031500d06044220164001400c504076411a03100c81b0619456541c0840050090660200f0007503110140c2e56000c501401104c02070460042d03140c0031039102030b031384401c403940760b10040e0700900883d00203100080080c020134107070010b510801840740c0c112102162518008114542d40500180c3d80401000070500341c688221061949210040d4102451603480c01462180e00500c2c9041685442d42d810503a2182c02400001c0c115a0401046003011000c00c80ba030350300120016441a4182801180701d42d000d458181605c100190203000541e080c01c1c02030700a401080005410400078150005202110784100b001c1c06d080c0d101d5001c2c070f2900c040c0001c41030f4507840c1c0000d240360700510706200001e95402c400f42d180c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 627822841 1250 627821591 627821599
    0x806030d05160206040306052502071511011d0d021216080f07050606040b1e211905010c0521090a1e050615010c17040503030f0a02070504021602 64
    0x9807542c10031a518040c81d00400a4003c50041400302c204242a0056486640300c84980050800020199818600e00180000144e000101300780b21150340e00740d60301e65008031414240c010440c1c2e0034645003100e0b01d070600d80c844110748104d003410042052114443c64489032004000b1a802c5484c0400d0368032608800c1ea601450000d80d03401001000d0003500e1905500010fa40c0d15500213040464890404641e0b681c400c03480d20148140320301d4a40c105200c3c8425403a0014040c200c401d05000341c5054426003440f00c2c12801d8860b8800c0c3c0420003501c2840420102e5407582d1802e14035000e4290380302c851b00c09041c001c2c20702000c040035410190164903182445500317185078662031251410604c101e0005008202d01500c03074480e5184c0c0402e5048000c1c0702d0001c692180d42e4003110400c044041250041c002440042c1031800305035010b480c10003c5005800d07030341c0b4107941d84001034907580c80204500301c0e040740800d02c482c0041d01030040c2e02c01494142c80a614010064680c810440d0a981c802889 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 627824091 1250 627822841 627822847
    0x114030d031508010207140d090b03040201030b0d0503040f030b010f0605121008030301030b071d1e041401262b030b040603060605030d020f03092412010906060806030d05 75
    0x701da50910b4000801d034403c021540d58205041c0130f4a21a00c0403100320b0103228410412040c2132003041d000302113407084030001c1d0550302da50380110041c0010411290b40328070024103a801082060001b000201894140948141c0c03444c600fa011080c416030003002411210b10b030401c04c60380c1000848405d4000e14146a81640d164541d1031104051a00305d81d0b140c2c80301000100030058458a000c0c02600c00d500c03980030300f80d100c440807a01800720f288000d41201c030700081401483c80c0c0080b21200444000d1004c00c5066440801c440011b009074031040280b06e840116810b18120720385203516200019000d441d10200000848080285642d101c6182c0d55445c204d00801a2083d807200d850b9910091090250641d0ba0403c20082e000b80d0003030a00c40c0c05903201d0b0f01c004500014001c0703da00d100764080d40c03d04590b60200204d800041c0c802030194080441a2582c5034140e000078420026441000800d650610100c1421034007160004010701590b2014401a03030740008221200003c0b601d00255 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 627825341 1250 627824091 627824111
    0x609160207030b0c0417010b030709110405120c010e061201030b040f14060603100627090f060e0c181f090f0f050c16060509030405060c0102070b0114030d03 69
    0x100e4440c0703952028012a040e54244400054040000c2c070072150401c100c0b2000d0007540c1c44c1c083c200c03006228400c0d81a40288020410f00007280c203d000032504022081e4209503917100490322010b02d640e4900c99680041c0d000802d1581c0081910a41d01c4c000c4d540315040c0500484410490340040c0070180c080758070300e4001410080c2e010740d0b01070b4541e4050100a4104066141950b480c04103460740c81c4603000781c000261042c0000c1c45080100c450f040303c002210741018a20700340502c00a0411221503448516440109a942d80d103a1440780c403660380041e40800b070703920030780c1841e0b0300b0003206200703816002261200008903030906400950280b02e500e040c4070784d00340842803405268400b14805040c21201202d07001c1030751001c40a455810f4081c40300c0e0356291000d10f02442020801c031a0f0707613110340d051804111030360301556100100c1000c5901d0a03403078000061081d00301c03c514584980d0000746000030442030308046030041089100c150506132041000a8885501e907100c60b080607a2076007002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 627826591 1250 627825341 627825343
    0x1203010b1605100c0c0b06030f10020f090d0507090b090f04140a021002070305120901020a230a0f0218041e0c0510020708120405100806042a0201060e06091602 70
    0x52004140f1a000c200410303031484080d0109103e01002c0c0d1754001060b0002d40d032424041244490044174001801c10f03542500c001c40000d40010503881a005020b104076226030301c80e00c2004001901980041450320300e84401717030068520000f9054001c0c5804024008208e80da20fa505401550003010140d214803030b541c18510340f404251002c0d40c06180240240c1c1c09a4010414a0030341340a481034820003010001c10764094030426414600503071210410030040351040240300c042c400c2c2c110302401c0b0302d40708224081c60001c18840c00d070340001003603506c0030451514003900040b65008042031100c51910307841daa903841c0400360302940458031590020080101c48174000002c0c050051400c4084001b00070000d40d00c040c140110f80d40d600c00c0304112899141100c042d5012a44018690414419000000c0b00d2070790000c1d0509030407a4a4101105c3c2c0040791200344030340d110742140c02504148030490000d0a6581e15403284048590740b800b484555203603020300700c0c0d0001200d403140c40d808100740c90803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 627827841 1250 627826591 627826603
    0x170a050d0e040b0a0609061407050c090c0c070f051c0c090f060302040f05100609030b0a0207061409010b131416110f0303270312061309060e1203010b1605 68
    0x4184e010340460b001241c203580041c04001500c446a94480070505400c001800f14490240054078903407112001c400e90707184c42d0240681c450700c1c555149041500d1105003901d82203954001401103840f1460500280c2030071904045c2d070480b841d40c0002c01201d95107410415410741d00a05c2d082c15280d24a2818110b02074110900a65024000700081250f04504e8401060103890707880d00c81c0321102001030010f00c5190164223907508482411070076200d6200b50070080d07000480031282c10752200c080b00e40e210720a50340c5512070f203503260001c1426091030007000309803c8014581c4441c149000c0510b03200203000d03201560f001c102c00d105e803540b206850500344d51004846081651520610349042e14500b4040042c3d8001c1c3c049502c0b00101001442c0764001c4c80381c010103440f000ba403050010031b8144000c10203164220b00e000c2c05101003103010102c3d03001664120501962030a46810040030b080f001005040415540a62210304650605240a005101d0b0042c030b16011209500082d051007401e200d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 627829091 1250 627827841 627827861
    0x70309050c0307081b030a020109060c0c050901030b0603120f0d1d0111180102030a0806011b150911040902010c02060f090a0e0601021905190804050406080304170a050d0e04 76
    0x103c43c0c042e0b6982c2c14007a5034903803174142084007400901260b01c103410b0010b01580300340c1d03058450b41c0009040c1002200d0004170b407482a60350381d074400000156a110144100d020358015006030019103010824035191118090505200030000c1040c10f0321015500117540b8180704200300454000000100d40380b0710b001c0300c000c109855103020710040352810356600508a001c0e011030803040103011440166101e008410040c0007052141e000940258800c0c05402c40050b580a400d201441c05601c5807200a5042c1c1d030b89014090b6164401800d018000003000a82d2000f100c050162a003d640001c1035403a01040c001d0103060041140464031a88d5030981e01c00060290891801070380d296580c041700030040e603040d40940a0a41c2d1900551441a941c109550700003000701882c00100d850110501d16000f402d0b140c4020600020804d81e95501988005228603c0255261810001d1742c00302c81100310700a0f0f44c26800511a03100080010a240c42e9400e15414007c88202c0d80e070011802802c15030030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 627830341 1250 627829091 627829093
    0x1d06040b0301260106080738032413050c0c01020708120106033317060f070206131707150c14070c1703070b01060c0227070309050c03 59
    0x200e030807045102c0f07100050890750090075502014412043c200d5405010b1169a500310b0719041c454101d4a2001445184030304800411040c950001980a42d030400c040d040b04110010a12180b500d920b8086e444031034080d45022150320032800001c200030402c402032549107494a00055242c2070001c159903002034150000c0d9982c42132464401000e500074011010750f07403121000031803054428824482c142403c40301c40f0741a081040031070b5400e0b9080d940c041c1710304000c854020501840300c180240c0f03007450280c000c05060402c000d007008029801040101103512060421121142d102c45200403960005407119640a4600b98008644140c4402401d0714401a0540041c00c0541d404040c2c0414990344c1c601c2c810600c400080105e00c030b02d0101818880c601c09007032080407602c1c170070749a6507040341c01240e01e0000d8a036030300c0032014026480000810110340048055040001c98801800034a0580200403040c400700c000c03d1650180c629400c05075075101101c10080c0c00c00c285601058018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 627831591 1250 627830341 627830347
    0x9260909180712020918190809060a030b0301061202100e0103140f040c1a070813270c050306010c0b06010c0209011511030f0301060c0c0b030a09120804031d06040b 72
    0x404007100020444070b04034000d02940000070842218250002d008443c810054180701f0f041c2c600484850b81c1c40001070303400100810200041c0c0c0c0e0360714004e200900254030045205011041003608581850384203d10041c0f035842c80d80010b81c0d4030303081900121050f00300002c01c4880040101d004107085050101d820200500b030180c50740021100b60303c15846841c5000c951919540300108410401440307807483d010600407980001e2030721020740101e248002042500660317035800304003010100300340542001409034589142689501070350b00344c0b450f60f0030b1040c954141503000030130a0012410140107141000c01140150788900c0d03900e000142c00601100c12540c4540103080c80082000c140c0000c078800380c80f001d41004001c000d440c000c250511059041d68030300f40095400c21000e402c1243c250306c00130f40104000d209a00030358080c1100030000107516015140003484e04803c10701319001d2100000c100000240d00ca250110002102e10001081d6400503000c20307003a00440c0c00c0600319103808 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 627832841 1250 627831591 627831599
    0xd0807051009120306051c050f061f080d050306060a0509100302220b0d05060a15020d0e091003081c020d090203060f04030e010e06091201092609091807 67
    0x80d00481c2c849400b40c80c1004a440c01a10f06a049402d140300e1141c002c5d0001a14000c201044200014000d0191060f01c100d03203400840700341010720031120380034040103c840c4030740389075a2481121b010f0f00102d0014501c00250840150076804000c08003881135a00003400b210b882d04c03507002d54400c9038000e8a001107410982d40d01502a4102c1180310490f14440b0068a15030f2002d820741c14200e880d041c094600d050b802030600b00207800700a0102d0782040795031000040301d80401010164911140d400707401e08040c074520081c00e11741504030552065010000380f0102d000c2440917101160742c003c546030764408448000741c1290664005990341148003003a410300386043d6810198025208138151a203954820814660f21882624060006007026001d41c0c01540200443e1000200040c03445081240030b0001640300001c40c1030140030769440d003c150b0100700080d52408214981d0b68502c0501e0f0319500c2100c8128040c140085204039600400304110b07401e003a101600506001c0166120a522 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 627834091 1250 627832841 627832873
    0x70809180421090605030f06040905070602030301150504061b05100e03090a06020a05100902061201090c0807140f1804050c040618030b0105010e01091e091d0703020d080705 76
    0x208412200703425051610b880c406600c03c40030b030429100d898a99505503191950649008007004203250340240e41e600c11900428403c01125004010340c0c1c3c000c55603581000704c41100b044040e0949000d00c20184003e110280c0c028071030440040004025190070040c0741801403400c2d40c0080c061030340c24078156200610b40004030040100031030507101c00840702d965410490342d401c0c0340c0c0b1000d23040f60445000c00b800d000c0c45801c40c0002c4c2c1c4c001031829003000c18454510155420aa001a00103035840e0720fc1c144480d04880032551000050071b0010285184aa0026083c07040321003141844400107020300e8600c0713003402c0900d103054010780100402c1c58620800c206690040c020704001c02c0d40c40c0b41d8650003007600e00e851410b90f9841010913500341d107840019194280c540250a0501a4403131001ca4108482046030719010414100303d00c181e0302c1e2018220881d820800780110149140085660086001600303800322641035a00700f072120100d0410079624080d811f0010070384d01134a40700c0121080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 627835341 1250 627834091 627834113
    0xb1b1204120302251e300b0a02030114010c050303010b0d1e0236060307170403021c021b1c0501050a0906050f070f0509061204050303100f0b0708091804 67
    0x50345440c0c085468142e0f02e00554221759846804031803000b05600040d51801070350458000d03481e44c040106403107115076840071b0b0040102d81260701903501000402041c0013200009000c00344c04c0c200881803118a0b2105910b0344014010045c070280c00040521480005a001c00d010078500006c0300b440d01d002c1354508020307620800d2030202460340306105c945504005500001003c4181d900036641482410500c80e485d0001000c81d8140311040807c481042d01c9100e01c24881d501c030350b01404070100940451052132540650316011944039824004900c402010703a1012482c04454042c2d00c1d50032442580300b080c50b030500c018910b500b048140000085203801c2000e015200d003805003c00e9445c021014905402110304130001000203030000081805180100307290800076047c580340041c01208804001400d5070f040b160360780000b081000ca92140900180900f201c071034450856407a19490101c0c41c01460b001415800b0001010300351542c55a41401540c01703240c00002e024505410031400703104d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 627836591 1250 627835341 627835349
    0x52a061908010b0c070e06040b0d05010902120d091703070c0f060915020303041113060303170604020c0a110118141e030d0516020a0b1b120412030225 66
    0xc1d00c141c0007089151490090311504031588008041c0f40c5c1c5000c40b90951190098a0f0603000340d41c2c0c1140c000d25807190040081d296000d4400410700400714818000d03454056034496540303030040301910180c181d00018000484110504440480d0107205211341103214041c001014071155407000a41803c00101e4902100c4403519050b50b600da440c109002d603181c440c4007410040c1c00410005000411003030040b6030b4814080c10103003c0c8904519104111601d41d00117402140702201c40190341003604140d030f80d000505550a50801e1040b440c0c03265a408101c0d07006000140c1d901e071344291a40300c2c50600b00703803403606541552490f80d281d444010b1180c186c8505030103001000d454000a00e8421003900c5081030140041c2030500c0000000c807030030380200c221800a0706641350700700f004d40e403071882c0c240c081c09c1900fa030f6590b9091440d45032103484282c404015426040105810013014544003600e084907100c8944d41d0118155150032410f10350a0020f00c00e26100080b4010154458444260103413 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 627837841 1250 627836591 627836597
    0x212060f01090c05030105180703090602040602010b030c06042909060711030d03140c070807020d2901050d120225180b060403080a1806080a0606050304052a0619 71
    0xb9010f8080b00c040c030090040e036400c0380c000e9404404090801400590000c210b00e40080c002582d550380c003090768800c0d1311a00c0140c1d12845562684d2600788040072201e40212001483d10345850300d600510410b60014500c0b01000e13901e0350360303200c801104940e64110000d000c65650078440c5030140e810065003599a000740305036181d42120700c0c02449250042c48000a5480c1aa44d0f803417449141e0307500c540c90854aa0b6414130020f4010b03294900c0c43c0304168030415483c0c0000003043c1c2c8030300f1b510108581d1880941c50100040042e901d0b01d00c01d0102d426004003101c1740d502d540c42400c0e841c188580041c0b42415142034081054424441c070918182c80c4000c206c9890705405c60f0121041e10303404032030103074880001c0004200240d4070714000d24140c01c0c0790a084c140690301842c40c00307066900c0e030b020340c01180d10b0350304001012240744902400341025003011400c5044c1a103880e650b50b4200c260580c04043c40030011001c0503000303001d0740b403a90f00003050300b6074031004006608c2e50b95840300c0000001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 627839091 1250 627837841 627837851
    0x2040b0a0e03010203100302100507050708011a03030406050906131d07020c121b0a1802280210110c10020c0706020607022e09050a05060106030c1202070212060f0109 73
    0x607614041c0210f034010041c40603802486400d5070200f0040c3d9450351401010301400700003120000c0c10a000e044024010400001140011502042e00b00c2a01d80815486500f040006011b9a034010060b204241c80030354a060315105e1038064a0f40c100c8aa030400107001400744080c8404016000b1014800c29941e400d6401540c014010b009581c0300c60780304412a60007001342424503000d000840c00c0e45640c000d106814440d540c6e2190960811203404030068250000ba40c0e00740c02104030003030201c0c2425100078494a001d00ca10003925808680c5039191043c0c0c4a594860502403100c06413540120070700305481c4400704a0a10308020344c88a40400070318001c0640c000707a010f00124170070f48181556001340c0700140400000b50080d1800300601c086a212802c07400b00d903001c1c0d910684108501c80d500401390484241000ca207018030507403110b010503041c00e024081991340100c0c1c800d02c00c403100038056190a001d1001641c490280e15030f0825910a840070841000249699141201c80d00481004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 627840341 1250 627839091 627839117
    0x60e150604120609061103070215130c050415030212010903031112040b09010e0a03080103060e0105150114040816051008060609010e0103150e0709080c03120702031002040b0a 77
    0xd5025602c6071159039009100b5520201c1d50a4000c0c542c0d2612500700010300d00e41c0b50a004903150003c2c3c6070f01c40141c1c4a100b80000c08602c4140c965006001c00e60707041c0e00011a55250841c0741e00ba801250300881c2c4407420068040039843c5004061540140b6640d8001d0604042d5402000c80d6031043d40028182003003000c9500b548007c41301c42104a840d001d807580d645840d800110b6402601418596503241d10740c24800c0400d1190340c1400d8030075030340c1224a500d1420800c0544851805c0d001059242009200b071000e0000002505401c080c24107500e4803c0c9410460700a0080f41c1c0b0180c545d0207025403a40c0041c031508003042c01e64204441c052501041c1e528111a0700000322019900300e80200b09081c604d600610000141c0c103414900070413400c150b0415144d405a03c6e60050300c2c192071801c180041550410b50700c40141c032501000b46280070441001a40e41c4920107000030048100103140b10654500340082c10104152500c01d6648a50314841c0c64060b9002219000024041103a111 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 627841591 1250 627840341 627840349
    0x501290a0305150c040b0a08420d0c0e04031b0308190f020d0e073c0b0c0a1502030c09130608100605040605030a240b04060e15 56
    0x31007540d4000005102c0951804400c0507094030190101e00f642500b40000107041d480b8038000d10102149554a0780d050414031031281601c1d50a038099441c0441c100c0310606003494024145040610284811044003400e40c08075411142c100e0b0090000b8982800129081d84031000440c0918820303a10f0281e82c80148003c03002e0020100c4004001426a902040910044109403000803600002c00200e0b0b00724809418203c0e4000c0c02c80f02c50094650800011140051001030000c104000ca858648a00c001c1c00060b64010940403004070003606200e0061644402e43d450064178201c2a00340e03640c14810949580e034001600e0440707041ca8036016040018565000740c031300504020480a041c0f180d4401040100600d034005180c2c41550765030001071122042000500107032000e00001252030801043c08240e904a400c594005c1e805040440005016400f01c00c03880011600c1c4c002e8509103561107503000e004030416440c1e01c035061400214031450385c00403403801602444007401c80e401307404040c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 627842841 1250 627841591 627841609
    0x501091101051306051c02030f0415020f040e040807020325080304120305070201170a09110603010b0a081b0a0f0201051302060d15030c030c06081803190507050129 72
    0x880c041d0000100f040040c607008a0150403001688180c900055204074107641c12a00201c44d02500907800d2030602c020b0200b43d204040711124603032402d44c94940c071070804503c1d81c89540702e250310031051840054280b1001c041601d140a0703005003642d8200c000500c3c01011500195511240030f016003c000552002c00000c5800719119404002d921403503540341030750642c02c01c01080e818401d140a40401da08180015148214070342c2d000003480140e5418140303541d90300030f034589001e080204014083c001e50442a030350f950803649007844284c0d0317a9002e0045810f0703005444100540e00132824030810382d004240580c0c070119641c000c04c225502c01c40c4400120111040c0690814400c0100800782444c03500504080c5400ea02840e0500395256075a03d034411140d03005640145c1680c90a022050b40440312642242909450b40c9105140360010b0f501c83c400d01003441041043c0c3c0b41d02490250040d4140d034142c81e0802c0081103103145a5840c006400220700c68150260140342c807000d00c074a804222 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 627844091 1250 627842841 627842857
    0x130314070e22140313061803061e0c02010506180f0a050a1103090705030606010203040e01152a120c0b1504150f0503011104150807120207050109110105 67
    0x24041c210345a800d2400a84040d640124100e0b004440004000c50052807000b04510740302d20042d0f0383d611442c042c0300d03c0b02c88983c104508010b20740c0c98103034140c00429004810b41303421150000d0350080c0c002c04c0c000b884544101d1a03032598105a182e10803160103600452007202e05564034083e02c002c011560904a034211240e49061590304041414900703c0e9210a0b88180400b500003a004c15003482c80100c0d40044403c6401981316603410300c0507040c01d00c800740e00201c080c001981070505180342100100014009e58000c10406168417121602c548111000761b20403004c400b603903841d00300044007096078128040d80d1f10030b005426124450301c02e4010343c0d899504250400496106c0ca002c1110300e1043c0780440d070344180c4403510103451503000d2140c94000d215501c00c850001d89003200341420f5503811003003507410141c140000c01150a44007000d140426003440d14503c00d5541c038009880220b2220880c21100d84080340000c00c201c01544000780c0300d8018007007200c440203503000440b03151190900b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 627845341 1250 627844091 627844109
    0x1c0506011701050102101a120304050316081c020111040314060106020d02030a121d030a090b0f070213110315030c0d030e010c0f0605070f030f141512010213031407 72
    0xc42c0c0c0745d080601e60051851a1805202c8100d00207010b0002343c03090071200000f040ca0b04002410002840e0030000d0341c90314080900a2556545031208050f02c40081c014407080b210034003200151914402e6101d82001c180c00c40c0d40d16240c5449041c61000c090030721145480521904c0000308001d0f00000f400150f82c0c3c038540c0114034000c8000401c442010300d0141c2290095107444a4081404082c800140c02c0c106200007592100780e480b600600e00c8059500042480c581001452240140802211a590340581d480110f0014403100d080061000300c40004a2540100c01d1146c081d6049220741c802e00c20880807186549509010003107130310031b04c3c0d20050100b000c01c41103c0d0300e54060304100ba05079010340c0700c003c4101c290391500c2c02074440846c0c41d0400a0810700c0c440c103010313030544188060703180c00c40010071444200304403141a290001d004100080c030305000f010100c2e0b9400c2c00c0c681c686080c803002036494250941868400e82c2003404200c0b400e000200d001d446808000501d542150307100303a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 627846591 1250 627845341 627845353
    0x7080c061b010501150f0806091b09090702030c071e15021905030301050103050106080412031d1603060c3f090507052d060c031c0506011701050102 65
    0x5000c0003100d900107042444001c0d5101c800d680044000c1c032820340244000c0481c400000c0d070f20680205040c0081c480da40130301c8a50b1042c49031035202d202102e03521210f05807201024960303400c0e02d08a1400747e03090440d4008008420009016030200c01341494054080449051075141c2c004544c84400341c0300314039106c8444d054200400a4403511b0b0304403000c2140152800050040c4001c0c80d04a00c16400707444a5000100400065030715100b407074014883d40c5004943e80c201943c3d881c9140c040c1c00e07484001c0588035021101b549141404040075440c80c0301c1142c3c030500201c000304142414a10098905a14040100d04c1b040c2c0942c907118440c201000400b6000f00e41c0070840d00581e00001c1c4d8039080c115180e4007200d044c21140c8038080e5150300950007011201d01d41402c001154041e40050b000790406804c401141c6c40b400900c00b09030520440d0b080d6110740000c900c00d0b2a600840d513039070b402c41c2c020605280c26406551711041c0981d400b84c0e0780303460f003100505c4110240c06080c4074242c0168480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 627847841 1250 627846591 627846613
    0x9050a0f1b0806041e080f12180a140c0604060215060307030804090c0228122a050312071205011509330e040e0c0d03050f12010603050601110708 64
    0x8010fa003280714816101040704810b046d10341180903044695951080c41c4c00040440c4a1107e0022855000c2100030803c00303c0c0d00141a915160304035007500400014400c449481801e20034000c4070404071024008648076943c43c0070082d41e4841070307034100301c1030844400030608a0402003070381d000703490b0400021443c041c60f0803070010060900b141400114000c40405540c1c055482c0045001c2441070200668010220f06000c00c1c9200810444002c0c4840c0b00440220203035070000b4032100200500028610580e0303420700f5415803140b51803000360700300c81d8420041010b80086034054841d81641c010002aa00c070b41403680c60304003000404012450116080008412040c2015295008115044485941015100ca00070324041c018000300e014070715280c3c213a0810340301d2060341c0903050000307000e04880306022038980c0510040280c1040400034180c590714503210101c0c1d150204844100030290f0396190000c0083c04141e803c2e40c002500c881c03095241d9940050f1541c142c0b0214009841241a1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 627849091 1250 627847841 627847853
    0x1e010506130f0b09100c0c0b070c0506030702060f1612111308030a020d0306050a05060c1f0b0f0103140c03070e0402030c04050f0a0308030609040609050a0f1b080604 73
    0x80100000c010403001c0c00c0201d42c144030012000000c0081c010443e4030750615404100ca050003051840c010022250704400103d103401c141001210400040f20343c2d44e08403400c00b04000302e02a00700d00e40022001050010381580003a000340f040300700440201c829110400241d99031a07540c4418400900c2d223540010701d030003e6520621009850039031540c6001c3c0a40e80d0701c1d600541c640d001c050755400c00320700a103c094041c410650b4403015403070204912814000050700b440014080e55001e02c0300131992105481c01004410141074076900d41800c40e440300300b46400503105c2d88202c907000ea04948040000d550090052002101d244224885d00355604041c488140d08003c005508000300002140c0c0951141e20056000b00d81c220003043e65682000107220b40180c0d0592560b0050445140800c081007181e4141c0b60045d804880700e588903206c60400074040c1420b00d00203440c9002e903a41d4101048440d0958800781442900004955103002503040c1c040c15180c41817000300d41004000a001620b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 627850341 1250 627849091 627849097
    0x53a03051c1413060b010f050f030604060e100f0608063708030309061006090915090204140102011d15191805190201090303050c100e10051e010506 65
    0x7041500003200360b01c2c00000b01c040c00c42500c2d0340403401c0704403001c0340034010390f401744a1000100782004150700c0c1d41c0d03080c010841d120b0394102494520b804070200340940d8407504180010071007a4095400303424900c280035160140d0344542e4000031000c000c0000e2050060880b2780c407400c001880b510f05c0c900700001840d20b40041010302c0c90360643e445c0381125200150101c11010348000c43c01951249001c1d00a10714150028207103182d110a049030820540b07601c02d000c44180c800c8040c000c624648001c88001c92910300340c103c069014000309022529440c05514070600000076402800103405000d00a45000c00940720700ca56500404850210031948004107034101c501184c0c242100c0420359009803c42e10b0349251201b814035140c11082c01d02c40d00300120023030411100651007003a559940060410307951444021b05100c1c01007078041400c0414000e0075101d00603004284964820a030348151640f04080d650b04006141101284450543c0700807178190f40004448504241d092070208241a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 627851591 1250 627850341 627850387
    0xc0415020705150d180503071709060f030a0b090411010f120c0f2d120f150915031205160618060c020105070f03020d0204053a0305 58
    0x2218448002a0603150088290f43c070703990321280d26031140110100c440980313400340c4a0030240745a01c07648002050010045856450f440b1111829403030551090746054050094070716800742c0d0200e262404c20300032000a500c28000380200b00310f01d0703c1d448100840705d4030541d0050304c012214605e03003800d075005011910b28640182003200c0340448402003102594220301d5000300080104507409103080c0c200004400c05d5900004c0c081001080c1034075030790b004c411904040100500680c41c03003001f100942c030501d5000030140c000c0c4072003d00b07041407030300380481c62240c0011646404100c0e10301a400400407001d482d4440703008101035a41b002d08440307036003050580c0c1e02c0000b909117100000401600c180985284d50b190300c240c040c140c9060110458000301650006c0da4100002c00051039404640c03451024203604006840c1c034404950728000340180e400240d04541e400284407500c0c0b180141d003d0450342c02d1002c80280e940c0c003512a00c0030308e40d085002004501d0a210380302c989606075041000c81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 627852841 1250 627851591 627851593
    0x3010207030909200d0c09120f0201080c041e0509150102120f0c0618122107030615030e0d0201021e071703041b090c0504050904080f0301080d09050103050c041502 72
    0x41484c40001c2449070740600d40c8903003a240e9a080032141c1e1030300b00403488014146114411400191b948030404c1030b240d504030027410400d0541c002026007040e2400ea0700035124401403240e4845402c1849946403860b070040318800c0d1029400107030580550912081d101d407041e0301500c000260354020600c2d07034000703803411440c505090142c141c0e45141000114030501d8110041d41172140c00040c26405c04018052001440b0010000304681c0411103030100c0d250f84908020780344030382c1d6407c800c40c010800e9410864480c240110007800c05075054004c4004005107105492507200d0214090b403c030b11901c450900c20352034450a0303055107409040030380201030103000f000201400b041e604008650044400315041280b00c40c04540c40803c0030510809010110006c0101c800d074604003502500592081521580c00c910006040040190550f6402103038100348545035612100907030b80301d5482180410028210b6000000c480d0311a028040c02070300d4015242e46000e0130302d08a00380303282902e00b2500035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 627854091 1250 627852841 627852881
    0x61403031c0e0a030807030f0b06160204141006020c031617070b0706060608090703051209062104021503061309080c15090708030f0d020918070203030106080603010207030909 77
    0x11403000e000615441d8401d584105084c9006c40303014081720708600c82202c200389060303004040b41d110f20044907000901d0f002c1524000c401807000501911800781c1e181c1c100c2101000b40072403075500c0400d640c10380d250713902500c0240c1040000e141d506c51320450320418000b45407404001002c031141d071541f80030310000d00b034070f544c00d8460082100310342c0302080899031150b030780740200b00991b4441c5405810010744005010014a03603100d05076a0070781c24103544c4400d20000313615601a82e4190459850714840c54030359859031040305558101000803035069004901c00136000540708861003c59100d0344008044070441d01d0b600c1a003100404c0702d000200c0b4801c0c81004510007102080114043d02104200f002609240c50a855030406034a40c1c070040046d0300900c4107031021201070043d1407000c070340841c0050301c4405030070004004a420104100c03101810700c052003042980480114182c9030381c0c0c0c54800850711501c050608034800c1c4607001d0001040101e05000c070402d1600450585001845a008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 627855341 1250 627854091 627854111
    0x60a0909031808062403063c0603280f061d0c0a06020106060507330c08100b0909180f010f0c0819090510020d020a03061403031c 57
    0x102d07107800c540307030139840070017000003a50740781440207640307001003d4031703e505101030021940d5840042c3c080154504010a8011040d1190080c9541250400c0c102d5a0b1000b03041c000d03218003c82940d03a18081c3c018403205100d0400c40c0ca92007000710341d080c03c0003810390805032030b80c540c110b182c46c80440305107860f8055580d01b9120110420f1a00f414400a0040030904000700003a4054940c040c5042d641421010804a03411006480e201504524100c2d1128402440084c03180300c4074411180a00841003254448507440d400200441295200c0280c03944031840fa01c000031009109031030601c0c20810800c03c03203007070003021541c000203203013045415030120415090400c1641050482541c0d9982105650311245014030700099085082841031820259840442c1c00840e840702905940c440c002501000403c1188124480b00d0400840d100d070343d080380000180d0301c5840000b00284c1449408142a1103074a00400d0083c00103000707518022141e020324141005140300c85c80003603583d01c1800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 627856591 1250 627855341 627855377
    0x11070303080402010c1a090c0109060f0c1a1911090a03021009030605070203071506050a0b160204050c1c140a0b040e0f060f0106030e0307140c0d05060610020105060a090903 76
    0x1560021b01c00001d0407a00d8055462807600c440300c1c1d841810800f03843c10410200740c1010501d1841d580c18641030000c80b815003001e001c000000d480020700100d0850401c010401c042080240070015080240109034202450030003900803000416803041c0b0807d420001450084080310403030341c0d1820101c0d165507480d02c1e0981191011100480541c01c0080c0034420000a0601823003800c20507a42000300c00d0600000c42d800d030310140a081072030392001640a507000400c8040b07005641d4020400d005d5480c00b90700420480c0c108008a48040d90403450f51185641d00e40141c403500145044c061581e43c3c2c030302250101030900a81083c0d04195501395500c0c045500740b0030401120030690003404141007140141200c100c05a00c610b0030585882c40260700201d0200c101c44603d900f014103000c10707140b24200e00d03081116410700d8540c0300701400340800812a011510900c5082c007122810207241c0b180505900fa1041151150392007480560284603d4941d6882810078a000e458600c240040110000f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 627857841 1250 627856591 627856613
    0xc03190c120509010f0314010e040c0816090e0109110f04021611010207120f0f0c150c060e030403030c060e01110d0218150a030b04110d0209030d11070303080402010c 73
    0x141c40010700000f403400c00c42d40c0209140710b0980c41c0345010803054000814580304410180541c00513200c084e008902802416074481024100b41025200f01d03070f070707082804941480c0b00d00c580c041050a15461018940d4103204820441d40c03c035140900030071200c41005201702704810710716071107a401d203c0b950128551100107c441ca11a411240480380301c5000646000c515911000503805203209140c0041d040b0b008201c1519030100301441d203040b141ca03100140b03408581220030200740c2940d40e40343c11035001600c1008a4041c01c805c1209030349201805071244218000500400e070480540c2c800580250300c8a10b0710304c100d000005025014001f0580c03e44c1c0102602018243c02043c882e104204016040d00803810480d0510410801c40f420300390039000c2c40d0111820b02d90345103080842500c6a80042c080e0008403400302d17507143c001c40210002500030b02c0d0001d00034440c2d200d4503c000da001b907020075070080d0301d4401080350519650b0101d401c604000c00482c10001c01c2180030b00003c14003e08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 627859091 1250 627857841 627857873
    0x6030303020909130305180402191806020102090f01140403050a0c03060f021e0a1403010803071a010803040b0d09170c0c040b010516051903080108120c03190c 70
    0x2580d20b000d2803040120492001d00402000d0304100214000680c11804462010030b02c0c083c1d140f0318500a20000e0003c0c000c100c580c081d00000100c281c400168022000b03d090b81210350700c48111038581070200d08034003450708095048006c00428101070341c010401c0c058421040c1c82c8042c903054030381d5a1141408909441142c03588080007052080244500035140650190281141041c808501c501030300300b400450000d004600080d01c03031405101e0380c1c03030000c52080000791550702e59540c001c0729925031192509a500940d4480100c0c01000490800ca04032030300c010065044c13500b4980446526449141c45001940c4d032040c800300040c132150b8041042c6400301180c2501d558400f481c080c00c141005043c28461464803640e503007640c0c1c00c0000d40740c002c2c4095004a80e0b08429103825031a000c405440051012140c9064108040d4000b00a606850b03910060710700c0ea20b042d80a18010f800303000d5821440303803c280200301506040d091040b000e500545419100701c50b403616100455402480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 627860341 1250 627859091 627859097
    0x1401110313090507140315040207020303121519050a09111e090f01020a020d060b041d06041b030b010905070c1a01030b070c0213050c0705061602070e04110d020a09060303 75
    0x404c94000d4100e01c2c0101981c81a181852541c603111104807050710104004a12540e800304040c41551001c1090305c41010000c13614941d0340c200700741c04049030b000c030904562180c483e4407020348030307103207051f040003f2202c0c090041603c06091280701c1c00a881c602400f03003402074003881010341890301b1124009140600c0003000c0d90ba1099481070101e28501c1380203840c107551100540300c00585030387c646204007039003004001445010000004000d0040b91404908031101105608894003012400c0c500407407041c0544040c8034800350702c007100c0000e0352001a0080a004004002025036500403540c010782615100074026180d40c0d81d080f1110240820240003484880144100106603000c02c0d0080054140240100c10300e038005080390081046003611f40d42c5840119240c42e1222003590b0070180e0080c00c0d500d552600440b545001070107600014018402c400c000240020864903290040303820050b1b548840b0030440910041420300c1e40202d800c81000c080000700341d41c41e8887c1502031803083e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 627861591 1250 627860341 627860351
    0x40b040b150405030d110c010f020f100b04060617040305031003020a0e04050f1204030201030e010b06031905060f0a0e18100b0901171504030329040e07140111031309 73
    0x70b418180362101345511181440705002c5001c40320391b0009020080700400346015070350700809007012401c0c2152181043c0481c42002c071426803565850b080030345240300c00ea9040103210781d00c2030100c07403110b88181d1051007081c0b140041804248503c00440d4010390088001d01120b03600d50101f1004203d5910403000321105c0000d01c420004103000201c1540c603018000c11078150455985015840b1303502c0b009051507030742c4480c6900340c0300a4000384046d043c000c00c4e99461785030880d992400b022109844514880c90000041c21138903080c00211400e034406000408003031304002d0054040700001d0300f0140c441d000680480c0030381004025400d0801c0c00c1d90004a00d601c6d030703c5c0c10b0118035407040e0403141c1c603180c00389482034400c680000c01403a201940754005e80a500c0c0c41c01c007980100081c04401e109030f000150020301c1d40ca00103041000c110000d44040202c0c80d4150941c540390301071805000d1500c1e01d9511105420342c4a24400e180d000310090580c2d103418202034124000d41a1a444030346055121 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 627862841 1250 627861591 627861599
    0x150702130204080a391701060b041502060c03070c060504230106081908031b07050109050715211e090b01060e060309060a020d060803030f010f08010c050306040b040b1504 75
    0x60758950f9850341001080b000c641040b035038a03511105d050189400c080045180c07608610b07001d402850040c0b108104081d40c540d1203941e070500c00e02401c01d41c1005849444007144640c0002012644108801d44c0d61213805629541c44101600c000340c015985a2000c49200d00452440c00d04000400d0b41035000003400d0f132030050b4490400811703d0b072403e21003034641440001300d0a4402220380c0030420b00e00c2007854446006005d49036000381c09010340950301e0041207000304800041c07200207580d0030b040c1d031064035446d80d9002c031201c0200d020003855803445051180180350340c903000307211500c0c107903d400c050520340d060b481401c44000e80b1041d50315905880040001c0d40d04040d0031080d140d41990024550b00d0304844080c0c2d5040c010f080000090303400201d12a90250b182d0000c8081c010f840140d03075613070601501000f01e00300c003801074841d000003022000a02d0001441a1113601405844060540e961101000300070240d0308280341d0001c3c0c486104c1038555030b4250b14842e0b0030028002e940d46541c14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 627864091 1250 627862841 627862883
    0x50d050f090f0a0b0a0f0905030a03090302070504050114100e0d2108060a030b220503190e0d020f040207081303051504020d1212020a0e0f150702130204080a 69
    0x15852002c065400c00c952000c003240031141640e510009001c40800c81400e000c11220052000d503a0140403804041450341d109941900000c050030b010b81d0031612116203c50800084800c03e100f40d46010341e003655032680c40d003040442d4100b884240c1c108100c0e00008000821076404801800f1100303412028440000382d040e900e9075001203c0c4d00d15215240385070131801b0030b458000381d020240c00741000d840000d4036611801d000c206d91540101c2400141c02203481d00b5581ea400c107071002402030815003205410103109508580080388014141601415a43c091060112044203407641084e02040150040b0f0400c00042050303a500c0f40141130007a28500b092824203c04241140ca94640304050002590342e0307104002d400da0708012800b08040c03103600b05490f400445608c600c412800414010740042c2c2000c11000902d40590345458140c050004007c0200e40700400d5841c09141802a0400740c02c0008940801c000303c60380041c94551581c001500d04002c08000f284d1b4034241c0000662001c41d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 627865341 1250 627864091 627864103
    0x3111002040f09201218100b01020f1203070e0307080a0f02090a020313060507030b0901080c01020d080c0a030c02194e02190f0318060816050d050f09 66
    0x1560209103d80c0341e9280110b00128445c0c00b1120071500c80e84c03c045110340c0031100c56500e0321001034048400003200180b0400192003003004040c0580200c40004d0786542010a02002c20f02d0144d1844c1d28566a458007920644481500c1c40d401d40b1504a011800300010098000414081d242601030014548100a840c2200420340c0d48030b00d006009001c01e18103003a0181e10003a501c0328021641d03079610b1070701314020842021704547c040c0c00c52000084424010a290400250a0b802d4414a00000d40f042e10038000585000c503815000300305c0300e02281e100e6407015544040e01d01c1504d032030f40700314130440c1042c0007a44003d4408031703101030718081001b00900c1006011070074102900c400f45507150800c1c0c401080105400388180e4180140d085562091101c180c0c0902c910303a2481c01717041c0324203015064004c809001c8010556042911a40c2c445611209040702c0c0e20340d0f980d0046640c0d006189800a036000c9080080c00010f000546151056004482c429800303036102e01c0d1285012b000eaa0700c2c0603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 627866591 1250 627865341 627865361
    0x501360509040c0e06010c08090607021309140d1701050d030c12020f01060914044d040b031e01090803090303060a060306050d02060304111210050601080106090303111002040f09 78
    0xe8200000c8c108100fa200382c0002145e540351919018008180c19103042c149500d60240307410b401c00c0030005c9405507000c078015140c0c1101c42885004205031680585041c030184808004e6004200d40d140c1081c0a000640c42450f06004c0585030361b4440c00c6144915030a03e015800c46210390358000300074410035004144809040c00f140903400d00d12000c0d014003030409080c807681e01c459000745e50600c01a02d10017a042c3d00301ca48480c140340f100d0126116565504500294080000384094605801420302010b00100a0311000804104540820310a1a02d0601c0341d500d0b41d000201003403044005e1485240164080c50303403883c0c1a0308000d816000ea0308008149464407409010030b071103204000d10465810380e40380d50344e0740720340c00c000d043c90360090403881c0c0c40209030060231042e0801060110314820f4001043c0140d403a14401500e4400c024050400040d0000d4800c002082c491074210301fa0206510954a6016003100c1d404141d9000c0d0f0001d48280030300990401c242d44075031207221454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 627867841 1250 627866591 627866597
    0x30d050906070c03030c200c1e090118090c090e060906160c0309090c0203040302010815090403030515150c210301050f01051c14010501360509040c0e0601 68
    0x81c2c40e1080010b0030340240c181c400380c109a03542d620f2000c0c90f07002e40036895a04c1d43e16021042c00440b00d40310b0650703900303010109a0094003104041881810381032005e1561b010000c001c9042a0300304035450040e03882c2003d034402102e07207490b41c6201041d1061b481c03002900329450007164409100c07070710324502000035000200c0da82c0311404010030010940c00c840c0d60f92103189000303504800700c0d050844140b021900000c0c00146000401d1104980000060084a10030b8840500700d40e6101c10401c0c0c0c001c140b8542903085038481c0002000603200741e1043c0c0c0c4c04001c01200002103159100401e40c1000d0405420b500d40100142001c05a03200708044c4c001c2c6144a40e88605104050300610b000e400181304070b5004051103c0c0b071000c540e01480c02e46000280d80108041d04450740c14500d00941107582c1c05403100c00000c000480d40b03520400056072180c85406494846250700305040307444024aa8138a927850aa03004041040d43d1110038050080780110201c0100384d0a00003920041c0d18041c2685040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 627869091 1250 627867841 627867853
    0x30f1106090d02011d06130e13030f030b041103090c1c0c0302060702060c0610090b040e030a0e120703030201050f061c0b10093306051e09040c02030d0509 68
    0x1e1950703450381103001c1503428a04801e5000001c24445900d4042080440d4405400b02d0001c100b00d4031800c1d00c00c01c55900300907542c0366403950380c04101e400001000c05000544211042c8202500a4101c00c0141002810026000c1a00740c98000c1503081a14019016004101d00b40060b19000815840040b08400304141c00304040c1d4cd02200c24142d8480280102c130041041420346d904d900c141e03110708040c101583c00625000001200b00b142c0d90041c0402c091402e01e00160f0750400b40715001d09031510030001e6142c0740010100340c440c642c481e840140d02065200e4126a840414031804ac011440781d000481e01d8104207444415150004080e24002d5030900422580c0f81680e085c1a00c40d030f030704003078400c0040c0c545404400120b20310750800c568040c04d0220161241d840800d08285414081c41c1424540c0d06148650301e600d40c403407142e140003501c14403007980384411a9042c41c00318461480e040c1e15260314000450300359003200b8503c00c0540c00100710b001c6850043d019942e440f03d400e03406001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 627870341 1250 627869091 627869107
    0x9030215010b0a08091002030108060421170a0b030f070614070308040b101d06040f0b0a0b0f0d11031e1b0703030e1204090b0d21021501030f1106 64
    0x45000d450380c100c0c104a5a0b10115800328014021105d4001030b0600c00d552300e68403000910380e01c260a40781140c500141c0200702d058011200b0b103000b60740342155039500c650800c285c80c030b5960300c0000d08280022984e491f20f040050f601001801c0302074100383c020b805682e28141d0040d1488964240c1242b81b1070041000364006070307000e01800da116034440110119030304c410b040f05007a0000c980000c070b030030b2500c4002120881c100800e624480d2004942c1400001c170328191840c192884805190380100c40c200044c032181000380c0c003922014140d40c2101c0c0c1484e13444076000b015104804600101a04000240180c8084400031a00c800c090700380035110604001d10701104201440e1244041e082011410404040c865000141d1290401d000c0300c91071720807105d8103100760340300c0e2082c4a201450641d042400742840c582c2e2045017138011125044564620b40c40c01164499800c8050460041030705034416050b0f516a024080c50040400b0f0407408107030301d801e0501300060310364a4480d84040c82100c0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 627871591 1250 627870341 627870359
    0x5030705100302031b0705010203060f190605090d0b1819030c020103020904110a02100f0c020703080a1e0903051504152c0604051c090905090a0606090903021501 71
    0x7040740380315403900590326503c00400040b90000060100500c140000c2d0300014448150040c6026250444d66641d00795003e0080000d010f041507954241c01640c200200460760040018081c400b1000d45244403071485552241049507048a00301140c2400380c050f000c00d00400c0000d43c0321900744030300c6001d00d0340c950340780501510383c407400007410142c002038005920740307841d0001c451240501c20041e84464116801a44992008040d00c002901c1c00c0300950000c07280d8000c01000d50242e40107808a182551941c940070303800359820348103201204a640c201c003001e0701c503848003207607040e0b44040915041d40f41550804c40020051401d00c588c41040c0404107100d880d05a480041d0080c00141c1c40c14500404007140c0c044140c2160018608981045041408a187c0d0f120700d1080d4243c0d020071254081d00e01803180d11050410020b40c0c030482c2413000c00741c00c2c1e010035009101c07c070440354400c681755100000d9032444e41095160301d1b1503c2c0030300d003090b0301007080507001c0031040c10200c06981003403400c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 627872841 1250 627871591 627871609
    0xd08030a020f07080309030306130209010e060c0c031204090f14161125050a30020603070f0e010e01020d0e1c05010902030712020d0204110c0604060c0905030705 71
    0xc1040380d0001d000c42c0312050703103402c8400d070700d5218461503100e20745445c4940e1650402c941850050ba81081d4145410550b84202c50304228141c4640e2001040c107014080c080d0440c42ca508441e20035600810b00c030365001c2000301202e00c8130900f079a40e910705020910701601c17183e29020407018285010407058030703a03618900d80e00013800c5103552100b110240c022a07030f140700d156891055015100c0c201d00c4102d121507152140490904d10324007026501c4080c8080a01c462041403c03002e40000311002c004040c92aa9020700051405025000f400c2e07000a45154025101c500104044154802000f500101300c07000100c42400c04548046405001030b403a1227a45410400f006980340000c452550345d06c2d441450740c0318040c1c000b5408449450200c1c000d0449090980c4203100350b0000160040b1201a14003d065010b00f0f0900d0100704e0368240701c06000c1e841e0410b040c4210500651054000c10050300d44038a0003803001040c000110180900380c0321207500300038040d420018003800f550b2121400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 627874091 1250 627872841 627872851
    0x914070e04110301140711190b070806030307120e0a1d0115020106080304090b0108090d090e04060603150504110109030c0b0a11070612150311041d07060804110d0803 73
    0x100504110b42d07040000d005005040a11000c000e0b0042844507007a800071284034441c40500c1160900a00951b0b08454003406c03020040c000010a80001c0c03029100c2c1400c25002140641280c2c2041c020b50b42d1801811f9140102e100018000000c4103000c0c81e00440d000e0041000045030011959688075660514105014003600c102404101812140c800d40c8850005c03c00f1806403a01c854071081800c02615042e00f078103000680c0c034000300d01c0e0454040340d40c51075000c2a0f1a05e440760340c90b0502c0d06890080c01803055400710f070345084c0040401d90101e480e03022149160380000300e61600d0b15080c603404001c1441d550401040c82424000200305074580310541d407040c890181c40d00e50111003299003d80c3c1186810b060b0180c00c2c4000340440d000b100c00f000440341c0310b13403d2241035488940c1d1624120781d07100c054401c2134588a10b4085090950105c88564420782901d515010742100030b510b4922994000030000364150100824814482c43e036070810481200d1007240c800d03441e242d4030703840d01005d89 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 627875341 1250 627874091 627874103
    0x606070f1b050a0f090608060c0d0e15071709030322021f020708010605040b1516140a030314070c17040305120d200f0f0f0d0914070e04 60
    0x40c00c0e1820752407400741c2002031100800041085407240c0212440510900c0342c0f45010f414044003040d00f22001c2030312403282c40d00c0c45049003080c50600e03101010b4242084850941c1c0115a1800211100c40622a01c120040e80f6503400541360400418424100249400025002070040c040f012081c40100f003c10521000313440400021070002490b55407410040c00b00000c901d01c0502c080c260041441021100864001c10180d0f545509200030f42da00c410550b540440304c0f906e1003030200710130805020a040480b8440c3c1c900c030010b9840d04030303189002038440c1c0f15a220000c1c200030140c0c1401207020303075120f9400c1e02010782018030000c0c004852407200107010b40b0040d010020418052070a03500159001400ca8a013a10300e10603000203a032005010040341803c040d9140300780c03e1441c0501c41c0c41100880e034146040c4108a0041c2d89400c04058406004400c0100110501d01d0102602c040198078400142c008001d04e04000d080e05550398120054110300020440c40c3c4040c80000e038440e420a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 627876591 1250 627875341 627875363
    0xc0d091e03021324080a0507080f03090d0503090d061d16150507151a09100e06120111040503070f0b070303050a020c03130501090b0408100207080c0307030c06050606070f 75
    0x70b0490740c584c2c15880c3c1c514042d201d10940003030b0b80500000c0c00d0002a001e903065840726502c400c6041d4a980080f443e281c0142c0c0100601c01181c00d204c2115410580100141d0741400343c0407001440d403540c0e00c4000da07001d603218a0501503180701c9030380c110304d074035450001020140401c242c0084000454458001c6800c0c21802d0340140a010b00d0031203661a07070081130602d9140c00030309030000a080701b41c00d84141000e9502080030604000428a00445080d01343c1d088a52902206040849000f85115000400c0c10720303c07415032030240900c40040d1080001c40351114105000d140c41c00800d82d000b02d849444a0f0410041012020100d0307184582500c0e01140030758400703214001030722030403039000202d11000030305401000030414824203442099881385007091f51031111151034082c6004004281c1c100301150090b00d12154010324189205601250504a0a0070311a0035904440c0d019800300e03a999044104000c0c3e94452942d20100842c1c206080c042c0f00d4484d10340307950100400820080d028 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 627877697 1106 627876591 627876611
    0x30c040e0a060e060405060406080a05011b020601051c020102031611032118030c0d050d0201060909030906120e0609030a020c0402070f08030c0c0d091e030213 70
    0x43c003d0210180c445008010081c000904000e5002e0340d2040001898103090040811240c084d50000502c102641944043c101050b02a082190040e400600c100d650b2044a9071610748200c0310800127031310f144010b03461489144030040e038601d1002140000c11000c02240082c041d4168151558500ca1580426000c01d042c4042442510184440742100445005580405600808071a064a075542c0072031909500c060b01a01d82d03811041620410503024040c680051400d1081040404400d48008106030464011801041603003004e1043d101740d079030441c2c00e040c4c0152003962807030b06010001650320360090361514058007511701070800d40c2c90503100b0f4030b01854004040c0c844000319a030381c0f6401075000601c541600038040c0028804c010081200d903107618825121622198100f40a507245540c03460250215880040c50600040c0c0302c8800c1c000403402c000001040142413 = true := by decide +kernel

theorem cover : BRFrame.Cov 627697841 627877697 := by
  have h0 := BRFrame.cov_init 627697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 627697841 ≤ n) (h2 : n < 627877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
