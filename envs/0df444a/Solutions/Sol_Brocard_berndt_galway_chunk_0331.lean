-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0331
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:15:33.826976+00:00
-- url     : https://prove2.me/submissions/cd002242-3916-49bd-8fec-da558f14a1f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 59352521 ≤ n < 59532377 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 59353771 1250 59352521 59352529
    0x60c0d08010603140c090d080c010e010e06040210080c09130f150b1905090d030f0206100f121a01030501051005030604020f0f0d060510030308090c0d020f0321030402 73
    0x69000d007043c545446110021903000101c500e0b03000019180c801c0c0d450b0100300c0401c1c203c0c004100050442c0002103110103000006411840d040410a402030142c0503003901010b860b510143c40095100d001c407001e075880d0b00c2c081c501d41c0d6030010440400c581010b50b0301e404125451005002d0400c5503a40d9154140c50400502c5922941c0c140c40302250041403c00500400c644104c00da1042564401c801c03407a00303284144111400700030050040780c40c00205240c050410201182000050300036240010b80780d0626880b0101260320030500100568a04140f2281c1440b1020003951442c0c41544281d140400c6041030314000c40c03203580002014074150101d80612400f0350040c1340329401500500000d60746080e0407400c1910200c919001c14840a0b0000e910910304050040c201410207003003080c44420542c1440490340aa04c80610a40c4c1300b402050302c071108000304540c850003100d410b00160910b43c11100c032501d005400c41c0c0b5609290701c0380f00f821400200f4400c06a0000100704011428 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 59355021 1250 59353771 59353787
    0x313030f0305060f0105031315021206060c07090c050705250f060509060307031d01020901030b0a0303020a24020d0204051201020c03030a2714010b0a1401050f0405060c0d 75
    0x4201c0c9410416800e100000401121400e25194104000403010544211f585c141c2016826403040380350396078594420406029410925801c54041c2803c000900e0070b0134410211ba4403040500e01800201e801c00c16484010618100460304002c000d00403030001030030800c10f40741000d2050303007040180350300c20181306840e501c60b400148258420b90000c00c181c6801006580800d441124000d403280d03180c0c2e400b01c0c000d01c0c1392504001170500e000740c000e80180040d80103181c200300030707601400f18174071000078000d900d8464440200181d11050410000c580740049640342c8002c0540c0d80340910380102e410a083e40c1005240d069041d40c00682000715141c05098040440e00c0c040c002d504190906c2c8100d9101e01004088601c0c0f5901e494005280f01d900d403200320030112403060120080a154204902e241240019140066180100240c80c2e403402c0d06491f4101e64154205040b001030704801150150082d9030701c034040c1c6600b400040307549c0d0b0f11600640741c0c60400000800d1070464141c4002c184c0342c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 59356271 1250 59355021 59355047
    0x40c0b1605060c090d0b0a0e1e0115030f06020a1202031006081003030801060f02010204030f0f0614010f0501030e070512060601081005130e0a02040501030b090c0105120604051b031303 81
    0x8011119064540c10303005d20500341c0000000c0c1c200d40d01c0010600c05010041a8184075006614a51070350307205858100c01c100589000800440150380c9028011251780d000180070005030300441400109250000c1134008003500e020843d42e401c4044010980e0803e49100b50a000050320521040303a01c501100d40c8581d82c05004e0b56902d1442d20003801d00c0206009590410005c4595030812314000d404480003140d0255011a50788601c1c00e080980d9082c0707100031101c1c10300700700543c488402902c0c2032030305031011900820300c86440d00005400800c803112405440e8080c00d100016181d0300c03440b0f042880182c0c44090070040ca0100300040400300003d04d1518984000316007409035869600c3d030b0000095410800107255265105c13524035000c1041e4000b03500c90b091030000300030040c0c1d40d40c21074051100c0108a8034110010390055030785020300242030000b1800d1000156075031a040d0441900150700b201e503803004020040861255600803180c003520007840c400200109079000c01d101c0480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 59357521 1250 59356271 59356291
    0x30d23040b07020d0c0807030f02030403050f0607080c190522080f010b0105180108070c080a0201061502010911061303050a0812070905010206070f02011e09060507030506010c0b040c0b160506 84
    0x74002c180c0e1421b8a07801045005010001c1148240103c18020002c45000c1d5410208a4128803025081c00b41d0390203007220302d031000515a03804501d04800c1c40050350800650745c00a409109030b8410100e90b6504280348000341000990111070254401641c3c100240c10054082c01d00c0800c0b800c1c0361405e40c1c0300041c0403410010304100c1051080c19a89c120034602c002441c200d8400c0d105c1180c1112a1035401c8406000701c00001041089160150b0000c01201e04002c01d030501a145103500b83c2c03c8034504d5101400020082050b00d80340d00c1c19200030b1a81c083c04840c00c1c02800e44985030366103401d01c1d201c412900402c0000300030007021102010070350300c001c280c5030404280e41072400003501c50b10041c11450601615a02105195000390007400406414146018002106104c400050110f201040d00d03400e14107400300d00502c2c82400390794400c5006840c0da0608211643d1010344e0700d2130090041d2004490b4050110300101e02c1390040681c0000c01c80040b64103c42410302c103042c0000507100000c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 59358771 1250 59357521 59357537
    0x31e0506041511040e040309090c0512040203011803050414040b0a05090a09170405040e1504120e03070b030f0604060e0a0b0414040c080d0201020903030d23040b07020d 74
    0x10400540c440e4071a6101c40780002d1041800184005011030803940003c0f1140414003280b9000c40c625000c1c4114081c0c0d5841040507511441c100490b1100c1d4100800224200304400640a0505915401600c042c0000a41c1100349141090501e0300315001c400007080010704100551608580c8005103804903010494407099900280108070300340301d014021505000000c20790211343d813004098582102c1c25464030b0541c411040219401402110301c107034500100d4403000440004c001c1c4031041c000884803c192129142c200c032804812040b001042914014030f50203071001d1000340000c050403400385071a42044095240000c500a154038010391402000300140c5001a4803650000420384001a051064002250140012052040c005081c0d801030008000904410904982c56241038645107440c805d0101c0c02d0303210740100c16500d40d009100850103100ba40d40240801c465600f0524200308110410f40490003040700e0554112840c0713003c018107140c0511484441c1e08951510900f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 59360021 1250 59358771 59358773
    0xd140f1c0503060907120903120c110a14030f0406020304090b03030702030a030302180a120302150f010303030f0f0c030e16060504090c022118090f0424090c031e 71
    0x76800020001c40c800c0606001182d4054010380c0b240e0004c0d041c1040500009880d800d01400100860403071141c403603e80412010701e9481a820708504ca071000b000b6004050040d10307100701020172038801c2200b0740420040840b2104405004100500e4950040c681711881e1920b000101c6100700c6140303000303404c00c00903100140d4000c50480c202680c141001a110740d96414642d200080c0c40da00b5540204500002150001c090301d0742c010f00c18440e0342103403004241c0d9581c52913854400e40b0801c01d4101d80600500000e80260005803420303008400000d01c40074110104016120049074035004291b95055070250000180000d540f011419400c50b450549440001001446507124a0780310980e10040c00f0346c094801d00c602c100d00c4040c00120200c80e01d00c600ea5010961101d4543d10712602500e10206660500d411080d00c9510040b070071110a030b031140c03585010140c0b81101801c1100140741d2000c440c078800e104a80105005102003400a07041d460102d081c100c4003c110301c069074042507410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 59361271 1250 59360021 59360027
    0xa110316060e040507030e0706020307170f07120219110109060201020408190503040806010f180b06070308130203060702010207030801090207080a0c03050906031501020d1403070c020d140f1c 84
    0x1004404283d50000e103070f98a03200c2c114002d04288000c0301140c02380580015a0a07800005040014002c0103120449501000300000d144228640344a10282c107114450200fa01800894440441c0340140c038110b64194400301031204042c801251004690542c00f60305582c00410000034111a00007185001c0c1400c0000759100000250100380c00e485088010405c00705206a4006180c0c0c8012a441542c40e54207005010f00c1500030300103002003040e881c0382c00d4050307401440e107450310284c42c107407a01c045601d0480301050024403803004055503912500050b1401c10242e0300c00c81e10381d400144c0318601031400130b041c1441a07002d1412580103200503004039080004a81c88181682044e00421f01c0f24501610300c1c0c042c1c1c10f4a10703440b800c0402040078048691101c500840c009909403141000b0740c800648881800c40e100241540d400d000241d5054010034115141c0c2d80000e140c03124488140d91a04856031000b00c0b10f40250b009020a203c1441c01040001201c18441c0031020340121000402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 59362521 1250 59361271 59361287
    0xf1e0319050103021c0807060609050105100c021809031303110307090501030203060a090c080a05010204030213020a080a020c0f030c01020c1903020d050a030b03030c01050f071b060b120a11031606 86
    0x3c0c01e170030190003005204005043c1e0031910100e0380036605000450b501d80743d6900921007446801e0050300280e1240c1d027220300c40d0b10443c01b980d03402040401000184403106c98910001850b0507810b200802c281c040c100011160300009511600c00580c6103141001498180386c40d5500c0150042e0504006000683e000310705540e100c6001000014a4505414420300c1d0040690103160786000c1d4050340001d11030190000d00659000b500c01b02c0009183d189041308903c2810403417000110200e001c00c0440380f0f2900106140c2d416007003260b903407240400e8014255803040c0a1044c4aa500141100000000740500940c040e00051042c20000c000e8801a44030702801e000071041003c001003200c035140c042d42c007215144001804907030319841c4201d0818000d02c0f05969107903861104a0000c2c9500d80328200e40e091480a800700ba80008009503078100240000e113503140d5011030150303813148510000b0008491940d0203000e0b588100c844c2d84090604120440c1c02c44c060f4560740d03031001c0c44413903000054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 59363771 1250 59362521 59362549
    0x2701020c070e040515010806090622020f190e18060912031b120703050f060a090f0212040f1103060601171b0c010b040506060c060c0f1e031905010302 66
    0x20034026659850b10600349045001581910301c0c3c5c100001c02c3c0000000b40c620301c241016000c44405864101c0c3c0e01c141c0580e5100d01d81118014200a81c0040c20102203003100c240c2d000d40350350b15581d003803030b02001481078940040056000307510420601b0701e49207600b4006900707003c000e400036003489881941c40e90000c2805101040000000c2102403c0320003003540d00b010249130b4141c40d203401c00480c80703403134009499550000e4205004201e40d11460940c1c14050301e40100410315541c500709403180506921030403035103451740c28495001a10309000040748281e10503500c64406c1078452810000c0f19220720320b41c9010358002c1d0100209a60055252507a034040700000411940d0b51144903003c084100c58881c001100102d0000c1d906001500810318211003240c0900542d82c2da20140003050140240d0120560300002c0030640900300d42c001031015103013849d000c41c680b103241840c481002d41e945103003000841c00082003040c601060004429038020580080c0f0144d451034000a850341e0b201c0b03803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 59365021 1250 59363771 59363789
    0xe010509041106070b0601020d0e01020309040e011404080a0908032b020912010204140303031b0a0203130e0109050a180b070c02091518090607180308032701020c07 72
    0xc14140a04120302d44a80c01004000f107550341e0803031900e01d1450704151441401341c400d9120b0040341c280070388002071440c04107034000c40c00c00791901c0400000d030440c001824155540c0e54407404c080c0b11054405849240100c007071681e103c0c4480c1d4002d154420030391280c12035420510000220410980643c9545806c0201c0c100900280202c110b0091182c9800c60b07078000c2c0d80c4011042040019005407003150301c4135102200c14105075041c95128402124043e054900c549901607140c00c08502803d00704040388116420900400b4807628000030756005044000c032404010000c812050045642c003498460040c06296000907100014003c3c034440100a214a00c0000340201d00c901880001ca0b034000385848581d00b8990743c17419812440c40c8540d8045c0d1070611464040d245c09884990080d02910010b010580c0c4100c001c844040240c50800f0546105400002c04036910402071800381c0301c0d0000c05034900d00e10045034440c030402c405401216034010301c2600c91400340070070108220740f6210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 59366271 1250 59365021 59365039
    0x60206010f060f090503150405010e010b03030f03040c031208010806010f030302030a0e22091a040206031609030605090f0d0e010c030e040605030a080c12130b070203011d0c040f0203010e0105 84
    0x3c641610f01c00c2894100c02d805200305440302c00c91307914000c1840e00503402074008014055000071301c1d509944042e00b5254142c0d1042126900c020384102c02586d00c42c0c0500084500b081d220b91300c0c0f040c80c01e40303403030304500080344500144045001488403070300412031540144a102d16684d00692240140c007007400502c0058280d640103511402031621100690f070701002040d2010b00c0554000307042c0c8145c10b940d4250414032050481071042c2040d8065078004142900355039452640c149001d90142e036540401c18148000800501c05000b518019410040a800502803448100e4508004a403011041195a01e041c0140da40c012003148070a0390140f82c2040c41040280108014184551156801d4481e014104003840500b10240000012010a07181d5403011800303c2682c9008108854080e1107100504000504142000700f222903c0907001003104120200e50003c40100803012807459048056161503a19085c0310b850228000150114111b5040000c610081e0405004450150401c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 59367521 1250 59366271 59366297
    0xb01091d09011508011a03030406090b210f0106020d2c0102030f04090b01020d080c09010c02011205040b01151e0c080c01050106090501030b030102030402090a050c041208040807060206010f06 84
    0x390011a2464503c0c48002c001a44c2d40049034020300a0b411204006c0b04048040c0e0700e14035020040b5012104665603110500d4100300c800c0f4001e0707000080c03d04582000d00004440c1c4429614210710800c2c4880400c0310030b42c9001c034042c6c1450706003c0e07c082007000c6044002200c0700307a54061460a039403089044022544000140d2852180c503024114900002c41c0c0081d0b226002d030006403003808203074240d4811010421054804040503a510007412500344040c00b01544980d0100300b00ca80145400302c80c01908803046412102c060303a06584100c21200140880b04000407000090300403407600c0b0444030302080c280c8030300c540e091090310100079940400d1002d02c10307a0410b40e1003106070003008020551390303448060032a40c000e2190902207800d11a45820919040c400d42c2e1241d03402800c0b454040d03450190140013004005e05511408406102c04984044070400a00600e031196002c1e50f96503040019091410b0705581c031040031988410018081d0302c54500c00f0004171041400c16403010445 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 59368771 1250 59367521 59367523
    0x20a3c0201022704090b090f0c0a030c03060519051f0501021203060904050a080c0303010e070c05030a140417060a05060307230d15050417031501080a06080a050f010b01091d09 77
    0x30a0385c05414a000f41d805d1240390000403409008409182007121300c40d0110a0902c00e07900003a01c4041c24001e40d485040003c00d0300c0c1c1e007100784d02020b01c64042c0d00301500c2e03007600300403180c0039540034508100c41c1401c01c0c0800121011480608400d000502c007050280085403410f1000070030071400f440c864004101001402c0040314440e650241c2c01c65102c0076030480c2d2981c2d0341c00c244144a0350826a002090b0b1850042c0180c001c0c0a4001026515268406000703845d0000031140d020000c1c07004200005045503400d80b040e02903100e40002d0480703400c00c202c0e044242c03000644581d100703800103101000030850220b0000c40d80401245108581100304e80020003110643c900907010b00c0e880140c00d42c1e00c0f4a00e602003840380d48200080024819450400c0b10faa0208441d0301d601d48005031500605580184101a0301141090020038a0342d180d040781030500e0201d1404844a43c049645a0707041c2c1001e0007244d420700c0c0c00780703060181a031410103510a140c80d1008880e00e4404000041500d03104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 59370021 1250 59368771 59368781
    0x61b09030a080714250b0a120c02010b01031a0603070c081207090501180807050103110c030f03010302280603020a0e030105010602031c020906090103020a3c0201022704 74
    0x2410078841034981d00f42e0b0410078503080c82165070400d280200300c502800c1401c042d0420700d4a00c1e16450100415052185074441644040c80000c144906180c4001d940f0b0254014034036499416400842c1c90000140090140c0d003400042c0f00c6100108581a00d1342d44075802981e038000e190385040064003200d410301c1501403140100d01880c2c0b11840c400c0002c215000710319042141c1080c0c2e030343c0107613400c40c52061003100c030240142903e0350800c3c00c1c00c0205601c20340000c0b420200c80150303e85011140a0354924540c84203600b042d0080c40070004105510b401042e5200340e4021708503040b5a140030b20801c5004803001d0180c1e0052641c04604500d06510400c0300c0f200c2c0b040301400070000d550711644040d60b25001116243c01864500c440c89114000c035000380c0c0c40182c000380c04e00342804016001074002e9000b00429a0030009282c2c001ca118071030b491001d100e8100700e00300509900554084005045009400280a6a00400000c41ca0800d000304000b8610303103802c0b800c113105a1410020740544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 59371271 1250 59370021 59370023
    0x1b030a150b1302070501090b060607050d030c09050303040f05040617070b160b0f01030510020c0703020f01140a0c0201031a06180a05030d02100513020a09021e0a0302090103050603061b09030a 84
    0x10700c0131500c0c03410007805501c1610706501540310900d8590f145010003540e4880d804006245401100060b40c03201d00a810914003032003281014403803030f82c440001c60701c1c41d00103901c0b03c4802541c03100c0401c01410244940005854108560030f0540c980030010b41d03847c800b41c41400725080f0001071000d02984100102da42d002c0c1d00040740d114074242610710a00c0e0341c400b800306850b2030090540d03400c50400903100715110800d030343c0003420f5920b24503001c1207074100c880c500c07050612007a802103c0c100c10700a002081440000c1d100c4120f01c2c040341c00018200c0320300c1e6200b8141c000443c1a681c2c01d07503441d403003035640140302c110f6895444480e000120729220b080c1d83c0629018466500d000100c507030045900030442074900300800903540e914480c003074003400a0001a4015201c120140621000d80d001007038407000c2ea00341200c403070100001c0b0400c603611450540000990200e600f01c0c0d55a80f40c040d254218508034000e00550800e5918a180c011003404a01e1140c90000741c0c41c2130070785052114038205 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 59372521 1250 59371271 59371309
    0x2031201052d0102030912010b100503060a120f020607140c012a0f060e011a0d030e06070501230106021e06070c06060503070b090a090615110c10021b030a150b 70
    0x3450070b01f003e140c06040c0b00c0302d5a41c840c00c01640c80040c914800c20a4034450f160091144217003500d0b1104003071244002d02029140421200380610158654000a0030720a1080d2204036003281600952802c0040c0404c020741004802c00505100c0b00c40326900104420710044040d4105800b131419180c1003402507401000c41e820410880043c49065000425645000040c1c440c0b031503030304042124011002c900117000c40d0310642070b405607040410150803118440c000004500c00c089a00650141400c3c05009031041108014000c01e5410301c030035219112010f0481c0030494003010440c1d01c07210028410070400603042042c00c1440030716040200201805015903001d0f940350301c007001d400d1380030350781207401594962000a040d81c0e00c1e01c2540112417814601c000a080c403900c0866104c1610084005948079804031250f07030f50355482030642c0120460b0003c040c10034641c9108404081c404004a01c682c200880d290b01141030840060803043c900e090004100720407800094500c01e41540c06410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 59373771 1250 59372521 59372539
    0x10801150210110301050a0b0f0f030606040f03050a150504030801060f0203070c0e07180e060904230109020102010c031107080a1106040f02010e0406060c0b0c041502031201052d01020309 82
    0x10780c2222100131416903c0641e440303554581c45010707500782c900c90340310700c080c8100c0c0400000c0c1100000304082c1d81c022400400292915507605a00c00401c1129001541c03180c100c00d50710410400341240c01c070242c1858603030a00c2360b0316264401500b0030300c051280302c043c80a400381c3d83c408603100b4802c40e1002c1d07620140d0103444c5a02c035050003a503c0e40840340003000c28501144684a01001004001182c1c84100d0401c1c40da41d44000f44100742c3c4000d001101c10200218031030400411241c09400000c52241c00066051400e000080c00e485d40d106496050500e003014010205215404440c041d0350400c42259541d044204200e88030030340310010712018000c1a00344010001c9902020030494000d903544100c18071514104412103c03684100c0c1c01183c0c40c00511380026a185008503032250780250381a0425582d0100d021124920456450050b0400100d40047d424030458490260000f40c68040703244810748401e0269034000c8000340203441d5005101d18190b8400c004031008800701a1104403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 59375021 1250 59373771 59373791
    0xf0402190c05070f08190309050913020411040b090f0a03050703080a0f0311030103110a0f090b09010e0f060d0501060f06030204060809120a050703020c1c0b0f06010801150210 77
    0x1120180c444011a128081c3d43c0000500c640032040d0142a9003071074010b80041d4409840107800801c1640c030840130302540f5000000e483ea9030664061144c0c0c0018401022180c041c0b042100700e520b10350f903020842c0b401340000d114000c541020346034440800c0ea400540003031841b0000700c81c80710360b41c4000c04500c10031801200700100310028009440594035442004603841005806540020480e400e41c2142440100301064101100401000c1d0180c00054059246d000c10119840a03810265049845150220050400c010498014204481d000c11541031040c050b0f58a07001c00b90403a4801c900341450302c810320a0a50081004180d1000b03080b00040e0388030030260203508240716580c04600504001408a4000310f60307144240a507611032860014030003015220354211650070350451003104241d0a19403511131911200b4002149141014036491a04041e2000c0080c05407179010b107407000b0700035580d8200a00f54151468210301104440034941c0481c80d0107030716600500720030b0820420107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 59376271 1250 59375021 59375027
    0x60f0305010207170903150a090506090606010908010501050612040c0902040303080402090a0c091a0f1c110414130b0301091412280207030c0906141e0f040219 70
    0x800120310940c12000c205001c03059401c0b0030b02640f00170b190980c0084001c01c1411400190807079000d034445400080d00c18440e2200f5283c100225a00c0c102540080d090080a60300242014011b02410009210960403d40441c07241c2c081c1502c4440c0d400c1a2901080802c01420192000340111100031920b503684c03814010704c6c41408be10168001e0316400e002c1018190321703001d00100c40913070391605040d0520708407881c1d103c41c0f01010341e20f12148040c011200b41545c080c00030704102244140c941075180b482050071080300d8040b0780350511000108410490615682d00711010400200e5a66070314008111102001c0e002c2200ca0700e900d9440c000f0100100a182802030215480e5002252030841c07003482000c4240c45907480141c920b011940d8a200e4100380e508000000444500c140c800a503520398840f6130200c016009013501c29114002481a10b144c0c0d04085030503c0d045941048640300c0b892407000c01309005008034003030040700c0803917100387c1c440e138040394146440e03a44001060014a4001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 59377521 1250 59376271 59376277
    0x4060b0a08060910030f02090c0c010e030309060a061a16020a03030c060c02030301061b140607090e0609070509060315060c07091d071712070b0708100b0418060f03050102 75
    0x2544640c0a21011624102d101300026058076070081c001e240501c5c03150204820b01400400c5204400010840c64032035110078001c402009203910f0085407681444041c1361700303102d002440c0828441c682070b000c10080440a294607034114480c1d03140781c1d075440f4203d41d11252003000d46000c0d4101900c40e400008056021401c0900780340100d81c100040344142c0e20132a00d038442803041e0780000e13140e0303a80050100d40c3c0d601c807505064454003001c101c48000c00c07130140c01c1210444600021a01b103d004022241e0780702c860300e50040303044a61a0705460442e0000c2c10901400d85180e003d00301c04000070302c814055007540100307080700405003034456820070f1100380c1d0b4503940d0058111060034400020b405401c1d115800c2c2601d00420007070500203042c00f444424040307410310100803a1162041550004c0884001040e0b00c5019a107070412502d000c51000d441ca0300b01500d402c4a000251004104a0b40200103507010b41c0d005207821908251142c1e0310501400c1c4a41210250561017880002000015401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 59378771 1250 59377521 59377531
    0x60213090b04060602031804060305010c050324030709050702100906060501090e150603090a0602030703091109060d0809030304051f0306050913170c010906060f05030a0302030d020904060b0a08 85
    0xc14004641c5860600090398060320070342016a00034000035180b00072441c01b0460380c1d500039000080087d0380342c40300c9003903400403080c420224074000203101c03c464102ca400070600d460306181c0014a0518004680e03166a10301c107105959541e1000b28030094400c2c8851225458443ea05001c06002828000300070a120312078107000c19900d6500003400403554400c180b082100c401c600c02480e458205200650340014020000307130240101c51400250f1510180d8002c81d2641d400140340103940c43c00c2d0002a42a8082038480c40ca03d20802655a88aa0b11074840381c0d4401d202c0354691902078017081c0345000b150440c0303a004050b4800079106c035051000c2c211001107981e605001aa070366a05110580c5030540d00040720401820506d00800e01c00035031540318a0b40302c2900d40c54a2045102e8030b08603101c0740790454110b902d0785000c0107060541031312800138040403000b614500c80250f80183d5a4419116035038140c0c4e8002c07482e41400d590310342c001801402c1c408081680c1d000c4983c002410751302e088032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 59380021 1250 59378771 59378789
    0x24030a09210f0e01050304020f01090e01030c030218091c03110f0310090501080d08070c061b0e040203060f0f0d06020304030f14070201090b0325111b03060f070c060213 74
    0x4240d09056100d80d040f480040e10603100d4900d9030b107a42c2c0030f0280700822400b495050110015000550002817080c5070f00a40c055440083c005080d44100a803440440b40c506080380c85020030f02c000001d0100b4940c400038010302c3cad191415880440c00b507002e84003c003014009190b0102d008903261341c01324000c0d440760010452100d00b0701c1c0c5403005102101d000b80166105613200c043c030030140c00c2c000e0348819001051420146030134090350b65800300791541104030290f84412060140c40c0c9940154140d0301d0700600721019411480d020011480e03140d440007040b48a141c034102600c1a80c0c8130f9004003234005070480c900303640c1c0346024100034012915404903e4000341040605040c1d06a0040640d0b011907416074030424001d1401d0300d003180316000680664414000100c48405003034008000380c2010305503841d910029060a2003031420041c3c0c030322035501184081d079054001751b9000b0900b00d0b800500056881c036a40c8810100301c0d4641c4400c440100120306c0001c810644110a061900441d20501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 59381271 1250 59380021 59380037
    0x141c030605042003070201021204030302070b090c130902060c03070b04050f0a030914030309281e06030507020313030b061314010509152d24030a0921 66
    0x182400115001030742c1d9550341860510840100703c02c0a0000e641108191001608140384006494035620007a50124080b80d40000c00404001031850300380e42c4445c029001d058480c1480006c5142503144d400300c4001103039610b4210046545903811307101d5205801c8200d0387c0740e0140e80340c6000705010940e4103903542d11545641390381c40c02000072428502c0e503050b520700100c2441c02521203a80c0c000445600d83c50300050000300b440340c0303941c01c0d40210782c081240b111081c604e08011800b0000010b42105140c1c50184020b031540e81d6000d032001c000c072141d9190008059880c12001c9042d40200f04401451202c903050001c144040b022035180103402c11100d51411a210034050b104480742110186042d00c0781000400280c170304014141e0303022400d102c000002c20302100003e600038003140340d1600d031036401c612001e81d199907000e10341403040d4050710043d4a030b505254447d414a402d41d00c5040d030604000000401c0c0420303540050340c1d034541c441140c500c008503203601248641a11844800050818 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 59382521 1250 59381271 59381279
    0xf04020306090601140d020d05030d060e15030a021201020f030c0406020105070c260c0a060204090f09080708070204110a020c010f0e010f140403050601080609010f0b0f0d141c0306 79
    0x4102d044c1200e1400d126180c210404038280b242040110380e0030f9038850148560a0302081d8180010030300800101000644141014802006a030700504481c0c000a0922480c0660307440008a0600c0184c044458031602d040362a040707030292040403070f00c1d20202d10100c18040b21600010140054400342c0c0c00901107a076440300c00b201c07001c4403524080e0501001c1101403035080311040b007810701d0724080401d061800d4101100140f4000d04454200d0300702d540002d0400454489204098100700000000c6c0041017003906c807440b082c0180c081c0034182e07100001e2407400b10340d110344c0b1000320f411180c56070355228030340b9000181d08e44604a610300d000c1046000c040361801e1140c03103001951038050312062007a118500d812181e40f15190102d036580d507420070011003c80c104205243c02880c0703203401044540fa1031580c06083d903945003100070b00c0d607080c000d0710300705581c41c20410300c40c4000580d000d02601a00781407140721503040030021441802840c0c000b28030310310182e0209400700480c0d2010702c0001d40e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 59383771 1250 59382521 59382523
    0xb0930071a130509060a08010507050c19031e03060305011406130608030a050702010e030106030b090f030301030308060906130509030a110312060f0d05060708041502090a05120709050f0402030609 86
    0x607098103184980c00b180d4041c002c900d442041c0c1a00248050319a1038519100d40201c0c0c00c540054a800000c1030020401045aa208004581c61002c00c02c070020b00712921507070082d14a80010a000d0b030703092480a00540824842c4e40460029600a0003e000505400b03141040416058a03440d010b0000804001003062081c0550b00440d02e0100055280a600c881d04540941110304100e0401403210700b12200c0c0d5500b400b1760030240d40510750001c01d0f801c02008042c501906000e22907030380d40060004001281c1c00040c620b40c00081903919016a0b510707140050b1625000b280715061592510080c0020503400101074200484942c4924003074007098115a81c0d41d00610f182d040d081000710000900a040000350a1000030016104409244040c0c0e596400c0c904100d40c0c610004a56178100818132041103440315507002400c2e030031407a0000c1c0c0b101151030030007540100c9016800c542401c00340c00c50208018001010f140d9801c028506140b201000c4910003501c050b440fa02c1640c0100d000400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 59385021 1250 59383771 59383777
    0x190605040b0f04120815040609020406020c0d0302030706050c090607060c18032411070b0712020a0f141314030d0201050c04140f0a0b09040e01060b0930071a 69
    0x3d0080744c6124205400001107403255001040c208900c0e0000b200b02500e52600d0107040060205290090b803a0303400c02100030b00c0d05403419a014400c858800c0c030907011236008012618102e42110011400b41d480000740d01891050301002c5404c204002010f000f80442640907852204d403582c0c425030003410407420401550b10601025002000600c42e0104e18100580c1302c1c1c2460200050101c0c003198981c164050303d4008207020307602e10b1201000c004640c1e82c44006944030503520300c411070034901d5200000f800c00030340c04200000c0c42001c4200a906084031010f580440a4001151503e03980304da45242c000c50b181d04543e40640306900c80c0b080c0b01030042c000c00744145152941ca500b020b04d030660707241c0d03201268004e0342c0e04504100e010180c1c64a40711440009003000e904880e0741ca514a01c14001158a002d07580c41c40e992401d081400309800f440c0403104c1e01842117400b02c00703243d03c0d5105e0206102403083d00c101200c40c2243c01c500302c02e0011840c9400c560900100f1440408a0000061544 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 59386271 1250 59385021 59385023
    0xa0b09070f080a0e1f060f0b0f03040201110115030b0c030106020d050a031b05120906040312091a0f040210020309030703080a0c0b0a0e0d03060b0a0c05190605040b0f04 74
    0xe8044215641c0644210320240c0c1c8400708942c081200201d06681c80c1c14160020380200e05040e03107400312440d0142d80c3c01444020081d940702d01d01000c0c9046400c103c0e5008501424146170340020224055a109071000c8900342c0d8075070002c000b0b480d02e40c214084556405e1100b1541442481c1c0054030015140064904a5103550060215820b04030b100721040d900010208080c59075540d041d04104010316011036000032aa114150340320040880c40d05003080007008008250701074020000002e0348420880b51101c1d10b4400419089414500014460844212282c9181c50081003100f181000040301c1d001d18004d4800120812158008907141e110b20a82250594407402c4100000752010001300303a10b424602d800030030482c81c0d9641509240f0b05460b6038805e83c2d00ca40c080d1401c0c20040c0803038091180c0302d050030460300c2e10740790040c0c030a409400b01705802d004a441920040c008180004054603500620810442c240340c80c14200511040c1c8042d100011b40b50b000030b507907091401c115802a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 59387521 1250 59386271 59386277
    0xb01081005040509101b140a0212030a180605070e0a030506040b040602040801020307020c0307050a05030604020d020a150f021513122f0f010504030801091a1203030a0b0907 76
    0x60350600301400040c103009003103142d06210784040820941024400d000b440002c4407a2840030f103140001c01840c2c208020b400c407001007005c1041c21206070700051030425030b1081442c600e44035914212488024404d40c2c06030300004000d40030134800c200c05030f400507220b5000c03030300c65035800b004c618144000322000c0d000c0200140d20010210b004035440041c41540580700b214050701d0251154600c5080e40c106642883c0941e10421816686203001e00051002d080252402c002c22031a141c002595000302800290180e00d200c1c00c8503081d902da0510001c05400703052a00a03000243c1c001c0203056818105150006004e810050f00d0b07610742040c85140204a001c199200d2140c8644a400c0403140c07003000340c3c0034066100c2c2c4042000c2e8405190600404101111801d00a88181d4003410014203e0340248203916060030800066009091141507810001d000105c6d0300e40344502002d02500f000441c1d030700c0365124007001d14040d00080150b1080c0061207040c002c85c01c0e0ac100344010300c60107403070340004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 59388771 1250 59387521 59387551
    0x3061503090807021e010f08090c010c081201030c0303110c0d02040e1e0304060306080c15071106030a060311040903050a050d0b1c0b010608160507050307060509100b0108 75
    0x2000d1007a0810301400303001d5815285001026400640030701c11840c0c0420840003078410000296800c400f0708054144142801149483c0140d20a91102c251021050611104204070000d10503110240c464040015500040d9540c490034a00141ca210b0320049001941c1142581d982a401160040c8074000150050600c01d10355030070013029041014600c00340f07100b910703070f42c91005180340e064000d250303a00f001540d520f60810034010160b84450300021351541c0311415003015501c0b0500140101d44140b240c8684400c0c440c85c003d078000c030061085590021011080c002c01c488a6802041120304c611301742400c003001d41d030512064868042003d8046403081c048250041d00038801407030564040700e40002c07036088108c001843c18a45a01074150356083c51821020409483c0c59540589950b0911b20031601d400d24804240102c0d01c841070b0104030001c5500000c0003400c0040d254255880380d020b00c01d901e0045e15059451a000c2440d40c04d02e13040071400207203540030b514000e000e40c006200d1012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 59390021 1250 59388771 59388809
    0xf0a020c1504030c0203070303050a0e090907050d1403030702060a0b010c0b0606030c1e030a0501170c0d1104022101050f010e0f06070f050607030b06090d060e01020c01090f050d0306 80
    0x1a40e1000140b0940920045160100c0165014007240e0040e5110b5140d40d900c40f40319040040c20270500350103150203561018188075810034005a0601120b0701240d020b42e05002c24903202500185084150501c0d11010050042c069004a18544109400c440c1080310b070b032011004494020740441c016020507140c07408110641405d10003541e0004842d0030f101d283c0650300d0503442050350404150a007121001c4140001b401007809020700401540003c448207a0001481984910306c1e80540d5102d220400700d850204000c9202d4856804c20081c011500d0344040704004d40c1c2a0a0001c18161420280780003003203074a01401040011441a0358581d8030100203c01d01090041c007050aa621502c180944000125412040280c1a00c9600078207031600f850f05014054420705079640b8803401e410b01a800498032009043d81e491908010042103010720141e880d0b0080c0b090740700405e425400d1181d07420902c15840000c0210300e2256085481140301c0c400203c045820a01a540d001602000303122 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 59391271 1250 59390021 59390053
    0x20f030609180a031205130201090b0304020d021203030a1104060203250605071e0c020f060304060905120705070b0301060203192709180c1215050106080f0a020c 71
    0xd60b0106181500c91240701c0d1020440f440c04901000c01c0700007a0940c44402a42c0105024413500722441c0440036042e19402e50018150b190709000b90054034102000080543d0b503003036a40b5010315000f4050752002c1101411080e20384d48101c1d0400c50310f80c1001c00801e1a41d100c1d03c202c1c2e00301c0b0056800355091100a56004002c1c0080e10b12010a4000c103891000100c2c042e03108080c0100801d890388c0d52500c600c1018900100d00d450424028400e0b80b20000c070146e05c803804186c3c00c13032170111542980ca9035207241003070041071a404040d00034031800101554115000005282e114021422908031580d02c00c03800303903240300901a490041e00140700079180d550358945510350380030040c1055010320540c45000d8060070100490642500031000003042418582e20820241d01c0080241d0029520907403659100c0945912900302c903813840040e404180b01a6449068050a0604090011b03503919400180b000c0d43c151050802d00b07407150041038100030503100702d0b82c500e5420360103000145201c015507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 59392521 1250 59391271 59391289
    0x101106070f020f010e030702011d0114030901090f051006050409050c1002070e0703021201150c20090405161d011a0702060d0f150302150306061902070303080a020f0306 74
    0x181948510300448400240a000b80402045d02c0c500450f00c070030442c000144a0300e03070403014001500ca454290030090741c0c40a518039000c8076003181c1954a45a00d00c0345401400183c40150510304030b060701d801008030201e80c40000a040880601c600741d21001004200e074030042c1c0003000c1d68021900c0840504017050005004400c41c015038030300c10740d140c1114040e248215a1341000981c001228140315030240c00e96405800a200c4207802c549040c0c8000d403034407d03040c501601d80d20105010508030264940c0501d0120343c041c200d000c850805140c440d41d211840748280b26202a0340201089140f01031298200c000030201d607c59190f440c00d11681842c4542c0040b42c02c4802080041502584800c00200703206c215488000400070944400e07070f022604451301c400601c0c4040081007001d03035128102024003003100d0301029900d458420018007140f1a03000320246205d4001c0a01028940115922044900903143c000325551000903280c124030654512901d5441c090000c100282810158 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 59393771 1250 59392521 59392547
    0x7050d23060103150c0e0303090d020f040c05070c060e0306070305070306051503040c080c0117090a0606080a0b091204031211030d060f080a0b01061202040302090406090210110607 79
    0x166442114036203640e051180036081552400028012100d00a60038492180071140524204940360b2030240003a03128810914541c0c030072520302070003800355601e2041c0c455108030003d00401c100c822702ca4002d030480c1c1098800b544c081a071040d000800d00d01801070300703c4c50300b00103000e040d540d03070351101c25401014040d280c2e40405558440100d80e40d10340340381503280d0358440c9801641328500391501149940c4140c000f042d00340c108820350710b22a600111500c034a241c525008c40c0c0341d550340e0404d0354507007840c5035009465982050b40000b000c2602080b0541c04600a80f40d01b1016a00e4215070359a45005c00c0d082e5070a510b00700030420108031101d00e0140c9542443c6031010400c0e09040c940b61a58109840210107907503581410004206c0306202040102051006407420700050340f10307000d582c0c0301481540c0a020402c500680c2c10142c0d83d0448000e0342e0700a190b22468242405c00c580100040321302203004121648100381e000e80540d03922100f0359902001409079544103002101c000680d03d203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 59395021 1250 59393771 59393813
    0xe15070c0b18070b030a1514010309052d190b010b030402030a120915020f060103110307030503040905010e01171e0f03030103061407051c020702010504090f0b011107050d 75
    0x41004251202401070a00800d1020341e49902c80c1041c0410204885040340004640347d920f640800c1030083c0b98201e40d03088a000d090008000c0c4aa04110b81802c6d00104c100b540c1015988804d41c20038206180268100254003c03101c004840d00c4846010003149800542422020401004905025002541e2040c405015200043c0c030590700c00d8545e00c1c00d80002d4001c01d150000902c0405402041014560b00d18801003407003400c030716150b503150203040c08040e00c00741d8000f03c4144140c8080280900650f400300450303590b1075603034004000a200178012041d0900402e80001412180009109002807001029092149205042c01d242205444551070700b80502441c0140c01401030010314003e42c000da00125940e94001500100d546000308000e003404030a0055405036000407012940b0440702120043e568615400140d54500459000c401d8180c10b0402101d045003064008115001007a21041b18a8a94903901501d84a241c0070f1740c0c1e0040456007541000ca24004400000210014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 59396271 1250 59395021 59395051
    0x703150b090f01050f0102070e0f0709080304060906021e030d0e070f090506040b03030f03040b07090902030718050312090f130228080103020f21010606030e15070c0b 73
    0x2902080c2518022540c650b00c60b0007640040056051800004400003424800780900034200b008007000303104050500c014502c0c01c0740005805502560744031028088980880341c460b075803580c0c000e100540a00a0318014000e5005001d41001c0e5080d020222010b4803000d14227060304d0004000003400d06107609007561041d21710000c0c56514501c00c0102405001c04d0202d603528060040c0b005071080c01d405140079501c00c000691150340104240c981041c1e000b040009981c980ca8000c503800c100d141c0000303031598070000600581076044031506641d0000b40081d0605a5540e03c00c240d240c510f0003c9800024604001003001480c00d00c50014a42c07500601d5109a5101c20520900f260070000c444080828001881001615054075a83e0740c00400e14140d01950b0441d40030400307810031208198081c0b008000c05205500d40b0185074895100544000c0111580c0c3d40d400a0152601ca5001070050082c50007054070201e000070711510410240d21512040b0000da51058042c2d0303402040d52843c3e40b048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 59397521 1250 59396271 59396291
    0x80a080403030b040c11060c0301030309380a0f0c0c09020d02041703071b0b040b07030302071218060c11150409020315040f0902030601090b06070516030b1008070315 73
    0x117441940034140c2d6903035071984100c282c94000f030328100c3d016001c00141207040c030042000a81c07244030030301980e0f20402a1060050541c44070041c01c40c07240c1100510144a10300c02e00100456000351401d0f181d29683c030b6050035545041a1768020042030f0160101c8442c000910000300300d0340080440e6a0201d4005181650701c0403104106a9804900d1000c4c0c1c1000440320305200100a44280940c007018440b14070515000c001d8450340f1072807140110003c0701041403424103000380e0665040d00d4000c03581c3c0752010159000144582e0203614508044002d500d000703d2503e1140106440d49580101080341c40f80f8481c1c20040d00104d1040007441494041001181c03065260001c3c600510a008902004143c0001080155403c41c14421442c52030030f807806025a400040076811500e00910000d070741040c0602083e541c0c0b144441c060030301e00c5549541c0701a03000c4c0e100c25404a9005175200500c58445810b8050012038621940a65500821040c004a42e0081d513803581c05801c0100000c01000c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 59398771 1250 59397521 59397529
    0x3060117041401050c0f07021003020d1a0306010603020f07022110020d0506060c0606040f060b0a0e040b030f330a02130e0702030708090f121018080a080403030b 71
    0x3101c0882d88146081e002401c004824000c55412500b0700c0005401c01002008a00c464051742c140644a94a066041721001d8004ea0480c0c1c0076440312001400040c0e0500701ca4895130220081045c0240f14240002403030394400d200b5a1240c500c00700c6480e01c0c00b80c0540810684940c1e441680720414450170b030f014000c1c04200140c14007808050405a210020300344a20304984004041c14007074036040081004109010603296800102220001200e414042c909402041c0b660012640080c6c001017100d40180c00400c0d1441c040c50465050081d0880c99050580303400303040018004076404500c858601c04440101e0491041e000c000c144407031071401c0c1c4080001e01c02515044000e650004840c015004160030345000340c8140041d05a0a0030001e40007980e0b8803a00002816101005c1503c0b0641c1d507c00020903480c140040c182038000c608070401035101c07485100d000064624018941003140401420041d005030001c40c254184240710781c00f03442012005204404040d6200c46012180d61 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 59400021 1250 59398771 59398817
    0x20714010c1101060e063111120105062b0209040612051c050a14071b05090a0e0d050a0215040b01061404050303091018090b0a0b030601080a02030601 66
    0x3441da6607544900400008103800c556282c1c0044c00e103c2c0138101000b0080c0c481c0c0d842c6030354107802d91005280d0110484145e40f07008104c456103141190134003480840074080038024040745041e01010440c107980c1c56003007200500c5044035592026030140d0140030030805e114148180c404554401515082c071003c009401c0b03520b160006003114100744d9070281800801c02a000000070280c483d0f040941800c0009052401840d102c00104041200021203080ba10001c0e540302c0c43d1b01c081251014101400704400780300e00d9020703807801382000341d0000342e1050b0640110030807043e8540103050952010001168550312054121703040d48100a100e486508418a04038400c500501e0303600002d5041a600a0202c001c3c1e0782c0d1481c03800030a200910480da004822034080302c004032100101d00f400380030142c0d094074482d07a0b0308020703a460b140001001c2056420540d168001111465a22519406d108403640015120ba07800164940c00041a0001e03c1e0700441d0012014105800001c801c0542c02507004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 59401271 1250 59400021 59400041
    0x109030803040503031510020c190503070305030306041b09140d02030d210c0806060706140907060e04051504050901020c0703031805010f0f050f1224030c0604050402071401 76
    0x284c800410042c6c050603400b0207000144007100ca80000e9440410000e50303079008031074802d00c9400040020480b0385443e89101d80100400307016201015030300d007003445c0c49400c00c8607000d0083c0e040c1841c41c040c030500a410240d0803c1c1540341c80f40c402c0e00b4940075804400440b1901600003601c0031040b000f59400300002001030885545030386d002040e0070000d029650100d0450038150341440442b203202500000555130204094501c0c0e41c4035645400c2c0b28018060680e440344021000b407060040301c0001060361010b547d056204d828150710a80c00380170440b4001c90b4030124032400000784181c1d500c0c1030382040f80c009280b00000360901a91580440c10000030383d008070041025200e408480341ca00071107540040009003055999940103610281c115407230810b0391070810000250300100300e104441943d070030b00e4520000c8015480c1c0569003240d0052582c40d43e030240710341c001440c15207180016180c104c2e21000780103142040d20308004e02c030107500001c07400c40d04140224099003c0403002d01c1244070075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 59402521 1250 59401271 59401273
    0x20d090506040515010f0302130219080106390303060906060903020a080102070302030403081309110306030115150c06021603030b0a06110d0f111203071106220201090308030405 78
    0x7a0415160452400c2d00750421601c200c0c003010b0040290314040400ca03c201c1e501643c200040d131000c041913000030300c10f0b04401c03034888000000701c0600e2039008007014180d40d20f82d07d400c035170103441ca40c4e0a060b0f00c03045d50803040001c3c102081400032101001034003400c148a82008110542c42d2075030a81552155080180041d6464a08205602d00b49800748000c1603500021490215a602d00035103074417030b500001c8c000c0e9000140c10891300c14484081f0b4000d044030003081040f1a5542821280c0d03600030380d4070341c1c429070800402810203150400020f0460710005600714200e0703030105040e1210025424140e61041c0d0911008035443c0c04c0748441c451151203550006001d400031000c00001c1340054111108010040c0c0506c2520712000a01c3c800c410034600f044600c01d9076407101165920021040c0c0103003801001d0008094031381c002e014600400550700d401c000a0840702c6500d940381003c45400803264681c43d880710007141c040403100200c07401850107c0000343c89031600141d0307034030580d01242c02e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 59403771 1250 59402521 59402533
    0x1d090a021309020f090f06070506011212020327030307060e0f010e03040e0403050706020d0e0a11030c21030f0a020f01290405281b0c02010c0303020a03020d0905 71
    0x100c88010460040900750b081d10440c2072034540340c20030a80740629400070f8002e9481586602140d40d80405403818541c0c402c04a8189603164029900c195045d128111008203220010200003030010066840070074200d0000d01c01ca01250f04030602003882100f02603010f0004100050218040b8003c84640c0c0780007900800b003010502c0841d600f1a01c90015064158009000502c080503087c3c1605802540618203207440d03024038107103030000303104050388010020f01d08010031520000200700c1034400c0d402001031410210000e0305150300d5500261155a000100c1d4980b4590345040b142440582c50b424000c580c20030611010201465100303036040000760f4441400c2c1c0440150034002c84414140e00316011981d1040030140c034040c144000b035030034480c1d40c1b15400180015076078a40341c5000c191081c1c003100c0c3c003032803005418020055034203aa500d1009800c200c4000900031407540c10807603410394480c3c0c0c51119a0b24202c0080d08424901c00825800701303c1210302142a00a540b00355004001400d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 59405021 1250 59403771 59403787
    0x50a1d0c120706080703020a09120b04021306080a030c05031219050a0b01050a0e01020c060a0c0c05060c0a020613030b01060807031401030c062105090304030b0106080f04031d090a02 80
    0x10790440e0103140c1106940c0300348420b020403076208071100c0d000103490901585030120081d050320380900035044a81c02c0c150030ba00314024004030112403401070340241c9044101d50007184204082d01c0d524082c03031b845684885c0b24040000c0c4240c420010207370084050781d0412412000b5005c000c4410b43e000c908200e02a400181214010f200700394200c0d4009030200058084640003a0450240c4405101030103840c800c90b4803d41d0090000403411a00140860f40e24400101c001c0c22011a1000c01d8620f00d405000114142c10101e04071621807664400500c0079031110780c20855903500018002040c50410700340080010310f403000c0a0301800e0a61290040c500c0c100f8001001c503142c5c40000c01c03c00c44940300410120f6020403150341500c049280400300305807001040b24812040f003000c00c58451505d4104003603183e01001810540e0301ca9201440542d0f81d6500480d1018800d481c041c1e03281030b40601103000207024008450000100103e9264501507050000c0c4980404450194800f41c002843e01c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 59406271 1250 59405021 59405029
    0xf060306081507020703111207062303012105030706020301060206040b0f040f08130b1603020d02060f0a020901090e070905040507022a030703080403050a0302060a110904050a1d0c 79
    0x3880440002c1c240c5100c914001500039a205101c0c030001c0c0040088408400060320b40c04c181c000440d011004031155107030f88100007081c0480008900d401c5a4801116000034a25201201d041300c00d0404100014076a0b034030381c1a181ca03007020040b6001c3c4020842c82c0f0001c0ca040c00a0741c0200703481d8014158500d002d090841340000000c06412101a1807001c000015131052140c1c0101504280d407613803a61440c41e084400042039070000182c004022510a0640403910886c030740c068400e03400e0710710100003503d040c0d9503004165041c4a00707208034800610080e40c02e90207024031600c1450702010140c0d5482c01c1541ca4403044d00c150700004c0e2404001e020508141c001c480e08600d091004045c00742c60440a00050203040c003010b003a680b0176100d016590b60341080b1103005560042b821640d1030f603882c80d08030396880c0c0c1c40c3e1080b80517004800010b100f03c2080d01c0780a107060380045525190200500810006100040c980304a16a940e0300255100c42031524540f078511055004046001c0301c0c1c4100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 59407521 1250 59406271 59406283
    0x3010f090c0c15150311040c0e03030a030b010201090206040605030a050601080105030c0f030a02060f0d14130b13140318040203071704080f0304031d0f0303040b0a0302040f06030608 80
    0xc080800e041c8440140415440404092900c0e0001403524200400b0311103038000e0505001c2d02c100380000c0b00300c0402803114996098a150301c089400700081c189441080c0d84a0600040113607254005002c1c0585550080d08084c0603100c05200004902402e980021840c1e00150081c000091011040040e1540540715041d00041c0c2400c204000358580000a661449020a136501403110400b4000c0f25403010044004810b0b40100502d4070782c05441a0307900c05030000041a9135440c00e0034125a80145062100c5029040c4002c80042485950f2199003c0308000341103103000801c1003910030003040039000d03010303a1481014065640c4803900c8480148115103101c1e41c03446240f0400900c401160007a0810700c0d02000100c0c95102c941e030380c2c24200e01d81d004040304403241082c000308201c20107620000381c0c07041c50485021409074041c03070024051242d00324682150598001c01c030a0002e03016000152100021601d4054602030311008030022800d4554864404a42c40300c13018001901c0078011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 59408771 1250 59407521 59407529
    0x130819080105100e030303011a070609050f060106030b0d0f1b06091401031109040c02030c03070303020405040606050c0607110721020108071704020d03031d0601060f02070305120307020a0b0c03010f 87
    0x30601e2a04e0708100020b840b4070045c400c10095000d05244004c0d182004416180741a0f00030000b0440301c0541e060854545036183c0712691340d4000c2800104e05540607201388041c4440c05840c031403604000e5942c0345d002502031042945c1520002105100030703821204c110b0050040c2d0703502d04c00090b10b000c0c80c21410006501a05040c14208190000c5074620303402550700a1404036404074940f144040242d0551080c15103600950100081100a03d03826030007c20840388255410070082d6900c50044603d405480007065072904841c022640380d87c0701303030b100c14804e0940209440c0016500c1034069103080c0c000046440c0e001c0d44031120415982c00c030782c2d107560064640c10000507200da01c0050718a46c400c0107100910658500d1940010b140c4130780c1c0414400c10000012005682d40554500e0307885809204a500040100300300c2542c0c20f01c00714a144c2180e074098024008000c2668000340d954200924100842c0b2030b0308a01804500391205450003405508070441d039075410300da201e213156101500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 59410021 1250 59408771 59408777
    0xa15090305060903160f0201050403230606040b01050702040903180602160803030907060815130b09090c060a080c07290112030504060503100305340e13081908010510 73
    0x2074202c41c090010392203171951214400c0a84446880141d6950045410107490f040118118140003a8011489055482000c2c12150f16503691070400040c0e404d0b4070a00d60000d0b109018100050425401400c0080d00c6800d103070b1102884104240c0e2401c41366030206005a10030354a05100100007a00c0340d02400d402c001452030f520300a09160350b1001603215000802501900290024000c507014001c100d4008180703441221000c80c00001508220030614841c0d280b040100710044400a041d42100c20040c10490510f581c0790029228030b1001003d0200913803040000100041c274150188115031a001140000b80c0054407076900e540307905070084040f0100391003140c40070075045000e640480d0001c1c9003803a0f4a68618541c0c0071911890707800140300f8402c8809000380155008102100d07104540050800881c1c003004110350034a42c2d22900c0308506141e4085003403101401180305000303000c4d5035020f141c00c00800c1c5011a078810240c03402e0004010700010702071450203524560100300c1c586 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 59411271 1250 59410021 59410027
    0x10507150605130b0414010f150201020909040305220608060409020a120f120206070c06020c010b030f0303070201140c070f020d1406010509061206060f010201060f090c0809060f0103060b0a15090305060903 90
    0x1008ca403103440501481c019110f145550f202410710035011101d1250000e041c1c4d11044c18140780103403076900484080100d9034560704141207501c5134a0030110440b416551804a5500c560301480000c0602c80004d03600001080404102c00c00181000c0144600c1204411030754020740c20800c464000f030000d490219000320b1f0078480c54540c07020003842a00d8011200580d101038040c42903004080e62081541c1501500c403990100c1c0c8808409175114060980084c8205505010207200d4208203c42c1c009140c0c50600000020484100c1e40704101d81c0701600707110881043e5200c3d44c0c01010f040301e04281e2035100c84018002400c1144050380c00c80c0045d120091503000030104182c8070180101018010503d40801b055035a200350007100c02880c012685000458a50300840058000702030120082042d0b1302c00b03c0c101c01c2000881500c9001c4035030030340c00c15034256070f80c0c0740c09000c0502146a02102d00d08001c03a81d411011034103101010a9119842c8807451403401c03d081c000001e0090105030014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 59412521 1250 59411271 59411279
    0x40911070308070822060504031b02060d23040501090302071d040b042618010908190201050405040c02010f051006090303210606020604140c010507150605130b041401 73
    0x10b0000c58001c0b80b207041c0800250b0f01d00940300c00652519980700c80c40750b042c41482c02400070507400780303004900a80c0d4142d0303901001c0c012600d00200000000307401a0302003066001c603038180d911020540510440c00d2410703000081000c500c81c10251020b45c0c40e81d543d452550700701501000208010038240a6240c400a00b8540704407082c0e000900103089240e041c0000382c2000179a00d040c80e0584000b6074681c181d1009a0718806881e0010345d0150158010716901c0c075241d6006126080c22240d81c40300525a05034100ca07804510640b45a0490501a042c00041010b07655409034260101c181d41c000034071801082c80080c142c0d0b001402d010a070010710744041c085154020400700549406041c503181e0068803800d2903034888510318150140c5440d10001041c4a40e010900e103004601030140c0d8078089415814894031100e0b514100c90200304100180c0e0005180e402e00d025a0413403103034000400ca65a1004200744074252101000d681d81d070b138111089549050700c5205000b40300700090481c03541c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 59413771 1250 59412521 59412527
    0xd1101050601050f070212190303050c1201180e150a140c09040218040501171e071202010c0501050403030f06080601030b0403050304020d0c0f0303090b0c100209060c01110409110703 80
    0xb10b00703c80342c803200c00203042425912400b100780d0000703c03500c044032300c2d1900c41a000340c02104021011000682000d003c14644030450007540c50070440d10f0f040d5101c61340f0300740195401d901c0d852107502c1c4044d100c010000204c5070138015010400303a070050202c04e030714125025030200d031040e01070060b8204441c402d0240740d6204000365000c80009550060740e428412060580c50551441079681c4142098004039003d49005ca00c80c5001c00c004080f603c040c40480055003140b902c41c0d213090441d50050100f00444820314100c1c1c0d030f02301c0c0103040c07000b00d9600700d4945600350307202100c060300465113582140c0c80508040c0309140007840b2840203000d0950550b070340c890f26140042c1c00036042240200c04282990b550135558180b59038030a0700701c40d0940d5520810304030004903110030303000708102d101c0003d29220840304603000341d0300311000f8040b0159440520700080d000400c009410080501c814000c0b401c003442011103c00340081041c1c1c0301c900d0600e0910540350340b51002d000e810007d008400000750 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 59415021 1250 59413771 59413777
    0x20f070515090411070201020c01080f0604091509050c0109090b090408030714030906190b030604020d060608030408031306030207120c050a08030403050307080114030d0c050708060103050d110105060105 89
    0x242201d0071040703103012902600e00c5000314003205603c14641030109102001d200b000386500b5101f80c003545d1500d2012401550b1205003113601c51054100a00051400e180c503500c000d000d98400c048845599a170001c41d40111219240304841960080c10381f0041c80d03130401440b400074907441400744481e00c02c020119441d0301001c1d100400e121400300100d030210f4041d00c020401e10342c404110303e82760711340b40f22003585c0c42c0c1d0709550b520040c00380380310083e4401d0254001c0d540d50700009002058551070f55400d00c500c600c0d1164040d41d850361341c1c02d0003288002050000b070004101c064004c6869280e00d41c40180761320320546c40030050602c100141d00000780c0300703880c4840602890030a0720303030701070b250920600b0640f440e040248a000c0c00403c001c1090b82100240d40240e00c16a15071010b41c0c1c0b40c0011600e5020020b40c0c01da40340d80014042c1900320721850360041c08034030a506442455503a002190300d0110280c004a44a4002031100009560b1100741c0385aa02c10440091009040620000e02a48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 59416271 1250 59415021 59415029
    0x60806070221160c030b060a030b04110411030108010b01080a090317091204060504061707200a02030604080309060c18100c0507030b06040e03030103050d0c020102070807180606020f07 81
    0x1c0c4084690721902c26900c02510140d000b40301d0500009401c51903c1c403110700442c04110f810030003c2c00402c0ca9400d00c80ba40d041900d91100c4c080070140c549885241500380588031040d80103889051007080c0b004000040d5008041e000d00200d544500710001410b0b0b00030040c40d40041c18505101800425802424480305d0070b00f0650003442601c900c00b41b14200846a0f01022240717100050005d001580503008108646140d82c801c07103110064104840c6035601035030184009202c101205c0c50390014007149506c841811400c030756040e0481e90219040100480d001e94801d040031041002484e41400803c2d404100c406e000d900c0d2442c4521401d5209203040c0d04980224603265015644900a211000d203164000c011640400ea4a160000c40c0340c0303049070301d103000750b00300714030410b41e1100001560306803680440a030801203c42c14089940c0e041111090741107100d41a0000b644540c1170040402130008a60407800c244011744c13100060300e180340d0046045502c00b503400c0c00c082e000070a5010a90b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 59417521 1250 59416271 59416303
    0x30c0712120804021c080405040f021201140604050306100305121306050304020a030b0f0403090f03030905061305120a11010c0209040b041103030c070f0503010c1e0c120509040608060702 82
    0x303915a80041803003510907a00d565000d20010511743e0500101078064001c84900300c40903c1300c6400040031000307901508499140c80e08905005002160600904010000000c0c1102d814260341c5e40000c0c0c80c0c1071040d10514680301c030420003442400350030311801c070f44840c04611951820350300c1040c46960203a1071046204200c0d0200220301190359980d0f00b10b0013190081d185850303904200000803103070f00c02510700306d001c070b00c41c0c1c074000407501d100d42d05240440c0e4054a59100c00340c076200a1064603401801644c1c5419a41007001c1086da40704404855850702c940c008112000c0b86150240510840201c0360f4140102100f8480040e80d48485c229405035110140c8400e40e180c44c0352a1001c1c0da815100d071545070002140042c0c034010300280b006e00b16180c0140562140b66520245030032141c00000784400141d607540000105002a010103190315940d1800c0d40340303c0f001d0340382c4609501d9901c4d101d40c0064800902070030a85800e0050364040c0030420054449800c050360007940d40c5101410340c0b600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 59418771 1250 59417521 59417537
    0x105240313020f040504060b0f0405010602030d0216050115030611030f061201060503010606020f07090c0206060616080403080702090f06010516030207030804060201020a0206090703030906030b061605030c071212 93
    0xb1501d500d12500f9082034083e009100b82c0c05d0510b8000003500142c11000e000d04216026242c1a00d03103406240d0484042d50040c602d40825002c0b400301235803060800c80f5013078800c02c0c02c51740000e80900c550224042041100d903952802d41ca4140c054500504000d80032440500500c00c5c40709155405607040441190941c0c3d0300e04554101a000d42526882250701d075280040000c0c40c01e80204055512020510a40740f20716241c1700002c00720b4104040d017400507480701c4000340b01c0d400c2c08402070280b11a010600310800310103545080865109403c200da018901007110320840c104418a16001070504600c501c8919000e00000e0807406032116040406030f070446405d0034907000344900ea005d5600446542d54032601e03524040d000c0e5010703540c6a0010700c1442c2c0020036404011845000350390f070558078000524035000d4102c0150462810b2543d1182d4200010b0441d03034500c0c0200030b203a5105d58041d5855031124a00f030380c28914654030001c805074540c0c5544001401303400084951480c107080030381d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 59420021 1250 59418771 59418773
    0x30c03070c0512030a15080d0806030703120c02040b040e060606030a0f18050607020f07031203060e0a0b100906050f0d0618020c0105060a03020105030414030f070305030105240313 79
    0x252041d92000c0542903000e4a80710082036003150700154865117111100b40060f1021702403a14120050b0310510303107541c214003c010b0706184a40203150304a1030044c21030f84135a03103079206d258122990b8540440807502d203490305800c50404c1e005248205078119810083c22581c002c1d080d4a990000f481c203445018000300061103002583d202c403800e524010300800c00e06516a1450030704580340402500c8070320494002402c040c0c40090003603100040b4601622840d4516600e5040e50103405c40140241601c4400100b6107500c603201292007454403001c0422003141840c10b0101ca841e007002e090081080b41d104c02e101d120307008003c603110040511803c40d911041c5040e50b01c028141c40d003001640c0c0e9040401100c400c921900a40703001c0342c060000f088152202d034200041c041c5540300090103d0014400240803407401c02c0c003140440c0c0381e0307029030307280101c0e000c8030303000c00e9000e5001200890404401404141842107490381c14044091541c42c00f51100070500d42c0501000f000300700720311910300c5500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 59421271 1250 59420021 59420027
    0x1501030b1501030608010906021213020a0b030702210702040e06060a0311030c06070f1103010504030806010c020f1f020f0a0c05090a0f020d0207060507020c0109121106030a020a0206010f0b030c0307 87
    0x44c000700f030749000800c00a030607807034040069401700c00e61a170484108404a52a8000100b000404581c01080c502c00c0d14501a0400c0c40b0360001031011040d802613429840c0c03009103d0070844403443c81095060707900c10403441040120341c45020006d446510020803c0034503111202c803181a40e403c2903403182d0003110400000e01d480c0b10914050380001c40400e006040118100e0100d802604c20861042c500c1e07010020b1500303c46046801600040318400841d0155001c0d01500040a0000d4000303a0ad060480000c92501c02c12002c030400e12254242e4100c034250b0f81030101070b031245030b004040c2085440036101d84030012014020a4410900345011440c000e0442e840406c140110040a40d2544c40c441348071030080d00001810b4600c1418200040c0380302e8800301e118a14090f05840d01040c0a0809440141181e10448211010b040844580c0b4480e601c0b04059803148006e0703440541c0d10b00001c00300030300304501a03216042c3c6046d6103034240000c01c0b001003540d5001000c0d038105a103c0c0d075040f10403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 59422521 1250 59421271 59421281
    0x1050d0c0816150c02010203040e130203070303050306100c050606040c0909050a02070c0821030903070b04080406030b0a1a13120501050103020f0612060f0103110c0a051501030b150103 81
    0x80850391040480300840d40c0c050702e4051080302e0314508450042825a0002e550103103841c54002e0058204010900101204001d0280c000c802d01c4034608200705290b0100e03141c940c16800a801040b004410030410389002c281d00308034891a4507003900c3e4841c46681d0036907070741c8003e00000e22031920b5040b0011141c1c07180b0312000040c4920a014003242c02d0801c01c0c10002d501900d41546e01c56420603011645403400602e2070a4000c082120b0842900800950030541c0c002500307400840c0820058403000c030345008480f0303009501850340c41c5c0e500d40c900070010b0308444003048194054241c8140c2004244500035411450600c0f01d0078007035840e031080320801e44031500c5400ca0000c11140840c1d03501809015407245040c0c902c2a26011200c582b42d508004160040001c51000755011800088180c108842040c8a5450604005c19181c610039480c0b0600d82100b11610346560025200006009042000c415503045d4000098100c2d4110b40724080d254000400c0050004081da006a140c0e907c03d500c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 59423771 1250 59422521 59422529
    0x501120302100b0f090408030901050c040b070219050d031206090903120b031c030e1002270d020411030906160f030b120322050f03030a1b06020a0503010e0a06050901050d0c 76
    0x45c130369507103050703c0c101009404c2551021150761030080010405040d01d02200c094881e02d41400d03091440c0c035030030002c0d14800c40e0300c1c28141c10585040050a92280f00b5412011486603d4840f840c00c81501004100c41140e48500c090509241003074002c25000072b15484802820324000c44d44040b0180071030f24000f0074045440c0c5400c0030722200d5104541c1a4805200790740c259007a00d215118641e115400e03401540003054400d10f900a08c1d51964a1003d4aa40740130383c054040000c1003644d80025003104c0e45e5003c4c4101005001041080d0300d641441503540c40303840082480308084000c00010060040c00c00010145513032140d5182d141c0c0e031417020701c0d200408024216650b9651502001202c0d04400040301144554500045614a80542c0d04491440098021400c0c4501c4d80001c440c01c9103403520744510004007900d03000c01b04566000404c40c40708180c603101d80d02d516140e2001118000100381c600e81919000e4280969541c0c007000d241120400c880b81024894070342891125840c1ea680 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 59425021 1250 59423771 59423779
    0x260d08061905131416080a0f0e0109050a020108010803040f1a120405030405100512161b0b1e19020f090d11010f080405070504090303110a02010501090501120302100b0f 74
    0x200040c4902d00d0b4204043c2c2404002199055449175595130805901c3c1c0d000c0034001c642e81e00005031051080d640702c82e50b180e81c40d0701c000c40c1c034144210445003100c8020000782c034541c00500c2c40c81309650b00180c5490050110000070341c9810300e4250b90342c040002d1b90103003140f82150400c221080240c0e800949050050203040c965050416140440d41c9a100b4030601380038001044c4d080344243d0007002510b41304074038404d03101415038424850781010780c42a20301c03e090005100e6600c926203000b1200c615110700c00d12135501a42000d88a048d42229520320070304421003100c04102c1e41111004050400040d000005600c424200344d038280b82e07005020b0b805810040500140c0203000031a42c014020b05000e88800200d404078001c1191003c40807036004c0c01079886000c04004605045d4000100107010b80b0300064904144003040005500912107040140e44400040c0660300e040d11402e030040001c211b011019203003565010f5110045a4018002c032a580c1409242507114101d08510f5104010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 59426271 1250 59425021 59425039
    0x50c011a03010b010c050a020402070c0e0c03070206011202030a1b2c0117300703030506030f010c0e0402070c030501090c0303110105070c0b0916260d08061905 70
    0x4501a003400e40c100d005511940c20441001c20030b500400070094032a0f00030000e050901c1841e0240300280d880180120f89040c4100c0c40010101329141b441d6004507241c1c440c0f40d0340d03400c01060003450b0803410313005a0801c691a900340070042c0c2d000502d20301c5180d80164000218801002171410a48080e800060b40e01845004c1d29480030a04c2d03000c0c4040e0400f00199134030b0342d0302e414207141605010907150500354004000010301d40c4407840c505000c0c5100c1d004070202a4242c40d0040700310342000e481140440d444506000c040d01c1c2c14448003012444003002040000000100200303c84690354106008940c0024a40705103c10310100c0720286130030000905c520300d003904d00340b2010882d600c4290009901c41842540311035044c000c4a00500d034070351350a0289400790f01c0d9036100010107070000110707204000c1c000a0968440680303000801a0040c01d10800c000c4082c408404020b40b5082201600a404618401c0344c101940c540c000000f610010507503552032907200a8820982c2006510035254 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 59427521 1250 59426271 59426291
    0x1120e06010807051c03140c0a050a06050106020606094c030c1205060703020f071b0501020c04020408030318120f0a0311070506010501030c05040906030803011706010f1203050c01 79
    0x1c1e0310b504540085d5080c220079402c2440010556010410040000c0c82656502c0c91841a42000d00801800d00090321940780141d84c071285407100380c9000b2a000d1342c540d40100300c01078041c08015440403066030125040d103404040b4415403400304208610780542816103200c050002c0d4401407210144201c944040b040c20062128904040e100880e41c941c180031000c035185501e408200c1650b0b6000b00100200d4407022001d4000e50045000404806003d000320404140074074461014140114601e00344503082000090503e0000320509000d140104030800100c9000402c0700e6011243e0015080007564000c41d150412100c840009044000824643c4680c58444003d0681e4411034404100c42d5040d1411094079008000b80508140c201c0c100421843d4041e402141d08102640703012444c15886000440071075415410545000341c0100041c040c0c00075000d640e10f111000c0a00a041a62501a000d8802003d44c080c0300822040085003208143c0124251000e0001c1c0d48024060036003d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 59428771 1250 59427521 59427523
    0x3090f032d0c03070303021e0d0603030318020102060103020d020117090c09010f03080a0305041103030a020a11090108060103110316064404050a021f030b0a0b04030201120e060108 79
    0x1140108000e00d0701c110000030600c03140300040300c002800d101e0266051800a031002d07030007908620302c0212001010300700301640498010081c0701181c00c1c0100082c1c01e078110b0034002c1c116410303d1045100c180da40d0000c00050303078001403a2411a1f90455208400b0207a52004840d800020031513041c22540345010310600040100d4075400526058881c81d25aa07600c079010303011400944405092008100481001c1512a41045034000c0c001c4000e01d90944600020a240d44c1c4511381010050300542c5085041118032072640000c01c1003201c18503801c1d41403000c8243c8550301880000c00000c3c40c043c0100300ba8405100d0b4904044400022143c075654401c0040c1070110101034401000c01d00004070001001e0502c0141d09088a1000b030a00d651a6050480d00001000c0e1040e40c00c0e1248407042c0c07006945051103509040207010ba0854013000c028405801c0e1110880441e2142d281d491041c854401254151400caa4091920f061141801e00801e0b005005202d02e42c000d17030103100004142600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 59430021 1250 59428771 59428807
    0xa0c0b060411030c1207020606060307050a02120d0e060a0b090c0a140403060b01020f0109030f0f03180302030909090105010b160807050f0c010906050408190c09090b06090a0b0f0603090f03 83
    0x410848020817660b10004202e880b020100d0f011079002a00344046000c0340d00c42c001030185e010280c01103030b44c48a00181e004845410441101c900d01e42c45201d18242c60400340a00c03a007280715000240611201500010006200180074040000000c110480b11500c03e51240e0900003168a071b00790b81d20307242c0c2400c40240ca0803038906400352040850201600340c05200700e4440a8051740c590001c2d54400604035892202120600304150311443c04a07900c2d080c2e422242c0b4040e200790001c5a40308041c405100c2c60060080c000f04251340f420b001049401109001c0b10080c0384a01400310b1002c51a160415041c001c0c150064018803d004011003200c078002050214400240c840071b6686035124000c444e680305500540e8010740041c3c51541f024001d0804c0c8a5106101d101c07400b5000d03441d50000411160001e505540d074801c800c0500c18603007800d42e400f030380000a159082c0f00f5500ca02c801b040d100032058606030b005500000000301d9a003c14440c480f0079440d420f00352650340d040d04810902e01c034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 59431271 1250 59430021 59430037
    0xa050f030115110a030f0e0f0909010501060e2209020d05010e0601090b04020a093305040f05010c050d0e0a1508090105090601120f050102041a0a030f020a0c0b060411030c 75
    0x82c1d084580c4010f55a0006060760800d0b40365036850340c2c000c440f0000f110040d10100250360404400398030300d40c0b141d5440d240c9520030040300c00002265850401c00801200c0f4800002c1d01070340e010300c05044000b80307130000c2c08200340f81d006006c21141514808130b242d25442020141c2203501e031a440344411240459030604a40040c4800c2c0124140303d01000700702d1040b16894000301d4941c4c41c04101c2c41465500d49280d800402c1010f82502c0e0440f0090035000c00c0c015031410004000041c141720038460000310101824080c6041a50030100b9910700b0f80e40c0c8e02030100303081400150180d0402c19030b2403112810246c800c000c510300c40c401014001078100441682c1d145515400c140008240312000a0000c1c101d510556103200c0040c115140c0c2081200304030019105950204004a0030070b82103580060852010300319030342d80e00104003004044480c1d804103020a940100251402c10758085078521280760019601046510758000003070050041184160244002200304107a43d400500602094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 59432521 1250 59431271 59431277
    0xf0305010e01050f0103091103030309060f0a06030b0a0905010b030f07030c05091012050708190210080105031c020304150509030d02070b0a2f010e0d0509030706050a050f030115 78
    0x140d072928580000d408007405041c3d007042e450300d600c815561083c2c1100c05040d000300032030b005c80340791140401e065034400c550203c91684880305100358403481c418280e0b4045040b1070104845401e50391a5140d45201614440741141c940380c5110500200398040b960300c0000500b25007079040925246501c80115200541d41e00e4440300e400078840c100341401500c2500b6203030b4510300060908000a8403a01c500a00782d50360302c640340022840b000200084880c08008035203481e09072005104002e00f0440303070180740c001c00000c3d00041141d514001450810351600105041079030120f05012032640c021680210790000c401c0701540780710b64101c4000d241c10003041e400d940014881e01c1c016aa80c1d000703440307018500f440400c04102c0951040c90070602103ca454450301785458200c4000d48404903144002c1c0c2280d55131404500420030402503a800c3c0e44e06400d00c181000c078803200080d00d44003d80300b1070040c000001240c030980c0d03104104586403000c4e0740c891035440c1d584541d220703100008000a44008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 59433771 1250 59432521 59432531
    0x180603010b04060e040303150b040f05120a051b061201090509010c080106080601080c0f19120b06040e07030b100c02041103010506030402130f0c080615040b03180a0f030f03 76
    0x518100360043d030096594000504841e6211550102e000300010340501c0080a2403c0001c203103880144001c00c0142000b5004685c0f09086c00e00300448410b11040d614810360080e4542800141f001c2070841032020307001ca60580d40080c2c00085611445000d90084285603030b28000b00310002c05070b0055019254000080018942c000415100c20500b80910000f01301d042c070002d1045c0d0301c50304c400740d0302418860496040080041c83c00d003203500f040301c008041102080c11204401e6104c0f140254a065000d028440c0b002e0b14404204288078502501381820030700310014000034041d13003014804500c0503010003000e8914103802072801c46540300403489542000d0a00702040440400d490684000032701c1145183c84507820020940801c540d02002c3c181c603180d841900f0205032140e020703038011030f458440e080d01d000300c20031101c0c0c021983e00d2108500c0521080c4111100d80c2d060301e0f44141c0141c03042032001c66801070785191a1059600620960340015038800b050362001d98080088440d8505111f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 59435021 1250 59433771 59433791
    0x60305040b0f10090207030504050607030509040e0d050409020315120610060915050c01110a050405030111030408071401090804090204060e0a1811070c0f0602100504020306010e090c18060301 84
    0x140d1180c1070740d43d488000f40d000e03000c1c81030200640c01006114400e0800038078040c0c0d103101040454020220031343c04200d02080b441400e080030301800c0388990b00100a05011041024003520074025800303521426039012000550b42c1c43c0e090180342030014020480708a280d145007800b9039844080301c4182d1a5002c100c0e0014216009460305c3c0c0903101d4040e00c410a444480408407110382140380300c1104c1e0364035129200405503009000302150060340d9985962981080145425501e0405000300c0703642d4100100300105d00d07000c0075161000d6002100381d0741042d603140002c1c0075081a1201500e14800094002a1a01c059004000b100c1c07071030301d8014031700f00700c1001c118a80c10103114415a00009083c0ba20000c0301c84d81c00102e4107031300110301e01e0412026843c1c0c40324000998024402108201c0c03000e1107115010880b05820f1100b00703c040c070040c07505902090f111034061082400e1907a00001203004500300b4407030040d843c01d024224070709807210150044d040d454141c0d2442d000703501e4418111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 59436271 1250 59435021 59435041
    0x307030f03050601080105090718060f0f050c03030a022101080105041a07080402012105130b0f130b0703090204180b130c0e0a0b030304030c0305060c0415030507020115060305040b 79
    0x503c40c040c141c4075a2060b03841c144c140200c03024010f002c813040000c029201110300030801d00355009840b559460039040c0600e4200a010707440030068480512906125940c10010004103e0b9880088000050707200c205900340202c0d80c22809201881c0d03001000e00214002e5415800f113031140c2d00441501201291b040300d403002d1317520b003601c0705000074800c400040e015501070a42d00c1080384682c02040040041d03243c44e802150400d4502003005600000c2d25801d02100c101100d030805802d0454580034144a0082040010410340041c00b611011000030071550196120110f1243c0140c004e01c00c0b1914180c00c0848604031480032102c2c14090808696039890010030200d019611540c011211400c14200c07100c2c88000a040c000525180c2110300603584080c0003410086200740d402074400c50652030030340e0034010010000408620107000070003249104840c0d0403043d5115080014460300c0d0000100e01504e900c0c1410704c4c1072502c0510000d2020b505da03120510a80c0941c1c44403046844101000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 59437521 1250 59436271 59436281
    0x1020c09040f1e0305180a090608151008030d0c05042c01081b04020705070f06050705010501060507030f03050603010b04150602120708032e090e010c020f2e020c0307030f03 76
    0x2400140c028850711003945641d180007001d004004181c1d404650381c403040c1c441276912942092000782c104003000045513440080c59038101d1030208003903010701d04102809030b481c000c1c807400c0380409403500001001c1a004000301d801910303440503d15200110f82000024100c0d06002c100305442d8681d00001e4141d5010510500031022848150002100c3c03c04001c065000381205075214040c080f000504166440c030880300a01c95529143e494480d141842421540d050380725209014040100c4000250302444031460744400781000030741c0f6110700010034010310160480707980161520591410162003e41c00c64100c80d166400c40c0c00c0c82e011024000031a00580c400182401800d0011130f8022442c400b1111a942c0c4000800c2205c2d02204034482c4400a1640300b50301e03c0d80e07200c00c03030312003c2030a000384c008040039400186409a60507035000d948203944a41203000700080203500034540782407804902891440c00d015510f0b0f851034403180d5103a500c020811004100e0440000103240e0090086d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 59438771 1250 59437521 59437523
    0x9050c1504060507060605060d0506030601091b0305071803080d0b04090f02040e10111b030c060403080c070203011a04050f10030b06060705030c06060a05120705040b01020c09040f1e 80
    0x109410146030a0060f5016042014102c520341c1d180c04002c0341d6a15203101500150880c1e0002184600f000d1b0b0a050a090040e0480300c500c605054500301c0d601174500483c090181d4500e00050b02c1d507244813084407a0a00707812144060703881a2030000030f12415001400d10005403c8003040700c1e40c00700c410001100d04000f00100708800e41b0101c2c102610382030784104903c071a0035050701c00410584e105c3e03d044403541418440040300206440c10347c03508281600040c072032004021460040c0416140d42e85000080000701044020000240040702c0340040d240c901d640a0024405500800f4418120300700a41c2e036180607510b080300054202032002e02950041501000529410f402d5407a07510141d070000348250382080d0104078070300001364104000d020307201c1610040c00450411004209842440303a1249104005807040a20400340129040088030720440380000d00040890040c0d0601511151546d40b00040008100c10302036120005090345124410b6039040d01d0a00d2040710480f500580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 59440021 1250 59438771 59438809
    0x4060b04050f1903050d0809011503031722080301080f0307120503130b041506050306090705011803062a0315140a0302060a1713020d0b04030c060203070309050c 71
    0x10054110381480f202d81e1034000c0c903142c11926115142e80f80d151800d103038a041d11000880c080200619110207125685082c80a0052184410301e55100104451041900c42c1d0007901030318007040361811504460010200c40420007809800d403820800d005070007d2107020418019140760b42141c070008012545a10350143e034040901103a400d080340d0350340004081d5188290241002400305004080151041d4411030074016030103040c5900e90295803e59022500950100b010f0004842021480d00c0aa890a00c0c040c0e117041c4038050f0180e140541940064120b614112400011200700702801940b0041843c8114a0b034004850460480d103400384480c910504289013408030208891000320107050041842c01026120b03000030b481c07a44401e0030b00000c0f840300f59100050201c80c600d2740740c0c002030303096240180703c013941c001c07a070f00920501c07004100841c581c000904150040807052100382d0059800c41d100d141440014008103a01c0b081502d60744110f5100f0805807601182e1010b40b10860750b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 59441271 1250 59440021 59440039
    0x80109090c15020c04050115110705010504050f0a03171b0703031202160501060603061d01030210110f0f150612071403030c151e010f1814070e04060b0405 68
    0x800d0002290030491050111300a03900424420713526401810f02a150405ca00c8140709408040500818928100000182c0085100b000280e8010341a501190f100f510801c0350000c800e4000703609810305810003400c401140180500c43c00d42079020784403d0029410a40480c40e42c0b80380c4ca40e91300800e2000500003440b1414043c100c0aa07900a4a802d00258003900d18548055a9450a42e007050300300e50300207980c510007000400701c081c00d410030304000304540d6132440d4156000b003100302d94071054031028440d5940e02480c100408005030840c50350b4400a8844007510710014903200c440703e504400d80c1c0da16500124400745480211128035400301c0d0010041c1c14a80386113a00b10310036012140d5854041402285c10600382485500201070a803040029a807804040e2081145403955102e46105a100010300642003880b5010b029070b55110610751411080f049154050b02020006010700e840001c20b200949421101d0003c1d002400c55003800000c1e00d8403008207460241c1d00c10268000022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 59442521 1250 59441271 59441279
    0x506040305070606151107090c05040b0702060f071203060905060f01030b0102030d020d02091504120f08130e0a0b0906030a031211030702070807090506010909020d1d030901080109090c 81
    0x70304000c00580e4800c000200306031740c2c0c5100045501080100070740c0456155030128020000a0000202030411241c040100d50080e1200030950b0049008000008200180000035552400181c80c1d902c2403d52146a42d1615031a00c14944d869110142c1d010905050012a025034140512440750310044c05c540322004c6020011005441c5080001d0305600081280011224041c001000c8204403190056581d503450024010300382c12201000b80340490070301c0140801c6003050344c2c49280d643c1000201606030480d092003203981c07240c089081e12003251010002645281c001c80d1074840d02c15410300b003007603000f80f009102a05804070341c603a84c942c01c80100365000038003c5400751400e860200c000038041152040c0d161542c1e20645500016a110074030400850ba8100042e0300034204281e0240032030304183c40040c1c242c5030300340500092241c01060600708001d00d54480564103089100c1085075112500040d03440741c2c01186c1c4a07000991110011481c02003500a05259692002212200c1031130 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 59443771 1250 59442521 59442527
    0x306060e0f1309060507021b060c070b031504060609080c010801030c18020c06040308041b06050306060903010b0a0902130e040c05010302090111062503050906070f0e04090804080d0c05060403 84
    0xb14500e402d58141d40e0582034001c40e12034414640320300e410b82c00911100c03c1240114070200c0080d02480d1180c00208030201c0694404101032088459040c8040c1d26501d41c68204090520007200407508903140040c002845036103c45d216003190058015240c0b00c510344001101c500509000c081e0005401c50340c20044010f121038054820180d01c10014103000110112609001003514250000b90170b11080c00248228840780d011019400b503180340e02c1134640800a450f50100400c07140c403540f40452414200c1d10290800d4520741ea000340f0207540385484011007802900003110b9982400e8080c07001088134160304d54080c0c040d5810010501060b403030315004402940c028005c050401034049011810204208442c1d406000031000e1298100303030903016410956941090f00003010300b0042441a60b92020a42c0c03a000403230b61900d0a651265150192850141d01915582051402c804c003c248807064014106481500c0b0a49408500d43c1d9411540f0402c0b030103003d80303da00035201060000740 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 59445021 1250 59443771 59443789
    0x31d0a05010515100921060e0109060506091303030c090306050907081b0319240212061c0b0601050c0304140a050a030203030f03040f020a1e0501081003080d110301150306060e0f 78
    0x600e00005079182c1b5501c1c1e40d0329050702e25550460045039180d44442e003c104c505e0080300d50041c1c0c01d55460041d49070961401c1d0010b0340036100541810380d41e02005001071701c14600340b40590b811000038001810040401941c03010188500e20247c090414140e81480e004100c90032000380007401044801100d2945440c1403c0308607003100c4015145c83c000e840100d0720149a030915441c2d2000688a081100d01d14040450040204d03104540070503014604044442107007440c190482c100d03081c2c42da02c0d5401607031144280414000a0300c0041030000f00100141c42c0800c42c0c6d0800d13a4070f0016295980709101e60464240002541a0018440c080f0403400d0800075581c0103004815000586046070049a076921040c1c00543e103070a040142c59400860390388800c4002e00702842c06c04124605000c802030750102c1030000900144001a4201c4174060f0380d00514140740b1440041503407540e607028002685c003180d055440c00b00e03003003420000c1d0700c9000d0b51480c40902c81c042c1c40030200801075801c00c0300b41c0d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 59446271 1250 59445021 59445059
    0x30408030d05090f0a050708010609140112020d150b0f030607050a14070c030f0605060f010912060204240801060302091003020a030221060307140d03031d0a050105151009 75
    0x84101c44c000005060108044598140140090200e090500d00d11700d00b520156000707400c44509040c2c96904800f14407103c9811a11035070070441c00c0206920011f80608001203000e803410000e100301840d2400691701003400d17004220341c507440d084906c405050304c2c0c1004544041c0802c1046c0407040302c140c080c0f034142a1181e03920214528206095480728070419070b03030300141d404140e03100d0398104100301c0313100c2e0070303080081215404403490b50f030700000741081c02034014040c26103000224174081200d1601518050f00b0109001e0200301220001d040443c000328104200091100380006400d81c06442110348205001d8072600001d21110f1061300650b1104480c00304250382046481405c440c08a0040c12480c0040b05551050800400705813500b0641e41041e82d0f90401c3c40c520281c0d90783e889011624055141c14042824422180e2099012202d140244d0030f034003800108108110041d0701003445030145041c01819903880f03405010002074034075200d8000c503403c41018041241c0703008440c9a01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 59447521 1250 59446271 59446273
    0x909060d08070503120a0b030a020105090a081e0c011805090c0c010f0f0606020705060d0914060403050a02010c08130303050a0e010905031905310b031303090602030408030d0509 78
    0x21840c0d981d059095000180c01e4443e50400301d0721a8441c0c12000b6042d41154503070006010b1882c80c076000a4071140301c0c0340000e0600070000f460524907126010300800130320707060003600d21030038031403030042d80b104c2c10500d0303808550141603048111980100403800c680c1c0307105039107603400c5800e20041c0188844003408030000e0f50781c10300c04201c00010900541c6084682e041000ca111101e240658003501c400340c00240540d042801c0c180015146c035410740307a83c203e8848011825181c42e0904030600000a29204044c0c001c00b4100805e05030440c0c000e0001402d50b80c0200003212446c0411540050169500e400020194803181c01280c4a5081160800600d410009480a242d03681e6800c44903040c00485098002082410030050344c00448a0240c000e4280a491701d03000d01d2621400c1c40340a2245e0944a62a105007401200406100c001420740c50f08440c0d500d00317014082030110040700904400040080c28040f90781c41c408415181140c1e014030065007071580340300c07100001c3d1000410f40102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 59448771 1250 59447521 59447539
    0xc0b0f0904021605060123090604150308120109090f1118010810050f10030201050d060e0403030204090e01060503030306040c02010e0607030504140a030c020d02031e0f21090906 78
    0x2032965244001d100700001000e11036122149850701904125050b40300c03400010315124021105003020101414480c0308440390f01d9144d941038001002054028800b150a5030001e1000c0100150000140340b82e800b03540c0d103080943c5c5d8401035003003941c000401c01011200407480400018400c014404c5c601b8500800a429555270703074100c3e454234034090380100c009074810703180e0340c0c0c1c00c0600c1d11546412903218050075040d4508520400c901c0c0f412440000d040000029403500100ca00e42d02c9540a00790900503940181858140140079401c0f5014403040c2d680313000036000c8454014416401181c20290145086580d0041040000c1141c0d608020641d503c0700c01d0100070003c1405824443d20a41d01d00042074142400c01500c400c100c41011a00c2d9445542080003003a046030301c014145a040f00c015100300d9103403000c00d0078445038040c1400740e904081034050301c02c8008119010b140c640b4500b21008a24240601a4410139003044000700b03203410000d0340d0840c01c00118030740e800703000a400150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 59450021 1250 59448771 59448787
    0x4050f0d03210203010603140108072714010306291e0306040501090b01080d02030409020706060503030304030e15070201050702060c0309031504020a060903120f1817010b0d0c0b0f 79
    0x1c14007140b850000b00a83d4000b0040c04126018418005000d9103805500115814850816964040d40c0682c0340422a171401280300e00720103188162004c0440d03102030002d000d030a444440c40c21403c2c00200e0b0840d09007074110000c00d80003d5101c4c404c909860403009e18020210521265440e90f03403207100b410b10b0344940c4107e1901c041017054020341c031500001800b0905800c0c050400d14041c0c1185080b900314071840082594004103450070ba07919003100507503a500910b809001000140e20044d00340c0030120401082c107400c40c5584401317010a40e00008410050540c00c00103110703103403000703020803414000040076040038000303040d908200204903031a2100075000a442c202c1000c4920341030180c0380b0204421428010b031840000c0c959410082e1059045070790b400c0c00c0c0400d4400f10400c2100914100404505c1052000d0070504c84200c09408035859a450070000f1101c80d10030b400c998207120b5042000e00f8406c901900f6140c00642250003a400c00040385c803558071040588401e00000c0c010b0305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 59451271 1250 59450021 59450057
    0x4051507050d0603030e13020405180c040e01032a050d080d0b03070e25080a020706110a111218090405070b03010b0406020d0e030c0d020102030f0d0204050111010204050f0d03 77
    0x18007a40c080c1c1c035141c0ca0340d0094010000702004054800804034010320080010f51104bc4020b0000354000941c165140e85a10400900d80503a41c04150301d405890300001c14800c40ca40300175120a5018403418107507448024261807020346100e159000303554621000d0100310041c016291400d039440012810705031380000645409141c6e007101d54a298200280a9001e1000b11460300d144922050071b500e55850038005072a40c00d004200b507070385640002d00403041051946c44801411098108561103409074031005001103050f44141c00180708207000311115590103400c0c1c40407130400c51894604507035014180414a0400b60044070b0a101e80031002c0f034111100d401a6000e07040c03140c0003035215480e1000c000d151580807803a101c20b002c900c1c10f05958544002c140840c034801e0a95070210000e50b90310040340785105250810b1100c28010410140302c0d03465800400803128241c0e94243d10f21507402c030303107400c0344658464540d011100c3e106001040c1440c05005074810f000381008008000000548 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 59452521 1250 59451271 59451281
    0x801020f0a021605010c030309050a0203010906020901030e010504020904060225080702090a0203100306050c0909090304082107030e0604090207030905010206010603020711060c0f030c0109050d0804051507050d 92
    0x100c1a5200c011403030940d0940e04000650f107400741001c0c044005850800043c000e031041c03501c06400c05460b66000c4017402004c024501d05182d001d17000b000302440d107042140080d00f0000000e40002e060507415418100d05000d102c0c0a0364005240180c16180e96803000001d40c0560644590104a08140d080841d4003000102d201e40c00f64400e0781e624020b51042200c00c50008200000c2c2324410320134000786503590f114403425070b40e1108000800307881e0041003607024050490032a03030014184080081c1c100d0040081c000f101e02030300860358040512020001100b1300d1203501c0c5030740d4100340000004a0700c110300c0d800101c50054001e07440c140e00d031421031069903c40041034000c02e802e01401c2006580c100103150042480e403600314103107159a0f654010017103031581018401c010106041d00c11800520000702c03145031481c01c883c0d0ba641a0000d036030103407100b00000e64403406141150035840b40181201480780345e01c10007901e03a9086001c0d40c0c09180c603000e0f042d071040000501603014052514418 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 59453771 1250 59452521 59452537
    0xa150e090d091a0306010f030f23010603050f040609020f1f08010906080a031206120c030606060509130513051e0118030822020a0b0301080c011d010e0307080102 71
    0x50580d41c001520041c0825038258410846159001440ca0910001da001d50350000401d20b03010032911060b0340110b002d000200a014078844c80c00b840d40040da0b01d445000c1c00710f0b152226201406a070784800550848008480100790800c10200107800209254400c00c1018030080100010000c0d00010030a2428120200002c030b140d4030050700e400980200741d01e80141b4200600344401810301e20301540310840c078200101808a5402c12410864043e0800005130050440074050340025082164070ba049074441655031038580000070492030f05c61001c4842600d07000c1d142c26074403d82c032240e11000b08002012440c004405c03145280015005011610800707044920504148900d4100c0b6401c4a0b403284e0318203041407a0b16a4500000c3c1c10000d0107521020b58980410303440100c2e008642c03500303820380303000398001c01d07500c404a410001a000346050b1303400c140c04c1700d2500d0f0013400152607161005a00d011107a400c0f03141400d0640c41110383c2182c02c81c0141c207071545d0550b0317400d540b42a80c2007465 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 59455021 1250 59453771 59453773
    0x30f0e031b0703080a0503040b06031b060d02120403030b0a0e010f0e061309031e05070b181011070b07030b0a0e190f0c020c0102061902130b0a0804060b030102070302060a150e09 78
    0x2440244189c00001940050080300a001d400342c0d4000440851301908141134010790b0017103203214561900c0da054403c0104c26010b2190a881d1500d001001004568545c9120f000c14000124940e109800075a060711151100c084000f403c24420481c1c0c0d00380100101e61040502000f600750034070300e01a108805200740c484002c5641c80c446e1492800e6928404d610400a040c400b400c0443c90100d54943c010400b9400b403041c3c80c43e2900b140e0b003090407140502c11582d04200d401040448500014086a8042d220b1000340ea1240d10044064581d00500c041d40000029024080d6907091008a40c00c1010a500e1504000040d80000185d0707407803201d01a5003a945070b14407040d00f41c05011500001e4001d1016141501c3c02194003480c0030441c2c0403100e4031950101d83c2414484502414a01030690200f4042d200c00302d00c40d0050441d10f044a00701c843c603003007290311142400c05000391030a03e545034000d8400c2e581d5400341c0900130540d120740c01d103401425440004542032140b0329079005589200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 59456271 1250 59455021 59455027
    0xe150706020a090f0510140714030703020a06050c0c0c040c0e0a080c09060306040210030e0a06020403200103110702010804020d0f0308011403060411220507090303030f0e031b0703080a05 82
    0x8401303050310120581c020340c050a01c1d10041c2c40c10690042401907546440c19040392100903c0c01c05024607200000310400d00d00c000101c1100307161700090f2491101c2e1107841c0910440e134503406008203c1c00740700c1c07a598081c1d118014403400d030310b080e41200751504003d01d041842d04000100160314204164046c003915001583e1010b050b0401092041d0b0245059005010a0a0907800b203103041c6030203039480040640e110355010340c0707030014410030313440ca1b4100000b50344440d2641055103c100050702113000d5800444960405940640149082e00004100d01e904090281d001920b404c24001c0080f603102c0e10018940c0300040340500400380c041d0190795154420340c101080590480202071403188664800d0040100140e4405401920044256442c000e59940741503417404a01c900043c000946050004211104d9032004443d01268003da40c1800450310905401d01105c40142d100c8030160010003600005e80800300b8080040c450082c01c940000c0c1e40c94172100c0c081e41104000034001a000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 59457521 1250 59456271 59456279
    0xf0111090103060b0306060715090503070c0e0907080607180b130602060c090609010f030b030f0105060307060305150d1a090c12010c08071206081606020106080d0e150706020a09 78
    0x1d440f500d409000c04600c0d803441c0d03080050004a05010704034000b800059176540140c07407003030507030400d0b0010b036480000c50351110103038500b14034000313024080c0b540201d03003940000e0485000001c0345000c80d4100c10250001d500c0302c5404940b0140e69000b9401303a201f8040c400594207100380001d2210306640400d680d005814450700070706020703001d041c2c400d14003414804d5518607030b07940045030709024007420802d44281035064140d014001c41d05019a15000f41a049000c194064008600c0765030120f007650340e4252640c100380c0c1110001d80d9084150240c9070a000075608000440e00c00043c01201c0e111130b0b0311003004019040b02c408481c2007000d500700c2c010709040b5042c42c030701e0312804007508030080c010b0340810b08009062190091514041000d14041d800b561030842e48000003070607100c0c0a40da20707a414207602481d20092032244000540c646680001c1c1e0f000c02080403030403580c0c2a030300d40314001d00490810840c075182603a484132450701084542c0028801e840100031210341030b12450201850 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 59458771 1250 59457521 59457527
    0x18100e040c14030d0504060509040603060e010b010801090c0c0b04020111030c0f061302010804110a050a0305030c0d0203090d030507020a150f021b0a0e25020f0106050d0b13050f01110901 82
    0x481c002e00c5029910600f10ba40c8801d40010075242030310f549141182c0ca451143e80054050000c0394800303080e032441d181004440d071006401c50b20140200303883e4030300c150740e88114810844d20035020b088001001c0315000c000292003010340300d4205005140c102c907405041c07607030030f42168844803400c2c03003d51154901d890614000d0103903d034000020682103500448903000a011003900810061109495090080301982c0301690f001c007420018101c500da4030386a04d0480e40c0c940c0848500e005a01c196a45000c43d644000304485440b00058454400f400700d56038180c0e034a41095401703e034041c0321b81030046001403000c441d0300710751140b5590b00150b03c2c00d0781174040c0c00c15101351103101e401031035410b0f603a00366124204807030201c603601404900c0c2951580042a00411143d100c00410866149061402c41c0c6c0040c1c148000840d03d0000c00032582e80308104108161600801030210004800241c0349001e0311800d0a08a80505e0944003290340e2040c00c40d003120803d4110b001c0c0d100c408640c058003541c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 59460021 1250 59458771 59458799
    0x20603180607170a050907081002070507470706060608070c05070b0714060a0207020a080109020a05040203060303130e01080d032013080105310218100e040c 69
    0x2e02402c207500a4044003159041e04503009010401c0c0300d45a4000c10319405003080b80200804100d000d490202c4140641c0e41c029600c004400d556612074103c010654545541d622031070700d030b0003100d10700015035050080718664140b09040b00c0c0258480f40500e00345021480140040d0384508400684035080500241c03441a01800c62801c000c00403138420005400082c154050764003058060341c58104501d000320480100c0e00d402c0c00140079103010700000d800c00d5009040100c0c8200e6140f4036180d00c414115080320070074070000c1d5021031021410001814241c0c001c603001040501a240f50002007040c801100500794000351001c0b6000b80104190031381441400b0a0007542d04d401e000720041d41c80020300c171003081c2c4200d00707010703e00003920701041c003880c0c800c00c004090a20003801981f07419070000804040038208070120040303940070312000710000100040e0303095000700748004400c6c1e070518031000003400a1500038031184881010490b00420340c10385200d103108804010310706080075a4004101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 59461271 1250 59460021 59460031
    0x1e01030809010306090b01020c0415051e040c050c030316030902041821090302130608070f06090b12070e0301020412050f0c01030605060403060507021e1b15250206031806 75
    0x81e1601c1383c1079246d40c3e80450003030f02c00101207502003828482c00805034408140360784040da002d00d41c403158025841c20b0454155410b0703011241042860721094050303030280301d00480101035400030000100d80c3c16001c0d510b0902000720389400103500303003191702080407940a82c15414910680e58088010000c0140c0070302061b094500c5030003604011040081c20000881c00028850601d0107000804c00d001544040000d102440840d00110b50751400e605040a0314050200000c0c0742060208100050704100c4000380b51540c540d480d160b950b0303402183d2985043c40903642c155000c120020b91022070402610240d80140e0203000307004030245101d482c1102c1000c140341490300b0b1440400c03040d030741c41040d2401c4030b4200c24040fa1035641c20000701d00780303c404100350460034000c1c55082e00c0c4100008099403840d490101a250041116003003041703060851b8903644810340300304540e8a0040110084031081c0c90f220b411040c08101e607500041071a04216001c515021020312441c40120302041990303001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 59462521 1250 59461271 59461289
    0x90a02041503021c02030106110c03010207030e130f151e141005040e0708190510060309080c06010b0c1009031d012102030703060501030b060702091e01030809010306 73
    0x15103050980507a20030401c101c1014598040b40c8000c2d03000e440c50b00c140744060340b44811581c0f5a1921005001200b0f440305001881c800c840301071009050510032110440c1c0c0503290301074482d14800810040c1190003800d03410454642c0c20114044006010355810309400100c0d01100c60304000295800071110200006501480305003001020f40c540b8240c41d041c103058800c0400e4030461042aa00f91265502426035001c200c000c2054040e405040140140301300e00204510035203c3c03115406444007a0303030886040074601c80811842d4003036803100320054030480840c0d041c00004001e0a0401c1000d03030180c80e500301c0c0061013403620300301801a204000416a010016500b46440003802042440303601c0d43c81020561071074446070b0089a01c0a041b204400c00f0001400b80c022030b510207904142c0d5081e01003400c05e0804035203036029018100c00c0b224058030403410711072680c00300006044050241c0c8941d5a91110203c2d0380c400950324076001e03600900308541d80c2c0d210400014102c0d80d2031f520643d10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 59463771 1250 59462521 59462527
    0x130b27010b060a0e0a0e100314011a01050904060801140105100804080703140409020316020c03071206090812010603141006080a0e030d0e0a020f3a02100e090a02 71
    0x419070b0340e001601d83c2c002c07141c6000b040c0401507602141c2c0320329203074101800c0f94200324100013a07041146601070589200e00c0750105214201c148490a9843c44c10845c009000c484940c007809500c0b800c090100041c1c010400320b0740343d81da62501d600315000d201140720003500344030050001d0704080e200211150000e10380381d422460203441e082000d0140000041c10400300b04100d024001003401590054440c103e401c44d600c4c2040c107a052400300719042588058014072441410310310300401c0c8101294201468a00c0760304076962040020700354008111005101070040b03510700b4a100c00010b010b0440c50b200024130a00081c0030000e080001885010007001c510000d201c00c40c0d114000f00e420000c216401300c1c190900144040c10f40c051540d105079a185040d40b040e0412034009003401815000384d54110140300020140100c00002143c080701d615442c82d051a000542d4410fa6222111000300d803141e040c0d00b9a002580c50700340e40070b035900002c10003482e50404d403800c0c1c22000d8209420040c2149 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 59465021 1250 59463771 59463791
    0x21010f03030504090902180901021e130b0f040305070b070c0801020f0f07050a200405090609030304030c060e0706121505130c05040b160b0a140a05130b2701 69
    0x107030b841030340107504c035040d2100c04400031515107100c0300c3c2c502e080e550702c400002d1901792404c07070007900401e000c81c2e419007180101c0d040310800b01c021599032445555540c1035590500e0100c482c0359122101580d08824100000408543d0920002d0301401c2d10400540c0c0c0c415503170034032404a1038a904064034691041020044040540c003c40d07030590100101c5986404081c00c003981407406c0610f0182031b401204941200748405880004008141110200721310b0302c403141e5666460004035158406030b80104042400301e40a6030360810f901d440b0b104c001c1118003c40c80030608000300c5074409000300d29046910203e0b10b0050142d2a0040034103420a550549071500103040c80c041004510500b6540c1d100b0801c2c10b40c400c404550280c40d4450b4003682e98641601d28040d04e5055100594a421410000c200f00f40304500500e49076a250084800b1540c82d40c203400001404068403c810a195840c40400042c100f010490f103d001c14981c2d2480004020202c5003045900075010b100a91401d00d04070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 59466271 1250 59465021 59465027
    0x3011412070311120d0e09070507060e01240509130512070f0c0602010b1302030c13080a030908060c0403170c060a06030203060117070b090a031403040f0b03010b030402010804030e0621010f0303 85
    0xc6c00e02c2800c40d044502600d0349a07003582c0c5489504006001c444c100a0f04008000c0d05403c50485200c03100755a184294000d0008841c0d100180250380d4000405008071720200703a20070107441c0c0c1034010015071707140b8070100701030402a0b07029039011202078070305c00400b0041c4010521030030000c1c0407070b0000b40000e00803100028140c0e00b400d111015401d90200100f036020324a032040e20500c3c1d000a26107050315880f041010740c0c4142c00300c81100000d000300b20210710980302041c024043c1280d0b000306403c2600310383d41d00d1910350707000b101000003000a021401d0140c20410449000c6c01141034000303400c40c1140103050800c01d05801070b40404000e00300744200503100140b100e048032101c10007030351941c403000002081c0300a01e03400a44140d80e81c11601078000b502200030800c40300c41c1c0d080342e0070b2641e449041c41c1d12800248504000741c1f02c10b00c0082c1c090b5000d440c2460b4054441e15007001c0590655000600b643c006825920805103001d0102008580702c003a0715000d42428400c82000b5442c6990003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 59467521 1250 59466271 59466287
    0x309061d0a02120304051c12020715030b04140114040b1e04020d09170a0810050a0506090102070e0108070614190f0c0501050c030901051302010503011412070311120d 73
    0x90140f8240200c480c244401030082e03402400d00244441c1c2004800700001c8406490f02c04107070340e010368640c40c684942d40000b402d03d00b211002c1045611911740808150024181c00300f00d1500103495150b100030000c9251061400707484e0448411034800e29110511044aa052101e140182014481075040c40070308401c40f12018402c5801503941c01c3e200381c618010303012060340100300750007003000081c603010701401808107015103503079142c80703541c44c030100c1c14104605110b403603000403407941e007404141040c00083c8040e02041c01200c030314541e00c4011740341000c0309030702103041c076080040103116050b44074034141140c08060891314100030040948001440b801c002003028441904034004c400ca00036100d0a0400d50840001c1215180042034400709500407504446154a0700c000500082103400340c0e071b02d0041d01a5031301401c42c0c1c02d08800c0640310030306031651540700122501080c0c0070b00041101c03d01640c880d89100b0001046030041c030405400746c1d918039030103410400c08188a181d00c1091 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 59468771 1250 59467521 59467523
    0xc0503010b0d0603020301020d050f0a09020f0d2a050a05030102120105091801090f0201110d0f032c0109061401030807020d020409020603070306080c03011109040b010302090603070309061d0a 84
    0x10007039a40d000e9284902c010603d5600094155002240340c0c56500c4041d44030500c1003014403200401982d80030b44400448400141c002c0d0301c810781404080c2107080030010520741030301c10000b0360f84880d003080503a6070f00030704d100c2958440039900c1c5040c4a5401d103240d60100418047c1c0003542050b40f200450725203200140140c5005101100c0020248a02e01600792200c0c04c000008010010b201e0034291013003611844141c0c0441c1c00c0740c50100b4013030300002d1410400000c607600c005a50304000303811005460700114041c44440440c2c4190701c00c00d05841040403c4c0c8907a00002036980545c94a04156407002e803584540d0601c1307400400210300250111116640c0c100c034900e0384148248001001405d001c000603400040202c104154140c05902c0328080e41e600d103044501c0c80b09041c0c20507003070340d082c2030700f800c0c04160a0144481504041c2c010b00d0855405045c0582040601808031300d06400881d00100001c0d00d864015080c0601880f540b82c0320702401203114101e4101d4202103655428580c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 59470021 1250 59468771 59468789
    0x1e0109140d11010c0c030303060815090a060b010207170708010b030607021902061c05060103050105060c0a0b0c07120504151704020d0c0504050117010f0b01080712020706050c0c0d02010c050301 85
    0x188802c8607071301c14501da411080c0d0100720424220703120308004009048601a9031200d1250380b04410032004404d00c150f05c00c10000d0000c0c00303c00c3c0540e0b22007014121202c03040341540316130000458a0480b8070208a80c80c00d06000070310350030b0b2900450500352112503818a010f0b40100c0148100c9a90110701540949801000f01d14a0743c1c00e88041201c502c40c148001c503050040d80c070080c0c040003a641141d0b00628003640c003440540d88036810446203104440c0310b904154004124040092014042e0945c014880003190381001e00a0711104980c0000300440d40004100280502910360b0700800d4012242080c500390b240f66801c46005042c811014201074480c3d020304142e4000c10a4042c220406020054001d02c01560350300080d958203407400070045555401c10700b220303565031b507a807060390300081050350b43d42d0f201c1c3c03169081618000c5212103030144050b002c225542c0030460030b00640e4091050310704082d960b000b0000b48a07050001c881442821039041c140128001940f003001e0342e0644403080c3e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 59471271 1250 59470021 59470043
    0x17180d05030a0f12021303030305062209030203090303070f120908072d080c0406090b091501140711090a0e1b040f060b030403090b0703021005060105091e0109140d 72
    0x10b0668030510141d802d0703480180000f468103215500086c0c24412284252418410760326103074200007a01c00e01d0466540d41c2c041c10200d1036161030030743c2c1103500a1806801a28946010100807034216400804151a20129a03500c0400c0101c403208030f90000c41c5514203142414240450152500c0703051140740903461f030146404401d0380ea8400d00303010b08044100a2041c0c0c559a59034203844000f405a0248240e1400e6000500c4051074054140301c440001c0064845a0720900c03501241c000c000d007003070304101c4407800780b1022182c40f00c01496a10f0003201c2d059024542d00742006041e030300050080e81c0e582d007025001c180082c40081c00403818002c2e255510f82c000806004540100b2408120f2400b02d41070440000320500d0085c010b50156019542d00d0040d961210b084e15503e220b034801c000c006034884010303245086070b55400f00350406014901107151a05a500250082c95029000c0c60180191510307021a0340c0c011048400920503880b441740640380250008511142c0400041c10000d014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 59472521 1250 59471271 59471297
    0x30a0e12030703030e1605030316050c06030a02030f060d050307060515062212020a0902070c050909060601170105030c0607060f05010e10050603010e0105010c05010917180d05030a 79
    0x502000e454186040c1107075224981802c1c000d001c3c1683c000005468021203507100b00194035846204261034014000f145011120301c15068000c000c880c058800340500c8001d040e0a80e251401103004207004e00e0096142d080c281030790900050b01800b440e100c1d000810501001910100c1a20b4406801c24000502c1313650b05440b0000c0b524502365519444500000c2c01681c08114030b60307011601c0174017104500202c0e2183d130020f003902e0341040e0195111154207010012600b0a030002e280c0548100c0b00301044075a0341000c120960300941d545921038110720100301d015688600c60802428002c440603209516003030100380c58019a9200c10b000e4035000450b1000c1c89007903080562961102c21042110350307503c1c101d068802200391580ca051081c1100000765615000003901d0580e101d041800c0070300d900e44001525034441c030034401c5a030b44d501c9240040104070707815007545842c01c13151800c65488100300341501e0341c003e60481d00303440352040040f0388020440010030f980c0640032a0800803680303008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 59473771 1250 59472521 59472529
    0x3080f0f0a051506030717090d0801290a0302031501080c0d020721030c12020c070603090609021305070e0315010603020a230703090e07080604180807080c07050a030302030a0e 77
    0x4143c0c44a90000c1002041c0541c1c6940205080300340883c8121640450b01c6851350740361921800d009000001c0c41c2900103001110403907100d0019550b004503103c400828800c1da180c1d8640080300004080391340030003007040008900c1c02400c0c024409280443c45403134022500e80090054030101d818a42e4040780000811600d015507020446500d02c0c114880e06603010010090100c100c0300703a0000314480c1215a0311001402901c5000683c00c0c0030348106c509014088005028103030301925406d40b941095005030701d401c94170341205000b00d80007203203602c1c1c011006460542940380c0c190213544100080e1849210340320f01036055600900e80540daaa0403414102c54401e0401503018201680c3d0003044c6003490680700a00d00300c0c1c80380e198070007515520301400341e40910071100310000c50155000600d8514080e84403001d800d4403420110058480394a4000c510b030805401200c2c001c000046032207050b0720800c03000004100854111290b01c1c210341d4001d4990141181c0c0d030703050015001c48030842d036507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 59475021 1250 59473771 59473801
    0x7140102010906020313050d210c09050916030c0905090103022106070903020f01030501051f0513080a0c08030a0203180f041a1002010c02070e090309150703080f0f0a05 74
    0x182000f0155220305218011000241000300d0459542c864030704929000c2d4040d030510607401c45460844410100e0340015600500554505e000030810300000c08111542d4002d20240100d038400c50340c0044066000d006000c40c8c010040240900c0040c400400803540d442c250b990650f40d041c1e07503400121243c100d55585400d2050700074103260088e0410032020030f502c0b0206408481c000c42e0084a234002a10054080340c0085c0201600b00e0381041c500054042c4000e43e00d40c0302c4074249041440c01c0d0402507164005040c03a0006903158000c80c080c20240080000f810000c1c042c03a401640c540f40d02d0443c00707982e900c1141e480300381285850412a1007030740e03080302159488402a009000803c60240c0c04855111003082c5075204001c01107141c1c41280c41485040c0301e04209800503c995424510412102b40d802081035040388401c20100c01c1a40b1804980e55500103903030f01c074988814071450040c4c44181c00506015480c06407404201828156154050b042003040600040c0b80d04c84044051100e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 59476271 1250 59475021 59475023
    0x403062705150f040c03030f170915011703220503030a0c06180203060606070c1d07020709050c031303020c090103080c0c04020304020d020910031e060c0305060102071401020109 78
    0x1004605410901202044186800c0070004509200340c2c0d8a8040d01525003003514041c1003005da680b01840003d010340c04003803150019041c950007114600c01c180c0000081161800301c69007103200121000c02c5100ea2550160210031851514403203000d1240303581e402110110a500301e282101c1d14002200082454080c0c140507050365942c0d1704010340603104a0785450f0440b007452814400d040500040e00f9030701c141d10f90080207804d190f1298010452103800c501030035a80c0e000e0541e0009175001d00030200f4483c3c500c0d03c5501d0103079844d0032003000c1d052410b6580520f000b1404c0404114803818504120ba900c03080e8181200007000b09401c0413131030569049240c5410040d064004401e0026280c094540016418111000010340c103060105901094074021341000000b03492200524100740c5007a03020f0400304190080350381d81d8950b403e2810080002158034209440c01900380700060182c01c0410181d0b040c02c0c4105c0c140000000d5490400b0300c074000101c5d031000c1c0a400c05a10239044017000d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 59477521 1250 59476271 59476331
    0x30f1103040602030301050a060f08010b0307030f0501080105041a070f08040312020d09060c020d020709020f09100c1a010510230414091005090a0209041404060902090906010b040306 80
    0x4030b0711010080e40d254000c0c0141403040529040002d480303441060045c05440c0f26503640100c40e40707003418000c4aa00050419011b02d52035006e055940038a0307101d160300038142180049a942031904014111072043e000c59408007603070404204441da0000700b90504803000385001d98041c2d45500b01103880069421030030314054000503030505043c6054000000650191504000c204078498003039943c4ca150a500c20b016030868030007001120240d6003e04600b1028108080c82c04008400044c005512001035901240c041c681200901140c030507800742e032144d222060004c0354100380014404001d560400010410060050244440c409404000c80701c20301d002d07180c9660700c946c3c42d0890b1201d0200d0030349c002c504590003e800000180c588200b1100040c0a0481c1a01e8007e4041c0c0a588404090360700603403104030322240745582849140c0305034041c83c1b00003402592441088800038014104180070380c44500144001c0358100c046404485e1700020000340c484a401107020900c04d132030181405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 59478771 1250 59477521 59477527
    0x20603130305070c121104021e0c0a051501060810030206070b0612060907050108153007170c1f0c17040e040309090203160305070210050c13090203060d030f1103 71
    0x110040102810030881e110b005510400b1201b40140070880c0560740040b114034601c0090803255582d4803004148035400301e02640c032200605c0d110b40d454001b44900601c4254001c00040004940c0604e00d00d820449481e543d40a040c610303000180309008641300500b4040e01e01000c2111680c50803440c10300010b20030103954240ca00508182c1e180d518600c1240c0c0410030450024445c012414800c29060314002c0405000d6982d4641040340d03041c110301c9843c4403500084550304c01c003008100c0c103002401d4207110440c040004002150170071040d842018020025140010840c200d91414040405582d103000d0007000050308001e0b28402e140490b0301c00342c0100040110301d0f44400c032601442107000346c481001d8256240003d00c1280300444480c07502e0201070701e43c000c0b55882500190740201c0a881150712481040300c42c1c400f220780c2601d0000a01d180021112003000709240b05030300401849104605624140003c2200c1540b6400700400b04414889200100350007a0341d0000c61280700c0c01100d403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 59480021 1250 59478771 59478779
    0xc03021603050901020f0a0c0b0a02030f040806060f04050912030903090d0605060102010c1404120309180b0f19090f02070b07030606020c0607051c0e030a030215010b0403020603130305070c 83
    0x2d02e41c40102d009005003d0304d100300070b0030500000c1200d486a4401c0030105494648405040702d0740202411108602041004150a04494010308094800200a03200c82e05095042106035100310300e01d14015824030040102440006c90710340c031004042a100756aa0740d40002603800c5108040456900023101c4c5030440c1070100951003148500001e0b0002c000220901905481c3c19005e0f00340b0307001d8141c00708005d0084981c1c3d400d05202d03043c400c0c109400f030103894008002c080c50cd00005000c4545c0d45a04042d071501d05200b084600c02020784a8140702000802c00c002d001d10680a904031040d2602040c40b06070003980c1c11110308540002c1e4040581c20041e40007030161101e44604030042c40ba40e503810001d403a010044030072641d88100140680121614044003002940b0300b107205001840320390801946051000b81c00c00c1c1d102e540a170000314516018401d4a80040c2c2003c562080709100070300043e02c0d01421250003191008900b030040c0118031b001c44007442080740082003a10900c00000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 59481271 1250 59480021 59480027
    0x5160308010905010902040b1602030c09090303071d01020d030207050c2d06040b031609030503041205060109020301031e0c0306060312030e0607200307020a06090509070201061401030c03021603 85
    0x1c0c1625107660b8140710690342c6a04400a9008038055900605402c004030fa0140f0052054045e07841d01c007078180c80325804001c1c001150800100c41d82074850700004108660160f20405c04801a107401502e102c00d42c82c0140000c1d42e40ea154030300078060580c009904000d1041c100b1440e10402c1e001012804440070395240c466000215a03a040121904046140032501d0300e04180c43c2926040d441e40f80c107607a580e10b00c01090202c0d83c00d041040c008a00c0c004030200d0300a000070b02c0a40b11400c4402d000d0406840d00394a0544140d01114040d441070006000284810454101070301c010318181c1200c0055081c9004503613010f034001440c2ca03103445000000c10440100810300385640d500d081001c0031843c0202a00d0302c01c11119000000c01d4540040355004910443e0b144040202c000c80e814884180d0104105078855008807000c00c00d80e11080100346082000607522210f50b10003030051034540f000f40c40c08440d645469905240e22416211850b80c0b2aa06443c03071807181007050041c980e0b80341006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 59482521 1250 59481271 59481287
    0xc02030910030c0e010c140a050303100e10120305040f060306090b010e0109051e130204050a050d0503030103060c0e031603020102011505033004030c0503070501080412080403051603 80
    0x80d901940c03000410240c418064030403030350700031800c4c0c54549108aa2800444210343c0700c071001c9a05010928159400810401501080e184510000c6589082806108203070741ca01e54044440104024200180508800c011204940071441c420b410300c50303d80b408ad522401580c20a0340548840000003400035810f400440c103c1304000703410405001040c0044070641f07100d99400d401700b811144200560300b4541024200381080030b5440d000d1700900320015a07124802a501084c250f00400c0038411403901169420050000311802e0071042407035510541c980c04144409060340d60707035044684005000748000400440014103655148002c80c2c0b82e4559440300303010507401503181c0782c0c0c13200841804c100407200b600d0004000f0021108072304042d21803420f0000c00c1e100707004606920712140407140000303031014520900f00c00c02c0240c00c5c8800d2520f85140e43d402241004840c605100c082216800183c288c1e40042c6000340c900e03581d03420256420710580011901d81c00c00451a0300905a0040710 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 59483771 1250 59482521 59482537
    0x1b0303040201030617031b070902160b010f15050306030a1502070c050f030a15060506040f0e0a09080a0f020a0803070201020a02010b030c03120d0f0f060611061b0a120c0203 76
    0x208008071354a4003901500c5910a1150740c105a00821202c1c016540d4000401e4500380280c04403400c039521440004141c1c0c0003115105407003003c0714402c0c4108024000c0e001e014003818030174100c0085c0761940c441c0c1d0b00a81c860409041c401e0000100b5129101403241106158000c00366902e40140d031400c00000754003001d801d4807000300201021402d4600710102180010009006001e1001c0388c1c1c8603010000b16114903110143e80d01c91001440c0c1e1a0040076000420454486800c414a0102c246003408030003009040900e140840450000d41c0300410f035180320b802840c1801016a440c2011f918008080c030000d040e24038048100711601d503054004140074503c82e4000d0140394107940616940b202041d409a0341a0000120030242c200c0c0301e0080c040d240805840403440c1c0c010704031341004030748681e250121034640310300b414002039800c045603001021400d40248540c2c41c010141c2410002d2255214181002c00284228204c3c410080c03008006103100c000c010160b84040d02950f07039442544 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 59485021 1250 59483771 59483777
    0xf070203060412030b0f010f0f020f06070c030f03060303090e0a0e0a081801110607050306240a0306051c0b0601020a02060c01090209090303010303080105010503040c0e04121b05030706020309031b0303040201 91
    0x11807440181003428005046d6501a10381d12111002204152407002c8800140c008500c1503c6041041d080100452400703501c458032184105035035401c0003015002c50039892000c2c1414580d042000990000929003154801c00401002da00d6401c410805043c082d1500e1225203d02c40384c043c1032000000040c80c1800d11407101c41500086440190780e00b181c0782c07482c0308a5170040d10008100c10b0045000319800720000b001444400b0407003d10411000100c40c0501e0889408201c108000b90103226143c05070104544220040c00842040f050200008400502041d100008200c1c164005c000c02c40080d80d0083c071680c0c8403101c1000b8a402024484000c2c2d20a0300b0440201d1481a0302004590581e40c1503174407010380f6801e101c010b6406030710281c000c8600030140000058140110501140664440c80c42035980e01c0013003400406440c0d88044401140c9080c2d200e01c0006180007046595841d07006002507240d60300c40d0102c5096000e00710b1501e21407041382910b900741c1c441c0403004602c40c5e4400d0b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 59486271 1250 59485021 59485031
    0xc08010f06050102030f031302060c0304090605040b0f1003060b1c05130b070309021314100503011a0420030405060403110303060a0b07020a1703070314031b0f07020306041203 77
    0xd509001560410b10805025070420805035400b201900000c640c030105492515038a04c030301d5030120b480e90340441680c19480c1c0000c60248505c81c101d00842000303103821641030203510402e00010708000840b02c25180b0481d030300d0f02602c1260380250046402844104411629282c001e41808451000102e19a0200d45001c000400700040100f0300d00410381c000421140d640e03200e0030103030001c0c0b002d01d4040e43e0059140040c0350806d4018002c903488404140320540141c00c041d645040075084a405c16440381e41045615203480c2d01f8008442040e07401160049003889d520500704100100e14800d0140e050800410001441000145c4600a510a0b50780c0440d060741e07506840d40f01d000588032683c0c0030000d4201007044032500380103801c000340010114004c513556840c412424108010b100300746070700302140750030174180c0050a2000f01030a0600721403652500c0180e000c800303030001c1105201000f000c60401e92500d910802c1d00e815550140880d00346040c1030510a454028429807100000c0c100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 59487521 1250 59486271 59486291
    0x232e05060406030809150d1d0d0c080f0904020705012a1701030206030a0e01090303200c06010603090302070312030b0a35010f14040201170f0112030c050102070c0801 73
    0x10710a10040f40c4c1c005410a080454040c100118650090300051800409200003070b01c2108070321400e4000320500c045d4400000c079401000341084074240d205800e200c181d10084011a946004450b03a05e11200d192a82e82c60178580060020f000da100060201d41c60045011480c0301c2100e0782d80459498045c41440794000000203da0181c0900d2070f1807028559031004100504219015640081d40088042680319904043e07900312511044241e001070340316200e0200740c51107040014800010303500c44a1501d120a031701a952084180300d41c0c420182d032401c4407400d05100b40b00180266500404068407000b220100401030440344681921561218100003400544100c80d18444062104c616001e54840b0401001a03480711200b8086552220220b21051490348502c0035041c041c40710399040c40c240380c0001030445500c40b07442e86041e081941400807000ca4a06910704440740b816901341c07501c01c10b16044503480040c0310000d15540c00030580d07104000c4140100c02c252a181e9000304445c80e19 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 59488771 1250 59487521 59487529
    0xf150b09130836011e0801030215120109060f05040b011704061b02100b0306040309031203020717070512030c0a0e04060510020607081003232e0506 65
    0x4161120348494500c4411000010807100240c80c908040d0f40d01418414002c0180fa07080e10900d05081807800c032031680410756981c0004100c124400c1c0c0c0d14034444803100a10001d001c0c0c0340c06000103880b48444030f0750090201840011030715480340300c00c44801d1a59660400c04040c1c90140034500404030082000729440c1014030429044250582d1202d551040b0340c05503140b250005070052b240640c640000d00501c003400c0600701340d00c2456600401050510360300da08101c414007990f0384d1003030f00441d0a001c0440c1e0710140c0c403426650480954040356420306020b4000f4481d041009100c1c019498078138040f5061000680807250188058035a0654540e040420a210480b201d80c5140010300c0800300b403c2c41004295003540b0302420003c1c403e03460b04002505a0031024102c0016400b03141000795281c1d20980c40d640010741c03100595007060455480b8542c0c083d46003040d982c00030005003a20900340040080010702072144001141c120b03415001c050000b12080301300d824050401001c1070307040c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 59490021 1250 59488771 59488789
    0x8120c010507210f0605060a0504090f060806010b0c0a060c0e0f0a03080d0c0e060301080604030908030a02060103080f1210090c02030c0a12111209040506010203070b0601030203090a0f150b 83
    0x540103005040000518414401400f00341c92a0084070313a02c080c01324003078030341400230600c4040e60b0725041d8a40f45810340c3d14080d0341246140e500524100a42044007040000b0090705584000c44130300d84aaa265800ca481c101c00020f01500c9182001e0401c1c0f18039170042c90b0360007058002c1e900b02c0000070309a02032004814041c40001c09403030f420040454000c5165008105000031841c00703820381003100c00081c0580e0001e0304058095045001403204040d009400c2400401d50070b4091401c000e440744c4040d485c0e50f81440701400080c1c0026403256800b071203104942550b940350103c581035040460725a64000c03c0c07800341c80c4240346004000c0a01a0002003076407620101c200003484080146e50300c510541048407400f10602c1040308114200920078480030b40c1e88901c40000fa6211843d07101004107440000e04420305541040102030081000381c185558420000e08015030741e5124001068644060340784090b15800401240104229201082c00d5a420310f80c0414041b010f015400c10503454 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 59491271 1250 59490021 59490047
    0x2030705070603110702090f15011d040b0a030219030308150d1403070503270a050f090402030c0301090807060609060608011203050d0504030f1e20010608120c010507 73
    0x2500c02902000294482d4000c408000b072130f0341c0f41d982890841c0e800704106500a03100b444c22031414400704681c90044013407040140b00c0c02d192400c039144242000601c3c01d01c0e41c0071401d0099480b620720311135684034401064000d40d4041c08114158600c4803140b2110502408201c2c00035a82101184030003100c8162910058002003400c44003c1d003a03074031072106074039040c01034085000902c00d00001c64000c0c0050841c0b07030b003450b00360740d0165076101c48442d0041e036156143c4d02c03407d5804030a1041d601c80915006c1001c1c0180e81d40900790326070340006480c04030407080013036056007000c480e002000a00c87c0900061440703030324103222054548040c60250f0310a030141200003002c000c0100300703421201c2c1c03a014540d8042e041252401e02c10200c203d059903070072501640414900c0a0b0940c2090f0300c40c4070140f041c4480b25440e0700f0000010781c000d0421520084800592031040c060510300300c802e60001008219070000ca6100d104040c0c3c0c03d81c41a0084011a483c075440c4c40300203038849000704000690a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 59492521 1250 59491271 59491273
    0x3010f050402070f080304050a050607030c1205060d05071d160e010503040c030b0709030218060f01050d02040b0a031409070302031e010b0918120f0405010509060d090803061002030705 81
    0x34101814040250000c0c2400c0d241a4485003242c07000c2805da0f8010b6000314042c6024002c40041410f1040c0b81c41070103400c10003014507001c0102071095010781035940043ca1901d0104203601d83c2c000168989840c00406440e5005000d000285c02940d03000d000c101d102410250700c0c0c15034030f071116841280700c081d10000100d1340304d0080740e034250f10030030055034001d1140f9240c0f92540d80301d48800040a20850340344000c11506141802580307021200d0b04000c135041d00c8000c1580c60510003256211201c0340c64181070050204901c0c507022900e405071000782c00c50426480d10f9400f0f15000502601200030622020021100403400650380403030980180d03078001d40104a1f0380550007401c1c8580c04010000c6040355656041c3d45090795603000e40c0c0d4002c000c085550117a4500c0240c1c41d50900141d0506295004010800c0c684e20032082000d0703404803042420400c0e1a8078031000458064454070040041d40b52034800d2a01c1041038560145010782001d032510080c04508510030303644ca00c04e003500940300b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 59493771 1250 59492521 59492549
    0xc0201060503031815030405010506040f0207020f15041802040501030e16060c0602070204090f030f02010e0c0d050304080703120f030c1e020f010c0314070912060507020703140303090c0103020301 86
    0x1050341c1c50f4070320300b4902d04050452030200000c21700b180c00e10340090b10700300d400ba511441031107418501801039405159400e201140380041d20760010300351460112489020720403034803001c0c4800780342d00305071001414403040c11807803030028080c520001e501900405005c2440d1010300c5030b92450004081d140840c0000c0801c010b141030200039689003c42003000c440350340d000c021000060300c0300e00515418520906000300340c0d9031103142c0502119900e5180300216031508000d1441e0500000e0680400070081e20329a070307410845d0800d2402d52207580c001248a2088150000c01c004a1981c4803005070300d2a600c002034120020300440565814806403000104026038230700d41614204509031012800b4011150054803e81c00c103801c3d04e0300620340c100800d42d941c2c492075003081000b00f00c5510450501e08180c0b034a0070b2109168404c013401070003615065903200090341c414001c0007540081e40d001364503090b01c8890700410681c0d0303500454200186010342c00c11380409501900035a816581005c010b000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 59495021 1250 59493771 59493787
    0x280e06031015060302071106040312140a0c020f030a0501050405060106020d0806010e01031509050705120115020303070818070b0307170403020714060706111e0304021818060f0702010c020106050303 87
    0x1019401074202518032007c030300c2464440e6915440200011031007203d100c200c88441c180090401c5c04c00d005040c0920108002151810707601c4505c049000d0350450315030f4009114000880d03d0440e400100901c150310300701c01e21044c4000000c5071812107031154201d840851240c0021a00c1d000151820360208980d00c000d0062503000340c102c41c981401034100304200036a200307114030a0b5642503651402107100015156450549040344034003400c440c44443c0440300c00560001d540c0d210003002d480820480c0707030114141003d050026188002043e00302c9060f41d1b111000e80c032082d802a82c5c14404200101001103c95510403c6280f0803901a00900701641c81d040c100e0958103c0e400180754001030400100d00090300324403d18280c00410007455890701c01c41c8440d0a281c1d03540110200c0000000d104200040c0d030390800b0300f01e0060f18009a11070940302c00c8100314a8a40c0c43d80c0300e080313901894040281080c1198011807040341c42e81d00038001003000c02010b9080340e10030300800c0d40541040140c2c1c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 59496271 1250 59495021 59495027
    0x80304210b190f11090a06050301030803010509040c15022a030a0303020a03020405191401020a080d0213050d030c02030d050a17060a0807060306090524280e0603101506 74
    0x15000502c98400701c2c01e1080058901c08450041c10520011040490510130904241081101419031030400e02e00d5541561601d4615000c14440e152140c802c1900242c10010581c80c44002400f41910b0070800142c206c501a4440715500700d110740b8402141074800c0d280001c0c2001d48045100034028007012030742520101c010b94004001c1c6002d0640812000401da124008403d076030760a4001c540344218104020000340d1240358100b10f04540c0100e04c80c40c0415801c4c021941441d80c03c01005035540d0800814038051401c5a000a40c01904543c0040905400040500c3c00e10320840c1503800045103418152224081c10702002c0000b094001e21068502d4000d405a80040c0020007519100f0b650341c04d2107141c00c03d0780e0013150010361500303c204136480c15801080e03041400c0d01d1821484010020013014606151043d41381301c0d005048030a940c2c1c060040300740e00903240d0b005084406645500080e0000002591454024070440e040e454401c046807084d14003c0c13100c2c458400c60640340c40b00807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 59497521 1250 59496271 59496301
    0x30804020d050106080f031c0c080c070201090302090112051c1b140303040c06030c090b0d050a0b09090a030e0306060d020d0302072c100602060a1107020604080304210b 74
    0xc0b0303415943c0f03c1d8041503840040158500d0507052200031079403096074191407828191400a11440c090900943d11341d91604040c02642c4200c0b070407a8242c49139002d00040320142299032000e5000010b45001040c5500d010040010450080b0304a070b4800d804202c101c030100707021650f0100003030034440d40ca10ba0b100300d11180b41c00f0381b4000c0d00074a55214900d4199801c590043d01c1c202d544040d60380e02005480c3d0107000328040f04c1d03818148030010618240a0320340c40d20030540c00d00402a40d42d0005101d89030f82e03611110f2024000b60440070746192641c400c0380d071110300c0001034021554504e8101d03614a0000b9825101d0300c0040c1003128070314940e40c24080062100175044056002d10000400e01c0c80c81c1d4031b040201045401000c4040170200000410380d9500900b6000340f0004045040c041d240d000254580c108500440000c4e000040e020046000d01800b10700a500001c002000501410000003400550f115000341800d51003000b88494030410402c00010000100c140000d003d0351401401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 59498771 1250 59497521 59497523
    0xc021c02031f09050f010b06070201030203250f0201111806030603190b0103030e0108061e030703080d0b01090506041d0a0e06040308010e101d060a080d08041707030804020d 76
    0x32034049480316611050380000c21900540483c0e6901003031410300904001c42d2000140400c0200700b1032070000003040180c401c0c10000383c1450b8001010508181c5085081e01380c0392040181c140c1d80a8500900400d5002c0c8280503c0040d070a1210840e00b8280c0c00041301c81e25815412000008181d00e030900c8443c0d007000742400e80c1030007840d40401c0500056004075150031b110700d0007001550704620b030250859009042840c104500082046452b464140c0603030384078a0b107001c03580b07451110f100019207885581d41004126000c08140218007408a0b00700036800e0b070092300c1e085041a12a010310003140143c0c403804000c50f030100340b1058030200644200b504584101000305900480044151501c45d041c2d508500003458400100144140310365501d802000c0c54001000907490803404422003205146800500c4600501181040e51421030a40c01003c0230b00544410650490020304183c108850070303181a00068282c0144030703c034004a4803541d6140d203951035581c0b40d54007400160198604 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 59500021 1250 59498771 59498773
    0x2040c050702031b0406080102091c0804030b1e0a09050a02010c060b061201090c08130b07022107031106101a120403020f010c050f071b03080318011401030302070605030408040b0d020301080d0c021c0203 89
    0xc003b2001c590f5000c00380f440f448a1144103405118035003200c510440d8014204c12401d407400d051100022400304241c000d468091030440d410924030f050000042070f00c0047c3d168010300c001503100d404103c102086040300d4007003400b0003409800e0b41040d5005201141d41c91540d05c112040e01c00062152181d040d002005881111940c2030200400303890034250700c21844140c0e10100d040c4c0101a07102038042031590780c403805801d40e8142008c58182c02505405a812034140600786121085400e00650b500d5554100011140b81030505000c2d4450f06048080109035003481c01d0141c1c05401481190820350b46641c102d480c0000d41d4a400c0c10100d00c0c2d0725030b000e1504480c0303c000040b400c0c800283d4003940c21240c01c0c64020f4002010203003155400310030b0400c8803e200c80100f01185c2c010600a04403a2242845a500d54580c50404003c2c0b095810007060801c0118032144014241d5000c3d44c180c5510030100ea44140442c642501d80181024000307500440e1032100b4075032400c5600c5171501481c4090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 59501271 1250 59500021 59500027
    0x41106040902040e0a0b06041206091b050306070e1f030b0a03050309010e09010509010311061303060b13020c070603110d020c0c0109120f02040c050702031b0406080102091c08 77
    0x24850390095002031101900407405000b44c090310b000640c0c00c40f104400c200184580000400d4450250b40304034040325440007920400d002e459041441c4481d400381d02c100e2442c81031a0818140c00c014000c850192040750700089106003ea22550841e020040c070302c010001d0744021510584500030361140030140c450242e0340300f6860381c0c02c0401c040c6120300091754950b00c64100041100c18001a030700d05c04c0c3c00400040245848091140c0e055a810424030101d0400f1740e07000c6009481010082038a68003a684000700b4400164040480c0200803106c0c00c0390300030111501400e81c011403e64608a07007103081c003004210301941c0070200d8024100c1d882428040001d04400403a040f00d10313900b059420500c10185190780c13080b210009014401d00300d1406068648480c0b20710401d9001c004d0140c0d5440f0140a1524054810788070f0459008044a0301881d80c0c00c8500c41801009400501417400c081c40800d903032006000f5542448009800188560340034201104c01120446041d2120780b010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 59502521 1250 59501271 59501303
    0x3011404050709330c0f1101020111030f0118020708090405150409050708010b01030608071a0d09060902100503160e0a0911040303020f0706050708090301060e15090a05040803010e04 80
    0x75203070103030107040c00d15109581c1c0050010303132452001000c9420810810100c110b10002098044040281d94224204040171980301d00140e0041c440103800501c0003201100304158003010741c1600b81a10b46c4024500d250208504510082e40180c44008040001c1800b0720074031410f0603404168080c8842c2040c205005502c000304044500f00001615282c129450900c0341900900903070401c00d400b8601001304e140b811414a44a6000d405250501055031458201c0d102070a810b0360380c01d15039244108840b1400e4608180100200304c7c00300e02402c0400070f401d04c401d003e1015a8802c2040840b540c0b00c05014580482d281502402e072250300405480002c210105248900040d44120003002903a850850601038030b8502860440802540141002c0c0490340c1e20174207581c10994003100180c1c8414000b40060301421440e0005558014100c007000701070302807010020040700050b9071446c029214905001c05441d411100a07084090800042262034988000e207035200e8002c0c88013010340001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 59503771 1250 59502521 59502539
    0x609061a0111060f240a230a0f1203020a06090506061c080901121b120f02030108030a0f0207080a120924110a0812041703011404050709 60
    0x148022410252844500501036560840348608191804000074100382c504119280c6448800600d81100d02100301035040c910107480c42c140000060041400d40815180c0760030818041d01004201d44900c40180f1902181c00c040025000b511607440410745841e0401140c4095201030020850842c8140e01469012440c503105440c9117603c12405003c0904003032080001c241161460010134500254000c40095055070480d00c40c445d0a082c91a0400003d010410080403504171070283d08468000c0e51090652250304212240300c280300410a000b1840b00c6401207010900500007030b640208480c50303040340502c12200d5916071610460700d409807203035a1981000e150003411a0a020000e64640703480745c00c0780aa038058490320394a140c100344c0d90210400d01c01c0711100e00905003d00751103100807503001403186100550300800319590307030900268090040d80e0b0841d0709607094688079001b0344101000d202100e0486101c080e120311741101c107400b000010300d400381000c0b060110403500005c060320 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 59505021 1250 59503771 59503781
    0xa09031115030a06032a1412010c02010f05010902090a030807020a0510030501150804050c0f13180501060602062a1b0102070201030605030d0f03051008030c0f0c030102040b030a0504060906 83
    0x808808500e091544c607014005121040301204070020003c400600080c3c1e68a0310002c450365008941004600c280101b418a0000c005008265080000360180b04bc4c054100030941380494800f002540c0e80e41c81840102d024182c00e2540c000740000040001c180001d000e4480c40e80024101148603694200144418007442c0311540843e4850004100c40141100010100103850500c50943d03e403070b9580c25250b44854401c648206000b0300081559150194041d41c0c02100c644c04101c90740701080014802070008408550310360804c040400d038181301040705401002c40000300ea14400b0b5007816481c0024507803101004090301445448818001c00c01c0001c580e00815000507034494442c0001000d9445940060f40a5406140300c0d0003580d900c5035112810004134500040c0940b0348024004c3d0014080d40b08a038244408110f8180307882c4045441500c281c42903003161405194181810300380c1c052440b841020800a00003d00c0c64191608016031240c4244400250302151340e0301d840480e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 59506271 1250 59505021 59505031
    0x1090312171b1c0e0a1407050607020607060e0c03010606031d030c07050d03050909010308040501030506090103020603070f02160e01060810060c0201050c031303030509040e0a050c24031603110a0903111503 90
    0x64800c41240a40000900a6402610b019601145002c202fa00031030568842c0350401040c0541c0c40352a80707800391040c4090054a17100900a1110f40d039608802409401c48500380c2002001a11080c02200e000108a45901481c0c001520865140204012016002c001e040e03050100030400921380d5514000d25034080c40c82005100d071100c0c00e0100050468900411040c000d881080c010300140c0d54220541c1d602201030720700b01103d4003204008a08200a0baa40b5030101030744cc041c0810212001c0202505884543e59251110b9403038400030000d01155208803000f00c2d1040d0020409540b06500501e51550040c007101c1c0b070032170a00c0700e511000b0740b907502c150005007010a502065103400e0203041d41e000c0c0b400c00100f20704003e42d01d50307984584a00d18518420300d05691803080c81b00380800540c0007007403e0107019440b032403c2400d190306000403014010010f4030300b43c01c1d17151441440e030540e07000180c280c0d16040c10a003540e49407400410020f006940c400000c4a040902c0000c0000a611030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 59507521 1250 59506271 59506283
    0x302070e0106020a0f0809040e03040f090c09030c1a073207060207090504051c050d060e0c0304021e03030d06030203280602030601090312171b1c0e0a 66
    0x103103041449030030410180c01035411034101005490104000b43c20700c500550704100e0705540e0343d441400040052900c100c0d0740105000202d000174003001100010b004403a401d4009102400001c0d2040b2044200c41c00b000740840c0c1403980901a0700c0d400003400c240700e11a90b00c4249045000d460307804503812031207050b8149500d808070390001d07454402043d904402c07410000f030122a09100c000394032560503014681c0010b42d901b0011b42413000400c480c18000102011a10788200f4110000b4801e500103601300d04040c0c206a00058051030360054588200c4505441c0750540c1c44542c20890076040d8901001481d030501501a600340c1c1e010b20040010b500c400b0400078803640340d84103260804556034044111214640c80344000290f8a0b282c072030a495005500603525512302005031071950707868201408a540f00c0401b02c0d600383d080f0042504100244800040581e00e0340e85090f40c0000c000540010640280641540124044100061440100d00205448100021f51032401c600500d0560706 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 59508771 1250 59507521 59507533
    0x2706070b0a050402030c0105040605180301060f0602030403030908060408030403050313060608160905070206070f11100605040509010506150a112b03050903040b03060103090209010b1b0604021311070606030302 92
    0x4611781013092505003502030030460300b010b26289002c2d00314003d035030b144403106400c80c104000b01d40e0294003a40240110070031144140e9190030300256680c1150000f100030a070600e001040505001038100d203e603605c01d1456282d651203560803070f941d40000d001100c440e1003051a00c4c0000b04035001d42005810a00f000700300610302011095940d0340310740d20405d10540b500090090456001c51416070000717031810035900e8110041412618010380c0380704400240070b4408200c88072840c0c3c0d04200b0484000312018003440e111110540c0c221001500e44607841404602d56965501c1320743c0c003414000c212818108041d981140059080240c01d070210107195600c460704040d8442c00701d0b0900040d51451408102c503180c50115281d586c41940200310516402000040090b8460f40000c104180e0141c41d0704120b594452021100742c1000c201204070b0701c0408500d42c1c500e1000544184a66002002800358800c8100d070b19005148130545482114420001c0303d01040d001e02808008503ca54000c2071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 59510021 1250 59508771 59508773
    0x61902100c0c0203060c0f0705030a090303140901020a11030c060304050105070810150309060f020711012601051003020f0c0303040506130305180112060b030910022706070b0a0504 79
    0xc00c40d0301481c40c5909200b01c2500420150f20b0001d0782a61140c18228903542e62400c0c107003a900f580c00b0710710300205244000200100d015030f00c50a018102c80c4a0f85541e02913054400c3c5103102da0140c40071031401079021218030804100345042c8044d082401405070b90610720130101183c5942c2c4110382c151100c1c1c1d10362042c495020750102d20305034010561a8440d00142c24004018507001271000781c94105529081090180180c40d44a800b08409500c002c5540380098503140014407628058107002c20141c500c00c1c00707110300743e100e203d048480c04500300e1156030810003045022030000410108265090100b500c1021300500189100c03001d0034020345d21b078949840d242c0c1c60001e0091450b000e100e0050b0114000942100c1601c58020300c0c40f14030340f222170131030740100c8104402c00204c007602070400b41d001480404440086020744001c8042e0340b80713001c07a03401190980c4201020100c0301440914a096003044814600380700541c000c0070343e8684902619004c44040c000d6445c400072581e15410300c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 59511271 1250 59510021 59510053
    0x206011a0304080a0809150403080f0c0c19050a06090c09110f031602010908030106050a0e030606010203090904030201112107030b03190206040e01030507050a3002061902 75
    0xc04100036160152942c605503668080d180078000d065030501c0400030118540b500b0034071103079030f00402d04101c0d01d96a00e42428000e0501034191482d98a0078107100200e80045583d8044410300e091000041c551a01460074034100345441500a5405000304200c000c00a010b41c003480000600600026031203a09210f0040221424007514071080402001201e02e03600341c1100b42ca0f489158003000780344006132040c2c140e01500c01e42000510f1400d0010010030120380010192461900c1540c44050b411002c0702803507074540040c0d65080c0035a0060100d0145807608440c120340c0b0522030320005c04c42d0b01e003e03442004103400001e05610941e00030515101c80c49101d1041c81d5100e00035103010300c903492a080100351075003440e0030501072000f03042e042e090540d15520200c90042c919070440060075a500c0c04c2030313511000a40145071103980c00d100e000444000e0540030307802c0c0d6000c94081044a0101c1c130600300069541d080c00702c0c0c000f041441080084282400b41c0c602030038042e00038001d6211540359213 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 59512521 1250 59511271 59511299
    0x70210060501080103060e01021204030f0207060207030506061002030c01050a0c080601030b01080612070518040b01171c030e01020a0206061903081b0c130b01090501030204061b020a1203020601 85
    0x216400600d0030508000c0c036a0f0201c0e6050440e90000800a140446403510602a228814402c41c0700030700e80c2c080c030007019840282581020340039030907962105c3d103514049032a405244000307440c0d43d0004000c03402c2c500e01004a603200391a640101c03450b02e41601b12480c01d465007200d00b040c41a5441000103104c3e1303000803035164088424070b810024010b0050010b440d100002d1300e401d000e0501c50418400810041000a001d040024001d08041e4140e000101c03100004980465030740e4000c074000079200c41d01c3c10b54800c03484680300141c4040c0810445400050401e030440c0303401c0545070a03218241101c203100510107102590f014089074036000e0107000c00754400c0000c41c01504a40002000072544290035102100100c030740c503c4096458403175071403a1102d4024046e6002d5800d4281d00d01c0b401c105c4e0b01c002662182038842c08502680e940040d0224010741c070500020940b0200c2201c86440110311101348580700410700741c01651150803070300d01c003071016004502580c410300040c4450380c003408038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 59513771 1250 59512521 59512543
    0x804030507060e03030d0b030705030a0b090705090903070f060b0604091b1b02130209040e10060b091e0d0501060f0501030b0303070c06050f0412200d0b18160902030702 74
    0x20140704840441c022030745e41d11850120501269882c1d0f11506503940500091004102c014112040c501040c00c0a03160700c0001d848005a91098400014003402e10741d80d05403141030410007460404001d6182c4850102681034125240380d07440010440c41d0380c52001a00241c1590340d07000035164101000c1c2c0104e0b001010024050041601c4907030300303c3e1071880210002c0790307043d45e10752449040012110040d00a401c687e41d8443e0401e0503030004448000ba6a861090a802c000c0c0419176407103200707000621812880503040101303103501000c00940c0c07002030002080094014140d185481c1c0b03501e42143c1c255000019082074000c0c04000c150381c94015801d410a08801640c5804001c0c1e035801d12071400ca21449091140125031907240c94003602c1900c0050090aa03030801101d480d02c0c140e0364000600d242009440c501035071030a010b0801c541c0742d55a5a5100010700341d44c0c5c60340c603205e010546002c02c003084103229213540344901c0d08c00c607504a0018108007a015840342080c1070b01074202010000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 59515021 1250 59513771 59513777
    0x3030f050703110d110c07080a0302070e0402060301050d050f010903090501092408100308070f02040c08090a030e04150f1505180d21120b0301090b0402061312080403050706 76
    0x3c5072a45071060001103c072032070204000010301c1040b0440441507406040b010b120707540600b00002031007140115000c0c155910a6095a000e15220b2150700c03260b0344280c4001e50054800c1c801405a03050641800070a41d0080c000c45203c2c28984507450700b540c1e1000e004500141c00100100315558000d000840030b0002026181143c42681e14412000e01074288000108540310b0049402e800304e1101c80c401640e0043c441c00c1e0741e00341c0f0307040110420000807002c9000b103103030000300c3c1c46103803291081c54010700d08040034101150042d10119165240385144c0d541c0b080d50344000490b000d54007003800380182403803003030005401d00d0403000b9103030304085805060a2200c204680812010350238506208030104a5014070412414106440a5124100313502c4810a0901042038880d404c40003209628a07a00c00a000d0f409692050500381c80b48208020245114180810018604003004e0802218003190002d01603030380d060348141d000070503041a40d90300d01c0084c050050181c02e100800c054603a5003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 59516271 1250 59515021 59515031
    0x30102070515040f02090109050103120504140409080f12010e06040b0a0303030c120606080609090c0d02010503060409020a030f1527020a1502033403081b040303030f050703 76
    0xa161039440310350b08042004204107607400035041244040081d01c1072034016106840075038550720701c0801004280030a8031070039400c40d0100050381c414030841d41035803401151034000c18507007800e02000d00b41c1080e0450b1844170070702840301815803c0380501484c0400e850302c0d402c1d80d40f40c036903030048100e0081c25281c09281060032041258940c0b9503040101e0703505140004000301400000c43e0790001c0e02640440140c10401e000890550010b19640240c0007144c0c58105078441045117030741ca0250310b0100f604207141c1c100c000d001d903002d840030f180d015034041c00210300490301c0d078006180c0c802c642d0011507038101c3c1400240240700a0000800c1110310158080000280c00000c039542c80c442c28182500c10609a8240821505e41c4000c40300185001e4114009000d41d180300070b520f85d00880018050a2048034881d407070001000e488403045030902c3c500c410b01eaa6162401c5505c013000a1416031039040c549070030080314456500901c0210300a03075000a1200100081409076500030b030060003010700f02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 59517521 1250 59516271 59516273
    0xe15010302060703090e0c0a0f11072303030412120e0604090f0e010524030102040b04060806032b0305060306100b0a021e07050315070906030908070503070c05040b03010207 76
    0x104006040d290101c440b5502d5902c54034003200d100d00c082e00489404031500c02444076055402d405000c1110160319100300e0035000035012244088840d00f1101680d010382010032a088039a41d00c44103090407100854682c03622200031a1640d4001e40c840b100100000250030181b054460041d210a801071511006030503194000490500560080e40e860507903038201c9103246d0aa41e07100e8101c00c00808000d0200380780c8032002e05003c80e15000700119034486101e0480c1d8a18042c8202d40c1a1102000a20301b400d007001c0341220450300080c015078161148500310030f0442114401d03001c15000e0314040303502c02c103c2c9000042c20342d100940428001d90180d410700079180f44400d0b00400750350741500402c4d00c507510810100d00c2c1100f007075001002c1001c10903880040f5040802c0754010b542e419070840d28643c0041150703031506402110a0300001c0e070309202c1170107064425001000404e005190040c00c0600645405003164000c0c46c0403100440c100400300b000f420280603884140c40704500840c145081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 59518771 1250 59517521 59517553
    0x30c03140f0304030c1503061d0604060503010c0203030a0c090509040b01061d01080601030c050f0412050105181c031112070e030102040f06030f0f0203070c030306050306040206070f030e03030a120e 87
    0x1d0b4040d1710540d8406d00e525085052003940304000800480616008003681c0c0501202203a1041d995603000d603050a0010400c2e04050240380100c0c001c0360f000310700d15a12042c140004100154030b24040042e403000c00510b0340e80f03000c8000c0c0114050140401594500600688104500c1000f00f11308000304007003050300da03002203c0c158028828200450302d24640c14046850b8420744125040f07043c000311300441c0c1c2c029030050001c0d00d03030302c80c130020030a5460f00300b0f01c05d01e8025800011b40c0c2540c000b5420358a01e004c840c45502c404403503400c0c0480c1b03051402d003c051858000000e500d900b070342d9100030001240e0348444580f0520000740d000310320341400c2256a0108540a000e035000b81900c035a4111045181a031159402e41c1d083c06c3c0840d1a03003014030b00101784900000d42600000d06140010445140205483c0d011765070081c036003450040b182e03031840b10401c0626404d405020417800340307442d6a1010320051409004c20390343c20b20700490140c200360071264190a40600c0764414120394007006a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 59520021 1250 59518771 59518793
    0x50601060845100209041103270a0524070801030512070812090a14070605040510030e0109050c030f010501080703021203041e0302100e0312030709030c03140f030403 73
    0x1105214901c0007140a8116007002e109604038031052103020100302c14a0100d40c06042d9058003110140b000002c062200182401f040d1040b4603008500c0d0f505040140c0c240c49038030300d9200303002c0a46840062544543d800c01d010042640050030600c5054044510550191644245641000442941152545035507840101136900700043e0000d50801031140c0482500c5202d41444800c04143c0780100629889444200044903000070f11001c40e0403800d00403c0340c00076941d950380d03001d0038285070204001038081e0016501e4145552102c07002c241400130301641940724010030080070064004030506280c03005032036103444581d14100041c814030744081980d01c2200c0c1c04030780e40c040c1c1000c4410050300307610881d032001501019454110001b094510744078030071640202d0b0701e0184205191425124954207081841c3d25820208420451209c0000071b1038100c0000d2406000c415140d644802c031a8801d81c00070342d80c1d1019600301425403503007004000d402600060255040a00d03640c7c1c1c03031440758 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 59521271 1250 59520021 59520091
    0x6080606130e0709180f0c09030809061602030109050705010809030a0918021209010902010912030f03050a29030d0309030c0f060f0207032601060e0906030a02030a0506010608 77
    0x80b03010007060460340325094140141c00248044511404c1c0b101000008240c1003100c501082e0410070b070403030000d01a6005800f100d821268881c03400c1c2403501000004d0f40441c418950b802c0340d03d202743c40075031400d00c5120551440340005000e00c50a04c0d0014120010040038501640d208014038150a640004440212440034065164541c504660721010740603104503408041d5910040001c4004150000210207000f070301d641100f182c44003002c0c40c01c2c9104260103004985446030a0071810b03ca0fa0045600902c0b4181c00030382980340c0d840b5800b0f2801540b656610140c42224284280d18040c050442e800406090411011030a541e0103441c04164113006032588942e00b0801050000c0c640000301e00b00880c00b0115603e020515001e0003444400d104014103c89082070311030402c0a0b142c41c50705807400c51316448a800c0070b001c00c011071000000c01694150180780c900d0170050300d00304022845a0711441c080e01c42513040002c001c1842c540188240221044000300d020194600c203110440c1c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 59522521 1250 59521271 59521289
    0x4090b03010b09040c06140a05030c0d06030605010b0714030903060112140a080c010c0215190605030a030507050d020606010f030c170f150a081b0a18060608060613 72
    0x5020400240105140703142150008005001c01081100d0a07410005650142d11000f91091800c030404040b030086400780000b1607400c01c0400c103c0d41c01c6c02c000c0d15001c4c16652008c5810380d1256141015503000f0b90040a030303400089410401c00034460303004481d031b580c0b2000a504148134440080d540d101c06120300c40000843c00e40074014000d188185110000300701c000ca51503411980b62107203c03075000b940d00b9802c5501e007004100b0018404106040342c14104044d00e281c0362a094502814200d4246401c03051640c0c400d8002401d0f00c040c0f2a00c0c0e21a8000d84409850b40c805044c080e003031840f04904e402c215040001080456a04265020034000042c9000580509460300036201001d040d0040c4d420682d0b66020040d0040f01c0145092251a0b244001c6400040b40400d002101103107008030341c1d450300702000a0724030602c030f45c64841c024a0700801c2541500d0f0b40e294907030581541242d41140303060702c0d06001c0c0304241d0070510f120b40040c41600c0c41458481ca00e0a11810400540070768a0a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 59523771 1250 59522521 59522531
    0xc050108061302040806040b1e070f030204090e0c0301060806041a100806131b12080c03040e0403020109060c17040605060112021201080d020604030f08070207120501020c070e0105060409 82
    0x190b9100c4160700300030201c107280110354443d201e0702c00c2944c0701c0c022a8120340640b49071000070500e413030f040c00203150f241541003081038540b10104259103010100111034109a1f0031f03c400101c940d45030007000c0441c01000301900c490141c6006040c01d40326150171101490344000d0600000603455041d6519123150010b002025840d0900381000c502c03250391140e01c083c0310746e400348507203001c07a41c103c03a0703540b40308044100103801006490f6a4406040c490400b290503045041d1000c1001000103040301701d10201982e20f040d407038507200c0c00503e0041d102a40140c2d907070755810301048510701c14001301d1555400e007102240f16003901012b518030000e000610090f1070311301250042e40a00c41284410400c020159280d65001e284c0d980b6030402480743d58803e01c14110050400c41c00070039a42d0241d9010f070380300780301e891004030181d03000c0304013074884003c5100309940082d503112204072105201d0b11031800940e6078006651a1490b01c40e0035008407140c1061140108025030300d6408a504840011202041c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 59525021 1250 59523771 59523781
    0x8030403260f0d050f090f072102030f1608070e0402011b0803070c17040b03240d0606030302060a0e0304060c0203011e05040b010602161a0c1204050312070c050108 72
    0x1660740500c0b520941203150100c0e1400e0140040d8112610072a41420114032950714410090380d0b44203401040300b51038101010a2000724001580d0040318401c5a44480d101d1200e94046490b090305203162071070b1500510700318094490b88103034041c0107040c0c03200201541401c00309403000c00e0700c01030303c024113001300c4090b400004018010600203090b0000c02c3c881c0c0f203140c5084040c00a16102900f01c0300d0b681c0d06201042e40890030000e0f202900c1c1c405103c5030865a840c00a0060039080551804c41d078150745100d004075645919503040100d214043c00b2030b1080c994540a841c0c400c005c0c0c41551080d08220090460540010546007101e01d039181426100203140046801040003050381d05900050600621390701100e6000580070340d07c0b8500d0a07100c1c1c0c2c4d0b01c6204030307251090005c1e40301e010280c170070080000044580000502c18605402181b810701e0780b400071881d0419000c00441e82e500013140400c654a0b00b44414040d16881c85081031412003d1382d6100d4000c0c40c1800f405040c42180320200f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 59526271 1250 59525021 59525093
    0xa05060306150102100c0e03010c0302030408030402041e0f0b01080106020c01080705180402030114100203040e040b061f02010c110309060d1109060705030c07050d02030c040507180e0f0108030403 86
    0x6034108176640d10030041414003550045c2051403002c2068000e60820403003202c00c0d4070920840340300c0d58000d03203180c2c199103603a13080101611241c551240c132520148445c01c0f02005500c68990080016000000c0c00006200050309040c0142c0c07081042d50010082c0c41c403a640c001401560068540c90b01130360743d03a002030400c036002d851102d0301d907000342c0301000100c0d008841154801e882d450884189541e141d010800300da80e4443c60003114105801c0c41e000c01c0c0043c0e15110542d0301700f40c005000410980f5014880d1807120540c080020044c2c0d114100e01d07030100d0b0000c0b020b0422442030005140f0340032044010800c98400c0038607120350240c1d10041d40c8a00c0c0c3d00982507400302100102400c6c2d9409190074450303900c1e0800380100e55140200c8a00044c14902090b00070502540034001c0c0024014000070032004140c014a00018454501d0385000720343c0c006c1c00d4803030140c5064030810010703007000c204804546034160003c4069a00420091010400c00c2000e03801c0740750070070529440344400180e41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 59527521 1250 59526271 59526283
    0x807031401180b06040f03050304030501050117070b0d02120a05060901080607050909060d141f02031005101205101406070b061c020901090c0f0207050114091c0501090203060a05060306150102 84
    0x12000c1406c030440c04403c00401100805c11680907400034089a620303941c1c5c00d03480d407900c001c00328aa07a0041c80100200079039040546844490b146006081030b81e9038a0100388944212403005010303540e0020010107241c0304400707030b000d03118807401018107140c8401701414070b20440481521503138858001409a0395020300304104958459460b5148400f2454641d41c2d80c0d03043d10996021128080500150910602c00e6a00c40c10303808125404040c582400d0020029200c0804c02c00c121008401d28981000b500501c1d0117001daa2099660040c60700340154101034098940c50f1040c0e601b04145004624200c04064102100702c8045602d8040b41031a526403685054000303401c0907540e0b0001407c070040d07030320181c1078000300d459194980f00300301c0081303841da10203004403404100803224030a01c003820400900300c586405007211035001e0044002002402062404650580d1684460340450409002c0300c2d8101000b04c0301406181852800039446c1c0000401c5d524030783d2141d80c1000c3c0160320030420 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 59528771 1250 59527521 59527529
    0x308180a0f0308090112090309090207140d05041502030f0304060b060c0a030905040c080402100807030e0a050102041a030f070516020907030c080c0c060f060f09070807031401180b0604 81
    0x96150a80d42c0c03032400303032a541c00c0b90840ca400b1030300e110740c000140c0040b4040c076810780364560b4035020341d1401c00300384500070b4020000584100240b40da60412049007008041542c1650391101a103941c81d00d200404c1200d03030b414007074003150030500c0070441881c030340c00907250030940c40400030488142c0c010100d14103004000c115401c07441050b035200c05040c0c101e8030107801d480059400b80012103010380103a90f05101520000d4014607078814010031144502245500244070f49004110040d210840a140041c0c109042d500d41e5030000301004210940c45802c64111584d0079620304500c0c00c0d0303005a010190090000060000c0001c440c030341d120704020360800c034903401081c01c0110309042d44010024840e42000d4404170703104101187d03048440405850b103c2c540b2100510869440e11180d45501501030201a005540030f030314841199a60203550b8414842c1e680ca1011520304400c00030191000c4c19200d18805200000503c00354642d507000100140e9140e401182d45421100030580c184602d601c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 59530021 1250 59528771 59528789
    0x303010b0a0c08180a050d02030a0f02190303110601090b101803060519060905151e06040e15010c1104020703090803040f030203100b100c050a050102030c0d150308180a 74
    0x4d40b404140356820600194904151440f035249034032601408210341500358040d500d54420607910000406074400d019010344007506030790031603000200c101510585074008401060100c20025040c0008000035401840b2030740703090010900d00c0740441c1c1440181e0071010100041d000140d01c0d110f4805030804c009503484a402c000514204501d86280504070300420861428808001041d840a0040c240100b42075107049011403429005c101140d50b41c800800d811002c03001080329585e444d040a403004003c450380f0409946080808150b06004035a078550510603507921500220f4900710480c20b801030151001039a82c0d04609042d1415012a07101c84914480004c0108103d058080800d0840e4400c0e021a03001d1030380312072003105841440010982141a0b40700c045107035881058004106400f55040d90740c81c04103a00c4490990740215610721b600034002680c240104040d129981105d146440080350703c500b566600b2195215202d00d004028114592a040300e40c2c0d04082c0304001d214110b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 59531271 1250 59530021 59530027
    0x705010e070311040b010309020a23030307050a020909030307080109020306030a0c06090812030103020904060b0d0f03030504020f0102060f07210513110a03030212030c16150507050c0303010b0a0c08 87
    0x3140c0f000c2024811640079000f1400d00600c3c20a650081c01840704855005225100e00d90804403c00c900106001000041e003580c6081100c0c2c1e82c800380f0040c5201c60151000d004111218018000400c5010742040e080e13610030000c001a86030310080d07041c156000e410000da604d44501001030314003090014050070103e07a4071000208075400600c4201100c40c00001c3d02c1805426401458050000344006500409500d00041c005400b95110f0b03010303214010420102c0003101d8507482d141c44140d0f40100c0201c2e650b0010701042d4038100e0590180403000340b0003001a49012040c042c400507000c0c1c4104144131408010504015110400301c2540ba90410204840d2030b101d42c510302d040419083c01c4d04c104500c07280380000742c01d00c803024000f9a034068004100f048860404005640e01c010200b0711217590500c48035a003540e4016140041d07902440d00c030920789642c1c81d802411558003414200174400c04020145544da804130a490441c0d03181c249072904d819a9080607110b10454002c0100141800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 59532377 1106 59531271 59531273
    0x23010516051207050c041b120b120d020304140105040602030a140f0f09040506061306080a11040816050411030f04050a0c142b03050705010e0703 64
    0x2442103404a508806480b07600d908a150100e46030341002c0380101c0c1d039141500038581e94900d441100043c10204203006450f04400015002c80592130340c10000266440c0790590f0b100c55241010f41d203e194401100944903803080c0240014040a85440ba07034951048050350280c880540045d4503080301180c0581c0d500410503d1031103280d00c02c1204038044101171010304540103045e802d07541c5400041007040b064071070003800b05000c4d16003807100e03490400200040c0341c210782e410f040509084d200d10140c0c8014058040d01c0c980f21000020f400a9001300000d044c0ea503c1941e4561080542c1d101c0d02040181e410040c1440404841800400da2000c0e4985099401c42d00c5002118811000c41d43c3d4071881c1101a07000780242841ca41541071581403000011480c00540c90b50708684009400090300040c080003000740c1040380105200040240c258082c0c10308a9540007100c05075562 = true := by decide +kernel

theorem cover : BRFrame.Cov 59352521 59532377 := by
  have h0 := BRFrame.cov_init 59352521
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59352521 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 59352521 ≤ n) (h2 : n < 59532377) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
