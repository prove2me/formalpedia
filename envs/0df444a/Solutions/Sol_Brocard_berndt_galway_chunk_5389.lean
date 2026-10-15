-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5389
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:26.575692+00:00
-- url     : https://prove2.me/submissions/e6ec87fd-0d58-461c-8c02-07ed65df9645

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 969064748 ≤ n < 969244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 969065998 1250 969064748 969064781
    0x30706091a04051b06091e03070b03060f10030207020a080d020d030e1c020a1e110d05150601120501080a0212030a050a0c06022a0c0a030302031228 65
    0x30301d40c8681001c04402c690081240e084641d101303991844000c000c1e240410003900d86030800b100100414200c10801c24952215038690640222070302c0c013004100054003864003054250b00782280130402600c4a912120300c81e00b025a00a50007030300c0f82c1c1c140d4001c10f40091203007030020f40d10000c458850103000203c0005001e0783c000703c115076000c1d0040c0700346869020010884196114054002c00d010a00284110700403c9031030004078651400081400d041e04500203444e481d94a4406e00481000c3c0c1144d0083c00c0d0405d080010030701c042400c040310032800c0412213060390741000482c0c0c50f00107a040701303041601d4840046a8403000080c0c21091501c02d030f1384000b0303498100c040380340c0c0c85c060440c407100015810040f4009807440381146425843c82020058108180400c4200301d8a200101c031004180c00c420390104402001c002c0c680007040151840c0ca140342c20342e14020b440e44604810007d403002c404000c603450401d0b500c0001d02d18011070003004004a4001038038005040040f00449520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 969067248 1250 969065998 969066023
    0x80a0209062d0c07090b0a08030a030608010b18060d020f060d0e0c0a15050d0f06060804020a060f12020f0702040908030f06030105010518040c050a1d09070b220803070609 75
    0x89102040f80c080010b00d00003060410328004030391028103134020300142c000100580005610408102602180140d92030102c4c2890804152500f1100380002d0380d132064201031a000000b020205185410000580340c894006449001191030441d200c1900c6800c19400a10b01605003e1030340680a00b807403070780644004c030a00c3c0701001032300c4e0054002ca81d014162031760440c0c9070720701407402880e613401e0006011a01007001a180804c0720740303a0b807000d00030821007801c1000b1441c121344900c025020600f420001c0c6a2041c50041806818020404c8000d0b4005a45200c2011150580d60040d034014814013420324140f51800b031982080c2d5400b50780c00000004a0024a41801840c4c140ca0000d010001068180c0c0d000e554050405001640c240100b100c02048580310410040090300326032100c020082500d0b000401a210b0003004001d4030b4000c3d0006205180c80f42e0704950561180000c800c0b0f200892961000b4041c11a038020320300c9200002d4140300300072075074011103019402500300e031081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 969068498 1250 969067248 969067327
    0x302010314010b0910030e1c0807140405060f070506010f0303090806010605120a0f09031806090b0f0c0718060e0105030d020a03030218030a0f1101140a080a020906 72
    0x4075000e028820001d2014080421103091902200d00c4000c1c480c9008194480f80e81081400d1502d000c0c0c50120f1480740e4844c00440310b4004100c1600000c43d450305914400c568950700455000e24040c040c42280c0003e11103200d805100d080d902103d81007400d640455075100381c130f03241c04141407100314007107030224070001001140410641e04a4100d911040d192000407414001c113928001c1c020524160391b420042680300e0b10707210b1108034601c04d4039403001c2aa506480c104014409074012002c100c0540c1d000d0143d8a501d409640150007504640343c0c40e44640b0f43d0701030600b09581c00c400941040d5608400c0500503681140d41100d2403030146030600c0c0d0f01c0c7c009040d1039020481411f000350707100e00521000030348079900030276003410070118888200351468002400e2010a14082da95641c04101030002e02400244002400ac0242810807894100b8a9042c5e81030268040765000e21a503000011548503054041345c00ca000000c041030350b0303129030380d00a1004105c140c0348042281c02140b0311110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 969069748 1250 969068498 969068531
    0x6010807020312360703020127051201090b0a05150414060d05160305060a05010e071704031e031b18030b0a020405060304030519020312071b050d050403020103 70
    0x6183c000307040410215969100036603d00c00300c00304020b18402100c020500003c40554089600302c103160090f040540c030b580001030081c3c00060a0204815480001c0c1d801c10344c1c4d0350703030078401c540080e18401c0750010f41e09201da00400c228603010305074500e16001c0201c8001150b211910a443d04040b40080c074103072409000842c0d840810540318288a0300102d111442c0c8201c0d00914544150f00701c800c1200e010441c01c038200314580c81100e4680c006424061700880074040c1c036014082403c20280701b850411802000c0040d1042c1032901fa80c0c028000c01c05152289850ba20500311805819040c0391640174010000d00e034561800b00740580d02a08040400d120b50307031800c0e1030010407500c070f4029410350f2102c00d02b2410207000340900d150308100010f01c0c1d45030200503501c980d000ea00c54075107440003000560300ca90302580040045420401c260040d50002c2400590460042d03e0a0381c6020b0100c1d8410403c5000c2500181c0036224800850000039071100013481524400e0740e0602203100780004806 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 969070998 1250 969069748 969069757
    0x10314101a040509100c050a09210b0702010f05010605030105040507210f0207050106140312161101020c0d060204080c0306040c09020c19121e08011712040905060108070203 76
    0x1c88508000300000740e450181c00c40d07904000300109480803000261002c8048030b800500642c081240400c48148084d08030802c2402480310f03100f950070248502c0080c102000c1ca009005003480508800b2130380d5503100758840c0400c1100c1e070300e003001556143c00740640550000d1041902c034070704040c001100345200e07183c0c81403288100f1500042000c000340100b0003411480300b0289180750300744486e102181d024040c0500a00b14004c0564010340d40344c062500300300c0e403820341c00341540042005030280803180050203050303500803844205254003500100d0401d0700442043d940b10f601e001c0c0c24010700c40e641d4024400c445005086a814403110300038180c85000480e009440b034010310b0802c0000030321300e030018410714a400090300d251284410403400e849030080010b80d001c038860610320b511507401458038441000c071a4480b0500c410700b202c0c002d0151005000b0401c1c40ca40407800c0c0100803000304030072403000100007149070300d56440c0e203240350090030700b01e03610341c005208000070682d0b1a0001c030881c2c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 969072248 1250 969070998 969071021
    0xf030a02090609070c0b0c042105061f0308071104060812040b0f0f0a050c0c0901030f262110080a061116050109030f0e06041205011401031410 63
    0x201410ba40380c00c10480d030a80000c08200902c0405201040010040c1c6c00c8507118001084140d510b0354100030001202d5a01c003000102c08102160080000c80e03c0040c45943c0051460a2909402d200070318440383c1070308942c8014070300b080204903c4108002030b0602c004a20303043c1c0341000042c0e903c49290b542c42000041000050b00c0420040c003828030180000c1084040074042c007890510415006103041d07200d0303088a00041c00203d002e0101a40a002191a0010484640d5250350668a41c41200744016400402102044500081c007002c000940f5003541c95451035151a4100c20051014100103c108504061844400214801c0b40c820901d015280814002d040a51b0345540b00f600034034007282d840c3d84c0040c040c00744030320340300300e1015444010748924004079940141e8a8094000c02c114803a01041c400c1c9220840c42503120342c800c1d20119400e406a0045200543c00c1c0306006120050640710090728540000c800d04c03014040340d1901c0c030302000c1110003c030f141e0300c0407904588008010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 969073498 1250 969072248 969072259
    0x1140414040207020414040c08060108010614010f1e051b0a0b0426030705040311010e060901052d1c0504080a0c1e060b0a0f030b0f07200304050f030a02 67
    0xd05106003816800b419a55101410024040210b801112610320007113404482c42411410180300d00f0310700340f003000d0051008400900402e03080c000d03070b0644c00c666020345034104103240d012924800d21a00e00c1040100f00c1b0610103854091011005025a103d840d418986d00103821441c0040300e00051111302e4141c0104440181e034540755a6000d240c081103000c5100d290034400081c8102800000960284040f51a41d41e0f55520358645602e5415954840c00c0c140962143d1a041c90386405080b01e060080920b00070790340d26041030310b4402c4162080e0320034002d103507002c1007143c1200007e0010028200d02002040100d12111a00c505136101110001e1a80c60702b4003202001c1401521607188451098094000644500e075100d10740444406081d9042922940700c80650f0504c0076021021b00080f03030102541c60f003951207000a248000d451100f14400c040c1c001220b9501c184c440507801901049a00a20441403c40303581c0e035085802110302c83c00380200580c0044c0380000d0740024543d4040c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 969074748 1250 969073498 969073529
    0xf070b030906040f0203030f16030f110726011506170106090e0c0c1009021906090b220305060103110901030f03110c04060905190e0304230a1202011404 67
    0x36244d581014070300c400c80e01880140700480192005101030a8859a05440541c034040365040041c402d1100b0031305038040c4551484802c10171140070030408151803204210030404101101074400d4040383c80c580413020751a0040d140300c400d65005070a0304840042e500d29848001b840d8114110010070f04c2240041032296404101c1d4942d007608259200312280703907032170810703401440c45800c1c4119075040c00301c0c88c2e1f602e008031021440d020f0f8440e901c0c44c031805070480302d06040c504007074501c2199002c0c0c48079002d0080b86440d104488400d2911380c69409600300d0729816600d00d0450f5843c0d000b80002c0300c02c000002a1100c0380d00300000c89604883d0014411681030b400d50318280c806861400032400301b40110001d00055813114021030700140407205000030549002e507410403422504180180e422802c00c5109403440d607002040c0c500340c91480c85655112440204408991403402d0a5141c01560380d07140050360b1002c1d4140e000742b11b4003e032540042c100000d203820300340c0c1c880c40c06902503500c021003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 969075998 1250 969074748 969074753
    0x9120609060f052701020a0e060c01091719020307021516022d03010509070618051504060206070e010801060c03030204030b18100e06040311100c020f070b03090604 72
    0x10008503215004000004400e04036200710740907110100c80d0000320380420004405086406080d80300007140b000001c505000003150010700c030709684c285051240ca0040f540b100031040a601080c500c580c000d88000c140c191000901c81e051708003909103c01e101151101c25481d43c00841155002580145844040c0300c200030f08103030940003e290202d00b045620b07510001a1210640c040d044007002800c0800d41e403c1c0220700c11441490010039000381d0500c01480b825030300024060050b2082070a000c003000c01c000c4410f94041c005e582c06194020800a454030104000400610a0321440e82c01ea40040d91200e0080c0c4513400e103068620300085040d80100300b91031107004c20446451182c170b400340ca00b0340c1e240c41d005280703d001e40f0109400c0c144150070141c0c0c00000c114002803d80300d04400d215520b400c4283e00d4603500000c00c090284031000c00a08144002071154070254a83c440042002d51b4071004001e40d03503103040d0400d40c06441039042c041684402001070328400c3d03201c5030040c5100e07941d55 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 969077248 1250 969075998 969076001
    0x3050c09070f0509060c030c01050712151202060c100c0305070906020a03121d0109080927010302040b0f03010207060b210c10090e090c04060f08030909310210091206 73
    0x1086c414042d00042c06114142402805118014585a582d100204010341192001c84605510b64403c8440b0044200300c0b2206080030480720940483e001511403844d04581d81c2440444850f003c030407403401a542d1506034041d40660f01a016076540c1403a44c40d21290300f0390765101c10304000303000704084480c40803e083c2c45400c03614202451038039401010015424503400d43e0a00d0b2400c40300f031840818041050309184203840083c42e1045030030750f00401304500035010500103010290141d038031594411150b46840c1c0b0640b00105006d4005c65407618907080100003445a4034034584560248021490740c80704402c00b1100c08100700c0c000d803200c0c521900c04c101d200d5010351100c070140038901c1000142004112102d134800c4c28a00040c00300940300c4410801140c069420285000081c0f0205010864000007621400c610a5800082e02c2e11408862449000054400386d1a4071041001d072101d411180d81d403500d100d02c29a1141d22514200800340c544060600801d403101e5495101400460000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 969078498 1250 969077248 969077257
    0x2060c03030c27220b0303072001030c090303030908120a150603023103020405010e070908070f050d060f0c02030a110303061503191404051501230a08030403050c09070f050906 77
    0x3030090004140485e4001329003150003c0344180d131450401c590100c8002c0b0090304010b00404246020000005170410250036100d1901010b0200b507510900700d000c002c007545c100e85500c0d0301080803031500c2c07801c8801007024004c03051400c03401d0049034000152140c064000c0d1003a0340032040034001c0c0403010303802900d6400101602c14078586e80ca0100000540c0301c9104041c06131501c2d4010354090300e420381c00501541e41c0f591000750940d02404c0d0401104200c6065401a03980440c0d038103507804264200340014004201030850503500d407229940d00550000300421510f12182c0303660030a8044503018a49901040b03580302d810141d074040226440204000440d0301005141c406156950705140080440e021484100801d1a240c820300003030000411250100340307882c50303009000d9030510b81c166120a0060615a214880190400e000c0d90f40300e44114000d00108070440f0348481e0b0345c0c100780e41d9404003800c10303038003d01b5102d01052029118501445910007030713031a5589080f100f001440f800380e10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 969079748 1250 969078498 969078559
    0x120603111e04020711031605031b1f0201050604140f06101205131122050621010b01030b12070b070f051504051c0206011202060c03030c27 61
    0x40ca0150301c420742d80e8900c003030880180140000e240c1250000e06061504800924006042c000e440d01004503581c00620b0600c40e6802a842303071550a090700100301554a4110240c036504030071149800c03030381e07415807040e03100b00800c17501440301c0c03410304681c00452201591051100d942c0c0800055190904900b40c21801c20986840c00d01181c2c00e02c890400c48400780d60312920030070300301110402c1c48001d4010b000026800c0315080038445174502c19803200b280d000e10306d1000a40b280300203142ea50b60500a0a001905948d18440c14050245840e008240f40c1d520b0501080c41c2c955039401ca828000d8007040c15001c148002c0c03813000d0601c41c51344656045070340200c40800c1982c0740b10000800900c803580303181c000000c41690311b082a1405508100240741c800702800c4074441c00707038802580000c489044400544500301b4405c01c50000c580c5612910422002d80e202c000309010110342207a0040c4460703100a500002908803a0848201342c040c2070381000d6000d924441d03102d01d4502001d0401d5001c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 969080998 1250 969079748 969079789
    0x81003150c050906040e0106020601061b1b17030903060703060e13061508010b011101020a0e01050f0c0313290d0221010b0d1404050a03120b1306050112060311 70
    0x4240f000030304150300a4115a5210128100402c00d40e60100f1040e070140c807a81c2400714a03000c0c200c000c2400c000d00c550020380241c0b0761980d0020200d040c801c80c90058a00100a12210680c4198130707581c0e030f80320401043c004d1049800040506109105040644404a001030030548810b000078010441440003940c109945040c502c0d0a800340e090a040144032880001c11207981e088005488040442d0710040d459004006103564280c1c8502c14a0b44003600f428010303101c49038445480114016035204070403031711001442800c14036403940328108640b00034100315039142d500a00d04000c0c413003070140e107000800140410085801c03943c02516054203681000d00c2c030001e0020505910045c01c0c4d002052803040055015821011405404168526188081d003d81010361740c051342c4000f10540030302000400060034031030780516007103403440a030002d0074164101543c50600c40101814494540440c074421040b54034045a4040c040860360000b60344518a014407080c0a00380c04204e845284c1e82 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 969082248 1250 969080998 969081007
    0x420030a0c090b040e1011070212010e0709021201140301020c060406061409040f0219090c091518031101051611040501120b161707080403081003150c05 67
    0x15202044103001032400740a06030740c01403802d140602141c820b90070481c01a0b04121111081c07800009800740ea2625403440040c20741500d1424040c030340102a0001c0d44a00104403048103113805411450009034030305c0503161030a689001b007204031f22681021440214030703a4010808124540090307510407201034000b42c5014201a10141402401c540031154651744c0d040c180000d2000c0e040d111120601a5181210381c1000d841e040039040300c108000384036409610420700c14450905940004210f000c800744100b548190300a01240000c0c090429905600c08e03d6450747c0780b05004000e540412850741903581400c0d500c60210300320300c40b254a41800000c0110071200c5007945054204940540c0400152030b014170200000e071081a4031031900c0e502614296170109030008500354100b41040412a0709103900d10040d03d08030042d0194007200750640c002c00c0b55031504869481d104030305c85d40e55810640c3c0c80d03e51a07c0c0f035008602024000340070380d2036039102c040302c960700c10010400c4505285040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 969083498 1250 969082248 969082313
    0x40b100e01080c0d090311120a020a110a08031902060c0325052101080c03031e0d060308030f1f0602030a05031012260406120b01030b130e1b0904 64
    0x145c03100804110000345034240750750001002407011000010368450014546403d05800035030f030b14800280035110071071003d501038a581c0d41806210003440401d06903500c0b80d503075081641d010044a104d040c05030003880300054041c0c1501c1c048a12420141030781f4120051403003041105142200c00d40d100b44042004031803801013400d06941d000301180a40c10402d581408031840c203060004016034048e0b4014015640004001e0011910340d030b40d40c100b83c40c0c407003a140c284130020b841c031648050481e0380c00000b8802e001b0000410180315082e81405224284114540045100e00038031031840160801e210741c06559102e07000840d044a40d900c070580c2c05507150300700c00c0480003080c1011038040a04181c05080704400c0b00910303041c80c500000c0380d41040e00d0720740d0180c105000030844503003099861500643c268029444444800800340c54045810941d04201000740309110450002d486038011840000035502c070078284c2640082c2c285822900c42d55151000f501c0c01c203110f06103551030603581410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 969084748 1250 969083498 969083501
    0x170103060f091e1401050106081b092706030604150e03040812030402010225051513141e100807090e0a140708040f140c0607050c040b100e01080c0d 65
    0x1e400d0402440c0c0345940d125440d21a40790741421130308843c0380e41046e004210003038020001a074048520b4080c1b540500382b0400b007420031312800c203140e03030f0216006002103100e150520200d14417410700a011410750300c4540815540326400c0310300400b1940045c14882c64002c2c1e50b0000d4424040c59401c80c0d0405803a500c05500b400100410318100d040088104001e40da410000304980824540b0300380040042a10081140081c2d4068280120041301640d261800620125994841c180d00c4008402303031609181030340015418078461042c0301c80b0340c07040c0c1078065003c03168032820b00040000c600c101c401942a11003190042201003403240c070160000b51407072030380c0e00b07248130300740300e04000a40681da500108025080035101008210802c3d0402c00014000d16104007483c0c0c00c03030b8040c030130508039140b507602e800c00d4441c903680c0040b80400e800c01040f10000d103a5240860485007841031b03042c00e506020744400604000d400003030840c124401154000c00f000f5030094075840801d0f1411092600300340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 969085998 1250 969084748 969084773
    0x70311041814060d11101116030303062309040204060b03090102120a060b1b03090a1d13020603011401120504120305060105090d080c1c0903030f170103060f09 70
    0x1d003620348400c420560b00c2c402601a03507106074100c0e0040c0d402402da031122a85d8280c00c0020501801c81c0402c400d5000b40502640ca01e5040030b0000c45c2c04280e48168039060180407440200c011a00b003000105851824495103003100745102c070b422005402d50000c0158600014100f41e8000c0c0e0b44030008204080083c0003503200f40380603400507070394000311042120710305002010190064907001c0148030860180c01116003600b072080000a01c1d904034840d280c00d51203030030071a40d405520f030f10000401c4183c1301460700e8404d98800540503107584040148003158038010000703611030010001402001d003000c0d01c007910032006141228036104681d0000d030450340152800d44061070700d4115442615454054940d00080a103012401c8c00c5001011902a84500344010485070011458850007181000794180b5091180c4601d0342c65420074001030300d0b101e181e01050b4001000b03140403210007405104070b03152004455468000581c03a54071000014440014141c0e003054440340980c1c007083d0b2400000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 969087248 1250 969085998 969086039
    0x10061d0a0812031e0609010603020903010e01050106020f070e01050913030c080a0c05010507140d0b04090b040b040c08070b0d180c0824041e0c091514120607031104 72
    0x2a83c9013000c0e040310803648541c820240d0a01130b40c0c0200065921a03004003411120305040168490a1082c0001d02414082801414543c83c0800010345d1541c00640c035020359001c041640c5c200c41c0c0711040c8160280d030074040c041e000710000001c1503140d20416071081c07849010303240200c98036000340d81d200d078140d1114102600003040f40c8500343c1803010038414150844850f0601c21000a15012000c3c1c1c00e0045884501300d031a980c81c0b101c0400d45a98118902203a440058220a0701c0c045c035120440203026175043d075140606c01d001288025000602070300740c0c1c07500c170481401c161440200e200540340e821030035444641010440c170006242c092025000d045840003500103484100100a400d1151880300381000300380109200100d00c01e81c050741c202082580c071110803507444d820420000c0c0043d902c40341d0340303c4c6000c2a03080c1003000740c401da9003550034821484141384090403c0100360302102c12002e0403904400d010443c00d43c044d42c0709512900c002c000190800f9901c8810304c50340304185485 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 969088498 1250 969087248 969087283
    0x50d0203010e01031101020a0f020139030e09041a250c0203061006080c03040c051206091507020615040b04110408010c030e1b031203160810061d0a08 66
    0x60017041107290652407010000e20080840b00b1154986c500c0c90f4030003110107410301014403502c0310a0301c1c01421b15101e03246c0140704a41c103203e00318810325401041080a400080e03900380e041d961403400910f55802203412003944401000705102c60040240c000e00080100340040d0300403501d403403c039417502680114541f10080b41500600505041c840000d0000080c10f000c050240007250700203204036000083c07100000e486c0d035030320306e40400d4004c15600080d502c031080e07444000c02030b500054180d11640d124015146010003120002311015021358440016030040b2001400b00c0040c2c4160708101d003002007000c121641072030013260481305034005030071140310009018448038809000e580e82c070724000e1404220100f0b002c0000398403440510000544090700c031018220f565000c000d2680c81d445a0103010f0f40d02c0c203094050002d10443c1482ca48041007101c00011041000382c1044000c03210239460f80703640700f8014210360000a000c0b03184a540b1400d00040400d06140420403010b0030211600c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 969089748 1250 969088498 969088501
    0x1c0915050702060c0d0906020d021216020a020f0904030c1b0303031a060910020a021309030f080601092d090e07080c0105041404090b100618030507120201050d0203010e 74
    0x958205481005250009550144040c84844125a003c5840c1c02004e180001042c1d8554540b1501034410100045049400030521480312860409224000c1c400c3c444c159541ca1083e003000e0741c580e001e461010303602031059401c900845c1010031955904c24440d00d00b141d02e0030407545d034982d940f45c50741c8002070308400c0c1c20005000b05038042c8a24000013481e0038401d04e452000c3d100091791803040d0403101e4050321120805121641c0200500c11101d035004180681151b80c0b034042c04014a82e200d030542c000389a10000c416103078003844d403190086906940b000b500c5400e00024096485400419150041c08810701072950010307003034514041e02d232607100850a41c1507608400e14020b81c540221085800a8417000940d0383c202d4101d0701111a601d0300c01c540001e8400c006001040ca03007101405c8c411000c0200120030000c60703c5807013589e00310f03103130030a101c03034045940280000740c0d010041c2503034400e4105104061102c1c400005041c030502d059847c12000465910507a00f0030385c08501400003050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 969090998 1250 969089748 969089783
    0x9120f0f16050303030402010f200c090c1c050606160809010f26130f03030b13060e0415021306090317071a1506040303020705040b15030c1c09 63
    0x100c004248040e65803040007850500c80001e03260b00c0003034002810701101c149440c0c80343d030041c1d4640f0105000714801d03420590800c2130b40c1d525100c6141c05a07106601c8071000802c3c4410500c16a5070030385000218080000d80060098001c04015040c603508c8041806070207080d5072040c0398407620510405100d5282d0b031416002504010410396400180304445c2d024403100c200d5440a00400400b00d5545d8102d074495142c1c940854010f03d502501c1648500084414103030950400d0710911820303102c0314502940d9041e0751007200c00130b00442e14034401e0036001c41c003ca5020300e4102c54900d4810320051408480042c08281202140c1c020310204010302401c00c1400749501d0300420407019035940c249040207a42c0c88130040612285d109a9124083c03010921060301800c046404001c040c122998450b16814069521078003031041c03901c1039003083c4444103d070410281c880c09a8528208490561301e802601849603000568504924112484c802880b22071a020f80f2030281d0244482540807000791 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 969092248 1250 969090998 969091003
    0x60b070c050306101208180a09090309050906010f05071a1305010e0d1733030705040207121d0a0e0f1303080c0c031c0e070f180209120f0f 61
    0x10040d41c105116044104421017081c5140b02c41035501c8942d203039580382c0c80b0305040b040d008000c05098000481c02e0001c90780000303030750244140c0d500030b48030a6400c1d543c500c100a01e02104443e114001044c0c001007441c8540504c02402c01d00b403181107514000702180c0061002d11004075060080154602a030390305202c001c0c40340c00c1220b1002006006000e00085028100c2e07d5072200582d040ea025400041a0b070000b1803441ca18000ca002581d00003441e07a49201d060400403660f0184a40a500b100080302c0c41e013403007100d41070ba522a14403041801d85000540c0c5092184681946004140c2c6044007070b03a40d0b0121040242c008054011400e04000032116940300008126160301c2c0685882440460780010345580d1002c01558000d94501007101c03180e045016011180c440e40310102402003006940350054982c4540300b00845070401e0303903040010344400742031080d44a590507009490080079000c1d00149641c0c48041c1080c1c811003404400945040840081c820303040d0800f02000080300800d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 969093498 1250 969092248 969092251
    0x20120120a17040f0c090504211b0b100f050310020a0c05070801050a060905061e03240708060117010e0a090f030903170a082d430c0303060b070c050306 67
    0x642e070070000391074650345140604841c0460040300c41d40070035038149e555115140e0045902e4143c41d0074450700b5110b140c4440c0001003620750800c0440300a6010904400044d0702c80200ca030020014220445409881c1009503c04003004c010850f1640b109808641701300300790f200410f1180c00001d820324100e9503e40c21503426401c50005181414148440d41c1d80e4100010094070403800c480c43d0601171880081e03c2c205801c40c1410084801101d40344400e046040382c0c0d44a00c500c0d840e400b00c65910314004440e43c941400002410801c0d00c0300622508c20381c9440c40358000c03000100001e10a046848008020020301021000908161414030420900588240300d40700b40c440500d080c4924402c0c06800520700a10f44070511000c0c401c1804c0e2a10740c40c85050f0001e001004800311410041240c0d000d221200c0700b00840d206030404818004c01143e04c5240d540000721180c10800203504c00100c5002c4400801501050380b5102c020410102c1a00200103281c8103091407070402e03140ca4241802e1440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 969094748 1250 969093498 969093509
    0x501090f06230613060b0f031605070f110301061a030f07110307060b0a0314010b0f040606020c0405040206040302061c050f16081306020a11010b090c092701030f020120120a17040f0c 80
    0xd0054070005110180d070149207503409507379411340c00c1507600460300618113036120070040c604003141c0684070301e0500c0040d4000ca009120009640d0b4404000f1307102040303907600403a541e0f4400c0203a8004a480e59100c011040c0300101381c17100c016982d0729914071030b0703090910080f20360f5564043c11402c0d24000d0100903c18006582c24801a403a0400c042d44451980000e540142d40710ba0000d411581c842003241c02070741d8002c2980f41c46401c40e480446481e8020800b9091251514002c2100c1d1109411018401c60b0a510980166105100220303080c909c082c0400161069125940c0f000944900203070035400c0046c3da0301d4500000075402c00b030a648a03a0240d41c003d43c2e40b042401449403003007003100e01503502568010b24001d0f00400c0300c1110422110842006242c010001c42040340c1c52122104041c001d03604c000b00641c1507007030408101c007000003800041e4800b04035a2100103d000103480d03140703807504201d281c203a82807803103240707802c4101c404071002040c1c01c3c440020005003039103040203442d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 969095998 1250 969094748 969094757
    0x2407150606030c02120f0d0f06120b0a111801023a050c1b010c0c1401030b031507031113030c0608010b0c060a02160501090f06230613060b0f0316 64
    0x45500e03031700130018419154004074052000409100c0440c85c1d40100003107140f1420f082000669804460100000c10602152a0072041e03002c1031101595000d5102c44c1040300c0c1c81c262a01d104a061221580c220946142c10350003602c3d1000346070503460ac41014a8201c0650000d400b240d02c1c0800c0350401210303d075030024040180701c0340494404c0020050784210045013910b01c030141c1000141c80c4079504e01030040954000d60302c04540f82080c018044d10700d072001e0724144168001141050f4603000142080e91010070f0788000100194403e400c00c0c09001800840146808507a5045181c80541d0741c00984039100800020049a41c3c0201d8150040040d83c10090030f2000b160030080d22a48040e02d40c2005503004100043c2c001d04940c40003217440d42c4000200480d40c024607000c3c4a84c60010810350b4200e00d4580141c8460782428591400040102e03001413541c0c0d55441008034100c4101310980b202550303603c0200701184607000078a520750804036200c5d180d18056a084103265000703c851710400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 969097248 1250 969095998 969096013
    0x90801091104050408070f0809010e0418060f0e0307080403150b0d24051906050103050702100e01090624050307030b040f110613061404052407150606030c02 69
    0x1420101c000c490800d044402184a40ba41d041c40103980c01024000f40c400c0c04100341d01020480001b0050080b00001e0b02c8154004e40b03034004001c11110b107d0003180e2a606400b0f41743d80080c1e00c550207846030346100c4400252104508a07100c0c80e5030080907044640c2900050184203002d00310520550969082d0400d0040c5040c14022a2640b42a048000d0100d100302505d0103100407108204005425003c07801c00803450b142071040c401010301610308002c5031504502040b10b512a0248038402c201c50740040414020700061318004060700004d8072419540c8110304000504240a4442508134a101010354405154000c40305180280e1180b8860f5000c5002040040d07200003950b0350054000c65820600300d62400c20b1101030061101295015000013003140c001c130300c2d050100c8169201d96448006580e6050443d060368072840c000d080d4851203481c0401c400c0032502e22880894030190740c05509004003a1f68124040107407040510b030042d204d88040c800c0a0b03162092000007040c0d4401050003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 969098498 1250 969097248 969097253
    0x19051e03090603040602210f0604060e0c09010c050d0e0109090c080406021c0504031101150b031602070b1c0e01020313080d0e190501050c07031e200d09080109 70
    0x60740320301c40649004401c04000542403008030fa050300d8144141500341f0458004034240e07100e03001d070120f42c51001d050402001c62000d003880d01c03441040d5609404d0701c2072691108410b80500750010701134141008265a01c8800141090000c140c07a01c5c0940c44400d20610100005449401540c1025104074078041070a039005601150035600250840f400503a01d100040001150902c22001010081e0400c4288010154800050803881d10158001c00104a64020300e4110f99081e04c135400704201d040c00032400c0c0c0d0400e10580d00d0003001d980100d07844140d40341100c0045800082d000c2294280e51211981031503241c3c00303505203030305401c2e008500e940360503801c9050000044c040a095900007007241d20072484250b01641d440565a021106041d04e520444400103c03902004c40300340d400c0c003011801904210054414042e810b0b182d80c02c100070705041c0f110580d1001e6103100c00b00042e1442009a221703942100140210740301010300340080c44100c0103040c1040c9a8040c0d1240e81c034103a080c501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 969099748 1250 969098498 969098503
    0x10c140a1407080906160611090f060d091a010816030210030b190308030a060e01050d141207080915090d060f110a02060f100b250519051e 61
    0x7001c6400031101c0c2c2c6851042c109540c650040c40401c54003e04002000714a2004803511070031050f12440c000d02ca0048100020102d501545511b1900b010600689540501d49030000c0c2482c1510b800300000c1340381e200e403030b06600c1c49041c0c140041c4413034003900140079840060104054074540382e807403105050324660101d070244520300740e0740040590b620000c0416540300c6404041e0043e5003980c0b81845034403400c0540d1a60700940c3c1241c0503900d05a40010010310380c1241d58103d9200508075840c01c00ca83c0c03900b480d01e480d007050000207802030401c1000040340d002c025000e66409104404d0301d5a410000780030002e0407000413240c4048041c0721008441d0341d8010780d031102d00c0d40444040341b6800042c201c80c02170851010404040440410004c1c1034940c0081c481d48604112000c64072035465040740140111058041c10290340c904104041d0241d5022085203403c2050049020310b50b01c594942600342212490004400d41d18038910b0014003504021605841d4007401440c15812150012b05a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 969100998 1250 969099748 969099767
    0x623040f050405040317420904050a02100905010f0806030d0c0222091209060804230d020304060e040501080d0c02030718061508190b030c040608010c140a 68
    0x144183d4503000001d08061103049100c075a81c6144414603068180841c240c9a50001035402e4806c2c41e10000146480480c002c191010f01c004002900c4010310815041c410300660080003a03850b0b00c81c03414100300680b0703026944104040305540c0c801100341008001460641d8808001041206c034105001403a40e0210380300742071070010f0030f002e00d40d0165440030800d40c1e105d2040d41c2000d221294800603451045800680080c1c0c45a451102d40c424170348010303101010f0318050400010307002400100056000b2071407218901d41d001840010350710b2401c07402e14180e9100c01950058001050811003a50440050170840a00310340a0006c0d43c100360920b5038030001c8400ca6001c00040008607410b42d142800070740c000c1d2900e94090640c0c0150008800060300c258402c00c4505d11090b1900c0820310b20511f140c0b4019006001e060307070160700710004803026081045c0459418040c060403040c00b136480c0c0c0701e4580200303075030000801c040c1a880c4000d000241d004400407843c2a08010b5204030320361108808 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 969102248 1250 969100998 969101009
    0x30a090b160c0b03060312040e040b100521061b0904020a110d050a0914010503060d0c080d020f2404120e060f0309060c040b1803160623040f 62
    0x1292103440100440307110302140c400c0642281001100030403081c030940c00640c0320741d805a00322510301e00110500502842175110f1840e00f080c125020500003084034000d04c0d00700d200c000041301b29548540006103101a0301c10000014520107503612401e074000e008151b400448500700c0342c102010601040b6a03441005229481254001030071407480340122003c64240101404840c21f08034100c070064203942c0f00341414001305804510016036955102c80d05002e140044e9510381c19504c0d11414026801d4008104803039600301060003040e414001c2154484030040c5600402c0c0700c4803207401c00c608040d00c0c042d0510007a10b4115200440103182d08841d80c11036403042d1702004105d40c48604560f07080010b42565882107000943e203200f610328401660060135034600381d400e6070300d60508500481c4144c6c401c04107404070a12081d00c142d0340202d10382845090180544240307040b5038000c4910089241c00107004110308540c4140710059101c00c2540110701d134082c0030b01d02810044142c24401003480b41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 969103498 1250 969102248 969102269
    0x50c0414030f010e0a05210415020106030b131709030c06130b03040b090c19060e131409060c18090705070f03080a0e12040b070305070c0e070809030a09 67
    0x300156500d08224040040d40250020004a8603941c0d03070b16101d42402005031200c0c416009100001018480c402400c06c3c03001d100540703082c1c585030f40e1300000c0454880c08425556901c0d400004200c840300c4062140303103000001c2c65081d1040c9041200000100102c01c803c0e80d05110103507013920006141405d005c1b04035040341c1c503070151101a16012070181c000200c42d00e004400d200811030140d0029004103441000e0320b4415443c00180891192003014441e00c0c1c1204030300400486001d4071500108450142261429180107641035060310101c0d40f2002d0030340413030b0040008107182400207907004403500c3e101a1078005a012242c1d0300c3c1440c009110b01c1406d0b04000725030303d1030041046803c1d20740d104410403c0024103040282500608450b0050310604004010b0004040420841114140b00c29810304107410101a8003c5802804023241406020415400802c8043c0341d9a030003000c5c21414041d0928011000602c0300d4005044400558000d010320b0742820741081401c41500c020510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 969104748 1250 969103498 969103529
    0x4050d0b040215070f0c061823040e03070c1d0105211f06470c030304121e0c0201030f020a09080f03040815070203211009050c04 57
    0x2100c64440b80d0402c0e00b401000140481002219800c15141a006440e4069440d0747c03813905444804098401c0340220642e04401c1c030986a48540300c00392100c60300d640071008400800400c040351800c0c209401c05500103c0c0c0a01003042035041d100140ca6440422800d103114502040c824203418011184143d48110f0703084000060b04d05882107410a1204903000010403000010b5101400901900b089040450100d00c405e203603280303048152030780426507204079600442e510450091506030010704516072414441240d100740500030b10781003074010b1503482c1801d1a0517040d000350304000c4418040000c1c40045484042071841c3d074450750504018084120b907100480041410b500c9603d030480c804155940d4140c0d1101803007058450b035100312400041c0e8602d03103070313902d0199114074845a4800e03000515101c01200036a40c0141d61401140e0600e0042c05014518040e42c02c00c001010a1036010008842d0b100b5004000410285400700001d09040740050303180d01c0780c7e01440800c0000100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 969105998 1250 969104748 969104753
    0x203011109060d0e1903030510080105011505370f03051603020904060504020d0c14090901030201260406140604060b180d0519120302091e0d1703180304050d0b04 71
    0x202c14220080c1d0004170300181441464050004c0006840110782d1801c0900301042000c0c1c1489024140c1d178856506510345030076400200c4656120358030740704030380c99090a59a41c509200e01129550b4210f1602e1407580008020001c15401c0030780341c410100f50802060042000b12000748410680300c40c40c000d80d484c000c107400310313024140584c0728176045480041c010140212a0340700d40007070b484560b41d64200301558180e0b0035281c02040000381e0305c035000100420041d0700403807d05200703000b66403215445415124096020040031941940e0785070b2902290700080300130a189592204044404004590401ca116131045c0121000e42c1b0304088100030b246190b0b07075004001c0e40c842c2d41c03042c120b400c1c4500030003540f89d130900c6501d4102c2e0450a036443d4244100d0090003032f205030f02e001801207020301c00b00c5a44030240e80e5412403d681c0044010b582000403d20152114103a0980600301c41d540e42841c0c40385201d117002e40c0c030340b000058200380018402a51404100410070b504120a0151502c450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 969107248 1250 969105998 969106003
    0x20123042103080a140a0c051e04090e2a12010207060b0114130e090c0303070c050103060e240d0506070807140c1906060b04320f0d050c04090b040203011109060d0e 72
    0x40880201c8180d1160440c0b140001c41c1005002f0703a002c5800a0101c010b243c1e01913540da10b882001950b290711a4903140d000c0c41703020b0405101101e0b000b42460700082a01244508980c41070100350791003038030b03000240c80558015050b590b442d40400303000c4e031510301e0724844e005454000b401825030031682c00b8080742d2031302d03810044034184802c010152035580c0d500c1d10b000645100b0b18030450307010900300100010303441c1000c1c0699119400c00304078250f00c40d0401c1d083c1603540845030305c241d600129580092012810800c0403911801d00c130b4483c5171007400c0141c405030040720040d4500b0070010081149150800d40420a105031080760f02500c250041c86140200241139280c014003540c58000c81c00003041104082c122080300c1e9020000d101ca14500300c030170504000070084081c0c10611500003420541084030882a45c1c80c02202905c01030a444400203080c0c881c2a2015185801b50b00203000c01c0d8582882044804818080854507042c0300c000443d10f58055000c494225540d01e404503040603030107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 969108498 1250 969107248 969107257
    0x1c020111070617010909020109030b0703060f080c03010506040b03150c0c030a02061005010212160f0c06110618060f070203040906090f0c020a020123042103080a140a0c05 75
    0x103850544048a4454800034840c41501c1a8020b103450350000000d400c001c0e42c82103a8400f50180d540b2401c050070364540b4078082d00090054410542d880c03a0008410070102c0000e0090034034080940581c90914081500351400503183c148114a40b0b08808203030758002a0348460041101d24030b064903611041e103e8003c3c050381c07410580c540800151010590b501288103440f5296400c0c1e0642e056460b980120b90301c5009000040b040a410000081503403410300c03401c948d0740e204040d280241c03080e075600c1c42c1324400c40d584004049a00780d103120b9059a001d02c5003552000442c0c4014540301442002c040e500c5402034203030f6864041c690045520310f4800d000700c030090b05e89140107001c056030700e26400004098011810100c00d00d01405025240d00c0816000800c540507036405200080062809400e07100c0001c510031032600400c00000c1805003001d90760f10141454146038400055420040c1c40d092005142d1941280741805103071a04003a0400c030790700704514040001d0694820310f010b07681ea118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 969109748 1250 969108498 969108527
    0x1030e030307080609010e060607031202070f14010606111506031006030f1211060c031e16081006050a050307030204170c010216080601090209060f1b0c010e1c0201 72
    0x20000070800216000412580038040640d07282045070f87c1c07040200d00d1094252031041e48100104007441c00310f403041e02050341c9907100620043ca0b0502980d1460080c61940004860141c050000402c030401c0a201d010010142070410160396056111a0794507165012502d40000404502040d0251810840142244441c07001009070507141d04000e2810050008102d5400070707101142e0300c0452141880c0f4524144250003040107894800c86036103190402404a40a840f100e90a4003010f0102c01e805400781040244840c01030031040c2c80102241b5000306615035549040c081005681e130b00c1011a4100c01076454881d4032521440012000791007558400800c0e00011a81c484030078502042d102d50701c800c2602100c060310b030110000d40703400d003440c41018003941080004000b0311809400406451000a003c00d00d41900713a0045c514a0f0804010202c03e45944a80d0009483e010003c811b2001c2c0242030245044c1c16050000e201007034440d11000c03c02403004041c00469000d0b06c0000410207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 969110998 1250 969109748 969109753
    0x140c0307120f0c0b0712031a0405060114070b0a0501060c050d211d15091b150a090f0608150607020d050d2c0105041e050d0303020c15010f050f01030e 66
    0x240c4d1400703541c15541007481c00b5184405286c0400d6910381c028868440886428444042d41100d0300c000c1100501c4018441c50602805400704080c420705003000784145889088410201d041c001840b10840c1d10581002d0140603201070328401081740040c4140c907a100e42d2400305600c0d901420000e690a0a850860f100d01d408d0204401c0d0911520000070b400000700b02c201c403c02e806101c640d000000701541c10003030300d411020300d803022941c00c02d0708400501c5010b000e00f500e545041103410724580c8a50348440000740050001d00440d104011890000c240750b2500114a0601d40d40580850899081783c40c03140c42c00145107000c5403100c2c1c54100c166608002540c01403a09440007500d81801c08480184041100c24009250b00c482080140c0860b01070391038a00b031504154842480700c12184a20401c2e0401d900005031540d2810764486e50305100342c2d00542c542e542082c00c103146c10300340c00200000c01105130060200c104001c40c10703003c680007190a49003c029044c0164002c040303d4688c1101030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 969112248 1250 969110998 969111023
    0x30507230312030603010f2d140906011508041e0317090d17040b0f06060c0105090a12030b010f120207020a230303070f030c02011103031003140c0307120f 68
    0xa50b00c2000d584600c8068000384410100307004d4030022a01030415500080c0b06041c502204c1c10f4502000440503001031100042c01001c0138407043c0c18000442d402c90141d80300c0c20062211410343c00f800d0a203441d050822880a00b001d64410b80301c8a20031503000710314849a007a030410316201d41180e1440c020a00321400c114240307840301c00d840b0b072884018200801c0e00352080c61129074141001da403065400c00c0035509a40c4a10040850310744014091690080c0c06008140c10040b082c41001c1c044c15102004120040d0180340503880c410b01c2407840c2e401d0504d000d1211040342d81160048a0000161030f244000c400b09401032802070086400180d0850b00d0f915001c03070500c4103140301d0203070300c02014140300703141400c803042603642c2c86007a4006004d40000f0b18410002800f4080e0141088e105040c8401101c4070304203a50720715001200c00c0c0107008607002c0d0400600c4102011840b02d010200040c10b122015840466580d4042d44604074442d081e100d012003e00000c0c1c0940703840180e00002200b501d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 969113498 1250 969112248 969112273
    0x6110d05040b10120209010b09011815410c0106270516140909090604020111010e0c13060e10030606090c2a060e01060611070305072303 60
    0x3600000c43c1c0d1250040c0d080d65001c00d041909908a6004c0c980c001d0260341c4903030916a41071015040b5485050500c204080c010030700c2c69207e800e0307101038004ca0400000160040e100140903a007000d030004010100030b29808080000c9003010b1080d42e0087e00369040d120f002d2107860725a03100e002021082e65203007100c04100395906010601101c20030100c00e011448424005200f107440641c1c1c8011422581c0c1098251203019214000760140b0144086052140d02c40106021272012110345409070861001c1004540c1c0004400d1310743e8442000030881c808400d03074400d45c4c1d1304040c881c00f441020103414810800310303d6081400689104031400045080c040c0990705089890301003120503501340080420084107620442c09030200a68441118088010004440c0301c80ba00d0703c652090000b0342014041a0103020b01d524040e15180001122440d0940040415920a6100226400050b01000031801c00100750b000c2c0d60301c2c20b624070030640206a80041840140d41455003500666861504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 969114748 1250 969113498 969113513
    0xf0b0703030e0f0f160905010f050d03020f03042c04020306180703021e0111150103030c0f0506010308040513050c0a11160e0403030b0f0a06110c060f070201020f0303100306110d0504 80
    0x7070140e04902c1170398900c4d20340d0568001d4600c24081d1580c00081208200013600d80046500c13280f40c028015118a01da01c443c0d00fa055a00030740004004100070200031a9003031580504506075008004544280c0c00c040d40040d80320701c000342c160261680c04003100c0740014001d100740002141e0081180301103921004202d210b01c1c82c050036241c0480c0520f4006040980c0c081090a0039201123a2084003a0f82580d5040d00c81c40d200c140c054411100032450f10b00010780070403020380030f94042d8640e1a159840c2500f0000341c11440449007501c00d0528050104414102c402d4690010150400c04004941151881d252001d0006890f04491400c90005002c2500d112440c8c06503010b0340e01444041210018405544090300d40c494204040041c204082485060b0400c50850080180e4a900d8013000c006150b6800890004400010010f080300856030100700c4c15983c3c0700038201031825854945c0b54a200b00c0140d1101170109500c0e01481c03a40201341404440c18000c80000820407030509040425 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 969115998 1250 969114748 969114763
    0x1e0c0106080c1e0d08040b1c0c090303080105060309030c1e060a09030c0b09070504230a0b0117040215031305120310061404031410060f0b0703030e0f0f 67
    0x9542d004014050556040c400581080309014110740c0d070030f099600303090140040782004280c50f40c0c54207010200d43c2046410013003090002548445000001c801c1c249802c8400040100007805a450010030000cdd401401103070440310203c540c85e849582d8009007a0661080001c1c45419020303400090303008a91503044c101d41000340ea0f046030125500c910707a020484040080140c04912050181c2c400100c8075084c0c01c0d84000ba08068901866840340810148d80c211501403c0783c00501c480e41c1d90f40012038189903400042c5880520103a105180007074942c400714106051070245540020f420343d22400808000094000400c81c0d880c9051a0740a4a1025644080b2940c0c040c41031238000c8803c0000580f406040146a108605490103c0a440105d444000c02c280e0500c1070000001040004900c911241c8419002d41480c480da0382050086a4079600481d00c8900010b0051000c43e40c0707070090b900b440c0da0600f0700190a00b10032072418500700c2a1401a029032066128001081c0703808540c06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 969117248 1250 969115998 969116009
    0x5040b040b010816050d21020a022704150b06070c180911010518060a020d02060a0603030e10020a140705040c360e0a060509070519051e0c0106 63
    0x181550b07600c9454864403540340d00e421961a60074440240040c0ca003d070101080030f4400d01400c035a42c14200008888080c1d4011000b002da000700c02c05d10158148075504403001048140018504504c901d11f4142881002e80b002d0f22070700e460404031016070f80c0ca130304c040310820000f003249441c3c0c1391078034098002064600502c0081c00301048507003010f150b640034200390190f000c82c11a81c44580d0400440d210340110142d18940000c90350f40c0f10017505c940c00140300810182c1e018080b5105002c0d400392600d000039049141140c5402402c0000c2503006480d816100e000b11140841d04801d660100d00d03001c4200340c05041c43c7c12640303140c4584e020002d00c2000b151420383c0d051001c121814003c0d51400c8040c040a4404444247e006020b54001030340003180d2000c00300a210b1640d2207038803c2c0d01d001c000305d96182ca00c0c3c1d038903401809a03240c03040b00582c1c40b91030781c64590f2418007a0600c150a9400c001450306c02e1200114440222303562034042d00d11030103002e800031921403800807420b901a19071071054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 969118498 1250 969117248 969117263
    0x50f0a061a1302030c0906070b07200703060906020415090f06031829040506070201051024030209040f09060b011412250305160f021e010204030605040b04 68
    0x8040908a25150001d6001000d2140303140d8200040d901070351004145846040d07082003100f42da96900381c00781045074000e003072850f058900414050f21010440344208416a00000700c0b400c0d00c00b0001d20361080d03030340c4440c01090040340c07460504c0c00382c0255001f070540c080c1c03a6800c00680070b0340803010400b01d41d068400c9413042d07503540105a0454080c2012020a03416081695011441c035402c10b140800c481e0030807168940403040d042484880c2500c003280c1c56003000c020b201007a90309025154015012800c6c0780075141c50914010f0790f0a01c401c0800101c40e006903103071405e40d80698140d40070040040c0c0184880e4904448100050041c0304080f21128a071845030001944510b00003c5107100d160301c018039141d0650800d0b001c003c00280407520754000b040744821824130b00b0000d0049240540c4001c5000d050480d8070100800c6c9500350300d007c01c083e5001381544150300240c211081c0090581492008a460346801d0180c804d580014064900340014072003040440340c002440755004008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 969119748 1250 969118498 969118511
    0x50d03050a06061d0a0902040b040f0e010b07060b04140703061802090f0d050703080409020307031407020316050a0c06080907080c090103061802090705030604110c0d051303050f0a06 80
    0x3090720448505001c2c542c00290440b00364080c03181446181ca42e1101c006001d0902d40d0354a054070026a880340d0030800c0c0c640b40c085401c1206050409002c8050700c1003c00f0006150304001821180e8025480c000d80800d444903600d110303d854685c409408420300f15080c0350701d490a040d020b009051244038911038100301c4c54101001e081d0034425070b44543c01c01018024011b2508007007140c103020390381c010385040c09100700010014220074001c0c00100b10081000d81caa10b4241400303811100111401580b04c20540200134525038080221812a40d00e0040d0015084d6503050041c074110f20003c0007403904080c2369000c602180c100100c00c1c4580241d0301100c5a40c0c0e05c4200301070300da00745030131119040500c4030010b200055064208030501c1e00300c100385c0071300d124150b00090594441605c803030000c110004140701043c1007174060341803103003120703400c451070004140044d664030040d60b55840f007002004106122804510410070307009540020856406200c107440f26602d5401c0500c00701c603130074034168 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 969120998 1250 969119748 969119761
    0xa0c14151008120d020309030d090f020a0806040c0513021606090606062d030b040c0f1b0c030213020f210106140a0807090f080303180109080a030e0c04050103050d0305 74
    0x4018103490340d19183d035400d0134460110f01e4043d4001810b840d0306130000b4041e00501e17000c10301c10000254020007841410b80760314014010f0300c030440e4112109a0301310344200404542d100030000210f440c1030f2155860407105a80080081c003e04074010200600748202c0d20a00007543c205031400c60088000300929907480d101901c01000d0010090645480603100400043d003010a443c450301c041d08005ca00310320214000390031121040000400b103030039519100702d201c0d8094004d640300c50001c240419242c00c0b603203030b0380061201484000d01c2203000d044c0c94001040d858040e00e44900c1406a810b490b0701b10843e6400c1d90fa000848500d581c99800400001ca4a205030325020b92440f04401c1d03546004410710b411200315100a15482c28480f0750440003c5403026050381800030b0048001441d00d90030401c4038042c90781001600c803d5240e041192003408a40f01d8012102030300304a080000f103515014621a080070307589000254000e240c0000003003407120101e00e461456416541c10042c40d41e684 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 969122248 1250 969120998 969121003
    0x1020703150203040302011517010606050f0f130b030907060e03030f041715010902040602011a42070204150305060c130305010e070302130c02030a0c14151008 70
    0x621019201200c400c10501816078194011600701c0d010348004a206404880100c00c00710940d880210161450241901a14001c0c4500c6000d040725142840c504601e5044281c00c03070140e400c2079811884005010600d07080d0580d1100d00600091040070f46034a2304900c460348074400352040c50080b4040141c1c41200345800310490340c0074500c2d0103100c1e05003400e046160b81041811400070301644501c040c10000380724181002402003403c0e141c090381e514208400282900c44441408002518010708044590741d030303580101c41000b2448054000c00c0310000030b280e455001007a02409540a060303003021001c1601c0050030007030300039074090040302d28040d007408040c82188030280003508520003040a1140b2a00181402c9031005c0c1d516240c075407603465440c01c4820000c5030b140700f50b0110400300f045040c84000e0b00700b500c0c00360108101c1e03070f40f10040103034a0744100d0740305008224580d40031100700b100028100103014040000c80768042c010341d44440d80868151181808506081030005610400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 969123498 1250 969122248 969122263
    0x1508060702060c07170d140601020c0102030c071719120914150a031d011b17062b05010b2b110301061d060a06110a0f150f1a0102 57
    0x50f509500d400b005841c3e001c0b0450071120303000c2031442c0c1080001540461802856041d103888000302c911818985c001900d4982c00000f0241075401c1401841106180810072070f0807103502d49085030650301070380b040a050183c0c510018400741c40040e83c010500c8500d181f00044002543c4405641c00d458480341000b03051120030070b69100c203011034801c1841c84018007074440c6440301d013404200e0a45003041c51401e4403102c095200d0350303036440c401c510000b4003a10740008c224211341030601a01e074005100ca080e80400400c2d141c0560010301e100c903420b01c03461010050f24250b10b403807040c5646003490705070b001c0c2501c80920781c49644200c0f100886002d2070b104190300802410401311002017690faa04116250020342c3c1640355503a03827400140010480d194071072095444152410901d024410403400642c0c50f08110101302904800c08520380c40010401d00f40e5420102180060f0b0403840c0c84652502c9c41c2a800c6003043c2012075052106600b5048583c052804943c00c401c00e6401c1d000490f0788109 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 969124748 1250 969123498 969123511
    0x7030215010e0c1c11160605070309020a210b161e020c01120b0603100801052208030402040e011e06050409032a0f14010c090b0405190504150806070206 67
    0x40c204a5260041c0141c1030480052038210008982c101c52214820310300d0700201d02c40002006c00350300c4401000480c1c401c45501166030f08080140c0d0001d50003090758405640251800c1100249480b842c0001e006840200356910030100d05803031408440410308441850081e9012465410080c281500ca50381e0001c001707496503006020442005004581e07201d03951540c200c0903551101c01072400d4135824015881003040107082c0035000c2c9410042802c40d600140703420182115000100411062070400071200c0b0b41060025440781c9a5000180003803c0c4428820210341c81c0004980700b02d483c000c0c1d085c0d1010b41010042090545d41c000307000c01c3c1d9559140050001741c070002845140300150740640b15031500000540e020081c00c3d0386850080040c40400c0d500400d00d0300c0b0b000001c40f0709000f01c000042c624a02600f102e0300d08071520985020f24041c1c948103c405000c0c0c845122007541d201c2004220080007804803415212503205602461301481d280c501811002400039030000030158040c14 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 969125998 1250 969124748 969124771
    0xa1803022d030f032208030901030c050d09030e0a09051902030c04090510230901051c061d010c020f0d0c02060909041104051506070209070201060b07030215010e 71
    0x840101e5401ca040c04024441500c01c04901191a41e2401c10003449160a081d0065aa600380c811508220303550200c280c44980b80d004005125801002c820340d43c041d442804e001c64406540030055455000c1c0c1010100d00903c1c1c00b071502e06141d80700c540c120700ca040a64400070f100c0d03140c0340701000759081202d0408031740c600c030240c4190041495005540c48119000d0050506481f994204295003050b01c000d409a50340800c01e10080e1030301e445903400359503030314400c501101d0468041111018144107041c4038a14040065020404080d0000180b9074421401c001c403445c95424804600000c4201c1912986030106414095000007000304600440d10000d10180203034220886904030040c00807a0004024000303540b0780c0d00c4841d001402948036884d058410070700f500500c821603c0003000006c0150340c43c004101030307840f590102c400303898041d43c0f00e440540c0c03101400d03805003c1d01c3e400815403150015003002459808902008000f103100e440d0845640d0328400101c2081e803e48100c1c40c0300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 969127248 1250 969125998 969126019
    0x41503210813051c030e01110403050c0d060204120f050f1924052d06061e1209030705010501091109040e0c10020c0102070f0317031015050a180302 65
    0xc40b00800907990342e02c64012913140c01070781c401003000908620194000b19071034800604607460207000311400203036410305603401e02c0d10b10f03101d40360340e5420a1800350003070801070745410a02c0313400c0e0106c030040c00410341e84529580491030090344521030980140c2d1a8040c01c41386905a4801180032850a00e05c0112010011880d441e0700901e03403130500c0714405140b400364103c018145540143d074400c4041e00c03081c1e10790760400381d1504400d1400b0b5512490242406c420407400303694003800d99441151100d060318040980b00704900c1030380302d0200e038455503180810400481c1c0710004001c000e8144540c0090142c0c1c0d80e04d00500d8192012451a031008103000d0000c503041d07003042e83c850010651000121841d403203203074010520090004148200603007008500f00e085507010010580117048203c1e07403800c4249940c0f41c800070122108075400e1004800000714032002011030104024112059038050251190b22014103542d0007841e80501107020389a5004481402403040d6080303a401038501c80c0711 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 969128498 1250 969127248 969127261
    0x8060910150e0307260f120f0c07090b12010e060103020d03030f05161d03031801140d0609050106020a170a0c0b01030503030901061a09010e0604050415032108 70
    0xe03450074480c500c00c01804015250895400300320a1004068100c0c2c04a1050008207241045007440f085040003035211b10361040200e500000c80f2800300c0a41c5030a15201c106262485815214220365148644a20742000c5403a080b95489800c90744000c440350880f080b401c4d4422401d8940103410564181c00000040000d410584151081b40b48030b0318000032404a4082c103401180d8099a00140c22200c40d8012041541c00c9a50300709503d28050000ca03041c0d4070500040c0e6a44250700c0c1d01106850f50020442e02039009600c2c00c41050940003070140c80380c061100315402000c00344103040c821070a01c400001c0741800032440c1c070402c907001040c0c2c58810103010113000b100d60040799050100b02d108024030010460400d001c9018620030340c040c55403400d0246695003510300c03503009140ca03078000c2d040544203c00090210360501401f03007400c4604020b070f400010721600995002c01e030054240801c0300c1400050141c4402913038407903455510400303200d00081e509101c800c44844046400740000c50036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 969129748 1250 969128498 969128519
    0x709150807060f030f050411010f4104081f0204080303061908070b090a090b1f20010c03050c09150c0c0303190e031903120905030a050a08060910 64
    0x40c560030f030308020440c01d0740540a0000c403181150151411088186204415a0b03c070710031310b045402601d00700281405840020160514004001685086428004e5407450001484002000c1e01110b02621159038030446910340850f54080800f100ba0f084111404003074901c00d50303003030386d100030021815a6207500074040800203242041b90301c80d54108002828500030041c40029090011080c2d80f60309030708091004801c0705811460500f402d10300411142e0301e92200c0c1c410030b80801200310b10910780c000f402392800f9039000e120f500710651400c900706105805401450b0002220743c1d080180742d60342c40c003202c3d035405140780403940481240b07981c103003403040d22020f04542c10311401079590282c2100006891640a0790340741c0c02ca1180c208440c4c01c2c2c1074100798109100718064024100d5940c0340710042c1a080d0300a0001020b00240c40310642800340e0300c3d405101050b80c084100e80e51455600005421600064210800105120002202410032490030750140b00007a8040c080c041c109844c240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 969130998 1250 969129748 969129767
    0xc1a0f010e04170a02030403020a0b0a0203030f0421260606030114270906090a020d060f090f0c1509030210080408070803040b150402030915070e12070915080706 71
    0x6401d03c07516003d140d4402400001407124020640045554514500c1440028a55030303008444280060100843e0650048201c9500414906540c91103695900c2c140810410307803881c40a90300b400780b4036494099000030348100303502c2c1c2d241c0f041c030f41150aa0a1004081404880780c41c1c00480c1400100a010742541303050f0003000340103024070400721004440d2040c0441d0700080502e81445501400405003044c0801078005541502522008240360041000a404004010a41640d416200d403410720603502405110307510028414080c81c03e4200b102e0700c1c40580c014124407900018000840364001c0c0b8800701181e6018100c407903080c0f240714050300c00c550010000d0701c401a082160400150148004501c920710810b5110b595003051024140e01011003407106004610400a020301c1d0680000ca003c640702c451141808182d036243c0b022280241c040380d40d0b03a001b40282d090b00c800140081142c1c816500603240c200700d02198013102011001d41441103c0c955041160180a01480f881014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 969132248 1250 969130998 969131003
    0x9160e0703060305030f090a081b0906040f021b070510080c03100b0706060602371e03110c030c0a0b0f19120507080907090506030f0303070c1a0f010e04 67
    0xb10642c0c0c84d1211400d40d030040b55410745c4171200081c0c40301141f902e1080f8001414000740280300c1501e81e101d0308100300d901c035036000d03203d0024000021160b07a82c540141c80c1c1203030740704800e64540d01c0800e800940890080200760050080b400c000c60385040c003804c1e4510310440c0b582c1c0c1c800951280da48a0a940e8400b40800030200050500807800480c040c0c020101e0a21034800095583e00d4503500904218019012190b02c1410700c10445043c2618402c01420510303001c100803021401c0e280c12001c50810014600c0303c0f04010100c0001c1c560050380995541084506490400559008142e26001c41c118200c0c3d00200c0110309110300d0f4000c4020b4403000174404c0e4800d00d010b8030300d0303c001103800485840740001260800c0e001d080d20f00078000c00ea0000103609010400382000741c01151100118007a00d200c241d641c10000e80695010800a410703000550242c0317549007000340c1d00401045059006a0ba40051000e69400c4295054522480307510400080c01c496401d010340344e0b88480029200303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 969133498 1250 969132248 969132251
    0x605090402160510050906070507111801090e07050d03080c130e04080a030e06010f120309090203150108090f06040308040f06050a06050a09020c0a0f0f060e03030a0509160e0703 78
    0x2070560b1400866100c200d42c0180c00800300b8101149442042d1007000308005a10741111060008054126007070720307002030b41709028142e62202d50020070070700aa03102440c15906a154000500b1507a29440072082c0e81c034040640e088951280e007880803030b40030700740b0041c00a0048800100c0721245e0700080d100b4018074070810f20105a40704a2030b00d0004040d0340a48070004e00113500c060007501071107408800a90400600502e40c5003801c223a868806510448c0002ca401c1400001014031402840c07005c1e010390711086440b4107251404008151441024902182440300803644803e40010228082c000c6e0b10018040b030342e10355400704c0351540c018104440300020780481100151b2180901032152179030f800001040c600e40404c01074100c6860b440032111030b01c10084001c0007000850b01c00f03a4030350031126200c0340c5440c0b840c0c0300f01009102e04016154074034141044601c242c01000031401100c580005000907200c8024941c1c899100c5c10301007906401001080200c4640305002d15400500c03800e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 969134748 1250 969133498 969133507
    0x1b010207081c2f030a031a0901290715150f12032105090c010c150b06090a0b04081011030406110c030a0c02091036060602010b180603070605090402 65
    0x3604000100800f01507103d1342010452417100c030f6141c80b440800c0d00c05164a0034418070300d80c0115040d210103018054164a4208400c48800700c03e0042e201c0908142d6886030381c405460522142c1c0030043d5030020400f9061111080c414807203204242c0981c4e404181d401442ca01e400314100200866182c02c42c107011a90399050042d040103901c18070f442180c548003043c6468542e52490500f01d59142140c144100211180b01242040700d0344080005844400615105c903000080c000b40034103081c00d40e00110440002c9117041c1407102800444000000f00d444050b0300c690091300303a420341040522810400c0c00000c02180e2160406520300c1c0d000362099203414943d520190640d8440d000e1207000c1082c140c456011410030403d86544201c840c11901216802d08a201c15aa2202601d0200071114030032800540070201008070b180c0c1c10100020050650303181c8001e40603002c2032190a100f115001c00508003109180201c0d0301c1010010b002d03041082c10f0190650351038005d4a005a002503003400f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 969135998 1250 969134748 969134807
    0x7050405010611012d0e01090b131208011202010c02010e060d0902030c10020a0b0702070b0706140603011a0103090309050a0308040e090a0309170f1b010207081c 71
    0x2003028003078860343da105244400a400000d0966002c1103205442c034060840c001c048907102c0816a01e1741401180106480c060242c0e820f0251600e0180500b8071821007050000880c1811000303e4010703c0760301c1da0410541191002d6880714000d101d44103000d0201070b441d400540c498943c01500d14414140700d0303049007089000c40d1a0303410110000b0b1003103170385100020540c90200002891100d04440d00444030384115002034445407600c50003000e620340c12000ca04a03600078403c28024000840d40c0325152080d505001c0d0152448540c001e408000071004510a4103041c060403030750740c0d00d100024101d070140100450042401a809030200084403801040540d141c00320700c00118010385415490301c0c109501e0390511070000d0480016540040e40090000e500a0294011542e003802464201248609500d04000440c8c8100c4410b008141358000c032900b841c00c49010003c070aa08a8010a8440000540c0e070788000402d80240c03043e01000701d45a510544252901d8492100c000400c4000b25 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 969137248 1250 969135998 969136001
    0xa0c031803060621170304021c0501050601080c0702010903080d06170115050a030b0a0b12010203070903030f030c05030627041218030f03081f0b0306041515030e070504 74
    0x1608211400c0303480b02000c00c43c0380c0d01c0c0d44080c082d100580b075101e900965560384411044c48100c07148601c280d404000031703048d5030320741c01e1403250048078041c040d00515007842d0150080100301c0340c0d0b42c080742a1202064513a000001a10f520990684a014400d401d603143c452640e0000752000d6140d0b0b445090100350300d0082404895900319650001c43c404903248002c6071480c000343c02080c0505040c1c03a0030000325001310b60054001d40c50007800121000e406c004201c5110480000c546030350300010038030640c10350200c0e5240403a8003a0783c81c071003002c02c8450b0480c26688200f040d840014024400709946240000d14510f000c441c021090f241c880020003881e100070400c480503036080b402011500310103a084000549071003100d06819200340d040d076540010800491001804001c0517000080307003042504580420307000040048c41d843c4d0390300c107191002c43d40110380e00d60040d4117012440070480d07061224442507894141d03003c08a8094504214001c0070110f001e0b045a00c500400044c494445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 969138498 1250 969137248 969137297
    0x1061205032502010912032c040605030c130b270f010815070503040c051309020112090512130f06032c060712020c010e010903080708060102030a0c03 66
    0x14501542d2103410621401c1070096881a030031803031400441e02000181c1c0d100002c102503e00c11040d00140300d449050445120101240c640042800d420a003007107020341c101480351441c400c035814070840d600c030410f040e00d035600700e8a07058004600c070130b550701801141e400908079030501404003820843c1c4460048044003200305090741c5c40d92450103204c0549048020980034004581c0108096a1047c13841e2010300c1004100008010000c40814104006220142e0091000800c00004140310411510041c100200100d0205100c0b41121800f44080d01032441d00700d80110240944904941000b443e591188030750300d00800391824045001c2c2c0c5a0340c51040508560f035000101d100d95001c1841441d0600c82203820340c0601d101c04641d00c0e040024403250310090701d250066040d850f581d400000ba00032050542d1155007401030102d0500415440a920302d0700030f641d141103075141c0140036540328006484c1c480c01038104000c04192540079170b0400d07010a02c03c3c58413840c4180d1004800600131003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 969139748 1250 969138498 969138503
    0x31e03032007020907050c06040314090a08032d072402030411270a0e0709052e06050a0f0507020d050d02010c0e0306041101090e04030804051504020f010809010612 72
    0x1c0842c070308040d800d0440d5501c0e031040035410320714501135902c9203050391003500410003001c0000c4a20f114804021850507280301c42805840600e400d49c0740d00250b516500403c004400500c2e95013000700300c803108034000c14050010a41041d00c0c041680d2280195100c0340b60f241605130403d030409003042c0380b40d803000b90700c958080e4020b4040840c0c40c408005071100500c106540c81ca94081c0041101c40f1603107902c90304140255000100604200f07052410f18086900c1055800c0c07410007000302c0e000703441030b052410550540c456842801c02d1008850700410703034002e00000a074240903840c2d5003070003840c070800c40c1001400c0550074046a94002039003a61421000c0350190400b000d0003603459024021100b02010504107102400a05c8011a81c1c406c0020400741106207081038100c3c403a40a6000900070b40329060328001649400d041c00f514076201914100c1e5544501640c0c81e000c440010341080c0610b900070440c15103454414011200200080d140d940c03d5565070000007241080d1405080d040c91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 969140998 1250 969139748 969139811
    0x1090f0902030f0114010f03091401020a0203120105120607080a0f0204090f0c020f1f0e250806010f09021809130507080106051807050903030417010b0a031e0303 71
    0x180c00542c214003e03006070710505203501c4498841c612681c101d03600c214200100d240004105246003008020f54400046100b100d510004d5540780c02035010000304401e08181110206a90343c5d40c2c103009c4601104a84e1008a400980108002d18841c44560390440519078000c9600350b507240e0170740c007203034004d0313014001d480e54541001e2000d44482c0540f43e514603d0307002400c51040b1003292941c50744a14000c800124450603207015139500035600a60901c1812030803541025071803106490202403504501e01904030310007001a035a000000c28034140e603408121280024941000715001e5003007099140c84d942c00780b50b08450b40351150001648101e00c02c203c090b918035105e0900600b00440d40e048030074980d050401c01d00c20f9840d801600605400348482c000c0780b0340c0d1100300803610b9015400c4615070602000400140c0406840c40311a840a658002044141030080802000c49803c2c80000c0070200103454046803524081501c40003140241404500c00400380303001c1d002100030703140e04401103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 969142248 1250 969140998 969141001
    0x260c031302270a0b0a050103330317130b0307021c0e011202070b1314120901080c030f012615010305061605030406020928080d0c0c0b0901090f090203 66
    0x3000402c00300c0e030803004014040009104060100d02d6140c2030340a01418035407140390318a11400000144448002c2c1290340c40f9a007080361135000c01d0350310503200503122032802e001d86424402c2408100ea024581103010703048080d10703002421005030402440b000c194012400045c440c103000d0f0b06980c40d400b286586c1d4580640c4108005030501107000c0e2074940c060b206200c0200060320303070880705821050441031a41c0220031850803101030588108481002c1c02149204d80240103901c0c041e08041c00d00340c03542c407000c1e60b0b1401006501d0001304e03680d0800e0fa04030001008600c4854030410010501a00b00e81c10828240c1d0b02140340414446000c000c080352040100103200050140b941c00c00c400b2058481e00501d1180001c0083c00040c0019203e50fa0020b0104003540d15113118428a0644030f040c0074010555908000300c40c180d6201c4c80ca498003c3e03003003800c0454807580c1c9a000c0181e204246101c214105060207405802c819045414406003040108460002c040c200006110310803015949 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 969143498 1250 969142248 969142309
    0x4140105072705010507020f0a1809060b01030b0906010e1504180c0509030a17040504090b1008011506030518031b0114101e0e130201260c031302 64
    0x42c6002610000c00500c00d05121907070b8018201c82549030101c541a0b0345001401c00170f03142003055800b10980e001da9203100240c246007074002600c0240150010080400440c0064040c0c0306010041d603804490000058203540c01500f89003480107004e0400c95100700d4040700082941d115800031070807041980405502e4180303a020b4010003600c5403821504001040001c00c2d503d4920510080c5140400100302e541c001290094500416006005118028040c24040780c190b5094030b4040400140103000b152100d0305005610742080c40580700e454041c9031480c210001c1001400030355140382040f041c4007540804002904841c1112038490b40012184001d080c21100d8024004880708100c00420054482418041e002c54110f481400700c4080c0b202da5162000c600d03900030402c46220b410a00c6540300140000320820340c03003030300c644214070f00c1c10841089020840a0b1069500f04460000d400001000044c5410581c64a07800c0b80401c01540045d50100c00711181a040c200e404141050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 969144748 1250 969143498 969143537
    0x12123504050142080618011e021803011b140d140f0106091503090501140f061c0f0f030c0c18050105010f1d130207080a0306060f170414010507 63
    0x2501104240f5022801e18000d6a5902d401e00205130781100000c02d41404500070080d08981504070846c4900c00c0385400c2c030100f40f0020b402228103401900d041c000e400c13001d800c0511542c480700e42c0f110300411008070810021141c440c072280e44451031000c14864080e100b5943e0040b12868000b040101c0054603000c0c03040c0c42c41600503844081000b400c29400c02016912543c034000740f8001d4038004c80c060541d8280240544103d002c9181410032100070442c0c80d008941006029203130480b00c510489810b4800600b00349282c980280840b00550300031800940902d04070080380340b00f82400c0c0d40c1645243c8a191502c03c150344520240c000201c030002c550012072103000d016007000d0038001080c2c502100c00401c0542c25607690580c3c044205e040700305503620f40c80e010400e885124070640da6908140703040100c5801542806021a08000d0b01080c828014100c90505003900e507165040349406030b80c40807040c038020303000380c0d041110207101c000c0c3c145084c050103120704502c0c0c03104100d12070700d003c0410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 969145998 1250 969144748 969144851
    0x90a0b16080d06091b1407020111060a0e07441c020c0909060a1e0c03020c060a020406050d09030c140a02030c061c15121235040501 58
    0xe100f040c1440c0b450311035a8010b100b00056402c440503041d00d03407c0520058400c2112415200c0244c800c4400f04068250203402c0100505446001c0e034500e645d8480e001061a0740c0c0350101055541403040c0d041890b0515980441e400031a1004042150001449141050202801d00c00c1c0c07010840c0b54a90f21a03010019401c90b0b1500380d07907038901494507401180e00c0781030191500769244c0d01c40f461600f4070121000c044480310042c1c002088004050040540290310001c0d050600303000301c400243e81c048041c42910100d4a40e031701e50918040c1890f003c60300620343c0c0d580840c01d00140032540c2c004110164503003d4851110002000144100d004252500c4c5850080910881d410400c240100d5100050100d407030440c0321012070113a140410b0500101040d80040c01c6405040c0e070488144079000c841c006201c0d50301d8540950100d2040082d1100c41c901100038201000e041403041507142c4003003005a40180145c00008039022008020311418440210003113512081c031f014042d0211580c43d03501c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 969147248 1250 969145998 969146021
    0x5100e06130e0118110901140304050705030106080a061a22060b07110f242107020d090b04031110030f290102030c071a191d030102090a0b16080d0609 66
    0x1b41480d00c45c6000230510070300c0640ca60094080800440c0400c0010448036025100081c024050240c03100d44460740c40d0f10000d015903e42d0704103000f00c45c0107104200d50070400540509015248400c2c400ca20110842c82ca035034828280e0350395400038803420000301901010f031280d103101d03814440071002c1105601107901110700ca43c03400005002c028441c4400c02000303442c0d42c01c2107038a910046100817448084402c028008044220803c032884e43d000c0b450444803040d6403950b20741c49441d0702c96003001d40079600009101c4000e05903103004601d00006001c06180161401150368407049240c1c0040c7c4011500a20b008201e200c0d281e2401c502050030f03400c40c110203100840c180345102561a0b0340c0da20380d00c906100001c94940003101c84c5046412141c3c1042c0c0c0c40203a814400740c004005140389441d04400e00c1c00d23045e141c011349491806000321740390420001c2c850000355061004140c0964410691040c41c030ad005803516000071503100117010301401c0030000144052400301240241c1c0c8041c1c044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 969148498 1250 969147248 969147281
    0x9061401180509130f080702211f02160309060206090c0f04050c0405031e060709030f0318050a030308010906061e0f02011e09050705100e06130e0118 66
    0x1030001d001c8010764084100c44040320750042075241c42203407092540d148000900100c00d540d0503642030003540300082103510310035075079034603103c0718419078200c541c9200404801d507401c1000d0003486c19403a04000105102c80d003200618140c451507103800e08403000c14048002c1810344004002964060000ca43e00c040420060540c2070801c10020340e140e10542041d51041c0e07a94800301e03502c94010800c0d50007400300541256156070034241800d07010a1590120b0155214440000711107a2046466404032a88452010000d8240341d4080d04d0000d55120708401150889400044ad44c0c0ca02e9011002140a85c89400d015411b00780010281d81058008200340706103220072291f01c0380180b1845841d24028a42402c0090034120101d000d0140740e4000c007003448100e8001d140d000002d9001c00d0506100f90700712105a130303441d020301400c2d01c440d800090204868085000700c60030004020081c4840c0c0c80001c41c16240c0b82e034000d800305603003a00f2550b0300d00359400046404000c0c0340f04022001c28078100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 969149748 1250 969148498 969148517
    0xc020909030f0715060b2a0d05091c020a1814010302030705130b1915170a1116060c021009020f04020901030b1002030331030e0d050709061401 63
    0x1c0c02150b900c01c002c40102030049046407441d50316a540d2012020381a0801c03a03d65030241c52607140c2c0d40780c3d21030110301101001d000401001a50028040b403070460b19485050500091108101c008980d2461501044d1850021480141e952440350400740414444414880380c0903c1c0030030840c1c40607440003510f0b054100043c4096034000403910101c0c5c104558005400400c640d800b009040100392168100007502d5a66407a07130b801401040581e540d0300c00c01c0c66242d8045c0b0b1300b210300c5001c401006c40801c0b8800007103150041290002007102d4442c004080c0b8040c10744410b5656806010802c0e14200c4d5203114200c0e01644c180280b4242c50140b032410b0081040940001d00a52115001d0380d200b81da000405c003640d40d0007600300314886d00b001050b181051126079406901c0754001c6611200c07800d941c10031450813a4039059030305a000544c00300b444180c1103950302504eaa40d18120704d96030181059040b0000100b0030000480581020600810300328540703180004541d0300c3c0318101d41841072a04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 969150998 1250 969149748 969149767
    0x20705060306060a171311010302180603090a170403020102061317030a090807050a06110c03071101030209060a1110050f0f040c08030a0804140a1e0516060c02090903 73
    0x1810780350070500850f00655100c6101c441039032000007440703503180110711410802c542d2209030308051074000e004d0340c901e400541d841c40044040340306100f40c401a112540301030484a04000020b13681c0011043c1c100c402d945019219101c0c254103a130101c0346c0a200000c1d040c411035034113009054012003880c010407104801691181c0c00a02d001d4907101d119040400050640d0005030003960b040e58000d2802c503070b9007000e81805901c6041080381541c805052603001e0350020071400071610003c104401560410004da512041d6080c0711780b0301141019005d00240c844c5a8440340202600115522000240da00b003505050428038008aa000924500820841e9801c1e590441a900c0305d2076082c00400c076034a51401e4500441d05401c50340640c4808503102d0081508400340c40d000d43c0c0600c200c07800c0e10003c40d4030341e9910366107004020161440f540d82661680d403180c0c10900054400c6040e0b4100f88010221025036086660050000030205c40c1c01c8025400c2c02c0390520b1700705c03000070091403a149154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 969152248 1250 969150998 969151009
    0x41e14040f030507030c0c08250b0d0b040f050c03010f05030d08070e01090b18090105031207080d0204050907030b10080105150a030e0d081914010b0912060906070906020705 76
    0x403080a003e01200060a00c10180704014840d00d0543c06101060055210a80386d9078505044074482030b00328000c1c142d07294072142c1c480d11720104d0303c14812140c68032161510640240130302910542c1c106407a4004030001c8a000d0007007a118420505581703442c4e602d040d00800f075040c00766004038041d822a8021b4091207600c4600c46a000c6000c0c1891100c0134065001241c0100003a804102e01d2440030801301c0c40d01d401c402c5c1d265680a000c07540c103070300c50340c0b12000c04d501e0b080c0401101561800030000203000950040260410500000c00141066640c00114201c102c01722015130010b590344c07040d0152441e2120b04528800000e03d40040d5960414001c00c0030a65010b401d020036441c041070b00904d440c440c0c2c01101441c2001000e4a501645521010b400c0307503016121041c2a60828a034040c624401e8402c451002c880ba20038045103910f481d42e43c8204d1740c824100c454000f032150140045030181000702c43c0c000c3c0e407400010070580ca4080002807020305181c00010441d00101c2e010400359a60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 969153498 1250 969152248 969152273
    0x6051602060a0507061b020706020c130e1608070e0106030209030601180f06090b0306060118060c0201120c08180a03020a14030c0a0f06060b04061b0809041e1404 71
    0x161401c0d9510141c0c500c0c151040d008544c0c005001d14106402c5c0c0c1450221402810100c1011703400322442d054827008141e032102442c15803903030002000c100896440c1c015800500b01c20510400f5183d030a680303290517500d040f25603040118280e0150b40304000000105a016005080d280f030b0440c100000c48000075256030040c4200819818100340c407000c40750b030301e9004032244550703100100310b1555201c0040c1c014102442d500c500ca4000c000014180d94041d100d8030640740c600041c1d40107144d084c56800c1e01d4035480604240c0c100140700c01c1e00345401e402032003107180713901107511201c0d910300e02021307480151481c5113900c0c0340d030741c004140e4080001c1d00003408242141c0c1c040050030080340800d03c924a98000c0802c48501841405101024000c403800c030469480c0c0100d000740030342e030744926401407a88164440c102c0003514a20f1b012031840a28441c034881c03248580c031440d10f8600d060303000a040e640c1c100070400d11030012103200d11009400d0f205160b29800d1009000e0090320701034645007070340d061 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 969154748 1250 969153498 969153503
    0xe030d0615034a0c040b0d05061605070c031b0b090102070b0708220614030106080403050a3b0f03033c180a050a09090c050409120801060516 62
    0x1240b0b40c002c08007419120350421414012520580007020144561354200c5180e80f24095440c1400e0889641091449081220b8102c8020500740d15903440701c042400307035620f201040050510030032000500461032000154042c15200400348006101c0c8202a13026510040d04001c0400252150b40d80100b44003003240c800035102601e51402d820300c011a84582e500303248200c0d080310303540781d0254810102d08042d50f109558040818061100e900440d200a0003424080f625100009000921030002401646941e1414013078819003032403480911645141101c4040c810740c8010b03030422001c005580c00210f82144d1201c00880c01c040400d07180e04c507040049030241c3c046030307130285c600c0303645c00022a0035400702064541c040000c800c40001900a00307400d6035080010440381319986840800c21098500c01042c0d00390042c6410700d0303036004000c031400485510200701d00001b0203a4582c42284d00bc14041c1036102a4542410130040181e8416000003041c00000d002d654002c0d02c1030000c0459803903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 969155998 1250 969154748 969154811
    0x6080f04150b01030e1c0f09080a08091801030606080c0108011a0c070b0d050a1a03100f090b0f070f09060905010e040207081b071a120403030e030d061503 68
    0x66110048005e446182940b0280d44100000d081544042d240000c000c01035a581c0c07120040861070085603008034500c0380304500d50102c520b074000700e01e403803009120388407004148984099840d5140d000d1404240c0c020307106170340d440302c003000440e9042c45100413403102481c0c00003140d8140300c840c5204d00a980d01079240e410010442842e801020030001010307001c2d403580180c44408689010005d40400c03a0708030034090601e950751100310700020344802c540c00c001b409016803040c81000c480c0180700b003194401c181034a9151181c0450000c0200a0040740ea0001c1d4008510b04160042c21540c120707a039000410920f00743c1004580d0744000001c003038840900e002000c4035014030005019014104000d4600840058110481e81401c06a00d0140f442c520644440b6a0354902100040c3c6500d41c00312900d10081110403061024404540d611501c28200010421850f4a4003072440c5c00c0301c9502c00d885980c42409000081220091035030800b1186424002c88406a484c104060324950210358a003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 969157248 1250 969155998 969156011
    0x1d0d020d091e181a040905150703060504091a0c0306100f0309080c0c01090501020c06070b0402060408011b02010b0d0f0b1b0d0603060e060105090615160c06080f0415 73
    0x107040342c0c00c03280d009052069800c2d058105400001e4020409062091110a04e055650f040c1d82058064804a2600180549030b40ca800c2d80402c072030404010300300801c050f941c0c0404142a0755a1260540c080c2c01800d081000803180b01e0480c2c4000005040324940340c00620400906646e407070101c0c2e0f80510145452100c240d0000c0d004c5e000740508078801410b0060203e1421010701e000541c40b00c89200c26a01c41d0459039942006a0700c80202400030340c4c000e0700820202001c10b001840241d080b51016100c24038081e030b1148098211000c804407038031072111558092500540c24000c0c5940c046048030000c0c2c109080c1d07601d11071b0465441c54020b09420721740c00011000ea0220000301d203200c60110201c6da481e01320510000041000340400c558891500700500031003240012450f0623504e01500e06180e40d190902003000d0220480301085a81e941004888816805e2001017003070780344559802030140d401d040025000060060644190043e0341c01004041036102c1203000c108415000c000800c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 969158498 1250 969157248 969157289
    0xe0903070f080c4321020301110a140c0705040c03150e10060201060503030f22030308180109120e030705192d05041a041d0d020d09 58
    0x2140110000c81410340038800d41d180303114005402e00d080c144138403000030340360b0b0010881d645058040001031412090322450248164080e80a204c913190543c49a039851075001070b80001c1c250b600300710b1001c1c0704242c08204a802250050035a40a0b0048034074114104001c1118003552803909200c0c2911071030b110003103003142c24042e0b842108a2880d9410b030014603030325041c01a84401d026604a65031140c490342c0040c04610611074001610300c01000b461400081340040e03440f640141c01d860000e4060b9a442e1101213400d107210034000e500c02e131204c04482c9000001511800321003074501c100399060001480c0004d421202040c000364084c18512100381c4c0b1500030914012151f08400c0d0050b1242486001e200f001040c05000c46a1b0310140c080a2072861407500010010030f01e0070610180204010707c201d2400d07420841d280c0007000d6030b000c88050140001400e5482200c47d20a062001745140c064500c420b20102c01c0404150008060010741490000c185000511a01d030491500807450201c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 969159748 1250 969158498 969158513
    0x2010c02011704060b01080606040e0c030403031e05040c060801061710050307140f010906050d020c0102130306020a0315050105040b13090504050d170c042106020d090c0e0903070f 79
    0x7a0403580c02ca100c4a61510340342400040a441c24801d0119609800203001450200300300c9007580c44a141d196000e80b1558250219600050030850600d910350a0319907901856441140d00b181c2e699901003910708040c181031900c10700680000c0200407000c001801482d800c01c00388403120728014421102c0d5076985001001d2101c85401c07240d0306010f810400580c0d9030b150320010701d10100031165036000c2410b041c01035800956601c07036000811028016600314400660240040140c2c5078005854801980c0195000780444c0d04100d039019030101d2500300741036152051282041407a80c05403c800e09050000e051340c0103e1244091310f15000401c2c4105003546c542a2008002016040c49039080c54030340181c07100940c0d1004000600480c00405992003440300050203008604a100e18081c1441d0920328104c42608648449000d46408000001c04910090018090340c0c0c030002030b40c000d50f1401540044499020325614101d45080c030089550210480350703165031140b100307070307001415113403400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 969160998 1250 969159748 969159767
    0xe100e06010c151113051f0f020a0f14060702011a040e010609061403120418050a0b12061b1908100b03040c0e01120510050c040902211e0402010c0201 66
    0x31006404c140d03004065401c828040c2071140c03210709000c001d1175298000d0012424000070308211007140881d0b1412154000c2c0c8443d60b10414500c142ca4140c44182c8a03c5920001d600d0203d6181085010300e0500a07009e02c0010741249032407000340b050808404001024202210700240f286035541d2001034030352003d500110007050200002c0c0032280d694050310110611040d5060f01030700406e01ca005800c2c00c078104880540710f0701c04400d00d10380c10000c0050002c0c58018822a00c003075903500b080d0502da990419003000c020042d00144032030b182010310140d080b144010344ca040064244402d0400300181c0810386094070f02d5180c021503c0d40c8464441500307401d60342c01164010302c004107010030f0000c141c140b4004e0743c0602154400d10b903620a002c1b8640c0740d8511010f0900e802a508035640300003160802c0381c00c1510901c03007078182916115520100c1e442880100441c581c2526a6080d542c45c8040d5141d20040c1980c00755803d540d20b240c2c2c0c3e540c04000420080c1041502c62100003168000c0d00d254 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 969162248 1250 969160998 969161033
    0xf0f02120a0c0c0b040f06050301080a0803190f05060301150509010b0c07171b0607081e0c030c07051c020321040b04030503030f241e12070e100e06010c 67
    0x403d1400da552090f1400d035030060003504000c0810040215200740180100c1c2c3c100c6003490001e02c4001074503121011740c0d40002d841c0d035280c0203220721001692065401409102d26022100140c5418036074201070031628400d50038684a28040b03420411a669051007a04490b00c0c095825607980c01d1927100c6040a54580040c800b29241c0100d103d6204000140500d4511001e50200051081403040002501941d080102054410032a10400d824991540c501455442c42c046051005044440d8255000300000c00c2a90380412401c1041d13141c81aa00102c604848003005134006940e0046070311031a516105d16640750804a140d450542e4082c211002000c0640c9000d44a5440345885500e9a2080e1003181c4545207100102d41d034a100c0c0c8800784e000d10080c01d503550300c0d0880313001808000d00e003400050015103003590b60451f03151100c460b00346540040d040a01009400c0600701e240010340070f083c1080c43c3e40700300003c0c020284000030560700030409081c0840b20355421b103800e0600c07807400046c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 969163498 1250 969162248 969162263
    0x50913082503050712022a03010b1327030509010c05070312050c010c14190203040306061202130212060d11040c0e03100e060609060604030f0506070f0f02120a0c 71
    0x71181890340c8500a825203c0c410140c02040540d95101242d0b87d0f03c5070a25100c1c811340c030b01c0f0b910840c0850401e00c112880d40150011a50b400400002520003c071418030340d401e6034072040f07450410039000d03140a9804a4940e5007948409180c1c034020158042c1410650601100d1507401f070601a042041000039940028003454001054500604c5900211551074013982062440c0310070502844c0e17461400403c208650b400d1403481f0383d01c4c0c3c6201525840c6481580402c02c03000c400305507540200d0001e40501c8822140341602441800320525076503510400261060041c0380b5242c080c20710703460300680d044236003400303541c418201040807030a484811a40a40f50000741c0700c0854004406213001d5008900380c401c00d50741c04130f002040e541da80314100e0072034110f00c000504500d4a0781486400983c050701070350500e6100c0d922101c0744020080c3c285e485520800411074169072100811404100c40d1078606d8681c024004040d5950040164040752807402165510849100c1d031100c9000d00c1c0c001e442c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 969164748 1250 969163498 969163567
    0x606040905010306321b040902030a09030801050108011202130e0d0309060b03030403020306160c1202030d0506061603030506151201050f030f1b0f0405010b120105091308 75
    0x41c1034009207010400605c0c07181d101440755a04070742038120006501d00d001c101200c25030b15100c0850400c0c00000c1c2c2110003010601011404c420140b010f588280820712001444400c42c2c10081c00540c0141d00c8a4100044280188401007900c40e40e54803156040c3c40b07a8a20743c421900200190034203407040c24151041070100980c055250b00480c1c1d080e40251030400030406c2400130f06440b4071481c04043c1d0183c1c0180c0204010300c00e52075030304054005034a0412007042640c0e8403141590203c0544100507071002c03507412a914a14030901d03400000440b2a01d2410444224141c204100d400c1c0c05014959503600007121900c6680d58201181500c0d2a29036941c0700030350020031700038001e026290081c003468006200904001031020b80d0190140014010010f040c1c000383c0240b00c0301c4420540022240c1072014041e01c4601950740a0046010000d48581311402362111212059100342c0c42850b4a5041c0000c501d28020503400f0190061070999898089000b02c0700c0c54201c00e407102034145283d03034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 969165998 1250 969164748 969164753
    0x7060f12141e0106030501230312040f031707231f0c09080d08270618060907032103060512070302011b0201020d05071a0c0d0b010203030112080306060409050103 71
    0x10450080a403440b000c2c1801d40d80707604044085a2003400390b91003100a4101c00805016600756026021800034200c80400f07034152240184d5400c540d00103410030628160038010446048240341d10708003071a03183e42c2080c541d51201446000000102c196200b4a00e001c4884000c05210742c40d1042c4001010000c00c8880c9110342004240e0388420f000040c10700100800e0440d808180e03032104008683d01c00b00c06447d461491014541c0c42c50030303d2080c2c0300c40e6940003016041404102d10400219080000100d01b003032a17030381407420003401100e1507000954184001114a4256049103046c0d803050841d5140b0444186c0c002e160070740220743c1c00140491500011800061800c0a4a200380c2e030700aa021040f403c48000241c50a4009002d6003141308584201031140380509103403402213000d0b00b484154aa090078020030250b80c002c006003000543c00345840c59a020303208041e5000c3c801949150314107006841a00540a0300404a13480003010501d01d550304429500a88104082000256541d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 969167248 1250 969165998 969166021
    0x22020402031816090b030318040c1101050f070905010f1d030f0f06010602150f060402091c0b01030309050a03150216050610061407020303071713060206011707060f1214 74
    0x4e1150180302ca00341842c81d030050a000c400d6401c0c814a083c0ca011001e192402000080c0550b4a000000c119203524040c480a41c2406014041c0030b42c1540c2c12054140810010f00014140d00440d050000820410510a0b8003460780804800305035640c803480b0b2894000030b802d010907861180c0c058840d042c0210320350500131446a04940c1c198080780c10300500010700c0c0e40506030440e40c0401c14415600010030900382a0010074180e40c00900e48100e00d10710030f110045d00f03070b180c04003928041c0c4840018820581c0003040c0401030b0008941e1480c2c600c0c650303a03901c1c003111065000034140d981c000c1040d0300c42c98006900781442d26400020b60781e2600d400d810a006000c0c0c94818080010118002003850000c080e080311140b42e0060b02030341c42d056090b2501050341c1d01c1c0c103510005d1140700708002c01003200c203400c4c050040d00240d8007034070003940740c40c031482a03e002c241075483d65500014030401000b47c00180701341a162260404680c0700080381000001005c90390790326400c001c00c1100308050306003c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 969168498 1250 969167248 969167293
    0x50f090720071710060518041113020702040e120d09050a050d1110020405100e0d05030c0a020108101d0a0f1d010e011b0507050c030f15220204020318 66
    0x140781c100d4113020500130384081950f0361881020f40080000b03c20030a204000a12580e000340509504442d40301c0010210301060510030210740340c0d550200c1d0001c210f1500340611120004000d008004120440401e0145880b8600c2c10100a5903203024040030080d05000c2d42185c181c2250a82e0401141c0703200107070072078904042802c030074019a614190703c8002403081c0d0f0309850000d82201500321200c10281c0c0c0c6041e100740100e0384010384615031000520200300a12000160b0030180c80200d4040c03002402034031002d410f41c8590342c8202e401f030200e0411000b150041c4900300508049546422080310020103070807124905040c101b400e28404c80c0c0030600040c0030080204020032807800807140d014201c8003d0003a5a144110400c40c0102451152014100c007a0141040d2a02e0295150020740390180030003404c00260030402040001038000e005095004c0b058000348a503002d459040901c94400c2610024071481d8040081207030a8601e0762210080c4a20104403882e944d42c540044200c6d441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 969169748 1250 969168498 969168539
    0xa0b0903011a1c240b240d0e250501120908030a0b011e0201050103021309240f02040305061f03050303061e03240a0c0c060207060b030312060307050f09072007 70
    0x90000d0100740d0f400494031501c1c02c3c06428520700b1f05000074107032140060580c9020b04091f034030860886410784000d0612aa101c81d40b0180c040141c0c80ca883c001410303100305004101100303890850f000b804111903d00312544000c49800000e00340d58040e00590366000c01001c1e140c0741d2031418030900c075a00d0b0154442c41c140e81c001c681a580b40d40d80c01020200380c0e03910030320040039441ca88061a41080d0314907034182d15007e0f13015007c100f401c004540d28040703802561003a24903030b002c0703414850051144840c0400f0f503001081245009425500e400c4c3c1c1d40c0c84040c1403140a44907138082403030a01c2e64202c00c411101001825114010a40e250681c00d180704040103c1c1400ba1030b00104980742054450701d4011215910790044424590300d691009401020050b652184c8840260103103a070148002d203030070540346085081e2824080c0c14145491703080d820840c080c20a64038032820664450032250b500800c00d281c001007031a0300c0031032620080005050807020b4400c00750045840c11200c10095030300c0c013 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 969170998 1250 969169748 969169759
    0xb1c050a0c09060f0e0402030d08090c0411030105150f16061e020d14060d020906060c010203010602030417030a080f060f04060b091807080f04110a0b0903011a1c240b 73
    0x1d451780f180301c42034002514000d502d40d20880100d01040d0041441c241d011503440143e03400c3d4004100030901b51503d0b1441c00b02c80b404000300501003460000c1503106c0006000c2001401c1407405c03280d00c2c00505c6040c2249481c0b52610300c0d03000402c0030540214034a840741c6401c8551041380c04a40501070742180540401c514105082503160f0604003080c284204401014110341c030320a034003403081c1c0e071202500c50350300410204465814088240029802007910781e000f583e4441c50b0210280e0204462441c2c0c5600d5042081306d6801a60711440c80c54028110b240d8010540c1c641c0800129102c2c200b408841c0c103e810481c00082481d680c0d0090009d45d01309440a01c040c10415980c12803040f41190300d0000301d103d000100d40304d145103030b80c0c0503481407181c3c03510001301c40070b08000b031206411640407030084030340000c2000003414203010780301a03410040361280d815503407500002c1c0c14003039102d42c840c0c0710310110200d1030601a004e00503880304110030302d0a400324001613100d60050180b000900740186d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 969172248 1250 969170998 969171029
    0x30080a0f170f0c0a181214030414010f020a0b0a06050f090609074d0105070f0f03020f0706060f08030c0a0605070c1202010606030f0b1c050a0c0906 65
    0x12050400002e214599160072080240e40c1e00304495290b4001094050130800d603601c1500b8040020b010b0302010b4090810801c080c85914540b801c0c04950801000d09035030818042000030903011100550000024205041c00e15440c6c0001c0f860240024006801c80e54410280480d50449078460303002e4030b100703503004010715010b42c0a1142444040d00c0d410340000d60380b00050140761291141400307864900311a000ca20407040c2c1c04040303000c41010148920307800e160f1621100c200f030003108140030604070003d11252418520142012503d019424140051198100451442541100c2c02811a807880548800f090b050080c024400c03800b071804500162003000c070b03202c0d00000580d0941d0050000610003c0704030360301d0b100941000f42c40541400f041400703c41c0051031807030000c041c003545a030000070721170b1800500a00340c996030102c86640518015286241d91204121180c1d4011648039944641d0140e140507890100140c0003e010034514282c04162005541c11800032078800d1406481c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 969173498 1250 969172248 969172277
    0x110c24090309030303010b130b0a0305061f020607080702031c1508011e020c0109020d11040b09070f03110d0501061e1d09090c0301020a11060f0130080a0f 68
    0x8900c00d188440360f0503441440100710001400c0002c114020440800f40307001661144000545e8001119110100791220104881402d11801c600040060741040310009801c420010307445080181c1004d00700402000001c00903402003046880307032000d21000c56668408103041d8002070040e44500c2c0310402c000b50380040c0d82d0a050003010ba5001d0507a203500744c03030018006488020750100540f64040e54942030703e05c015a544900c0e10140340d01410341c0c4902d010241e010413040b02c440200aa21548170701d070038403529540c40310b0b41107106009401c00164a5024415044d0f41d0701854180c914018102400403800d107500248698007000c0c00200030b155548004004c0c0c58490040c03002000d015604181d0b0f403014070300841d40542000c0c0c914203403402240c0c0c64020a099910451a49020508600c100c8400c0102046440d0380003880e8541c0e80c0565041c800d480c500c602441d091480350318807140c5540d10481d0356607030301030120360b000768981e544607a84075000d00001841d080e000f0208030050154440e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 969174748 1250 969173498 969173503
    0xf041104080d112b0c0f03080f0f0c04090902011206030309030506091f27030305100b030f06011128060b040b011422030507081c0210110c2409 63
    0x78036083c80441001c00d4020105101409000061300380100044c4100260100d0004030011500703030700a40d00c0035600d00e408082c0d0641484090011602c0700290001c05c50042c481505031000d0f101044408501c4814500040b04c0800f444011140e0075031900c0c40c00001c0542102c0d410049074450002c4d1074035030360f0300700c019601d4100c08111040481d441074041b803000c02251f03004c0900040300c01001c40c0e1031450145242141084074034214080b0740c1e11000e1040c100c558142031030082c05c1c041c42207490341c50600d5441d8032596015000e00c2c14030040303004038641c500003481100440c89500001a180560018190422248440c826600640340129183c42418a8042c2000401c011303100c100000b1104070b038143d117030742c8450b8075044800151001914100c1c10800c241c8002c501440c02806078034100000c5038201300d07602001342004111840c14208468001c107600135000b80c0c03d800050030111340f521184041c8250790072244a03004c0c0c01a030145240b610b60750240c562400c2c542d0201d207980c5413001e265 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 969175998 1250 969174748 969174763
    0xe1308040b250c1802040b3103110d08040b0c03090109060f0203070f1407080c040b0f150c0a060c02100e0c0307090f0b060a050d15050f0f041104080d11 67
    0x900100364541c0038005400c0c4008040710a469813080140342c50b98625407130000d600107418842d44c40001c4040c0e0408000c060004164991600085004940c41c655409210102c41c180e190300469178202d84000f480074080a40c0c0007400043e1071035036100a42c0005c15103a6010714142c602103240ca9601003400c61040c004140e00141c11b400851600c0720341d44036910760501415086440c071030384401e100b1291f5002e00400c4006c00480d001040e02001400403c0b0954069010840c041c1048a240c21601da40700307245040c2181022900540e1400b2081e0290708010348070801400b22402c1c01304140c0c0403503001507019030142c440c1c042040081c00c04402552100c18508a86906501010091298000a600508403050403141c0054031101903004601c0a401c25880382c80860390120f0140142a054007a2000c1e0b4810164006009418000001c020070000c00c42d140c0a00301c1d4018515481d145c0ba404200d000c003c8040442c1c0b00c690302c5108659401c1300b403a034040002c4440c0401c83d00c0702400940c82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 969177248 1250 969175998 969176003
    0x1031403070b150a0320010311090105090d0c050a180c0c0b0c13030506010e0f1003050d080613090c0f1a0702040b0d12020106061b0201090e1308040b25 67
    0x80b0703142e207840301d00350140c1a401000d90b500c081d407a000040040e16074040d00b00d003000a0000c0345422100d04001508540c5a6640c04c188480208050b0400b40c0e80001103515405040300d03441d01d032801d5410414502c07241c5c0d4101b0303034100f20b06500210b8111464220b5903500130100105005601c89203c080f0350305203100e40000e0410451a01150000882401407e10301c0d5117002c100000a035079407a4036280080a9000c03a19101144083c801a10010940d450788011990400b2600d01d1642d9103890341d0726440b81e21001002611000700c0c1842d130314001342002241426209001e1307580c2c80d061207130381c52103144200203050b10013003000501d175035240454640f0710b0342c4101c142c2d08203003458007440701a0a80d601072681c00400344401710001040f80821101010040e800015140d0a128000d44170620182498611800c3c0096400050780d012000c0b0064450030100381d080e9407900c030a080d08840d001c0c0d400400d039800104010071400070f864040c1028407240c1e035207804541e5a000c9890980081c48030007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 969178498 1250 969177248 969177263
    0x50c0d0b06070c0501050c030708030c0904061502061323010615170f0408040b07060504110913060b01021009080c1e060a0903020313170606040218010c021f080103140307 75
    0xc2003251b0140d405003003003040b010150391a0460980d20311009500460b040d1a80000101e1038000900703051040101400b0744210441400d0501913000c3e6550100421880400c103180503102d00704680030700b40740d6556a4940c14001402003802045c1d0103061903000d541d94840b013800b0300b0141544101407801d40261902810a501e4031001d000040364880107006a0750a4010000001c0c10f40c003007001400504c0c001d8800168505040c50100160500040c2e80e600ca2800d40301840410885040c210300d901c1e40c40180000d1020035040144c0c03c0240180030640d0741c629011042d801e01c400c1100500d603507102c182c01d440aa0f0444005e546064410b614010300300c0e070210000400c188000e40c0050009400f0340122410121145018041c4095a0308101080048001c04400040c010802c45030803480881d410f5003046540b40c50f090139503034040c040c1070401000810354070564640360082242c1b070740c00207045800d4180310b20000e130011000f0f110890303000c400012200b2041b10301200f95508150b010f40c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 969179748 1250 969178498 969178523
    0xf0a0626070f05090d0c1d06010203042102040b09070302070618052802040501030c0302120c240d020c06100f0303080402040908120921131215050c0d0b0607 69
    0x1048403a60030003e140368005c4464107580c0c0206513068002402031540200e0300340100340c0705240b07070b81c54480901003030b0542d4400e0200f17000d11100700d0603d01682800c4440000001d200b4000600234102107041d96410001c00c8051203042941340c4c0087c10101d0003000b040c82040d60590740040401ea01303840241c000e4010580800004060400241200030084818545421950006001c4502c01c4c0d10480d080380300d0810400460a0440e100c0810340c0202d006461030310005404218100c2c50444a0f00300e13007032102d6026204c0c100f108141c0b581c0c1c50b1306420031520343c03c4408846035180815501c805204145402c0064020014504c00064075410796800d44141c03200d90030300c8050425060100c2c3d80c00c8044c0114041c840d450441c1030b02c103032551030043c580040b010042c101041d859840800d0420340030888031040280c41010541202c1c1010700a02c0f1184850501303c5030b01040d0154004054207210901568410240107007912079149501000614a40780030050f4502c51488000c00b545600c08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 969180998 1250 969179748 969179777
    0xb090129010f020f1009020f010203071112030c060f010501140403050d050313080d0902090105040e060105090901150e0f060915010810080703051b0d020604030807020f0a062607 78
    0x10800202c40d1054011101c803441c04865244c100301d0300b24000808156154142002e500d441c3c0600d840d030034000e00245203000010b0315504040c80d40084114001c090b4410b11101142040085600f40507951003550480e040101c1084030050003880769a00103100c0d2804401c43c050884212400c032940300004002c1c0380b05207d416205904010b00b0400e02d103150540500c0030441c2800241102111010005030034180c910402c244054107070015070080e854014000342d800800500b0505507070b01111802d01ca6920865070034050703e95542c40a0240c800c04c1c00026001140b0b94140d4040d8040601030011a5918401e00402d12000c841001200d644503501100c254058548550040700b0380c0d266400031516a03648624103291540700312220b500052005001d44203140c0d8601003030404440f000da101c40c503500000d000f80118003020701100b900240c65030455407152202603032200c0c0980040b460030f42d15200545407000380240003c1100f5042003070b80403181d80b0000203218100355150340350300907041b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 969182248 1250 969180998 969181007
    0x6050d09021c0524010f031103030d020f0d05010b03130f02030a0b090c0a050d020a0501050f0c06040c050117060a12020103021314120c09010b0c1006030b09012901 72
    0x641040c1c0c0c0140c280c10307042000500b650702d4180014014002803420a840c00190401e18000c401d0b04044204070000500c00060038803d400e00300c9821485414424110900281c214441c0c4220202e0092001521170480c82d040c10182000c83c5501e44104026a40c801000020380310032546498403e11103280030380051620041c11400e0340c00682240d4000c0d07896654045400300030340c0c40c904140d2020318404298036140300810050801560742860400c2c3d0b5501164080c000c1e030141d18180200030810714603040c20901526000b4210100b1110350b410a800d00200740005401050f0004000c1142000414418203040307000d60345c041d0a0341003082c607103108140b581089101c22030401d9000c001500d41401500c504d01c014100082c4508084180c8004100c9100400003910b046a08001c10200440d50303000306290440701424102360390352248650140c207080403140d41a043d185030171404010300100403401d500c00c6543c180200178405a0010a51b500c40e1072040d081c100080599031040554480e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 969183498 1250 969182248 969182261
    0xb03190501180f15200f160b060411040320030a06020403030c0303050f150603060d0b270d020705011b0516061101020f0702131808130b0f03040204090c09060b0301031b06050d 77
    0x1c1b00da82e041090010604100d034078081001d94042941400748600c43c9418420b41107005001841a0318040c55a0707181600c401020300c003c10400c4104103c03907629241400300c103810b168000f80441d5602e859107409000300500c12002d4000901c0e003400105030108100d0700301d005900c1060703c00030280c041c030104650b55000030b00264000701c8441d02c410001e080104100c0c00341074644015200c0c40303044406000840c45038415825540c1c084540d50321900e402040e1802a10383c2031920003d000c50700c07490050010784180e0020090310482c0c640c010310104d0400500c041d1401644c601d00403a41c0f044016082c0d0080c4134103500000d004200c0480103140c2000c0743c04450800010105002c00d0031011000307402c41d540c0040e241d00c0300004800d146e54000c118000040d05803188040c0c1131951140500c2e00700d01005100070b025070340d5a449541801100a9048014240c1040c00d0260a03250801070090790801e2108541d40030071a600170100b060000030703040640e0656035909040001599848014100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 969184748 1250 969183498 969183517
    0xf0303020d060b04141c1b0308040801140a020f090405060f04090b01090f051509130b09010c11010908030601120f060b0c100b03190501180f1520 64
    0x38200400140c26407540160402403521415541c1c540d403410454424104180380260700c586541d5018103100b2004440026500340c2103440c240c150036000c619401442850b400103040e00001240006840c0030541282495a03010005450780d80c917408124002d90113102c01d101441c032428800c68040d810164001c0c0e6000b00700501070303001011200086002c4601411059801e10540790060200c05610300403c9800045000c040002c1e203450a84450030502c00c2034021b00c11016480172610403600c500180f4503c942103024004a414004a014000c000d010f216a010481c244030755a207049061241e41c100e0f94102c07170094035507581e01004445c6c28000c800311341f280c1a940c6031a090024080d10a00c0c3c050481c4650310b80d6200f40b0480b605103800420061310300070906101500300c19480c08118142b1b80c048180300b41114010310b2410740e0150948100312001c7c0700047c0520018062610301d04045140107040742c84050000010346400e81b040c1609804080d018000d1403502c4c15003a8008101e800c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 969185998 1250 969184748 969184751
    0x4120315050406060906020706180303030b032b0e030109080a2609030706110307020d1d12070f061107140103270b07050703140306120d0810061b0f0303 67
    0xd03141c4001508440322130f00040b00042d24071900348012501044940f010303140c2c070300f0070b040b1041c4100f90200d445031007400b0040070581c0f1508121040e45003084007a100c075001030310446030382c038003002200c000105003c1c8000000300c44152500301d90406106080009400a0307000d85480d501c00740a1301c0062442001c0c0760001032003001c0250072426988002d000c0c030050b80c0555a56051820040305030b0b0400722208664907003c105102d00e1307640000386001c42494500700350fa074940c200e40c9a8442031080f908140d03009551084005003601c0701003234031000e60307030046442d854413030f00c0d4203003200c8950580012a0096000714000d02129603015080e8103429014500482d004501da800110320a2898125891018400d8003003c100001c0c09030281d84003540380307042810140c580c0c078010400000c07280250440031002010885648505580e0b811900601c0101d0f04140740611004004001c100c1e9245090604d8141c081507003407182f880c1020241004042421401c01900c0d00009440203560880500d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 969187248 1250 969185998 969186041
    0x18170c03060411100e030616051e190207050306010b16080a051803010b0f0618180907050a05011e021c0504030204060506031b070303020405060708030717041203 71
    0x1503804011061146100300f00d00d400c0005070400340701c3d688141149040c184001081d0b0011140c60010f02070303510110700518051001c1c114a8165040d10850092000041074440c85001400915000700401e45541c5a40801c410200728220b881d12000d0090a9041d00880010010b48860303002403e02d508100481d0380180e2400c0d6611112030303200c0000500800c0010422b03618403035074124000d030101c42c2540244903001c880d5000034500503052061a21404010410340c0e0100307503400349241009030160001d480c0c0075a01843e40000402201d08910a104440c008501c909020a100d1304403032040e10b5401c2e900d070504039130000021114046008510501480c003450785140d0806500440c00c680b145075446085005003c159500354003c00d00624042080c8200c1e208400d00c618091000403c0039601c621803480c04501a11a5520031540000041000401e21421030300640c0181550b0b12604221410898160b40301342003281c025160701c201c00d118000e1540030f6000480548002e41c100f1114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 969188498 1250 969187248 969187273
    0x40515160c05010f020a1101140d05070503040c0b0906040303030c0507050a0b0603070914010302120a06050a020301090b0f0f0603060f091303140f0702060d06031a04050d1817 77
    0x840202602036641e00c4003510100183d5030070890401000340389102402c00d4101503100c01c65902801c3c95901d040201c0301158018855042042d6801d00120040030700140c14851001011504241c6044e01da855116100181d909034860841320100d001419090501d440c41c1c03410380090140f440c4003010300c04200034210000d8014800306c20f0540c4215049510360412100381032402c40e454203d041c102d46062504019201c500c903241d41129811550416030b42020700d0624100101110010807144c100000c0c0103e105264024605031442c0100800080c1008010004a00c8a0b0f43d241d507040585070034100364906054008541c450b001820003114a1120b9020494804c82160003194811180302e0540806501003182002c0b041034000240c181034140000094600c24140001d00c079200002d100001508141c2107000155001801c2140791207c801c2d200182c400c04440444840c0200c0000b400c16900452941ea400000d5151951880d03041a984080900007910201c140b44503d4144440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 969189748 1250 969188498 969188527
    0x5060a09050412140c0604140304080d0f021c0e0d020f10020114090c220b060708090301060f06230426061302130b04090512090109050604030206040515 67
    0x483c882c1d60308180c03103400e440740100000144c94150300d48110422030007240b05000a6119081504010b40203115690700700c681d440c40c410755201c0c0641d8011100d2174050290441c00f8044841116000d45010805841310341000c14100050140407402c1d900349107034142000c88086145c0381c400ba0404c40046803500005403000d13081000c1c030b13005039190407050302410310200e00c2c141c01583c450000c00060f0303176043c0010030003680c0c5803c114030b48480303202e4402000295045080c0e80e20014081c00c0d692019410541709503406560703000c0c000c0d0301303040d000910381c8156200c6008980c91592800d0100407400c40c118211880c0c800d101c06600800d010100f010480c901d40416042c411a0100c800c5021080003e814508000c06541d241802030360488003584a00c1d0031040a10283c0f10b0005900900100003001032010580260140c80303141801c480194001000b880c0f40711090300c401c400341c1d0b6107004001d002e00c614040250000400e0104120f43c7c00c0c030040381c0011102d01c0f42d5007420a524140000b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 969190998 1250 969189748 969189751
    0xa02031e131b0501020a08070507030204181b181e022b060305030a05030901091403031e0108071401050409091217040201080117030d0212090115030b070305060a0905 73
    0x4142041826110307080000041c205102e100900030261050741c80c0100103501e07503503e890040d02d088030014130301003003150a01c4140080c41e07000708104012540e00c0640c9200c003040b100c04a580b0300c0c0d0000340c4041c20120500c00d40858403030668181c40140000c1120340900801540d40f00b4075074031040c1c07100c123800c49400a0222802c2150290f9002c1c00300d407514641940888801c43d20795480c0840c1032000c11404000c544000001e4100340b952034480c094003d00400300014041c00744131032042103151300c840c04801140118425001d002c04c801c203240c80e0303007541c1c1001c0c490301ca0329600210080142c040c81c83c43c16203070320328141000b6050279501d0b80703620140c8800d20380894490b1a01c4140e42c900c150408105a2066187c0c03d444103549420f5001804000060265600781c107010107a20003110010001c5408440c815041035498440144141d0181c00041c8d82d00c0d0b04c03e50810900b11704102e04100340d4000c80390013494030384150701d8210096004002c0078188541088140d20045411190341c080d05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 969192248 1250 969190998 969191011
    0x11a0c06010b0306010311030c0403030c21020d09172109100e090a140a0b03100908030103050f0a0803070f050405040c2115090b0f0a03030918140a02031e 68
    0x110b0b0380c0c4c64071100040807100c075410510541031090041c020542c1844042e00d05581d410b0034490405030042c100060030441c1800e031684c820001d502c041400720fa000c554845003c8094445070049515441d03203412402891404030704551188003184512804070b85001d401101003a110f42c60610060040340071429690414008526103803c155041d04040d0706040e401080a0b0080064440143c3e90300e00c00c1c60080d10000441303480f04214902954180124142c20b00128001c104042542c502841d054000748015a900d00401404440042020400300e4010394003402503403540da6032500c00c0c0c94444145060a003080703030034007000c04e00d0345031407003183d0501d009038590020a4225110182208400060303078200320781445c4000c0020301c0b0f8441c2c0c010682d0601640031801c14013207804075001000c003e0b001c070740c0028404400002c0c150400c004070113a8405840300780c24101c269214030103484510031070b1030403560220001581250036501a5800c00c10ba900004104600046041d0f8002030a8441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 969193498 1250 969192248 969192269
    0x4060806090609060c0a050a2a060612030e0d05160e0a0c0e060904230c090319020a050f0315180708070e0109021e04030c0905060117011a0c0601 64
    0x1446034003078007040129807050400700100700d180f0b80304528a18600892041c40180500842ca03008a54090320030001c9a03554040311600b01c07070052181110700c1620040940d03030a490700c00007003800c100303020382c007406560151103509610a101c414002035014a5400b82e0396070040245102e0006d00c0c8a2045000b404038401141306070402e804100201c0f0509119082400540702d0f2152041e04c1d4041540e1744000200c0300014000c01c1c0a000b800b1046000d0030620215002804000442c44c54001405d440001681160114052122a0900d0074000c4401070351018010600300518980103070920a4080050701741c1d41412840c00040d6213142c4184c4030070100c40c19180e0040341c2401c0800c00300000780219001040010310f0405540c1e031101040c01001c0d0380d6500020408000d00c040360490b4940c0c021001041d540301c0d039a0810b000c400001d406011061418400070070100c0d072041c4140c00c102e08a80b980c00c40141d10b050161901303a864a10843d058120034040501c900384140f116a00034401a0003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 969194748 1250 969193498 969193501
    0xc0816080702040c110703061e09050106150f0c08030601090b030f0f060f130c05040503030403030801061d1807030b0301090623193812030a020c0105071104060806 72
    0x401c410303203141301c43d403800b0840420b1626144490005012048070b07001840017400c06808828100340741d15100b0f140404904008480c070030010b055024008807424089203031070490401c5d1b003c071b48001f19102102d00091403c0c4107200801e441d0001180c01000c141000380c0e03007594031002d0440941040b500c403099020a801001104101c01791140d91102084550f400c81082500000e4081102c10307103c25003840d91541003903e403a018008940103040000e0489031102e9591400900b4030600b4040d540000e02d414032004e41c855030310507405030300050061110700e03c941102100c28400400034001303c01c06d9114030811407551003e10507042d08501900b00820309054240a22294404444240d5002c10100042005000c0402c40c1d440c1090f140260120780c00120301141e4a90f00c40501081d51619440d00c1803681c1c2c1c018070300300c0030700d016016a0410501c500f0362030256101c0c010341c602500540c1000e203803103c0f20741c4100000c1c42c0d6240b2900c2c98201c0c20346141d01180880706180c0240d0750303c0c1d10a10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 969195998 1250 969194748 969194753
    0x209060418090b0a1401080c030a060504021206180d0c020105070b09071806080105061c031b1703060f0307060504060f1b1412030115201501150e0d030c08160807 71
    0x4200e10302504120300244403034600f400210307680c0c0e02000c5014282cbc65031a80070a04664904003d4891110081e0480700103090179403a4410b4411025019006071140340d841452700ca004101116000d50161209820624240c4a00e1070070704005000303289034020a83e010400ea007901c61b403010021098507000440b14184058107085510107000c0510899159140d800049030220b8504a20b5602d440c2c40820000c1d081c1601100725181c101c02003043d072802140282e0090100042c62180400300e84401c480540b4a042c56201e007803d01946000a404000501202d400b410200396090002d2030725500c803048202100540c000300e940c040b20724400000725034882107006c0041c161a00700f4403007402d145524214011102d00c20089103201030100301849480f07001c4502c18001460780428082d665454540940c6d1841c4910034060040901c25014284411512452644421443c090113240012606841c10303110b0b0507690a04480d4600d0800c99051044e140045c400400c900c50060141c84010301c0c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 969197248 1250 969195998 969196031
    0x3050408071202091b0708030c0a08010b0a1403130507031505100b040303202409030a020318060912010b01120912080a0b03011a0a090209060418090b0a 67
    0x190710010300b1944036840d5102580d10301039029002100c03100b0800c40b400c6080200492802a82e001511032440441049000900200181036144290391440b40903030302d4000724140f50040341d1030003000400d140d04c0c0ca21441801c0c070046400010590aa90310381d00d803035480d50701e44000c40c0c00884078007070450011100313242c09000719500b111258072810022402c1040c22901409070344805801c209501040b800b92042044904039000c03103207400e9800071015800b0416650b082d0a0301810000140070000380c401c0c0020054801d6117003a54040c600c2c009000d602241749102030403600ea0702c2003082100c50a40d80e02d401c6516819110040003161015540001500039031448072800786881c10101a07200054940c40e5006100703580381000c2085480348600c002c02080304400303c5415610346001c005070140413400c00d82103010121101c2c068581c613900841c1c04d90154849168005409010900a22400c1c16203504603881900c00007400007080d40300c14161385419200446000d60b9440310410301c1510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 969198498 1250 969197248 969197263
    0x40b121002120601090810020f0417060609070201020c031b07150906020d090501080103060203070c0213090204050a0605150c0f060a0b0103150605090f030c0301090b06010f08060f0d08090d03050408 87
    0xb401e10405c0c00d85006181034680071808401031a01e07500040c04890020400241c0340a811003039000c3c120400c01240c1039513900d0065481c64480c0a00c64005807010348140210b0300030358072840146080c5074011100c1c1003040d00c00b8449259a004040011a0f06510f034601e483c0c03d05140c0c2e440175103191814001034100202d50500e17404005200300240b2036640c209401074112544094016925502c5d07a0003203441d840010b41c0203500485640b500791000c0e282e84c00a48071203008480410881e184d440d6804120b960307038030403950440b01207401e410240e00c40101070801c0b4041c040c00da60282c50300d0700c90036040072000c8592505950361403840700c0f080e59052107544c00615a00060301c801c0b0f81450805400e07409a1130780f851141c5040b8543d42010713203061122040d4034402900a00074400b10380760801c06110211040c1c0e000600c20090401071a100c0e000d064098240a000b04140b50540c40600c90342d1110141c041d00c8010040000c0556a150722004002c0c1600039550ba580b01e0381082c2c0c07010f0034082c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 969199748 1250 969198498 969198511
    0x106051801060c0b1518071218141203070306030b0f090c090702030c0307051b1804020f010c02030a0b0f150f0409020d02030a0f05010c0306060e040b12100212 70
    0x140e120050042c15000802240100d401401a1540ea6100e4640c051071002c2503e1182c1c02032003201443c08070354442107846000d032400362640500d9010b00345c0144100c41e50404201c031145442024a4003003100c175882202d04400c60801d6030881400100d02c04c4040d0310a40d02d80000a644880c10020b00811080050b0062a07442c00d256440c24000511a540d50201038410b1180740c50f440851030103402007089421500401d0300b034a403131701864101541c9428081c03449000400142d030a02c10b552030601c1b50b2940b50f103229407041e400c644464090111620340d0304019414808021178400169404100480c10b4501c10042c0703241c5458120400215560050258400c0302c3e4001400c0d01a5510700c4c01285050702c040e01c00040400d02c1d400040e4885901c10342c040c8d054021a0002000d00140c0115051103074000c030000e0000e0f849642c42102141d81912030240010036400161000e40b6064100b800e080f0b03401003010020101090051781030802800c0d000103900c0d40061a01803908048a46651048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 969200998 1250 969199748 969199789
    0xa2321270117180d0302090a08011104092304050c130204060f121d0d031103012105101118030601030506040318080a0f030314011a0706060b0c010605 66
    0x1499100180c004100d40c12400b50780840c01000401c2044048000e40407040440c04407480b07600e051001070001d60000228034000c05c054480829030510501a01088081225100d481c00d450203409130002d0410000c024011203850b182c0d001c030041c4881e803c500450154002d82950503e00c800c000b1601130002480d20010b0041c4010004e50750064b000464805881c02e01100b40085040341c1801400208040d0070010a10714905000742e40000d640780112100c0d0b101004281c1c406807640000c1d00003480b4a500203c1c03d200da82c41c840b0098002c102c1c3d2a8403803011902050900841c41007640c0100c00200050640442c42d003901c900191005415148103502030710265045881d00b907242c407002003001d020320a0301c1c1c020140f100310341101d01e8010007d580580c1c090690381d2030148c9200e00d0f0520254006800c000400142c14503403072800e4100c48107404255a2030240f000340100d1500050815110f040c1d55845c00035041006034000c0a5104661000280e42820300c03041080b4046039800d05030121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 969202248 1250 969200998 969201067
    0x9080c011d060708090307030c061101020309060106050c1c2313141c0b010501091e06030b010e06031906120f0201030f0e0a03080a0e0a2321 62
    0x41d202105494000c40d0199000395035042c250400614078411801c065806220301c0304004240b00303081da68071051b40d440c0c2c0d4420308481c5080744058242d01007919002002e42003a00104102030050300100795098941050f02d54462400308500c580350400e44440000c242d80680c0c40010074510004e07000d5844c080031486040a03407040c4007030410401402002042c1a2240c041103d6550f06106000300780d240320f4241c040900b20340380080b203009080c8202404074006110105031814103403011135003070004038003059406d07141038800ca019120300c0809a061003110150281562116070085100700300c2c5002c00c051501104110034100c0303d443c0e12901940d4401e00c50b5030000f0b104030124600b801e07024a000304202c41501800d034001c2c80f900fa61480e491055081d14000c05400c425554030032124200b04002603641d070a0001e858414109004000b4001e020103484c2e42c0311030b1034109907542948000c840982056401429840748046060710404001007a04075480032442c6540e003200a1407a10031610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 969203498 1250 969202248 969202277
    0x90914012c04080703180305030c1506031c030615090302030c1009090506030c060313110111210c0102070c03060b010f0e060a0e090a060614030f041202070f0609080c01 74
    0x140c0e6406807009020f8400000e809084c1440f813a0303060500d01120f43c2e40300c841941c9140450b92917005483c1c5a65600070514407005040f4103110081c89124040c02408443c0358280031502e681502090301014541d44440c00300300111402c0c900040d00b05c49407617035000d485c2180100b515041800491500c6041c1c20003562080a9112080342c0440d194050040380c19124540002e00303082e0304040554200001200700a802402c0e41e03441c40510307000c3c01ca1038031500c0040d001100d0194030300010610079482030055119502c040d00c8401c90b02f070071012209040441c1d0651071420f80c1d0010005440d01044e02c1014030a01134544182e40041c202400e0212864500c10406440f03100c3c42d400003440341001084640310240510142000942e009101010b10300d0700d001d801c402000280221800200703c805406a504804c0f02200e018403c022080042d0340d50356038071f20402c4505c0100b88411800742c0280041d4100c0080d0701d14010741496100e210a103801d1004c8146010034550109040143e01000c4125 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 969204748 1250 969203498 969203579
    0x703031b0c081506090604111e0705070f051822060b0316090b011b020409030c0c0308030103111c060b0a050a080a0507050907020c09060109091401 65
    0x100c04040c404814a401228105280200400ea002c5001e5000d400d046066624600c240648112800c51304503030035480344002d1004039102d44000040004c07040040c0c0b0880c0041f00341004400c444908a2481c00c990b0343d403500c1c2414499070100545d902ca92209109500d0a005080c0008400e02d01008030ba16140030b0f8a0030081101e4003421082e44441002d40c00d00c0000c2c1c0000c52240009000c4981324181c00030445211501480b0700007203a0303d0005209501d62088a10040c07a100d80c1e248940406603039020840240044103040b014400418155800222406a0400114041d03a0015101e6145040c050220501d038107100e4824010091525691405c0484c1c0c1061260440000034a02c450800400c240341d010f41c0026501c16000c0c03030002032424000a02200e100d11074000d4407580d035960700c03e10041c01e6007542d010016801c040e20058260600c0440d10740e110f9014984240002da82d8035020341103400340f40001002c901c0500c01032281030000781104402021034061794403403a1801e4203005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 969205998 1250 969204748 969204767
    0xc060a3204020d0501020a0c0204151a0f4806070c080d020706022805030408031905132a03080313060212160c0804050108070c060f0b090108070303 65
    0x101060344060114095448103d0b0409259901400841d52041c20340c1c000303480400c0d5801d0032881503051621001b08040980000c10894900c1c0b14220242e11380c0c951102c8aa40001d0b00c1c1081c80074040c00084008a2170809540711041d40d0f04d1035521740c916200248401650141c4285c1c205004a40710b22841c110010f0b03d194090b240d45081c0c1d0400c0140d1811818905c1800c00004d0390600210788681440301319401401d24801d52144444150441603204030115403003202c42d004242c0510005011555200c000c42d806441c4041032184250301040160031030b0400c4d210303c4000d10701c01250b041000302e01962408484001840e0040e4407043c048509420049400000c040000c04008900780740d100c003030069803040d4030900075500c2d4442c8410b9042058000c851a064078007164003c00238450003240c0c3c045403641c0088041c0d14060405005645819014000c002000700f001346a03804103005200b284100802010b01180342d12043c41005422001038000d0991030b0090842040003942140d4002d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 969207248 1250 969205998 969206081
    0x1021050c0702040c030605041a1206010b0a0c0312060929031b040b0a0312090b0309100207030c0204090c060306241112071505070c02092404020c060a 66
    0x324040004c040102c0c003405a0b0740c032040e002420520ba140f1410340400f079406013170780140d40c8140082e11201800303130b49010030312a08030150301c10418841014454a07071a8a0b490103410480003e1010080070000c030b5889a220003829030b640c1441d1000800d000c1901102ca6040c400c4c0d4000c100355000c0020b84415042140006a880c20b10301030241d5261034000c62240320300200754001003507a078244295040208000c100c00520038800108120040d002643e0180907140c00406c11091001030329002944a40e0041c1c09220f803408144005076a80d009100c0c00034490b00b070001d0810f10f03051000d030a6504c00d4103c40740c020341108025000c15000891080340480502d0060320405421a2376814480e1525040818140000313400c001e200381c02e0410740302a00c180000708802d40d1007680446031900000802548a646040408c004008051240d103074045d403100e01c5032a0225441c000307822640306165078512600300c0c40c1001910189842078124140700240c04456142081146014264202901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 969208498 1250 969207248 969207251
    0x10626070918080d230403050712120e0a03080109060e2d040606080c010806060a08270a0c0f0b1b1e060f090729091021050c070204 58
    0x42040c020410340300118000c1c1c01c9809156680c01040183d00a1300101c204909070492240c100f0100c6400040311606c0b5940607a18035040844d0313540c81c0c07503149485600d0f9a0810031030b0814072514a109200d2031002c03501030f030000e21090000b480c01606c50441603010030000703460280704000001c0b0081007168409202e00700180300c204186013407030f00c1100702c520302c0f80c078000600200020800f20f039103c0c5d400c0e10211400c40d140d90742e00320011a841c034004c440b0940c1020050014005031401544070381d40105d0b061001340240d560f9002c4450707072034001c183e001820758040d040c20001d0001211814003d81691000c107251681401703002c001070b119460f070f041d04404061104049116081c03001070f0f08404132100d0f000d0031a4042098036510f150036118001d40150280101b0b00407a40010a58102c0b00e00884100b1030f000b003920f0720f046140c003203241d10f2982d5004001715442941c540080c031408001c0b80c0c075050110b5117001e40c070112000000d49407a024502c0e08083c8441c00c5400710586040c258115030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 969209748 1250 969208498 969208511
    0x100c0810080f1e03160b010807050402031b0705070b0f07150c091e030f080c2406010c0507050414070f0201060b030c2104120e2d210106260709 63
    0x3c60386103106030f04595907180c2000801200b040307030801c1c505048806210807160000d44071000c000803403100b41c1d44403804218040044101049440241010f02e000b00280c0d0211aa40e070006102c1e42d01549010174404400561070b004c1064000140070510300700b41041002c4402d51601a100700c071f050240d425482c0700d800c09440c920158244000c081e5601400c0f000c114000b07403416000541154580d00c005014800707031050400803103c00342e540c490000940082d19140c0308010b45641d002c80d44203862600925002182603125400380032080c80d408100300304c00340b2700701c0c04c01401c02d0010700c00c1c7d40071641010020850380b8440c50a40c0d4000c3c18112007960361b03502ea0b5030a1070429802929241c00e01319584100410300100b4801d840c00d001c91070701c4034800342800c61b00304820340003a21602403502c2c0e84c60700d914603041e11448001c100300c100504040e002c1400b000400440c55120041c000517691155018003c403a020041941129a60480c00f07454014204100d40c03204007501400850a95a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 969210998 1250 969209748 969209803
    0x103020f0d061508010509040f140f0303040f140f030a03020a111f050604021608070602070c140f2215050a030812010503060405150405100c0810080f 66
    0x48592078140c0140c108103690f030724880420b08200c00810580841c070102c00020300b90130a100c2051050303030b0000d860310401945650b91002e20240c001924501e214a801084261004000450045001e440e442c200032000b031400c0c20010952000d0003070150021300a4003a81c1d14000b00b52802c0d14014240940c641d05141d9046412059070342030802c26100e40c007010320310743d1014912078400e5682140140095610b00e8140800e0b845116100303103810241600306408a1481000740170101e100c0c4c640585090700c0d9483c1c605072602039030032014401c010302c48101c00a01d041400d0034050101501c1c040c1c415541418101031502c100e002202003141c450040b110071800034162003001c0c0400801109250740c5904203041303150801035400845145c1500041510301e800607040381f141d0351207070041c201d40c0c45041c0c0350130b00700c5400380040340c0c03900ca080074410180b420f501810b41000360320780c1c03050a98a003820b0415101429540b080e1031903049400501504640400c100350600981c5240746102182d80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 969212248 1250 969210998 969211027
    0x2030a0305061503131104181e020a1d010e060604050108041a0c1b07080a080a03020403020603010608070e01032007030512270c0d03030b04020d0905060a0c02010b090402010302 78
    0x2c0c1c4a1010700000204001d04030a03800501c401701406141c514480150803c1448121040103120403a0f680703d4500e440300044004411840341e4040b116003410300440d6501140d48400b0701d400c0150b03645869013603e89101d0011a45600600141101c040706040c140082403462142d401154100105040081c042c07002c8043c81c8040c0d020000210001480d0000aa001503000078419509000c40d049052190060004040c025681500301425081d200e558078a4000c3e44010301400516400703000c00000350303840030095070003060951100752151174480402040d2000d00703503185044c10725090701c41015041024502c2c00300c0da010442c0c541c1e6881030741800c0e10036000e0300d8903094060805030104040d07603603482e4a4061080b02d90502c5030034040c414500c5d9445034448002d440d0031070804000b074070229120340c002d14600d650103400185000d5801040c00180c60030700101786c03182c0d032041c0301b402500e0184d8400c052107980c03030f44020000440250006030002c2d1014102038105034002ca0612100800d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 969213498 1250 969212248 969212269
    0xd0204020910050903010c1106010b09190816091806050703090c031101090f0b030606070f0b07030b120a0c0b09040b0904050a232e060609080606040c02030a030506 72
    0x80200640c6541d01e60b0052060788819480f60003542403802034031001e80288512a5000e501601a000582c2043c03c10402900000c107445c3e405a401c88038120f800d90440f66200c0a0140e03034010b1300c11100941d0305003141e0840c40d407000395041d1401c002a1444100c18500c41081c2d41e010a01060743e8448501c11009402d0540d40603141d80030f000030000c01c011410640800225007070300c070881059a2803010f0559404a845407885120080001400c80c2c58817800604002c0e01c20720f0300d00c0645015882c1c1e45110340080f40d40d14042691103645014500e8940346080c0c80e142480000c104109841d075540001c5022480f0300d05003d200824245850748d155081540c05c500040c1c00a0303458509410640d5884002c045c05450f02044c01f0003882e0701004c0c000b01000081c10100081c041c0b82805080c81100c108881194084844400c05140c00503d540c080c08000700703226595030703046900b030140c80c1e030400e2005070440e03200c0d034500314006610680100c01e403200010907003400506035035140e0105a07040300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 969214748 1250 969213498 969213517
    0xc01120609021c0b0405062803150203070927200c0709050708011d06030106080f0d12180b040c031203050f090a23100207062003150d020402 62
    0x11683c542c041020142c141a03400f48880113104050a210901c400c540d0255420b94010803500040c0b00c1e010040c401c2c40d6959020140240a015942c1d154004c02c69000c140764000150008240031900d503009000b00c0140c0a80415100c00b08045c03050602605004415072a00c0c0342c45120700c0c528241048841c0e0003050340216250b5459030314004040e1180d040d0b0040d0301d180c034540804506e203144a1100f450582c0c01980c0d2040e0b0b42e40c1040203400329500010029641503481d500007140101d401e110ba200300d071041400600c507032440008050420810411031001c40346c5400e10307412403c2d0b06001c100c22000d8000c50405600c2d1110b0400080c81c0c4c0d01c541002c1c100d04100d4400e0300e0020341c107a10040c811140c01c440c0201e9a2a01e50040b40c4540ba065005080308a80110701e04071400400350b0858110402812126940141e04000080c1c0c0c0003000140c2d000b95591441694880c6401c41c28003814200c0c00482d450351a080288d8031510f640880107d000702c50340d04440086403a582d046450303050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 969215998 1250 969214748 969214751
    0x307171e0106120e101e05010b0904090f02040608071d250504030605040b0601030e0604050604020906010c02030109110315190f060302040513140a0b19110309060108010b01080402030c01120609 85
    0x5d10030150b10300500180d540b00d4035288008070f28030108130242e00c80c06041c2c840c003040703191400043c0750800c0301400c2c081e54140d601c166079544450042c1d95034850280100b007008050b00c015458000b40780c0180e070b04074481c036240d001c040080107406040300043c01541c02c0749400203801801c42440407a5a40034507040141050304e0300301801b042c0980ca8175120700c180400daa05100186007410042d03160201980c004000e984220085401480c0c481075040d8080418500a0020140c5800090030745080381015101440d00d010034110a050600c00038403102180e04c0e40e500541031040c6e10040c2c44640206004249541c1c286840012440350402c4c002140c00520078091410243e04503062003010b45c6003100d01c0d20540c8803090354008041820364825800c407440101035911109105d05401000c0100c12416513a000c107896201c1001703003e10300450030000203051b03135818140349500b1940c42c00c01d118140403002080000583d00054103500007002845c2c400e9000b110b83e030140c3e02a14071a0020080c0f070303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 969217248 1250 969215998 969216013
    0xb040b060a0f080309040506120313051e0a1404020d11090109050301061802030c07060e0d02060a09150e0f0d02150a050106050403140a02060307171e0106120e 70
    0x11080100060140c2021244140256500c6090002c0c0407000d1051030181d40040c00a002c0d1803030f1075409150f00440251000801d08422000c26095602203100003020f00e005020511003070410980281560191b40e20104680710106c000844440c05403040c0803a061405800f030030507031110f0301a5001d848044506111034602e00500c180190844e4444500142e0100030006030b40c6070501880085600341e50381440c0642c0d90f14a040d0207548020807440c4411000c0204400090303030b502c28060340d106038002500b5070444490000b802c0a60103080e001d4401e05003106403003c90031340110030903080b08103500020601d0304100c650b814030791a0396402d600c0303016003042d14030031a0300424210001078511880b81625a141d24034542255028043d03000000e00501043c070000d075100d0151040d030303610881150040c040c194000382da182d00032130b8554000750f1002800085203216410043c1c2010b58203a8000e040a869200c044041005104441c01c016031010039100e4010168000d001001101007a100c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 969218498 1250 969217248 969217253
    0x60e06040b0f0f15040e071a07031e12020c1c11010c05030114010f02070b0f04031a04050a061508060a020a0206010f2d0518040618020d1b030b04 64
    0x2000c81c100ca840310101e1240340020b880342d507250203082c0b00e0340141e00d003104c00100041c1848000c01d8510500b10083c4a0311401003149000c4482112a001d0340090040d541c401500e0024103040365141c50072489440e810a1500c07036034200c43c6074480e908a0980040e15411955a01c074942140440c0c043c1c0003207075100600d0f0806034020040001c8144100003031048480c1c00108817030900c030034481e6686610028440d40f000307600c1070100e150500c02a104886c2c0090700c84807a8152036010604e02c840111000404000f0804102c80c000104049500e0003e00d600d0b081c0c59107510f0f500c4909008010544d0f03000803104007450b43c040c40c4064421542181c0b414580150550025030100c450345002d481010000106501107010704002d8504603001d00a9242c050802400c5024020803000b40989030000d0200d070315210000341c08440703028648071030100e04050170400200c89031803004911040311500c0e0a400f40e140c40700780c1e80106511000700002c01d142031000c044071440a409c021f041c50342c0c800c140800d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 969219748 1250 969218498 969218513
    0x20d0c0905091c261b0c0c21031204021f031e050402010f26040515090102040605070f05071a18060406140a0306080f0706090b0c03030c07060e0604 65
    0x1003140c0901c908011510032000c140e4248202500f4280c1d1072003441001c0701200341804e5030580180300ca104000ea00ca000c82004101c507044841030030419402903820010318a030051140c0440c0040302c030310350071510040c400c0030b0701c6c0c0c4a032103904103050100802040442d00c41d56200a00240318241008031550005002000380c489114940103280f0044210345e1000224442c5500443d416181c404040103c6e074002c0d900c184118007143e400000c240c040c00c281c0d40181030300d00d1150340314602420900f400c0c52082c981213100500701041c02e0380306200900041d5080070417100e1141c0c01482079140203015207003c503d421142d8111110051080d8030b81d40351501d058026169030701a005445403850112414040a03018500c603c8000036822148111024900300040041c1c602900e40800d007144c84041483c60103140700d4821400743d0018000f0400c50b80e101100c080074201c810221440c005020500c16501c0c00f014041050301a80080c0c014208a0355500c5004824640c05c240c44042c0745c1410000d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 969220998 1250 969219748 969219763
    0x12090a08190306050f01022a0d081c05103006020909070e01080c0c0a0c08070609080601030206072d0b04060c0318060c05070f05010b0f0102030c0a020d0c090509 71
    0x40119007040c202044c24600107180d0701c501d00307040c4d00800300f0009007205a82450610b500c80e9401d00c014195405141c0c80703101c0b801000502421200355261600346800f1424506120407920035403511052259981d16000036008644089413a1600d500c00d190211449190141410980003601c0d08600300308100d94001d85444201280d0801469030b9124007524292514141380d4006801440091940d88041c00a8030001c220201140c80440e010340d918510b03400d00303400c80481c682c02400200f000300d0303002d13800074060103103a8003a0806500d96400700d5154007640400038400b4010601031001132960003a0001135904202500411004a00b40889102c405560a4a01c3d03801c00c51060303410f0b0300074000c1d1a00e4098241051141c0c1c0425180c10b001015040c0c40c82040010412000000c1590b0f240c0390a00b203800b5000004104c50f403001003201445070354250032f0554005004981e4004808140011895010350b0105a058100e24040d01c40d03801c03a401018504d860f01081c0141d0600015a01c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 969222248 1250 969220998 969221047
    0x1b0304081020030f13061406040b042307050c030409020702090a0b0105070f03020705031014010815160201110f0c0c0603090c04230103050d0807050f12090a08 70
    0x100481500762425802003401075921030340004041002c04c0d00c005492128680c40341081604000e4000f141e9906170603983c507410b8801c1c0c900c2e1a81c060200c20325007441044455541203d0800580c51040d80b50f20411403450030507890780e844580010852406027040750209045001600c0d41c2c3e60315100020029045100b0582c0074001000c0004c1018000388680311141d40141c42d40d0341800020303900c00c4611b1000e91401c0702140110080050b094404110400b0310110f8400040b8042c001d200000d1540340b01680101010b900c04c0c4003d0030500c00c0c038980c2c141c2020244540b8020016003004c00ea000d08099003400d0078090300041e480009180c00070140007500f8844081d59180303d000020810203000a441000840d008040c40c103500d403400340d010461943c410303405d517801b5948841d010381c08103109a00548107600401c004001052740810140e510444500300381b410980c80307092a804c0c5001d20941034855020700004603403401020802c680d00c450344001794903a110401d0880110104000007032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 969223498 1250 969222248 969222251
    0x81b0a030f24110f07150c090905061c02061e032403010c050f070302120304060516050a082d0c1e091818010207030521040f02061b03040810 62
    0x100c1c0d1210854054200b20100000d40f00341490610107942c100ca0340721040c21a801c015540754103208540b0343c017134254a251152955a8031074542014102501e000400403885842d46c540c0d640030255820150001035034040d02e00641b5030518080c0b80c01d010b018485807500350b41c0088100404810b90b8540344020648401403414449280010306007600c050100c000041a1b00b486400309020351380c005800380c0341c009d1046458424008240a5046d4400c0d40e00351603c070f4440c002c03c10703080001860012801240d10b0118640b81407540d00a0520030041c0105404071005040c0c1c0e40d1312032110180c25540500c500c0081e9090070403c84000c0c07240d000301c00b0043e62030415480c10390110304071402d5410050b0094605010010660110580694024403d0000c0a0184000c9044040900c0500050b61181d15203568800824010390786210515600c182c20075010400c000029400800812082d541580c1454890028040040c0d2049003100c9a49a52101240020344101c00103051002007001d91170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 969224748 1250 969223498 969223553
    0x30a09050f01080a0e01330503120412060902100c05010e030405030a120203131503050f01050d12051b070f0e01030b010b0c030d0f0207031206081b0a030f 68
    0x2849400d001c801003450128204400083c5041c050381c0100402003e001c2c000202c1c4202040c030f50321804056200c00c80f40300ba51000c602030104002801e98003910045004003000311000002045510130b0f80221710741c9203c503045800821129030042040254002c1540e444003610550041010060030404c2c0c2d040d6081918141c1c44520120803a0191500540078001c6070344d1548800394480e0a0364480c80c2140f0081214413203020302080300340c0203444000d04d035088030808403070010300341d03031000c7c0842003004a0100100301d41d50754002c110039090b50002c011340c20050b00d12410b40700f40c0500010346a01c034031014070000e49036070042084400c0d20603202d54949003c1c1c4510004403400000d000050460852200500c4008403c0c406000c0b10151001202d28141c00c3c1c2140c002542c81c419110048250003180040400d600200d41c1d581c4a04046010002d40d4900303584c29544581021122580c203442e075401c134141e600e030f900c4c155000d1500070100c101c240b400307860088400c008007800c15240344132110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 969225998 1250 969224748 969224759
    0xf21030b0f040902121c030c0806180405071e0806090a03020a020d081c021804110a030c1107080706021e0c10020a051605031908030703150f0305030a09 67
    0x105142402201030321070000c8240c240203100050080c08010b0f64446411110510a40f000304403031031080c1c8194000020a040040c0094140d0301071064074001e22104008210b102d131559840c2000a00341003c41108546507420624103015083e0465400b88000d010407030640300da4202c0c88002c0710181d0040741c1e255522502444d44500c00745c540200180c00c43c400c4ca00161504500400540340600c1c1124034081c0000024444c0f00f100509404d4003503000304a851a00b42c5800d0700e840b2018080c0c50520181000d121400b070248034074a1680141942d41d600b4055107442a44000c0010550744202c0309120b8070f0b000c04c99641c83e414411000184510741c1001f091607280803a031f41c0020120340c0105051000b03c801c2107040d00c440c030504401c5114016403040420710400000c3d801d980c0d2106044406030a1809050030040301c0e5080c0914604241e10309400503001034201e95100c9024580021200034210017000707040d10903400203500c00c2c1958404000d004c404801030a03050150344412024580d0798 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 969227248 1250 969225998 969226001
    0xa180f21020321041a18010507020604031e080a050a0906060902040e101206050615070b0108070911030f07020f0f01020d0f060305030901030c020f16081203270a0f2103 74
    0x104c0d4000d102d441d8440e9100c480d2184260390b04d8200504141886203965409541401c50300b04840c5400142d0080040c030040c07540040b15540d81000c91194148549192400a050548049c10302901199680001814548641c1c403500c002e40d4007050920002e81c0d0f07141007401030340180c02014010a111130215130341940809882084610910b4820507021007922503000038a0000c0001d03800080d04c402109210b8080c0b8010700e1070034441ca012102ea54140300c05140303441055005120708a142c000d00201d9481c1c1901a01e03030000342d903480100030f0703940c81c1e00481c146000e5451100384c40c0b1800c1404006000c064000d400500031201081007061100d68201e0252405031101070171680041018001c0d952081d080402d500c5500d0040300d9035410b0004000f4a4030300e50a05031a07111004083c184400c15003808181e030b601c040406010b0550074a0384c040b184110050070914903030381c00c20403141e1005c1002c2c0840604a034003c04604c0305010b90b810552402c2890107891001e48411003103078892540207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 969228498 1250 969227248 969227251
    0x106020601150509060403021f1211040e060d0206030412110a110105130e010b0405030f060405072601050112030e030604050c01030f29090a180f21020321 68
    0x2d03100b03244a0b2201d450740584040d0302c00c01c07185401c04020480440580c489420101d600b280002c0400030200c401c0c1c00080c0300c0360440180c0b0301c00c0317170600c64401e04001244040d0713401d6a0044a1441503030300c400d0b0024030364007010280250412004010031040c4041c00c51180c031100404d46500c401ea10080740c1c000e8490080e01030003003009080110702013655104902038000d20fa110240e40034550b48505e218410260240e10032801c80c1d0300010240a141400d101d10310350584e09100415003400c0c6a580c007510f9078880d02805000c0c00c800b034001011155400350400b14289144000c0285503155002d1003281c484500c402c2d808203869242605990a00003059889160000c2c060504400160011000703130030523241c502c10300345e151285001c41c40c4d04000c0f820303102c0d1400840b01400c9030003041404008000101004002c41c80c00101882240307060103108111540710040000f85807852800100040e25070014102c40a20050a81c41d11900003000380070684940b403070318546040e115011104c0c01d20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 969229748 1250 969228498 969228509
    0x2310050604210606090c23030411130f0605010e060703022d03030f04210206061011010905060f090d021b0604031205030f0a0908190e03030706050405060106020601 72
    0x4104001c10200e82000b001d550051040d040100e44001191034810030380c0d00390707000b44e45075998910381c844400f0341105101c25015404046c0143c040071410102646000080c4003801000c1403c00c8216640e440002501400e4440b4104001020082d45200d000b0030700b60040c203021486001c0da104461038014141d813500c0d54964014103010344038038654410403400f5003031418649a580c020103400700c1d090024521071005010324221500d8541414481a00076400140096054082c1c1c0e07803002d42d000c96526440f0740d00392807001c1c446144007402c850041000141e0001c0d03510703049100041210106081d030040c2c0408180c0ea4160b111608099151400070901a016038495a80d0030000501d80781500d64a050080c2107074217155403a102d00c00c0600c2c0b10900d420004100104201410007040c848580040c0415400c20000301a681e8401c603502c02d040c1c1c90390003030080194044029200b6820407459000c05030599456003941d00d007540181005503001c41e1240180c1d00081412880000d420b0304864 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 969230998 1250 969229748 969229759
    0x32503021216021e06120a060506070309090c12060b030601020f070f0314120c0a1e02010f030b12010e2a0904080a020c04060303110c0118180906231005 67
    0x80107908100100d0000300c21300001c500a4003080c1074a544440191000804a2208026502d4441c40703003412a203e5420103441041c1c10301074480860f922243d000240c4211031000618400c031000103840d0b40d584030842c4202c26051640108501401d00040c500907075003038003101c41c17500c2e804880b81d031074684e0b82c050038465000301c0008001162201c02e141c9004084201501c50350f940481003150a0760001c60320450b50380c0074000e0a000c200342c0755010306c10506e82e004250100882680002d201c01c88a80c600b104068a628901c2c2503580c0e254501c000000c20325008109260010802603203030102c6130f032891181202c00c0048000c0c208003080480c01c0720002031002c1d5140d641d80d6a03c8a064000d003802c14110704c507035003400c00a62114130078a40038500a0310b52120102010042c0d500d40303031050b401c40b030421108804802807003200000751000d0b00d000f070080c142180244410580208207004000d8680c9041c5803040b0441c030100042100e4040c4111500020356444540d00702d803d400b144200703600f12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 969232248 1250 969230998 969231037
    0x60909100902060705010213030c08010614060a0225060905190603020a09031407030b0a0e060a0209060d02030a090611071e062d0b031b040c020325030212 68
    0xc4401d80c0940d0425100400300c13802e044051700c03500e007280c025040030000702055610a00078025100e40103030090114a00a00140d130425105100840d0783d00c608a028a6006c1501e154560080c4211800c2e50903903810781035034504085860392851004d00c20040401c1e00380c08081401e0030504045c091407100c0d02c044400303d80c80c0c014206c00940c400c03c142010001c0e800c101000040c2c8003040f60302d801c0b13850740081010b2415810038417100d0300301078444c6090915200c401a071191003c1201c50b0300c080c2a280c01a00c0f20450004190940303e42e00004100c02d100000308001400d6552101604d10f0250004000e08a484183c664261148860140c540441424201c0754204181d201862092051030080350500e09416048421040d1840551142c0c04100400c007000d800303407103034140d400011001810400390002c00d045030a110944030328050354503508001c1b9494020000c80d1010902d40480d508403407042400f5102c5a0f110510407030042c0240079241c91320400301c02c01d07110002c0f10120700e80800d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 969233498 1250 969232248 969232273
    0x2090904110609030a150f020a0e1003110c0f01110306012304030c030f02030d1d0108041a010b220302010e0613030501110406090b040614130f0603060905060909 71
    0x404085000754800780030007543c040b40d01c05102d5195503e1042d00b03a50040760003481901e0644400800200280340f044c4207502049900044182440c041503c94440c100d50111007140504200c4100c010202000100b08106a00004102004c24070130300080104c10402030301414140300c1900d400780050749401c031880000040d407412003510b800003040c0d20700d403550342c0c0e80382c40c1c01c4210b607802500d49a81c580d10403800d50500388140f003104561442d05103800c003144206c1210a070351540780300f41000840c0001408000c13461030114401e61021050081543e507034003030f000c42644800c88201601c030702a81050010503007824070b00d06681c1d0584400386040808000d00415400960701c0f010294071100002000c00e90a104181c808207040510540e500d0418401a0108041e07900c1140e00034000c100400078154054205911914420b52a556602206103028102c03402d0360031403002d07904006130004c1c0054040e4001000c03501d44403424030071030780d0360401c201a940080340c0400d907641042100441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 969234748 1250 969233498 969233513
    0x70c0506030903091801091406012f12030103021003060e040305070f060606090518010e370f0501050f151c0609090b01050d0507150c02030f1f02090904 67
    0xd02c00908400c880c02c0201940000e821807080340d00c03005212100b00010b0101d0181ca0003042100c034074001406a00e07051000c00203081c044140e07400414800792260300c00449031202744100d0350010100855481003244081c4800e030360b0003840304900c200c118520341c00351103020303001d042e0403034400c6500801140e41c0d5071019903103036010000403201004440a458001141d070300c2424082c00303680d03036104400b134186014000c0305003010118010480200004004010800514960212111201030009a10200203c003004240d80e00e08040101c00003034407250003036a500204500041100602081e41d0354010300100d260686c040c69000041206124640b05072000288052410207480c80c07603504140c208002120348a82045103000d403140c440a080c01084145a0302400701100c00e02d41c2c040301662016a25032a0380300326a2940b00441413019101e020350400707000950041d0a27140100c94801c04107403100b80241290814980500402452000328402e9400d0450040d12078205e40e00c85486a50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 969235998 1250 969234748 969234751
    0xa0507080915160c0b07081515071e021203091309080a0809030417070513062919030e070b090114090a0b040f08121312061407020a0512070c050603 65
    0x83c180604428a1000036181a5445104a00a9440815500301000306016554210b00c22900c6080d08440d00052061200204d13203546a01c12000c0d000c0c41101c20000d002550940000780d4062100001c6542c1810040000c0c400900d046034034208408540d5114021174103c10390107051740000b8003402c1c00060050200c0d0340c002c42020100c80c201940d039260f40185444443e03c4408507041484100108c3c1450209407420a43d100c0e010300540d424210844182c52548890b281050406d8004008035004030007240c8103038440b0301c03128031900d00d0300300080c015103802d04410440c3e118070540056841c5404041d507030304000594a420104803119490001a000034000a90200084070009401104800103000403d05510110601d9160601e0503040800c052442000d00d40100140011815900b803014207940240700105000c5c035980c02c02d00024008903465a803c0c542c0c42040c040d01c00d40004100c40c07400c2c402d100b260541d0340342c8401c1da0264040c80d10700605071003004605000c1c42c5404c0d0040c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 969237248 1250 969235998 969236041
    0x109050a0e010507020c1813020105071406010b030108160305121b0627010c0c08070602070b0901151706060111191209090212060121050a0507080915 66
    0x114007544100000741c2140c070305540e8580540d020182c96401418108840881a024102c10301c4203490700d00c5170742c0440e20340e10742c000b030401900080340d0b820415911a070404040400084801560710754611480c0c0380d0080c02250a40d104180511b12140100c48a586c10340740d10502410340d0110701c0010341403035000034480d40108409103200f403032944000c001861264513089005100007903545200007200c40220403403200c1d079041c04541200f81c0d812400010b0b085504c50310743d80e601c00d075500301040203000d85580100900115000d101034848150020341c094501206903946035503580f1442086101c030f1b2002c0012940000d000030341c0700c0d030103035800401001342c01c01501c511000342c80859090000702c0d1003c071460a42032611000c0d05612560a0001d00f4099104615000106136030400c8400010f00d40c50400c001c002e01c10034400070400040500ca10340d00014011414001400d00140a046440c107000581210000d00301650006891a000707201c00036142c0d079521111a80090754000c4a4130 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 969238498 1250 969237248 969237251
    0x33103030506040f0f0b010e01080106090e04080d1b081003020904020f0102010605030d050a020c220e03090a0e09010b0103050c0f07170301060e0316060207141908071410080109050a 80
    0x80c000c0c007070801d00544c5c4519048484c0020304100c0314001510b44405001c0850400c400000148591500000c0d41c5041c0e900344008a54a0344e954a8070070180c2c401c4180c0d1800142c1801600c0c6180105003980b8504507070591103d5600c0d0795003914020b94901c1c0340c800a94455140d0001c90094140010781c2c0b441001c062001151f80354403030000c07a10701880c050b00301c1c00250000480c13020041d0306000e11511a08100d4201d40d41d44100741c501c02007007503e05402d07034011740e4444454090420800880d050740310040c1c80712200666a071010700c0345120484001526500b49601062151b2080c8529881682c52500b15414880b0413a2402055085820f045888403c00002144100754400145009020641d10601c0c0e0703c980390241810f240502c103440000f44020001400701c5500130481c8420784420b00e0f129220240d26100080c01c01c1000124000700080005022a064401091100580d1a00c7d00e07601c500320b4400d014007103141e454040308000900040c0c014480d4105941001d90810389c071550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 969239748 1250 969238498 969238511
    0xe100c0501020d05010e1e07140903010b10030c030b0a0f0e0a0609020f091c02030c040c0909050405070e0705190f0e130c2601030b0414010f0203310303050604 70
    0x180e07800c81303c081c0c0044105100c0201080a00c0c03034007030f1160000c1000202c28640c3c60400a03800707848000108207031142800701040d0b8142c151002d60203103a40c1c071001040204000c80d01075002d801054840d400c1e4000038100302c9083c0c00750070000300250031900d11455005030340c0e151032511103100070060030f021009506c4020000e50b00c11a8006405d07103811090ba42980c030483c039020171a14000440030440c04100a469040250382c0100d005080b0794001e46002c551000b13102d60480701211181c1142d070b212850300f41403000b801800a00d100c1910b8481c00007042c0c944450b44151440d0180b0001c00450801800d600c042007803144d8841003801103903080100492540400046403203810f003000e140c12a690761340802d091684a88a60ba544100107402d03081840c05541100f81c01c00c0501000e800710000e10302040c100960450700d04009400c0368000c1011800d00c0414401a40c003e0700d030b4030501001d132000340c40b00103180200100700c000d0042c02e1100301c13000750f41d0503006003034010b000759842a900c82c3d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 969240998 1250 969239748 969239767
    0x51002070e091c031e0b060702031b180f0415020714160f0506040b0711030703050c030606060f0d1e0f06032307092703020307120e100c050102 63
    0x1c03000c501422200c070160440101c400321251041c140c801000c07041600700780d41c0482c1e40151149a1140000c01c0002003109403030a000b0820a11034a100250144030754000c070b1401c10040c0b0410480024202d542c0d2020b9584219900e10307502e01625018020b51001011600141044010802e0200700b0030b40582030071916250001c581c0c03428404100382c3e40142c072080c5a0310754046050b030302904110074409805828000495142c0c0143e004100b122240001c0120502495000074041c2ea2001001c4600880c1c6a142035a15901c106030241d029114400100d41c0a01d400c20944440c0c0300400802801d0847c4402c9081c040d00e144c1840050014502800b405600c219026071803e04107020400b0330071030b146181506903540245001c2600700c0c10001400171404000ca440c8048403503010003c50811002e6010b99000020380344c2e1003286034107171a0304c03004154000c000b42c4052400340d04100d00e00035018100341c8910303107040c0c0381c150700880140b44010998000c4030b010706020b000d000010308041100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 969242248 1250 969240998 969241019
    0x20d0c0203330a050114060c01150b1206010f0e09130b0a02091c080a0f050c0d030501030303140f01060507050f060106050712030207020603220b040303020c0f0c0a05100207 76
    0x280040030041a68410700264508422604040f5034681086550715000071000c120301e50765051403041000060b4170744003503002d40003144902d882200e58144680d8039079040181d540f1540f80c91078030380010350001b0120341c0900b122003c00d80081c2c071384ca03410050368000c0000c540d6004280258918074036030444041141407001511800f50346170300590b160324040401ca0011f52009402d400c8100324044200081d042000741d0381142a01d090000400340b003294161098081c0b200c401c40030303114503025003c002d949030700309504880c00f0340c030104600c91032040312108010080701c0d0305030000344e0000100071440c1b1400050545030700610954110100001c01030341040c1082c0d010f2800204007141100601440c01e01d0040511101d0400310b1a000c003941c0480e42501004002201418580281e4450300e0300d084203200031143d0140ca462082d203480d203000b90094210050992003440b5154505d44503850000e410000c0d8030004116040392882d12082040f201a412490070850007004800140c80f64076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 969243498 1250 969242248 969242293
    0x402160f0c0611211614010501150824150c0d1106091b0f060a090929040504030903120f020d0302030f2413050406051303020d0c0203 59
    0x15070780424400780380410003000302c003c1d050f0281454100d000c405804c8501e02c1c0d0b00a000505059529442d86508222090606a6800702500c091040901c01004020640c03200e0b05855407488480121003150a0865000300304803070035880e40c04032000d01c980c08002d5280c0900c030700e81e00810074030703001c2803000300c020060f00000300401443e4000003031503000e190801c82d2950803842c2071f0000c2a461a101c406142e444420090303401e03c43d0b080204500b1309071601c01d80750b64601e0015204664896655a00030240410340c450031400c985001c00f5002c3c10f0100601c0c0c92410440c05000007083e940c00c008004c001d03d00580128284100d1801c000000f40c18041000c0000651f0745900413100f001801c081d0810082d4622441094810410040c80e4105031740b0b043d400c41080c0c20f118401c261090414403150080b414081d5000300c0301c00c501d045105498100b10711807403180405105640b502c64048945502c82e02000300903070000e50700786100a00c1000a480740d80e00041c200e0b8075213a58441c3d09041c8115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 969244604 1106 969243498 969243503
    0x50406060b070b1501120c050c1c050909061201090503040e0f01050109150201090602041401110606030604030c0f0b13060b1519050c03040f0302010f020a02010e0402160f 75
    0x4909041b5522052414040082129801003c2e1494001e078031070032003c0c8940d800d1010164902c100f40c80e001c291b40d4a500341044441c408101e8881c0004040e150448500c07010040707000400d000d0034580078014006155214240b00404041046c0180500107142da0240100b1090740e0080d0f29004482c205d04030b010311141312840032400340040c110003414070741c00400c000c50003005140b080d198440007600c501c0b00350610f007042a070315403100311216507041e0041000140402e0007117141c0c0da100c91040506205c038a485946081136801c041c2c0b640c07800d1000c4204584100501703403180c031512100803a0300300c000d0100090513000c00d209003600850b092031041640e072405401103040e00d0049002d80f090780c0c0ca40c0c1d1111240041c14105100503400544624480800300340023143c008022034040c1d41705408005075505110203944840300b1070b803010203400e1001000c03a16840045c240c403032 = true := by decide +kernel

theorem cover : BRFrame.Cov 969064748 969244604 := by
  have h0 := BRFrame.cov_init 969064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 969064748 ≤ n) (h2 : n < 969244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
