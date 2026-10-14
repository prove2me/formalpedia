-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3507
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:51:28.270895+00:00
-- url     : https://prove2.me/submissions/289d2207-c206-4324-b43e-7c737c31355a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 630575539 ≤ n < 630755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 630576789 1250 630575539 630575587
    0x403020a0b0a0c0e09130b240a030f020906060f030739022b080c060c16081b010c030608010e07030228030f12020d11030904050c0f04030f17 62
    0xc6620000d00154080b90840b00d100f078000d03100090303900d8030750010328114002038481c005608003070102c1841b0b272410388410300a4903481303200c000c041d070042d03070030b00002080c050716065000390300380320081075105118040d621511050b9110303403120300111003403400c12182c0017240d032030016203040c10b0383d15105071103210003900c0e03041d2a445200b4a2144403100c0044010803200c040c41d0340407200034280502c1d00098040444080c0030b072880c584400c0b42c4060329114201240d00314065088405002c80c1008025000c0c0034184070300074074020480300000c0d0844041170090400700380d9808007804894824400c890401030104018503e183c150340004050031001e4003c01141070180004a1552382001c0c5491b00560303000b801480c00d00402e00e000c40c0401000714007840107101303103d4250902c9106103102040049007030042d40c6082c182000b0300c409800c0c010f01003400d5410801ca03160505c40310500403c02107000342c1c8081020380d80c41c580204d000081c020a00d500e0b1074144078100c4412020301d1109030000b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 630578039 1250 630576789 630576799
    0x90105040209063103030801230102070303030209040207080d02030a0b060f0d0207020f0307030515060d02012109020613080c090606040e09120d06090c020703050304230301050403020a0b0a0c0e 85
    0x60303514500c1860210702d0b00c131040540008a000042050303086180c42d81a1440c9552058080b424500068100380d0300f070340c980c0d006034418241040400c1c020f60040204080180c03002d0300d442042c0d121042280d001d0140c848a403903001081282c10b0b40c05105444c0105821600e131803400248020351449801040341d04001d041c0c0c0024018110341d00c81d80c1d4240c42c00e0380a404d559000340e41c3e09060b40c513420620113118500000200240162030204a141629135058691118000320b0307984a000138044210300140140c2c0c6e865622001da42c3d04006043c0c10b02688010500280c280315820342032884000c0f009000f40400c90512680d541d403482518140c64030303404d103041d03180d81d042101407900d0b9000703040801d8420006244466284690000c8007070b40d044030002d2080d5601ca400c2203070b4418140c4006031980d00144001c4c07003200200791460107103c07484088410741d0a0100000780c2151000e89080300075070300034042d020400081c4504030380e020320341200400c03040c0d50390540613142106040e5624454 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 630579289 1250 630578039 630578077
    0x21031d061c0609111306090b031617040c09060501020102030408030f0702102a08040b240406120b060108090319050c16061101091e0809090406060509010504020906 72
    0x40d41042d40850300905002e441408035182022900581d03521014106142100c2d800000c01e00c2c90080c01000100d5090440c1c5070325654416400b60f0031942c001140c42c0c01c0290000700759444000036480c0c1e0380624000d074001c8010501d0485c0c90000c40e04e895102d2410f43e4018000c010210740c6c0322080d42c0d4006220300c6000d40669603003500301e0500e84032000c40170b070315440c1a02c410713920240c850700405000c400981008580d09140c80544e5800c1080340c0062038605070700d0005001d01d48051071000314414945c0080340b225051000141a40d0a6400220f1700b000c208060b1424814041d4070b8580080c402e0904152030f06104009584911425030b4542c4400002c25032910001e00c81d200b1285880e00c034405542181a02080d441218029880340100103008040340c0c0701442c10600c41c031102c0301d80c0420f460b13812828100d550108001080c00981e18140c007071040c44a00c0e00c0344046540b01d01d202c0d0000003501402c11081202c6084117810040c0202e206108421030760f11214112001072920003102655 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 630580539 1250 630579289 630579337
    0x172a01050c070914060109051c110d0602120709080a031b0609050604140118020f12150f0709050a0501030b04061509060311090f060d0621031d06 64
    0x85072007603a10001151007004000107000c0342d10791010030031040440308010552585001101ca4040900446ea0301c0b02388155030240700d8040003038045600d8803441074a0b02c0314818000050703003810071940507038501e0b0300020341030080c2d44804680d41d80702c0500c5c10300e0800d547c104001c907942d42800310380007000c0c00942d200d224081c1240120700354115600c0603045c0040301d058030707245d600d5800a4034201d40600c404204022401c4040c052141040584200c8002006440e001c1083c20504084440e070050091050b2100441c4240030318400506821503003051800c2a140d80384a40f140201510200100050f0501940c2e0340c281442c2c003124400d20b008035050030010001802051680d001211810421000c40c40181e008140c040403110151010081e08075100c6a910181c42200081c1e44d100c041d0503130011244c0342180142c100c01c908000001801c540343d0080341c4120015400351130910540000010803d5404030704580381d0301c000704561030b10108e40300114080e40910341c0000400002c601069103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 630581789 1250 630580539 630580547
    0x12030c03091c0b0612011103041101180e0a0906060302100f02070602031201090203071215060219050a062309070e1608011415070809150708040b030c041e172a01 71
    0x2c0e05207401f00450764a00f014504810500e42c02c07500140440c8a100505201c0b030150348030b40c002c0301c070010080002c0e503640c0140340700140b0620004440e156603034480800580c8802100e0b0312004281e80710030502d8042031002900d05507c5501c004110b500401035103c100d8040c07007015045600381800503840e511009020f542000918004025a61600760303000e9a0006018034a0100d504940030f54070401c00615041c4280d0040401c01f80040d44031346c0c00480007400b01d81c4a482804c2000c400b41202c8100c42c882a6802d4030203443c9078009900c100d205000045600140b240c0085001001c00c8100c181032001030701c000d074144180964a900d10b46074010a072181c516400001718440c00c031503a1503200e803a1038800c0d030b0400e00e00e5501a110a4502c15003034140305080b25400c2d60407002450405113000580e0383c1603030008050304035005041c4400554140152809400c0301c0b01505030109207424a10400c09400e202d8100103040d50103010505407009a000e100c280300c014921a0001d0514442c0040e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 630583039 1250 630581789 630581801
    0xc0918080f0d3207050c03040308070c1701020319020702010f030c05040807030803011403010c1b081201080105060111070f0506070c15120f02190c0212030c03091c0b061201 76
    0x5004540103071910880c00f0103686800c0f000d0b0a44004a802074940d160b0031121030240c0080303108540e00401060010a071000d014045203403240c2c01c00b070100e5403540e6a001c04055030b0f0004000381d030340110500516107404c0341840d901e05080041181001c555800007407401c2c41c641c1c10241072640e0b490f0f030390030303894031a40840f0b000d803580002321181c0c140d0701e10b003200640c1d00c00d05ca0305480d401b8000700b000e03840c681800b0707034944400f00c0e513242e041814002d048640790108404007151485030411400014880d00c100880c000c140c0d280001074149004000581400c1c85121841c4540d007052009014000c00840070500f46c8006407503040e2180000c0c0303410300d0008100c0c2c10942198414042600f56a58419001090401d9501c000e004078840e030b848a4059000b0415a068050000d880c88500b0380c3c41500c10184060008200482021414142c40e0640c1e0042008a42c6500000f801810f02d04150700195662150070300a0182c550054a030f071070600130702078500380c82010414110003402100b50464 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 630584289 1250 630583039 630583061
    0x13110906150c030408060f01080303010b2206080118060302030d1407060905010516020a050d030c020a0b04050d0e0909060c28121a03070510020f06040c0918080f0d 72
    0x4035030b4071011402071035903a4005104148143c828900040d140302ca01690031350407585c106006600310b90074040050407030741020450849080b03030868041c44811613840b043c0c1c0100300c80d444421955040c000710b69282440c6c6006907030003504040c42000140c41c00a1440c0c403000c007900d403042803058505015240f52140d0040a4000c904000f030b0007040c054103500450103401441c00030903d600f020007069868882e00321000e80709800c08410a054240260082a0180c03000d106841100589a07120710b00080145c0c0e09031120380c05050010301654002c41c2902c002c3d041120306081c1860802d103556550840142420012400407602c401d2124103040352423103c1d0202d8030307883c03100340e0030b09001400144102030050380603080450f401c1c0c15004100c4488001503026000c1c0c0100d604000a210161443c0d413080c2c01140724403215503e00c030806208041c0554803805142917840e1a01c5050010785c1d0760480b420340c8004664003058001032140003141c1442040500d52511042c102903003800030b021031024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 630585539 1250 630584289 630584329
    0x50a021b01200f010b030a0b1f0504050a0c0806030313180902120a050c1c0201211103340c060b0607030507020108012102010c080d0e1513110906 64
    0xc1e90b0781e94021076031032400e2402000810046a2620801da40e4800c4000042c0012603041e005c2150b581c16114001c40c1c68040d4504100816500d01c08a0205d400c201c0b89492030321307951110040c185902140b29504464114025800c2144200114458000520400c0810800700c0c0c4000020000c81c1c005405c40d0360014801100c1e1481a0368242d111314801000300c61034040d418418038280303040080d0b200c00c68203620288400746065401510080b1000600f00ed11500044581181280ba800307217011011094070400d842c0c0c1401ea9410030110441480f0701030306d074400d04100b100c004000402c02a9015035103440402d4070b036142020b40080841424558000ca4006501d0b01403641003801015464402ea841e10641c0c0c0c1d80da880204420201b012100800c0c40041e00305004d50b100f0030000c0c0710a801092041e1038100c00180c0b4100b1035682041110365900000e16409086850710780d419401580c10060300d6940340607680d10303111003840c066020f21aa80c15404904541c40f00409507180381c0301c10f80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 630586789 1250 630585539 630585587
    0x50d0b03120c06092407050a0c050d0c1703010608130c03080a03050103021e06090409080909070e1e010503041e0c03060b1201200702270403030606050a021b01 70
    0x2c403260b281c1104507a05205441440000e0005c2c0541505e60303140c1010043c0e0089071600e401800b1101913200c8020141040405000280414800c0c0000e00b54000e0300d458940f610900ca181c00c020b103403010707800501043d505100400603250003900703982d881070303c3c00d103010700788a540d1034401c458040b50741000c2c05e40d41000c82e20740340c0c1035010f0780001d0503240200c4188495001450501c5031004266094541000701880403901074240b5400402d902481000b0982c200124400852846041114000001800d0020389a901e05199641840c203500702030401c10151141c100207402840064002400502e06600000d0411042c0200d080c0780b13540803081081407945e9080480141c00440e024503c1580111030700001e407103051150001c4101c0c080f06032280100d080d00261055003000c02c0a07a0888040300040c00f11a910107840c54520400c0c1c00f06ea40c1c20706081c24000d08032b6250350404014800200302c1032082da600054090703128982c1d40d0b060b003140c54000004079464036141d01c00880c1030710504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 630588039 1250 630586789 630586807
    0x50f010e060f060d21050f070b0610020a031d0607051c020c06070302060a020f1201060f1e120c141b0c0a0e1801021e0304050d0f050d0b0312 62
    0x1007201401107401d00940704141e15010108040149052001418042c0f4050400c1820312081c0e00755a0701c0b6810301305a810300e2900c1c0c1d03070040103a0080c942180c05400220410001e464803560140c000d10061006180005695902411140c0304860000301e41040c59a400065035603030301141e038000d41c41002d90707139150294013045412060a900305c4000d4015824190800d041032000d8980f01a01036000701000c0d01d44104d082d0003544a80b220b001e00d9042080386900c20b080c80d41406000b80807a0395652090401004000c082081e01c01011600e48442c40c6a4100c032036110001d100c06940c41c48001402684003441035608074048240700654400c00725000d000d242202c00801c001c85d08103410794011618400400c040d8043e107004514a80c1100f0011600b0040c1038501c200302c1c2d001140c0014035000e021900222117418012600c18282400400c01003041070a105520131103000d820800c03038060031088007500c103019120300c407803601c0e584182244243ea410400e94540c2041c0e5680706507908000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 630589289 1250 630588039 630588043
    0x2301020d06080d0e0301020c10050a09050322090204031a1801060b07200105040b0a0513030b0603010b011112160c0b03013003030209010e090c04060f0203190c050f010e 74
    0x1d24850100d44c050450070300b21700f010700850360f00a0005c40a40103a02c1480c0d0040010940076101e0000385955961aa00080c810001410200910814110f10b4400c1c103c55034440700741c070f8000c0390300c42e4014001000080c0c001e00341500381c00d003001c15414040d03407800940c0c07038040d5890704805160341c01c20000003204848240141140c0380200d0300d0101403402683d016500354024410a8005801080100305860f00d0701d01801200310380e071910915001c0e06160030001401c1e65001a940c030142c95052080b1481d00b442140f145240c282060210100d59218081c1c0395203c4012100b10500009107441320514025500000e41c1d901c01c00c405604c50302c1d4681812650424001c000d5100305000300c40c4245090305200301d40341d04055914184100c0303140d034118043d41141741c489040c41513080c04c250003031355800c0613640302d12019000e00e0703101d503e0480028061144611000c081d500200003084405181c8496400004200c1c1481050031005140c21072802c0c0c40b56105000310351030010003141c41e00d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 630590539 1250 630589289 630589303
    0xb041b0b03150909060103030804140d0302030106090806040f141504050c090603060c2d03040501090201030c03020a0e120c1207090c05040e1519030b040204060b072301020d0608 78
    0x70b0b08040d00128140c07105100141806840302d00c8294040401000060300c0f880391940e01c00d01c00c45801c404109411103c600c2d0580e20001240030a0f000f20051249540c03210b01c0d1001088800000e110606080e25080c511465085000d800462414102141010204680c040343c0720001600d0390380f0716042c14a16140c0e0320001a4611500001003c0b4805280c009040b40c000c184480405141c0541100010001d94600000000c060003207010741e164146014051442140100b00220b131065251000400701d03050843c035401411f01c10700800b160035038031020100d0758050175141b88075000260408103184c900a50221540600c00d26040c409110022441d241214412202844040750040c03056529005600480b80018090000910020501e03031141605840143c108001443d0069091550b500d1580054a0003501e910902c411400e0510071003005008641100e4104440b9503100061002074170160307000c0150b98080d01085110a504490307991440324010048959180360b10390b01c81346 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 630591789 1250 630590539 630590551
    0x10213091a030d020d0e0301180302160b16032a0f0615060c0b1e0c18090403021207051002180102010b010c0305191107140910080601030b041b0b03 65
    0x820101c8054590a00203079186400080d03402501c9403580b030140440e4140c0720807034101e80c55907c541c010001090b8045540115600a5019240c1202543c48140403000a58042e03005803204200021300c428002d18610705669051500c103078001e1002c03420030862560858a00325100b41c51203003404020341c003601d0410b280c0c0708000911000818800400000b0f419100d0304000c601d0201c0103000003124464915071180300c41e880105078240950302a044688110707507104101d1000142c41b40d07015490145182440b0044030182c0042c949560001d490306040782201041c89030200c4d11600f0000240700e109485130102100f1916411215590704c2199000203080740594607014090045512400d0b41d8948240c00d40ca40c989401c030202481548003030307611280000c0042c01c80c0d010342020001d102281c02040c05c26402c99030b50162070f0811082c60b00c05441c0441d6038100a002300400f0001103041411207800040d9115642c1d242c0c100130215a01000c40034003080c111200204902c1c1190b0050341c0622 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 630593039 1250 630591789 630591821
    0x3032205100305010e15060c010c080703141314030f0703030c0e03010b0d080c100f091211061603060b0c010c2a0f0218040c0810110a030e01021309 65
    0x280c480341e81036044031028021405030010380400100700700104444c180764058007501d440c0c507204024104500319142c8031001c0c4000b0392640c092000003a418040c800382e01c18852401c03083c60800f24403003443d005100c94020010000100045910002442030390b80c08800c0a8040c4d0341d0b9261707454003c005201064406003c030f2901c00c01c8a8040c1414031407010f2210000c0c181c10701040b4107031103c04080d0000101c040261182c8017480c4108645400364844400000c080403956007102c2c5000c00b200b1030510040c2d0100030030001c080107101c4000a000da040807101031201c6001020801c124083e04454116200c42c40b80080c01d10481f0300305500c59500e000d00d90391540036410212200c03a0748280d0810441440d5800b0f4001c21000c00c1c003c865001d500c520042550104800d8801c0301c10146404907000c2d50341c41000d0354100a5600144000d4031001d580c0b9008001c3d8012041d500300b1075008401c4200f0400d80d4a100c0312248500035411181c10404400842c00140c2c0d0b0b5040c0080070340201c403542c1c0d03415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 630594289 1250 630593039 630593059
    0x70c0b0406230715060801181a0603060f070c020a060f0f0503090309010e03010f36151805070b0c0f030909130f08040e06120d020607050903032205 65
    0x45810b04600500200805000d82c074015031038540a51a4030380d904001840e5649400015000e00244658411030a0b140d40d610072140c40e90800604440d01c2d01c03410400001c09d10b08114180d500403410561040805a0240f0700d40c5807a2070880d001a5581d6009400000c07400c000324400f904404e00000c0303007000d81d941400d210400101100c0e2404203031040f41069105000a4665602402ca11100c828000e0000102010008040c005030f82c04444444840c01c0b0061690304028040040014a00e0100941051480c1070743d4500c1d40c8409503095415405558000c040480c5150350101643c083e0060100d44150b40c44182d52400c42c0d1003200255800e110306010b00850b03d0011055580e800401481012266910409101003ca91110840701e414044004030001003540c80907002030b140b45041a2a10700d40b100502800100346003c400ba1035022654000c000c540c00130740316030703c000d02c1d2900a0321060340d000828998050703120350b811090022440c0d49003804030126107600b07d6208031204000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 630595539 1250 630594289 630594317
    0x260c0d02041a181e13020f040920030708060d02040e0f10150f06030c090306020f0703081f030602160203010f0e060601081e04080715050a0b0303040f1a070c0b0406 72
    0x44c41403c1a002e0010410502e00c41e2024a081c00e1082014031640c40c0251030580f201005044030350042d040724000030b5032031503801030460040c041c450401034103a02c500c0c514103103480050455100240101d200b0000c005080045403a603410002c4078449103002c8035280301d100b0b03081c95194240e00c1c1548401501d000c441080003291860740e641140d40586210f806a03003020000c40142891010341800c0c04036001001000541c9031008103c52584a01490345904091400600d40307a00504030085c00151040c00e0004600c107545c807501202c0e40310000690f5100c0440004842c40218030000c4c2d4154a00710442e0508100c42d0400d6074569400029900140c0c0c07008015141464140c0c0c4030782e505410018542d80d0010701c500c40c240c00c00e008440c51170400816907121b500b00700700b070a160100e503500c403018400a07039540d01034020031400071406181001c0c2004070440e00c01c9124820318030120001e51b212102a0414401c4032807807600580038076902919407800c1412035000303101c1e410000b41c4201042d25 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 630596789 1250 630595539 630595549
    0x7031707030c1e11150109140628051203030907080d02031204020f0d03020c04050705160809040b04090c080f0606010903080307021204090b01260c0d02041a18 70
    0x501c10b40d031070726203e0620300741c68403215200e4604407065041c000039410300d98035a101046880e12030040c612142e0150360401c08844103942d03032184a256854158030622030f4564400ca600000361140c031980c45071198031803202c0480e40b0341c83d911103500032140b00300d0030b600c182d40400114440c4003c02c04450003141e8815900d50381d048080c0c00107005800603c00c900d410803c0143c00c0b50494001081c1030200241e001c0085e80040300420100d000d644111785c8410130b41814020705901038018200b036800c0c4800080c0c2c5110180243c1c4c0000c0c80040b00080c00035169a95901c6400a0140907000300520b2000e0b00c0c0502c64521940100103180c0b00d070512034040c4043c00148030f4810380040e9560a9614590340d11400b1a8201501000035401058880c0b14a03807c1c0b1406000200702c054404980305e18118000341c00c0c4140d1100c500b03002c0a0501e900391821510f464207c1d0820303204082c0340d40e60031600381113500900907504503040c01250540344082c421262000f8210080d03c02d0a200e06030f82c80481004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 630598039 1250 630596789 630596801
    0x10609060b070b0c030711100504050d020a080d0222082d0d110f01090302060619030c0608060a1a07020a23040510030204051303030606020d09290703170703 69
    0x141103403c643c000840c010300c001c001d9504184503042042104406c440007908040d0300310081a2419551000c210a01c03404010803856005140064101000a030f03c44500d540b080ea01c03480c01c0150001040110080d041c58401c3c2c0c80c80000c4500700717140d5190806241c54240510b841f901340d840107562450741013442100200382241c5030300280488080540282d40c062a070b64401e610a025220402c0b905400038043d41c60110f00c284d0140000c1d1410070104075156500700304034018120b103018140b0000360581000e50507662035080c0007240303a8a001c001020042d00d500040c0700f281c1184880c810400b44c52000d004090301c2151078140b86500e50b04101055030b818003003061218084665001f0b01e040603800b180c3c1101075401d500341e0761a103d801041c00e440068030740013124055080030f43e0130b0650511600d00540010710145c041627602070001003445445005507020b00c40d00c40c0d231000560f17100b1b5481e0303404460303401f0b041034407890141000380c0000740d861401c58020501d2400503020034483c0c40340c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 630599289 1250 630598039 630598043
    0x6060f050c1b01170f0603100b030c04050408040b0a11070b0702090f0703150f0509090304050d120c1707030e010906020d0c1e24200c070b0c010609060b07 68
    0x2c2001c032800602a20303080921580d0301c2d05111904200e100b03810300382e1801d2481240f0400600314113052020605240600282e2240c0b601854030804c0400b654020411045d60170b4125008541a159070808010507c503552003189e00b00000070b10180d445030011200240668a402522503080d40d0b015821311601c18240000e501880c0c45001580750580d510100d41c000e051450002189008840134136890a00c0d40c0000c400103400c440e0410461a01c5007205034010b1081004d94105031810000c1210600c03028002841c00c45102440b1001d68421400c0d01c0320706800420048901d4070610641200e82d20151040e00040c103180004200381d400350100000b01c50441e8003c1807002c460103c100e0b400c003103080f400c440088030004400c9030300320310302d1410401d24007440c480a03185502140800b242c009030020b5404a50030078100190147d1962a021003201c0307070b20421a6120907a402542c100f60868000041c4043d01080c0701c505110154840b40c10749501d81c0041114903120b05100210b80504980 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 630600539 1250 630599289 630599293
    0x140403120c0e1f090314030c011d19051005010e010617010303080714040b040602060f0906060a091109030d1e0215010b0c0a080708070c05061e0a0e031006060f050c 72
    0xa00d0080354001900d00c070701c1c002146460b110542e201c1d0b44d900080e21b82650000380301c0e400442d100000d41020300c9803c1d180a000d6004030b80c0009101401030301ca519008550014400003940070041c020700f030004404845000c041003101c1d44e143c8011724202c0f0300078080c440010f8080c0d039207800c04408100705030341641e4068840d50f1080d5030381c0104450044c21001460520740b014000000c1c030403403c0000c0e0002c1d045680190156190126083c00c0700500100303002042e52001d414080b4503240e05404c0d0052742c1c00e4000c003045d1900c55550000c100e2254900343d41d003500c580042502070b0380d40525181c0a641212484628420004004aa1341c440c0e0b820545c501e0036002004000305c02d00385001b080307080228403e6a4520f5001e450304103254110030307000d80e424071001500710200300380c00503210041c050403070b04603040c07180341852a24008549182400351179400580061194000d8500c41101e44005089540740c00340e0440d51405041148202d60202e05040c0ca010f440c0341c0554142c0f4030510210300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 630601789 1250 630600539 630600559
    0x6030501050708070f08240a093905030a0e0607020c0306060a050f0d0309030b181606050913020408030a031d0606030d210923060622140403120c0e 65
    0x91f0031440c0c0f10070321890102c15841048001d1654a480701600000c205004002420001c1c10408025000130388a1241d00a441c2072208600b17040f01c0d50158000084600e449a02ca1380d83c0600d06c002803502d030090109074400c3ca01005410b80d80000c2000512009905070b50803030b143e00042c000c00010034042e0301d0348585010707910b0200e400c00a060124a9003e40740c0742e100b695903501c400440d0304080c0c0d18600c00b02880d8441c003d0880c4c08000202c0c2e030807183c0383c8028400d45805401462401520703840b81c401c69052118804401103501501c0161903004203030385d0382768020341c80500180078a610f0b07810004041000c40d582c40c5804100c05203c0d42c806400f41455401071a021200703411140041302d420b4101c4640112408424810410b28a10a07242543d0782d004060740032003076040c4c882c3d5210070b50b4009000c008054842c200c110001c0b0802c0200b07000c502c1c0140341d0300b0024000010015034010400c0081100f40750380704100c41000c1103101c10400c011403150314100c40b802c1a90001e1504107030005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 630603039 1250 630601789 630601801
    0xb130213170a140102070b160219110409021212120c0703020a030f111608060f06100c02030a06020a08011a090105160203011e0c0908030304110409030c0606030501050708070f08 78
    0x85294a01040b0000044c5011b410f59200c282d01107003540c00302e00d03090b5440420040107404204076417000030b09002103c811113150b5a07010344e840d12009018019500d0b89120821034850481203190700e2090020750340b0398100580611300540207158800c18882c45400499030307411000007141c0f89160542d004d0841e4181c00c0d1420b4038010315070248182000008822005292000d2000d254412a002081119640741c040b1062030111b020341a880d50340004c0060104690b1200c00d0803071071500a040c014444106c90000a04216a010020300b6031800040c80e41d03800c65104d450700c4e060b10034911601840203006410052240504d04104c0c0c0401c4082007000c48003803108a01c405180d10050000ca03840284115007085210380c4001c03160603a07103605d41c0b80c01e031903040758109015180884c0114110320b05038a900110001000c08280540d40c0c0d501d40c1820b0520403402d020303040b6040303a07003030100341e58a00e0100d00a28088a8203800600b188021941ca00c0c850210380f0010f90300390707603280c215480300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 630604289 1250 630603039 630603053
    0x902130b01050418060302010f0f080106270b0c070602070b09150c100504021c020105040504020a0908030408030c010b0109180509010b0301090803041a1e09010b130213170a 76
    0x240004905002040c0070026280e01d40304d8030707807200301c03020384004c0381c103e01d148000b410200e02c1c41c4644041c0130390720f81c0e425100e40d80b12070f003981103440f980343ca2500a51061740e11384030131000d644070b01500510001c0209a101c509001003d240706a001264203c42c2d90309822622008280201e82591408210711003a62601c443c2209101c5090074804d440d05060030586031411050000c041002a1500200300c2985010100583ca400000503082e124000c0341c0d00003801482980100340c0f090b80d000c03421700c0301544203501d0314000d061071030220703071303585132684e6031603940307801c1a03e03000c1e842d40c280048203107075512401d90740003251031543c000103003a000d8002c000041c1100801e01c82041d0f58840a43e0b085a909010b8101000e004030b01043c0e6900b018140600c41d542200d80b5803001c28402c9007031102c0741100813691030210400300e0903012252502600203026000041c40d40381d1044c0e01e010f00304070300820741d4002d181c0202c40f015000c8074242d5a5030f140b20221041180401c0d07a400c00c0740d11202107036003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 630605539 1250 630604289 630604301
    0xf021f120228210507090504050406060512160b040b0403020402090310050c12090a050627060c040915080c04020d1404060b241602120106081c03090213 67
    0x110740070400c00100c10703040d5400c0a01e422100038000800f00c0b0000c000b8080f80819540040807404414865441c040c81c016000344814420a4042e903661400102408110740c041e42c0501002448004414a07000c80c01343c0d617500382481c1c03032000821168002010780d9010100d40031102d54132000d03402d062460702084025000b0310b10941e054021101c00400c054000e00c40c29126501c50f5503100c0d02c030030601c206030108850041040d00603a00c8140910b000c610000303000743c0e00a004816664203101800004000800300c90281c0708548036400c14002c00c88001000323001510020752003003050302428110131805d21458414040e0542088200d0740381c80c281030b0002c012140d040803020a0402c00c400000c4240f0070111010f850300e03592500b40580030301d0000810f00f5441503034004540515038048030480148266110741c40e640d43c1c0c0c0b071103050464a500c0c403550842111200200034203550340e0020b50302c6001442c0c0750b860005541910448003800fa114004103940c025260000070150394041d1402000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 630606789 1250 630605539 630605557
    0x15300f0b1e101a0c0d0f020f160308090307081525090608090313030c0f0806011a090a05090403020703061107030804080306040219020a0c0e150114090d0f021f1202 72
    0x201000340031380090381001240c1c45028aa55000c40f50f0f14020002820685003001307100184c1c100d40402c0446000340c1800c1419650000e2049948108600009140c8070a9130301aa01e03500803601a004445101810140b2800003802070554030042880260a12102c181c520b202184c0084420b0116034801c14815500c54500402c9925116903800c40000c40d50150344200d0b442c0118440522541c500740c17148038010402a03004000e154140f040000b210a070101403e0300c52600401c4a104035903420141a000b170902610050719403c0c2030078020344690482c041607601d242004c0c06066a0720b68141180c0760180c05070740b0703005c2c40d8660307541d10180c0e035101a10035170348240c003482044580c50848411403060310032600105204901c0e883c0003c0d802c2840d0344800c0300c6c04260010800c031031500311310f41141c51000b40b9111000414110215007140500c41c4041d8000c07469905110801c80c0c2c0b00e80b203030791303c0b030089600c0100e580c0b42da09000210b03124a101000040c00c4201c403880c20202c42d402504101c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 630608039 1250 630606789 630606839
    0xe04110307080f0627031c06150e120606030d052107081509010b07035c0309010c03020a061e15300f0b1e10 48
    0x1951500d84510304841007083c21942d0f0003030002d201c400201240700d02101118010b61113041108410501d441e40078032100d0156805481c81c090901011031b902c0300014014140380b600070316404031802071060800114050041c0c0740d00f81d541c0b10107070001401c6889000010014150300040310b4003105e690700b00a40f05400e907020300ea2424100341c0c0da049114400c840e80c1e0355103071030b900e800007003035090f48003880480e80070303d20100042c017a031085d2070111281071b50541821707924910036400030b0100c540400221806e144406070b4510307042d00c90701c03e07159018066508000b210b842c00c0e955030004084422003520b1507803040001c540194020000032601038040e00603208555001d486a41c00c0d00c200320010440044420f44900840c0020700c1003165205429180e13840d0a801e01f803000840008180070409403001006041a0f48203404000107400e07940711104a98401c42454012401e0b0816250306668280141a0a1504451980451081c1c00c07002c9191061480d0005c0c41048545101d1001c5203c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 630609289 1250 630608039 630608053
    0x4140c030a0905100c021606031806050c0c010929010b040504090f0f05010903030e1f0222030c08150c0a0c480e1501030b100807030609060e041103 65
    0x840014404c4ca1452406500640302c55032070054547d0040c61540c02203000e0514000c4900008066540071880196002e480081d071510360000540c514010401690065800c2c114041c00700a668441c140750341c10881c15254034280206020043e54a09000d18560204144010012450240c200440060007200340181e203907841d4441d070748404420a415a50f5a450f44866004c1503414481c035100461118003a110038031080c6c14080364102c0340b4411200894020031440139031050648415078111540300c0c41801166a8600001010b040d44912030003402043c0c0c40c1703c03d4948042c200c6124454031070f089480c04808003419541c1d464008400e684400a40c02820f010038580346024138800101c4240c0e200510564003410b1544124003d094030b0030b82c4041c2c080060459072400c054004000c0b1040d440b2207160203004800401540009a45c84920080c03512404ac2d000017401e07004142d1a6802c1c03000c1a21001c0000a443d03e41c410303c0200540c04000401080d8028003810211000800f13580c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 630610539 1250 630609289 630609313
    0xc08190204030210050304110402030606031302032d0609010b06070f0305161401060515070b060d02030106030b090d050406050702060d0b0405100509060d0314030723030604140c030a0905 82
    0x113920140b0028020410000030f010034003948102e4001c1060040704c00758034500c1c01c9808208180070181042c2141441405201d08641d42030040c07031900c804203600a001524035100c1c5030300040e0300304128406070141e10045500c44406010b10202290050006403510049554054004070072210130b82c10044148802e06030300030003210800c4031b03a009213513071644903500200007421074032503a000e10f1180e03070005c8040c000f040004041d54407264214018111903642c86e008134900c5a00710b040250316501c0c0c0794011041050165105000d04200c1c011284004160001038940344518041ca001068051050000600e0800d0003482c0c1d48035a900045902c540e0400420306039981034502d503042030078204041c005800d0a01c2104d0384810101d910400c940a2510042c1603080b41c60903800417040000300180702a0300500e0076881e1001c01841e004512040c0010782c182c2034000b9280c1c28071442c00c00311680881c480c19403000b030080704c0380c0300310310f16503211150050000c1c5880841110785005c0c2e1111140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 630611789 1250 630610539 630610549
    0x5100908010204091d0607081305011803080907080303060109090b061b03040602010f020f04060309170a080114010c051b0102120c0c0f09010b030606071110020f01050106030c081902040302 83
    0x1304160000440ca854800c02168400000200080d00a40c00311040006403076120322071540109510702014204c01d19070038400c0c0988508400c0e0f10344a04501e000c42d040540c000c4220348225030305010344259a0b00d0b01034443d22480181d0344603001881e2240b052140429940c000841020001d1925160005034409018000440d0701d80c607445800100c1c040001d00d40a014907118240400741c1146005885449900140101c0c000c04c0101a078540b400310801102d9002082d2030020464165200c40c00454020030303102090145014007a80c4100401d09940030309901e00361164802c0180c54801c0114030503110391542911070390304500c540282d0b410704821020050843d00e0b040c1c005485204142c0083c40241210340d0900f0303010300040001000122003400590760000c40496509986804608002107038030f0300c074045180d01034181281c0c050f545400044030314a032460b040c028442e980c6c0e2a0426000c4074000126080411075240c005140441c000040d40985041d90320014107183d01c94010031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 630613039 1250 630611789 630611797
    0xd0f05250f0308151807140d0204050f09070c0f110a030c17030403080d020d020702060301060302090102010c02010c020a0209100b0408031803061506031009020f070b0a06060207051009080102 84
    0x141d04551041800400d1590010090381c2c420035054000251680880101d18074030054450281c00000c203e02203000107109032028418043d0500034144c03610840c1200400030750080c41013038850030b00050005070301c0c00c007486000c0c402c040d40d4480969040300c0743ca03130500c10500000119801d006940e50108685e48510f0210065405030b000c03845660b05000c40307507400c6460f441110b001940f05000c1040041c2c141000c031101030707500d1040581c4410800c0c010034044d0062200c001d50000021002140559242d0b0152400c10001d038024404039000700c2050b802c85810b02d178940010b030444907002c0007500b410000345800241c140d07052900070303942c2c00703d08009400541014909400c00920411160321741141d2800c01c60040740a00f400f03040040d11300e000c06486094203030007a4001300c0003500903014030503980b00501c0c50003403e640c0c8040c240b0714154641e1280314121400c0e0181c8002c543c2e00c02480c85136005458a503001002001e081c8020404009110004c04040240700d03140400e100400f80050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 630614289 1250 630613039 630613043
    0x20a05010e011a030c060301060f0203040909120e01030b0604060e0f0628050c1908070c0e010603110705030d0b130603030807030f020a0914040b03010515030d020d0f0525 75
    0x150780c030540802c0103e001240c094144641d1110091107115950300007103e0440c1e00c0c5040404000f07049410582c114042e50740f02001c403c0c0381000c184203100f001c502440c254011580c9282d44101c40c20015030440380201e03412380d08100103000034400e0b940958107071000004010074109800228000003172881d0300400d11060b440e00c070711200c059200100e44a00c960b140b0341c0c1c01c0c09810060000c0400d27a9880e1030881184058500baa200024000120115030b02c06412203000800d0035140d014500e044c42083c4118400a8a80107030303074104d8643d4000f541d40040d4032401441c5001244410180a8540408640e074040e03d40f5410035031040407489924004c6200703032601c44041c68040030140031034292418001d03295004001604410f5840004002528141a800c9669021820100700200030f003501c91901507190205109903c0b1195400c44d0084000318101e40d4a41e80c5944120784038071100035a18042480c40c0c0903556511b0080c000b4060844d2100c04001c070b120b004c0800c88013449001d03002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 630615539 1250 630614289 630614291
    0x30602070501150e15011d120607120b0901120303141905060a120b0703021b03180102030a083c0901050f07020a080310050613090507030603150c020a05010e01 70
    0x20341d001000d09030f1451402001c0302c0d5403400507443c1844880d000c401905000504106041d44e840541000c51924030691407406450001c161140040c265600d441c295800c5000c154100150b6000c04254014404018400b41000d400c0ba4a401c00068401d204910107d061545820303460400380c0b1419596445003650301da12042a24010410100315007014200034000c1c2004078080c8100150050545052030780040001c040c0e64404000300c009004a030b81c0d001424620000b0030500c07034000070142495000c800145411603000c02d0059039288940754070140440c000c0000100315000c010344003080c80001e801d507040c46c0342c0030040c1c0d074111a26034418130680c1080c000612080600908c24198080450001114903041c00b10020b0760300d92451400134680390000000500151807030810078024400a001651240006184000c1d4008a4014031040d10700e0000003603501032090141e40c0c101ca4100f0180d07048101c503413031000080c0c0f18005004043d0302c135041c0c1000c000752092080d031064500e9440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 630616789 1250 630615539 630615551
    0xc0204050f060303341a010608130f0609020603130b2d09030408070b030103060f11160503090918150f0403050c01180605090d05040837030815030616050f04030602070501 75
    0x6c0302110107401a000a4204115001080741c1544030f4200781d03910070740061401e40341c019189800405401815070003034000c040401440000d1107000c00c5101d00902c0782c0c150004540c1c6480361070000d010140c4518260600c0044811000e641151031241c06c07440f00e8017941c1c942926041070f986480d401d81c0c407a000c0104008010030a000c1c0611590507007a200503020b002505030b4820014013030041d10a078080400002d0030410411400b041120310f40c2d10702810440c8075180201c426107469000e4440c0e00407a00508013000940c000c0244181c0c410584204d00b0384850700c0703a072012a026084813014511940d42c0d542018460901001041d0351a4450b040208052400e034040d18200440355960f4018401c0510007405860b0700403c090409041b4085a100c00d800014182c022204141001960012102e00680c1c10b00d0361142105104d91901d0a00c00e10351022101490ba50b6001103441340e410200504c900e03021184540e00420040310841c9805050948075150031049900400c4111201d030742d188 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 630618039 1250 630616789 630616823
    0x1c0210031e111323040209040e010e010606030e062e030510050907140a142b0201020106060806280b2a0a03050301090b04020d020a0c0204050f06030334 67
    0x43d400005002d01600080300d0b5003c0c03210399441515081d00d4544190303008102040345407103983c031140301107807450024881c1c18140082d85001b802c00340100360019042900e03c2202c0c420000f0380500962130903420315016411100306a4844c40c080200402e02c3c82e41d40000404201c5c208000a5188800f00000400b81000b0034101e140524030b42c0071940720340900d4030b10000c070f82e00c0c17107004000ca03003090380c0854602c0240d4000803c40350036411080c090395071a2078014900040c0705007035035841d0702c00c1e0020000640c80c1c12007502e510384120b499076400a984400d48000d080000d124a0720702c600200c8184c80c0b035407100056102a005902c1c01d40016502103100142c0c0083c00c0404040301140c28081c00582a654600604c0381c0f1050040782d040030388581d44c820940d2140c3c0d0407a40340c6208040115140d041c800030080103114030081c103a1049003480046150354004469150060b11300400071840d014002c003400202c880e0140c045c5426610300e0f106401c0390147c441480d01c07074912503a41007203114140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 630619289 1250 630618039 630618067
    0x50a0b070b1f09150602010e070605090307090504080d110403080708090414010b12010e06030c0d030e10031e0e0c0f0415030813150f0c110d0503091c0210031e11 71
    0x130f03a02400131603041400101d180c0c1d201003158070076994503141580e0381d100700c20007103032809038030307510550442d45032004200900c0100b5020308020518524180162a01c55a6031603045c042c902010300030010410810300000c04600003040c3c1031030003a20100c0c609002c126000d41c0040c0903840b40080c9070740010b0203801c1c0c01071381d4030060250070100e030171030024100072001c2030303840c40610344c0c060207903520407454010f140c000d110030303803410340010700e41ca503001154140200a4449450600790031041c1403c0f0007a07081040c010402402d20b140010808120b0721003c00c0003400382515580e801660340c0401c21681c450128071000514003680005560384040b400d40f11360b0022070740c00307403c03503600d138003c5000b40c0c40c0d0040520780498258070300710540407071a090244005401d08251603003d8800b8034504108400400900400b003c110740461801c0d10750750340c0e14105202000002d5000030003620040304c160082d4842d00c15044800503400d070943c005220401141d0038040071140c514004100c0005910300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 630620539 1250 630619289 630619331
    0x527191706011d061302161110022107060609050618010b030f0c0d180203010b0d170a110d080f0705211510030504060501050a0b070b1f09 61
    0x444001c09480d89415103600107002c0d542c0e100f4624000f41d10104510b996003243c42048000e044100315030b1500f103079410050744c0d001c1510455010240c11024031040c60100304a09001d03c0e61f4015244521200c065921904000982484c141c14280a4240030071b000f4450800074050940c4002801c0c14031004111016640198080101d01010018092080c501099980007002d481d14284144ca912460f0703da64002c4000204000d450314010303140c0902d001203c41800c5001b54000c000c800010302c20f00c80110700c01c0f000501840310703d000761011510040001c203409040f9107040308005024460807030400030304150400c00144800280010680d41d00d5654fe04601c80342441440e161200060080340106482c080e0301c8036405500050b004611816001010300006001180d00703140c50708041c0c000c01e411760303040e80c0503440d0400100c0c46007040d00c4000203452503554a00e00300080e90303481c0e02440c3c0005040c51341080003480340500100303210f00c00b40c007d005992008180001c2d0324000445101d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 630621789 1250 630620539 630620579
    0xe2115180607050a1803140309040f02130618050a0b0c06061818210a0801050f0a030b151306080607020d1b1a15130c052719 55
    0x1100b400b00d03850f0003c040b1480004036042880c44c640c01201c03ca9201e012551019000c00c102d1105154401400f00040c20540c40450742006a111001d586004900030044500e03c0005c0c104006e0000342c4c0a03820302862000703900d603010401903c5202055202c002c0703910a40c01e00d0408100704091540c1400220ba2042e410307100c107c15003500054a00c0c03000d20251205406500c0c60a901882c000c0c00d0001e0606203940d0524082207078076078010f03d100360307008030f41c4140041d81803400407038580382151501c550484000c0c100158103083d40c942010801c80036041208110039401900d199445d00241f54096006500b80001c0481c0f522002500b040f00003002c820454012180045400e50052a01031040c800301c41c0c6003190036282d1034454a40202c840310361210188410030048503444d1996211015501503c282c80a424100e01e8401a20040003068012401c14804040441e036918004800d000f10144180410885200401c2512144210b420400007005000303000c501e20f040d000c42c1c1d03030301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 630623039 1250 630621789 630621793
    0x180f1b0909020903210c0618070501020a0c15110a08040e07050702210c0303030a0605040c0c0302070e190e160b04121101030b030d1115070e211518 65
    0x34110b1000a4840142c84804050011804440710541c80c0710020f031002e1b0a601001c0314400c1c10b0805440b18003150005585015208400003c190b55101141600b15281d01071010a041410441400203080c800c1c0c210104000c0f504d211881d603034001700100da240c180a811102d0b0750343d00300300780402031140091140c0c06200040204070010b86440c2c6070320503403000c06085800032121225850303043c11210300850313505100110903c00782c850103900103c00c8500489041104d100001000c0d200b01202200280140e00005020440601e8085403581e05c0702c401c90621f0b040e6101240e001040380d620000360f004541c0070904810040580100985c0078000d40c44116007400c0c0b03041845000c0340601500108550740d001d00f01900c59010303401c2107081d944000c0c181ca405220314003004161100c1c40700c200c1124424122014030381907900000301c1c0515607640e50303801c08100d800203000342444405030552111343c1c2550700103043c2009001d1040c0790302514010011a0401440d10190304440d0b19a0001a17 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 630624289 1250 630623039 630623047
    0x60f1506170109111e04051e0f01031b12140901150e1b09030c04061508130b0105040506030c04060b04082b140c01060e2509180f1b090902 61
    0x80307034041068641040040013690784180c140e1117070800324007456001c640c010204441039070907401030842800b2440ca06448080b071020894004405071428514a40000343c2124100f00701135200c0d0441a15102c0c0000c0e021940c0c1407074010f00e810098040344d801c0b01b0b90350b40b1030040400081c1511590010422122030501e01e0070000c00044c01100005240083d00720001002000350314203006424507654014001c0000b40d5442d66040800104010301000080c500400901c2b4040c82d0700e400030a10382c000c1280d40c0583c3c01c002c00c1c040240409800240e05100c0d0001414940d40c0368002c581c00341a01c462929112894a11000e10307103401c0300c42d00081071143d8090300c0400d054044220032045d09501d00f54000070003980701d10007948110102c640710b55003400804103010a403510300900a550340c240f011040c40050542c00004100f2407465000180d50306810840d0000100010b004042210300001e00620010b10324030441e08080c01c804041083c9250f03408010f900540410001e0a000b1029440c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 630625539 1250 630624289 630624311
    0x15060503061201180809010210050c070f14011104050a0503030405030a1b0317040f05010e030c01080702010b0423060102031c020703030605030604031805030c060403060f1506170109 80
    0x5000c0104024000c0106421000005800b50001c4114040f0b08020b019610840d0511529940c007004980e4058480c1098102102e1010b2048030720503000c00c1e89140c2001c2d5103983c2c0d0040030190400c1078940700f9810640b444d1605080c400c402d00c3d00c0c0703801d8074682d65615100034001c4100090340180c0c42904107010070001905c1c040380910030a03038013200c0803051518507035400c3344050280d00040d0805203d0303a00900c480103044020810fa410b49500301e82c5032a900d400441e00c5950140440b509034100005404055000350703060354004000d8000072034082e0b010404102200e03034032403131740c42c50070100202102926404150307160032040c2171000e140f414001d090240c6c99405003500c4000d01a60000b901c00c2454401d40c800405410002c00b80c8020b410f0600b4000e019a600340781c3c440c01c0b001142000034140c60001900e12050001401460a2618545812004210001c0441384003610303208080004007954100c107004d46840d8903001e000f443c0d850400862030034140c209400f40d07481c04010071380e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 630626789 1250 630625539 630625547
    0x30c060304060902041b1d0406050310050a20190311180102030403120e0f24130f080d080c1806070f08030a0b13060515030a11030a0903031506 63
    0x5841500018007007000a914800301700200a411074050b00c80c0c200144036208141e221112195144403100c24100f030040074010041100d00600c2102d40c55401456050118900c40d0401980904208400280c00c0152103052031803107102e64100d08003010014803840c4411400390700390748030700c01c42c5000c11a9034400301c540f8515100b40540b0028a001c0a8035202d9180c0c400c000700ca0181d540710121805441c0215005000c094103181024400e495005000b142d5040080078800440000e44880c7c0030040309110480c8194803c840b0481d20075041e19004c21220702800042008010400040515240740d4400800c0410083d2100c0c8154004112090a854442d071501a0401c0d045940070390350b01203407130142459031607058020040c0310b010040041c215840d9101c0396040c01d050b94594590a070707480b104000c46045004e56a80809003c0b52015a01580405554070910039a0006008450200c01130752a400403280030300032135200c00b0314504042e4035014070030700c0000346000070f0220317420101d010b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 630628039 1250 630626789 630626791
    0x90504140c03041401060b071406130201020d1d1c12030603051209010e0909011d1606030c0c0c03120908060601170a0f090503210c0405060906070b0f0114030c0603 72
    0x903000400351341544010300001e602040080c841b201240d59591420728026402007144041002e15004400020341c0042049425050700c690507400391000c0250514250350f4410040c081c1c0101941b404c078a0216a00ea0114801c45000e00300099280c8030395501e012107000542151050805007800c0c00ac00009a0001c0d1410400b46086038840d120807000c001280d50700b0000707501a03403021040303050042924065005422440c0303000c03400701811852640e825660300d01300328807601c442504002001407038441c1e0700404100d52039107809404039030107071255a450b415903081603640c4100d8481180080d45c02c51201c000404004000d0f00c45844c0c04800681658030301c00c02d101d1002c141c4400281400c82039400f100c00080c100b28100034608160411719980d400c00107000d8a503801d4a80613403485a038405003d40b00700c0c0c400c8c02c03143c6454100320501007141c00c0150310b240c20110511214001443c500728003403284040f103014126070b6240ca2001404101000300d028000d8010740008031107030311080100c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 630629289 1250 630628039 630628043
    0xc1903142b0e09130602070b07020c03030702090624040f06020714030c0d110d061e060e011a040b03182802040504080f120412020106180c09050a06090504140c0304 72
    0x1d400f9075103400f201440392101c010700130051403000490104000c0c1c4c044101780942d149608031101d0000c883d0601d90740f071091090107580701014500280c3c0a14008407982844503100408107940d482c0c0d041e40c86010b070025003280c040e00350016018852240d0401045005201060703040c81a1180751011944600420a640c0c0c020310b124180328051001d80b040c0141c000310042c061a401c4205410800300070903811883c0b0a118100009805040c4000c0c001c100544c1c04c1d42098110592805081040c074145000381140314020030702002030101d113810081c51051000250003081d001d5011451402c01e81c00d06440504207220011000c04064500501c403043c542c180c0340080c8a850f02e0816040d81e019614201000d54000140481a2981151030038040da2155548250040c00c26805900340c6881d4003d40301c44040721304442c001c03809590861444000039040000b441901c41e400b0a0004402da0000004200d00748170412060130584500d403540d560001000016040941210445120143c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 630630539 1250 630629289 630629299
    0x50a0302060a0b090f181f0b010815030607051e070f02010210110f0c100f02091f050d021c1a0a170607050a1412060a060c050c1903142b0e 61
    0x612040301d0010010349800ca01c42035103800d80c1005402c0c034100a0800d2105041c0040c64100214000c08bc11105948401000401800b1a0f80c1c0707003081140c9070f07082000061200c0d01c0e040451340c1c03003004c04401800740b980200b0040c2c1c51000c00b4000a031030004034145000c42d0624206031030b19242026410340b020811a01016996009240d511a150100e400060410036141c408a028841066401412400c90543d4440d140b401a000d076000c02911010050300070840c1048955807103240c650003003481e61100a005410034000c82800c1d0101c43e003406540c101000300494460280c500f084140c002000034010451800b500c20300403c0d124130007d00a8814800301003091074105005413090020085144c00980e25051400c071207060000007603400354010107010f00040b034640e00c00c0c11402c84403a008001441481c48010603c0702c42104030140c03030f100c3c038041e205c040001080751580814400d0280024401191084451130400114132408542e0765201120150310300d402400c824803141041b00c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 630631789 1250 630630539 630630571
    0x3090c1c05010204150806100206040303090812090a110f0a0b16050d0c1b081f1b02010b030607080112030c1a04050d0e0603070903060f0603050a0302060a0b090f 71
    0x4910000e404045100030007079400800e000c143c0d00c40c00c00703034141180000c1c2d072164140d4032540d0034071035000044800000140c1120340005e02103030103a00300f104940e100300f11083c80c00e000a512207600c00e00903110b00b07125030000234900c8140b03c50240d1020550404649808045450354000b40c4001040c0c031564860090108020300050f04540140504c190001d050300d00d440c60f00d0320001c0c8a05100d0304215004100120540c13120070b40e42a84009a4000400400d200c583c2121b256200c03031411034540700707526101c4030b03191101425094004803250315500045135152040080504008004125104000b000001000380010603504103016903050700b081c850f1680e4a04126808943c00a00c0d0b100b0600c10708188410407100040090b8481099943d960402c0441b600300b116602c410f450820000310010380520200320b41c1e41c40140c0d0040040e00000348656a0340c5e0704e6090810409058015801200c00c10207003600d14005c4841503002140c2071583c2c0e150203824002507510151034040d14100c264 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 630633039 1250 630631789 630631819
    0x4080705130908031e0c0403031d0d15062405031902190504031203140619182412030e031501080303010f0902030c1e1b0102040509070503090c 63
    0x2a1000300307000d0b0403048581c1d891800a8010403030f8900c0d025122a8222805c0c00200d03103c42a030103407402e07640d1540d03460101c428100c00821103030800d07103405030340a00c0c800301800004604070207901074040c04c1701b00800d59901e0030001d044a4942c500b4940080c1005980310280c880e03009040702c0d40700340034504a000c00440c15108500901a0100300d0034480700301000c9507511504800640110382c811044006004070301603003102a100342c000e0b251038110101001c50024504040c06020050080701086142030342c0f01281690701303510f540494000c51f540d120b003000e01000441c4e000c06e410110300000020500d441c8140482032504003001e02080011040d030380c1c407658140100010104403041c000d01c01c1d41c41310709280e101d6000303124841803c00c140710002040d00c268002d6034481c20707400c3c4056080200d00da481880c4103003820346550b0803040400030210004544445048100001800180c41d54240024447c030203401808140502c03500b441000408034000443d465000d00544442c14407030028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 630634289 1250 630633039 630633041
    0x20a030f03141201030204050603030a0c0311101404140a050304050402090d08120a1506050301090e070803030a060312030b130f200d110f04030803070513090e0607050408070513 78
    0x80001d10b007020b0b0000409196980040b114203050303a008580c10011900c0e06000c02d0340e41d00c07a014180d408035000840c0c50300841c3c0262052008503d14600b5260100c0040b01c00000b1105607441c0200c600c0c0d422070500003480300c480b844e1002c4480d00001405084555110f11380d5a015a1051a2049400040c052100e03140e01c810401242e9104003165200e0a0b504940c2201c004210392000380280703030403600d01840c0c80d807100340700c00c403501340d01c2c0d40d0324503400c0400f540060880403141c0c114038801c4003070015403810204002c5100f081e4030280001c1c0d280c00c500c0d00c4c0920030b651300591000c2605060360020b49946480da0081c500541d84000154410704000041c0074060307400c0302e40045800d218104040c0500c0d4801403036600701c0044100315500301c84182050341e0280f200307a03400042050100f0b10000e0101001990440c5550408905154004400992420b03170307900480140c030f031110620030800030100304c0180c100310141404c4d42418107000c026560740c2098402d0501c2008801201540102c0e2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 630635539 1250 630634289 630634307
    0x2070e071704050d032009040b060909070c210503160c1b0807121e050f070f060e04090201120b01050921060c0705060103170c010504111c020a030f03 66
    0x440100c0200307a140904141e52103c251846a10200341800b146034107400300c0c1010f00700d02d848031071400d605110240007407000074026a0348081e003280c0c041140d94480e50300c10340302c244101020341d1041d4001c03802c0c0c40c00303410f1481c4010101c445c0c48404446052100e40180a5a620400c448400c0b8288420884200c6000c40b039a0030180188000088071491070001a1089041e83c0c009011600956030b41d12400a0094884102a20044240c01550720344414098450100c6005500b107422280c01a9035003418031120707074814220741c0d5052204002c1e454105c4c10819084600300e500700a8600c2d00c0c0c00180040c0703070155100410659410f02c00c0c00740e81c00b400a941410001405041c501000030400d0002c0805201712000e1768408e9900040d1400c50706000c0700c00999004000d041e440c0d10316030b1110700201055200100118080c170101c180d000c030074807442d8410b60040410401c101003800c14030100c10b040781420b81d1010020f9142c0c5001d62100360403441245d41c8107105136130107292030034100d8031fa0b04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 630636789 1250 630635539 630635567
    0x20a0201120207120f09120c031e0503190f17010e0a0f02130f080a0809041503060212040303060b0c280512070c050109081f1512120503010602070e07 66
    0x210042c03803484c2c0c00d5806000d41d04c2d07242194907500d00c0303607807034501c054215844500700820194070780505000054501c4410b01c40010710300d1913940c10b03801039950903080d900304090071070200c0d40740100000d0290384107042c0c070328040c9503043c0540700d0340e0301988821314103605000c0c00085503244008030740104210351001c000074031049400c64680420000c0b40c040b881e07403881243c0c030554011801240c14440880c4c040d911a500040052401d1406002d11018042c041c06000301340d204804000082040c500080c2040550041c91805a14040ca07001e412a0f069401040071904284450000d2400000300f030080c030200126020045802c0d102105000c1c0a000710007003046c02400d021030f5044000c900030f0030722603106004074040b0300c3d00c4000444d0b44803c103104000882c6d003c85840442da481114103640c01c50409030002c03800089442a000d10a640341d800400c007625402c0400090040403950003028070150319001d80366514043d00203681c7c244500581c21360200d19000700e01501c2c02402c178020740f40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 630638039 1250 630636789 630636803
    0x50c04060807082104120312060b030901050c0a02190c17030c0d180905040c0f1d0901020a09170a17090102060a14011a0c03040f08150601020a0201120207 68
    0x107a2180c241c25100c2070284182c456a01c1060520155800341c2003440c00c4064603512941d05085ca803102103406141000b509a06108182042c40d6180d4164042d01700600000000307203540c0c0c14603803121400c40d50024030440f43c4d5403040c001110060790110ba1425480c1100b42e2000682956003403800703003c255544901000340c0c858801c5040b800011001c4c0100383c03018420703907032442c3e0b049034213941c0402400c4d1503800c490b148100911908000390700450300325010304581072030702d900c54544484d079070103a80014241d40e03898250320900a203e000f0040e4052a20002942404611900076003100700354003401001c04000701daa82180b4000308105c402440d00b00d0004038440d082c03a0083c03202a406032189a0050040c100040d4528402d4041c1d01e0001111141105031a0300e801465403020512410301e60003035600700820700d10400100040e1000e8070180e40080304182c548400103207404000480850600364ad8010005c02d6038000c2010706100381c0a080c0102d4003c20414031800034803801800034002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 630639289 1250 630638039 630638051
    0x3030405090a1b0f051c18060b0f06070803040b061212130e06010909020d0209030a050105060a0611100b22050126120c0c090a05070912050a0f050c04 66
    0x240030b69030000d03050154081200c1d504110403400441d180c00d00040302e500030450401a80300f851071309000c0860404250800042e491144601f090300d24044810140e0351107488080e004594071346075401c0c1180745c404907183d600e401c1c0e040e40ca006a6000042c000744c0102c3c441400111907495540460020344c024074150b031410302080070380710902d80060400e90700c1e01e20b0003030020410b0301d80701035024002c40d0142c607103002451920b1040b601950003a03070500c401580901280c00c0d1034408000554825214100204151401c2e01c00e0044288066002404102d0745805103040c901b00411008540003111101044540f00e42c00807030105e292415501c07014611904e101c42000038180d00035410380c0c10340d50850080151641c200840d922402c045070010b40c014140d1041c01030750502c010a880300a800545010034401400105540d00464000e96017a40326410000354580c04031605000d800c1d002403e030f00124164490655850f00034200130816080c0ca480302c3c0030300000700000514451300070000c0c0300b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 630640539 1250 630639289 630639301
    0x20708030d060906060c0503090409030e101119020612060a050d060c0215151903020919060b0f0a032310031e12120e0105010b071e05030313020303040509 68
    0x40200f07125040c455844c000c1c0c04100c0714031844040707203010f40050003103060509010400c401409110070031000e01511850090681c0c840d2000000c040140751500d18611290401160500240c840740301f0a42c9107511800005030f4410040e074900075040300745645c070740c0c1d1a0000f143c180d100035044540e0209407007800d001002095002390b08940d4460303094500603943d03403582449a03041520100e5007194010311503003050419a1241d0386403031124104003a44e41c0c1d281c021070300b46003042c2e841645407400c0c224200c42c07603021070050130010050308065a10303195640e0100c00d0380f8060f90146004054032160610144500d0102e4001400c903101d5042d0b03100d05001d84070b48403a841c0f91004450500c801c2017120003242d28920040301958025541714118444c18404980e103480d0b065140502641d40c140c0641010001d00c1520302910508200c5039a50304a0b0424014403440e807200c00707070f100b00303601d11541c005840441900c0c2c0000603850212000000303407001034214003541c6c0101e50048019010841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 630641789 1250 630640539 630640541
    0x60e07090b0a090906182313020d0b0a0903021903080114030c0406090b040c03090b070503070513270905071701020904051005120a08040302090a140f040308070e031c020708030d 78
    0x3400c40c8819001c000b110051288100c40d907c01903503c010b60f00710803000480c0c1034024060701030780620040003248a404695995910610142c0340580260741c0e540034502003640410076014061036291400440311425640209000d50501501010110b0700d12030054640341040b95104400000f0404d000c210344a13440f40d03009044105c60544a0750500380c0e00300600380644251500680c228404091aa460013026242d650001e495042000401c001e05062049402e80c0c0401815100f40c500313400b4002c104544402101e4000485a22840c2c0404800024000100f0008442200c280040f0044042e2440c5009016003415141c00c0343c20003040204201d410b1040303406851045800100200c801140240d13140c0e00c9200c0104800010081032016140050016500c1140c500c80486c25207119130030305007555801e5500c90f00142a4a06000c1010742040d90030742e0001142c601459001e007520300082c0c0e1a030303075282940000d000742048204035510901010001d00040422241d690fa035040f0004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 630643039 1250 630641789 630641819
    0x120a0b0708061005070f0c21051c0806090423030301091a0a060810030c060509010210021350090402060d0b0307091d01060e07090b0a090906 62
    0x68000307000382000a03020719101403071448008a5075295810a0010344e1004a145081c1909032052070303007094001030a01c0d6115090f0300c80340001c90341c00300781d0f20140741a070301d800c0040081080341c40080180359078080d80401c00030351105085600d0f5000e5246d80c2404001d9000030200c0904440c4400d4140b003a07520000001c5048488021080001c8810b510254400e214607050856202401500c01c01c0400e01c035500c1183c11204501c81040142c1c2d882c0d65200c1251502e90040c8007190010680d40c1e015a018003a8480410200005500d803624004801003554098000e01800f0701c10850f9030310700c4507160000392001915104892a4004a010f03400001880d09c150b0300580e03890034421410541000080180240c0d40900101e003484800319011000d00032a641664043c0b0604c0360002d00f10b0050300445000f14901c9a00c0e9080d40583e1050a096910a400441c05c0490441c03e00610a9002c40400b0880341003411050702c07450611422a4450500e9019998160a100020401001c060011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 630644289 1250 630643039 630643051
    0x6150207080f070b0a111f090209071e050c030d020a0e120a030215060d021e0114070f0b04020a090507080a06170606060f0c030f07060b090c030411120a0b 68
    0xd03002a0007005525030782d60300138007a554070050240050074445004500c140131a0440c4815640b842d4110110a00c081c0a000703c00c0801d01d4440140c40c09500307044d20000d070000c0312b6281aa005000c950315142032441003103110020803000040c0c900d0060700a100b07a890301541510155511086050002d10005a1000c07492040103101412034134014006025820140d03d030300603000010401c40800f66903980206003542042401400c040180c0d00c00003803080110030305500e8071000d2020000104040c4070194000c16034030003004030300c001c940c0444809071029800b90a0045960b107500c0132846940c4c841d84002d0203141080140019250499881c48c0b00700c080800c10025070b56242802d921410003602d0840c01904041d01059140c18184001c1070690b03844a1024903118424041601c0c66000b0402510040340205105040101da400703103603030b012400c95194225041c040f0b250726031448003070402815080d03580c5c01c8030a142c50721032550220103200c1d000e64103c1d00b9681070074004143c00300c401c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 630645539 1250 630644289 630644293
    0x60c02070803070c150e09041b0f0f230a0e04020f04020304030f1817010f0b060408030409180f12030b1212071b08070311060403110f040615020708 65
    0x10208240341d00000f9076085036000807100e50060700d84200c00c03a6009450034440304120030200c1d1030080d9162851b066001e1441227516183c03c0300c12000d107400c28035045e04040007180300000100204803c800018082d20b540c0146000e410500e1201ca4418035070b10781c0400e070070215281700080d803103048040d607a02c210300a69113030040c12103400401040b0301c8101c8006000c03c25400340b45104621a04180c0b6000591070400d03690309031a041400c0443c01103a035042d030542c0d1540010b40300300640340150107803218251841c1d424203090050b41500c0340141c1c01000186680d600540702e1188561860f1054190010801822100c0074101012620164860100480d0402900c48410b04040598456208241024140b140c5040c078450107a68020282070720f00d51a00c112090308244a52071910083c800d200080c200e0324650300d403c02040d000c2009440c400c030010300041010410608404c60389000c12900b80b00283c0204000030010181904445040e4294001505943d600002c1007402d58003d402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 630646789 1250 630645539 630645553
    0x607080f010e0f04110303132c0118020904060609030303050603070b0414030c150a0801080c0604060c05012912030f071209170a060507030902010f2a060c02 69
    0x42000403000284291581190440001400d9030380fa0f42401d0342003442a0350381125034243c01c000a1961700a80b124614084e00310004114030004a0710342105d0005540a0064030300380001c0c401c0c4074210501c685442c40d1210080c00c0612003d9904542c00603d00600410100d501c41e4402000404503020403008070340744c00e01280302444c0016181e0b0031500e00800851a090401c03550700a02002c41c0c0c241605842000301e0105103a4441c400080017500d007052280d298940d60600800c8400181d120b5280e80e009000c2c00c0c507454540c2c008032429100c0d1070400000040f00c61600900400c215603c240c0081c5501100203842080203a60b03055030b0708100c0300e05012401c8194465100d20400358160701c050800c10801c0c000429501440303801d4a0030381406038220b45d40d554048050715007001c2b501c2090b008480c400e0204140d500c01c0d150491030901c0c0400c4180038503400a0219804006e1080a200003561018850043c60a11720103030050841d80746e003080310914020024043c005090000745c0100340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 630648039 1250 630646789 630646801
    0x50405011d0114060c010207050321040c050105091315091b0e130b150a0810080c011d060403050327090406230708040201020c150a03150314060708 65
    0x8a501000000c001e071040d600e910b03141003086000c02e119402c9400a10602c60b5605100b4288050072000d8041c102940e50380580b40c8600c4021f1400c50030324108c0200307910501000c5800300f1121070680e0006c2c00d000e940c500854000451042c01c008101440d24200890700c21500b0307010001108607040b10600380b001d001c100322000714a40c0300c002c9400000e9550200c0081d5803801030707030a00001d080c0c400005044480a030200b2400c0c20650f0741c101000b007000803c503c069030320180d0702e984074a042588040c0c8500384024151503581c68244581000070702d08541d58200c2d01c540f59540204d100920b00da51302d554900c0c2043d242d81000b04203103041811003100c00c0740c0c0e55580c1252020210b00400c0c20038a81e40382d81d1007400900b640c01c11032800141c014031141c1200300c01401030340510510b44a62220b803901b8800240f80010384940d2130b000c1c0f00e0048641c0780700c046034001c0c0d07040e120b294140451132028425105803c040c2d2a400900f110001400e60b0900c00c1010030154012002991044a55a926 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 630649289 1250 630648039 630648059
    0xb040318060816050904020d06030305030f060303030c0a0338030105010e0105220b0d030302040315060302060901031d0706050a14031014010c02090c0301090c020a051b030312070905040501 83
    0x8980c81004803c200e80c1981203144941c004206a44005000500781041070349200110b48103900100c0100b00c0010900c805072026000e110341c1701030214015442d500d1300b0110f071a070318000c400d481028980c0340c1c40c0d044100b00b5520030034401500c20503c5501c610300110300080344239500c94002c5019521f00000410ba14028280141c1600ca010b00051848003130b404503180300c40b0021419500b1240c0c3da00e01052140d03518409104803601035139001d80c07954154207041c101d1050700511800028940042000182c803030105540880c0d00900f0002034080044000c0208020300e07000d104d1a0307002d000c0f004111541c00c00c0c007414040d001c1c0c0e581d41d403c0340a8808006054441521f00d43c0800302003600400080701e01e0103004403548018034112149040c590b000c80e1800d081912480740051021005000049940c400c11440024500c0202a00c8989489541e00c588000c2064074901c204018001240c0e101082102d00600d030808941c1d2880c940701c180204126070740d00802c0d04c50340c207060000901e0f00f54 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 630650539 1250 630649289 630649291
    0x2418020901060c150606090f05030f25050a03050102030a061505031303050c060a09030806010201090807060b040621060c05090907030c020c0301090c03021314010b030703090b0403180608 82
    0x80905030400c56401c1400030745400801940454000c00f942070380c802400410300480008220a40703e003401d090030030a6403c8a04001d1304150b009600031090300c0d030007100002d4500c03480c0031074940c400c000b040040810038081d5040d0700302c039801015101c0008100501540158070808940340c0400c0240d88034084003003021074403192880019030600c007088803c107540c064510224480d0404c070346805c0d400c0d014941422002c442074403006554507120020b158002d440f060f88948240b00801910304c9954400000f4004c6040c0074150039503500c07111200d40c895510110190620710340482c40340c00940040040c11345810412100d0a0038841c801d44403502074400e440140b00000d041741501c0d940c41c10201c00421301801404118481c4d05e500c0c0105072021322840c4110b50082c07a05021840c00c43c014000c103010724104940040740b42c0362000005e2990488510305554a07040c0c0c03c3e5681d2101c5004a000d00011040508620644400e01080641003140048031031080d0482401a1303540303510642c0c038000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 630651789 1250 630650539 630650543
    0x40b060405090304032d05100c0f020a150f1514010e01080a0203060f0a0602010f061514130e0a020307120e03090111101410080f190f2418 61
    0x102c04c2c80300748001000c4403020242142d0855180c0100c0b40c01c1d40c052600d641d44858143c6140d00070080c0542114002c2c010302d8035484013420002c00001d00f00320000e54502c0320b204003034039070007440d8240b610b6045141c01c01c144000581c5410f0000340c2701220b000300c0c0d0b8503140c882c1540a1610241c11000c5500501111140d804140c507400515640e0044800196200405280d8824075503100d00c07560b680c0b2103d042c80901002e500000c0e10503502000103044450981220b1030001174a4a0032450542c00301441d158030315081051034840c40e803441d4400724089560089401d900f03c0030104032041e81c0c07030340c041e51150000f682c2d8121004200c64074041140c0380c0e4207d4482c150400c0000850039406140501d581c280b40030100c58100c48240d110310101c60007c004600342c2160081441805402c070301e5444080c1007420003910b030640d02801880d503505140780104041e071840300001810302c00342c40114000c0581010030311602d1088500443c0300081d40304032980d80304c0e20f002c244449038400402840003240d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 630653039 1250 630651789 630651793
    0xa1101180b060402070f061b0804123902090606030601140c03040b0c031308151626070801122d12020a0b16051206060d060806040b06040509 62
    0x420030303071a0040c24120003440d45070066000c02c01c42c0700080304820680c1400f401210002032602c04100b90703032035030702200004504001d650014040411954204140d10480a0030300230f805c00c0700717549040c5042480e010f03800e01d812000040c080d0f603d500c4400c0d00303411700c0c82228004030650b640c4040100600099500303500064140e000c0340709641003000201500041c29040741e0a0903038450a140d441e41c0300d11106840c1e6040440c00c190440341c5e0341007000140003a580a03010312500080d458aa80300300074681d1402c000d1001104c4101c5000c1c000c940002c03601014100c5041702145244854884145c1740c1c500025841000010083c2d0007036181801c195001d4100d0f20b401d2440c900f01d09501070240d209024000c1c44100c1900020000c0008542c00760142d000b81c48001031030706081d80d0442d00140a106601001080d00b00047c3c1c0c010100c950024082309030300b0254032a0b00c04a600c0740181c80c80d807010680361600102c3c0d42e031000164148190710414244400b41d480034288026500c094803c09919 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 630654289 1250 630653039 630653081
    0xe06090a140a0c05040902071b0e010602101505090f04170903030f0306041812090602010203040c052206090f0509010b01050915090301140702010b01030501030b0105010c0302071a0a1101 82
    0x4100c2d903800032050784009140c154186030b26180007000f20f03803000801315104164030400d048034110411074080103024110305210550314080f8065110b5001101d6030741d1583d56416584011580709480001614000e440394000e8508117000032041c0c003080c1c4094620788180350350410b000765204112401e03880090059420310600c03424801041e00003804056003da158948000c090100310403001d0414003580c0c0e50600d0003403242d005000064a03030030040c03c41e40104104004508070b00760000c116a4162a00240003450340c014445401c4003489510903541491400541c949981e003009081d070403080000c201540350703002441d088aa000e0b14403804901d0900c4015124500350a404103290588d809661400704c1c48030000e0700315180945034419442c50113043c0032581c0d07424802e9002a11007070800700215410350300e5654400c2c03c1486000d0400803000b0300d0000b014070034004100100b41203e051090503803032124032401608001403540c0004c50704883c2c804003481c140a01960128014101e80f60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 630655539 1250 630654289 630654301
    0x3b0406140903043507031a10050f030a0b0703050105190f0b2b05071205090a021003110c0c10050a14130506190809030a020616090f0e06090a14 63
    0x100c3c004801d900d0200d03145500d03402c240c0381c2130090340b0b50544681029016450540c5000280500e010407061901c071300081c10000049010030580d400d41e2003c503003006015500c000040d2400039642801042c0500c92401c0c0004107405030442c0313040c4c074001c03103091606030108142006448614840d144010322102d204011203184c0800138076a203411f400c8011901030b91540c0c01d200f00b4085000866105a50f1001c209059034010b2500b039801e60980c4e0706105500340005140c0da0348600c010080e1203034100303495080c8503034002e50200f52a501c81c40a480d4442c0d01d07449641d5110301807454041e000300031001207a14a01d11a0084a6a4080940358081a03842c221034488050b00070f4101c0c1400c0032000d600116803590b410014101b9001d01c103002000c0980d5420006000c140040c0c41188a0b500510164005035004951b071540304000b5070f1405113040210f802129040c2d00c03640603000c004246c560210b582c0168241240c820501a80c10700d80546a910b170410481d0000109084281d20310743c08292 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 630656789 1250 630655539 630655559
    0xc050604020f03011413030f030606021f02040f1e080c0303070f0c032003070611032d03160807022409251706040c3b040614090304 58
    0xb000000e0000980c41314003210040c01c2d944152080307074000203c01c072503071304161744080800944500340c501400075070300e0450b0195841d03124401d40000c2c00016906010116a00c0d81030304d00410000100e004c0440e511104441d911231190728180790720004a034041006070000031201c0f60140050011860800551105130700100c0142c4100c505941c6e4110000120310390400e0020314003030f15030490700d0b80c1c02068105441c0c103009600c1740c82408451118a2150a404420b580d049508120015440c08280034140a1049507a0903422141008001c2c40440c4c07490b03900ca82c1001c1903581703404101d40c9559000780d175100350f0f42c00c0c20603030540c0042c54061401102d00645030050000c604880034412444614215490400354840200c1440c44040041c4d048100360842c00010f140003414103824507885041050700d06001e0032400d41001c14031842d03500c01c0190303095110717038500b0301c1d1307502e60f40080d00c03400008102560251011418001042c10086100364090302507007944004516083ca40103240c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 630658039 1250 630656789 630656809
    0x7080a02010608011a21061b0705010f151707060309060213170c18070c0f0609050618011514010306080f0d0206010803030f150a0b0a0c0507060c05060402 68
    0x2108654a03810b0004000000340074407800030110341c280400080c001414002d43d020011003445132181042c010800c001e0300800d815030460503600c185a003020b0301c41c8030240d0354403802c84000c000f9841d0950020f044900c1d940101180c5c6586094040d41e559030740b0f051600d0308011a007013251038010328000c125443c000c0e0f00c8008041c1c4035031800350502c00961910341c1400c0781a40206404582c0c48400c0c10f11140130711102c030103100d048816603210011603000d540094030040c0480d00340004140c1210a010001500c0c104160380014103000c41e031018039145888603001e039105141c0150b140180e000400d01030092400d11414090050305a514086000045210798422541416502c18002c5580103050210f113880340040f80042c000c118000300000c4c9840c4050f8003a240b0394106005010384402401c0c54150007002920b02d200308582100001034214902d0751000ca591200010004d0361607800c4101003d005005c2d409070780e07046581d850181d40860303d0f881e0091481d0000000940145400310940d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 630659289 1250 630658039 630658057
    0x3050a08042405040c05060a080103020405041a1503060c0403031d130204170d03090506010314031c0c0908010b0a0501050c070e01030308220b070809211c09080708 72
    0x1059211640018014290005048220071501c443c1000107000080311a400140400e50b25946404e6541c84000e00780350040c00001e102c0c44c0c80310081428469802d101c1d0f54004080d4951070704038108142000a4110000b01040c002d005020002d01d6400d06c0720196401c1301d4058488858004ca07081680e4144a0b450480a0f8040b03c80c0c80e8020142804d4405000074205030340090320000358407590940350070301c1400e50408060400d5491400508080707140c60440b40d000208a110500002e505419401250030354841603d0f200040c91b105945c030740020f45909450303241c200380f40791180d0980b03090341c0706a29503d4110003290404c202c0740d481000240381c404005001d81d507605484240d00a2640360a80c815000200c2e01418892988071200510f80c45811f49040d1414440103940c0744e142d0751000504074410310001000052844405002d5070001407420045c0c110f16005030301603080306401c05c811910103031004400d442c880294602c115040345070032081c0c080c10145582c1c0e400300154042c3d100d07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 630660539 1250 630659289 630659303
    0x9050f0a1521020a1202130501050c0307050d030b0f0307081c0e100f1e020607081509040b1807050f0f010909140a0506010c120509190e0f1303050a0804 67
    0x9190020342d00100c203120740140c80c0160740c2d010000e60040900d455450605850340c410800c50014101c07088a1400301d0741c0c2800c060751600c01142c11a4214042c070a0050a00e005502c09844500e51580c0300d00d2b840b450454020740c1200c40c6000b03041e9166107074041c4d00c1d11036000382c068034248485100c1191000000b407401944d800f1403d004200c4144521040300003080b90300981600d2141c000e50480e0300b40f0300003072400b03c05403a0f285009555140140904040c07003908400f0944621203090f401d281d240002c3e0508140741440c2c54000c8030700d1000c50701580c2c50640d500e82501c01400100e455000c5071802001440510b49000400c03502000c00700f42181407010089001502030072a0007400710580c51400d20040e1464068504400c0e2071006101c1810404d251022030001107070795041c00750201151410545031010100480c205241001c0800820a41c641000460a81d61407026116001110582e2001c2d01c4045500c104001580b4000300407903000c0c030107281c201d4031542c03a141d407090280d00c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 630661789 1250 630660539 630660557
    0x304050a02042004031101080115050f0904110c1005180705060904090b0a050a0c08010312031a210d0201140a0504050c0604080102180603010b16020303120c030709050f0a15 76
    0x90f260380184c0c0554012036411a40b140d100100e0342c0c10071200380c0142444401d40c00d03002c0211100410302d2186444c40c0510000201e00b8200548445d031240520030300c10310800e5a0380e003440b0081c565503075030714018002550414000546085017601041303810030300d1070000d21302c0718140420081c03260040307941940c00c00d565044500225103100b0520b801464641ea0004003410800802c400f55402a581c103018840720714010400625200c03000c40c0301c0c0243d4900014030585460f62a140f50b42c0031001554000c2003210158901400403109541c1c0b12010002c8074062405181d041e802e950028514169038000d840c00101c100f0040d402c141d52040c030502c00e885880c0b4440000a1940d04540c111401300d0f0b602003403801a100e9881140400329104841c110305641c5403400100440c403031308030024063322111443c1d10454408000b07a4403140000519000c0c1c91406c0c035100c10707041c0c20481d842c40001e021141b00140034108494060300900014014001c91403d12590f0400250148084010880070031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 630663039 1250 630661789 630661841
    0xb0c010e030307091406070b0f1003080a0f03320403021c050307030f0e0705041e0203340c0b06010c050d1107270b060d180210050304050a0204 63
    0x8001140f099005132500d020850410004851004840010782d00900d006c1040c00046005e0301e820a51080340d501140e0740740e1380c030200b00700401150b981c4000c10b110400302d11070681c2604003050713030300510403681c080001d4941e800d150307041d260306c1c1c61003e04020f12594001640e032844000e45503119000e4011580441d14034064100c204144401102c0010030100070302104690501590100c080c0310a0180891a407816155403a01303030500c106841a035450142c103400300125085045071040c2a50215103034038001201c800ca1064a602850b0314100f06046c8252400304c0da82801c0c1c0d40340481d504c0c0c0c1341d001e07441d07650600c62030310103001d0606000d420540000080d0081000c0d090303070a02039030340d02807022082994601d44009500103403942200341c2e41d864442c0100c914402d21001e00721001040701d440700004a0312a10a4990b1522224100050700801c460444002641c0038400d55075a03034841103520040710b20740400d0b6401051a00a119118007500e0140c2005109106000e1800c860000710 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 630664289 1250 630663039 630663043
    0xe0402210d030906050901050f0f070201110c0601030317090c010804110402030a15080138031603021003020f0706050a02093003040605040b0d020f04030501150b040f0b0c010e 77
    0x2003007000903203569803401080b400d4040d040e0445c0e41e00e0020b101606119065000000340246540030800c02c03c000038680301d100350030548440e1208090260307680c03400c00303d86481d010240800c0c1c01080d0707019801601d86d8040700c0202e104003044805454502c40d60340044604003800b501c00c1d0f48130100351030400300341d0380c80b80f008500401400e100000e41a000e000c1c1c04c1d054402a40c4100c030030341d240c207130703031495048164a040301c83c0c1c5280d04c03044245181610383c2c0c0c2901c00c0200c89070b07900b500c2100740d1201a80c91079031f80740050300c0c02114800022400701ca801ca0907880381d40ea08500c00c42060040d0000250036030032640e007040400002609146410010840700003080403003250005007110741e15070110440303106a0800b072000b00514074040c20607901a0842c0300c0e91050301e007039440024241c1104012541500d00e49078011421075522552401e01501a042180e50f60120846030000086d0350030f08541120f0031540d08dc6060040315151580840080c0c002240c441030554861034194045101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 630665539 1250 630664289 630664303
    0x309060301090f060b0405060a140c07061107080105070f0507050c031b090a091a1b0d02070302011406130f0b04060803030103140604031e180b0a0e0a0e040221 70
    0xc4880c00007501c66000d81d1410544d003403644401c03c6100c08000074009a00d0b038100302c0307820442d01e040c0500f11011503d038401c4a0700c1101031200c254065000081a41030b408100f80624003150000c0305c3d8442e48442c40c49089900640d41d44004c035444d0908250102d005070090f04d480ca00410645110550000c0401d0525400c3e0108400601400600c0e00b500e00c0c0030a6466013200c115141000341c902e071039031307401c035000901c424506014002400090340070303852096600b90801c814000c030f5103404003089207501a4000c804114055401c0c60406100683e0314204180300f100000e0011420711035001d5141d000b00503a0005010551b2200403001540e00d550081c00010850134000307503600e44c9141041400d890110500b00301c0c541200080c03001081d801460300d251104610301e04810050441810750390312240c007840e020b80003942000000e02c1410700300a00340035510f54494030314002c1c1c03003c108007002003907001d5a41040c12140201c3c0240c10002600360b52000095030307070226580268400303407a09007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 630666789 1250 630665539 630665549
    0xa020a1d010c0f1b0e1e060306010905090f030a031e0902010c1407050a0b0409060509010e0c030705221a040b030a020d0b1306140616020424060e120601180e0309060301 74
    0x140141c2481b294405440100810b46615204614642803c00c0001c3e19613006105100401d5101e40100d42c03881010702c10101c0c45c032540411070f65110007040c00600079141d554200b500303103c22400500d03216010b9004148a040e1305a42c2d20510300002d0340d900c0701c41446800c1000484c4941c200201d00c0f41ca03403004200103010041c014030b84079841e1148803001d03100ca50300b00d00c1c050f8424000400034640c1e200000341d000324529510070b44950715100c0c2200c1a000715081e43e4081080d8003406c13a007100209003600240d5013800a601003107410704414540b00c2c8182e20036103c8002c0200300150036101c1550181c40d860484402c040303011814000001c0302c40c80d4035095207103040d82d509802c001102035031110064625084d42e14500788001d214040c81c00a04244c00a0702440d01c8400e004140c01d6120910490341d22002c003296146520b030b01c0010003001da9810200d025a0b100361810a005038005260703812203072180780f00c140491141c40f5050142000c4403000500e84800c0c03040e4101c1d0b54441000e907010b80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 630668039 1250 630666789 630666809
    0x904050a02220e090f0316020607150f0b06030603031c090f05060106080a0506180603071701060303081506071205070503070b06010e120d030c0e090a020a1d010c0f1b 73
    0xa0401c1c014214400f80a0804a0141d111100003101c2a030080f090b2940a1055030030785560720254004140144101080204030344094014103140b0300c40c9511101002f00b1101c42080600015403d004451001b950055415402405440b103103420708889041c96a10110011030848056516603411036102c0c0000c442c40c4d00940010300442c0d038000c400c0c59001000000c03e1165013007441c080749034050240800d40744001d002e80010103a4a04011180090404510149510381001001402490240021400503030040045501540b41200340003804400410540c80e00c0496a00c80c5c0754150100c2d1403105100d000c0c4101400318109002901115000303c03108021860200300042c10a407851482c14031806100e507154400140c0040c2c2201c0a000d2810001064a440c8809681417901d4500507544800c8075010041011182c0c2c0103052858000c0e100c0468441c41c1028900d881c008000c0070a00141c1402c0034400172812000c241c0c180d66005148001e00042140801c03080032800e07810100043c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 630669289 1250 630668039 630668107
    0xe0109031d1c080a02150403050406050d140c090a0608010506030105121009051005011d22020406150f0c08271306050a060203040305031905090916180305030904050a02 74
    0x1185d014401100200c5140d071160300c45140c02e5401801c0341c0030707600801040000109001e61415166840508400d0000002100903c0d148140380615803101d4105030198070f44440004116002c2e0391030034140c0d1001000036085030b0a200c1488613210010681c2c20072842202040c42d55411180704020045020b83c1c0a0001c81c11015107201c299241030388000420315001c02c01d006800e07180d042c51a0000d00c6032980f0311107112892210400c00030f040b00b02a60091402d400000c950030540c403050075100035503d6043c52a00103210a5844d12101c250141038017034200f03d0b074075200100705440b0112280111110307a91000000100d400e03000300f14185402d060b61b42d401845245001d0401e400140035071f20080d468181540c2da01d0b41c482c01250650303250b0820b40103490021038003c000b038640c4140090003125061400d600b141c01411080854000070400007500030030541104280241525040001903207007980600c103201c018000249000c100f16420f0007149c08001140b4070112030b10544103004800c1d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 630670539 1250 630669289 630669307
    0x190b070804081b030a0308090127050d0203160305071502030a3611130c091517010b03060f040e0c130501050f01080a02070b0109050702010e0109031d1c08 68
    0xc0e0000a280f52040e0f903403100c141d400c5541e000100342c5543e5915140100d00380d140c85070054058810443c890480d061002c039942d100854100d04140c116005004035038503403251840c166224030aa039800d8040740e000d91014800300380541c00a1041d18828040f070302010580100101c12078200f51042c003003140d02c520308035000001c222030024400c119104902c3d0350194106404150452660f0010700300041030444840c55610321120030030001447d5010b02c0902c202020082c07002c0749601442c0281100a07032002c040d58810020240800201c0281c0f00071a420a4034401c00d076000146411f41c40359000003003103816112801000c0c070070050750300200340c60341044040020643c000b501420590b85007400401c0256140030b40b200c1c1d44030b004e00b490603250f1540070324507002c0c0c85001c0015100c440031200010b2031441c0d9a010900c0303030045038000c1041d4008240641c0c02d85d450000d0290005000c143e41c4640090118104894060000c100d505580c000c00610710320025000d109030341d010000b003007000c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 630671789 1250 630670539 630670543
    0x1e0114040c0e1e01030e03030a0501170a0309060311070215180108130f15022d180103020306030c030a080702181b0901030e19020102100e0606190b07080408 69
    0x1800c0d045034100b15020000c01e0003c070741d000200310680204110a0700511100740d02036031280c40c0f0704072420b003620f030f0380d181c4a845031015200a120b04ea400114080744035010860108450944a50580d6603c15031481e00204402500e0b41044180c000754081205034010f82e203405a2156065580c8445038490f118490390203803040d50725007264180010002003100c00f10744000c40007840c0390700c8444c000c003051607410b10b0031102c148900515230551001500424040c1018541c05160a00b10b6482040217401491b020f1b980c00b618002c4c4000c0c243c4000b6504003503000340c002c1c651064000c2c08031003005000b080006d2814050007015107407540000307682c00030341c1020300c1014600020584555804c0c2048840d54503038400d850515020b00c10003080003180c42c1e1007900841c100901510840d01d4200701d40b00e44079499090907a080340980300700ca114540b130741c2e9a4007030607460b07009120141203d55100414010500100510000504042500411001060030181c0a018007401000752213504000105d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 630673039 1250 630671789 630671801
    0x5040b06040905120d02040e0103080405030c010e031506011107060302131406030109020706060b040b09090906270a0c120302100b0d240507020a0c1a030f1e011404 72
    0x1e0045003007550900106500061140d0705010351039225589181c1c54818000a0160340c0220144054210001050240081c041e1040e43e504909813030690a0400c0191070300034001e12030b00d416420008004c45d004540d0072405521820606200d10f185910152190606015070172000100740d02191900061a8460955018181d020910702e00211214001021400144a070060054002915400b000403079000240106500301c1c020761101c1d210150851190000f031070441c011101c01d40000da800c500014983e00900d0100c1c41907500300c1701e44c00b05219540f074491401c1c10a00c2041c601100040302c696030000180000c0d04604860b038500d00d002404c201ea00520303402c00c14200052205141d5a032051450301035405185021841d00d103100c85070b408202c00401c074070943c4c54002001201030f0041240001c00e8440c5405400361074a0b481000a29a81181c000300c81990038400078a5104048034081e412490910888071480d1058011203022017090708243d11b1035039411002c40181c00c1c20301800d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 630674289 1250 630673039 630673051
    0xf0506030d05030412110106090b0102100504150e0328173607080601180501180e0712080a08161d01260f100e070305101805040b 57
    0x60008030351907020091180c000904050703d44031038550040c00e4503024411940b40b000b81600244216641c0310048001850402406d502501035014201e103652943d1007018840c40d400f444000090020040510090141c2080d01055120422400c11080c060400d148441d9215034540600481740030b8005043d149188104c400715907680341071044c0c0030810741640000c10351fa81d480314484060711a1003601700c041c00c40c60031200e00070f408010401c02404143c170303070607a82c1d040d0301c1a0711a1040200c03801100c40902c5012200700414130340d240310000f04d800006034495408200c5101580750300c3e0800d250f001d034141c11105500009243e0f03c1a981200365950b002048050300e0401c0310307251001604040150369030030307079802e0402800e4055030b0255801000210408400e40023100310b049400b041c0180599060749401c050b01c0000340d40100455402003941c52082c1003101944072140d0a078094030025004000001c0700c0c10b408900d0f10348035034140c0302c200721ba40c401017a58142818030740c55003c0080c0c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 630675539 1250 630674289 630674293
    0x91303030b150d0519020309150702030f03060d02010903021f14030108190203010f0e070306110301060219080d090809010914031510050a08070801060902040e0c0c010e030d0f050603 80
    0x101d982d814481c03d03a60112050380c80495540c0d903200c01e4084071030410038403039809480442132017030081e000142d540c00c0e559420b040d40490744415100383e90f28040c08a00070820386003000040c5407818903008201c0600d1040c1005604c0307544960002e1300c03222020b000110018071503080001216844650901003000b140513040c5194103024180d82c48080707010b0103180c01040320210808640b0309501c50246045100410000004800c3c3c019844020f948000c1c8d0b503180c2003080c0031440c2d0600301d08490481d00d40343c0042407001c00c0f000c0c12030f070341c520701ca4019180800184444100803400b4000d0566442c464881c0c203075290b1030310001508041080d00126400403000f26100116180003d122012407072030014824180d035104c1000c00007290507004103070840b05071100040c6008001402d00c0c16603010300000e111954490000700e00700c0c02144101d6001d18052800f294030004c2c050001c1c40303c84000800070611111303091005103140c0c041e0141d60309480e40c41110b40c02902051061580004080300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 630676789 1250 630675539 630675559
    0x240b010302040e061c0210030911030f0c091806010306020318120a03021c060b0712141c09020d0309080d020a08030402010f0c0f0f200102100506040b091303030b 71
    0x1843c051203000414450140e0300d400007403080e1a552844882a1a500521000340820b8a2200a01924014104443c81c0a02a050400e18580850f07505c0741c02e00c40c00018044403000f80104844100080c050401c14104070040400c080d409100d060b0180d40560b02c09a0b89062402035818802c0040c0c0740c20006e50070481c0041d003070355080c01c106c2d0b03242403ca14001d6250308820b040d00e1444074001d45040005854007100248120121010702081030088042c801c0c14040e41c0c505072400c10000608442102040251078039100203100150007852001d04001040789090b80860020641a513060380031500004042101315403c12140d03444100c24400b0f04518561552038540e14000900028144031002c041ca003c2a4072800c41c4082c5642c000e54958100e01c118244410140c00c0d0000641303002c00f250300020030900320aa622030003250103a0061481d451010b030070000404000d80300340c0e80181c8a4010f43c4490b41c0709920305000c0c20f00901800b582c3c00c2540b90180032108010701d0356024402941d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 630678039 1250 630676789 630676799
    0x504030b04081305040209012708100c03230c030a0615030501080f0102180f040e19030905270c09150d0e0d05030412030b120a050f0304150318240b01030204 69
    0x43c9d101c1950410f19203400032918582c0d1301d0400b40f24a241c01c0001e0a11884682c1c4852000c1744c1c01c1100200880c1d1003c200b44180b0001c1094843c0710810040460b001036000314a50005034001558444c0d80d8403800102d198640c0d40411400b05424a0304c030020303440310014002e0500500c20240034000c081e000318903040c0505050b25840110301803682c450340b4401255007464940c1d03045801c048580c5020f5415071084138421101c07c40f40c00c001980012040742001c62141480150940c0c1c4a131043c0602c403d00d05e4005201c00c8500b001010412000010311002045454130002460300b04294145e4503154080d9408540440b44c4941001e03015070700201d0b204000d15003007001c0703a400c941c11041102d10394540b20420b4018024444015800040c0c500d000c2d1088079000c601c0960711844dc40586240e03c80d0320b002107a490055000303800b4a07551030701041103602e000790300862591a503c4c100d0640d40f4000c1d00c9140b402d02040c014084054450080641300500c5441407494aa5090030b04500301801d08c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 630679289 1250 630678039 630678047
    0x30a021315151202310320090f09071a07051b280e0103080403020f100503060d0203010e070b1b0105010f051201200d0c081909030504030b0408130504020901 69
    0x38443d2020072940026a8900d548950704202102440390b900d4261403a54100c07400d0a0003524801616509208006100d002d03c1c4452503041828000340f20020030744880801025956001e45125010f10402000040100c00705020700a554a41000f841d154462414180d0410b010281240707a8101c0d020340800c4141d5403425040c0402c4124180c0385076003000c1450703103901103026030411115080100e00000400034004014025280300b5901001034141c0c0030280200ca461551030640411030510004189003404441c4054042c001400440c0d002221000070b418031009030800d043c10800040c0c0700a00d440341703c0142c594214050001c01407980b500e01407444095580c005c0d17034032502882c4d1555119080942000d240c0030250018540240c6607000204080c2e440300904962540c1810145074025009000b0240714110198070b80c51038031030706065a802410756032411801d12206201c04030100c2c401400b0144114465071500d035607182c0300c030049103110b00503510040c802c5004121046480e684 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 630680539 1250 630679289 630679307
    0x2106010e01092d081903030b03010b0a0308090303040902120f07140a03360c0603090b0c030406091208060306060a120b060609120c04150f03030c02030a02131515 71
    0x1440410a1070b03ca00d4018066808015030101c41c00388070b002d040c004164044201d9007800c61180d1403c000554a0740180350a8459a00f126903005400240810200e0594002040583d1006054034a886d0300c0d40c000408a0f0000c0e609e413040765200104208444480b0112580c110103641072030b0140708503003407040701d10f48503404c48241055228500c41490900a40a40c001c205150b1b100800c0c00c0c0106184036100f10102d80241c0d001d040a1a000540764013a10031381100703a0308412400c0c110ba41d415001400c41e840504125582039a030318400700402c4032144401c1d104c000d10b035100c10031428107908151901101400040c0300300c3c40d1080401803101e80d4180c0c00b9605074462035060300d540c1c0d03070000034126010740000c141c4c11488405500c0304680c2d011844444280382242c0400002829500120220a03540107000e004000742c4002d0010034054104025400d10003021911000002e0380802c05124081c903440c845591554980011b154074003503940040c0c0024880e14426110245005001101c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 630681789 1250 630680539 630680579
    0x21010f06030b0c4305030a090b0406050706180b010e0a050a1b0c021225080102040501050a080a020f072f010e0d082701080901020712142106010e0109 66
    0x1418008901e210013402d2004038036021004805910b0740242042c540302c0e030100c00300c680020b02902010030215206804d032820707241d02e41c0e94541082e0a5a070b60300000c001800729a0300c544049203021000842109909000e0508204401d05a061010110090302c502410381c0090500704020000a80c1e000e00d00d29440b4065403030450041e04c00c6001280100c040044003401d00d000307195680b0812140c03e20741c582c40c04080301c90100300641e1040501c1c201c0c040c9025040c002541001682d001038030034404113410000c000700041c41c1c000c65002d81c070110750019100b1a100c0300d0f0902c901c2c1203a0710618145403103265100d058002c40c440c44000820a19040d05928071849003031f600304c4c0a1103001d2054076042c0070384145250107204024062900700581d10b072a14001050500050b016200600a46000395403001090201f00d065641c192520080200c104134180d500307001481c500b205000714003804119941c1c02d40040e0902000040135454000c0740c050600403001d00030000705000d0248500c1d440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 630683039 1250 630681789 630681847
    0x90806010b07032d03020a0210110d05100b0c07061b1106030907170601090b0a08121b1b1e0901120807020603090706120507080621010f06030b0c 64
    0x1502180050b031003d42c0105a9400c4e602c1d64101040d03642540c010b0581c00f83d0b5400302c1c1c034042d005d803a8001c1507591041c2c401035550f109000b1400048050f4006a4100e0034000715010029154140421b954100440703403400b50b441507200f0858a03800c00d265140000705844030003200491034a860089501408203680501000400250f4214091008002410a0858442c500410320b11565a5480c0070702034407068a2919810006a19011601500321a4403c01909512448525510311900032404408200c3c6001c041468030340b03c240b25000300400c900c00300700411a11f120078007030090046580b400e03500c400d900326945030b647c40008042c1112008140c10700071500078500070b0064062204025085203000c810b10006101c049190010349484e0b90398100403402c56586041900c200f910030358049000840414614280a54540c81c0c0d203842d41221707030302c1c112490340007400c40758100004001d05558401c00e10402c080200c005400500720500c2904100760070111800c1d000141100213014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 630684289 1250 630683039 630683057
    0x6010e0103060915090608010504120e03070f1d07050a020a1e02180114060f0a08100f06030b030f070303090b030703090c0f03050d0801080c0f04020c0105090706090806010b0703 78
    0xa40c0c400c0d04010082c20200c00184408621009080c407000700398002c040c003860501c0c002240041051058a100e9500701c0c4440d01c0500d5110416a00002038011958150051000203e2660810724403503000304803684030348007231400d0501e845401140c00762005041110812009a2296000907038417209a0840150707101f0b00c0348000f02490f0b1040002c002500301910521406508540c07900480c103c610842e422404006c000042207000d108a4007a10300900d41488003903d010b1040000c0d503403000c2c1e040d42e19008283c8410480c0e0f14112a507000d01c00207a00c80d025980740b81030038032100d040da800c01801440d0890560f980507008040714003402506010100004619170b00c0b980100c800035410140c41c408050312110241c800d11642c0c081981d041c0700b80c0c4001c2003030714400c00039541207501e00006070103800782c0581084080460032445907400707502030113028628842032103a280160781600080102d10719160f40541580126841074610744c02a50040000552520880744030a03410300e4102c02e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 630685539 1250 630684289 630684317
    0x405040c05120c04060f02151602210d0b010e0d03051315020d142113020618030c010c03122d050103021c021c0807051c080a05010e0601 60
    0x105014082c0900c00c009102d200f4041d10710b01440003403098030441c1d5181d51503642c1d43e20003070740d0700ca8404178510715040400c0000f134040000311001da031042905205452411320520320b607a6840710114840081740340000b2304400314503101d100b411401c0100b13003070500b40750801e000003803d44c07075103444064103000c400137000c414040450941e40140007242d03040565000300000095031000b4034032140000c14604050203035038002603400d484c1c1700c010055500d4592813658400c12118403000d0584105540d03200718040c016603494018201c070502d00340001c0040500581018a031405201102e81440042d1001d4008a41d10006010b88002c0444000c0750b05481d030715190001d60450300c000c003502c071070b00380303503910007001c035400c100c0c100d9008840e08036101031001400031002101d110000e50001c0c840e407011541c08020411240010300079400d150030100c254071664105103d009401d6008102040b46052058000c031000390450700c5904204495810a01540c40100b03000e429a0b044c002c46441c0410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 630686789 1250 630685539 630685547
    0xd080f1b030c030d140105030c0d0c0b070809090105120615010504120303050603010f06060207211707060f0b010c020d02040e120a1d09220b070f08100305030405040c 73
    0x10696115411259114500703140503883c2e0704007020103d44e06091100340319100e046a10301c075050fa030000340541200d00780d100c1000018034602d48100c0310110707280000248072180344040e01100d8021422580e95103003100812800c0b80e0140c200511070303041d00c4022120841c0009010798044c600c1e410660158094400584031402154400090b0b40f201d12a000101a1315410081c01110150000e1040240301540c1809540c014007800f4016403100c4020055001c014000203985e0b43c855110544803034180d01d40d88242c5a4240b0300c05580c0c0c070300040074410008144180992051104c80410140038001c00013030002644800c040e100301e480040c04025595164481e050381800402181c5203d04404000f11aa800c9866014040342c2c100d400e5241d80c401c1c1c07481f125040c0000601907100daa84990000b054201c0503014100c1c0b00c0344065050002400c1c01c0c103d01e00a03030007901ea900003000d81110060150100905101e10544000d40130000940008140c5054039811640890b450000d030404039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 630688039 1250 630686789 630686827
    0x903160303170c070f060902091027020c0f01020c1912031d2b05030411090405030f0c03071e0f0b0a022104140f06011503061511010b0d080f 62
    0x1070151707440c645c01c0000f0071500d40c3c01604618400c2d00c421201c0d0303440e5a000b0750000315600c00c601c01000e00050b54040d0035641108140c0300004c852005080003d580c10051030000626260803191f9400542507031109020003410758960240544070148040e10798440700041003603088a0103054995141c0c5503082c242044511114038203074121462104886e290a03a442a4038200070982000c2c10b0a60385403911900c112807086400c0544541c100301c000b0140103280340700800a66080c00b00b4881603003451408801002d50310302d04e40003961111918100212480700f1040f07042c003017045c000c2c1014002510460161016900490000700b90b036075548900300030348220190400c0c1d481024074803084112440d03d1244c044ca000f1840080410500140c00303503502c124408046031507000c01c004006101c41c6000e4418484620700d0b02043c0150380311486105132607162001ca010600800c1041e800700000d1203462150b40042fa154084812581c5414030513100320040c40d0301c0c0c210300081008081c92054403803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 630689289 1250 630688039 630688043
    0x1061e051c021b0a060b0f01090e07020a020d0c0e0c04081504140f011407050c060112230a1104051005010503132a0608010b04050105030a0f050c0903160303170c07 72
    0x604030f078103820440c9911600444030442d240c3e850110041c03042d0610618640030020b040e10354603512410221801700c0c1090040c007070400c42c4150001400180c0722580d100c600d1903c25501d401040b81000680f00303030b88000401420381d4103404d01c400c11025000041010008400c090040300b13640703550a296070542c031001c5031031420740304150003810741f42030561050f0262051046009040d03100c80e00215020311075440949050741c800b80050007031448407011038040510070840200c18080000010883d6000000007540c0c80e00300264140600038204103080f0f0190044804005030300d07001c1007681003007042d0700801d4100040440014010141000c0d551030154020f50b4032401c40c0e820800fa0f0809809010048802080d6814001506406540518140d440400b0345604190a00004481d582c00080600400c19280d00c410710b1556054880c0b01d00544540780c40307607920380c54001450314000e5400350f01d0368000c41c2e0303c50801c007003907100110546000100b0306000b2261203404924685010708400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 630690539 1250 630689289 630689317
    0x11d04020d14121c05010e09150703020c010c030e0f072d09060e0403140a020c040207030e090c04080708060609220b0705040e0901090308041103070e09030301061e051c02 75
    0x482c0700003506020076418030f204607201480745e0703a00c58903e13003112a400c3c0d50382a065881001c4d240d01e1001011300c010340c040900d16005040c00000c402d01c900b9901c0310425000425034410a926a4071000e120662414861000505425160040303110030410704000640340c0c21200860564058441079445c0700601c0681c0c018042c041d140c0b03480c442401800e0f1821004500b542c03004030302c48405a0165070004180790064035812419105010103980030388021000c004503504220555502d50002500400c020000c442d00c0e07078217050f800c9140004c02e410002481d40200b0801c80240e0700c1c4080d6542c0f000c5a05410745079041c4e00f20b8100043c2ea03102c04002c01d42e00c14081005807075503004001d4000c07540e4054100481c0e48450041c10b081f03c03032103000680017403408000a808100411440304009802504860300d003656480d4030000d60800b078503000d006400002c01000802c0e4030210740541d1001546030040d030300d444040041e0480c883c965407400c08078440741c8a400e40100583c150780080c000030030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 630691789 1250 630690539 630690547
    0x140f0601080f0c01210b04090209130618021c08070519110a081b0f031e010f0c05160c090207030c03121509020f160b011d04020d1412 59
    0x82100d444614030314003041c0500c00c182070103c86603ca41812071044c5070195200700408054a48180605003010352607421980b50600f441c0141c40d540c802c03034804c0340b078a440011810001e2078402c00345c41c41c0308004440c0c0c5180111060141e0365405001c4244050405d414510500358604100d0324000c212000e01b50b401080c0106003c80e898038268044184605c8040841e0344503031080240100850040400ca648000003003404080140340b414269a802821506200c1c0c550000a1404400301003ea0035104000741c20b01d09071000f4003c008400c01020350510404540c01c9004000b80181c80c03284441885248000f402c0c00300541c00c440251503078050075540c41d9168203021b0400704100c00304800203070340103480d00e001c01e44902c900d5944a0340f4000c00184245058514006134000c1c1c1a01d00740b0b201c0400000b000c91500001541d00300380716802c816499850f08603540e980c0540140b1031000307007000400700401651485841c2003410362020610a1842200e0b02891a04541043d41e07201010002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 630693039 1250 630691789 630691799
    0x100c03381c0b07050f0d15080f0a03110a030206060d08282007090e0f0601090e070e0108031b15070801080c12191a0109050f0708090a140f0601 63
    0x201c01c01500850b02c461503070b1940181241c0a04c581c1034844c1c40c080f401d000400c0c0b800c8003034201c10014240050019481c07601d800066051107220702620662307500188000d003c16400000303800c00c0141d0200640b5011030b840e200a500e80764010102c52146440d014004c0c2000421411313218814100301c812041407005100e00d40c0c1160001032850f0105250103082c8910001007011308600c228440e001e02082454080408040e0500401108082c0a080c0301c2c9001a802002494020702c1c800c140880e0860f05d4208090806a81e604001c603003014210041c89007e800104566001c4444501405030040b111040d0303007030032215985250500029018070074216445034a490507900760400b5101c0f00c0004100304034001c1c20591545881b500104400c0d901d20041400c1c14400c107003c1e094040d4901ca241901403102d603003d0300020390300ea9481d030510090050150707810354058040d007094031442c10240101aa11008481c2c000d140b40d0500b80300c0142008140005030141f100001215141e507124 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 630694289 1250 630693039 630693079
    0x12160807030314090f0d050c0a050f0307020a1e03081309050702010b09130309030b040c0b030a0e011a0d060914010e0106051005210709050d05100c0338 67
    0x510038503550f040c1440441c07441c00e4041134600d48041303070b0b5000f414030344110b510549040d0070071004c00da0940204807031007001c540300b804103100710b03c040c00c0075694601281c410400251302d650883d00d42006114400d04040c102d0708000c806403904200d64684038400303860204c228551035001858454140424004460380540005030312401c2128888203c0da81d00c2800801e144800102900103101000100041a44050b10303941240c0506180001c8980324440200194010380c2c0c1502050360360082d40c82952828070a4448616001c00c80c002400d241c040080c0c400381400718003400703250340c407244101040711b1002d82d0301c20400004000d121600348c40314140d00070903203486080d005098440036228900e1044045624851402242003140740051b0180800388100421a5051000341c41010440b81e40c0c818241520358480c2c4000e003a4030179141865810344140c810200181410101901300301e60032035490340b417613058007030241941c0d40d403100c0303c010103826041400e6003084200c043c500c8080700c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 630695539 1250 630694289 630694301
    0x140c01061d04031e050703050705030c0f0f060906070f112107060b0a0e040305070303090807060e2b03090312050405070515131a07020a0906170708121608070303 71
    0x25212141c081140000d0584d000b01c40800d4000000c4040154500103400b41004d410703501c9c02107040728144041384000740d150501040c1d0f1103071142e1011000c414246410404150700082c450081d0880d030806003000380100e00707400010018032082d0b09010060410400407141c2c01f046c89000e0503041608212401059800040e095654500b881d004c0500c0e41410040c035411141c6030703820580385564545045981d608000002c40405850b000b0881c04500c042015007281400340e900002d103001c0346080b06d4603180075400020b07400303643d100e0000061a040050517410007860304000c10103840a2804548100c446429a481303030745020103000500100040b0402901c0061704c4441e48c103000b5080c03140941c0104140340c0007401000d241400b03103181800107d5000320314a921b4178101b04980d070004241c030705940c000d52169a502d01c1c0070407843e04d80d010080c0c660510000070386021402c200b00f0302c1d00e6102080c40940381007030000c0c0d0156648031012505c40c0068000c0c1045072202007a1800402a0038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 630696789 1250 630695539 630695543
    0xc0827040605060c060a050c0d02070506060a120c063e06010e10090f0902030f06061026061f0512071403040b0a11070308040b0115140c01061d04 64
    0x21510780003007114203241c07085403d403904100007428541d4421140002030301c0010021084600c0600c0030401c00c494038001b4061480c42040540034071b20789a01400b01c2d109055100820a4418000c1c00c00401d4000780c44034141c030750034a04540c02d82100342003c103a14a4100f0271541000088116601d200f450303803010400c40504406071b58040c1d03607860070f0200c6c001041c0c0d138091600d40d241204101c0440150b0103903900101910700410020f842d0b4001034140800c468416210360440e504204d0701c0c0c90140c0032070310118010b040500030000600c003011041c2d03c1e909601500982c00702e01003581983c1780769005d1111000348021201510f55008002c240d500400020022465000301043e00c1da400781000f08030581140017004d007150b0b66500c40351102c0b98050811619607684071030090752040d44400404689000340c88800c19400c1c5890081040c0710140d00c034030130503a0340c0e040c0c0048540d44800f0086020001d051a980c40d1215459010b00600e0070707a0204406000c01450a030240784070f02c0307816219078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 630698039 1250 630696789 630696791
    0x30803130548090a0c09090203012c130b22050703050706030902060708090a03080d06181b21141609050108160c060c020105060310020c0d0c082704 65
    0x744003403500102d100488103032180d000d420f4900082e0040d40755408640c20981030702e013003111150340e4410801280d00a0300030500582074000d4441c00400c200c118004030b01d250003c0c4a4a6241c54940c0d83c40901d40b18000901e942c0c1681c0101c1d6075020803450030f100028400c03403a4117483c90940361065503100c1038031013201e03a03000325074000900314000d02ca03102c10309401802a41c5000c0740d070741d1484030650007449203e80c4510400d002102080c40034018010001c2e01c14000900c9505040c0d20b444840300500c01444018241001e201d204a940f45240e410301c0c2c40350503c1b014040352a44e98005085401d11804007940c90702c642c0301d80c403050001c0224051898441510800c94180f4070440d8049018007805000c0351034107020406100c1c0d42c14088032080c500345004040f09079150b49034405c0c2c812003a80d00700181e441d0000d00040e45000e00450301110b80b02c4508600d0103501c081c600b03403a4100000701c1402e000d003d100c4a010301ca402c10483e118a01768410351304091140303250804220080c541202e00071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 630699289 1250 630698039 630698143
    0xc05010902101e0809060402012a030302040f0b1809220302010204050109050f031f180b040501111c09171902240a050c13090603060b0603010308031305 67
    0x401e000348040ca010351704d82c1000c0c0059555580065440142131151a00c2040401c4600c21020a00e901d604242c94841e903405669a440d140c2000300c07542064002e4088440e080200c2c030707400020000c40d0f5248071401c3e19a01040d80d10341600410341d140024030b00465100d8050300c3c100301941034dc020026500c0c240c841403103064a42c820b201d900508001000d4140e8462a020401424902c810303110f036080e081800303c2c25080007407140190503c9160121082c0a0041c184401c000c001e0040c0344400320310700d040c03034108010001c03191007100c1000600502183d43c0c4006a0a005c0d0000340c41e4036072250400c1c41039440e04074009003020040e84000c000c1c014060110198a030a2074a01001b401d010000303c6100e44c0d40700c41c11081d00510020342203641d04441049012800300006640708020f058a540005e016440c6043c5042520349201001e8454a02000184000344110007501d03003044c1d40d800000c140d403495180141c030304181c1c0000440e43c0b0034a8130381c2c51b540315500b03e01c240318201d0b100320100b82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 630700539 1250 630699289 630699347
    0xa08061507020315011a0c030d1d0d050d060501050c030a050d0204050a080d0f020c06070314041a04090b0a12030e0a05090c0c0c0303030108332d0609070c0501090210 73
    0x1b1401010058042038204024042c440390407900114800a440c1c84100d0b0001d054500d100c0c81c22140c00b00001c0498400f15881000b0019032190100600c001e003015440c10001b061044d40702c2c45008145404d2000106002e039911006a040d00c1c00707040007402c0202d015864914030359907258407140901c00201c020303160b429103600c00705201c48900380c080c0155040140e10b560541d044080c14141589044003804000380500f6080d28100c0c100d0f001c224650f90f00d9050410f0318080c1d8500c0003e0034000c100c1031104020080181042502c51505031508942c507180c62000100030711010341c081640610784c10103000a880c18a00101407035100c41085540b2505108141903d0340000d1051420791340000400e18003d443d02da5010901c0d00c480c0034101412101036401c480309a1060b0344c610f8007041e07050b80b00403180100c00b40e58850300d0740c20024844117140c4440080c81c0b10310000c1204080000000d003140402009400480d881ca0380108503048620401c2c00c010041c400a000607104c100002e210052 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 630701789 1250 630700539 630700589
    0xf090203060a0b01080c0f070221240c1c06081f0608060a02090d0501090515400206040b090109171915050711060702030a0806150702031501 62
    0x301500f06840b8099280d48440c1d0300380d8075030840c591112821008010f0600181d40300c2144003901e890b03803c68944910344030301e1468900100e200c04a410f900040281140c407607001c110040c0d112101061060b601d01a07907400c17800d1911070400001c4500d0a00f0004144d1b0440400c540c500c101441410100d0300000c44034501c16900c040c1310702421500820080340e0a40c0c3d082c0c0041c0300d9100b000d0b00c00c1501d035a55586190031154a074100382d51030380000b8400100000884c660a420040200c81010085064070300440b229264404003110062101d00088069000001008019030024030240d1210781ea000f5428541c0d10402d43c2c18001003240c41c01040c3c3c0e80071048100d0100c05042c008080c2003c2c0403280303c020320034096060f03034100590b645088160350303203002d218841d0605580b41414000c640181d149400006400107055400c00d1002000d0250b000258640c01441210f071031070b07185a100c81071f01c1c2d0f9215411010f50140a0060598512070303c90001078101d8240700703441c0c0341c40c2c414400441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 630703039 1250 630701789 630701801
    0x402160b1017120706021e070f06050705120a09050f010c050c0106170a06051009091401050907080d081801060623030106080c03090f0304080c090105101b030905040f090203060a 78
    0x4103103074107204000116841b54040d0a0150507001100030240550680c1d64580d00200400c50710a07120041039010402c207030003015084501400d1181c180340d180c0c000c00607a203e00030045681c0941e01c0503510144403081021041101100c0c000b0081d862104100070420390040b15a2441982003000019801016100c80d01d9802e1050b400750035000d44603030300c0401408006d4151102c10300310341808070b15a90709100e0900d0340d0303100345a00324840500760401c0d420340724014042d0301c242e001500700b0003c0d40030105000404c9540c0345041a1a40e40308046800c4104001c128000b083d07180c900c011075401d42004002c8100d510b154440c145041d805010421680f009004078000900090041003001c034411000d181c00043c0f0300700740c80c001032000c281d00345035406c02c3d0f00080c1c82d03a12104040d01075042241d001d5000d0001500e00d5100300c00c420744003030207240c444013004d020141040d92500a0500c6100754501400c0000c0c8103000000d5844200c101400710060b060f40b09003d000d002c40d0007a2130601c02c0d8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 630704289 1250 630703039 630703063
    0x90a0c1b0804030b07050c010f020702030c0a050f04020a1707111009051c0509090f060a050a03050c101e090317090a090b030708030d06030b010f140402160b1017 71
    0x458030b4181981da03250f05541c8041d100201344002804a003502d08000c2c095180c00b850098001070b2038408c24010503241010300c441d010700600a41f0f40501403a2100701860701860019100903035148a4101e0494508200400e0801c2800700b04003070001e40d030780c01900c04e04042c4800d011148a042001d605e141140e400140081c0160300080035003818404060030315520030401d043c4203003007182e0040400e501c10000c4884000c25100c1104000c080d01e05140820080d080070350b01106014107558405a4a00c41038030b44c40e00c10b40b26145120381c0e052088500340c5448000010307000b500703e5030942c081c102d203400e4041104c003408012004190000507900380c2e280550020b181e480d07050724114000b002841a00f480c160540a00e80010500b440e0800081c0807419000d00300047d041d140d4204204510010f811801e1a00e501c40e1040081d500751407480301070090112401669101c0d440f102d94524529640e00811290b40c1004020350111003084800840350b03940d00380075000f403c2c0c2b201241c80e09070010003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 630705539 1250 630704289 630704303
    0x606050a0c02100509121507170f13020a080303090d0e0d030f050d06060804050d080103080406050313020409063318020c030c21040b030f04050c090a0c1b 68
    0x11540140c60b000070f420810825904000b03203800d049102107080708040c1021504c50340d00c42da69038800024000c0d0465800011480c194a14a62403008403080c4170016007080e40c814195401b051065022400d0b0b0041e05038028110702240c2da031107080702c0c0c6941080380c0702451800780030035004140d0300858070310a6501008122a0311a080c03540d081c0c2c2d008000424101c04c009040c0401e00c52050207108000282000d901c92148610f0645005440c018480269a0030070001d00c0040000034020010307201508c40e141031844d01d03a900c044014610b88048200698054103200c0340c9801e1004580c0a00c9040382d12694038101d1041c0b081c002d0f24915100d180508034103035614420064010700350300d03070101f49400004c00b5180c41d1010800c06d14542003d03031048516040181c480b100000c805852501440c08026401d08192a100c4260110b000003043c108041290300d000600300034044c0060103044d140141914000d00708036510380002d003078540c460008141007036501002789003555110025281c0c4015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 630706789 1250 630705539 630705557
    0x40b010e0c040512010e07080a0b1602031c1820030f0c01110114010e07110106050607170903011a0414061c170301030302030a030605040c12050c071a0a0606050a 71
    0xa204e425041e0702d82c001107555991144c011400344c1403001030f004040b0340009100307404080c2042d000009015003081e12180301c10141010580c0c000c030a40d080c01c49213600316500d90410000c440040c160045c9a58554522004c50508019001340b50310b04118240f00b04140d903120341803c0c075a03101040c3c110500a54018115031410b5032080d50031100c000425400414414100f1100b0020000c0a8206114450b112801c02c0042c0c2e510100b0302d82e84c002084020300103c0d10301404684e0714801ea100c0a0640c80c0e44140c80f40c2592101d40840b5640e040c00740007009044001810000e00444800265115500f03001d0403803000019600180e02500c1c1c01050070805022a030007240f00c40412031001c0756010500c0303000d14098409040510b000350701980146584078600c840080c100c510030f800c040e1007945071081d40501b69a1050f8003090b0b001c603c2030000ba198840b0b29541c0154050000001d100b0451a090703020385602007034000f0702822901c002070202d03039295101030b60305000d040054000101d06030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 630708039 1250 630706789 630706799
    0x501060305071706100311030a051e0708010e0403030e0303090c120c060909090c0d1202010b010903080706270f0b0105030c090c0a0905060d0207030f110a0b0a0609090506040b010e0c04 81
    0x80440810b152041c1000179280e10500f03015030042c0c100300c440110b20703a528ad00b084205070b03d40e800c0044011b4282500e507514541003070007911503d0180110001d0410358400a4201400f90740646140c080000450b1385078549612055680e000075510203000754500c64044d288000b0000f0000200d9a0041a00c1d00f424020b00901240040007440e0480034814201c44080c0d540303600641241c0c003406800c581104002c1d456003e400d40300301a46490402c81504002c1004c2a0540162400d5541c003031404950803400400c03e01e20904001d1603a0484200000090f0401c280c25810510385881450108426a030303440c1016220401d08120030341100e151400140350490200040244011504219003038a03180c6010403003941000c81c801300c480358001005030905800400e04091285c01e450007118000d042d2641030f889540705000184402c0441d80840d641e8503c5401410192800780c00803c1200c0e003900b0a0b540d0b4030020788043c0e078011203000c008101d100165040030f1040e00c402420602d442d03c2d003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 630709289 1250 630708039 630708049
    0x41b0309060219020a060b030a0b0c28231207050c030f1602130603052d0604060518010501270b0a03050715083105030c010501060305071706 62
    0x160030100d0350194208000b85503803614100c1803820907880d03070003001019024071301842250501c4980030f11030307809100306a0003d90882041584513581100003616240c0201c5040d0b0303c501c17825400740740e092421a540107441d030f108a078504000b50700510744142c1d09114072848124860b05001e0340c0c00c160400c000446290050b0010b1544610540444e03140c07801507040b26006800c1244c140d000f40384420301a2003546071103000d1226400400e0020405203146565060355a12583c2c4441d01c24031030070040fa071290100845036181c1d240a90300340c0340b4a2615240c040018102200c1000c86c88100c4140398944e011305100d07071416140030042030508a01003003c0030070000c00b104a04400541c644c01c8400300d84c0c8a001d1450020351244c1e0041016500700030f18042c10f031480d8000b080800c00c03035508104103c0c0c640c1c0d40c0258503452403541c901400c00641321400300b01020321170203002c5210010f080c1e004400c055100038125405642c00704111348071814201c0d0100c4d1261454800c0807544004150a4500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 630710539 1250 630709289 630709301
    0x160314040c03021504090f0b0a090e0a06150f090c18080d030515030a03020a05011113030f02010221030105010924030f0605100203090a0b1306080603100f0b0a05041b03 74
    0x91000550400e5902c140031021f0302c1400011180381510340c1e8080340c00f42444180171014040c03045050014403040345910f0760b26205183d0280000d078481d42c0d110354079150049031601070f11410460172030154545440101514010300c0e0200001c0710b65402e5109480c00086a10948640300013900d0000d16000d4120080e103c080c0040024004411a4000e181c1e0f0400624203602d20a4018001003446418594211030040d5030000d50201c0410800804c01f50400c050f1055a60041201001c0c0c4041e00040345441c8801404c444000c420000c1d0203802000c200c069412260241c2c5e4503445c01c4d458800400c440c1000d44c21880c0d1280c230981403099101c0c02604040b1105080003800110b85503182d00045c0342c040a0050711003d81c00004840d0304a06000c0400c20281900a49040c075102089500100910b9940f0440301002140008104590340601c0b0600d1500c00320700051240c414402da209006022469a9a00ca0000c44500040600b85402104c0c20b84007440307110f000002d0b46502c26805041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 630711789 1250 630710539 630710569
    0x2030907060509031903110d030b0d150b0405040f05010b1518040902090a020403060b190e09070914090d030b03030901030b030a05060c12010609050603010312030f05160314040c0302 80
    0x2178041c2c0d0102406190511040b07890080ea95245058000d0a4060030407080c0c180440825041c41820841520341c01810400a54003030a028251007054005000800407004200d901c1400c1106210620140c114404ea12a01681c02002054022020094945d07400071029080c0352b000d01085000d6844540d24400d85400584017081c0741720503030300007621a402115103101996001c2001d0080c86058031a414442c13009450040c40c503103003044d209014203850b01c01c01188a241c0000241030341c106200707040040c41c109800344013501008940c103e510304c1c100c40e84c44a52091064200805100c0e01484c01080c0c0c010300510b107064042e000450203031050f00d1049800d0f00c03e01030f0400000d8820001c1ca0700c40c2c000c0705401a11401a2110140c0010042c0c1c4910b081261500041c49541c3e140c208981c1100d50251025840c0f0290700001e8014004031880300c1c404a207130400b0080980e007500100c3c1d400c1c4005076420000b0b01d008000c0000e0000003500d0260030000200000c0c40103003400030b2000b201e58 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 630713039 1250 630711789 630711793
    0xc140907110c2d04110706112214090403080610020c030a08040e0c0717030a061d07081003050a080306011808012a1e050f040806060a090203090706050903 68
    0x2640200c0070505060403c07a50b000041e0304950034108800c10110a91940c500855050000200305600001309018401c8040d05240e9507107001c081c401c0030300342282d20440405c024030210700f41d00e440304810024180329200118008940f00740e01803601210751440380b6071584038003000d034441c6018401512030900310360341903200301f6040300011341d02008078040e182d00c41c0c0341250361b450030019940d005040107072610104110038020107001034002140c0580741001100300039102e03910191408050314165102c1920701c0c0b50243d20301005100c1290a520403010707034803402c55139152042584000c03055440050f0440c1c03c41c270000c4000441c8007009581003481403400440203040107002408240069202c403071180c0d50b80000381c514204880307201c1000040300d513030f50003004020303500544a610046440c00c00041048a08510540900190b80b98800d59403046600c441c0c843c02c0c490f644602c25118280720300580b8000149000c424001c036071140300401c018000c06841c103417041c0c40070b4120207070f40c1d035042c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 630714289 1250 630713039 630713053
    0x1704120908031b07090606020d0c020120030703020705091303030209040b06040b131a0d0c270f120f020904030306030602070b0109180507060f020106080f0a0c14090711 74
    0x1404208042d00f01180c1c0c00c4100008100c00b0f0700200d1418420341c4c0000b09150030701d0002c001194000c152040c40c11701c28201928901d220b440100d844251000c01c60400300800c0c40c0c03010050b00f00002900d030300f0f4400e4080b512202d4403001006112103007201c1d5004c2c1c4100c0c00c01301c0c2000a00c20340103002607180141c00811081c52210001328180c0040c0c114954002d808102c00c2009108141c100d001410300c035407100400c8001422496891150050348100a42c80d00768510002d84039800f2030f401c0003003850083c0540002d0100c00c02032080302d48a0780e054800041c501103480c0325140840d03034103140d011410a011903502e5080c0200464028001d0b000e040e070315400040414010b00080500c2d40c401d0014108640c1000381200c00c4515010b000034454682c141250300041002640c0300c240c50850420302d12070202108207d014000b290810700840c0204a0b41a01380c41c8000b50f055103191240380e508204540760401030b400c110801350125402036010011500b4203010303254000a0960200a032141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 630715539 1250 630714289 630714299
    0x30f0c072105060708040b0a0216050109030306062703121101020a0f1706090606030a0b041a03190b190207050307030f030b03010b01120b030a050a05070e010617041209 74
    0x4032100d20500d01c9080541408a404020342404030540c400c1c0a810111174600b8503803181612460020005c45501d5400a40100c1c48080e2009031003090f50b100009000c036256914004016106511400c4049104903030b041d00035105403102590802c01c03950003600481d20319200d80e80707010028400b21050110007001040003078001c0c0001d141100e195217130150a1801400010078030100000009801100c03941480b83e00c0c2d0b40c00d1071041e0030150480302d0f0381d201d07190703041000001d142e5000441e601030b10780007450906200402588581c0c0d0401c805032041c0030012140710102000a40e401003600c0d621a0018a001c449032005c1342801500010044c28820240c1d1074518580c8244ca06030080360340024400c040c00d030305028021004070b09600a01c540841a00040c10454a52503c0120305444025240d002d84040007071040903a00101250380040141c18201d440e518035006a40d1348403620000480e00e180100c3d00846c0b000394031608201550b4076600c4148d02000008076810402c0311907003000072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 630716789 1250 630715539 630715559
    0x90f0c0f06140717030106050a09060903030c02040902060906070b0417030601082e0314071e0603241203181a09030106180204060e0406141302040305120921030f0c07 73
    0x1002c0d01f929124560b9034000540e001e404a1140d60241c000c00c01558020310000307521160700083c00d681900d002c1401c40c010703c0041d4650240181c8241c0104020a03401c091092448840340658000d0b4007070303c2100d404840a030103901c0100d95240c040784c030000100b200b08107411061030b106010301816042c0b00c0f035100c14800700d007030b1103034030035038020281030036103801050103015007001131045600d40c040d150421003040c2c040d0480c42c400e00040c140c0e1100511400c9a07024402d0003c012590105540030303032203e80110b9140700c00c12050300043c62014608201c040304010703d800f62810244e455420510558082c40182d11a0f030850380c01d5500d61f4000680201c1e000f00d00030030305040c40c0c0050f8a590800000808004803010100e10888c01c0200421100c600c5401c1c1ca41910015100f0300111507581c0410070103449550f000800a208400d10b040a090a0308007403c4044422607190b070b11022a900d1140319405084180186038108020320b811410400008007540480d900503110b009540d0f81c6200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 630718039 1250 630716789 630716791
    0x403120f0609140f011505040518010819020303030a0f090f03081602030f0306010e01020a170702212512051011030f060d0213090f0c0f0614071703 65
    0xd455151610300500010b00c0320702a0800550850f00f449401e441c10707040c0801c0800040c0700301040e2200d101509200c051244003150050034000d000c0000042503c40034002d035030003d11035500c140c01000006088404d503001c0304d020030345e0002d00450454171131100c10b40c003c3c0743c507c815042c1d0315960010303031001403a02c092550029000b0b4842d1401c610f84485685540b0309040b200c50308641042044071416295001503d41020080c6001d0102240020050740340640500015202c443d950b812402420041c030010101180700740c0d851800c0e19001d00e594440c1c0320f0118025811900012541041c0d03120640070b1000c43c492050852900c0ca41c1c4030b024441e0820303030352015101ea8200d05641448030346103015507607000c40700c10323452855890000303840100120081c10091244802000c3e0209543d0341500345840580d500a0400009403245480c103c90500c1080403201703108803031000580d018142e01180102c481a4462444c10075030341000079515407008404583d503000303030340c4883d1000307020402031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 630719289 1250 630718039 630718061
    0x90a06030f1a13051903210501141f181721030403021e150c07050705010e1c02062a15041509030e090c180904021503040312 55
    0x15121040c0c4a2546103100000f4085030891000600d500c1c0041c43c00554104a0581008030000021403442c0495400d2140c065540025480451510340c418481d84031a041310310202c0802c69500c60502803000c11012a8044034000e90700c108603160080c01038403a142c580082c48107a0b0aa00d8550740b00301d0682d100080c5040c1d26a109502d000981c04c1d801c1e240d0118030f03804054950071440c0942e0000d5845008081020507405c1e019000e800852040040086003405440000d0300d5152150200d0143c6d007200c0010742e5140700da207070001520b5008400e2009068400752a840740300f0f20a048900c0060003000040360404400c1285401013000c03004d09070341c480300d10005062406858056140b804c89200c0042c141144031005010014610704500b040600c1c006802061086c1c5a040684d00403012148480c1c00c40403010401c201c1c46031100c0200703199190f500c0c804100d04c07034860500c8016041120020342251040d00c00542000c60000a0740e8003901c689041c40030072602c014001c042c0c0742a5440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 630720539 1250 630719289 630719303
    0x605070b0c092d151b0f030a0906030b06040311101107090507020610180b011101020408011410060c11010e040e03031b04080304031b091a130902030c0405100f15020c060711090a06030f 81
    0x1e00007241cbc140540f60b070b12202166400e040c030341161203004900b240c042107244220784902104c051303075000b100c18412440c0400180c4052664800c0c1c410040c29049135104010301403000003d006804000ca18816100c00e403111116001500f40040010510b44400750b050120703048805100040c240010070141020000100700e10b800b4559103c0d41c3c4201074848400100545420300200354030201c4171190340d4100c20168010028100142c2e4010041405180c0040c1003400c11035148400100840c001c4111140246059812600300c01550169002c0c2070501d8000b00010800724844551481c6448072001040300d0a41d654a9040111491304062854542564410b11090300c0d01d40c94401c04444400c8091000d64500d90000f501c3e0880d1b40c0c03045108680d030740b001c031b001c40004884100103409550355800005886204940103455504040c400520409010400318100403045d44c1c4a95481181e401600030701704104032890340300401e030343d600c2640d5010020200710b2000000f5290b60143c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 630721789 1250 630720539 630720557
    0x906130f06050c06040308040602070602030a06030201080703090b180708030c0f010c0c0503091905040f020306090709120b0c2a070f0605070b0c092d151b0f030a 71
    0x10040e910880c07580001c003405800d200468000e4004611280d0056040c60010082c2d6910f01d4171200a001c0d0300000742a00e4404070030481300d07401650100003078034000d80300c919259403840022030a5606807480203040700c12204c04030322003648130231070f4141c0d010110068445564032624018595080282089c409034440c04840081c02c0080c0b20b06080701c001071500201901c8652074640c0d4078400c071402c640c01f81c1d601001211040bc100200c581c003500c4010000c0c0044140c1400c004040e41060f41d1603071103070300d00001080041d4080c507195400c503001e00112030308901041c0c60350304d00304800400c1381c840b040341007017003a0062840303003000c0c0780c02d072290340801141519284456140c000b40350421010ba0401a5040c0700f801c1d0004262032445500002040e003554030b00813481c5a6028080c0d260350020f00d241c8107640c9a802e079081410203c1406400100c28004a10400c114401e40d0107426a40c04c104200788001c0e05a283d0414450000510803a09208803501c00c003441d550000c0756000000311182 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 630723039 1250 630721789 630721799
    0x6091c1406100602030406050306100903080c010c080a0902030d0809070306051305061509010504180602210c0a1407020103182102010501030236090714030f21090613 73
    0x452000343c1001d1000f903003481d0038008042c060348400752440d40302d410303074100540306148940e2403440074543c0030041c2a100e294604140c2e0207400c42641110102c1d081700005070041c01103200d0040e070309400600410205101038001d0b1600700300500519024081d9400c0070020554502803103002c1c080707182000007090540c2c105181481406030155000c0b962256285403180c1d02c50900d18150340b02104c001540b40d044101e404803105040718010005800030591003044900315229071099007808001d0070322503442040410381031140c407200101264686843c0342150701040081c0030300e18030605000035000705040c107030f124090100004443c2e110000400c001d03607195002e4816030b00e01c03941c00240b085504590010b21000c0c15461074202440e07e641040c0e251001c000340c481d8400c45140d11a004d6800c0403500700b9161078a0b4000c1340c03c0841c10324049103560500142c0f0785e2000ca40080a0714410b0031078401d00411030702e00d243e0000100000d0004501075502e07180180704056004412001e000d2905c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 630724289 1250 630723039 630723061
    0x403090314061920090103020d0609050a0e061306050c04051809010b010906081b09060309010e06011a1b070b1b061b040902030907030c0806040512040506091c1406 72
    0x280f031215441c01e040c4182c80c03180c41803594040d001070742c81d55a4240c90b80e4000380101c00038010120b12442003400d008000801c03940c1584060f01411307818138240214083c07841400d0f17650038240d1340c0c00f120501138051440420800c0e0b1205410804102c41c0c2498079a8074000200c001c04805040078458200100303014205000341b048424241c02820164001403920502a2001c28000d21510280d6000c05042e103060100004803110750714014440c60f20707420b1062a4600915140b090507450307104100021400040c0303890250203110404d141e907442e040000d034942450b01404030b8628203a200307440c0301140c6111540c1c041c03d140c0c40c1c1c004400b01c207404070902440c507055004d0b225a2640d060002d03001c1451900c1d0007101d0a42d1119140980c0c0e031345482081c02c0c540241d541c0081c04c2c84484003004203c403603010070303141d0085000314100d5130307600703500d03203100201340b1452041d00c0d400a0308004a81072820601489484014072061411201000d40c0345e0090184405030760b10b155400003000c10403241e8807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 630725539 1250 630724289 630724321
    0x903141e1204051201090f0c1a180103020c0709060b07060b0d030806100e030d0305160914040e03070206070807140a0203030403030c020d24060b120c03040309031406 73
    0x340c8001c248036101501d1412041c4114000c03240502c010203060b08198000b50403414045500c611802510303c8a0b00308441800c070b15000b09610400c90b600170412460307052095542820203caaa041c0341b00710b0800540081d4007082804050b409004000124501c2c903200f400c2c010515400303d5030303a4510514042085404c400200d40c0300d4585070103064046a44680030725404403040c0c1d0400340941c881b050540d4003080518115a051280c4200700303a896915401c854007804020110741080d0606800684504402c1d0050910002c03414003085035078603150b004455200d001c20213507440e024240e004076004d9400110141c45102000907207004101c13030088140d501c0d90a8502070811410180d001940700e1140344005410040704030000030940d41c440400c50406a408515000d000340e542ca207640c120852001c0042141d0310300080001c50480c00411560100041e4010000c1c0c0c1e40c03560108149a000940140c003003090404000c00028500c01c0310300381c49095080108a5440c10074541804d14030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 630726789 1250 630725539 630725593
    0x15030203010f0603230c121e04061d0703080a0f0c03080a0902060405030a06141f0e07023d09020d030e01021204061d031501090903090314 61
    0x110400040180c00b15919411060320300915000c00c0265921460b01c014254a080300d04409500c1000e104a02c624074009002c200703c0c22100000070382d210401c40c81e0f24031548240b01c5409240d0400100000c0d41a404204200c180c8011140c646001d550428a4040c05820840300700300000f40309000035030050140054241e8504d4540701680c000d0741c0080180c4e0001d001744545903200e030040d20456403501f064401134000542102c02c184107500b080b0000d40b44508120b21140000c0c00420540c1c07101c6044610380e1050318070f00d003411b5032800501ea0b90b000001072611085014402143c08c91107035400c4000130080c2c0313542d229901c00c062000600c05403102d440622034400d28000d521001a10307010b011408190b01070405408003001840103030b081544034100300f982c0e804000780200740c1940111400182e03070901d03006070f020864107200b810b60f40c0d0b0035042d40500c0007801b030300104034068240c0c1040d10307030621900d0000205d5589a6815811071181001c00302180c2108400b480e8031280342c0b02c8020320403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 630728039 1250 630726789 630726791
    0x801060e070210020a0c12031a040203070c0f170301030b01080d0503013605130b0c03060306060d03050909240d031b03030b030f210c070501050924041503 68
    0x42801c0c10041d41c1d80059600b005030950300840d030381c1c2030030740150100004142c0080c0482041c4542d02002030081c0f24000066148403145402280d55081270b100f038900c00d412944032801031072015186d107140602c00043c100e0300e100c40303115420310024a900203940290700c03445640304954104800981070104003120b030010441c050004100f43e1801d4519901852003030410b150b80c6801a83c84501c00002c503014850b030040c00d10060044000443c0300600c0f01034081d0410039038a448000d09051580303c00e0b64443d40c9503020320b01045942c9440c210030640c2c035100c1e040240c03804002d034000c5411040c0403900840400c812894290070081d43d213020b1041c5034411030351051030300750f580d40203000c50740c415032078035810005c2c022001c0425019a10480407000300808076000e20401e08403841e03444160b44101100c142d1030303403c44108180d15500351100c1c0d03481d03100a86012070400380119900e40049a01952180043d03440a0100404e80150410b03007101d0020f150395141482c481400d040070700301040f0105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 630729289 1250 630728039 630728041
    0x30515040309090e0c0402030703020d0c020d02100b06040b0c0f0105130b09060f0a0b030a150b010306050a0b030415020d020c01051f210503120703060306050a05060d0b0c0d150801060e 81
    0x3c41340109520740c001a0842c2c4c0142c480d100c004007200240200d01c40010860300d8209000d8401d5000503c060320025681c2c00c6030b0509000244080a60720b20441c0d280d0402401d200500c6074010103400380c0207216200d07084652500310001218207490307041e941b144620ba03502d400d003003e200c855140140d005040c8801403215041015041080105c02019458071340ea84411070112942c0612000418581203150141810b450080c1e9400400c13280c000c070780c00f20f854a54009076600301540c3c000d044130cc1f280101810340d511074860346002c0054411900300e4950801c0340c262106074a101400c0e150440100020f5240b61138115805c43d02000d00d075511880719416004c105000c509d030408900203429a10980362030440d032928a20b94018501426201c50300001001409589036000000b101d01400c000d0041752a0560440c04986041d2421034010218910410200b50f80c2d5685580003075813411520301d04403504800208944078610381141c40c404201040080c41001d0060001a2000100310026 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 630730539 1250 630729289 630729311
    0x51318020402220303050c240f1015030501210c0308030408090a0b031504180303150806040503130f03020a05010309030e060d0b03100e0a02010813060c05030901291903051504030909 80
    0xf045a000304031000c100c000344001404401d00241d01c400805080700be80c202e403c0f07070f050040c02a02c824000c1000d2105404102914510040d5006c060180c105038040001419500d0b031414a40c0010f0081c1c448800400002c505615031001c18001090ba00718070b56203d0800510700484ea81402d81c1c1c04d442541001c03658240c45c0391080a02554075450b08000034005502d0001080c0c0100300c0d80b01960a00480c0f0400091010120003081c1e130421025040a9464031001c0c03641d103503251404082d40000200c04240040c1d402680070a0006d4000d080118004030420005405517019200c0802e40d15104d16446003913040400644c1d840070613410b024040400c0800c05556211203070303000079040010160205000541d901c035000d9405400440034000c450000f50041e00541c0242c48040d07140d0310780300b00090840000c24140044e00440d035041c080d003194080800120b00000c41030030150f03960300c040020004004001f24420800c00c140313a414981b4150078090245222a03200e48002403c00f45580340e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 630731789 1250 630730539 630730603
    0x10b100f021006380c1c020f1c020a050d09060e0609060f160507030b15010c0507060815130605120708060106050a0c020415051318020402220303050c 66
    0x84105400700000010031040c1901c46600d0442e07101d00f2058800056240c1940c0800300d910540c13561540c6c240c0c106081424001c13680d5505990701c480c41a082044134078072851214009a070b118465104a85e9140e41c0d545410342440101ca000f640031481c415010448642c0101c810307422980215062402c1200240200701d45114100c0720071080200010a060344c2401ca1880b490130b990045e0881d020340c4e13140e1400340d60800f82900c014001d00e0007103500c1324840d0710079403210030046d50100142511a2601038156404000a0070100c1511481d080303810050b2a185100e010400c0182c00c04641c2380d1801090140701320b00c5c2e02c0540040d070801c0c03505004809000414904580c1d0620345542d6a81c03240a0440300c0c00345e0450000d500c42d041c803004110104480b00302906989080340c02c010b45131466610b100844101000364203055440c3d00d4010f02514095001d418040d18404541c80a0700a110480e0b12481c119081203002c96000725030004070010800041070003c02c0d03803242e60303000005000800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 630733039 1250 630731789 630731819
    0x1a0f100f0e0a06030803040b04031403070518060c0d09050f010507121b140a060b0102030a271a130501081017010905190302060f010509040212010b100f021006 70
    0x600802566010070700b050364aa03c007400035500040403a45a080c10319180610310307400d81e02134001500188083c100076500b0403c907402548243c035034900e030450545040c40c40e804600c41c516403180062082025001d4240000c81c2c608005075078240300c0398104010425140751001c0030038104901485808000703000c9001006c580b070146c0c20102d0750103400f0803113005504050b21004041c41040c00041d82c2d007040018280840342e100388014040c078102da100499607400380d00850000181040709292070241d0123300c0070001c0103507204882400741c0358951000d01040a2004a1015400050182d0040b002c4e110482c0600002d1a006455042020382540701c80d5250117a8080341012102c180d1615509500c0150240d60110580300e01e404001017207002d0001200f4258054000c035030000c0d0503040ca0310b600c1410398a00400c082c019440e01d0b021720040c85004118440c8566a8461903201c0baa10100b8200300032000d9071700d2411600d000c15009040c03009240d007200000303040100501882001c0c003604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 630734289 1250 630733039 630733049
    0x126010e0c09090c22020c1b0301051308030106030c1806090e0c0c060a1a041407030b03010b09011412010e032119020a03110d02040f0b07030e06090d1a0f100f 70
    0x380303006003107141d030024411404050174600c04d008100b0844411440c001940c110109e000300540d6680d42e1010704101d6000100502140040005005080c000c0c3e1201514000d03515100c2c00801d100c1c0b9120b001d40e04103401201c08035401000c10010610f400c03030f03541e40c010082280c0c1c03030400741101c0e543e42ea42d28000e0440c0030a591146040c0c84046030614090f01d18030300c010024401e0350742e03200c200685070070180d54410000b070030107414849505050040c420750580140807800d10368644544410780c45080440c05900030641c0b030150a003070000b4014500031402840c00356a8482c90307442a542c1d19440c80c038003c0501080803003044005030f501c0521040701c4141c91070259448903281d00c02c50040c80303109001d50f0701860100b0010544446a4040c0007511000b048815a82e91500704540a0740295407008001402c018052081c5050940151210302009012015980c1c401e5551006824240c0e5040041040000410540c1c04030301d0051a004504445640303909814400410142d03100e42c010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 630735539 1250 630734289 630734329
    0x212012607091a030307060501060e01090503071203170a0f0b010e180709080d180501051c02091311070203010c030605010207170f010207030512010b03010501080126010e0c09090c 79
    0x410800050080ca08081c01070060540f6940d080d03507e80200140130a006241c001000024400304a5010300c041400740c0d40010300a017070003844c1100c06c44100d0a0003a00302d04100d94150307400d10081c02a11a24068010342c00701145480040b58102c0072202014046070402c5140d03191580b281c3c80f43c101038200d50040350381d15aa69a51030741c042d00c1599540d80311010903c00c0b40001c804c0f00d5445610502c0e9100701d202d258802d140c0e42ca00440302e6018954800e03000480d803152107035020203203070b000b410101d41c0a000e0440c842a01200802142d00d41000200d10440c0002c094003180340a01c00c645042510b4141040071a0421000039070310b04260099984299201c003103191011000c10003001003654240095560b0105490b0041168208840c070120016080d400410004c190780c080d01c2c1030358010383d01c05019030f180a07198907000342415450020810000000703a0031040c2801407005030904000103118900c503000c14043c0080300101000481d421400c0c100086917101031405d402500d01020f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 630736789 1250 630735539 630735551
    0xf1b071802090a0e131407050102070e0403050301060807120515040e0601031511070b0408041701050c03070c14061512010b0f010305040314040806040309090e0706050a0201020409021201260709 85
    0x40132680141c1800040d2000e4051b00880d510380c2000a110300a440081e400c1c0d07000640d80f007100c00078680c400d07200140851010b20051102602c03e94038240e001d1594601000a265603010000c101c0b001034903900c003014050344800f8203505050040000910540d00200ba07907603d140c45c5c48091899030490224220f485000001e200f086902c04c0d10021a080800e17208034ac01c1c81d02d40708250341d000744520306e0301c607083c5078400958841c18441c07103100d0700c90310480520715074039203008039212140003004403222003c00440007030040d01000064807032000c5007184004c50300200c040017040700d044080ca42180c4c1c103002d102c0b04035440718003400b04040c5003820b01042c2c5803605d04d82a06c2c501a410521041c19002080c0000c80e00300c0044d11034020743c0241c41e58202d8944810003003080c1d614003119035450b50300c80c410411440748182c00502d41b80c1c2c0340e440011f080c9a16804031100f640c0c0010b04e14120986044014899005208660070403041e0b81d4140b42c880d01d031100c040c140c48895038450701c18002c1da81c075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 630738039 1250 630736789 630736801
    0x40504110c2d100209150a0f0c020a0b0c0105150d0f0f110d0303090201081008371b050a0608011401051e12060f01140f1b071802090a0e 60
    0x2c0300d02c800301c5000c0001e481c104000ca04a00f402500a8091948101d0380014003009202d1908211640902c6981c3ca0304900d40001c0c5c01641c1c0c040c090901282c01003e103400c0061400d041401400c1e01c01c0208001007024105200755a904001c51303601103100380703513000e40000050418084d01604a5001d0340c4450341c0c00160518040030302146a400b0782111000704c2c003004242d4164008902140b00342c0361214107488401e41246545014080c1d02e103d0380c030100c400109040d48824014280000e480d21040c07018051900f07040b1414221002c4884070b10444030004440c800c600301a000c1e1600355070038181e5518042c001000050184259603400381c1c001840b4159034842c00840d0103442e80e1414a405071992000d80f5a51541704526150030000340c0c02c08900589032050b0b1a4040c110142d40f0501e904081d4100328856030b00c6403984c4550910104403425908180b001800c1501c69040c1c00381c407500345000902e00c00406824401d038026441088403e01d10768407040800705032881305c14030900580c0c2e10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 630739289 1250 630738039 630738103
    0x40b0a05040516031104060503060d020f12031e0c0d11190c090528020a03140f010f08160e070e0d060501060e0621040201050f070602040504110c 64
    0x6500a16001400c140c100600b84540121040d21100f1540e020014158825000c0d840d501590107004001001000070506520704082031605050005010b941441c40c102c001a560442e035518840d15a0400700300c1213203500c1403414581c000001403001c0c92900c400d040c100c0317440e160070b1a02c0c80e00f408908291000d030300000304042860f90712184003804141d0041d00f003103d000f9030325101c1c101c0050b040c0000250344d0442121481652005408001d244000510340c51029400035200a020140e544580044040031140107500800d8883d40080807941040480d80064601d6000050349070b000c14419450b8041300042d5904031181c4031035800c3c41e0f8540c0001254040480b68441d9400b010ba04103100070b00000740d0005040361610703250304010552032414080b0780d0080c103240042401000c524840760118456000303902034414902103141100c3c10030035002e0380d000070038155900c0b54041024441c4e41494440c82c1030b1092801d0b00c036400c044903a00a0b65454070b00324141c0101d1360104000368080002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 630740539 1250 630739289 630739309
    0xb070203070b0a0f0b01050c0d140f04030803090106080f07060c11120c010810031104050c120f0702070f151206050301060806060418080f0a050f07050a0212010515040b 74
    0x100001c804000e0400480360700140c136400c07201118003454140000242d41c09107040f50540c416910142ca40750030320b0b58041d00d040004802007030f40301c0b004200c4515980500e0000300059441501c0d0651a070820103003080c2100c0154101c1c1c0400e41c8042861005c2c5c4900049402c2191114075100c5116045071030020103201800124580254035400d100d02402d0011513022410340082c0d80784815075950310211284100584400741190343d482380e159a641c10990440c9521480d051402440c142464580d41d0113481d04a40c0d0307940e050980c3d0280001a075050100400400c041035004c0c52080c141410458540d0061043c0760a114140c19000c483c080c2d2501300c0002400000c0c02003000301c1e680d210058889004841032407080e031a20700e503601c1d50301001d900320b01c045030890740190a1450841004055a003c1c0c443d0106000d41030100c1140303804140c00030721102c1d10443c0a000d151501c0d10601c82000e17001650080303180d04000c100328101e1001a40610207520455011900761200c501081402032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 630741789 1250 630740539 630740543
    0x9060e040f0813120b0403020d051606090602120c03010801050109051603021605030417060123060a020a06050408070308070c2d020a06050a09090b0f130212010f06110c0d0b07020307 80
    0x4d14040d2060211131a03907644640e00035020b6402c616081d880413201c5102d080c640704d500c510b10721b5440c1d0100d000340d400003407803a100d40030041c07610040c07a034042d2411078100c45c101c20503030300000140100e0034280503490040405240a12080c00d0003455503a0100c5000031080c201940400c044c400000d030034030104002030300841600c0e44c89860303406002c1c7d038000a851401861090800029120b000042c072910250100008984032080e40000c004555011301c0381d81003148245241080403c1840c810780d070040e403051210700d030384140c039203000b03400084010600e909000c4126420800300d08094000c807a280c5513660090304641214642c01d1910310381074400383d0003028400e0b02240c1d10750400000c010396011603e44440da56030750341500e8280c88c880202c0c0b6070441041c241412950910140c1041041461207001d03041c5150701c020700c0c1200600b6030041c03000c41207691081101c250089440c004041800002c1c180c81d04640d0301203181c0103223141000f0304800500d400190b8451090083d691400c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 630743039 1250 630741789 630741809
    0x8090913021e1e060921010c120609050f0a0c0306091407030e0610030809010e040e0c090109020909011202030a1208090d11191103010606030609060e040f0813 70
    0x240504020760505a0380c201c64010b01c2c0b000e103504988243d6450300d03001580000c0480740f0b030000041c01c2c059056a05114881480402254011861828040c1d40e040600b56075810140e409a000c00c013081d40c103e03a020300300c001d01e04402c0c003144208c0d0114699101c007100300049000340e103001007100240f076243d10840d0500d1414024040d14504101000c0c010700d555a001e000345446040081d883c1c0c0c0b07083d01c581c0740e503001150302000041c1c4104094040c8040506281c0c403542101c01c08101558800310f400000d507000304840301c0062a108102c64050140c0707410850174204030754081411198180154128207551589010456408000c9440b60642c45034101e019560340340000351203140144c64514150080c0d14407150040d03c0b5040703040800b001c4a0041040d400503414060350191404415038003042065128002d58a00340200c20040805960028055140c1200c0d00211001600700c0d104001e103840600001c2030840c2c0003c0b8000741c002d040d0700d0781d030052449000616940b07540040124 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 630744289 1250 630743039 630743059
    0x806010f1115040b01060212070b091f050f0117030a030203060d020d0b10120804050108041b060e0901080307050c060a030603060c030603150903021c0309080313030f08040809091302 80
    0x1a0710b0242d4901d000b240302e5101d100042c0d0329010180e860b4481e1116880c2d03011014001e980c04588d202c1c801c69081040001034a045009008a0702d55007131034003203000c04c81a1074406104c0200f64a0800500624000c598948100101c21296403a03100e070400800c101030700800441e100795202d0744411041a80140080107018003840e040f585118100c0b0002d002d01b41ea61000210280390f481e585103120360001105141c1400c180c010b4903407130340160003502c0c81e80303402c1032813003409040006e071002501864613040701010400c000c10907540c00c160400e0324560014070099000a80004003140501d50481351191a4184260b04800074400781d880940b0041c02c15200384080c581542c040400e80b03002c2c152018802d0350b110030842c00d950030004002c2c01a440510441d0260039108000d1801010518001c00c003152503480e00c00c2241c0007503c01000090144e9400010550450041d83d1031510504280035180f034551110341543c0035030b0b0a0240038451030700c000740002c0c2801c3c00785181c40d54010901d04403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 630745539 1250 630744289 630744313
    0xc0905100311160203060702160308030a02120907050f0a18020a0c150c030b040203160e030a020a03050c09090a15110c06040507090b1509040f1503030216090c0806010f11 75
    0xc0c2043c40000e90103030141c0f80100345182d01c003149015254402c4d2482000c920b2540d034819000703610003003440030202d90a120103010711454884140c01034050100602042c0c0c2042e0802001030141280c0c1403040880745000c01c690709400000e44030341c3c02e0070000107850304500d6209a401138a50000142440500c54010500d0300603540b0410f200c0b40b09590070402c41d903500c0d0520040b4030042c0ca60506410400c9209002d1501c5148101340099010302990703920769060f8089415440250011a41500510711191721809c25640300b641c40b840d1180107100c1d81c0201c0d151222001d00d44240705015a894503801079108040804948240c22a03c00316030440c90241001902e404c103e02a421890b82030480801c04e5160008903800018408041989000b1101d4104401014459000b9000c19101d0300d5a40c5103c440d00f100400542c003039005004060141e25810ba40c1480c15081a4181890042c4084400e0384c0100141d80c00042030800581c1820302035020b0320145d01014441c201d61040c485860340d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 630746789 1250 630745539 630745567
    0x2010605030c1314040c0e10050616080d02040f05040b0103180f021908061602390316030b090601030b15030a060f09021201050108120d0b060d050402010809010c0905100311 76
    0x7003240e0711043e0781c0b0001d031500716900c409408c10780f26a95000e001441805003000311818820b80c0103108108091074000c06000350800c3e42c1081e80410081c500d001801c0004d81864050300b14083c20034a010006030100c81c0c0640e001c00d480306000340640e50030013032280c2151911701080c0003222400740c482c13801c40e9880880c0b170307501e0104803a140c0c40302c40084c2c0c50780c00c480d0001075140c42c031210500c150180610220031140b1400754081020b0b80125800070500d1141e00e007407100c406c00c1160540e140585509600b41101d510740094400b103d1548440f004001250003401e009170804c08501d66100703100d021a00103403038644400000f5015615104014402c680c00d44c1c0802d04880c0f0075640241c044241d000c00608885092103591070603048120100310075020f001c010201071340c0d80303080011440f41440c0458004c0d00541341c04121540d440043c00195a000340308140d00c000e03084001c1c003c5c00710010b00101200440d00c01c3c3c50007100d40824a11441d070113500001d40750800c1880301602c0f4010140c5081d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 630748039 1250 630746789 630746813
    0x140a0506040e121c02041d070f08220f14061609080d050f0c07030302010b090a2904061a19020712020f060c03070b0105030c0102010605030c131404 65
    0x244110714200000b0540d0001094030350b81c158450090904021000d000c44014040014150b00c804e5802c1201060540c0108810340d03159243c0880c1404919180001030020050080d040060180c0c8008001c041c07610b490111586006d07003105103032180b100b0303d841d400d40110340f140100046015414400103001c00103000384180e080d8900800303145040c100030340742c418050040d1001600540700b000000d034005c10003007480c691003402240c509500041c1c020300300380e142d03002240140d44901c600d44a9107096100c21f50400c030051001c201e080d00d07801c0c15a003d60b2090340c0b0714107801c001070700b000c4244d580d0b5441000200741d800d1120308002c045842c042401c0d07111000c2c0130b01e45070303007001a10005440011440d0507200d0b0120f0030704084000d9002c22042c03940782c201980d4041000c1000c0b040b0518140054003095114a0030300d2001c0d41801c00301410000408800e60440e80743c4101003145980002c1c100c00041003c0c0c80e128a01c080e0180c01401400540a6180b01a2180803d000802120303400f49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 630749289 1250 630748039 630748051
    0x918060f04022a03161511041503150815010e10030201080f06040906020409020c120f04090f0e07080312071d010f230a1b0b010b0706140a05 62
    0x8440311245082008a0090a26114509160303002032003e01841140044400b0300780320803681006240c43c5280c80700c042642040301c3c0b86115440340303080c41d440c50003070388640b003a50418181005e003405000c42410000c000264205074481e8140075540020b4910140523022100c15600c000103a0084803510400a10444050203051400140b00c00e2030103d1000540b68141d4a519449c1c8540841c00d002131005442c1c954060f945a00701e03c00a94a0f01c0144020604c08402507160312503010704a042010301e512403085d410b0b04224201c20543c20000300c1e820354207401000540101d0181d00c100003410720711132004c414450001c001c603d40c0c9002005e400c2e0403021620180d407503503d43c10202c0f114072502500783c0b80d20917200c6c0d40d60410740c000d4640c130460885a14142d030035000c07002c0c2d40c0852016015a9100c0d181000610f2102d503e034404ea48012a014804440601442603551b40c1040f000520420010751030120740714040080c2c1c1d4200d101510484c0e440c1d1403850030f00d10560030082600340d5803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 630750539 1250 630749289 630749299
    0xa09110703090e1e04081630080703091406040809090c07020109030305280801060201150e01090902130911090601020c0904060b0a05030304031505010e2802091806 72
    0x1002400c0c0c2001d00c516840b032071120f041c414041c1260b4132140c0744540040c0c021140120107011110314680d030141001d1b0424048c00c0c1003075052100344103407140019001750014440e003c2c0220b62100715000b0700c0303035030300481c8624000807900c08604192000c0c0c03810103203a00c59401003500348400c1c40246006061011412550717201d264a0b1544402d12034490240024003080500c007041004c00c2c046d40191441038000b9161410700480412411000592100070704045800c280041c88a2a424031946c0100c0c8607004204030701500388405540641d005104500c0201d440341c68040454030b80812542ca543d59650f024802141caa1600800000341c040401e4000c0d080d860000e51103600c0021001e031894130181c540080b6071a0758072541c00ad40303080e030700264000c21202d100141c941c078100001c000440c0102d5100001d45000e180078005d958060f400b0a5441c9009414458141080d04109950442d0600d2101500380c511071105d0180c000c1e102144e912500c000428143d22070501720080c030a10044807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 630751789 1250 630750539 630750557
    0x120405011406120a02011d0d0c08060702030702010e09062803030e0406060c02150412300f050310090504061e020a1b0501061a0a080105010512150a09110703 69
    0x205205403030011014030340310b590004c00c0300400740d4021744c904d61400000641e841d0b41d9600e00c01c0418082c502c5004112000511608200103801051012582004041c8091803901465400080c900032181e0581486008020b000c11020342e5242c10700e01c100c0c40c070740920040410120040d8603000da07071f41c4030039400314032180c1c0805000d2410703120341d1094031031584a00c04083c0f02a001e110005c2c040445003800c0d1001000007056403401c114207907a84600c188420b99081007007001078200560b1031000303036640f502c0100491480c07541040e146280c43d191494507079207a80c0d907000c41610143c410391008441d03914080070310041c0661074000044200860042c424910000c2c00d0000072445001c0c4200000b82c04400c2d00c42140c28000d01c0114824000c1e8000708103542c03202d0f0f014140c540f03440801c080141f000030701600001e820203d801d0042c032003401c0250030506038581a420400c0000c200f4941c0c5581c2140b480600e0751441100b0000d0502e241c01041000b0406010445940c014103058000c200000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 630753039 1250 630751789 630751801
    0x40615090503070f0b031308160c080c0303041806030f08090909070605160314040603152106051e280b100c0206071e030305060108070806090c1204050114 68
    0xd111401c8941454200310180d01e0800d604115406c040c0005d445510140700101c003047c2c107030000d0b00009a00425030480ca2456240c4031600891585c000b10341030304175000203030701903801005071801c403620b10401101c886c4100510100810503500001c04100c101101c41050045450280040207000d8940764207544a16440326661480c1d407180800052081006044032014002c501d0754013031003400c2c01c255901000d18900c4090700160805000a962520040d826184048111005114034082e004159048004000076100e068901070102615000440d00040203903070440100344c0d501c41072032114201800892000203211084100340690b049088041c00402c0c407400c0d1000710700600c00d40c03020b46299426604240000300980c1e1140c0c09112070700100d080b15101200036450030003684100000c42c64041c08645018003801d04102080781000555a00048011303008401200c41c240e082d5509407a022651291906400e94104180e0500042140c15001201c8151801d040312000d540c442c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 630754289 1250 630753039 630753043
    0x810060344030714121609080304090506030705060c0d1b080c0a02030c180415060b041d0c03070503132103020310080a0c090b0105091f0f030b03030d0b0f040615090503 74
    0x1a0083c01c0e1400c05c6100440d072082c0d119030040410003524140103440c250341342003150960b00158030400f101c585400030080a0b00d0103105000c080c08040392090f00b0401030301c100a41d200c1105043c8018402120360b1944400b040301d070b00b0701d403480d8030407445943d8090b4411001c0c0c0701e080d807079001c900034400e1181620007464090300e180351709110340c054818565150f032144003c4a84000e03c0604180d6100408200c61480780010070162101200b801894070003040320a07582d601c01080300b000058140184030302c9a0f0b00c0400c0f40c3d0007917022412800c1081007801c01c51003006054001038001c0504d01e00c032650040e01500a5480380049810110b070f8590356040c11900c03040c201c0c1006100c03145049061110103c107030f04c82460918103241031420a40c2d4180030072600c80710f11440d410248802d40310070401c40d80c018249c900c03240c0e070740c60203010309020040807039624021501d4000c0844c2d00c82c43d400340c407a21441905200000300070010701585565182c482d01c00325600c4101000121031032404103c41c100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 630755395 1106 630754289 630754297
    0x916050d0b06070501151d0105010e04021804052e0b030c0c150a062409060507020117041410140103121107030c0810060344030714 58
    0x71f003080740c5160038680e011072640409082c014051070342d11910007500400191000b60f1180b00d98030080104818010783c540d00f09250200f041140c2044040c2c08200b03640302140200c6003080d1400c941d4050940b8080c1100c80c1c4405c0000c0740c6050b400744020445c120340c072403d403079030105850030b21281800f00f035410002040d22001c1c00d002070381108800c000045c170f00c1c0b2407401103000b008001510020607031040b6003e00c00b001c0781e01070640e401020820b5403410034681024440c81e081c42d02c1400303074441c03003103120082c404c46103046c040b05228810204e002c003210082c144260702e036991740d9041d10038404000e0100701401c01440040e40d81000204051032007040c0740480c050410110501c0c0c680560000b02c1401d0400340c0400100d00d50300c881d120f400c0344103071401900d8800700100e07910002c090401c0002255541d61b202031501221409103000c0c101c0d60342c031140c0e0402400203500d42805 = true := by decide +kernel

theorem cover : BRFrame.Cov 630575539 630755395 := by
  have h0 := BRFrame.cov_init 630575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 630575539 ≤ n) (h2 : n < 630755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
