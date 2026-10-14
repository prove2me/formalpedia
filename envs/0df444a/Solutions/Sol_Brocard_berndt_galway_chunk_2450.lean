-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2450
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:49.880489+00:00
-- url     : https://prove2.me/submissions/f11c5057-74e5-40ce-8cc3-b62502192d4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 440467625 ≤ n < 440647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 440468875 1250 440467625 440467639
    0x160f03060f080f160608180a0f11031603120e04060314031306030626011e0c02010e0102130e04030908100c0305060d02010e01050a05090a030c080d020d020a11181302040b 75
    0x3514400610006c40a0030b4a4800c21014800312040c4000b084400d8240b64484110400c4002074108188000c8520f07480718044e000b2140b12400814180442000740c85c2c1c0010002020410800c007212401d600054494110755501c80103c00f14801c090241800a0402c0003940ea451142203104002d80d0183e00c00c20a150815009209000200101c40d5025030300288108010f4001301d900d0b40500381d00c006da4916240e001f6491507000c0d00d02c0d0440107403580c05400a001007100354510340c2c00c0740314481d01280d001c166044140402401070740d020f07400901924040c000181c651402c6800c0035038600b070094580d0783d10001c4a81080c0c00d4020103520840440381040e55413090340000e045202c00703280c3d00341080b50000c1c4060032030340114162030350035030082c000614254407490090100340322406052080d00c5440050f450507880019408034804256018211b807480c1aa10b900b005822407481a501140650041112072622245244600c030070400c00e1018040d140148400c0300d58199005000d680 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 440470125 1250 440468875 440468879
    0xe070503190c0f0b0d0f0f050a270c120c0510030516050307230c072322050c070b0906040b010e0912030a020403020a0b030106090806160f03060f080f16 67
    0xc1404d040e150000030400000c00c0480403208076200404d0066480e81140c0d00e00b006101c00717030800790b100108002c000c1d5130840c4c8a004090f02c080110860200007403642c0115041030040081c1c950600000c0c44c0300c0d100c02054140c4850010b51403015800007040000c2c0e4078000c01c901c9100004800555090600b0f0a62650401d40002800c0f17821083c102c00611041c590000b030442c810038101c1d80d190b05074505403660261a0440c0e0b48045100038001400d255420300484102d213445942c101e03e85041080341050030043c40760304005001d000b4100598007600340080030100300303228426032150070b8140c09412036242529008400110680140f4804001030701049042000010035941c201111515035860780d0f251070301c000191142d500000d40043c40d0341d40c0000e4070406000954103840b210348602401d130382c445400d16900c0404584089090908840440985010382030082d16030302145004a2039588444841c540f0701001c1e44201110f6000020821248030b040c004a072600a12243d207020b154 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 440471375 1250 440470125 440470139
    0x2030f040b0c180f1915080f25090306090803010806090f2d0708010b12010b0307030303020f09150306032a19080d0801030c06031e0e070503190c0f 65
    0x40600034145008802101c2a1075071651181c00c0d000d510002c0329403041d00300742c44282406d01852140d440402080c2c0100114607606441080030b0311400450140001d00c404004084060321a654070a80034481c202c18080081480c0c2d010b09200a4000c00005613254900071100c0d00c2c00000402c00c000c1904901d6022024040c0480c480c154420900032040b0351150759031400b84c0e0405806015207d0344134090001810110640001c0c41d08601118524884d032500d81c0054242da0703012809941c590407403a0300f400000e00950180c48008524038116003000d82c141c0111f544584042d117120a10b010200402015240401c40c41740f040283c001401c2e2010008480149800d0f10486103c0c070030b0718408003048400a0010b14000100b464204642402802071406031101c00c081c0820703241a07045000214900780070340180000b00e43c100c002d4491100c1026a440014914144088040e02a4020004982e40d041001820303603811007881c500500160314002d01e0314a4185e0158950101d0040c04015603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 440472625 1250 440471375 440471407
    0x10f03150903091814090601090b0316090c1407050604050c0103060807090515030a060608070b03071706041503060f2714071208092814060d02030f040b0c 68
    0x1c8084020b4413120301008031100014064134a400c80c0702c07908080c20000c0350080080c20b18103d62289100300010881314082c152500203040c442c1010319034055003049207982581c48643c2d056a241307000c1040d00b80c138846078500c9070702c00d040c103558a52021052001741b05040c0000d030234004090170200702d00d52030b002c0d0701d07a1a1000c6104d2001004d5503100080c00c900c500c580e8811003280300505030f580c0c003441441c000c0020841030094074500e00c01c8000210300491000120390240340039842d07041c40143c140c00070540d502401005180c010742c0780c041015031034003078031207a00285215403004581005801d2200e011200ea061540c0b90b0300340001030801200c00c40c142c00b015105d4210030004070704c02c90350451500e4403070580e00000c540b006d0600270805014030750b4090600b50b502100c0e85000340001c90348031140840004031043c0121650b401c00c0180c49070380c040c00003422402a00d494106a180d2140c0b0b800c9800c202c411122211a00e01000100603082008962011700200003d0070590b4000700c107211 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 440473875 1250 440472625 440472629
    0x2a1a0a0506010c0609020a0b121b07032c060a020f010f06062a080a0815030a030912140304060201091505040503090d14010e0f190209040b071205010f0315090309 71
    0x7071182d44185c0c00301591243e0100c04080c2c42140c00c941da03a45030300c4ca21080100700c215022440e00c02c46100c2c10b078092403480704540105425075502c420112100c03140203001d08982a0086805d414036070011500c2d1940c00151492403203540140100c07002040c40542954805000f41c1043e914104051003040d40000c40310400184108100781d906404400100c0c640d0724501c40a00032110110304590190340c0101003034400c1d81c0d29008141c0d080c0b01041031640d524184000140070941d903801c24171403541062848400503000d40d0b40c4146034a60307101c7d07450540e4020741282e40141d4464041e9000d0059455114150039840b0f0810001c2d454151100b0761a030180e00055031064140f1204241480740141043c0c035111003020082018145104600da902e02c0b0740b194014080c05201d901d00550b80c4024050501550060141c941139640c0350b48068400764020b203a075050010941210361480e131544140d5000e020900f24480140c0d045040c190800c5c4100a8030500160a001066000991103000e41003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 440475125 1250 440473875 440473883
    0x218030604020a031106040f03080324031005090312100609051806040903030608010e0105060a0503010917071a150114090d03030e0718050414010209102a1a0a0506010c 74
    0x205c1100b92500190403031146920084500c030003184040140201000254043c10201405446801d18041c04c810000102d5a0300c980c55000b50a804c0703494a0160070080c0c0c010007203400e80e4500042d000010704440000e0780c02c440c45111860041c05142d0b0000c034807001924003222444821150310042d4100b00171b00400312070155031a6040002054000d41203e40a0000c0038000e00c182c071450300c1218000d080c11140948140c1c1007204c001190b050601c61020407940090b1840c10121600e210807055030705c449411240050101c207825080d2690b20540c50085604001d603000b13241401c03000400100c0900405055540104080ca06c0c9aa40c40340c22020031358182000300c1c007481c04030051410000254000d07581103502c030b010060801c45550001e8412440b9902c06009180c04003201801c070b0141304901500007141000005055000340040c0585607c101b55505100c10881c483d05180c0189220440704c000e209840c8810342d03c03850043c1a44031204a200b00000e00e0040002004c3d89070905000e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 440476375 1250 440475125 440475143
    0x507061422030c03120f050f070206130504050106080a0506030d0e120709020c0c0411090a060c05070b0a0309230d050c031b0f0d0e01050909091903030218030604020a03 74
    0x1416541c092002000035034110f040b03003040540e2800d01039680405003139900e0010742914000f400c5180a40d003501e02c0d0600142c0b609060803c1d540c05e01c061a406248028100711b070000d0005000c0c1e6850040501170140e83c0e485588900b4012900c200f0794001500d9240300e174020200c0c11001551001901d0001744044440780702c03041c10f9109207400d207100b80d00481e0b1210300005501d00c0301e02c1c2c0021074000030102940c080141c603111030b00c000154040c0001e40741c0e0003902c02d071040000074407030040f1919190140c1c054503025940c03000c15078142d074403090540d13011036200c2103458140075601d01080c69047c40c42980e0312442c00d080c1c00c0f0548a100c803031202000c4c00004180381a402c0c40803c1640c1880d130700884541885010840240d82d5552142d13400d40c6548540038160075520f04c40c1c0f520361069a01a1070301d5081ca04a03000300800524020416100741c4600c540700708080f50800c0b50b01815078040e84006030b43d15141178400b4044205a44400d0007039108006010042e1100c0c0810000c43e50010380300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 440477625 1250 440476375 440476417
    0xc1b04020c0724031416050d051905060f030a0303050c1e0d0c02030c06040809041407080f06010e01120207030c0f0303054005030d02040308030405070614 68
    0x400074014014541814441c1410100c3d5003403200c3d4420b440c244010384080c1100f032651508800355442c410070092025501c00106803148003a100001c44a00e1904001c4c1c140854401d054085480481d0350f0442e1a0702d00d0b06401400703240c1d100b81a040182034422007006c880c100c0210b5074414249074000d040556032000a0345001d415010303100c070011a400c4d0050884601c0394800c100360094a4074001d0039107082607a20702580004125094035000358003030540da9807141c0304c13145150009241e581d00a40c039600340988506001c0f1200b8400d42140e119105107040049442c004020004e1100341071007110500184640e03088501405a15454100565039644c10b180403116006083c50042c00b1320620752100082540503040188a1111413a180038440e416000c0800c1c040c010706000c070300d0107400032021910781c84140b9a08810501070404c5a00c0d161400340c400b000c0307901551003554100d41c04001d000800c0001d2250000405161030035503845041621218400d1044c03100072010b900c0b400c0ca035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 440478875 1250 440477625 440477629
    0x3040308040c080706170604020a1b0204110307050c0f03090d0605060d020312071a01060917070b130f0506120112050712030305040302010c1718010b060d060602060c0c1b 75
    0x2d0098816041520701090381c0710f601034019840b42d102044c40060782c1000840c1418244299022001e0654500c0d01d400c1c00c84200c1084c032140306070140d8025407100008040c2c09250b400450140c241d035582c41303588491801c0349034141504010031880b40e4100b04003401c6503550300c5410b82c04185c1c0008000496484010001d41d00031981c0d2f5009425004850004504c05030200103444050301a00c08078240300a01942408000340c00d000301004503036400e10a11403040020b0390318011003480c80466244580b10407002c0c0741900302121070100c80b2500c450030300c080003160724001c00800c81901c5039401c003a00381e840c814804505008058a40c4013503000001800800c02c03408008000b04002100e0390400750030010090036088070240d0166080034880201541b0038440c0300140548400f0020558a89004150100c3d194401e2501c6940d00c1d1400c0bc621541d0700401002c40a081c000009003e0b40780040185c2003050041c020005800140b05044005034007050b00400034007801c1c0285164500100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 440480125 1250 440478875 440478893
    0x151203220302120d09140102030304110d0501060b03010f0e0c0a0c150c0512070f0c02010e03120309030d050603060118050c070818030105160909050402010e031605040605010f050304030804 83
    0x1c000b9601403003400b501c0d007501c100429400c001c4c004954904040c103480350404107002a600006500590003003000502003842401200c647d1a0018201040f440b010749419003515000c1d0002c0001d07140000042002031244004032000304050402e8030701624244030215a54020310100d40140203450090008108069540e1003004000c50070810000403074210083c607a80215500d91003544240010612050140341d0041c101c4500e03944030441c01c1c00d00d07801103070b050941c54400350b003510510041441543d0390030040c40c03246141c00f000310303140c0c02c6000c0510152203001c0d05850090b006680140031603600c10000071940048000003052035120b0060b410180d10948401801d015800300c5c41c0d4892400141d0240800c0108400901c60b41c1c07148058003001c00c00c0c260074880403a01c030302800c00000c040780e00003950040c0141401c0720100d0a060100c0e040c400aa260050703a44807000d02401107261a1003118040c03c428680b5000010711407001070032910020b0406000e0003148000282008039a20f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 440481375 1250 440480125 440480129
    0xa152703111212040906031203020f1b0304150e09130b07052a01090c09061d062701060212040e0103140f01180c0b03040503091315030b15120322 64
    0x30040e0313998542d01d403c80b0b00101800d000031200c082c0a10010b0741568072030300030340d4442900000b0031440c0c83c094000e001c040d408902480b1820b4042844001000702c01042d90004018054880c00075140c021800c029400c2d00007001c912820407006120000b00b900280316a50002c0982841c1d5030b0303a45040d0f000a911040c02c268541e5154202c0481c950050713064000b040c00c0c900c41c60070343c001039803500e0101007661700c00e0003190020880c280f01c60301c1d11040303050510740284026151400e92101410101041c4441c40303601901551004010014079a04104101c054100110010704003030030303c5100080c805040c400038051640d00c141c01c46803518244070b0800c110791104000c000e40a4041080f1503085298942039464803400c2d8400100095100c0c1200e00c1a94014082c520703040c0c0d410308001d4844403010203003500c1c6541308008041c0003040d885840182d805064000103d00d408000c514540043c404042c0c003a000208290b40311010000607038010740205a0b15441c607e2100c0c03082c182c2e41c0816 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 440482625 1250 440481375 440481403
    0x190c090317180616033b03010c140306060a03061a03160302090d030522090501060f230705030706051e0a0b0d120513030602030f0105030f060f060a1527031112 70
    0x40401c1c0100e1007191203001100700240d0017800f0007004160300b030f108040b0f0002b191031000740800000e81d9031301d0308000070704041070a410000349140c1c403440701c0c0804034401903080d0a08036000041c0914482c3d0700819101d10510362409500d000c00540205d802800070400040500001150551190141d5144240c101402100141c44160b640c04a9405040300b07114600108541544001240b4070032045603003500e0160b5480c1c03c004403601c40362440c55100800698036808103100704c10004070741c1d0160b10300550340055000f4100040c424052822040501058001450081c00c650b46880e41c10491840507080f0034215030300c1500d440f007502c4910030102c00c040c039600040c40100800541e540954010300d2040d1300034801e6a01c44052556503550100320040c142c1c44200024922070354900c2040c0d1047c4081e10b220030040c0d07a1105c4000c822000c003d00c501044010018220f03900e051310002c2030000114041083d80c0d455034696003000011a1191406560807d2a0b180800030030820101341000c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 440483875 1250 440482625 440482697
    0xa0605040f0506011206081f0e030a0e0406050105160f03090b0f04090501080a050a110105091f08151c0501090f0c06020601050405190c09031718061603 67
    0x3040d9030000107010803184580842d0007170900c030154101a20958041d502260300810a8014415014034590289058402d10756180e08000910707a000340080e05c01c1e116240c41c1d01030700c0c0b1001c10400003610055041f803410800c040c006019050750340c21040e00000e410000084118806050403110b031840354100e1304605100040406901244400410460ba0284070410040e41ca9110040d113501000b01c3c017074040d9001c5150400422203541906000300c0050600360310740b0145002080d05243e00d1504140141d500740c1c0303020102c68200c1109540041c4c1c840240c42034241140000311914120b945d488446000e0b2010142004000d40c4003d4080d2780190108a49107058a040b10040000340100001030081c07a000141c02d00703090080e01d004030300900115400340620800000208400c0c0d1420041082846000022864100e43e51802d02c040c88160366843d520524194040c3d81242ca08030300603841041707000640b040441100c86860b9141ca044548a0141c1c00c40550cd985000008200c000d9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 440485125 1250 440483875 440483891
    0xc030d05070510020c060408160c060302040e15012313080303101715090c1201050901060b0403170f070c060f030c030b0a03080a170910150812030a060504 68
    0x40c1060103407140500c01c4049030a0044103661a509078091413400e081c9582c0528003003800220300a01401c080300050724880310743c981d281c40c0d400b01c1030380d036a11040c04613900040a000b084426002d099202c400040002c0b960021040020014510004805115030740007100451060a4030102c0300e242081f5400d1894403034551940381c1d203d0348140c80010301d580c0748c2500096800c07070500f08142c1410012000d00303151640720303c86003000c0000414166031409040242112581c91024481d0362140082c00060689005c88100d42100c0142e0041c0d0031413a42484100002018000d8201d00300124103440c0b501e80300e0114010445004501c401041c04004d054041007160344408800c55003000e540d010b00181e4104401034085400040026420101c03903442030021800d440010418140c1c00e152400400440004034006100103072211017040d0002050014183c44d01c3c00703803a44800442180304412880c3c0358040c1e99400804203030020002010000900410319944490300a000162040c0801d01d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 440486375 1250 440485125 440485127
    0x13140402011b05070b0d0216080a020f1908090604031506090b0d08030a0b01180303050c160308310602060414030a0207090b04090b16110730021017010e070e040e0c030d 74
    0x74020950440051041c80c1e0460310010002371a0340c0390450102c015490482d03503440380c107425444000800d4020004200000004055480400c480789000b04002000340c200050a02500d1038810001c1c070408400d0003102c0415042001c41703070800c00300c02000070100d280c82c006030b840d40c0d15410400f80720110b5081c00400d15400900810782d07401078106031b403080d41c00404580f4a001d40d502014050010070700c800415000003d212410050700c81d040a0007c040078207440880c21081e8010800582003603049c84200714842449223401c3d01d1040165090140000740255500d50b60301c03d0140098940c030110b28a5242c1d0b62009140980000c90032005140c00c070314500890041c0d0103c44005181d141d85048230131000f00304201a560108810300c1c00903000d001c0304140d00c0000d0211102e00c4542e9808500603a1500c00d9031405401c241c40e1101a01009042038600d510140d12040e850340000d01080030090307000c2d00031f401100045600080182c50aa0640c0c07914610f0b000041d00342c420011519142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 440487625 1250 440486375 440486377
    0x15010503060f0d12091e0b031902040b13080c180709090615020c0d02011d042301050112020301050a1710060e100b0f031513140402011b05070b0d021608 67
    0xc400c41d0b884d1035508580c3d660206014001003034a54808015035401805a582c407c0001e5130084112034107260303841e4000d002c4d13104a80c0541d10204150704001620340228800d02e400e040100400c0340608a40e5004d640803450516140050722400311400340001c2c00180074450302000392409400401685880702d4034800d160301007804060242c4600841c03800949849920b03141000e034181e4410001740300c8842c1982100d003030b04020651003620f410b403006107901c80c41d82e11207091144207034500f410b5240900140140000c0d9040d00c401500400c0140502e444100101c4116812280180f03001806040c3c03a608021a02c044d00d800d903400d10600240303200781c02c08802d003d2140f6862511540e135032210010114070900d20440305046c0c0c00d000040c1c4001e500d6483c80c80390300025240112583d0308c000d0110450701040b01402c140e440c02da042c44150b5a00001c1d202a00c50b60748284441001030b525600e65074500e912a01e0141c56001959100150594042e00c1240c0ca56036034018205211340b03010041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 440488875 1250 440487625 440487653
    0x31202031b0d020a03030b0a170a1e0b0c030c0702061210080a030e0616050f240403050318030c0a050307201302090411030c0310060815010503060f0d 66
    0x51640180e07250700707460001080d03084034418190000c129800c0d140e038041e4082c10340c21141551091843c00006445180244500b201c0144100680745c6030089142c00b00300744040c103510400084248040400081c1c1c200d49483e084106a0b1070144c40343e0741c4408042480c418200700a402c0f81e00070a4a1034001240c5200034021926601408030f00c6888000c0d030b1396641c00421000d40003410742c11203c04107003407150003804407891800c52001f8070a84d0751602e51802500070600c50481d8081c0c2c1522200c2600401d282103a40c4822007403c01904040e1401070441c04094103509200d54042d03080e0140c2c130810003c44000c0d400a800340c55145045e401e1403526070b04001400d40714581c103407070581d11189035140c2e400a0200002c2c000100303440c00c8400c02d4020b401080b0302a401c56a41c1e203900502d91051000b6521a80d0041c0c22550f603803038011200041401e071580400140310701e643c14000d1705e01605020768403544003842c2064899946c41c0c0011140000c12035070f0380d00f04924021480a01c6515214500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 440490125 1250 440488875 440488897
    0x80a0c051e0f011d1504050703060509030c06010504020901050d0203061801090e0f01020c12030c04090f24080d030b0f040203040602130608011409070512180c0a0b0702060c0703120203 81
    0x401d400c1c8184c0340411034125038100b4003040c0c101c417017652003403d19080400e80050007442110807494490381d602d012100103449600c00c075480401d144140e50307010802c80e40076141c00e581c20b50600342d02d100040c00f030f030040354044e180c2c60740c01000080140e04e82e044100c00702c1c000402180219690744035544000c10a058800790b8501942101c80c1c080311050080340c07000c0c01c0800040c00c1403042802200d07110741024000c4130b0040700410000450400c03e0042070440b503000388000851081e800030361400420b04804440902c0301f0b5800030080014013082074071042c500c40c203011482c43e4801c00010904152510034582c02880482408180038465020348550003406160138511030300c90000382c80380705091281c50014007984c880040b06040048090f03030040a0340c1001404d207001c00e90780a00b2000b00300c540507007440f142500303560312150801101c0d0400c1d000b501c990301c00e5800c0038a19240c81c03192400180c01480d0021310301c0155082040007100a641002c3d041c941c0303591100000f0745a074007101e40e200c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 440491375 1250 440490125 440490131
    0x3030e033a0207020a15020f07030501050610030504110603060a050303040f09060506030919030e120c011805031903021218040b2b170d06080f0102030103080a0c051e0f01 75
    0x40ca0301c0c00038802c40795199002400c3c02c41d0300d450180c44110900400b50641c085001d1348003410308500c81000420702451191001055900c1c046041c0a440700401107c681014180000d110118640c0c5000c0380d500042900e210395283d0396400822244009948640d070184800100000d148004001000030341d0061101445629074603c20000140002ea460201c560081c448000042000042050142c2d02c43c0c00c2000340860303644e00161925a07500d514000380e4100e442200c40541c4c1c8821140c00144200c010844420f05120110740c0d02c41c04200c02c210160403079550328050600070804000c03441020f550003641d80141483d000c480040040c0c07500e0056041000241041c60102a0f21030207982444210a503400c5000303100c401602844404d41d810004a01f10940d00600c07440101050f511000010480c9450105000d192800184031010540d02c10b000510000c1e444c401103803141c2d40c00740b03420010401281415030628455000c035001c202c58880422050b0794000c60119840c40405c0300030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 440492625 1250 440491375 440491477
    0xc020c060c011e110406080406150603020c01241a041e031505130206090d08160b100f051201020f031510021b0409230303010f1502030703030e03 64
    0x10340c05030b44c2a0540200f0311380381803000f030001500c500b10701a445801150f001c0303042c00c03801e14492480c0f80c243d08580002900010030880b0341d10240901d102d0a000450f40812084505040c1e0400e10704500a66041a007209800c02c40030b80343c902524090304514807044140724400304403c65501c808c1c8012581d07108002a00d1600c40070714800c0512540040700c0654080400758200181030780220b00c195404800e81d0031400204801401038402079800032000e003008032640c00c0c00c41906500400401407503020a0050010440c81c4a071308084032030551362681e01a91460072540079000c0d65003420f0000b43e01100f00100141100d5070030b2642807041c0c50414013400940d004030389905103881080702c060043da00c80303405401c160341301c1d40c4001e0080b011000340d06181175107540c1ca030310440c0c2c5004e00b42e803010006001c1c948800150030010000f8001c11b813040207003884007945038020118003400741641d0392120015400c2c203104403030078124260400c2d626480c14011141901808401e00014000b04140c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 440493875 1250 440492625 440492681
    0x1606020f0f030a0e0d2108100902040f14030f010e07030b010b09010c12030b03060a0b04060e0f0a180812070e151603020c060d0207050c011b02040c020c060c01 70
    0x710b52a034040d6644142007030400c0400d0040c10610305d141155000b014105441c0520040300361011565560703685c00321039040914840d1881d00a503080320110740e104000410941c808a01c00d035007125006030f0401140f40680700020b050940020100e0160350030314850440e05840070031030406880c46000c4e80002c59898030340f0103809010740004203005c01c5005501001241c1ca415981c5641d0441f45070219029000502181c01c3c92800d40d681c4403615110203048110345418015400600a0300600455034640000c001c800c4501c05004451440da6440c9812518001001182040703034001c01441c0d42c0d003920781d10040311228200c4004001411000300f070102440c0804c1b00d845002c5908559034101906060000748101c0c1c200411400e611817036080d142203844d61005003a0207020407a006855500398140340c0d091056078109241000b40c00d0200c00181444020b0342c0b217041e03806032000900d207034601c50242e141680603940241d000710042146402400150000644680d055500a10b0724008100b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 440495125 1250 440493875 440493877
    0x10203010509102108040803040b030a0c0302070305040314120a051810050706150e0108031801050a08130c05031626150a20070b130b0114031606020f0f03 68
    0xd50307407220803885140045001e01060082480780940c10b880d186c56a84e2034041d140d54030a51111041c3c0303401004200c603042d114410300343c240e00c243c282940341c1840703554003c00a100c2d50000505070540318100c040340b00010083c40c007842c07204403d42561640345100141c201c1e08818003003429a000c0000034080c3d8146802001903500254a44509184080d41c410b0094004004a08042d4440c204000303050101260b056008161031005907588050640d0a400600d4072085c1031410700108001d441c801c9540110082c0d40310070000c20044d1610303d03900c0c004c0603020b012350040d0b80c90f1094003960b81c040380c0c22070409000c5412144180040c502c1d01401100f21500300750b805080c40d00011510088146a440401c0d882000d410001030f107030304948241352800c010441c100402641c04160001086440c114954219120060380b902c90780260ba5409400d100c14045d601004030000118061a00c04200c40c24859500c10080b0070000d8962000a61b50140070741c2100161066260100c0b4001d0080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 440496375 1250 440495125 440495129
    0x903030b1c02100e13061413050c0409020703050c1e010c02061509090a150504060c1817010b09090604020918060a0c0504120311101109040906020f04060201020301050910 75
    0x1030114503100104000644013540301240050b0003c0c208521600001668429600645200241c071125902d40c8401c0c03004c4400030324810107400b0314080030310192081510550b401c40d0004440942d0740c2e82540b40c00c0f100c9d40244002030300203104010066103a4410340da10801c00d502c4140017045020711301c0008070b070380d1082641d030103002c04158000082ca900701070030042d501a88500c00c441a40c0340565403034105801c0518501d8000395124107000400c40d45e8050440c1401c00ca01d000c4100340203071380141c003404449221f0090400280031101070009400c0d0400d04030140020180c007000e18080201075113411048508030302c110000800101c58244800904017505401c030001c041543e24507881e40c0c01231107401c840400340f10051000103502040c40c0c1c00000c0d0b030351095580480013001c0e400e041c1d12300b550a28110903028200f24400041160756401d032116080122804a080074481c105000203100e02001803c901e007001a02080d216015002181258400e0700d01a005540360b1046240c414428 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 440497625 1250 440496375 440496379
    0x1f030305030103140109080c0d0807080c03070f030b0d030215090102120a05070504031202010c140c101805070e0f0a110307030b042a09050a030309060804050304090903030b1c02 78
    0x1e100500201d410400b8405016625000000303c02e031464903182038075009000c1c3e143e800e42c09040c4107801203030b004078401c0d0440c810b41407460260500903500d81060100a06503000c00001c0c488010807644241c1102884850140c2111134209150030001d483c2c160424581c00104204000305d011120148215010511403104450b50394076030f130200314050000030380424104a8107020200201c0c01c1d001c4000c0715003400d5000040c1e0740e9007846001d0321501006003459210f15041c054003150750302c0070510f408103a00356400000c0c0c0303920402c04401d20f46001500503001d44202c1d0004248981440d04e8140140c10340300744800159100c1d080380c0142c07844c06000742609441800403e25550003600100d07500c520082c008106400e2003107178901809041010700074100f0182042401c4031b0307040028a000f91000f41d40116140342980c901078031441c0e25110305d60401244400182c24008184247c40140025801c240545e400506008016181c8582924030403044020800702c4803c089800c0c00b009940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 440498875 1250 440497625 440497627
    0x10e01060c08040b032d060105030601030c1103070305031b030402030c0112090204090506070f0206100e13050102030f0612031201091a0904050f0d050301030314030a06080102121f030305 82
    0x80400444100a048400b2502c103101404040b0361880e455016620507150b400c00e100c40c00c00341c88540d001c41d003201860042000c0385101400010303648141101d178441800c0c00c6c00300e080c052241003142d5900303016808031102d000100d00d1034205903024000314001e40c140001142c8008613000c1400c510301c4113a40082d41075214410981081d40140802043c0001412000681c0d1400e500490259102c0d96011a41d40d00715100b000422a005003a80f40d0b00c42940c402845649040f10f004000034500340207880010030088001000c0c500e90040600f810756101c2d000355104d0401e0040c5c400090810344000c0d04c0ba010340101a544400c0004c2940c808454914000c15164648a1080001d02030751480d809070003003420091105444247c2805e008510500c0141707101c0118980c42810001d0407c5a4803c01508100403c04641d000c403404980b400e254180c0d643d40d40742e0207141c500901c01071b404079005500100d04400c0207141111f00502c65512440c0602c0501006410002c600741c07240001004244 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 440500125 1250 440498875 440498879
    0x609020103050609071e0311070302071a090a0311030f1903170f07030b0a0801020a0908060c1204111309050a150608030f0f071b0906140a0e060a0f06090e010e010e01 73
    0x280191426a4000c06e50400040c0004c90366002d007881e0344540c83c184c0c0564030526003084117407506192240c03584400d000280c20024a400000c903035038000c4c07001905405410006030741e41c0da0f05001d40383c0f6429908044940c40b15869804021a81083c80d00341c0215180f00d1000c0c0f001c03654070003014801e4030786a14402c21607480030030580090001380d08180d006803031018040b0b41e00900344001c0c00344000c56110b07010f0f09407031b00d9070042c60884024609841c4001c18000e0361000c000c1d02d0f000c6500281e1003801c00461503400c5010542201c1390002c42150181052420424024007040410150740108002002e02d40d42da4064800d4806030b114000040d07104106d585180c13903810000c0c20205036840c071203910307040494031102e0300817100303101d440a102e14100003002000c0b050f116080c001c0005041c01c2105152a03000144102086c5c0b141c0100b504600c000074032a0f590740c1c80560042d212209400b002c803911007034000c1c00c0348501d01980034148100d000114200145152890484403901a000041d038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 440501375 1250 440500125 440500157
    0x170f06090a1d2e0b01020a080f07020612041a22050c090a02090109140609040c03020915090f04060f060e030703082701050304020a23040504060902010305060907 71
    0x20040441030081e100c1ca0a84461401c032040c00400c1800031001400c540c540b401070b0406100c210050841d0840741c0c03070304d8403408013641c0100340d451000c0e820a21440e02da5605504000507481107000007948118005210410709055401c40c90140d801203244e000300c1c00490b10801130644040d90a0032685441c4403089040d2080400044a000d101c0c2e03040d6030385407080c0408681c00c0c090070741d41203d41580110380810702d0b5902c80d03001c1c401045040354401312601d69501180982c460386042c00d001c2c9032034100c3c0c1200396000390100c03400c510025182031084800751404050301c0d009014240d10031015580c07003c1851605008000959000e00d8072414014079101c01501c494042c50000c0d03402d801413400000101d1034180191005045a1101401c3c2d40b0120002103951420040c010b0f0500205109010240c4c4490071880c0030342c0c030701c010006480724003000d0000240b440c80c005554454180000c000410a072031f0885017416200ba2400d0106071214000c07c00440c000300c0b00790300040d800c100360008803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 440502625 1250 440501375 440501381
    0xc01140a0201020408060a0507020f06131722080105100806060907020a0b280204082a040c050d0e0309150d0605180412080601091205120a170f06090a 66
    0xd50940001841c10340d80f82c0c811810004111503250320300d03a60b030042140042d01444002009840386c0003070889440c28800d03000c048182410054005c20f010580318901d0f2900078100c0b89400c4030960080001141c00401c03620180d000d0048510341d50030a4041764032880ba1400781170035607811401409a42e66030100f800040240108980118401d008082e000710301041b02e1376014400c40200158540803d08248030903076000c1c1e011110b00d501c100400c210410004c603175202011214001c1445e01c42741c0300044c139444044003181c141d100d0714000d8203c1c102038002004088480340d02c201800344030398128286403a40100cac2c0540340c01407044070903290744c2c5101100511a0342d0007400009403494949020600c20840141459050000b20041c003051107441e040d0111040c2c058034090f1554504a030000381040120b200e200703550400ca007400b404100c001d00c0000e00048100301161f4072981040310080c036030f2054429403111903540328041200500f842601c1c900c51070018010074a1621214103038402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 440503875 1250 440502625 440502637
    0x6150501051c050a020d020f03010305011a1c0203150a060e0112121b06090c031103010504030e21030d020901110105040c031103150703054812160306080c0114 70
    0xc02c1d17500700000562135a0910103050000030000c000c545030360442c41c2c0740c3e085a000e150f60b0701c40c01c5200380a509850b82c450f01c01da24040c0d45001400046041e030300c042483c00d824483c0f0441d050070600c0c204180100b071076001d6021155400840309044e42c0e1440b0002444400c0800a011628402c0390031607000d0080b0458014031961226480c64000141c0301c030030495402407c1182e1400040307208001b44981d2100001504604400030042030500e983c000c0c0c03107000806002c50042007040d01290103120343c2130313075112458400c00c1070702c4d9112042c2441c04001d5024030280740c0030560036501c3c2d90007a041403252622503580010754186d81d50650302d800e05001140d9200030341c18440d0b03007034040311420394a84407802071144c2d840101d40c1d42002c2c03211400d684640f210a0500d5040c801700001c141e140800c0c9001545d98a4100003030b64102407003000380030320130f2184280801c50680c0a00c20f0f2288241c03200e03c0d5040d280d55080021603280c1030080d4607500f084600300d000900c10340702c0401410030300c2c0c01480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 440505125 1250 440503875 440503891
    0x10b030a150b04031a0a050f07030b01050c0105012411101a040c020607030e010e07150203090316031208090307140c030106030f11030303010e0f1f0306150501051c05 73
    0x41165a202c0564120364016042110401c01003111482c0180710100b5030340d005070342010103101b541b03000402900b024030001c264104050329030030000003d90091049032903040c0c10100911103981c4a00540c04404140c140399a075280305c00307030207144091044149175844c500386409856042e04914181000e000c15014403181031820300003034207686d9100d10410445003c903802400581c40c14200103002c64880801401069040401b400510a00450380c901610007621102c030039004250300880c41c0d409401c542d1501486521100380c00e80c01400c12240450f0700c00e240042207a84c00f0201101c1440e0f065904001c02d074002c0c041a4001f60310703101c1d88064110324600700c030400741701803000a00355a8540d00a4610800b80120841403000c502e0182c100c5070b10542c021880c1d07524090200328644402449a940c181c00c50780801d5088086560031030300c04610011014000f600c03403d03d500108030030070450700000c1014200081c00d5015074140c0e42000800c034a84c40382c0c0991159503078003902d030081c10342c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 440506375 1250 440505125 440505161
    0xa0c02150304050f0d020f030a26010b180a1508090f0d050c01141b03040c05041b0807020d050307050d060e01060203120703090f023123010b030a 64
    0x52a252041024520a40c0910300500342800d154130500c0c10b040424018400310741180803402011640042241e00e507416a00e456015510000c10400071404484030030b03501c80b44410b0000580c0c9480348064124007aa440349001141030b11401c2010040a07441f540c1c3c101d00000750200103082c000c3e032100354800e0f01c05082c0d802d443c611012440c01c1140700a901004140c001ca06101c000300b0911800d138880c0180ba0a24030141004207211050040e158a05600001c00000003820419210101e400518010b0003e02003541c0e0303040c900d10500b800411500000380c070400090070346880042c00c2e1984404603260503103951035001040700c0c994031244035a517415488030400652240e14001003402404254084d584403601c080040b011070801400301c2080604000005c804030f524040310740c0010384d04a503071a1809e4400b502240400c80c1000c049645162001030380d009a10003a00855500c3c450006000d004032914000051040401c1c05500101e40c4103200186a44019601c44c10603819008681 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 440507625 1250 440506375 440506399
    0x6091d0705031312090f0e0903030f07120203011d090c0109030206030c04050d050606010201110414040b13020307090315140c030718120b060a03030f0e0f13051806040302030a0c02 79
    0x4141d04034001c42d00d44c0008081600800031407a2554424028290420124000e810001200f640c0c9000281081c90b000c14210702065406000b402c4040305800e40307010540d120745e943d564002d40303103c0c1d4850322550f02c4005400240e10200c01b01300c204001e0416110005014290740034400940c00041255410010402c0701180d81c0d500d1000c070402c841d101304000c0c1203902d043c0000a0070349414070b1349021445010303c41404080010440e54080c00010b981c00079481e038000300091a42903a500084240c07910000602800d950301c100e500007900e0054840d10751003150002c5c0310b0200c949810064180490715404500c54007111802187c011240c0d20b410440ea03070219500b080740900d41e600c14110003d1100a0204110365154181e41c06501166210a101c1ca55140900344034580003101c400c2212101e040501592560311242810002401000103030042d0b04520307009040543e201200714800180134610480e0000d00d140c030a540c143d0140d410300d440c8001c103440160b00400c3c102d17444071041c03601c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 440508875 1250 440507625 440507633
    0x30501050d0203190602091c02030114071b0807060606080603010c020d0c0228080a060b010206151908010c0306030308090a0f0f050a05030d050403030506180c0c0705100906091d07050313 82
    0x10b231040001c00e05050051703103081c41014215820624045020140041080322442e00801900b5007000c003240a045500c03072610b41050a03105405000380f02524140f008200c040e030000f82c541c030444e01540208580741035208240c2e40c450402d0b0b0cc0ca0000b402036007009005081040c44040102d1110301d99249609907420614090304282c0c004001d65807100128005020031402803102000c1e02f03001810280c00c010101c110002070301030035a8010040e0200d90170311480101c840500604c00d0710001c00040b078900c0d1004019000910040c0c0c0012640306c04242c00d000701149a012036903014880f990610000d41c0c442c46510540501505e45000311280344020038002d0000301343c500c6082100180a1a0074600038084810103844c50340070301c034000040c01d150484e11028540011110080070784480c46903400398075140460b00850303003007021174910101864202d10b840301030b5280354541e241500d4803146da880e140c1d600300006042800b00040407440031030081c001180c00845c0f145612420070101d4071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 440510125 1250 440508875 440508889
    0x9080c01031107021206191b080c090a0e06010f02010204050a030227070e09010e07080402040e0106211e03051804090807050d26011707050a15030501050d020319060209 74
    0x2405c03e540c10031b02c10099071911184440540f134a043c207080250006e1241064040001554018207104005000c159281e04003820784202490080440103026101d4200c2520703d417040e0380050104004810741112503006000b51010384101034a6110810b19540801c000c1e801c540d00500344890039081410380a00340c00c2e402ca4412602500c4800303020441000707020340540e050740030300420710400d018800da0355448008641c0140d0105d82c04101ca4040291590040015a00c50f1020701c0e5440c204c0185910304008001d81c0902a04100c0d0541c5d4002d03090117020a2900c0d0000e0000c2c00c10002940d182442c011402e40855010b070000940d031718180e03201209544072030800c1d2050b92240c41c02050580d40300a44400005100c213510b100c541403410054001007040c0200d605102c09021003001040042102e14020314000340041030559a03041d80c01d074420b0400d940c210009007001c1c008141400c2040e40c0700c9111398042d000305908000c580c41002d142c02e500508079a4103408000c42c00c40b0742d803861 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 440511375 1250 440510125 440510149
    0x4060203040807140303071403130303020c1813170909010b1b12040905060f0d0f061103130303023604060914040f060e01181209080c0103110702 64
    0xa0015a522410030b50780b20301e44040b6078007504052612144a1030703152404029900c2d52580003c0b006c038a0f51b00c5141c081d003140114003409604030321051002090550000303c05160405c00e03a580c0052071480040c0006202c0d0444022035020300405080700007e0002030403040a040120f449418202000c0010b0f5944100307074845107030380ea80452810010001110840306080359923004180c48c1c400254400c0039400381340b213601280c65842c400a201625043c402c0680010010b10501880c01d092911002078804080140d41c840c0c9460020002c90a0181c00c9030b00460910101204250a50307a0440295021109000c401102ca00301c00105090328070607482c001107001100e10349103201d0302c00d11086400b903038450303c00203080c100c660404804840a654200c1d8011105102c0c00c80e042c28604040d08d800000c103a81c6600c0d02c009011201c2d040c8200d014030521071440780c898000c000c1781c102c91505c45030049030440e4100301d10420466000b603010b88040e981c600842400d094070798000034244c0c2090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 440512625 1250 440511375 440511377
    0xc0901231207032102060708090c0d02061306081006030e121b070609081525020307240b0603150f0a030b0c0c1c080624070c050301050c040e1b07080406 67
    0xd0715813003020036014003600c0d40c410103e151294151800d035030416600e03200400010301462135010380c042907441304ac00b03c0f180e0030202003450300800eaa500005200c4402140c542d00005842c000101e0600d00c82d0007264215010100246400c082580202d4040d500c0985a1140301643d08010344d24481c1c103001800040100380c540314201803801c5040e50502c9200385000f61040907580801924401039030500885640e80b04040d080e050028209030700c1c5101c0c150b005444103126031f600200c10050491041c00c0e00c08038240500404803000e0920809000581d0108160080b607414043d25052601400d0342e0303010000d100302003955a07929811207c41098400303540d40940000c1000408100300448146c25103200803003426060004401008079001501c0b041c490119500000d041094401c8107190714075441c0f03103940c1c5c0c0394401c4c5400c00254845201e003500075424140040c41016030401a0f600300c44031851400200d60b200d1a80f0307007400c01c0c0001d5511038404d042c49a4404140703220082d0000d0405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 440513875 1250 440512625 440512673
    0xa0e06040b09040b0f0d0f050f0d050712050c060406061a030c120613020a05040509070207241806031e060503120d1103090a0b0a090c0905060109170c090123120703 72
    0x1760b0b08209040801c070450004c510785c8801d40ca1800728bd131000840303a41c950000154041809250f800715554803ca500030b01c190701c0703441c0070700003441400d90041e002c40781da405250b80d0311403064200c84402d01007295044030511080c094080218010000d0b0317075012a00402c40514810148015000c90308480803040010700e000c2802d01c40d60900304402c41d04400c1d070b030005045147c40c204280c1c0700204c807101c8503455008100c11002d440e902490041c030800d004424210281d9486000040042108500b0410301c3c03605202611540d0782144240410303508060090015126038404600196011010a09900f03a5a401c05c40340081e40c040998011440c10b00034000307010050030032614409001d000c0b8150b007072a0428030705c00140e42c0444401241c2c8990008240c5659000058502e94502d901c240082013259041000b0018081210000020110364144a90740c90324402c04014201e044402104202440132500034a003001100704c58060003002c03100102d03246e90b6258401802180d840030000b00f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 440515125 1250 440513875 440513903
    0x708010f0b04120c38121305120f0c0d141e120a050403021b0a300303020c0d020a020d030302031b0c06010509070c02030a021c170a0e06040b09040b0f0d 67
    0x1a0040c14190700c90b03820800a410701140000386d821010020b010492800403800070181002020300c10000d42c00380906c940c60700c0361408442c0a500b540048401e009070700039400c000b013003107020700c00380542e44000052035030a00310030030748000342c3c580740008545042506104052686241e481c80701e116025038080880c640c2090326010745041c918104c1c101c44150606401859600e50116220807601581460165102c03a031440100950003070940b42c0300ca496174403003001415015001081c0d10700c501400c07a81e1440e400303601240c80f945c207620025440041d200424004ca446038010350f41041c00c1e92903042d00000d0b10780b1050829800401050384541240004111a01d0b003401007039400182130900d81c8482000d0303800a522070904002c003d1080c00600c4044e071a064010f9003010b4059400b00358140440c1c030640020380543c21000910b40082d10b07140d51a202414808181d600311003098190b14200f1014500b0400034017911440303581c0007000740058110740c0e50b602480c441080d001e11106080d8031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 440516375 1250 440515125 440515199
    0x501230c070e100f1a070206130b07050f0f071206020d0b030304081006060e10080403120e07030c05010215070f0210050f07031401080d0c060e01140708010f0b04120c 73
    0x7407640c2c8905521000e2a9800303120f20501021145045c3e03048450075612030000382c6002700016a504507070206603000c50302c1d02c00c0103070000d400c00708064000201c0d0400000200899a1003805004040c811400c008a90002072001c0d005444614481c884c0890300d9890f910101c1c0ca90340103980480707840e0748041c00c1174500700f80c1342c400d0002400b9036103042d24400c010a00840c0192512070a064108000c01c03002406252013107058094425001c13105102c0203e410300425603c0034140000d680390254048002050740c000030700d403925803032042c01810710365480300b10075951555810303521025401040560b00c0341403030510806200c1c8544984581d0b447c00c01920090483d0b039180c860080b04024040144040710700040d20410344d103e145420544044640f601c9009000c0094650304190f0078101074540101058100c00c1c4110300315590030031643e81c4e5429034104090682f28007910320b4030401c42400f0a100750401480003600a2480300701c403582c0d506154101280701400211300c0d0780c043d22110780b61 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 440517625 1250 440516375 440516399
    0xe030f0604050d12060b0f0d0f0608010e010501090c0c0b0705070c0f14010f140d240806070903020907140c07140f01030b03030a0302072301020d060501230c070e10 72
    0x948403c0d10200301c4603046c400c0700f4915200c0c40500350098580032461100c1c001c40b54010030b07201c1c000c0c80d00600c00c0a0395911103d000e030400b440b4018240d400c0c58001306507500b191107100c60013070682ea100743c0b900301c441d100c80d101c00d60050100d1040190801011000c201280e04c100002c00c0010500c40b42c1d01d1620f8540e10003001540116070400400114820b10f00d540660b0030b03401c9107424640d880e0348402440c030840051482803a01c1d604614403502c8005007440e0001d03000d0407140108103441c2c02e950740b51001c44081c10107010095005100c02c0100e080184640c100180319140040342525040da2110080d01d4040c0561001e00c44101910000110341009002042044000e01701803000600b04800aa00ca001d0004034038105540864010107110100c0744010b0035400c441c6030600c1c0001100940c40c00b030341c0082c80400d0120f01308000000c9a5114201c00052032440c0c6410210302d026a4029000940c0103040c40d07115031246130004070303d9446410350607010b0b143c0da20014100c40e180c00d01603000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 440518875 1250 440517625 440517647
    0x250317070302100e0f1608011404151a030f010606020f120f070c0e040309030b0c1c1a0301140103020918030d090503120c0c01060509160e030f0604050d 67
    0x42804140550000a500010700e00103800c0d403900081002c1c950440213601c0c25285081c184064492102c159008800300440107083c1d07102c0707000078000e0100c100f009456545041e11300070a02d03d0100700c10b07082410254850403043e2110540e074442041c6a00002e071500e2020140d200207030b556154108015901003008964481401019003400208188841524001c91012201d03161300050080c040020310100715000d05600340c0303504070a0419060051441096000c11105594440c0100c0d5445107140e096444004100b507010b02e03480c030415690000307012443c041d0100d00d184031170b45d03d01c80d9a084c0a49200101a000c0c0748a59615500400041510240024182d00401409500d0103000441150003460350200081840f01131894280d10318416006000e050b018030405005010703003003130020701180f1440d00007445103e44500030007900800655000300a080b01d00900c10041c0d01a2440340806507000b0186e40160003445d00c15401e0480440b0111420341268000480003034100390f070420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 440520125 1250 440518875 440518913
    0x50c030105220609050a060606020706090f050904020d021504150e040506010c0807030908060a02030a0b0103060e1305100207032601030f08031f08010213120b0402122503 75
    0x1060b48600188150544240c00001d0802a01c1d001c1a0b01405802c01600c106070350321001c10400c07165280d078020345507020750007808005110803800240f4541160106000d507600100b000595131140d07401c0001d25005050b041340c2107503440e24110050a42c5070080c0004003418054481501003c4100405003101840c40d41d00c140c1c038003024804d16907489440122450707448100c2aa4488aa050503200c2c035080c1e900401141c071410301003100c440d000d50003450160451300d006010803001c0c40010340a48455010b444600c1c5035840025204018030080c20007128000c0c001d850200803000d0012041e40e0140d04141c000c181c41c41c070400381c100035041c07440290b602d0020340b80500b541581e440940c28040d40402030b180420110100c1d55003d440090b20401e03140004170100e10541c1c0c1e070721040c042e4010805400003081215400505c84407840c00800c90154007079502d0440d561280c0c20007000c10289000a0102d1144120621302c10075101c01c00e10a860000c0d100f825140c1c44c52804001e03980f13111800c42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 440521375 1250 440520125 440520151
    0xf07050a030506130201020f0708011a030d0f12020f0f0304031112040501030510050909060108011508063d0305010f02070f0311160303030914010e2a0904050c030105 73
    0x1254000c03e1840d0000503d4a41d04c038801d5541c00100d01e060088002c0040c0b60042c2e0300e0006408130158840c4500c021020061020000c0034010140c60300702c1c41c640d4002050b01142c480151910840d0030940b52080c4d00401410810200e1124013950440d4401612414001003440103041c1c002d42e0000c3d203001d8050041c001d080c040c01c10b9044500840c403d80d418035840e5008101c0382c1880100322006411301074000001071903e1422503980344002c1c46684655482c2c0020000c840c0c0310b0b0350340751080e40d207014014411920f038484c140c08400100381c08181c605007410111504081030092022040c80c3c90f00c2c1c0e0100b490304601f0903608440701e4070242c1c80704910410080d000103648374104660141c05007480c48550359030740c00440c00c00072080f0040c3c2d20403400c183e0100c101070b01030348183e100300d000e4034000c000803050781c000608868402e5400722040d8090512248052003640cca260b540741e401c0c1c0d51025002d20000868882034080d00c040f105500071280410407402d0900c28244e100c01112034034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 440522625 1250 440521375 440521379
    0x108070602071503060b0a0c110102030c0a0b0a02040812190305010f0509100824100b032409071d090c0301050f0103060513020408070602030a2c0a0303020f07050a 72
    0x42d58075820b920688011140c803403100c041d218025800800240104c9540075510400028000d000c00100401110000390140c0400c845501c0041a00e441800800060151180030f85030114506002000c0c284180e40030000480d6020052065800d9106580380603501e841040b030f4140c00c0f1b842c3c0103413042c0400d807a103401040410041a0080116441510704038510b40752049440d1107000a50040c2001d807044c4140d00d8159407039901c805002c02c424025098490f1110402c180c081100ba11819100800600118040c0401d200c040040c00f910ba08058882da0544000714000c1d000441e80c10010805101501100d050358028011445008031018034092505030391002c0c041c001030103141d00401c00c0d0003161155900035801000905401080001241c80c0000f800c0013a52240c040d02c0d40070701901c0702c00941280000281c405c1951643c40702c0103144001100d1104010703e2000d2585020304070546101c90b0340b00e0b01c0c92a00514001d40c054910400f2045400f464030340560b20041c040c0b80d4240c82 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 440523875 1250 440522625 440522627
    0x60303091e05060c0f01050f0a0609020c0a02010f020708010905060105090109020a08071b0c03080306030d081b130b07050d0329040903030212010e04020a06030905030d050612070b1201080706 84
    0x1211054440845800752265003500c0a18176104840a003034800d50328000502c02c01c3c44600d103590b8030a103c051418441c03a038a58034541c05a0140c5179001b00d1030b80c0300701d141000640c06104005202c2c3d48a2048940d12580c801c88a03003034070340340e05042d01c01c2d401107801800203007001a042c50144c815403a0551a080c2c810f4002007850030300400c40d200308080c0f6050f40346d141c20781031031510103590004d200d16911500d0f4100010107a10642e2414031921078600d1580c0030f40e0040e02c00d24480c80c0b2000101f458a9060904000075070b2080b00c4030000aa110100070480d80090703c0039040143c0214010113103805408005030441310010041d03201d01003240c615016004050004640342103041c0e50100b07203019149001d601070b00880401500740381095001182603c41410344034031a0380201c40b501e42e10343d680c02042d030847c0e19094028203141c204100c1095030300704640040e5080500504081e160001d0070800504140a50b0001d0640c888000341c042005625000e00602401c100c001400e1200c0c50414 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 440525125 1250 440523875 440523929
    0xf060403060212061c02090a060b0c03090a0f030c03080903010207150203040b01090b1c110409051c2a14011d010b03190308150a0f03020120030901030b030f0109030306030309 77
    0x305c002e10461000c8001a0140c0c070907007110b401032000c0c103412622100c05c0812180c0701d4101482042c068041d540c80015415030800030b91045030b4000d0702c0040d003d4210344504649030b00c450170041d010740d001c01060000654090b03845205011603480181c40e030405161541c2c540c041030703000c00f0680b0309200b46074000c0c1e40c81d460b00d40300d94420010300b6104010140b40c014040741c100d402c0b103035000c0d2811004200b84400800c8241049000e012602034000707000401f60b889a450040e02d602c01544c1610240758400b043c6e111300285801014a601c0300c005460b001030950300b05441025403116041c2d500e03000c2080c00d00400854070012800b0b801c07e40c2c21900c20308148480700c00043c04000a40000c60f61140000b01d0300304022101a01d003941954a6a5810070103140b94071049002030660303207180d140c0c40310401303210000c4011000510711741a90031b00118003810201c3d0203540c1c10f00800e04140401c0c0c601344070340040c4503c0303038401044151a508024000c03d901380c0c01b0134050b44402540d0780914100d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 440526375 1250 440525125 440525179
    0x604090213021b071412010c2109560426070b060102031602090a14130c241b08180909010207150b0f06040306021206 52
    0x103800140c50303151951580f031107506400c500b12503901a10101003409a03680c15088040d0070255503044500090000384c1e800ca6002102580c000b40c81c42d140c1c8045440400070090f0540307503000b0042280c811a44901c11412812107448011a060a400e8103001000ca0380c96000080040484500c02d01840f80d12101d84850400d10012003000784001030070800740003609080107240f00c0140c01c0c82002c42e9400862580000d400b80e80180307040d0f0011b03003650320000813101071480f140900d20850446509002c4003200140680305150784031100500d03060701c4020b025120b004046286280c05103141270441500351a5040500182943e00d0680784050088000140c85113007071400302c0c0740342900d41203040103003080003004000c0c25000034401c001c000e8081d1409a9114112400d5040f501c507008914202d1041c2c040003010701428000307000d000c00b141c2c2c0c00302d51000c0000d8041401007203c1800140d5950040c0c00c122605607010544030800c10b6004070180e80001c0544400903c40709094141d5000030205d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 440527625 1250 440526375 440526409
    0x1060603020915161a06181303142718010b040b0d06050d14010606050412030806130903080a050601030b18060d0b0114120102120601050f190905010806040902 70
    0x3010110010203135680100650050b00010585140610b00b45040c40155080b07840b03480301180c1680952450384201e8042d04011800340490b043c0e0780d0b01941c0d15034250942815004080c0700306034144c40c030002c1071140d09032004400b0544102c240c1c100720b082201d00240b5110041c82e400140a01516141140e090352601e01517182c0300c2014040100c003a00e8141c00c01608298502c42c00801c010488081660b5441c648001b40074168848000b00d5090103544070301e1030b004c07001c110300c0c2c4003080c091483c95401400c041c0c03d21f04a4540c0503e14002e44640301800c0b0002a1540304101c04020320303209594000d842460184540b000841c009007500180e030030020004c0390002c0120303040395200345c103120500f41d004054500940c1c0d103154460341c1c4004200c049004400080d840d0940308418400c803035001041881010300c0e034549000464803600140241d1107000e00420501081034800d4446500c02c5c02140d40d4900000d042c14001030100308050700c81c9010710f0510720040010794074220011265014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 440528875 1250 440527625 440527627
    0x100e041d030a120e12040302100201050c090d0614010b030403020f0a1a0601051c020306041107080a0807110f101b0e0108130209041523010501050d06170f01060603020915 75
    0x2800342e10600603c0144e44446807807240b0b8120700300c401407200140007224000c90b5200c199403a440c07030a82c03d98804917844e0502e400b0403c01c8045524050200c030301e00c14000e080004511030644a403a4240c00300b17070440140400c000c810007013015810050381c01e007840c0400213440601e840b550751917000a003004100058421081c00038000340d01c01c41c2903d443c0e80d80480ca141d1007101c1c40c01480300a50054803001d01039401c21040d200c0d400841b0040380c0500380d0050340720380740a040280403a200396010301a1010480204c54118000b00c0402c080c0807926492070103000b01ea00c0c0b8400001c121003251460000c40441d04d1500c03944540c01c10800d0001400a0900c03255130341d94951070001050403c40001c0d07014030120180030a204c1c01884e54a074101c0c440034200400083d001140e2081211000f400041c140001d00600c91948224007502030066188004507819469444a55000b01c0c0101d52011640c0211103e10540c042405028001d02e1b04d414218901000030700810f048405a160480311590 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 440530125 1250 440528875 440528897
    0x80a0903030b061603030b0a240203070213020a0305100e0414010608032704050408030a0e030906030a0902131509091403040b0406031103010608190b100e041d030a 72
    0xc000e4200e0342e0401d00007409640d03903040e044000814002c8131501603000900c2c00d4610380d518107201c0104030584420841401c08060000c03070054040040b50381c48004c41c0414403404005807038081c0480382e10b10300444056103d18040f01e0040481d000104002410018400700b0030030382c1c080c0828950400d410000c1b28408001c0d0243d040d000d82410b92042509101c0014560145180301030900080c0349032042441c4488440710800040d06d03c1910050711a507810004100d04080c10b61000e60342c0c400403c10389040918600c00641d00f41c1045648001c40c54891410600b14500701070360805181413090108120a60307100842c503046818042c0100055458802c10240255002c6081307618440d00120ba641c0e90b118041e1400d607802520820010904081d0701d04498200d11781620b050380c01c0ca1356403406595400040c030407841d4104c0309001c1d00c6503561040d0201501e4280301400390b80e00c40d498503a50213500e4018881218520340300300500c07002c4002c00905100d00031007103420301030107441c01c911581 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 440531375 1250 440530125 440530127
    0x4050111041406070c0e010611060108010c020309092e050f010201050709050d020d0807240b0114030408070203070806061201020c060612070b0415090b0a0905150409050f060a1203080a0903 83
    0x80e50a03000001c184081100005440ba8271991006035200d00710182d4010382d03a9100c540707003610441440400980c00901c05c000080c1000194541d004100c100841c020700d691184a00715850400ca003900c0c4000c2c913520030b004c04d041074044805090310a200821591415280082211840d0b0245034800c0000c5130850080d561001390002109420150f255a100481c2c0f4168000d51152680540e4060742c0100d9520420441d114140c40e075203060f115031801d5044506900307003076030000f4802c640c030180c00d202c80300142e241002510050b04401008000505004c0100072000d0344c540b083c14801c0c0e004000c1501081d6010407120b401000030f0394140044039400020707a05103072554010200321030010800042c0102e0b403840c540030002e070a0310340c280c1301074403052400300e284100c0c66013602044018204000d5070501c0c0c0e0140c0710300500114001d05258031400030ba8251007081d41c0c1541c8289050050021914004001c1001408d0224840c005003215035006884e50300010407050102e6500c00c0f0b26001c1c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 440532625 1250 440531375 440531393
    0x1d04060e01060e090c0312070b1f2102130915020903010b1c0b0c0304031707020f0102070614060d020108040605070528030c021b041e050408030405011104140607 71
    0x15041154030030b0301900c3c040c81e484d0b503145c0c00000d02d14070134440d04a4404150940804803446503420000d090069034901140c6501203007800c1c13000c0300f2600045000182229443d03824414091102e1072990300518a004001c040303d03580052540751490300d10000b00040f030500e9000402c414125000d40c4174a07042c40080e004040490302d8a4011784001c40740d400d201e001c00c08021714184526101c00d816125420000e03410300003124000d0105150030f60a10075050010302d242d90018140c8100e0340d808020b42c1c0041d09a130030011044031015100d40c5000c50100301001000c0e44100d00359114803050b905500000d1000c80083c3c4003500480da00c8021138107040c07103a8120b50107034581101c1e180260f0440880a41101440246080040d03d0207000c03031031052001c140c410b28061031410b14005405100100801406c0c04000c000030100f510883c03288014050180b10301c07a90144440ca52a40b40034240a07003920600719000c0103010b07003003100348140d021104d01180e8058040c0c1e900c41d2034034034070702d044600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 440533875 1250 440532625 440532629
    0x30e0f061e13080a050d0e060406080415020408030c0c03010e030304030c0c030c1d070801061d03010e0d0906090f060c0b040f0218071101060b09090702100c020102070c1d04060e0106 80
    0x1e07070240c030b00021529a20004003048214443c804035000c40c404050202c500c00300465444c0d07400b0b4002c00c001c218180c45802d43c0c68215004548840d120304210082c94200d81c0079603c140010341001c240000c0d005403c8c0180405000306030000d00c040200000b542d038807440010402024080b84098500c140205409004081e6501c000d400c10240e4039540c1c0f0030010000c91441e144214000e50020b50302c81d105000442c102c88041d00d502101500c00010100c0480780500740c55019035a031144415a080300700410020782c1d40d1510b85a26003810040010800f0040d90040b0900d00c555803400c001441d0b02c941c5081e481d58001c0001c2c4650345841c9400c83e400d465052000e0f600c50b40e020040031007025000c490500944080d10303009031640f0103000703080c2696011312541c10710130400c1c13000d12400d0510390151580b2181900c181d5048222a1005d0700481d101c001188005079800b00d4a42c00300038074115610080c009000c8816007800a05645601080c1c00410040c8001e80316104264041d009402c4140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 440535125 1250 440533875 440533897
    0x22110060803070b1626370e3c0a080d0203190905070e101a090109080703080306100302030903030a0b150414090703050708070e010c0f0f030e0f061e 66
    0x12160340f801036081b142110940b6500c109503010504072403103e101041c40e58552000712804000f142084400500030141d0200c2c5803158000c0c039511010080d10100d80d92008900c44250081c1603405040400c0b1600044541c02a643d120380d100710041001001035940300c84105402603901d5a1313a800e4080d80750f0303c641c05076501a0030089603008003c00450b2000a480c407509a2450555030040d40c81031280c00da00c500c6070010002c038040300e00350440800034400e21a041c1050b46403203030b0701c40149103000720f940d0054a46030800300034041e161922050159086600303280030360441c00d14081b00d588034480504510459075407900640400c1c0c4502d17401141402d4030166103a1942c0d40c030600b1416005841c06103601c1070680100160941d4040d01c80c0c1d41c0140126503c1307100d50f5898100c00c6c0c560400511015051007014003030b10740040d200310f580946040c0300703044907160703610385140140425001524041c807900081031020481d0301c1e50400d86092602c0b100c0413000c440901001342513031340f14440d03001c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 440536375 1250 440535125 440535167
    0xc1b01141804050705041a1303050304030b0f0c2a0109060609060303020106051203090d110303030412031a03061303030e010203040f0b10030803040609022110060803070b16 76
    0xc481141c810940704403461003518144030035034816804407040d220782c3c0034200e50003101907401c0035100c10f0b44004d444160020404840401d44a4a41900c0c50704140c0c8110740e00c140320410015401d008403c1e05400c007114040d2203007480280c180c01d1400c1e22440891608018403210400300a9a09401046260713401040810038640c5403025200604aa03010a50142d030030322030005414101400740d075030220358110203582019144002c001c0c0f41c144090050355107041d040380f0101d46690510043d070040e41b05421092103160080c038007500380c1d00c20222418a581d141d6031240015180860328a034801e881ca960345580803900d26080c0c00920000107101c0c19980301104200422100c1310001c00040e006640c0c0038029540d00c610415041040e010042c03480d4814008940026400e4100e00e0000e4801090030f81007002000a0318038a4104094140c92940160000300ea0020103204401c050b1108002030b61030940a6114101216805400c1704001001c05001174115842100c5c0d40d84500d42d040450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 440537625 1250 440536375 440536387
    0x40e0f0a14160e09150405060d060e0c120609070510020a051903110d12110c1f05090708030906070c0e09030307031a0f010c0303110c07080c01050c1b0114 68
    0xc00084211251400b2400b1004605000c0c5408000203208482e640741046105c0010024031000c2c01c00980341540254840e04c0700000103007180078010ba2051858002c04588160608005815403c02c6a0514981050007440100c0901040074015075100b6503d05212060449049103411071030b14026007940100c42c09043c80d051654580ca00d00c0e8001e9844240d0082c004940c640c5600000d42c0144c082040d4890306050300d01c40e501f00340c400621140b4258200140154043c0c1000b1b5007183d00e00740e9100e80098620040b01901c1143d4014030303442c0041108a0800c4060b543d20b11039460352620540b0003003a10742c00c010100804001601c01c0764a080d040742486000f142d40c2c0d0b0015509003000c81e0410030321000740f45a1581005a42ca002000c120207400d4039001964150301b404402e0f030801d51101c000310340705140a00207041c10070301c1e030001706007241c07130006518141802c0c08002e60411101704061040100c001402a07400380840203031009400c00d020040e1014103d4140701c94462b2000b20305 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 440538875 1250 440537625 440537641
    0x9040207060b090a05090a0b090703061109031002091509060f0c0604030306150f18090203010b0403030207080613080c071a0403120e0306150109080708010b0a0605040e0f0a14 77
    0x30040341c54005a42010b0f80d515001484029a10100c5000c01c1580c4082014008110b12141103500074200c001612440c40e00e0303407a250150340360030003480984000040c2050850404001c1e1003200400f000c41141865502d100091000c0c4071080401e010b40004200d01039140c0c3c1da4070403101c4240d4851401691103075400c08107922010100e405a010034549800015000c1c441000010110160b6a515408c441600810b03030f181d0030040510200903a40c0f96000c98600b1a83c0300441c040e0444508880d04c072451858000d1601840342c002030003a80241060100c90380d08440c1908105506c0070116031102c5601c03115900d840415800343d040c0c004c0000003c100444134400600549020310510720840c101440c0c26a1380e000817443c015095400400000e02c00400c4c4540340c441d6610514110f010b00303545060b05440c158450304070080c241d54a02040c0b0700d0340380070801e1600520f500c1c1080760406250200c29462080014150710b090815800001c0442a0030b42c08140e508211813883d50b09406c1000c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 440540125 1250 440538875 440538881
    0xf030e0f07031b080604030507030c050618011a0603040303200a030603060b03010b0d110114031f050904050a03080604111303050705011107050409030509030a1103010b0a061e050904020706 83
    0x8000e503001455580c080010003c0c02a10a00b0340b05610004c02d9241c9841e80c00b01c0b40e5a00c0064141c4c05c00c208440c030100001e07814401107020703c122440c004103404404034860300311405101c1d0f0042a10102524003d180c50f08016030340d01a07014140003501504010804d0718900c03c46c3c950034034011000815441540d050b611140907a0b005140c1008000980400c1c18202c2d4648000c443d840005002240700207500200342114840c03040c5842c0059501003445c24606070429540003140c40c0420074141c1c400070030360b0000030041c2400c458500c0281800c1e100c60ba1038102c41000901084044e000007410b545864001500b80e021a07010241c1e500300311100d4181c0e41c00140821540d80c000d581c4002125032051840f91070850140300031308031040c642020000108074004080382445405d0000e41625034042c0300ca00f0314980900300e980c024008000405003101c010144080c03050b052801c0c240070141c1d1017840e42034800309564001200c54034022095450780118620154882d00008a00040200b150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 440541375 1250 440540125 440540129
    0xc07171e1309060b09010215090c03100f051003020105030c030a0b10020d12060b090405100801020c030304060e07030b04150f0e0703021302031308070314130e0f1005010f030e0f07 79
    0x400c00300900b60700d4540e164a640f20317020025006a002a910160f040b600d1005143c001050030110b80b4994449404203040c900c007c0c040200050760341601102001090140a078000c42808005450130700316030018007079000203010400d00190100c00166206250b9000c10940c000c01002c41d1405200280c1c0255900034401804000038102c82c0e4122594204d0302801c0706407031180c80c1c0e06050028903004d21006080c01403100e07100e0104c0e00e10000c0c11503030a01c02044075a8203200615135034034250504074241c0f01c101c0c0302450207600c901400c00218002a1110f90040e512a580104c101140d450190241401c20b00c1c0c485028a890740520035190700040c0301c801c4920135a0340c41c1016001c45010f40c203c0c04229289140461802c0003d40002c0c60440242800703032003800c102c080030a04803040442e0f0f0304001081440c80464000c1408100000041c0c9548a50845c020088070301d0011101001d0280a22406050142c0207004440301c9010303410150b40d611045c4102c4090080340329181e6a204194 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 440542625 1250 440541375 440541389
    0x7030e040504080a020f0d080109020d0f1103090601060c050a02040b0d0b0108010c0311041404020c120c1b03010911041107050a0605060a0609060e190503030a0c0b0c07171e13 77
    0x1d0681c1080080852820307121f006a480d104500c3c0e182c030588a020b54080000040c005aa620740c1c0548803c030ba01c21015070101115006803070f13103000020280303070078011b0300302c03030305004203200000f0009800090b80d41001d07034107940110300302d105580490038641245100070101106103001080c82c0505510030f11880358281c2c0d007400440044000144240303d5805400c1c0320b0302c01405004401c0c10150000c0400c414920121102c0c40110152000d0607003203404000c049805c030f0744843d0440f02c5c00b004450000503044008018141090780c9200c543d00f8403400c81806035840e090f49801900ea840c095446154014003541c1007041580382c184014503007251140d206082200c80810740301d110f80003500988916850b101803030421b0808206000501c40080b2a02c503c1c41040800d840c1c0b4144051300c001809919016150f0f1511b14203482c02aa00034212440d40070140701c0344000c20350003024216441d40300f070794031680e40c225001074825480b0610b800441e00300001540120108008600381d08440d01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 440543875 1250 440542625 440542633
    0x7030f0c320f0109050d05031b0c010f080c070209070212070327050a09050901060b07240203061309020d0807031e03020715020309010e0d120e06100b07030e040504080a02 75
    0x1040801010b030201011441c0007603051a0140a6410646071240c0010b0140307048a0902c501c2c1b032400d0300140010803a00035160412005070b525940c0080000b00d001005007490703c0503103420b0100d006540903585020384a00814408aa1914024071440d640e0700d0010b00210b42c0c0d603c0509028061195031351a2220800520860700c483e84c03801c0802c3c605580c00144a05086171506021320041d14018180000955031080300080c4511707001c000f805054803030842e00d40003c06041e04181221440c410b0340c40032038010000c02140e03954124907070f6494001030800065a00650004c20751161000c0d400030409000024032078181a080043c0140c9508942c981000d0640851801c4081c2e000d82c04004048070741402600c8078400c501e4000d55404052072000140c0d50114880301d074501112402d00c0400714004040c89058425103026100c4000a282e0040145041154030180580c41c24802c290400c1c00c045600010140314100c0303204142c0c030080c02407145023481d01705030704039a11803080d110240c81 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 440545125 1250 440543875 440543969
    0xf03062a040b0906210a0c030f05090c120106090e0307020901090b06090f011206090203100b070c05011404030501290301051605133c0807030f0c 64
    0xa2900449050780c40c00401d060a20716003106102841d00041c201703908a00400001c0050001d420f80458401d0142e0000030540584031301c1d024044561800c0c0c5441c0c9603042c2820015004c0c0300091004030040191202e1015031031a0324168010000340c2c102015407410070792440403c000010241000301d000f1901e0100c0e59994803500d10440361808091074000000740007030b0b4918504145000000300040c100b8052010b1901c80c40d1086078066000080710350750110900080741161305107003001e00810401c0501d80007141d1584001205280b04807410045241c040300800e0303101c0d0090702d00656000000f84181c1c03401a01c19120f243c101020f8002d00c1c18a4a040710315480c050165a0084007a400e030040712007038034141104c130b641c806105c3d002c00002c800070002e054503056000750f4896541c42c03456400425001076103600e1416035130a2404c03840c1d0050092092400124100c02281c0d882401842141d2141c640b4102c0d030089540148c0080d64010518082e1180c0c6d80003005000c2107006160303440c05 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 440546375 1250 440545125 440545201
    0x80d1d120c070b0f0903120a08060609010c05030714160501170a060f03050703170f39060603060f04031202092403070801090c021509071707031406240f0306 69
    0x2c01148d0320741340050300d07140c0400c80c203041040c010011401d040c901004618450307280c00c0c2c035550009204480030104a490850314285c103000030000000c00c00d42c506c0065203441e00080109040816502c100e1141c100411614034440d0302c02001800d40f06040c1e44400d550b41465900c0e01003d10040d6008004101d0462111003400e00704c510300301c03c181403542000c01d408441e0740c010a81040c00d40003e900c02d2042451154048400e145d0980d02c240207140d40d00e03141c018182416405000c400307007003150000340f00c0060b80001c0c00d41c0306110206401a02c1e0200640003a112032417800100030709940300c4000340004d401130002584201419250300c042d607603a03944008100d9039038852100040e003200e103507140b0305a038058406411066190407541d0742601d502c11001d084004010800d40c941c000e000c05c0040003004031380f840c405240880a0016442c3c001c081c414071100300d804290030702c1d020a0804400b942d4400004440c40000f40c22160740345841c0d05120710161030024000d400e00d0035801100400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 440547625 1250 440546375 440546377
    0x304030908030913022113031b0b130302150709081b150702010507060e03040e090304061d0d05060a0509010b030616050304020a12080d1d120c070b0f090312 69
    0x5508041c141104c6040b061000100941141072500b1140b007031b0000f0391008002c101000e41c0905190185a56440740d5840c1c050000072070091800142e070070142c0782402041298200507808418040d40c442c041c68185822420f045080c260f031182043c00600b4408030fa46c1c48000c4100742e0308003004072116440b1005400c00411111110140d0100c07c41a4006040c030009024081d07442c81030600e5428101140d036680241d4140f1030a090040e440860b081007011002c0d000c55405c2001078019520f0076040550080c4000415450008011003403054601d103038803041d6003204043e030400c081e940345080c90303c00c01000e06001d807907500481d8209400800700b0318010070443e0060801004408600442107000c0e0b0b415000100280e0740600504000150000322042442c160303482212403c0c1e0707803000b1035001001c0750b060f01022003001c5503110340c506140d000000c00c060815000107100f40c6071200321054501d841c0260304800d44041e004107a03041e40030fa40c28060702d20100b044041d25000c1c070b03585d00d078000030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440548875 1250 440547625 440547637
    0x1e0308060d05060106030c05091804020f010c051c0e0d050c030709060b030621060702010f050a060308180423270d030e07050d0f0c0e0705090103180215030403090803 73
    0x1035a005a4010403080303001f6030041c211100301c0e080040c100351202000030040107084461884484080c2e042000b1440c00078015015104d0034240504e4041c0c1c15111a540d54002034981a0903607000c101d010b00b1540100c1090180d25401401c0e8981080c280c645135481706802a00140a407003003402c04102074030b00d070081c84141c5120201c96070550384d8440411601c0f22410406402602c0840c400c5040003200344203444c801c2d12a50004a045421101620101d841c000c00798441c00349010014000240341c00101c440ea102c10303948a9129201e2000010010100004107c000c108000c0c1d58403403542150f8240c1d03208240d454400f006030701107507540c14202c816042d403e43c01600030420144615000b50301048486800c00d0890b1245a220741c049007429103401e0b010307166000450003040c200480c2441410203810743d48804540c50602c1d17000500300f4060100000d05140c0c81b00d420b00c001010311524082d0860b0002e01c54440e100b88170740001590f074801e440942c0061614000410181000400c03034103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 440550125 1250 440548875 440548883
    0x20415020d2c1503090708070b13150e09090d0305090303060a180e030d05090c19050105090d20120c0d061a090c040f0906030206040e0903071e0308060d 67
    0x2041c0110040481c911a01ca4075603283c2c8103068240c0c0326980030303102c0d000d548103070342510080c010541014500c901d8a0349944c04001c5c08141041240e0380000c2c5414040100e42d64000506081c004858050b038410644801007a00b149040003003210168000803400e0b440c0f90962030400050310341d512031503140e110803078019400548104082014414031008001c1c2d526030440c3c00940c1030481034000d4150b62082480310b00c00c5480e00107025210320144a070700c400700021034000300d6003803841d40300c050b41c4001407103103a0612001140040325601d401c03142011565200f842618654142d010200c1d041d00328081460050101103030340000700d0b030009064011008010441c015040540d40d07600c01421a0801100e0385d142407108004264a0310f08000d0302418070141e849403181d040c0b0349400c5a8029640c8080750150801d0410000368072460121000c0c0c4408004081d0540d80300d400317852441c420204018101d001d00d13145541d40074803280346047d00501c01d41d07504410761200c0040103941e002000b13010f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 440551375 1250 440550125 440550167
    0x11030304080702010522050a0509091f090c09021305030703051015080d0e10030b06030a201c110a081501020111070b01080d05130306020a12020415020d 67
    0x140120341c811000e81440761052412a2800140110781c901140104980d00440ba141322420700007460419117290241800b519010321900e42100d00f1030351805856421329001d0300495540e950601d440e0001e00100e5041055072040d00d6880303900034005e6100c0700c0f5022514112190219541c640403580f03000300c0360030200400d507401100d0a480300404002d0755540031072001c801e0004604500b408183c0d48108c10303444001c490301d10282841040d0b80903e00c00d800b010718180c0e204020380e035a6815640c10244503800010f94040314030301c0151702100780c00c04000040c40440e00d82c5201e03d656900018402c0800c0090044102002d803071003550054600c0600407604900000d481e5064001a600c00c40e0014800450b003c24469003401c402c1e4441c840940341481908010f2000d00401c00460f02418113601d480c5240c449a11311070380c2400c0d864000101140e8000490010780c6202e24441c2000000392081150741e0b42d62555002400000301c0c900c50054060085800080ca005890701c501c1a003402c0d00c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 440552625 1250 440551375 440551381
    0x6030c0304143405030a0515280506010f080907120501090503031f061b0201120b043603050f0a030f0c03020d1503030813060204081507170601140c01090f050606010f110303 76
    0x10110440c005000101c0e0034510b5075030740c60102407500300b42700801001000140c2800d000d1700040175101c04243c0c51042c00044020b200840c68001104000c4520b510461800580640b4100b40900b0140d14050468032000c41800f1341110106039003080184050024121a5600d0001780c1c0c0d00391b00e408898500c0c031741c0c0c00c0d0f4a40255000d10b1090407918101030300002d00280383d1000404840a00340f41c85048407140c14100d0303503c40e4100150500010aa40f041c510001a0350300418600c00d210117001911404914050402c0c00b0390800e04201c8481d50050003c00085040100250000e00070883c25a0500d9026103041442034030007002c1c0d941595442665a444240b80c22810380d041c04e003240e5040c0e01304000a104a000d001c1c1194010109401c5030540c24030305401046101c54403850310942c0410400d100590303812061503440c003184200601e880c0e01315401114010031070b503c0058209840c3c10940010020003017181d9100303c000b41c89604d04086200303021107503018009030000700f580c07080000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 440553875 1250 440552625 440552653
    0x161701060305060d050124050405040f120203130815010608060108061509040501121a0c0702100e030a0c15090b090603131e02040b06030c0304143405030a05 69
    0x100e500c004050010f0b020031003150717182405c54040000c142c244035034187d0030903140d00d1984141d10051804450510940c2015210543c00e5012120300400192650303001500050081c402e0300d40494410042c8000320b59121402d60311581091100000041960004500d0500980509014180680d00e80c14513544100c01d006110600202150444600307000007280da035240d0264070b010304135007045000001c1c2c140c0f60100034a00e0051407105003d40b00f204010441000f5406d5030100382c4c0445400c81078411040b01038520f400754001c95900350040b0510003082c408000c0c00c101c01c680f0400d01405440c07070000011200010079004241800c40100402c40c85d914212001d10341060155005111283c80303030b030b41c0d80584480d240c503014003410020910380951500f4814540861400d8600750b10b10b24004c00b00c00444c1c40b00410003040d4100c101c0140f02e141c401080402164071034550610300c120302d01c41501705460b64460304103022040800d80404c45d810041401081d81340d101009081c030740c0400311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 440555125 1250 440553875 440553881
    0x3020a0206130c0b0406050408100207022206030b010b031e090706030e030c01020406020a1104050c0301090c020c040f2f0304120302070203010f06151e03020a02030903070306051617010603 83
    0x3800b60f554200b07041c0042542e100b04401000186100e88407681c0d55441c240b0907900b01f488000c640d288240c4140000c10240e1295054446110304a2620b2054885e1034900d00e0020120303504090460000b050011031101042c80086004d800d08890140c5a090780c1d100e2400744030805c940c3d41c61203402c240400c125071802904a0360490a050080d0303428a20f820314440d089030815404200180d0211700004103000380700184142110701554140860300c0c0c10400303812944030600c2641885651802e4418540d4400d10600c020690020814440e1440000e001c40150a1130784040d00c0440c540c074065880d0100c0172040340a0045e5182c4410704559071034440c403000c1250300d06110709141c0c0810158005075020311071211810f652180004059042003a0041f103180d4403680d56052241285c45202c1820f1060700301800395216203405a542c40304180c040b401c41c0207210460fa01441012008401c00c80f05420240c40b41000e1614104c02060444080b10312100c5442000e20040440006000052180e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 440556375 1250 440555125 440555161
    0xe01270501080c150d09081b0309010203041403010207060c0306050f090f0f061f091d10050f010207120602030a0c0813030c11090f06091503070b030a06080613060c03020a0206 77
    0x604150304140b407000c40c0070301b522041e8500f00d801940c0050104015a0380320351110b4100b01c2c0d00011802d108204001130340d24461070051044664425813901019074094044401c0254494418865020001000750140815021707561007455881d01c0705049040000c0390a101e003103c405d10307480d42e031200300f8042060240900400d410455002c0311501d150780089a90501c4070303070b554511107118541014065404007860354210191424024032908045000a41c800e480301107a500050400040c010303850442581c0c0f00f40c890f0001e01480e20140030403039001c0c41c45810164410b00444500c24021514184101c0d00d4107a6402c1c4075041e8400302707100e0071080708400d02c02d0040800d888000d0002607030313190f01101c1086403039aa803130810440d81402044185c12582801d504d81c103080c0c075040041e80301c3c4040c1c025854440d03804400202042056003101c1c000f00000416581e141c10000070550b65215524000c5c2d41c0305080c40c10004000f4441c0c421038859103803d40c0680120307210000d040c50703c0300b444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 440557625 1250 440556375 440556409
    0x40f0218070c031205070f080a0e0106031b050402070206160303180506100e090706081302060c030c061005060a03051906060f0909060e0606130e01270501080c 70
    0x104211081951811019020390402c0e15142400700c0c040ca4010300d2401c1e5900d01c1031900f802e01d0148200d071a00514489030703410007030030a44082d075580750001004200d46996000c156003851000018080000f02c074000001c07500400004207034860003440107030301c10030380e0003508400104082507143c640800c1d41c20074036110f80750108000d2000c4602040e9880f03884c4080e15241c10007818420b0070700c0310007850001001c4a074400c0106181a04200791180254030800342807010284c001002029400303040d110240e8010402600c901c0c0d0301e14516920303005205100d00034410f0b580800c0c1c0c9050390607c480111280180f03a2498070109001c100e028040141c40060016081d108061861000e400395501402c2180c0c6d421210602c2c050340241826002d80c44403008914001d03041c400c1d01201d8403c56070156080d81e007030341d4514140f0742c020541007040e442920b0005d0075100108850751807207a80401c200944082038540c0c14030311140c0048500a00c103c5000c0d074407421041100b410540700000e140005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 440558875 1250 440557625 440557639
    0xa030921081807180906050703020309010e0a051c090b0c0a03090801050105060901120f0608210309060a110c01051f090e0d08060109051503040302191a18010f0b030705040b09040f02 80
    0x3941c1e81b05c1a00d030266090301c0842d40100400170252800d00c00c6107110a0048010844c10500b40c5410303403501d40400452102a42e074009a0804078007a0f1100001008a040440d40d609111134200f5181c5505120441c00510072120000b00100305005507416a040107005601c2d12001000540c0c608020861204e10307140c030748841c80540003541c03040340018290f02000d0f0440858860000c50110241c0800106501c01841800303070100001811541c86008600c001501820304140e4409a00030300d492640780c0d600740030800040c0100100391800c00c104000c0f821090f80d4481c09000140c0300b20ba41d401c5400e40c0064000c0602d1841003003003d0700008181824442940c5580101d00b54024204400c000b1340300c008113110405a041081e92100900201c403910507000650301e032400740c14861000c107100c1c102180410307000c08894842040904810008001e1858040f0800300506070f021040c2d40300c1c0c0503600700000c0600706070040300301c0d64030004c2008045940315034440008500c100c1d0300345d8002d20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 440560125 1250 440558875 440558891
    0x10c031421041421040905040c050d0309030308060d02061c020f040801050402031e031c0b040e0105040506060a1a1b0f1513020906060a03092108180718 67
    0x20312101c09024038010368002c5201101c1d04030a6143c001100140c241041c00d900188600210580c141e505613142d5210105441c0c41c0c5003441c401e69a602c1d04410760042c1039004000415403c08020004c4038841d0b203507013203a556014200b156103065540007941007a0100820a240c103030442c11040e80030500c0e0703001420001c003890400e006801c03070b0f08821101da556800380b01c10b5140412491404094600e81580d0311907039266003d03140c0c000c0a00c040021607290b5840d250107035030394200d111500406402006003caca1000350b107020303010555090302c00e070107120086051800c0006800040c0da1440d5540c0c4498803900000070540d600c2140410320304440c0c008400381d454014004404640c041d00010090b00201c90000d89940c000a400c040040160123448001030b2655640580d000c8021294142c403a404800c00760003801ca0204000e01d204165800240010700130980b480c08040e030340e941c6d082140d5940c0050f0f03111900400941d20300750b000d45020005000314141e850076501e1513480101d1104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 440561375 1250 440560125 440560177
    0x80604061a0a0905040c09060c0512032412060601140f0d02030f071b030c0303021e0c0114010819020310020309060a0b03030307200a0c090e0705010c0314 68
    0x1c1c62018003a1001400142420703010782c444103480103004100c804000240100b070300a480200b8900c00c2c0380500c0340c41452081400414001030005d410503101640e500d00c1d00c9066464030f42c120701c3c1c030012006081007403444981854880180a5244540208070740d444040042d5841d202d400c9007828005420407985505507000d401a020910441c3c4016882e41050026028040002080c1d001002184808c0940801c1c0318881c0c201100c1d01810f006841e6000b0303040441c083c0c8903a8101131810742c2c01341c1388a080340c0d002c0c01c01405003001c140000c00814103c00940021500d0a20030019030b9030000d50000703038440742c106824180700e100904581c900e030740703c03800a4140e03041103032010169002102084465581c50046c00f01d4001c0841c065482c500c0c00c110040c0c1007515100720f424803d80716500903d80c4180030008600d4854100030003012042e40c07007480c034029141500203034030607015103140040c0369405815024945585a00d8000c2030309110b104100d19a0040144d43d4000800c09449000078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 440562625 1250 440561375 440561399
    0x90f1e05030d050f01050603070203030103060b010e0303184002071a0906070504080d0809010209040e07051c12030905010605120a05010e0c0d030c0624140d080a08060406 75
    0x2140b201c01c0858a0320703160a1002c3e0425059001902511040041044155020048905480e0702040c0001c012120b900101d410a0301d0102d0181c051000240226002507090940e00e8840d4080310001c160100003000048400c100340c0d40c00e504000c4800854102c20100a80358030f540c44084401070911045484481881154a401511094444060111002060200c0e5500150b01c0c00d05500d000d02e400700d0f2560fa900a05d00b18800c04c0090b00c003050b0004020f4040750399500c1d004009109418100c003a09844019078801d00c2d10a00022581e00d0481864510000442d80c204d0310030058076200343c1051700036150507041121079540c1c40c4000b08041e0743d071591b0038000c55000c00081c80500d03c0e0746802c5086401036010310341d49601c4032180d4072180d40c1da0100e0a00340d07903051510b81c5807045d00346000c0c0041c04601016402490700074a42c1003454a0b404060011101c40e004550040e480342d105002e0109200e080182a044080040c556403a019007242e0741c01000c060000504a0340d141045046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 440563875 1250 440562625 440562637
    0xf03090a1b09060816140a081204050102250e041a07030504060b010926010906020c1614030709181523060a0509040302030d062403090f1e0503 63
    0x1610440c0301c000d100720038035440740d0ba000d03000343e100501da01508014070030111107840c03040203450048148502c5d103a0325894296002803080c0700032a404074110203a2200b10750080d004060041c030680d41e101110f140ca81c02c035005100302042c54460741c0c6d070074a8003654409000031310a58440702d01e048184140711003490f10364424001d80d500018070b41003034503040040d11070070070540b41000801d900c24042c0c2a85128104186804060010700410543c40004d001d0102d84101410b40341c8003103400da030240004100081880059004404059203d0001401680d0314110b62a00f43d800b4410078081c50615912160300750b620703001c0c102e0031000070390b40341a852014808036115241d190094201001c8800c43c5102001d1440c50f480c825901d8580302188aa0790540304080c0306602840108090500a20840d100c0c5048141d090041507208e20b08090711121559402c40ca040c40c240660b10400d1003841000305e55071740f00c8111240e00311607848001415072080404003c50a049c0300381030001e04100000c00c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 440565125 1250 440563875 440563913
    0x5330f090103050112050c271806010b0c150a321308070f020d02090c0405030d05180d0201020118030903050606010e010f050d09080a08180d050f03090a 67
    0x2a890901034001070542c3c0301030303006074002400a46107900280b8003044500031500169807030210303c4e20310303441c200380c048244101e49083c0c210382042c8012000241700c9104c1c2100071404940d442d90780e407003449555102c0d03c501d24119820555441e00e05003400300400360415079a9102040300c103100b1b55150420741c200541c1242c4522100341014500e004070343c540e6481079410a4965001e0314a4480302d000e4030a80780010410f9240d003680c18210365403120403001c1c03650090b1400c01c0525042c02000003581c410f0054901c00d00c03512071030201d803910a4088031000408082c0000c5142d0491043c403800094402040307042d55221b4654130b0a040400c05050303140d40c040c0e92074160b180e1850804d581000c00103000b5a04101400514135036a0742c00641140341d0700403510b09941e5030703601c0300b945100910004c10014080d14002911700c41c01c951115803030307000714910794020301e01c0341032a071601d81e4600d00081703400c0216505110b546505400e1300d018507408001007007942e540c0c01c1c00d070f56005803015101142d0b40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 440566375 1250 440565125 440565127
    0x10f0b0a050406030e0709020a200d0212160b191103070c12090321140a080c0d0b0904240c080c0a02010609050405010c0f09050607061a0301110408010b090105330f 72
    0x100c180c062003044482b02c019074000d010004040f0300d0094556585292510001c070001a418803182c5400412500c400d1704010410050b0500c51004c03039408030310792694480c0a00b042e030f81c100e0300300d9220202c0b406031382113466010090285039207003081a10700c07105240502122000001c0403862000716200c0341e0b150907904c2036507445000308c0a488640388003c2c0a40c0500c01340240c9030296046008660058102c002c10b40c0c9804000c0214009460105d5041d42c101c52518140002c221002001307040c2c041404419420800d055010003003110b40c001d8401c0e0004d501880811507550b06400240f125030414400424546d40310074070740065410070790301104c90b0717990703541e4644059903c85c440302a030040038680307022294940b03000104103008010000d490a903440c40341c1d0403a146402090306010001500910030b0142d000e40c251182d40103445100f0645d424142d50140300c3c40d007801c8140c181c60008103107502510840503005102081d61089038010110900e2449401118101030610340c41b081941c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 440567625 1250 440566375 440566397
    0x61e030a03021e031804020705070b0d050609060607030e01050a050706090b180303100b0f210906010501111005060a0803030f2a12070e0d0b010f0b0a050406030e0709020a 75
    0xd000f01050452101015001809002c08104c1952040101c0035022103015840d90b415003012400d100706940001601140041e5500c1e484440c0c1d04202e10401080b281030300d481e942d100c280400303417280704070060005440e104407200e60340c01400903000c00764071840e18909000559581030112104203805031004001d00003001241800314031a5041c0a0b80e04c2c01842c1141400300c000c005a00b25802246204180032803114042c4981c0002d884560089111b404e0310a065500c0c03001825409407070a200e680035180002c2699401020044000482c440090803114002d030800c000500000c0c082c01d81c00f8851350400900c00d90b04101941c01820f442803001c2c7c0e54140321180c440460070782c4540c4100310307010b00c400d601c03040310b45400e403241000301044070380b400e527075251044440000403d50740c2d6010741d035142c0b15002c1c484022580c034140d0300c0310400304900396100c4150400f036008140c11000003400801040c44030070301c0794000300e51303038103c10045031800e0381c84082c044280c1c1c0183d0a40c4000030b40008e52 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 440568875 1250 440567625 440567653
    0xb060d0f0c1b0b04060908030705030601020106050301060b220905180c0102060f0c0706141302031002090a0314030408030a0305160f0f0e030f1002042c061e030a0302 73
    0x2220110030082c1040070300a80030054090704080d02c0500900706005440014052022a8000c0c0221540c0480f502e80d80e450040300140840d0019102e45005603e00000855181014403486060310110843d582c01c000c1203200d41e0740d00445000310f4110b500448003001910103040e00802e4061aa000700c00140003810713003031452070250b040c61010704542c0600c051140e40c0061003540d64000c680401c11607601c98240c20604054520085c0000c1c81700018010440b48234826444546917920031001d030b038501d1114040403416030003903a0400c0d9200705680000c0002803501c042800d0500e00e0300f000e5900f01580c80c2c4402d411a0041e2080e0000300f078981c3c04000c481c1c0500505845040201d00301800d100001100003420320003442046824841d6204c6280e0b41580c0410607551310054000c21250024680d100d64000f941051051004a402c004d944440030000190440c0b900c0004400b50120303070362807408100b402c40d04d560107241130701c1c00d1840084039500c051100c42219406900100b541407e8004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 440570125 1250 440568875 440568881
    0x30c030807021507020616020423060a08010213270507030b0a0510080411041e0c02070609031109040c05190f05152d030108060118060e06040903030b060d0f 69
    0x1c0c0f0603d80102007102600598400081da2121043d840320101d0040140c40441c0003010003503c0f9240126240c0d10000c400290006094860107040d40d0f00a41c0ca1342c1c8852543c01e074024a020311a08000c40d0703002b805440040d500741c0303070000d1501100b600d00c0d00d81c3c540c0301e00071a0801d031a920700003601d40d44c1210300d600301142d1101c001c3c482a41c0c00e99220402e50401400c1203405040180b04020300040004036585503000009100c40003010380c0c001516594640000701013000e20f101c05030288040024659020389910307411030760492804050f40313061000b00500010001c004480c0c0707035240e40e00450140c5801c0c851048075144112400001410841542c8607802c040d80030621945040d6040e00070701c1c1928080e2502409031180c3c02045410044060400c1042104003040e59440030000090110303001504034100c414003003244000f00c4200c02010180d6100380500300c111095100403a80798149035000c00364a601030318000603103513101d030005402e0341c1c0009802030f4032503103030f62040c3c0c0c240c03100d84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 440571375 1250 440570125 440570149
    0x30201020c10020c0f12010e06090705090705031f1203050c01051014060f0904110a030b100903030e0d0206130302010210150312020312010e041a091c030204030c03080702 75
    0x240c250b22000c82e9100b00950b90705000d8003440c091500022800c081d61500760056452901442c020b01288440b14001565960101c03556440d91082000c0000e150500540c180d000d80e28503135515203181d45044040c580780c82140c8400102841410000880c1080294000342091003a07a03400d540d001c0c010307480c60075100c000e0890b84180c0c00b5084100f14864111045126600007030312110b03162684131008903620f004000b0415045814440340c0c0040340350306070042c20902034070b031020410607003160140a000300988401382c0110307485000600100303015104c042d4081c000103103020100c0c801c03a408225030350002d14100c84014400101801150780500c00060020b0b200c0004000c0381c205600c2c05441d6107000c0c8030241080300540c49009401d8400d104072801c50912190700700303995075280d541e030100c510221420b403001421501c02801403907008001d240246c8075400100700c0864034400c2c2850200c0d285d071640050590801000000401807401038000b54015416a6203c810a0050000d452403003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 440572625 1250 440571375 440571379
    0x611031e0105060307030e01150f03120302120414010b1503010819110405060105070b100e0a02090109030b1302211c05070303090c090f0504050c030118020609031c0504030201020c 79
    0x14010b001030340740c980039a81c1c4100c1d9450042282c40d50b0141c4980105006081140c44901d0610b01045605440c0c113080c00f240c0c46040d411810b4400d1401c02c90032400f9800308201c200301030790089008101c980c61000160344220b400014011801d500180c9440548401c11902920100042000e9041070011400b015450a4010300313007405980d44c1401c00704940e9010780300e559100b0119006920a806035503480d03078041e650f92003d003840c56010511201610804001c01c2466001404402150007518603038401a1203107032000d401e541c1c48482103400200742880801c10003441c0d41c09030b0f0340c2c001c580101c4240041208028440c02803051b040c0400c0309401c4900a4075010b040f11640c3d0301c403085440d059010325000a0301102c0d45018001404e495110202050402002c21042022540118007440c4640d081b02c3c070f904249000c1c542611b00950340b0020030035882c038000d0050b0402c3d50040428850003800e441314019005c0f200f91940d20600000070001f1300106052046503010401d000e40901c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 440573875 1250 440572625 440572681
    0x10903030203090d0303020c07032d150515031e150105010801060809010f061e05040506031b150a0f0e090f06010c21021f0b030c060c0a061103 63
    0x56440c0650b8038071800303003114010340d800121481850720079415900e40602a0b000d48031a150703a0304004588140611074541d86600c03108904200c40041c5409611a5500400780c4030042d03000b60541c4001c1034010215200c0e041203200b1f075280342d603084c07000340901401e50b020041c661f41841c0082c0e00d40100c0194004d01c40c800e480050281d80c3e00505103e045074918174200c0c03456510380148034058540003a500c4849424160086000002c9065682100007441d280120380c07035451040206661080e01e4094154102114065804100c3c5001001991000d004032410200c890000c0d400e9a0080c4d0f000e90011703142600c00c1054a5000e400100c005200715090119030070300031f816400003c8081c000c541844040d41c244e400302300c038050b00491b80e00522040300c1c51612608001a4903003141c00d04842042000c030403a68240d81584c0b28040a040010b40140f104081c00024402c26622000101d083c0b03101e01400d2800041d42c038025007110303800b1400903684078204048501c050505a0512200c5040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 440575125 1250 440573875 440573879
    0xf0203130b091603080a0e0d020a090b0102030702280e040b0a05060d120e040e01060b0d0c09090c020309090c120c0f07140a141c03270f030e0109 64
    0x3062410248499802540c51070064403442010b40c07800d041900c0d140506529140004140144600540921030454503a62158002035080010304100c00c000251f112002d424144410041c80d446800d101e07906004803032412041c1c1d00064076020765240c407104100303504440341140060601d003102c02807404081810040c107141d80c58582d07100780142120304290b654000102c45695200c0c050700e00c2504101000d041e0072440d1002845011102c01d2503029a0030900d06031260001407141c5000c4420350401c41c1d0808134404080c8002c0e00c00c8508041c2080150711012490018920075828910070540046680d40010414041880c200400250b5895800e100e001c0c054080a00a16440109240c44603a981100400c6041e140220940070b8052545206031024640f400113196806902446c0c898002c0d50309400d00c190740d0341c28601c1d1400c0101d40701c42c411090b140070340c02c940c10703038020000003149042185000940b1045052000da8032484030701e95080515800c400d1000c01c80c007080c030b4001031040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 440576375 1250 440575125 440575141
    0x30305070209060d020d11120a15020c030c1e0d030e10050702030f0a030501030c0506030405030a1206030807051605100906050d0b10080103032a06090609170d0f0203 73
    0x8000c080000e401510480c00040c8540e0743d16409024540e0700034100301c90002d05007841a19445407900d520f000f40c50b0542c541c0044803001820740740a80d84190303810502c0c07100307000b6075000c0c0d005410843c03103034403090062014115050041e80d040b84d00d5000c11801440c9000880f0780f60552000050040c54a042079403545a240030510075020030026501207415120040e00300e184d80300c0c158040324034900200e021606e4a6058000034100c1b400341081205060b1100c0403c001480103a400508030341c810400410781030700982c2c04500850803c400040e00325501d440309071003540803032400c80c0c103504440c000b945500b0060750038401410060326000e011206058018003031056501400d800c0c400d0200d03440c0d420881c16004a0407103400904940b406200a00c0c4c05040c0440c2030204074045941940d2140211000d242c503001d5004020f41c403000080340d20b0f140d040c001c0140050540d2095100d4414002195a24944e5007059410001c0150ba822104483c50704841003040a90341090040050207500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 440577625 1250 440576375 440576377
    0x12010b0f041e090f090b011d06012601090209271b0906070b0115020a03140706090b0702060a0e06090c0609060c0f031306020a02030d0827031b07030305 67
    0x41c0b82c05003610207010004070405001e0b4201c6a20851045041c01100c880c40002e5400004480344940b29514580e6215200380601c08010030447e03940050b40340c0050601d42c80303400c0c00d041a0404402c5100d100304a2111091004c2090b080101610b40004195150341050140d2a55003400100c2d0800c95002e802c805407003a00029088452803003050350400e08c0460703140221207800c100249207594503030540c03528108000c0248203007400c2c42060480c00700c043d800400d0034840d4a0741651580715400d001d40750b0000302c4e04540400d55400d55111b49580004040d140c06901844882c0c004007034600d00740c9180c009131007035102d1a920940101092008091001851050343c4008442e060344400300b07040800c2d107e00940004c0401c0b1309c10980740b080841c00c04001010070880120000306019101c401c01d0b07a54180e40b001c02074041e0300c51159000400c1c82000700c0b68010150303441074040e5801415404030260080d41c0c541c0c00c2d0307801c00200300b88111481200d0b45192103141e0003030091546180c80281803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 440578875 1250 440577625 440577629
    0x5160608060a03110102070909060c090b0f040e150409110a0503030711040c170109020d0501050603220c15050c0f0d050a0309030216090f05101404090c0509090312010b0f04 76
    0x8213181200c18100d40c2c1c02404502c2c041c0c02d101108100c03001603400c124000d032405210250209807443c001190664101080742d0403015200c4801d480c0c140f601075600c00704640184040c0501c44074014988055455010361401070780518a98030b50b602803641040300981d0140d0040c0d1080d881003215100140301e6404800904038100d40c002182c1d0602c1200760340e03100031048240c44110805c000450742d1078030743d0301a0080c2156101c0400090781c94000344586813206403030301c3c01044070300c20780e20710044290180d0903107003071017811903940492f03a0f600c4101c00001d1801c45d082c0130890103d81c1e06d80c200410007034100c3e0768014100414400c40e001d030002d4143d06c5910b8403c003c05460300c0d012401d0600170000d8183e001e007182040c80c4400d54a21440c030091021940001425061001113440d00c3d180c14210b80c182c410205c0300340000110b50b010040204011001102ea2800c8482e00261546d6410011441034014034042d607a50022200402102a416080044a03220034407901904070007500544003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 440580125 1250 440578875 440578883
    0x314010f02092b080a080901150b0909070905031207140c101b0b010608150406060f0c020f030307050105060a0905190e030d060303050a020d08310f05160608060a03 72
    0x1503140401403460b107190f20140250200000040b04410682e00021652003118020000c100c5600c000c1800c212104a61281211200c005d02000c0706501e003d000b001e400c100d550030300c4d1000c1c95468020078203103171a15103c0f4540b8440071a24405102d402d50702e030b8202c1e0b181c0c0e001800390a8507031000101005000440e0008014610f040421304041040810913030780e400080240d415a92030074000c020200c12a103c2d0a82c04000c0302d0320741d16090a0060a041d2003e0b038407450b030080c080d1001121017903070100084e82d008804100e003030a1601c090005160540c014000031805141441c06e000164486034001d12a080c50b000030495208100d081a4440070790380d5001280b44d41e03400701c0c0c50385140076000006410500d494800010590804001c05485296400703540c00404c0890041d1a140c1084505210850100c250000020030305000e0b41703108117902c500c888001c642611a614034001541c5c04587c50703444150845a40401c0b0701400300186501d1400d810245400300110308442250300c4010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 440581375 1250 440580125 440580169
    0x9040603061b05091c051603050106031217060f0301020715020703110d0f0f0504081e0105100b2d0f031905011d101802070b010602070803071106070b010314010f0209 73
    0x4201b10082c80103044e8026403d00c042106616414400c0c000c0c652848200da00805140d80a4a03d9000d1600e00c1107842a0a4201078036980d0b4500b800503400511490a6055508110300c0c00011840c15a8610805d0084401600c9520a24015080401126820703403154000444004600e030f104141e02600e2605140c031694a5054540075511401217820826031401180c02c2c0b0700c0e07100945040480c04440100003881180c80f42c1040c40d180e40300703034050102c030b1300d504000c40d040810700180c4030740c150201c0304928103030f00024100200d0f60360414041c01d15012800020b02585585074803202e07840e80c101d031030104043d5160507149420b0308290030029a0040301000001d8014140c3e0002d48001d041d83c2288044520100800c44002d40c03102c801124280382c0c240010070168800505030f801d480c0704400440c030380318160b103880b403c0c805481240d95200a04015001c0090030141d0218002c610030030b9105008044101c800d403c3d51081d040340071000348103020a2010b17540d03481c1615540301034481c2035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 440582625 1250 440581375 440581429
    0xc040e0a0b0a2402010f020309070302061c020a08010311030d120f0b030319021902030d20011118030d080610030902121c0804031e0509040603061b0509 67
    0x200e11050701c203500c509901601c3c800c1090325540d12200c850103000d083e6000700040100c261a04049000507601404c0d0f9500a12091005060020041c4507100048100c12000c05600140e40140c3c0d020640550000303189000410412642840030765100b2400c0b0b019015842c4080401032400c03843e41d481915031515940002d580b014158000070425030b0180540b607480c802403101c81c4810710004414401803280d000c40285501000101d00309996000f4007900b0f059a0350b903030460711042c0b501c0075000303025140d07800c841c040c003401d200e518846540002e11988401d1808204070912000d803544078000d4000b241551801035215509647c4094103c81001400c4c190000c12001454112402500700e040003504584c19800062224403003454142041030041450707804598180782610002d010401c524003400d50703400c007400d00c2000e10348030b4a099401c03d880f80000500360b40180e88107850060b0b072180c460b196800381c803a0740c0303184a2143c2001803804825401240c0420310302e05c5c141409a00c01440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 440583875 1250 440582625 440582629
    0x4060b12030304051c03021b010614060c0309010503040c090c090510030b150a121e05130302060406023115050c030d0c020307140f010c0e1807020f03070c09050c040e0a0b 75
    0x10f8588c4c91a079945240b048100f84e00209008001c107004840b501c2550059241040c0f4291040380c41301e40740d603c055810161048015265500301600445a290340d5070380114007940035100d00002e200c1c8033307a10660348914100910440c62643c0341d040f800c041c00d000d40030300345481c4d0449058141e04000d01c210b9031001d0a48084600d0000b010f007648400c1c0c1007136510780c100c64401d98460342049200c04100b00e2a20341c82a00700240c05800c030010003503004880001c020030855800f800458203031420394030400d0500d0144103d0703114180100034050425144c103000301c00e00a0a101ca01e03040605020740340c6800740c0200707039a034000c4000d0350400ba6118402000d4051003802560f00c400d60102e440082111858400798035407208403080d82a9610340501c03251924072840c103580e080d401c09412448894841001140300550090201081d44112840495010400c100130020103000c0c601c8000b0250521440c9801e07980301414000e010306050000f8000c030040314601d070b5003110100d20001584040000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 440585125 1250 440583875 440583877
    0xa02090415291c030516080a1206170307023307032c04050603010b06031801050606030403050406111603391413020304060b12030304051c0302 63
    0xc100d050381030420301c11034842030b0401c80412650101800d0041c09224910500450310700702d020300414512032448080c0440e028500400b061003146282c40000c0025869000641c0c0c008114640003840c400c6001950851a10170103029080704081d42900c240c0c0644210743e40d01454402070f00c1072118040d407a40104e00d0880740402900d603104211441d031650381c0c0034991500040340a9021070200c00a910840340000c00d0703145d03184410300074801c1242002c01400001e10004040940541d600c3d50074000c640d03903500c007551280d00e4250407941e80303c3e41e44d803010b13003540c0c0c02416031405840c0a00c1404002a040025642960950b1502000152030900a149002444000003403221a07120001c000d20030282034850780100e5007001804060300c100f200b0250440040c04c06803000001541c240b1041d520280c448035444001020041c00c0c184040308a8220f0340190703021910640d0b00c032085116030a0810108881c010315400ae10b06602c3c0c19121140c07928a2072014240408110b9800c40c81c55010b58 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 440586375 1250 440585125 440585153
    0xa0f0b130905011d0a0b030d0309030c300c0b0403030b0d0c030602030106031a0f01050c0106051809011103041509170c15090c0a0302060f04080f07090f0e0a020904 72
    0x103405010b256510300083c50001400b26404805440c80f0340000d00d206140d0084951600e00a0000c0642c0010303064118018103410354100e0401500310120310200c0c00c0c424050307540340030095281c101d84940301c2c024401c0032601520350b001c2c8080343d0101404909a0341205501940605002c9440001d0100180c0355a03240c100003000711190304030120601403284c0c050341c1600c0564404004403406030002030508506401100d03480100c480c0b0540c0a035100718043d1608136011400402c61507150340c0000d50b044005084401c002500104002010009004039a130b4000ba464030b1b10301e0340c10319480d00b0015010086440020703d071224880340c01c0010940401c041004994001030301d4100c4a0a00d944581d00780417241111170900340450b0295102085410007100d00608941306245154203015194200704011204000c0034800007a02101c02d110f07490240c03200318013600519003006803050850f0600240032504078038103180c5035000c01c0009290f6004580440307042455680310700e8000c1d80707440f8030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 440587625 1250 440586375 440586389
    0x80103110f0901180b0a0503030712030e1213060e01140a050714030309061810050910060308041a040312030e0c3006041e03090b0711040b0a0f0b13 65
    0xc0c0c40009413000100c1040704140210f48030134004240b1500030031942102d180076032a4117070400c212201c00100c01c0710b19044810a982008a002c4012a8074241080d1a035511082131800c00607210302501007244940340135180ca810702404445200000070102c52444a4200030703290000340d011000c50080003903540c03059204e400003c02c01d00b2910596140c0c0c000740d0310000340d4400d141c00301350b0300003100080d14060170f05500180400d24844040001404000e03021003501e008000c2c0701c04151419014100195010748000c2c2c3c0e0321031400341c0b50480341e00a91416114503030148000d0001904106034170142c50468a070126004607880c054900380342011340c0c5aa0711a8514800c1c81d0000080428403025111a101c40f02c11012081980e0381c0f9158202c0f4001e141c44010015080f000c40c400d84c50703ca44038028506900907546030200315409501141082e2083d00030100721840d603161a01540510050039203030190003524140c2c40051040c141d0060401440010800010500e14150480010842 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 440588875 1250 440587625 440587639
    0x12020307150902090702011a06071419030f030501181a180a0b060c0d230f04140f0a030305180904060b040c0906080f130506090f07060906080103110f 66
    0x75111000000301080c0004902070502140082c00e07050040c0b1420205407450f9a0264001d003200042001740c0e441300500315820710044440072115141000f026a005c0e1002000c50111640e0342030140c844c01d0004400c50406040000611042c51006920040300544070b41c0442e6440d40210b40c88000d0742c1c010403858000d02c412000030203126040120a0250f940201c0401480c000f4205100e8140300d02002001c4aa0024040b10601440740340100c03445810041c000241c1d602c4007441030200c0e070140e02620701e10b03900450140070040070359440d042c111004850400c01d039201d4001181100d210391102130140030003c40c00100d4040301d1654182c800400500030310051400345041801000000728441c0140d10304820310080e2405030b0141016a012611032075082da0b101064210a14001840e80c0d07010f000320010000003031410403103540540c00c4200030f0300c45140a154142e140c414036a0002080200100007080401c0e0002c0029042d01c2d0441c064800d0f03440903901040c40c43d0b030303c0d120058002003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 440590125 1250 440588875 440588903
    0xf050d0905070e070311030402090a11030907030c0b1c0b04180f0b010e040b04110d0b010303030c0e01021605060702031509030d1506081909020406060f030e0d08010312020307 77
    0x808100c82e81500c0403105403c21a48403450202c04503286c442038081c1303248042000c50090714014038000c3e40400070090209245003450b211080681041d06c10f2200f80d4010441401008807100300300c0301800c0c3c00c0f002d4a04000d40d0709a0440c151020652090295a451803001440d407125040301207442c0034003403c000d07075849500e00035941c0040036805903002c0d405030002080c0042100030481c05180c1000000c0016107894440001c00c194500b00d10b503001d118940840005409844018000c50094600240803504404042c02c0e01f110000e02c54115000717207900107452071004080a0503140180e8050362038426074400f10340b8100040500c030b50540c610320104601a0400001010003e0030703144140b1542c06132208080348507000b0302443c00170440000000e00480329200e50f040702c0301441d60340810928010b801290032581d40303400074000101170362011545150035000340030100c0301e603000034050f81300c01c0300c4001d106d00d030180070041608902c4c81805200f103101b041503411941c3c1111030a04020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 440591375 1250 440590125 440590133
    0xf1e050c06010e0402030c12190b1905060303031303050d09050609070b0a020c01031a0a030308090c091b0304020102120c0106050406080a0b010311040e030301080d080906160f050d09 80
    0xd008100103050600c40c1c1800070400e4101c40c01454000d0341c3c0a801807240d20a0a810064070b088081031200c41d9104509060301d9054000059a04041c05204040028201a00740a5548107910000000d5a082ca401e1000f00d031030000841341e01c51a0000d400f24000114501180c41e881000c40e01140790f82000c00c443c0922001040d45405038000904850140765a6662a162400f4071004500903030440c9200103a076500031f81203010251403554100514400001c000f6031608840e40040d00000c042c07108000c429041040304c80c95065044858a04518041120401d40c0c1d003410401c10128401002280c21039000b00200407220582c00c6c0d03e0b03900d44040e183c94600910003403042610403030415800044210011403035489841d0002000c1d5040e0b82142c4464a4007414075024a0708103641da410440c0741d030401d00c099406072100002400c3d079040900c60050000310064600e22164000c281441808548803400c1c2060042904040f400244014410390b0306000c1e044803c001c541c1070a01d80e50401c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 440592625 1250 440591375 440591377
    0x30f010509010b12120706020f0409020c070602060703061a07020316080f0d03091a1b16021201020405030d030b0402120414070e090d030f02130b130e060d02010f1e05 73
    0x1101e41940d070404c4c0040d0381d4141d0340d550390030680d1140d0309040030000070010a000e90010301008040e4564545410fa48601020499014090071945a0082e4909000099041c0400c5030468036a18050042034140065840c00b840301c00040303422407400040d00411901c0511001001140003a290112181d8031038070310341c8030310207c42510340314080c240000141a000b440382f4219603400c040180e5850149001002410740064500c040c12103013541c603030064540400092034400d109c044c007490003400900c140301010020030902da5544c0d0041c0424007103510000340059a03000780d4036003c00c1a02c0d090010800034483c800c0452400d044020801c41804840c0c0484240404000110b500c415501e00002c9100103050700c5070304503a0444080e4076102d61080e00007410720011440300601c1c00d07502c280a01d103540c185500a041070b9102191f609843d501c203200303180040068188804003441c015000800b000040c9100a040c0010780000c1c0d4401e61059010040e89110103800328004869440d000d042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 440593875 1250 440592625 440592641
    0x204150807030c060215070e030703020909030d0e03040b03071d031606020c010f080711030418090c0801090b0403080a0f090b060a050d0f060504032d03050606070209040809030f01050901 82
    0x1605910355000105070344001480344030010030301011101522464030071903a24500c848d600d41d040c440c0c84404009a0380b801042d0703009000d014000e694914080c660030060712072180598170340381c009000801c1324140c081c0031641d00110524004912081100c03880041009201e00c05815204948420805481080000050320500d808070340e4900086401103a00b07d5004101000040d6000c001c2110743d8001d40c4003440c040c0e0311000340e0b0304003911403510308140308025400c14400c5407145680b00501c004500110060106c10000f8409408140c0303d030310740ba40740070708020b003003250140010316803002c01c0e03000030b81606a4220500103403540e0b051040140c0310030381e0320900c208150180002d003407800b0803044d11019408000710718001190307280d8800900c1d000784150140301c003205807525040803a040310015000c91846041c0c20800d4540000c1c01c41c4c200608044c0144000c00c0040c016a90f0040001d41c01a0b010580d16a074403c54404641414401742c0482603039805c040500100080641007100303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 440595125 1250 440593875 440593883
    0x6141302070215090102010915060e2508060d0506040605061201060501140f1303050706120c02031e1620091303051813020d0606030b100c020415080703 67
    0x2009090119080100e00c20220000d6000110708521820070685002802909a050000149800301b50b1900e0300b50f81c47c1c49a807455900c0d41c41c002804401508803040340c0203d040c04a024481c540071820018102500c0340d01024802640000b54155480008200c50f003507202c0e0550310141403c0c902139000c3e041c243d071007600c180d0795000301501c440702c1407007103400701c84050b5942c0c0c0d00c89414121240b900d43c01200c100e15030f0301c002c101102e0350703c00215a02000350720450061420910b0030400030800750105980c064650b08048980d648954008140d90140c0184e00a0001016101c81d0203000b9100c0c124200100c007054511440a00041e9000024298051107072018282c0b031803001c2040041c4219200045000390380c0000003c2889180507003400401080b41f4496091080c00181c000994500c42c11101ea800060040c01000f070b60040310b0051215081c140320207103141d0001601e0b032522110200c10069612203100075590703140c201410300108110840240c40e241e0b200c445d07e6516070301080d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 440596375 1250 440595125 440595139
    0x61e06080c12030a0918090204020318060a0504330e0d030f020c0706110c0301060e090c090403050a1112031005011103040b0304062a0203180a030f080307120614 71
    0x40d107410100403540d031404c4903683c0517202420001502d0030180d140c42880f8240f651034900a0050f00ca51004502070b00c0302080b490341003c01410303458a0000000d003240c0700c090030700080c00005120001d55640302c4455a100c1480800780041e454024010903d05004050800c6803410400c5004141034000c0a040d58051000b4103e075180c90088c0e20a00c50030030401e5001c0c0000b003110600c80e1081107611030441060310104c03100b40e80000d003501d4440d0410301e00780c49a003080c8481d02400b0030020082260540f2601e0303452820780c401500f1030040382c1944080c4008135120424810301070014171039200c0d4813100c1948906140b07a07409000e441c140101c1c2d02140c01255580005070001094a00300c4212074141d42c5996160b43d2102e02400d206141d0141e00d07001448004200b07091844a000194043d40c0150340b25903452005014060b00e0310035940c0103640e00f00c020300200341400074419149400583c850703903030f48490038111035040301d506201c51348030315040c0c0220784e0301c0e414a140380400b68122110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 440597625 1250 440596375 440596399
    0x80c1e03102f090607030504080106080105070905091e1e090a0302120c191a0406090c060306060c0b1008030705010e010f0b060a0305090c15030906070804050a061e06080c 75
    0x1070541c00710310b100e0700d103100c800070700088005191100c010b00381d00d40700f4039003c0d00f016550005942500e5294000d4096651901c0410011543c06080701c070050004a03038410442c2402c03555102002e04580c1d080c000786000d840025030040d049242100c49600300074a03000c440c50500380540c0c482c0705061040340103004841e400c0c81003031596803c0e180071441c6500030300042c52070070606141044994034112180300205180c00a59039840010b64440c41c0a1240440d03460701c01e140c0000100290342280080c546031030820700101c0c1c0d0000c10303107a40d980e20611402081d00d4540c100380140c2032692044200d4400001e200c1c080240641000d07209002d40002480031404402e4250140c0e20f00300c654a4010405202e036814251003500101d81102100081d40c84011a030300100b50030400c0304010300d46410780041130052240b010001c1581c0403220789058000703030800b9528039403202d01c1c1a0740500303516218049888504203680042000b65654501006803070b0750381541c90703150b82c1c4000603d03104038804000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 440598875 1250 440597625 440597681
    0x1609080d1e02060702070b0705070b040603150f06051b07090908120907060509062803020c150402090105131e090201170103020a06050d0b0301090c030210030204080c1e0310 76
    0x1e40f9016612640141020508040300092650018881070316144a0424006a10181440100043c0206690100d4042d00c507901ca0104c01e0040c0d071041d022089140c7c410403420354800141d4000c40d007919403004420114105c10782c54210143c0008801c1440c040c1200100104140100b5131003502c134005001c1641c581c034540b6160712075403084c9004220100303c0455a45403040c02480340c0711310f0085451032070010031201b6810341c0303c018180010a40c00599551001d004121018560304004288852482d0a174040383e400d22052c8503450045000803003004110318181c000700c009281d04542041c06d101024624000f90032010016404548041e43d000c00348444a55058140d81c1c0152402e80d071149408022141580803464001c9816a0746c1e043d11115a400c1c003660071660302419140341c0c2c003819030040103055116188000141441080104088440800c0c1c28010403000c4a075040b12b00d000080d055100d03001c803c54613501d4050380e007500d890441294008000d480780480310f00e4a68144050f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 440600125 1250 440598875 440598883
    0x2030d0503011d04020a05040c0315060e042a0e01020a17071709150a0201091a15090702070302061c0509010c0f03180b040807081216050708031609080d1e02 69
    0x10041c0d000080b06c11309220300e091a80095030581410b1400140300082e482d401035004143d0340000380001c5006150742c2041c0b0f0326004410250f00607425486605642c2d0140250400708905810144120080081c2d00c90703009015015074240c001d04400100c54061300b10303080b26441440c084038583c481e031b010391500759010801e032a00c424001d4803101e680345c07400ca0740411540016841500315921440003c000032084034245015115460001c0000d05100d076019406110515415000f0f6104004028666034001400c10881c0d4041e2142c580c0e0343e0401000c04802d42d44a51201605404e044c01cac001040c5055000500244090340c072440b8480e018070080701907035482c014101c40701c00a411248041401007a07000e810a2080880341c6c944907187d550405039403c1409503c00c140410020003601031440540071000751028070301685001c20300d684041c03060102500f80b090103180101e520b181207010f0b44401026011800c1110890b4008100061080d010048112080315106000780902c41c0001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 440601375 1250 440600125 440600131
    0xb0a230307080f0c1b031801020111030a090302031e0d050a020301050a051203070b070c0308010f0f090c030603020406080d03060f050907080408071b0e06030d0818010902030d0503011d 81
    0x340d2404003d0301c80700c01c28030304540003030202c08043c80f0801526070310510002e4900018401d1802441d00c891214002d141c00b000e03000c1c0c103241503904107141207070071404180880e50300180301c1c813001800f048a410128954000c000d85007a075000700d06030100e0422014000750000205290041c4420354502c20100c007070740020720400350450034805080c4014589100e007000c1045c03440302160308086d05611441c050b40d0050b03610702c000c9110920900d050580c0100818098a0036407880c103040c501d0550902d480844c1d5224031003070740e07640d002c19540c181c3c40794004d1001107070024024402584c03181480e64484c01c0c95030086010919000c00080d000c080001c0c64021030324001e1594004d5500c21a045e070b004c0b031004000311400035040080100248035160b9a188000000d0000290300d0704148044504882c0075000a1080d07004070758100c800342c2c1c45103c8540c801c807100c014803494850700710214050408010000d50501640b41540021580038000c0c504880d244001c2d018007007046c20b0400d154100035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 440602625 1250 440601375 440601377
    0xf010e07020d0f0e12100213080a0f0201120e0601030b0907140f01050a1211041d040506061905060711011e0e0906130903020f430b0a230307 62
    0x40d140c10003003d8051110a00b10304d102821501842c40304000150a0009044203000c2060f03011441182401300c205003240504103040062880c4100ca864064004190890090400c41d200426400c0f0f01c030160049070791100c00c0401c540301541c5a05e48801c080c0310031104c080ba40d00c500080041e00c081400c884540c1408080c003041c0144500400445031940890000010b21485904801030f55101d032007800f0200540703010490b160b42c01c01c84030b103848504070641001c02c14452800d110100d040840c4c030b80e4100c8822100340c810300040d02d58241c0c50a0441e80310a500c50f00200e882000e1190005034003a2040c0c0036039504d0903502c405001e0842c00c00c2c14103d0030000a41c20705484241d401d20a1180760044001015856509000b42a440944403204003c0380140c001c4241001446010484e20b40a2042103030420040c20040100128440f0b442120b03604500d2040b18030b003181084014080060001c0605140d039504207094003410154281c20050078610f038400702000c00070229403d4074020703a00d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 440603875 1250 440602625 440602637
    0x50f07030911060d021204060c020c2d040b030d080a060503030a0906030b0d080a0509040b041e020d0f020c060103031106041109061207091a0406030201080c070f0b0f010e07020d 78
    0x101909010f0b15800c680120041581e08112000c0400208541980f00c0c0b440303260045101d1074203190080c01c0c403a090020074060b480d00000e402007001c40e1101040c0307044e180046250000c080c20001400340505c42080342e098042d1400ca00d4096070b103c8603e41c42080c8115050000ca940d0f0030502d60f40384500114480000e10011060101503c240c1103e12103120060800c5008442c81e16654203607030000c1c0003000481c60001e14032a9038100781c0a05035181e801240c04000071a00d4040700160020300b06074844030107600244034826011294854031400c0e4a0304030440d10382a40300b4803d69a242c0a000c1540480d501582085000d540025018416035001581c02c1c081501c0e441440031040f00649003542c00050480032203109041084180d0040c0061031700412005859844800c94689103503e0b68003031401c00c4018000b50760482c40141c0c010301000380c1150303640c1440c208003a01401c1f40c1c0000f000c007009001072007100c2080c9410307030341a10003488a8490546400700140c0c0c0d13851003081c0e03000200362 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 440605125 1250 440603875 440603903
    0x30a020117130506010b0d0c020c060f0a200705090c03060307050d02130e01050114030109080a08060a0306110a170f01060f020f330106210e10050f070309 68
    0x30200c2034650b00031241140c001c03038041880da14982001026080000301050102d22805204041d0150002d26051170000d0f2281c003606e9400300d452880b40724a219203410000440300c0d413240c0300d945101d1000710740402511600c801740c90490740740c0c5180d1080c503121b2a2000c01040381c01c01c8200485c1d004140050007801c0051401c0f0500441d1202010141c0e88540c40c80b0303050000b140f0901810b515044094000070716581409544a50303034920303040b26402a0315000d00300c00050801d6045a00c94801801c04941d66075aa00c001821140b1980008203940c0c10170034080034241440d07001d850840481d4940d210100d0311035501640780c50044400003504070150004200041c02001340c4c0c1090f100e248181c070444031984030500c2c030f0100f0880c600400b55030388005840e00000032070143d981d4100c2d500c024440035450031100800750072651205100300c8048142480c40015a5442004071201c1c40096481100007000b103080240021100010104614000104020311038440c500489034000c0c02281400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 440606375 1250 440605125 440605157
    0xf081c0e040b0f040507030905120c12030a09330b0607020906030102090a0e011404020c0618030405040e011d03090a140a031406040c1d150d080301180b030a0201 71
    0x20548200b100c3d00012511210182902d85000e900e200c6c0e80551800325002806103420392501380702003510644032805210781c602e042004104460142110501c00343c50b503c03485101d80050900160003007281d20b21242041c140d440100c40c0c001f1040344000c51481020001d400802591080d011090307020ba003c21143e40113141000c07a5035040080503000600b01030065020943c410000e402400f070f0204044010071020a6240d10369200c01010307a010b500703040c140d403200c55407080c0281c84200001001d203588012400b00304151801000002d2080c04052185054240204034503c118410440c0140f403e2003d001f000048500304040134011600182c64805502050307586196810f0b0b010075207440010202d01403000040b0115082c801400503030a0034a0f180070208600da100e0242032103070354088580c52480a0515031300c200711420b6a02036402642c00103080e02c0c08820700408070213001c0004609000e034240010301c0c820b4913010400000d2104410141d0b18825002e00a00155108008203001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 440607625 1250 440606375 440606381
    0x30c140d05130209090f100c080601230a0906020613020114071b030c05010810030b0c070321020405030708070e0a0930120513030302030c0c070f081c0e04 68
    0x160000d005203080b030039580c0041ca080c4070a5410180c00d03801007000c0450b4000a20009594659910302004406014400540a410010311450601484021580721404560060384224038840000741ea201c1c82d000307014049a00c1e0b4000d402c014401c000000e1040c49011000c0c15400ba01610740c28100102e83d42080c10b0713540001021244160072481c41c035049180c500100c00650b200c1c0c6650038203942010001410300d040100300d041e010071800400c20114010415a0b07801034152101140c0e160043c1c1810794840da4080d04c8107050203003180d180c598800c02c50b0b000d0003d88800710192108035a841040d10740e00c02c518007030001d43d07026140122f00151519071285851610803002000c4003120801840010780c41100903140341500e04c070040842c82d600001351040e03c3c942440030412350500f80304280058482440007002e0641c0000400d2100c2581e0081d01c0b540d0244c581118610341c1c0700c40c01820300c45402c0c8070320640c0c3d200f034000800c00840a50459100c50700c1c281e50b0019840c400c01d08000207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 440608875 1250 440607625 440607631
    0x300d0905220507200102040303020d08010b040e1806090c1c17090a0b0c0105010303031515141306090e01080106150e04060909031d03011802060d0e0604050706030c140d05 75
    0x1803204914034071100400303c4140300e081504c00000141c48603d1402c001e070806113010748680030421031a0050041001440c280c80503141540d8030030100750b40d2000000420807003105215514401d900c10098100d10020b241030480b034003a903805c0880001400c0144450504100003441000c4112900ca03c010181028005000c4005c180c06801a03440d43d5446c02035101e25501c0209075191801172003410b405010b403000d01c038040e80619140c40d141c0301203000c0c01e40111450318108180e4141c2d24100c01c0510b010f0320008961074a6043c02c80f070f51000d000d4848152482000c0030b0100c01400026403071810b02c00d00048038034000f5068006180304804403050011010040d074015501d59000c43c847c4200c8c8100c84030507200f030329400509400c02c070840c503042025440c142c0c400e0f030404100b142a1601e00154920555043da841900d4055880420014200d41c184501841c41404200800d01200240c040211861078504003c8070002c0c01d811240714001101481102404020f5489903000d5640941d80c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 440610125 1250 440608875 440608877
    0x20a0e010f022503021008070f0212091909110405030f0c090601050a0c0510020304140c21070306020f19031401030b0408090a0611070906030b06300d0905220507 71
    0x190f042e81320350000f4800071121800300001581d8200300b041c0c00e1f40040c21090003460b44d0006160003640700c0fa1440440c45440031040c0202d4519104e4208040c15003000c00140082031424850103005070f09108041d0050700c14039100344149005104007900200b4141503545000c0c000014643d03840c00117481d180d106122200420000d40307034000c0881c80c00d101001da01c10303400c100980d40741042c0c1091564000b203002c040170785802c0002100400d81d034001e008281c149194500038581d00414460760b080000607030016154900002c1d01010306101c0400910112404106e00104801e040038200d08403005900f070140c0c1d007480c813801031011529488641347d1003889000c3c070381c1c074024604002c1741000c5856070190380480c01c03051200d12590400d015580107000007030800c00c02c1760300d59165540c0c0303140c1c09401c0c0390080103160019480c1c81624030303006403103c03001021000c0144c040781c4456a1841072255035800240c0030700020680b883c2a0010032048030391480381005042d41c1e01066402490041c1c5500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 440611375 1250 440610125 440610193
    0x21c09020d200f0603070f030e0307350a2a05011508063405090607030c050607111c20010203010305010b190605090a1701020a0e010f02 60
    0x4000ba40a0b150769101080155200303607181c0011040c4007040c090b490340544a01c0e0103004005170b6039400038400c00d525005203000301d062407070441440c1c00d5100c0e0360340242c0621502c0c503242c1c00140b8071412a0383d00e410400c6500c01c400c4a040510985400b07548071180003d0100b4086c1c0742c685802e00c8003402c0c2e402c04070164100f002d071144c2d074850848a03071460051114011000421039030700140442030307024002040011064866001a5500c8990404d401040c41d003203104121a2501c40c81c20307101c80c982e02a0500360748000368200035051314007541c0100e8091040c0d0000401d014450780c0404000751810005042c10044540080c1c1c040ca01d92032050b04019054004c2c50030400136030b6603060381620b41c800041e529415410403d0035107928101c9140103400076059000e581c032510003814211030541c607282d82ca4484000001e482c46260364080c0300e050081c80b807901c1000318194000c3c5401d94107521480f201c03140c1a001074400e1030b84900c1c0900542c020302c601c0940c422819000103c42e230207101c1c0c14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 440612625 1250 440611375 440611399
    0x40506180f041d06090d1b0614070207080d0201090c0e130501051311030a08120702030f0d14060102150c0c0102120a05160c200102100c05031603021c0902 68
    0x1040465401158010010b862546000f00414062240d550000c401c41d002d0f2040000c1b000001d01030414812000100300850b1918606002050380700158039140b0708055003a900384a6402503a41065020742000b5000b402c08869030907005105282d8002ea0215460035030601e0841d10302e40039a0300a00c3e03aa41307202204507450005d4002c1c032910b481156038090800400e903440c1000f040001c89030015034081d51000704410045003600e4282c410012880014200707542c2c0312a0200d065000b09400740990b80b001080701c00000c805500255104040e188940c00190b41d403000490b0b036040c0703100810703096a42c40d5000c120b802840e40000c16220801d500003500d000c00c0002c4090860a044410b000c51380d607284140007500c4001000101856158a0202c0c00c2e5242d0b51907440105069401c0304c0c0041100f92181d40c0d4a9001380009007401000342410855020b510f90b010301a40c0c0100c440c0582e2150740c3d00c4103154a400b91007039810408d0900c007050115180544118000c0c000140b007680d0200c444042c2d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 440613875 1250 440612625 440612629
    0xe120a0c09020a0e0a08190302160b1c021602040b041524110d0509040e0303090f0c01020a050a0f051501030f060c0e0112050c0c07030605010f0b040506180f 69
    0x20300c004008111005a50300c0c24a14024660010015000c1c4500c00c20007081008082c0001d25480721246040703040c60720780251406a190075901d2041030002e894100001070f001c0d24880103031620f801802007100f03e2582c405210700880c803c4841d800304a800745c0170b5440140c149903005c41e510003405400001c41c802c00c1883d155880c009544200906188c8144207100514100d0400c4404030403802c11500d00a000b010300c544955480c4015420814081036929081d03032203801c5900d04011a406681d40c0c2e0404015240e143e2040c81c000f003043d40b0a0020703049140d4800108034507055048409058020626920f52540d00c603440390548684c170500c00c140d84e4034a100d2425500940c0f04210301c0580082074580301c03055a003551b1202042c898448610780e0280d8000790300110071345a07850006002d90340c8150100c880c0c001c07204a08400c0c441d0303000100c2045100e60209050342c2c80c0c0d010200e9400e59800801c0311500c6140940741d003148051013800007440d2400303584030355004001c015001420210340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 440615125 1250 440613875 440613893
    0xd1e110f011a1302040302130b040204090204090f0e06060307030b0405120a0c0311030901050f070f0501110c06090604020102070303110c0d0804320607030c0206070b1f060e120a 78
    0x20484a10b49254039002600e01d00041200d61030f900f044010b40c140341c07654002400360650070b504411595103520881c40650384650480f400703840c600b2011511039851300080c800030816546480d024500e042d01d0311000171400201144600002401032501a0a607543c1071610030016000302c0d154170691007803070b510600840c003414440f42983c0c0e802000044906008100c103441000a21094008210f00512660311500f2030f2001160543c48943d100940c0c80d00d024109600c0102070120b501e003081003035250142c0300003801a000f0702012103280340c443c580c2140c1c40395020ba4001780075920900701040003a01440f07050000309a030780f0646803061042d802190101c03088410450b08040001001d0140400c00c94400c81051401da115209403003128182e59500200f01c0040c80c410040464001c0070140b003904010041c0707a02602003030b101c8155107800040c08500343d40040806c44800102d144014942c1200002c96450b507a9001d450100d50050004c00410342da81c0101602a416039400030503500f0b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 440616375 1250 440615125 440615141
    0x90904030f0807030c080106110c0a0b0306101115060a080d0306090e010203041515050a0803030405070b0a270b0c0c10050c032a0d02030406020d1e110f01 68
    0x915480303060070340290000c0541000404400905140200d820005a40324410906482e0f0798240300300340f0301503848024a0b1840e8441c4503648103940c1d500c0401c00b01b9031000910700031101551080ca00c45c2250606032070051180c08455056030019030005d070555076080040307800c084c1c040c088890740c5d0744440d480c80c140b0320b1034901940480e440d00000c10100d0764070b00c55201140c110b0402141581000e40c1c5044a4088000344c0000d11510349607200c5c0300d8081c0c944c1030001450000d003c004127964a1007926242d03081160b00361360761700500000140b44480001142d502c01e44960700c1044120f0300980210500c0c40340f80310104c0c0340c802c0007404200000b00d01c0c000c0c05500d000500070b0100c00c0441080014071641028460708012080c04411000c0b100081a10800d4a0400c001b40e81d40e82607580e20140040340388030701031080c480c0401c2d458409030040000c105540386c0d5030071390700403003143c1e4810380b00802c40f1103040701c208501c0b49031500540d104070064480c0161100a40d078421032480d16039402d65131a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 440617625 1250 440616375 440616377
    0x408014b05042d020a2c0a0b040f0902090901091527030c1209050a0e0603010f02040308131d0103030318050303090c01020c0d05030a0c0302030d0203010906090b0a050609060703020309090403 84
    0x4201c40c3c01c00c0d80b520943c2c03107005203000e000300340e6246110424244644e0b085003958003148600000f203580b6007481d030424407a040c40035100b0007811341004d4119020b4561800180d020300070400119030210418083c5110441d0400600021040000d000034010420a404021507111500c96030404a54000d48104403502a540d96034000c0c2c440d04000c400d0025240c582414044070140c200300640310030742c1c600308a51a0400c0c1c0c005076a200d1004ca0f015040c41203140d08a540f00241c0441041208000741c00c80201c408150000303d9100c1c10480d68048003503504108031944000100b0000744660403040c2c41103480e81b901c420740100c03640d58034650f400940d20000c454002c0a0100e00c1543c0c10000f40c104041d040740c0b10081030f10f0a4582545a10230b881481c010044048104414903000304125110a402e60900310f641c0d40e500c0c03520f1b80081125020f440042070a1a04000b414900300c0382403029500700900081c0b4082000f02000741c2580405022019408103000c0500725a8a10014134400c80c00303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 440618875 1250 440617625 440617703
    0x20906040b030a0e06010509160c0803100e09012702013f0b1003090302030c031c180506061c0c09020307021e0712080408014b0504 58
    0x1910000c000e641c0700d100d001040c0d6121100400a598403508d00b1504119000c070f0200402400400803640071245440203000441d000041c00008243c1c03403004021598070850401094880090710360a0b1120103c4046050190010703151a0741040106881c100348141803a21a5a0b400010345120803101e4a04041d1800b110b1082c03a0070078620003510a00c141e00c0103080201d044410700260496140b501c1e0382c010156207050541c00c01d8001c104444e503200d202e4040340e0b100d92101c080b509515044002c000c82c42810800300b580502d101e44803041d800b990140c05804140d9580041c04003e10101300040031130100b91802d44080f800381031842c0c015010b400320169491616610180c80e140010101600e000a0301550742440701c0081464425280300c241c1210303d003010760801707800d03038020351f0481c10b669440d00f0b403c811902111007151480500002080c031a440c0700030000d09200d200d0a65608502c007000d03652407a00c1c2a964000c5504c2403003a8204136444d8029208a16190845102c0b146000e82c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 440620125 1250 440618875 440618881
    0x6011a2503030b030c0406050105190c02030a0c0519060816090b0c01050f071b08160b0f04021002060c1213050d1214070507030809070e15150a02070315020906040b03 73
    0x1400d002916030172900b07032821f0000f18544000200740f80f041d51138110141c500741000c4040030b40300d0302d81c400071030f40c00404441000e45142000c415080d418071a16200306090501500c082c1d01c06803008044501c1ea4440e1040e81c4d6a511740c0d400303900c2c0310a030804100080f000020034040150780180a001d008000000b5441c9016140d00750121005004801072003840c84201003000c2a12a4240072075501c1703407010b44c4401903508020a4001c5640d0010500c0000382d040010340c048002e007240c841e600840303008031518079010059031120425142900d09510030045440d00000300c020340c64008540f51000990340440b5251070b030500300c0451188001a00088010700e00b00ca07513018070810305810429160450801d800058a00c1c031645400074148590100003420741242448504020216409400300c03d1510062410b42005001c98151003944618240042c80521000f0783d0056030340b980050803020b0860700e0703070446c481d099000c0d4031440343c003041811002c0d182c0c0d0010304010b0001d6080c00b900d0382 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 440621375 1250 440620125 440620129
    0x92214010e0402030703022715030c041a010e030a020d030201050118020f04210506010b030105130603110108041713030210030b01120f020f030103050c01020d0206011a2503030b 78
    0x180180d000700d411a5280040c4070243ea00882c020b422254121241c204840f00c41440910700c6014014420f402c0514000b0044081001d1000300c0718054200c0a0340c0c2501c00725801c0000703c0e00780040d0807100400200c42001a5406264071400e1b00400a04581e03001415600144000201d40021030050351103600420401d4403094114485200100c41503040802c81c00e5501c0c442d0080341300c0ca81d5101c801801c000d41000c00c0c00038010501d608031055580d15a1144480e886650081c402c00d400784400c10101c80e150303080e52007000250b960000750409402024401160707a210003030400d80d501030141c0e0700e071509a40d1686c01803102840c5922072190035332450041118103248503103414141070500918169036a4400b5400d0002c1055000c00500301c100d01180344001d01403401694940c41e03001001006102d00011900d04810090b803c403180d800311000c00326183c21080c4280f010310b2403007158200c0901440c13006069040100c1c080340080000148968007001d02c90303101034001c02da9400b0110554 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 440622625 1250 440621375 440621411
    0x190824042a08070c03080c0a110f06190207051921090e060105030c0a1d04020403050a0c270f022a06091c050906090307031401050a060513020922 64
    0x120035810041041c0400d500c0c0600b2591000f441c41e00440c0300090ba0401d014061162270b002c0c0c030320b0001151003040d0072542c0681d80300801e0b900104225078258100d0030b407007030500071074030040e51200190520040b01c2d018040902c02220b8121011aa07400042c1103407013101e400032001801580d241c4819603d070404607182500040c014a0422008204005800e42036504807040d400b01403420302103902085440040c95459848681e81c0140001000402d2113070014021003518021410000c0e01d42c6d07101d6000410108010005a850040044c2c0011542d140c2e440030503a074814a8001d0720b001800c040010024080c2d24104034a024408040c100400c800c00030390340d02c82030242c024800094143d07820000401b88080003c00c201c00001e071310301c0f5625494155403115a01030115079000f901c81c46c1c23202c41403c441c2d6282245618042c000b0700c446079180105411640c000c0c0141c1d1144c07001d07015800c0617501c6a5102500f280c120b603a9980ba00c0c1c0c0c0d200b00c40c0c0050074020300008a006000c4058070784 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 440623875 1250 440622625 440622631
    0x108271b010c0305040302010e0a0513021218070608150405010303120c08101e0b0f07031803080f030c07050a0302030c01060603060e0109200f190824042a08 69
    0x42000d00b021810009030400e0891301034030740900380300c01d000c003458001036142d1a9a412654003d84000201091060640c0160019050007418a0219a02c83c031101400e6215070987c49040c2d0302c10303c010844c003801846102e8001000480240ba4851340ca804501a0740c000e03070049000456242c00300200c14114490012034039400e2070407080a082060191000d08610700a20020310f1120481c903003541d2103a00300000070002c000416407220425101e8100513023010100b038010a98007420316014601c0121074100362940720b0301207400c03c200410004401c1c1c2008203001d4911400300544004140c08008140115110307600842c0d8480c0480317002c1d42035901c282d016405250800b1024007640300550f80d0981500c000c00ca00250710100b0541d80715400c04e071001c1a0025000000d901d00c0e10907003050080c00300303840160466288014031b40702260f02240441c0c0007400e8121400d000c014a003940c0c1c80c2d6045504008002050402d034000c0d075582e00d00c02800c9001b8034611a46121105d482e001041298 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 440625125 1250 440623875 440623877
    0x108010608040c0504050613050a060303090e04050d12090f12110102042603071a01091b0807030b131a0f03010903050304110a031e0512090a050108271b01 68
    0x8000d00b41035480108400d00c50080382c3c4203545450000740e07103460745030400516503103e400a004030700702038940038000d28030b40c0000c2d000203001d001c02043c01403070130071b01c4c0340a50f41c0100185107000021000f118040e001504030f9411a03110900c5070045070021000c050020301510010030901c07034a0030050301888041071411400e0340140400c002a50002c03049800000c00844402e107443c0f200c1c1201c0f821442181c80080180c034140e0a007401280070210314505992904408001c011240900704502e02800120540007801840c0020341207442900b00c40f035071b000094100f0400b02c82c0300714424103403050b0001070094010232482054040c50098020303468400141c00801190781d8130f03100180180b0008202516034410210300034a581c4401d41c0ca4001140c00860940c120100c0c142900c407005845041030341d503841543d240a002c10301036400c0318090703900105050900da00d41001900e150100130b1040c4420040045003c1703c644103503c40c10b071042d0b1041c01601d403450300e010300c0482c92241141e10034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 440626375 1250 440625125 440625137
    0x161401061505090409060b040924020313121205070c1b0602031e0c1f050a150611010209041107020109060302041a18120d020706081303080903131401080106 69
    0x581c0e40000440341049020760700480c500d40325040003006031289201c0107800c54601500441408110a02505100d1612400c0014501991507010a03400700b0350300e405140020701400400505e444184110a11940c10700d010044101c0e980c00701114002c88180c1d01046030412018100b00c0a020003100c04086000301d003004509100e4002d540e8000e5070b4480c5d5201d90008800c40f4881010010342c0c04292001007100d40c0e1034282103000d650a03000c0c0700708801070350408001c1090480300d03004203041c1e10048002d61491500d4040100c49181d030040940303116543c200001a032580380d6008001091246040c5103070303604141c0c4001441c01495602c203c0c1054810f2105000c07040640c0d0a5a020303a0010001c242c0f00c02ca01c413501d88001c0410a0010380c426803035400e404074110007280386511119250260b60141d960380c5020755801d001225070104224a0740542000a8065106183c00050000803a0308000680d0414060070b0016000807242c5030001c900000e1543c0d11002003409840d0901e008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 440627625 1250 440626375 440626409
    0x506040b030c0c1e1b090f071b0506090f161a0f04080a0b090708070b03180f030c0610050a061209060b1503010314011103010e04030516140106 63
    0x800c940c080035048101808000580310b5103034104001c041e4400c1200c61340c203c41c0850b2251510780d40e01e5417603c400c0e181e2040b0385100804c0e2034a400c05078421002003481e05016038130900c00302c401041d59031102480341540c05015020640c100481803041010100800c8280c1e032240d1503a10f03150b00078041e0b1188200c810000e220090305410001003801465004c5520b0b07460004440d007240c010781d000038600d442154070107000c1c04040700700c003401440c0450988010544407118076031610f809000300030582030100301250428003c9101040e10f00491800e40b01c1400c41c245815086603c000d400c0f0b50654400701c2886980051104c4050040004550140ca01c80c546000072708043d403115160b0000c1a510314411045c04050b40203080e01403001000d1500c5c005c28080302884030f030400e02045e40c0c2c0401100e4510306542051081900c079010041909086a18114240700d80303d000400803800c0060501000c00a0003110008020b510f200308452481c0320020960300d804c4070b500790b004401c60001034400f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 440628875 1250 440627625 440627639
    0x9050c0a020d0807051e0a0306060201060503030703080912040b07030905010206040f0807151503030311040311091003020d03030624050f0c0a0c030b0105270c210f0709050604 77
    0x10b8022041550a002506a446080c1a261401250701501280396903403001c00e442c02440004141c58120ba40701000181e0b12000101d0072074105002d5250542d01c100316920100b801019003a501c19808422288410441410400c00c0c0e08568009480c403c0045101c10405801c0b82c40070000c0d001c207200818480c41d260b110351044005111000d4854880044c18005010b4046a602d1944608200c28010b094078590010080441c510041d000079181c0341c58590000b4100084408403608040180620200d40041024000700501652119034a2090000c01a101d551084106c01d000b0b4400140452400c04a135003035524030841024880c3c510362444040d590404140c910b08101d4aa03826103400500c440c2c075203010307080d1602620340b07182050000100701c80d044540341a0b4409440083e24107400504103140000101204080020208000f901d903820640140484041d0426040c2419000304034600800500b540d841080c1d11160040181080d00003031254020002902d441d1310303292038546 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 440630125 1250 440628875 440628883
    0x1704020603010b07060b040c050a030e0114061c052e0903080c0d06050a08030a020d05130311061606060503071a04210b0c0a0201110909070c02012709050c0a02 70
    0x10f450700110700410003405026296000d4850a0b50107002000514621000648550081041540080c0c01d1905a682441040c0102d14042d100494003d4071501d840701000305104036034031100c0d1912034500545010a100300f10078405144000a4003a42202100466241d041c030ac0b47c220029506190103080081c0d44400690b6000c000170107030f10f80301c2918003011000342c5466031020303034001454040800c443d04c000c0004d064910031a000c80301440107111080c0c03a070303004907507400800d030402c0380040000c982c0c40c0d440c01001c50307001000c43e07190400f140700c080302241e41c22000f0340f040d0b5550441800315040400c54200134100035000041101000d0681d045c06200c0ca000318030302c815480f80c040c4520703043d404482c0c0b42d80307a000c0d07100c003004d180c451128046a00040b803880b006600303009070f6200808000c8210b40c45810050040280d86d46c6000c401d961035407420310101e040003250301042c002181d0b00c0d400b483c1840201810580300754686040e02d4155800030300400baa00d070080180302140780d000a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 440631375 1250 440630125 440630129
    0x2706050d050603010f0f1a01030c170c120705090102060a2904020f0c0303100f0302010c0305090f100306050109090203060607030f1b0605040203060f01080303310804030201170402060301 82
    0x1103004107080e581d607008640544a1444a8800030b41008401c0b200032403641c21441044420020280311450800011020388030701c044000d010800d007030007442d5040701ca6020140d114111243c56442d00c030110b009003014400c01ca503c0400141c01003088500c0350f906201c0240c00c00e4050f41c042c00b030140c11100680040c0f5681a82d01401100c04038002d500fa110364040d5101d50840c51011911180240811901ca41c42140d0341015100810400b1428601440850007501d4041e558691000800e6a09581d20707489464019480880a00b13203c07040d40e90f5031f11070381a40e8141d076000700d001b500d024009821a0615040944014010b10400c005500c506060700c0c2021341501e01603949107000d00040d2041e5141284034003000b080c490303640c01809401c2e0042400b0302d200350b048030031594507003414207200e0b082030240320b09981080000c00c0f0f0701c0790075001000031884c850010114140010500c06030070800345000300c54250700030a040042d90f0f00001515080b00034412402c5981c44c050f03000442901c014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 440632625 1250 440631375 440631397
    0x3080a110f030d1d0607031d0d0804020d1b06110d0201051e060a0906081b0f01090302090603030d0609060e0c0403030504150306051206040b090a0c171606270605 71
    0x7601000c0750364002d8100b0019013140400c00c1c0c90050406040040c00781c4500300c121f406480646511b800e090600080030322948400395600c6078251030f103508005c16901e03403070300c1a60f0f6901400004480000781c120407a0082c04e00f5101c00c03c29880d9600f6a0342801d90072403810095900d08010040031442c4091451070000d40c140e090a0951b944000003920680c0c03175080700541c02d180400101e400e03000095180c0100101e0000d0400e0f806190040004a00c02c050a81c0c1c00500554010001030910a4103107030003443c01030940b42441d00b2403890707900715423599018280300c41d1a80303020490b000d03c01d0707413090f0000300701600e40d0f180074190b8801501c98030452040b5902e1101003500f5000c010300c84c0c1c3c81640600340040a4403081c0d05207440540c0c0e158001d0702c0589020b500c0c2d00c0407481840d40020b02c061211f91003410300014500e4103509500e07003040541c520040f40140c070422074040082c0369801c4c0c003405a0b84c44076801c054004a0204559a140b034a806020084104c244030a0350840d060314405940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 440633875 1250 440632625 440632631
    0x70c0b0c0a110a141605011b03110a050318090606030403120603020a1215360501061203020c010525170f120a2c010b0a03080a110f030d 60
    0x40704122000412200307601003034000d0300360400401541030100c01c0000da1aa04403800f0101410600303800c49250321a850102c0c142010340b402e00d0a80c10148440c503402820000740c620006e520007030904003400400c442503000050b248401c180d0008400c181d08100365001204c0c3d01d0128046080c921010f0005000c0c0b0280c48120440d501e42c80c0c004102640d0301400c40e14107036640314665004c45030703c00421122000b490f1440c561900030392192030364201066104050a641d84c542d80d0050740c8106d1407007840203240704810004902c0901402004001c101d103968a44115406c1c000c7c1400d00f07100056041010401c00d000b0904845500f00000d44424501c00c20204c0c4c1c0352070000f00c0c1000c03035903849860000105a42c0101410781015094600210b41300388855070f5034450300001c0350000418100110070600940070780480040b03070b40081d40341b604000511600100700082c0c030920300390700c1141c903a0400107000b00d40036803007100d00030021590b00c010610241c408500e9a224010b030031203911940d075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 440635125 1250 440633875 440633887
    0x5101112090a0507030b0405060f040302030405040f09080c03040e07030b030a0303230703020a1b020607061d030309030702130b0f130623010906020d09050d0f06140a05070c0b0c 78
    0x81c01e00011800c2c40c3d02008031044a0b50305d15095015400c1281c0580307503400307020000fa5090400481f01881a80c4c544e014518090901007040014403e1101c0380100b03a0392884484000342100d0300511944100100030354895182400c40150108000d180600300350500328000a03586001030800906581810080790710303005010180c41500d03403103030310000700b80f0183c050210141d0140c0c000c1600700304075078400107100300302c0014010454514038000d4100e0402c00100000c1031540d805004090702207100750f4940d002e040012461500b00b41c40d03101c0d003030304005100c104507c2c103031883c01401401024184036421100700040c1c140c180bc694007a019000b0308030b00750324000a550041000d00189580d8482d0030740c12000c01e110104409891034007065051001043c00340c000244403200740c40d16610510f10500b01401d00030b005188120407900f041c030034401718001503840d000d100b260020503130611425141640c03181c000d5070006040c2a041c03181060070303600030408035402164460000c00c1080e41c3e4035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 440636375 1250 440635125 440635141
    0x19050405062b1a0412030c14070803090705120105060307060e0d12021006170d020f0d0e060d24050901050109090209060d06030c09060e010608010504090f1b0305101112 74
    0x810341c3ea200ca210020704400300020055412040c409003c0161303810414421800c0c02a04e40505540040310b40c0e0301c2c00d2048000140b000c0c0300465102c0a41400d80314040e40c0c40300030030140a00c0c0d20942c402c0703035180c0c020415941002c01600009280502d0f0807040030900201007500c044082d4805450080c4007100400424002c000221b08042c54100421446980301c82c503803829440c0c900461201d0251450b4210361510004d050f10f61404090003502c040c034020711003a901ca8003802c19403608400b051080c0702144569101e0f058290b01d18000a18050740c2c18200d40c1c1c90502541c000d80c2c400d0049000500050760300c9040d039030a88108480050790741d400100020414054078040907800c0341088804400c110451000c0750469204040920186860707050315035400200340a81d40c0000e80d00340c01000545001d400ca80d110341d000d6801400b074000e0a03194183c01d141c0e0907094444240c020301e420410132108000012084007440000c0001c0c01c2c0210000c0203034403a000c00e00000110010105d4481 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 440637625 1250 440636375 440636393
    0x2100911060724020c0c03010b0135310c050105160210020d0809010c0804030c0212010f02030115140301030311071502061014030a0204110919050405062b 68
    0xf40b074540003203500d10104800740c0b1001c1e510460b00e04985008512421070385040500a614100005844106400c1d010010822454100c02c2c155402c800c45c02d01d5840c030552103070380d485001d60715a0f80d40d07500b45ca8443e40c00b480011009003040c07011020003d02c02010a41606070f4100f9102c003403a00950310f0140503002e40c80c1065541e00690300a007041f1032401c07848c0d000145c00e49821100d448003021a583e2a1b00b481c02c0703510f2642c03c00f000c10390150006000921038610b00c0f0841e44001c2102c0340c0c403040d443c0b10b50f0848005030000d1004503400401441084d05081050341822a1480c2c11301c0e0008850080104600040c40010144081a14941c1e80c1c01410b100c19000340c80d50241d00340c01d03455503890081d9183e005441c0005400114078000c500320a554610306803006000c1c2c01000701000a0b800d0000400c00ca071070b00c4c800400d05001b90600c9503a00300008100d0b5251010045c0c0d0030341014100405c40d00c000c1c0040380328520002040901070840302c94104101e032890b940340c6074499035003401c150b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 440638875 1250 440637625 440637653
    0x1030f060b030702011107050c0907110a0f03081f091107080c0a0201030b040e06150a2c1f03030c0c03060908030a0501090507020c040905070503030415021009110607 73
    0x8506000010841d209044003441c41403007941d000748064616414071540314403070620040d0051b0030001c0350408a003800340b0516000b000c40d2900c08004034141e0406424103661020848081820700c01503070070b060780040003c1d00100801c1303910a4000003003401070b8038818640701c3d400010780c4601d90700500c110114250f9071025044204a90759202e414600342e2100c0d100c24040740800c0c42c0c640c5804642c2094814800d501c0c40002c018811380e103030300d118441482030324022540d00210401d800304521401c1a00c0c0c54070b241400300e0460300710503100858803d4141c000c1c20aa0446070710072080c621468040100b804690f09030a01c1c0044281c07508050081d00103070780015092a040c42c1f5141d003007100440c020f40c07080c02100000c002c23a03600c0d04206000c0d00c3d015910040180d01c00c102c4c480e068030742540700c4600188540200e03500c81d555100841e0540e002940040218840c1e209000010758050001c5040c402c103010302041000000da440c0c0d0344148250a00c54010030010415400b084040301001c46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 440640125 1250 440638875 440638901
    0x1002070503030f010801060f05040203100f06020703030e0f1f0201060305030415020c01320706050112051b010f0309110d05010c02390114031003020a05090f0c03060103 74
    0x9528125400c1003640c0c0d81c070680701c4103000060742c000068402070600c256002d60310042d80a549107490032081001a40000d0f05202241e20b0341c81000070003816102215000341303419006005014518200900031148100f0694091004c40030003541903a1051200e403200203c809070b014020740c11076001c07401013845400051247c803000801003000701c59040c00c0c40e0300c043c6075822554000c0d540d20044031a002600b001b54010030442008a1043c1c0300301e5a0a0744032101005a507041c10810740b151401d640080c1e1241c00c03078200c801d8616003031120502c180c050803000c0c02c1f06030103c0074103200000c120f42c40b810413441c10543d907510700200300003d05540c11403060004140c14111000c9041c0140203101c050818405441401105004007085d482080619154807034117001e41400313403d180100d600040c1900b41004001c1d98039112043d0084040c40c0210741d01c03281a040d0703d0542c4180000108160403840c4640c11130381c10082803000c100b00040d80240c000750030940b60f03250140160083c01e0170a011030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 440641375 1250 440640125 440640127
    0x60702060a140d060e010803120606030a0b04051314070f030609140d0e1e0616140a0c1a1602010e030c031002070b0601141608070c09050703060501020d0504171002 72
    0x2001410f4036040b40c400d94030040c90314400d40c2da031201030343c0d600d11130602e40c240004040c0c80090a180341120256a00102c0c00303401240712850180000d08881044071140c820003d85401c4005210329100300c0d0038a526004010f100450400b46115000702851200901c01c03900c03041e10804200ca9462140074046036281254607030040e131417000d040b4941e1400003d00039219040e110003c00401e0949072585400030342414940007a08104040b07444140006450400c28003111020300c1904200e0500c469001c1d100d03100146087c40c1c98281d80b400003542d00d081e1081c082c0594074051a1801c1507005080d03090801244c03c145400120f81090385201c241649409111f07c030304120043c80e0020108075214019601047e0344040040d05d100d442c543e10345004000a204c291508e90f901c078000c50307059000e09040c0303041c20705654071a0040611074021a000390b841d0010f100256815028040161400740040c0030681048a03000f01140201d01c240c084020302d41c003a07088980305c2441318400e0603c2880d815 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 440642625 1250 440641375 440641387
    0x12030b04051e0c0a0903032d0906090b03270f0601060203210408040b0304061404230c0105190c060207050a030207060905090a0e0f01060303081e010302060702060a14 73
    0x1200700309000040c601e02d0303400281030324010a084440c144400e480d0444158156142140c214000204006540c0f0207151103a984d260650054640c40070555220300c1382a080400c020b0801e0b6950b032050100e05002d20511034031460403101310740341c0c604a0381c002e02402e240301d0000b0314090424000d50460b024542c000728010341d0120051003541a0007026401c03001c0e161028841006044030090004034046c4820300c0003042e131340019078016004e40004221911612066400224290341c101d94100b41d00c0682d141441c2158826003406420101070b08000040c800064102c2c420a2110a6818500104010128040c2003000117464000804545581c810f24000743d80b8808420240c0151287e50400200c0b60300c0b5190020584801030070b10482030300e0f9011554054003c0a2609000303008112100c24000c009220b4480218000d44d00c0201798100f000c00800c00944c82d40e00e20122031011001400962030341812034a466170306a50b080c0d0341d0300210804a0301c4007007049840c000c2c09800550 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 440643875 1250 440642625 440642641
    0x406021e241503060603060115021005090307170306090105011b0c0306022d070305090d02180a0f09080708090105040b030408043209280510050a08070312030b0405 72
    0x30542c0324a10716440c1082400301c0204042d61030008641d8203034503922110040c0040d2070001841e81204103203004070f55016401c42203a80a484081710b60900b0769002184070f00a0249505072861041c100300d810500d1402c4c005d0101e000d41d281405028103002070101811f41070640c000c007803100d06400c215281a559124130b00400a5480010701d404020703c1d0306144011008140c00170b40c03100c0c800300d001915100243c0ea00741c0b09500403000b213a9204450000c00030158840d1044100e0360035041342e1200152a0a8140340122542081803030f01d0246402d08020006112004441d156500a0740c0507403560100401241d843c491600044036544010080c002088030b008058002e403805592554500300300e1098501c1ca1041d50054a500c2c48103c022840380e500300100b5654009000311800b0620300d000a01c00401d9003001c105800700d29980d00100800d1000300103010707014002c12590084980c1c90480c2842d0784958600019004502c981e10704465540290302100d048180030b0024041d52801050b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 440645125 1250 440643875 440643943
    0xd020408030918060105041205031c0f050a0507090e0423280c09050714180307080601080d0f030b0d0c060314160f050f03011e09020406021e 62
    0x110300c50081600c081c11400c3c426050b407409109040686d222420300d0310b000e4070881454000c4800340c07154002000351042c5c2d40d6085c4032200d2550201d1002041140f07400300b040e0201c40c0001c00c0803c0140c41c2c1000c1c45a110380c8212901d0031600240200c10039600d44d400c08504036030780003683c080f18402c0c0c581441b05a11000c0785d5001054810740c00b82000c1c1300d1110b10f0041c48100844001c0050313100c0c82c814440701a9551202da04400549030121401c000910b901f402640081c20120841104002e004401c0c43c01704202400380203508040c285951400b0082c541e5500d065609038240191b0140300102c2074400d03400801464801000c1000310012801c2055104486005540000e8140b0b400c0d18180300301007a1107070045590424030706000d455040102d402084050402007003043c10006202090407620145000c3c0035800101b6140c00c0a0350245038000301e00354440741001d40140010003480ea00421042c0d1006280c1d4607a10720700d403280314014101000010800c140c1d4070040d1105e0000c2903506 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 440646375 1250 440645125 440645137
    0xf0f210f160f050f0d0f0608072112112b0507050d1b0b0a0e01051e01050f0d061b0305060f0f0f06070b0106020a021905030a020909030d02040803 64
    0xa050a6032a29600d419001034a001218000400c8060031840c04480c45a00203008001c5402c2c4524105400c41c203044041e50040c4080082c01c6441da281030150010130702040c0010005001710034040d5100b030f0b050301882515600040c03e018800c04400080700c2c01007883d80324400103982619141c1502c450320740c010030751041d120000706400014201c0f0150081003110112500000103000c2460702c108111092909540c0d0154440c0d5401c50301400218690300c6c01d4007903582c2031000300b012042c05400780d0842c1c10081c00000b03602600181449000c01072030384181580c1d410741e004001760716990045958030906d040010581c601c1d150f403903080110050000c444900180e9810300c440e8459900f00200888222071060340517521790455801e80c58104482c10342c940004d0003041c1041c400307031110030700300030240c3c0540c1c05600a40c840c0b80442c1303031035003031030180320515644e1040341d504000c00f2070340d60240b00900034051464440410716007603080050310390a07401918291b54981d221159181c598101e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 440647482 1107 440646375 440646391
    0x30b06190801020a050d11030106080f0601030605090a0b01140c03040905181f0b010305130f0f0c060e09091c05070c05090412110a0201050f0f21 64
    0x3e00240140d42143d4960b1340c0c0724203440041c44140c1d4101420030503110010001401556000100942c07c603020482007501651074500690080c017940c5c00079a0b00c43c40c004100001da00003900700208020303081c0d980c400071011681403040c0e280118418a0b1158105000c28040206203a12640d4004c82d0500900c2c00c3c0c02c1d5440f009804d24102700e20302158000a0710051010b0000380c000c640c0c1d500c1c0c080ca0100601e2410114184220007842c000074006103500d100c080500c103481e8070500c0c440e038018080704805552424040c00d10000354407544d001e100018000b8800c0350020030040a0080c00f2921500013451036002260716600c103440842c1c022841c4d81c404509626000c44d01c0784528403649801c6a03100083c80040c10200417854868800c3c0d1018a5210041c0da00c102034070300c0d07000e051075402c1e1079611840c031503a594001c0f40042c0304294620b10b030784294000c521a00c0b030702403040 = true := by decide +kernel

theorem cover : BRFrame.Cov 440467625 440647482 := by
  have h0 := BRFrame.cov_init 440467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 440467625 ≤ n) (h2 : n < 440647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
