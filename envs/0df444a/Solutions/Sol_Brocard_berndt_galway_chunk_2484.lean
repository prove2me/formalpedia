-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2484
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:50:48.093583+00:00
-- url     : https://prove2.me/submissions/c5941c8e-ab9c-410d-99e6-6e3b2baa4e28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 446582733 ≤ n < 446762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 446583983 1250 446582733 446582737
    0x809100201022a0c0409060e01050105010f17090a050613050105161202033408060330040503070b040509060d05100b0f060a0206011d041221110406020c03010614090408 74
    0x139010b0418401e1a105182100c040c121384524001c140d406c0c41c0000ca0740f5445100300c00c010052540d1803420b058241d8030028001000603113924040c1c082e880f0481c010460030400305001d501e1a800407111840b05040282c00c6640142c03034502071210201d00401740d00e80c01144900704072060b2000507030f66210041c110049507000b80005071700319140f0404c00e105e4040700224400a40050300c8403110390b91100c04050300c13a01e410380741c0c1c00c0140a081c00c0070701c0d0000d803403c0c0c1404d8504181c03207145459102c50010340340601561040444c000001001d01c05814010080d40d0000c4040d81c403050485040c0da616625807e89102d15000300342c0e5020043c070181e8450079640d03000c1001426581e591649450025100c5100340921414480300543c098194100c03440d2951060341c002d1035203010500d405400310790f020000050503007500a0002840f80740c5283d485041300801541d004640d88620703240006e41059000d2030702503c01e0340b4001d0200100a132801800003480c1e82107e440c85150b86500d030811481c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 446585233 1250 446583983 446584003
    0x21c201c02010e07050a0b0f030c0d05040b01060314041a070e0402070c210503070807020d08133f02150a030614060309030a0305090709090809100201022a 68
    0x10200c080c15590190700c00700c00001072605550140d070b00c2d44184007441c44648120000218104010300012000602035600700c6a65071005284c10768442e01107040d00e900f0345054a0315503d000c01002040d8244c0b00d01003468090310070105441c5425166a007928513114030100b1980301c034000240314584220b0304052110303001802151100000d040900902619020391004070380f641d850100303550091503141d0072566000d00250f15040d03455450b142c03150026101240c0040000c000d0000040c04d400c05010302d901c0c1110715400b82454000d84120070100343e03100c511602d00095030003013400318203240e40c41411510180c00302a00081e102140b41c80b0b282c40100c3c0d0b04400041224081305500d900154100e6400b150090452600300e010001244020364004c2c281c1d03441004640300300ca019401050740901190b050f590741350340e41c2403228255403070600c0443c0c00407030019203420340386041d0b9290780451003144001c50500c0c001184489048450008600d105c5038080c110340304d0094200882042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 446586483 1250 446585233 446585263
    0xf05240f03030d06030c05040603051b0a030b010909150510061b0c03080a110c01052208030406050a180e01050d0807080a05030105031e060a090c0e041101021c20 71
    0x56210380009030f8004144502040b50544818000018a032400340103030810380ea0440060540e1508520380c0381324201d44903040540200d20a80000042460400402d00030f1030301007400700301d4404900d00300303005c500c00c1a2007a017440e140509102e40780100340c008c00156185400c0c40400a4001031740301d2140360369018001e01d80c11004401008010901c00540808400f98032090942510310409036110401410203500249041c0600d10b030f1440d0744a850100d4007401c442964081d0785840815003958010780101011840000d0032030070603580185c0c10710320b101540c0c0c414550359042c4480000002018400c40d4880c00d02c0403162814004070340100c80407254042d48040d40c1d11441d143c06045504244201d0b4403178056400a040381c0e24850b43d941044403240340c00b40480e076942c0260200104448502982c3c421503403a004a14a41500e80c140d00840c001d0241d50800030100000a00d072800400f0b0b5440c036001c01c0031040b0081500403050040e20902022001200341019042c0d034903003c841008410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 446587733 1250 446586483 446586487
    0x10030b0405071e080c0a0503150406090b0f0906030a08090118030c0f09150b2101030807020a1212050d020c06041101021b13020705010e0a14010f05240f0303 69
    0xb20160304483e035240203030400259503100e40386412003901c25200848855803280000c00070321401510070401158072441b681161003800e140c0401140455845800051005649400400c80c83c07a2000c6505032055045a503d85503190150100380c856010900c021f08030342010035015840e0303004085c64845030310344050344c030b0820396a81403890503140701307109003c03000e0404440810702054074010704128501c07440d1010b40da5841c15004600d29407000c40d4071002c1c240f070441001c4640d9400000140254001e8045d5511000540100b100464095203c0e12080c040c2003d4540020900454111200b803c0c1c1085903c1e45602c0302d501000e40b280317641040f030390300030301c420401004054006034009040130782c00c03242030070001c110103014005240351103076000c1a241140d1881681035001000c0c04c0f4440c070004207030008481d11252410180780003c07110038590641c1642c024070244500000b1b8824604144004c0c101464044d00018004604110010b000e00c1341c4e24035a11148002c0820f60000b400301d80d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 446588983 1250 446587733 446587741
    0x4050702010204180b01080f0403081602071703030a050c160f020414010e0a0c090602070e0405070317220e070c0203120301140901050f031905071806090c0201060303080610030b0405 80
    0x4200d01d85d2040d01280a10001c10564032800c034055105980c0b6480e1111251604880300b0034019155038400b08522504801142c0e09080404581c1d04901e441b0003151241855028041507800c014840d1850349018000030b54135009008400c000d10b5040340c02c940d403005030746c000325010389508018080e4084500c40000b034050100d2400f188940342c0c0c845d040005100d000e4003141c85902512035000160300881e010700c82102d40e2a03025070414030640c01c44000c1c44c0d40369503030329000c02082200903192802156103507196450030345880d02e0f281020800d800440c103040b5140d40104001d880c2501700003100c840c2c40110b40f01009209039030061596519200d60303454540c0205c0c4040241c90034040d00d944000000c490a0042c140c4c100030b031000700035060b502c1015980d41210025401c0560b05803203035400010b0b01500c40640c170310322410030b1000860101d00300300981d001d5400020320304c0110380c03400d541000070990001610f43c20490846440384001c1000303030128080c107841c03103009500c545030401b40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 446590233 1250 446588983 446589029
    0xa020f0f091e0a260f070501080901050403021507050c07030b0604110c030a0c150e15160807050c1f0509070f080d0e0414040303050405160f0504050702010204 70
    0x80c05000d882118145002100308040c1e00c00903041207003064020f1003a050510814410802410708100b03c458400f1404100c0085645020900350498400f90820704d8184003a582c4059529030155400009009905090707500940c0c454460044040c001c541d040030480242c40740040712079501155040b20f841c00c1d100c1c00c1c84101454107445541c131583c542420720354120f003108203171004d41d9941383c040c0d82080c20341710042d13410003100715048910143c40080518030304014400c1410406000c1c0090059022008840360459809084c1c031440f4414180545400395101c0140d6610090502c3c0560300c0b0942112064540000503035a00b0700081030008801e442c0c80f0b1980f043c2d214040c0305088446240e600e054034480301040c0d000e0070364186c110b441000710080c0a980c82a4010202800000e10450f8038001e103000b42d01e09480c100c0001e901e0fa424041030141c01c10125810f0362888100351101c07440c024040c3d000109611445019984070000070780264000c2d8151401001902600c1942002071005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 446591483 1250 446590233 446590237
    0x1401050a0c0306090e0304180222060305310c090e0109060c0302040b12060307030c080a03020601171522080a0807020109020a03060e0f030a050405031902180a020f0f 73
    0x780c0310001c0d140c00c0c8001418001401240c0440c0c0c05207015525203802c104d81c1c950781030344d00c0f66183d820b1502040501c4128501240e001e403c1d6803070040d00c103807050030f09100409441015110b0000c00c00382c00c50344000f620b02640c900b0800300302e03002a029030141900c0c000300c1d40381071035001380d81162915039a8009150b042d04404444d0f4440d850070490036080c00000c0cec040380914007803100741020901500000c088001c2c4c0c060341102000341203c6000da0399645511104410750400300ba640c01525482c001c068040180c1c90140201c01c6070184d80003814107103940e40325a403aa8040c0320308415400701c1c1e000c4040c0070010444080129001e00c10103e0f03810000d5140c1e112111150006880a0008000354418852a40c101313500078280e20301189561205000780039420345030400ca0081415811400004000510001d07500d42c8506440f54070b00810903003044040d10a89580104015501005079a0003240c1c00444501094840e160f443d0b4040000003405040a0001410400a8403c034000002d06c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 446592733 1250 446591483 446591501
    0xb0310060317030705030106110304080d031e290a0306050403050705060c040f12060f1e1805030313030c050322050102010c2a080301030b01030309051f0c1401050a 72
    0x81c010800614642c020040b0f480125034941c00550701b4001070002c0d2344910010f4880d103080750700316800d10352500b5409091041c004807500200b961039004e9403200c80701c2d4411a8280702803050802010000100c1c0c0002d0036040c0350103c2c2503194008080324181c1e1018544c0300a150050070400507458140b80c041e200d640911000c3e01c1c5d9206050009500c440d00307402311410740d450030f010001c2c90f0b0720b000c18040d001134010742c00300c1e09141c540c0e10010780f0012034030404000c2d00548002c840a4102103e4000c00c40c0d50690700a60b4003032a6900c0540030a030300008980d004840d420408182910a00b01142e0a894501c0c00800c40d020028060a40f4941401d800444120400c1c19078100b51f61a001a800c031200030300301201181140c0b14015007030307a806803041e03c001c500741581d120044180d0345008e07030313580300b608100c034600203040051051550004464016000a48000c1c0600102e40c581c0001c3c0b080d1201c019040021640984080000d5281841120384149000b4001801d12580b01406042410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 446593983 1250 446592733 446592743
    0x120109090212030c0a08031b03090706090503010b0f0607020f1c020906011d040905030405040c020f0c0303120c25030203030a270303023906100b0a050307030b03100603 74
    0xc128000b90000200403102e51003400ca00401440b1a190f0719030205400082508218000800002c456442420000c610036954400500101410580c02801000d038075045180642e240409409294640340c81c0c085070100101d88850300d4901d20700c0046d9480c0799a00c5a50340284240000d51045031041c250140741c0e038801c8840011036540c0c1001114058841c0d00060325514a80780900402d05180d400350052340c0c09881580e02c2c1907100c0001c036055802240804005034840100c40c0348808041c480c2c0c0301002c200710081c503c0c214a40c0400420010f002c1d200c1c101c00880055032407085010882e4880c0d141400c801c612215005d5401c019403203403c12a50410450304005104401c98a002c5041103a2411400800321011503500e00320001d40081c80180006d0100303600c1103a8400c0d140315581c40031603841c0e4001f81c240c00c0d10700425082c400040c20a410501d030b102d1086c840003038a1400d0317403003140c12480c0c1152655210300c400c8001c2c0c40700000280c0c150040c603007860603c4019070089420350f8060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 446595233 1250 446593983 446593999
    0x905030d0e060601080103021e031c121404030f230702030f0c06030705070219090221060d03050c0102090a03061a18040b04020a0f14090c090f010e061201090902 71
    0x4001c45458090483d4490700155100006100528024200745640e2212000c111103e0741d240d0086442c00d0f01d5038401050781c1001e03000070b0540c25442014486100c0085005001d6240e50340364451002c040070b40000d0a1000c03024002c100d05201c2c0d0301089038800c0650480c9074070f00c0403e1803464940e1003120180c1c0a80100d11300040d0360000001c04011a64020348824a91b60320301340119140d400c0340704c040f0391201040345000aa8444110032001030f040d0701b00c0050ba039900c6604004206904003004030341d408038040802c40d503a51568000c130011a014103013250340b0320b01c460105d0b00901c42d0300c0c2840e80c0b18001d24400700c00e110203580645080d500b002d10405603085a60b041103100390f06002e03486d21141c00c8900207000607000200c020740280c0301401c4100300035140c014900d40380506030040600c8808000703000209180407040d039a000300f58450764a00e030050020120310031181100503a41400140c06c48090151501022240300342c400656001c02561030703500d0b4402a1028900c203034030a00c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 446596483 1250 446595233 446595251
    0x1050306241b0d08070302030618040510050123060d0e06070905030f210c0708152d1b040b0f030901150503031b0313060c0b0a0501080c040b030f010905030d 69
    0x2500b100700a9080c1c4030301d4003030f51700e082040f406548024411600088660320414880c20014052406070b4401e4006e8044004000c3c3e4110454505034880402007289144e030030f0f15001800d940b04c020007020746d5116038800c0c0c1c0b04041340150074940301100d0a840f0302020044495480050f0304c0076220100e007034400c420303810240543c5c0c80c15880621442d848091030980180c21f210380041015000007000d0f100300c26901c4142500b05030207600e001d840d150a002c100300c010031051503030700b007944150074040007042d12070900c2c0c014006004180400716079240525100003e5140191002030481c0f00ea03035961041206c2d54100e060b0010342d0032402d030b03608010540241034200e0350340005548020300150f09064480c803128160074000c01000d107040c00300b000813220800441038840c01078010303071301c880f01004400e151030385210705c00402d810035080c5814018444058042129007102204560108141950500203410201d4a03000a803045d0719001c025001c0041c0800a0614842c91400030011102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 446597733 1250 446596483 446596537
    0x8220e0f010b03150402180303030f1005090411060705160f1406031b131d0103110102011a120c1009063f020715020d1107020306060105030624 63
    0xb5561865140d80003104105141401e9001d00507c2801c02c00c03041c0207603c904040390540e4402e0300d01000e0001c4400c2082942018844c04800410064682e00c00c54507154403a148000c40e00035510b4031645d4001400f80610000300615002d480508800904031940c1d04060101d00c5000c3c458022803000b0803103544400e280600503684a00c0c2d00b0722101d80443c00e90801e8114036400a9144001820880c1c00822030310a802010f0018144281008800394110b05041e02c61100c00c1020904581c185919400c0300b1044d884084441c21066443d040c03800741400d04542050380480f1000d810241c0b2403911034078981c0c4211500c044440545441d00d010715080013169000c1a400112080752080074504130410402102c1980b100802400050030075811b40d490f04a803501164800d030145401080c10511030410748140f400881c1080351442c9031600300d0740803a44601000b004203061000c08400104240c0b01c1841115907031502d0f04182408841d80c0716002d007280c0014004511183c510030001c10301c45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 446598983 1250 446597733 446597737
    0x1170d030b0d0308100801020c163203070e0901050a050106020a030903260a020a05120c060112050c03060412141c090203011e050f0a0b0108010308220e0f010b 70
    0x24005403020440042c00c2e2000d0f40c9084015200101e10600044005a4000c082c401f03071802480c070328090400c05110442c00040f41005801ca00d003c0c01e4200c085405a018408444402480030340c0485007503022100002e0501b8010b60140040c0000202004100e0806500645c480c1c04ca1420401045e41c8500080340e54801e070010003004600c49280c1070020440040c8002c40e0381d0300924400401480d503420031089900b290040b0800740e4002c030105410004248400305850b0b6010301041d00f07100c108030b4065580c10043c85402020016800c3c02c2052180c1403008008a90700030701211198202032510b0304002034107880100002e4101050010b03004480021076101e07240c085e0034048a40d650082c40760040622050403a4159a40c61084ca21a44a40c2c65100003000c0c10000203264036041e5030215a17400010110144285049006440c90ba0003030403403030641c0d130030803040b0b615410f00100b09154503a2454085c041c03c0b0702c000c0c00203000b43d040943c0e03900c14190441c025445036600e20f00c1241c28 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 446600233 1250 446598983 446599001
    0x30203061c0b04060209030111041d0615390609010606030b0904021e100f02010609020703022d060a051e0601021f0615020708120f040608041a01170d03 67
    0xa02c00250100c3c000c54000d0300130317114a41c4000e00000c4e011000100d41481c6074400c3d40414074060080580510707010040042036130001069484551a070710060305a606845505000e9680d00114504801c24014482800e240062030705070301d03416400c00018803070b13035044103d42c442c00380d41c200b400110f01c0078480d02841040742d502920141541d1140d0f401c00802d081e5440ea41522024909034010380341e41c40b2400c1c3c0800300000c0e12000c102c0c03180380400a00f99082608800816030041002000007580054050359512100391707042794240114450000c10040d003e80140e0714444c450a2013a01c1c8002d41c49940030396981000090400050710703403210328040495015001d0380180c0e001c0e9404506110210a042d2002d6200096094441c81d8103a80e01028440070070050740406414800000108034100c0c034441d20080c0b8504010940528401600c11801400d00f00142c40e4086800c0118030464400560664019000b803507031038285150100304040d840856611800f1150314a0302c0c0203115440078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 446601483 1250 446600233 446600243
    0x3031b06071713110d0b0601020d050f0403031103041a18011806120f0e0105010602160e0c070201030204051f0915090509060d020a03080408011406010f0309020301110703030203061c 80
    0xb0b0b9910400c0f40c2036111450001034800140000d02800503980d00100061042d02c1614190114140070000a1500c60b0021010382840350400c403014189407500155001c499051922016101c804d04100741503010310340c80b4106131400303031404140c5401c0c100302402c040900c0d06200c0305108090070046401c500019a00300310800012401e00c03a1a08c6005078004991041801140820211410000b101c440c040300c0c1e02565940c4006001c400c0d410301132100c580214031861201a400c1140d0111440800b814040000b100007960740c04590194050b10000c003001001d0016400b0900b800d03482003046000c043e000102505404100000c03204448802440b07a035070380240307080c104030501c4586034018003c180d101088a0031031006a4454100201452081000310b840d189003400050a584500820f007954034407580401001c0e0360701881844071480d0a15010038a9070007800860300500c0c115003880180c0300002a100103058050f0002d50083c03000f41d6046040482c0310104543e01d00040400500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 446602733 1250 446601483 446601527
    0x50307031d0f01180512150f040201051801120608010c0921200a0b18030312160320040f050f0d03140c100f050a0b03100c030b03031b0607 61
    0x72843d44641d144000c010b210483c803141844e2030300001141080500c40113000d035417000390300c0e0740440c6042c52a6604415404215843c601380307a8000380840c000d02c88901c1c7d00300048462811181c1c810014402c8408110008004c1d1a0311040c8460103401003000c030310b0108003243d0300001d65580b1420394000d40001c2002d00041d41040743d84048840c2e0240c1110b80002c00740c050440d04650741e9070311020080c02ca1903203555a80e4041a111000c1c1024140c40038441d40041c000c605184841d60701d1160301011034072601c00c408103082429401800c11408030b129080d00301130044128000c800c020015100c0111050629941c1d4008029500401d12036144e04040700c001074900203070280521039420302c0020750007802d0501c0019182d20b41114044800400da490304a81c902d4511248215500003404100034000307928404082680c1d00616010f155031a9910050f159507284a58401d9801c9080202501c0e5120712044101c10306030940300c005940c070f00855001c9401540182c03400440c800d20f1002c0b0320 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 446603983 1250 446602733 446602759
    0x605150102031e190206010608010f030c05040203061201061512060317070507120602130b1305060a030f0608060601083d03080a11061e0402040203071407050307031d 73
    0x20f0800c481d5262507845142030140c0240340c25010001c14003901c80b60f0052200b5031429800400c92207041e40111007040820b201032000c01c02584600d010380f1b100750b81c0907a81e5240c0b0400700707500602c15036080c01c1d02c0d4a031500c0070540c400d61784000300c07940405668000c100510756210f0b000b01d621a1200905100c2449503541d14590203c001d0014035024000b542e032055a034102025229421820032100741d07500003842c240c42d80212a209001c0e2200700803642c00c12450360391205d1812018000c0c60310950010603c840d003036120f90050000d51640c400240102c40e910040103650700030960704540807813400000a18400c40f51004150354034283c0c9581984600700040c0303480d440d00703100301c080c154881060021021405000c010a104445a0b48044031200305c4080e4604007100944a98594007480840c580300070881100c1c5c40d00160112401a50703034861000c140c88285080224450044c400f140c2201030290100280c804a8000e0311500500318812555011112807003071030951083c41c0710303648 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 446605233 1250 446603983 446604007
    0x305220f17070e040519060506090106110c1e0402070c080c010302090319080409020408100b090907051c020a0305060403090518010e090f030c03040f0b0406080c0c032104060515010203 81
    0x3e5904540120240c4907100d80b00041c0d095030244c0c904003178811031f40b03600c20f111440c1000b83c00c1a005280c10b2134904140703010356541e0760710341500e0b001c200d1241c082c40701d0a4044032450312040c04d41840c001d00c119030b81c4441c1d1802d100700707080381d11a8015901401d030140810754000e00855a4002c2c00401820590034107031040b1081440c88503043c2c0310000203000c007156048591008102514100c001040c3c8080c0f0340080500781e0740c4048400307010300c060314140182d084c0001548030548104650711000c20202c00c003a04901c01105002940c09100300c980002032060100d00c09024074081d41e5200f04441d280c02c14052507111b96400d030f0458042d480f00400c00c001d00301a41942224901e002e0740d01c003511648416203141c01568580a25400010f070801001d99140e40c5d01000381400710015050519084002d480703250010b0407040c038164001018a880c070020710031181c1c41c508100c40070f04003040c516001d00303140008031021200a841c1c0404078035008262003158003040700503402189095810703410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 446606483 1250 446605233 446605259
    0xa14040b04360b04031d0315010603020706020c03032a0f0a030b06070212060718121211030d020711010305060904110a1a0d0501050114160305220f1707 67
    0x20702c22142c45140140310000e9140e1540c030380220300940d0f900f0307401044c401d030f01c0340544150b801c01c0741710b40c2c000d00d601500464801d048a044698034100140c41e0384084c1450406071054240140941c0070010803c0403a40790040041d43d040c00d80c200d03295000110264100c0e8920408141e001520414000040014841c2c2c0142041d070a010b8811810900c8550101d03078404c4901030b040750213400a408000344035902c180d40d410800d200a00d54403940b031818000301d443c10200d00000d0544000b14080d00101c0b8050003810340301c8590a4212592510455440e4000350400c04085034600d441d1420039040d58031038050a40540c000130308a03d0103485035600c60151070040c450842d0000b280c11340000e800100c040354883c051302c040300965982c400e010151011110140c02c50781c140074040000410401d4628140c0740c280310740031009002c540480c1010754003030003410081c03268180d100380b1000c054a030030302c0348800b111b69010310203103140d80b542c0418880c01869000d044483d8001481008090700c80c00c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 446607733 1250 446606483 446606561
    0xc2106010504030203010f060312030c08150303040b1602010207050a05130b12030403030c0507050103050f011503062706150e040213050d0507060f2c0a050a14040b04 73
    0x10070920705952070f80840c0c25290304c0010300400b507940d03140c10028041c805101c0802100c1624007000181c2807030f04040e002c400007804601b111005400400d00c262010070464028002e4518640d0302d40f100c000c0d941d0034011101c0c1c0101d00500070104000b07100e040608448003514030041250500c00c81e02c4052400a0104440706513202c00003a4240ba005401880108040c602a659603d00c030701507410310034a804100e40c0018109440d21081110500c085021241903c207540642d8a04c6044041c045002e00b1460700510180b030900c00740329611518034441074118190518051042d1680c4036804100c0ca518142e400740400d41e0240360000c2841c1941c024070708414156680e4100a4444010503005400403808407041c2e4010b00e014880c05070031071002803410307100385001d2281e10603200d0160075000594000f09100340f0b00e001860803990380c40c50140080c08002d440b66400750769582e1500521340c00b041d60035000341c0c82c3c0310000c1c0d0345082074021401401600489001d82d00810300702c1000c4407030164 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 446608983 1250 446607733 446607737
    0xb0f041505041101080a0b0a0810050c0c07170a0c0f06080f0606040501050c01091205030603150910020d0e0a06051b1809061518180f150d0507080d080c210601 70
    0x201415150b52361232824011b04040c0340181101202e201500c2c0856801a150b0400707054140581c0d480741c2c60001c0e030a010740d0300811030540042c2c9101074552800a0340d0000800c210074450000c03c080c010b0481c82401c0310032039070b030341b01041d221f00204840010742500d0040d0000020030080c01254000c034000c0000c41e1b095000018515503646680c01c4501c45400c6190000c1e5000042c00303440e140401c06243c20400709200f00300c0a003041030340d0f40d035503180c07596409900725004200c60141200381d5010707582102c03022040d11320300100307440c01c40010b050444812050802440341c602d10040d424042d1040c5c0d50b2488902002400340038104841c090000f03103020340c0141c41e0460900142e21174009004003218655010750505041030400c2050f03016035080007034420410007003003507020020b812580c01211587d00001038001c1003010400d006054100640b2078851524006400c440000706096000c4660751104026211079118020520075140d04103074490300c8428184005d04c030301c1c580c05d80040d814 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 446610233 1250 446608983 446608991
    0xf111201020c100b06040815060607060c020618120d02340204060509060607020f0103240f050315070e0102010207060e030a0e06040b040e130b0f041505041101080a 72
    0x58254942640d02290120b440c54102e18011020a44207010f0140e040c40201c510301e040c2410308800c0307940d80c00086150750b542503c3ca40820305030b842c1c000c211500b21b500843c0901c031490320b0707120280d55901c09071851242908401d0043c0c21348040810b02d44207200441d40900d1400039030b004560040c3d080f007a0401030343c0c20068051141c0f4260101d180c200030104007844a000d0540d4010001190461380c8594090700e90f4008008580e0780700f90803a40406d504072a030741c1d00701d5000e10041b801000ca1558568850707400901030b020703a600c42d24001c8100c0301061304203103042ea1241d007030545500b102401190300024a8002c035544c14025130680504240c10b1000609202d40c5466100a640f91090701c3c01035604002003070811903503c90501507a949082d40e00c54030f071601e0320040944074810b5118508010314101d0126003100c0110101c2c0e01001e03000549201241000456239038080c1c415101241c1b0602c826455074008841030107514402ca03040541d0340c4204020500554110703000414940107155a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 446611483 1250 446610233 446610259
    0x1b0f0906040f0e040c080105191a13290d020607110904030816020a0c05040e010f02031008100b030618030904050a1a04060513090c0305072408040f11 66
    0x82400340310010b180e0840f100c80a4107150a02e10704000194200003078070b0341000100302180c0e105482000c05921140e0300002c0d02c48414140300c8003c00c8400005902c251000e4503030b903201c4080c0c2c002d5800381c0000c0410b0000e01c038848010803000300b0300c056640c3d007000805402c00058904540500f10329802406840300c001400000940b0503c030440e0102c020540030301c00e01c618094884589190b82d4400c2c00213040e5410700d9142c410100c4418032400344600c1e00e42c400e425000c0d20030b400100c002160a00f00b95120f0400c100240791040c02c0e03000d56102c52040750392060300d60400e03005208034400081c024043ea03448800344040c114aa40c03040032031911041145503581c0e11503224851007072501300300004080800c605071900c21012507811503c43da081c01710070300c5143ea44072242441104903860014240d0b00f54900620109841c0c2d202070054050072000182d81100c000d0024880b0f91900302d40c400700c140200c4140c400d040c05440241641c12001c40d04800200100d400760780804005003200300e00a2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 446612733 1250 446611483 446611499
    0xf0f0203030c03070602031602060411130b0409080910081003230d080a110703053c070c0927030e1002010b0f100f030203040609060f141b0f090604 65
    0x3000300002c9480711b90020401011008190307840b8080e40e0284064410360500e91152101c0e10700741d004081c403507007044940d292a8003c50f0320842440f90003500c1400720308098100740c40160400c0d07085600808411840e01e0381c2e80d108a000b544141c0112199840043c2035403648400791004890340da180c1303401d6841f51300c80e0400c10006200b045a280d5924041807424031100b03400d44e00840d007020700b0f981041c026240069003000a80d14880c400b01d08038104503c15500d440c101d69294200f050002c920709a00340c0340c25106000070f00800c0c0c0a40c0845041ca070362001408122800807500d03071503a0500c03100020210591220a9000302d000e032800344540ca054000144100c01a42c0038080036030741da83c0070554141400d6190640442e002c540e90b43c0f0302c0c1d0107a4000f410b10084009400d0400d41c1c000300140c10480030303a00201406401404c104000080841603900400584181c0c044001c1d0110015442e05140e010141c001e850700f0482909050b2007408a901c0c0780c005d80107043c0e10020611001c070b0001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 446613983 1250 446612733 446612737
    0x601062a0501140a05180606010507080c07170604050c030712021c0209150406053a1a0105090a09120c0f0b0901051e0105030a11120f0706030b04090f0f0203030c03 72
    0x1000160000407241442034201e800d00e03150ba075481b0700342d4005400700302d032507038100c02592640340c1c01031103d0356a00200400030b03007018510341080c40800d006107140749000000082c1c00344900d22841c02c442c00150308004040d603410081c418540581c00d056115001402c00b00b103031b82e100720000143c0c040b00d00e0156000503465070701119000c1d1100103c0b070290109141c2805060010101950009540030104124402c001507400c2d103161025442e415510403542122150b160b0030360803c80089a0545903000806000700030711505100e228010003046400585e4030440381c0103580041482e188410f0b1520981e00d101403001c1c1507c54084003070305407011420420b0300500c20024840001164500701c03442182007009561218001c4072035400501460300e00182c9841d00719001460010400030342000144c3c000c58907001c005980c019444a141200d80024070032060f2051274405001e444000000e02045803420b520192866040101642c081a01c500440071464005002d6030711700f940100e00b44c0e20315 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 446615233 1250 446613983 446613991
    0x240f15020c030616170c030609060109080f06040b07112107050a0b061014040b0d1b1106010812040b0f070807030507020f0901031a060604080f030c0601062a050114 72
    0x161034541180c1d00c0d910303171011410780044600102400b845c1003080030b100580c0001001e480c0100d1220300424031a81c0140e44110042c802e0b541125140300607a465039407228011b460841c1c1e20706a0801103980180035140e42e50f0b00802a1004014400d54401200307030400c0340040380c1c64a4002048208003289080c400c020849000d05903464090500b9402c5c803840d0345c032100800c23041040c41038544e1301c00521842290111491035540c50344031001030401c03500400450907810f210030f4090540e6021035801c9520184070003140400c1e0340380d503030380e564040d6102c9001c0c8510801c2c2d403004010500c9042d000700050200c0420440d01d03d801c2006035990710000f80c0c0504007c0c1d02142c1302044141c1140f030245944568010103030360f4603016524640d152020004820703844040e10001d200020b105440e403900340e400611450341240d4042c5480001151294080318440c0d4090046000110b610307400341020741f00341140400030f007031201100c9103c82c2c000208148200d81c0c40d5281c0e80381d043e08140820b03925010b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 446616483 1250 446615233 446615251
    0xe24041d071e0801020a050a0c1e20040218040e250f05060a09030f02011e0914030109031e020106090f0c020d09080d03021e0301030501240f15020c0306 67
    0x880141404107003449a0364807100644c1e0040003405200c070b501c8815200b6803429401c00410361245882c100704810007110000c021100d400c0b04113070900403c24401c2d0b0413269010400c01c40301503650309100503841a1804544800404503540da030301d041231360008901106200580e001041e0503c142d1200b9030b04518280d50041c031101081c00700d4600e8010803c001c040403200340b0319000c400080500000f00358403024040051020079042564015980c409900030340c1034010050112a4801030302aa020380100d1312b031108040701a031003d0605224074008a50907880d89190701c0e210100580c0c03001841c0e03c0030740440d505c3d010000750340c031464040c6400410b4100e5012900c40300c5050f00a10f400b9000c0c03003401c02c111074070b8010420290003040e1000c50b0f00c4c60745000361b0b0751504055500da42001101c41c40e1031070fa00001c000002d221040d401003070409000b0791241e0307403051030490702c41c070100b410f02900c1003054010108004195655840484101443c0143c2d0001d41d0144002414008210341c0004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 446617733 1250 446616483 446616509
    0x519030207290c07050715030f0e01021309090b0f06130f0b090703230709270e030705030901050d0b090708040605070f050304080c03040b040f0e24041d07 68
    0x400c4400402d420703a1140752404281e0a003021500e800d07690314518481d540d0f48100c00e5000d040c4462098119094000c2c2d40f21040c441c40b0060300829000313602c5614841708010429402060700401800364609040c0c1000e00c1005503103030b0440f9003605110192240f58070010f2184041d00490840c0260b035034a0101d03000005029925406018142e040104071008041c6030400e422a12080343d01803020702100340c0000c0c40c9580d2800d4050b02c25020030b03040074140440c000c43c03031250f40d01c00311030310b01c0074051601d000d00525004c864000e50343d000c2c09038002c0094006100108180d41b1840180100c0b982da800045507404d86c03400400c4070720106407031120005148000300024003006005040c1c10600d00c0c541340c01e0181412100500e1400054002000440e002074280d0042c48204182c40207010680e4030250380700d90f11a80c03816081446d01c01c0c00c4600d0344150018004041144202c480c41c0381d44e84d6940d11032003c810400c002820000c0040340780901c0481c4489503d0000c1000f82c000c2d19000d85c1442d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 446618983 1250 446617733 446617793
    0x619080d0212160f110301060306060503010e030f0a0302070c030215070302060610090605031807080f0d020307030807051c050106020a050601050f0604032316051309030519030207 79
    0x28200140b07015580401c00d010046151118031030034a8840b1a50441c400c60100b19641c645030907610418030f8403d51640c02e105010052250641c8040210b0307000b14000c100e245000352909850b40a402d0418040700c0043c08148070700c901a030001c00f92103229144401c40c890301c0e5800201e8441050025655858003c00c2c04020560104003084c1c101c403088844078400700b10b01100424126190142504108011000c641040c0003480c204c1a880441000e403040d03141c849480a0755106080b801203994460303034004001190020040b986c1080d09903490039402d550303505094079140d00100000340242d5190580390548042445a24081e1195601030b00d1074180c41c1c10820728115040e0041c5109074056181a0481c0e55000100c3d03007142d5111000038080305940c0103d0f502203500c0402d400050281d4000d140d800c0d411984140140c91b0116183c144040c0b120512030103c8060090043c081001045403031030b80041308201e008110300724500503141414995900d800184090307c5900ca8090a080301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 446620233 1250 446618983 446618987
    0x1203060515071101031104090c020109140d08100e1501122906040e0402010807020f0106140a0b091011030c0a0c050a0503030307050901120b090f1603020717030619080d 74
    0xc0c10f080d00d0246401e00c01d00c20b0305c15110451340f1691103400b04541e0f0799010b031500c060007074000c0154107420007813250300039080c620850344505107085a08002160500002c00e8200845042811b841c0b000c86160384640c1e17003154031501409600c06041c1030080740000b40d010140f490040100c42c40c10350390751044010602203000344030001103001034410301090000344140708640c101030b54081d03024601000e494681c10300a0b800e0811002600546500340000030800d8442d0391640c0c200d00c90152180054503a459101c00820b001f00e4502130f600078030001d00c10258904c5011682c4014021009881c03030a09030038680c074a801c9040da0215507030382050000700310382d160070300800c00100760550245140d40b50410f0018118481c81000c5818000200c141121030112680301c403001c07500103004c03c50303a410704000324200414206c1c2c0245001005000007140c0c01d100303009441c0e85036440440c0500d5546250300141494000400e880e8004592204100c0714403010300c20000240f40050241c19020541500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 446621483 1250 446620233 446620253
    0x100507140c030f070501120c030212040f110109031e0203010e030c0601150809070b0d0914010b0f01020106050105480d08042301112710020604120306051507 69
    0x10744811600044405c20090f42c21425000352145054400100200681c0041e0028011104074020041040081000b0044a031800400c4c6500404050803008132500c01151419440d000041c00c05004020800c1150b20000300110f42510040012a840e18003050030303891904100488000365203c100100183e039031000d142900005586001040d03440c00c441001c1e5551010f2184501d9850b000039072441450302980303d40e0f5441ea21020030b030010340e85080164080d000c0b10044501c900e4030341c09580400d600520902044810607180d10b13042c10001a04d0544002c940d0041301031940703014450029a42c000711041651003040b07601c284480342105022850800c141944009000043c01404045003681c0005481c981c051901401c8101103411120702525040c0c00c498000725002c1110400049000c1071a0881c9a61800b0141d100c2c0d0810200700e502c1e01a54140c81c09600b210b80402c0104214030040010741d40701e0300303022a40d25030703a20103c2c080c41d4182006401505003c00d890080000f0410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 446622733 1250 446621483 446621503
    0x14071e05010b1e0f030f0d050307020102091008071b150b010203090301050405151005060403020d021f03021801052502010c0f0c061709072c010312030518060402100507140c03 77
    0x1700400560b00140b50265943c1c0b6007074800b8041c0000400001e104d14401d40460300b002c000540400421103802074040c043e06415101d0b0700201d41080301298942c0003101d100171030940c10101301d00c100700c40705413690018079200c103100d41140020005540740391001d010340341c041ca00c5180140019114820441344848000e0594425240c1034141000b103952010256810f50380c04407154a00d15800b4030024495580305480c20000200c0c0050340312380d0a4044c2d018082c5078070441e03a4028000840b000440766441010a984400c00074401c40d0a03100700c81c041c001480c02d206040c80c0050443c070b52030744189007030841d80496490803410800e1202a1703100400c0c01240000e8250382289042c179015035034a5111038000c40c83e40d220514420040c11007402caa0110307aa880010f45240340d42c4030f0231301c401809109051003011a0403c80402d2401d0030a22141000d101204046d081c1600d81d9400c002442c50310380445810044240000c0c001700b048050302131041810303003009000711206641803509001c9220 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 446623983 1250 446622733 446622739
    0x70603050f012904080115060f0c0f060906150e040c05041806091e030e03011104180902010519111b0a0b0d090503040608010614071e05010b1e0f 64
    0x81c004010810103281d00400c503200c0c1c82e07203560401d10314100c404070502541d40031104c5907003068900e5005080c14120718068640c1d6554220075144111420307542d114201e0002085220044003c50210300e01c4ea100900381c520030200856421800c2040007100b00c12500000b42c81402017092004019484925000401081e1414841804500402c128030b46c031105000e04240d846240b0f00d8104122001a0725601c00d055031003003003803d00c40c00d00500c070004402c6054001d41c60220749480040b03802c400e0b901264010f070240034052407517510340c070301502c5420012418008103000000030740c5036042e5568030740d1410b41d4030648002003018406150445440750005d244410340356101658035841001c005680390303d20300d9036490300c0c001040e20042400390301c040e017075010206010802640c404100341c126400b0b41c0d24907146054494500149214200c0b00414986140c0b04840c0c0250074045003080b5103000d480001840c0c0c240c2004200ca105610b0350490500010b1001406140b03000712010303000304001c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 446625233 1250 446623983 446624011
    0x4171209010807231224060d021603111603021c1b09020310061e0f0e040603110a06051309150b1c0c030b0f060a0507050601030507060305 61
    0x8022850080c0c4190005981005003280004004030300504201c48030b8074004c030f40a840400030204121441e041144600000130132100441caa40241080c8202c000c5d4610001c5550960710504000655212142200f0003603002e1005a1100c1c4600c6008650070b0301036200d4030901c2c201b06400074100700590010707540d503e030100010300c05038480020801400140c19081e840c1c0000c2410310365044207104c031090b8081040302d603021502040da0b0300554001e44040035840e8003141c565906a60302a41c48140030064041e03420a0243c01e4803a000c4001c4403d0a03042c0612414018804641030b220345400550300b04180c1074a091250500706203550080c0950700d0128204020880c1c01c03d48030244d4803820f0036068481c081610240c141c03035551030040c040c00b910305940c0c0180c80301304030710109a03801c080320445c42c0084200d501e600a004401c11048014082140e01756500d04000c04c40d00019071050420405106200c00940104203450286021720b00401701c032860910024150760b0005c000c00448000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 446626483 1250 446625233 446625253
    0x60708060103110307091a040504020403110307060f0509190810090309080d0914030f1b0103110703320d05090601050103020708040e06031c0c0203063702041a0417 72
    0x403010400055803017082d801d400c10200e47d0014160790146802290703201d8800036000003040000d500c0c034110100c09a064501540c0c1d00c0d00261100c41c925020140411410480c1c03a41d10f141180e88008404110509107a03850b132a50003080c41c0542540d41400781d02d555800000502d0f4100703550000500f0100e0003060313016410140201465520320814070b00e9510400801b0300e550f4103001e2200c3c02038904040380d03110050802c000d407e40c441901180e01091401c0c110000014140084501c100e406440d0607020850313096103005c801251445a0201143c01c584d500c0309403a8280041c100f81c040f001c0d01081d42d041c150070142c01c107581a44020305151040154a0014007000301761011101030b01b10281640d500c200110342840d04000d071114016070035059401240790404292415079000303a0846080340d07100064240d50102c8000c451040381441611390702c01054010000508920003440941020341e0b602022030141807986110200e4000481d0034440c00e20b0714007240041d000380900800b80004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 446627733 1250 446626483 446626487
    0x190c020d020708060105010f0c05030c121b030301050d0b040f0b090a0b160c030c050c13050412020c010824040516140715020f090d0606080d0203310305060708060103110307 76
    0xd21348d50b002070102001001d810b226060003a60110322185040e954242100c40240c03080c3d521003654111141102060585032001c00419a410303510081e03d0301244481c07540310140064030080c011580142180c900e1800a1590100d240c0070301170031401403151545900c4c010800d134100070010044c82c002128418542580248802c841d0364241c10811406801400e140d824000c00d11750ba6500100e4054030140000c501c2d50100d0310440c001c003a82e044800806200700d031108443c240e0350b40010040b0340400d140601c2c0601d041941360041140c0d8541500c041e02040541d07408441c0b4440420a142103984490317005041c500715500382c102440c1c0b901010b0342c2c5078070144031034402000201d039000c0707449004030816a00700e540b6860001c4c0040c51500071843e003640075140c64041c041c05030081c1e2100560b540d000000351026012503040c900104500405100c22545070400d10700708209520f0340010100300280401d0b03020f032075180e0750f102d400e290140014090310f210014003401c001c410420000c00703075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 446628983 1250 446627733 446627747
    0x3010c181a0f04080705040b060702090f131e1b0803030106030b041806240e0105040203040611030a06060207060f020d0c0510110912030c0601090203190c020d02070806010501 77
    0x80e80310658461640041c40703000c0c214002c03004103401d0300750001000710341c0c1040010300d1400c4400456041c85a400003505014450041c004000d4000403003402240d180408415029030000e2102c0b030820084007e0344a40c072284101a1380158040001803821051007481d1080a040c0000c44403411000340c9444100b6559101c14441c40040559480c02c5034a00e41e00c64000320000130f011030010031048240c2c207058004207104018080103a1401651306c50700d03120240e81400b12a85820504000e80c40d040600c400303035100801c01c035030302607031004505d0b400105c4a0103140a07602c100e400142503428150080c0c0b511580c0e0300030b9400d0080761104e2511640d400141080301d101c0d01c1c5403900d042980d503d021031401000404940c0c49900b095403100c0251820700203005111801c50340c820506c0e50300307004151280300d900d091882035008000188043c1c0001e400854000100b01600c0004881482e09102150300410403103006802c8031509401c80c0e40e040044070090454000905030340e52415002070034003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 446630233 1250 446628983 446628989
    0xa0c020a060f20010908040603140603010c09090b0f1c0308060d08190e130b0306060a1a032503020a08060a06081f03080d0e07090203010b030103030507140a030e03010c18 75
    0x155016030f41d09280e1802034200c6072000c1d6115248586075a10f42070044c3c0640045414056041c02880c0066024601401202a901c2e969182d4440356402c085000025000750354846400c402e200c005079441b41c0340d42145001c0411814080e48c191841e42c80d00609441d80a40f61500c115444954003012070a020204e075082800350264410741c11100310305035655104001300540c0081046000100303009180c0249035035000440940f00b59548400400a02c070107140185408920000b855184075840c40c0000d40e0040c003110703280e0001d21407011800d04070785c118203034407000242c010a0400d440f9401ca104c041e00411b00321164140e0a041a80007440c5141c010b000c21260040612503a100d004a5a844005036801000640c1d80f5280c8100d401c0240c0010103820304180b01e01440000c00d11107034403d40307042e9500074100314030f142d2850700c0454464200500c00e64100d01030301e40d10b0501c44410005103817000c5c03007500d41c14a6505107030101421100c11088010901491401c40407170220202c543c0d4080d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 446631483 1250 446630233 446630267
    0x110c0a03031e0f1704110301110306011403040c06111c020a0b0a1a0f0f120a0c080a080315040608030c061f0302130509152802040e1513020a0c020a060f 67
    0x80381c5d070b071403c242003120703680e11400b9095442c01111411340e0170040010f6202d10030a803264004100d00c000b00809511040b2005800c20311640e00900010744110f81125103000710004440c1504d40d40340c00c40c143c15000b070040101580c4003a40e50b400700440c000c0c07000d80c454610f0801700030a244030000d14114071203c000b070741e01c0741d0380341e1005030910395074a50030b00001c0030050f0605c1c07400d20201030395030740d90740c0400c406442c030b0074858400090003440000c80d82ca00545c03250a2a055031100310751903141f14180400d90b41c2c41603d0340b03030205a185041016140c5006c5200080265082403603641c010041e4030110703000d400425503001d0000d600d44501d050b42e94410030b90300061551b81c08102c5800c00e500300c440742c0300c103c110300244202444800796103040c44400e881240207421800c0b4410080b03115601c0ba4101980300040010300c0403009814100340400d01400300e2900501003240802240d10203c1a140801e8420b81c000c0150704181c01d141c8054038035418202040c95048030301801882e60785e101da5031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 446632733 1250 446631483 446631527
    0x213060e13080724060314060906090703030327050c0109170a02060306120f0a11040603110108090709060602070f050406080303040f050a020d030503181606110c0a03031e0f 76
    0xc10304c600340024414214441c0020003901c1d8481c03074070048450745088100340038804ea60105000200214a440c010046040105407262a6a6054000e030a0481241001d06221f070b01c41c001c8a00102c17000c18005124101a2403081d0301800054485541c50300682d000b890400905902c14400250b000c80ba160112803168580e504c400014250b0f444002480e00741d03010720a030b84010390100042400c4030512524499907000025000d01c0100d9049200142c0340d09256552a1155409060b00640103600c0f00706440650780c4491a1409403282c1d94042801a40810700c200550403c001603000a000c0031175003800100e04c0d1049103592408050f0000d45141c8445004408100041003074001c0c0e1980603048070a4800e2905004d0703c00c1d0000c49803102003042516600c0c01d58040410901412000705500d10001428040d08651548102c012424640304554000c9481c3e41c4030700b580d20082d0b200750f4540c031030103210b102c00200320b02c1c20960030828040380d410380c591016000742c4d2901246000c00c110b50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 446633983 1250 446632733 446632763
    0xe0a02210307080409020405010f031404061122140306043210060501030b0d020d0b0c0915030703111e07020d02040203040b0f09030702011d010c0213060e130807 71
    0x1e0440c4602d08004124000000700000e240c0800d0f000381040300d000f62100e011041500b581a02038810030503922004514280001740020426840034a0800d4481c0446d4204141014861480180c6101c0d040751004101c00030071546802c000d00395511501500a04080e0409a48002081000700342d01c00c0d0700560014070f800c070b0103d41c081d04000b40c88804d080b00c2c540303010602c4c0c0344024012070269600003070401c03252850904040c40407001565018204440c841429141c60050700e10280203400d00d00020851901107980b5155400c4280142d07194890b52414003100280888841621440408109001051190f0f82000b04005149039814000b940d8680d80d100113003452000f004000e6101e40702205110601c00c400c4c4195101c0c4a188200d41504c0e111242c4880c2e07a0300400c540240001c00c2a04c0aa400b41c161481c8580481010b040408148101b54005034492140301129814240d459108001170184100b0700c5030231000e2500d4a00024005440b40400b03489201c0e000350141c0071a403500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 446635233 1250 446633983 446634049
    0x10503011401260709171b06090a030602030a0e0105010e071101020d021215220e010b0d05060406060504200a0e0a0602010c020f01140f04080403060c0f030e0a02 71
    0x1500103a0414a0501c1c584402c0f6040320480300e001c0e2032000010f042d041001c05c1022010402d4084404400018024500d105084519200f1031100e050b4020f0014081e1200300e46079000843c0240d0305c14038000d40c4925110040c0c2040380e007003000310322080c1c0c100001008080400410242c2010103460042d00d0102c00c0865507000e44503070380342620558030000b49040314074a06601070307000d03021210040295190315010004000c10707815541ca81172903080e61210900619500543d04000001e001103900300f40a000240c1c0300c14112000d43d9250400410081002094824900500003c540c20444018402411200790141e01d1084002180004a01103518010a90000c03200350003844a80d0031912400028040c0c24903c4403803002d4444c4400c9040c910f0410f00a0802030281101190400d50b1801c4c940c2c1c980082c050010307603a00b0b500304008000304143d40540c46041070b49440c2c01207008030904004080f035610100c4104250000584880141c1d940300c6210040c5c4400e60101403600c01035820 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 446636483 1250 446635233 446635247
    0x30b0714070503130302030c010807080c09130903210c0804030c02180c0417030405090c16202b08130503070f0e10080a0825060e100b010503011401 65
    0x101411610002c1010500d0701440700e078010942e8421f4060700e01d0b1004c11b40040d907071440203440000105021800184000344000c0c054000070a0003401840401c142a40c11000c6a81d031280c11b138001820b012100d14102d4024503144103100d42000c04000400720b208008004440c007400013020043c4a138105801e641d101c0d00030a4038100c0c91411051141002000d401e82a4403d20a0b400f280c01c00c018500724408010059a086501c045c4c1791103000d5aa101e01001c0f1039101d41880d0b080491400d601318041100f1081c05a284400c414012000c0c041d4841000344401950b0032611071203207030001501c40c9a180c90b5182402903803100b901070b11409101070140c0e034908150032164051143c2040004d403000518044003c4824280c65810161100740020362400c1150081c4410b42d40190300e584000391880c00204180039880c408003030034103108101e54624031445001a5116921118a125032035402d22414410188150042281d80321900020744240014400c902082d1241030368240303e6401280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 446637733 1250 446636483 446636497
    0x515030a080927240a030b010e131704080717100b0604210b010602240a020f04061106060307180b040e19060e0c09041202010b120106031b030b0714 65
    0x80360f06549801e01c81000c0da04014001e140800380505a648036600304011018280c0c0c4e0007c0c002c50b116800d040079441c0e24103025000c0400d50004440340000316089110b100c2074610a9144c0030350700c40c80e107005540781c41201d0300b040050030051503030708858a1000800030b803414a02c00b00401c11055001c00289107000715440840d80c80320b40242c5051840039100d0701c8026038801c4008141c1c90340c0325182241d41c1c1201e4025030581c1040340b03280e582205001c1c80c120ba4040000303440940740400740c1050b115184c005a00041c08116000e032100c083d000180200795018000750b0051141619000c5104421080d03500000100d075510340b4141c0f400d860329089030340c000170580200e0f25000103d41400c0c4150001007c00e079611803500c840c84c0d2030f9000208000c1c2072041c0c01089a0707040c0d10340d0b4650300164000c181800d011b40d944c07401103000036250f401c1102084007441000140b501d1460a00c01c2c9414410740d070b10b444003001b004003400002c010101d0544c00691b10f18203110240c882d0002c0c213180e4402c0348 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 446638983 1250 446637733 446637799
    0x5090f0406050613091404020f3a14010c0207050409020d0b071e0f0503070f030e07060f0207120203121c0e0109020f0402122404020301090515030a0809 67
    0x41e015004440d505a25002c494450804100c02000d404d1b0b1741c0701d0300900751030080d403040807206404c4262900c1035490380d0f00c621842400e24000410841c020001080390024948091749139000014401d40361110300000c4c001400030b11204034600d000031749451540c055035100e9646c42820106640300c3c440c0307000c62139900510f0003586080c52000035100040004000c1c003503510b901d540004862241c80c00b41001d0119895407804c5480342d0704c0c15141844600108020159100c02212080d8402c01c818002020180c581d908006400c00d0020f0400459411441c0c03030550494103400141c40c0002c02c2c1c04114494800c44da03c5a141e8481d840c21203809070440103915040142c501034005044d44540c0340c4034400c454001000980105100a80c01000b18079101400b0b54000213210f60501015840e10706c005a519854a01000001904a07042138105800320f664842c01c02219900780001c402040030128014000031841d035a4118181c41074a038994010b0349400c42035003038100e140407a000089506 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 446640233 1250 446638983 446638987
    0xb03061b03071202181c08121306180606150804020603041b03060c0e010e1305061c08040305061803030109020a090b19090e0105060403022202070b0f1605090f04060506 74
    0x802d62605032a0110061169a0020580070132260980d5001502580601052306226002e100c1c207c801c8030082540d1401c400051070800064803500c074054114100d200411008401820f150307044038140c0e0440904411483c203a0043c050304041c1c101d512030340c11680c1907070700d51380c528080507501010091364006d050441c001104121064200110310801c540d921200807101d100111405c00f50001d000e900501d40180d001c040c048940c010030307071159003e04050510903104002c00c910100c1140c0680314003c000c9800d0042110901038503401c03074091032003c1d900b610408185516444180300301188940d00082044075107014a60500051a0700c0c101d4584590b8014068010500d10707902043c009045143c012078080c00003082c4034180d800291120b410541103038244809110341040845082080321241011009a4002442c0c683c0c803940030301d56542403000c515100e03030304040e1000c0d110040d150035641600354000309695a2800c11240c0c540c1c5181c4044c045001865903402a9400c000c0c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 446641483 1250 446640233 446640247
    0x30a020414010303021506090403360806180d0507030306031514060108010b04090c0e0607060902150901020c010e060c060f10050109081002070312050106080105040b03061b03071202 80
    0x4101d05604983c02134090711280301c010144002e281c0422144d9036800741400740403e000c603100e81c01c41080341241c0e11080982e01c0c0000301241c0e007000c0180218420b205030003c148254042880200e0f008081c4400b001666508020410713194800320242e0707403c01802140240906100c1c0d00500000c680020702031200d4032455100d1400b81c40507880364103100c1620000b10303189522032a07405041320061540c4506060605406202510707000340d001c0100520054002d400303640344001014210702c18213000504800c1032051210040c010440d020b81690188a9110581d8021410891440d42440c0c0030701c003086840300003140d5000701c580c411501d1040d8802c01c5002044803855134040c2418049100300c955440004481004840c010140340390452950046e00e010700760080d108452080c102003128072030300109c103001c480742684040009a200001040b240c00c00e841541000321094000d48010725002291042402c80c0c1010a06400740000010321441e110310447c100ca86582441503696800f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 446642733 1250 446641483 446641511
    0x22020c03090913050705041517031209190b0403120509010e12090a0b03060a03020d0602091503151011010204060804350307030902090a021209030306030c060702030a0204 75
    0x481e10750640a82c90000203d0401140341c00d000140a90120043c04078908140c1484080d00402c11030048101d19250003064086032001007103040013104004640b1040742d80203003000804007a02074103517070b00440401804450300014800100350010500386884e1901c0c5000c4985003102c0d800700f41c4c100d180909201c2c4a0300103403c488090403c040c00c0350350040c0011030072030040c80b40e414060361041ca010000c2100760407140c051a40300100405199116580781c01040703049545190443d1140c0c0d0018942e0b0704c5203424020640396074202c03080356003035280001a5a503681d801c0701c0c000740300350b038580200001306203d104042c50700c1251900079034945039510300203017014205031000c0340c511072486080911070840702429103005104402601d040504c80e62004082d50015018404258880b0f00032000340e00d90f0080240503a109030401aa5015a40300c25440800081c0440882c2d420400030b100c81690006130711040044100c034400c2d910070a502c00680b0b403918000e00250458204050380038114 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 446643983 1250 446642733 446642737
    0x9031207260c0c0307120f1704030507080f010203040f030c2f03120a0f0f020c0a1706090a02060306040209040f0c03060509090307022b0c090617120922020c03 70
    0x1c42c152044036600d8411004041c1c0310b0f80da41c010f10101c1d0185038030f204041200c080b03422000b00c0c012403030400b469401014020203a40560402d8a0941c0601e00400030a402080310f6004070350306600131801d5003000c0d075550030b511900341d101404101d0340191403010b224401c1e881012003145105142580c41d0f0b50412000f0303002001c0740c088d00c24003a440c4408865504c01d0110b4294010650315a0002c407440c8030203442d250101c442060451042015a0744252641c0f64540003401d00b05500038005a0903e80407407605900400300c241c3d0b9045003110310010703141c01c0700b0740e070b00316808a50158030381850b10301040041004e4800c2c846818104480302c503c2d980c250b48114103449046e12030f14050b0b0b075492403160b504d00c50000029005107505070703590000c0125403801320703c014003000b04418588058036000c851074856082104c3d401c1c0d480c201084404040260720342c040c404500500300c9182c880b54906480d0181f04901c5004a445840b85200310a110071803200c01c0549041c21900d9000c1c03a00e2140c1d0380c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 446645233 1250 446643983 446643997
    0x1806070f05180a081c08101205030d14160e030a11061606090506061909020703050d05090d021c020613020103022119050c0d0e010f0903050904050c0903120726 70
    0x4072401996011003d11070041c00344151f060180b840541458400856540d0740310f503805a0b4180028030a03000c0d401024040d41e0655042c8040c03561150a140c03031007103003035048803c268060002079080700029071804a50000208d402075845c000960100c03010404501c40ca0505c0740f6002452610309042025942c018203540380500219213442d40c4800500072075450020341141000803c000c00c000b070a2564009201d41c500c646440c50804540b81d4096061710025246040f40780c2200c07440c2c00c182641000452551601d074111008410181c031400b03901e890340a00050000b8034411041415039003e60100c2c0d04508488500e8642e034075491084540a00c0103030740e030a203909002110781d504040103000719801080d0001c1e80c28609041804108000e08806880070007d5498101c0303641c413400c0c244a1101d103d8002d4958954684202d800c01049402c01040243c9004050202d821507850000d0000400d110035008240d031910f003410011041d10b1854078402d0b40c00d0035080042c00e4074494101600744 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 446646483 1250 446645233 446645263
    0x9051005180f0307050f06010302011205060d1a160e0112050907030803040c080609150f040201170c0702010e0406080a02090a0908032403011a0d0c0b121806070f05180a08 75
    0x542d2080c03a07515840300d1083c480603000443380341d4400c040103002d51185402c0701c0014203800109031207a9458802c6001c40d010b41c050b00c0701600c00c100303283c1d05c50706560f4040701c0245006158100c0780f1b40045c0181102007904408943d85500060001500700442005540c028000b02d459181502c2c1080c81c4070b1003409405043c2c001c403130100b100440c002030f0003126080602c6400b095070b84e85241c4091007010007081641001486041c0c03000040c41c0541ca41d0203000070a0310103554505500015101c800da021110f4029450a84104000320300424440441c0341c1c101c032151541d44881401c0e8019081249001d014840b002040c41480310749000381907540350170503e030b0390b21340d62941c010517080751040d144200540c410f8a41800750791410444091410340304c0c1c10002d080e00d445440407910340d00083c410350004e030012000d101c0c800f1503100800007004a900000d08a42c9400240102541c8051682c0400d0000105c0c40581c0d403880c0b40c000d05e031030800c040d1140c0c8425603503040465803001e160315041e103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 446647733 1250 446646483 446646493
    0x2070b070b011d0402031e01180b06100801050d03030903170112020f0d0b0601050a050409020f03010302010e0303161e02190905070e0f1905060313020a050409051005180f030705 78
    0xd0101e084003c0703c0d101d290000c01502100004000e0307401c101c0340d42040103061303542c1c401c002100c034400189400c90715070003101c2d0820140f43c480b0074810343d5480720b40d03c40b050180c6403004200f56650400740b810030325418500484c01d5061362900f5203030140c01c0c03000c030141141c00000118440706200070030030300d03107008803641d0b031604c0748600a00c110000c0f2110003904294540001a416500a06c028103942c809441c0282c89d0907907407200c0100701d800218002e01810303000001001907681c410340303210b1604011405580313003030042c003003400d11035410420007440c0d58001800440003144e003000d043c8009401518080f41e0004081756000c04002600820050516040c040f4243e14411b0400740c4490300040c29a05018400302d0811421108a1441d1813419044680205003529000d002e1070140041c1d000a00c0500c2d85481005040516504400d0195107410441d00120700000b4880d6000241034200082540b59040d024445180c3c6518400407440342c00950282210004000c0807050b0180c42070710 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 446648983 1250 446647733 446647769
    0x16051201140415060e06300f1005060105040605071704030c0902071b0530010c09090c0e0d080c0703050615010201141605030a0e4e0a02070b070b01 65
    0x80c881642590081c4d0071800c8003200c00080140148607c03a140c2c0b1030510074038410403a4500d1458225140181c001075009000c031405403809502440f0b81103802400c2450409013440c034024118000ca82c00500100d584040405038620781d40300f102c01035504102c0500200d6120100b0b8000713507008403411191032060711401c03004079180070b40d00800d0b180b00516886803200c1c40120f000c1c490080445030701e00501e0700b2682040a100c248102000b03400182c9924551034a092440c0c000c5034604401c02051080c8101d488030103560342042c1001d10396020a1454940041e02c1e4002e2801540d508010001d02c145001e02410351080391034400c154501341e00a01400204822024200f103064811403104c4e003030a071107803041d94000c0d00a168400202140054221540750800b40b07041e9103001c00300782200f50032000d078158009102045240c080c01d04440c05240300d0158243c0c280203407035000d1280310800410b5806a003807003448207400401e00005034a40b01c1c042410711100300c2c00c080c0f044c10240300c0c0c41d034100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 446650233 1250 446648983 446648999
    0xb1816110f0d1706091f0f0f150c02210f030304060b1003061410020309030109030315090b06070204020705030c06010e0115031a060a02011e0e06180613110d0f141605120114041506 79
    0xc1880d6940c0541a0100348401480960b41c010f0003034400c507640e008dd40c0c0d10007000e2804001a52095024540110f1054459810f02282121004a0b10109805e240040c05000c0700441900240349060700d07088580c401581d070403800c0d80200e0410650650801c2d04450a041e8181c11001462407803902e00080c1c0707940d640e644e4044510480c2100d420240c2402000003602d400d9018182507030244060340e180021034501c0034141302090b0413580d40010900c0042c401b0303c16090341500c0341c0c20241803c01c281c00851880c041220140340390944181800200841c0d000c0c400e401c8561140101000e501d000700b40d41c418400601590120b64615108100000e900b54601d14074400160250f8000b07403005071a00c410070030b1800d40114003035400b846003004806580d103510003c00c003024006e10b41c03144001050b180400101c0701c80d500704d02d00d40e440b10390090031112140c560f1b0780c112181103c5896442d140c0c516400d0142c41c40c40100707500d45481c0c008010034050600900140081d600c5410800981c0310290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 446651483 1250 446650233 446650247
    0x1713020a0b120105090a0905121e0406110615010e15221d13061a0d0b0601030e1b0d05100612060b1816110f0d1706091f0f0f15 56
    0x901964001c8400f04c00d070b144910700425184800c02c003980cad81c1c1c1c202c95144850360360095000900040c8511005640d00d0018041c50f030f040303403000c0ca10101d00e142d0701c00000d1540c941e00c0941031103003000041000039202c45000303c0f4a401c40d065801c1551420010300780300c1c1c0f02da280c40b5000d00341d51164541000d82c0355443c0b10920404808a80c2c80d8407003002e44a410050011290043e43c80c641794404014139540c1525498030188620802411031410400040a60380c03d54910001a48817030121100f0300c4541000c1079190f4415a00b0102c030607034a081140c5800a00510000380514201010a150f00907186201e0507074011a01842084a598140031540c451000c08403910318040d004600c0009103005450740118452400704012040e004056041600c0400c01000961041d10b80584590f00003445a21100707860000500d50301e411004158240002804052482000d40f00c4076580d0081e079131400042c211400301503c00729146c40303480d031404545000303090400141c2c405c0d2022341840b8409c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 446652733 1250 446651483 446651501
    0x1104020a0f050c0102040f1518050609060a050702151e040602030d090201170a051e010e16170c071703060d0204050603011d0c010f1713020a0b120105090a 68
    0xc0c0700080724403601401c075115040f031a00300100d95000c2100042d0000c4180d0303403502502081d04200c0d1408002c0502801c03042101030844803028031410100083d0742c3e0b42c0d00341c0700c2d1044c095424517a01c4200c00c904503003078424480000e5212641080c24894501c0300c0d0047c00c03c41c00c440240c00030440c40b5121240c4980681d1284500603801085100e4901910b900200d450500c1810f001070460a06200400c2c00902100e0755401c06607510100080034017418040b11160403140c0c0394141d0355041c28544119104010b0071103042d0f0100d810424071345031041e0207074401e85000f101e0300c4282e4144000003011982c0020b60950340342c103150b80c4c046a0030020300e003100d0240c1c0000f80040b010142940c248005408018484c43d415540c903086005484400d5000d1030001950101070328a03407000d403002408004100d6492810010340c0b04080c1015100307103000a4025855001d003200e1307010248001401380750240c100b071380000d4001c10340f007400a051180440c107070351040f1815451699403810103c21105000703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 446653983 1250 446652733 446652737
    0x390601030c060e060f03150f120a02120a0b070201020c070906050603071404080d020a020a1409041707060e010e0708120a050d090c030302100f0203011a1b0d020a1104020a 75
    0x354003041800e0140d44001049880030301321908101880701c020000d078004959555660000c880101c22900e000130344130b18440001c0304c0341c4098050100c0101e913110221000240188020f40c0b801e1650309080000445003903104240c1440303407600c904001d000c0d4004c1501d150440c4181c00780403850400c2ca004d00c3c81a80c3d000340c5414116030b1401c00840c0c000408404285186004010200320b481c0140700281d0342001e90f80040a6202172071050100207142c542c400700c0a03981022860302241d864103030b0107400c503401079518402c411003844201c5880c441e00000401d020b2030030307151004001064120414000d80801642ca4503640c88401e1501d440fa00c0882d840121001c00c611000d160180003d841509244e110008003203440307696031384890205800c01c1c0d001da805619284002c800700d01501c0c026540c010419421945090001c04940c0040500304810003408261002c0c140000c51780700ea1024840310860340303080314004010751524000705040d120300304a20403007415400d050080b284c00f0301c840e03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 446655233 1250 446653983 446654003
    0x503040f1707141c050a090503070f0305060903090109062a0317281d06010b0c070605071505040f0f06020d0b04020f0d050c0403050d1d01020a0f02011439060103 71
    0x5040105c07255840180041c042c066a0240030034240c408114a401620801007030201660071400c0551034018002d040400321747c0100240d1071340d80d0b80b004400d030456440f4180603001454070100215490f150081700c1352051541a00301c414075602640c0004e40c800c001204180e682c964065141e520740190106e548005000ea01c030b190610925802900302150205805100030b0000c0d00d4642041c07808e900200f070132071011811100b44601482200010190303400d01c10315000103550782c2d4070406907a012544030380f5990303070001c2e051083c203000710f09400354000400f0804410b24500b1500035081040e0195030780b460030341c04c200e075414144200d44140303004552281c284884280e032640074120083c6440b0428609000c0000015170400441c00ae00c007441d00d44101c540c07400405004c1c3c9180318000b0504560291031604049a0b032648608005902032801c1418010321900210080c441c58143d07580d0b41d002d0364030801c00380201112400d1112084420110403100d1500020740d210420700001e8007010003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 446656483 1250 446655233 446655283
    0x5070e0906220204080708012c0c090406060504020a0906030c0e1309140f06070e010e010519030b1333060804050c042a1e0503040f170714 61
    0x1000750062550004080241c9025128a10711b4240340e85513000f48100d81d190b4002071041c202c0c0281600d105510016190700c00c00107210740c0d66039806218102405400c0c180d002c1000c0c46030541001c805064080e100359541c4c2c4002e10300070202c80743c5c1d11520340028903110061030700b51302c240f00340004c0d510024000e111078081254150020040b0040444411602c0c96403004d218000340304084080c0304650103424149058840608074a2000c1d502504000f88100c0c071060320fa0b04202901c2c00340d100f007200c1e1180c4998029080d0010440d00c643e155202d90101076070b511100498021032000294001620155030600c03814501d11129a402c640085d02c5c682d07010310000b446420000e91142c0608111100c40b400800172404070f520026100f4048141038a403880b840c1440c0c100c40720f10002d146820307001d80070170540403513114520b0440082040000000b05060009482070500d889410003003038016000340751082074082d8400710049502c4902105a00c595110210301040350001d07520030305407500a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 446657733 1250 446656483 446656519
    0x20a21060e0f0d0915050f03180c060f0705011506020309120325050f0a030f18081203010509100518061f0f021510030b09100c0305070e0906 62
    0x8201c948191144520851545140300c200115109140d190316003120030fa050400d91102180d9103081c490030712a0030000440c80045150449510200c40c1e54801140c110654046050440000f00a6403181d00410348600726082c4400030a4010b2142c0b0003040008411300d07a00c0e540e10754922031040541c03c1071100503141c0c142002c2444048000368141c0349441c076602801c2c28004000304402001500c0542031300c0c02c2140800a143d00c1c0f0003148014624000517903401421034410b406444204078107602d04000030880c6d94510000381051005444e040c201401d04802160400d00c6924496245803011404006422180c8025038501034100c907088501089441c2c42c0c040c2c0a4102d5401004006003208440b80c1507a0048a04234155a83d444012001000a01e011015481034803008407800920101851140c0450216980f1202009031359440307048079800c0420141124240310305204011644942c1640300c64400c4031350703803200c1d043c40141c0020300107480c80840305a07402002002114071075007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 446658983 1250 446657733 446657741
    0x1503061005040f122a0306020903010b060c0c1c0b0a0c0912060504050705040204120b061503040b01030b01170c01110f030a0e040f0c0c0b070203190c020a2106 70
    0x203102400d019141a41c0d69021840c082c42c5940314184840c92010703600d00300301d041034100c46008103041c4c0201407085c00341ca2208941c102da00c0300504c01540003800184646007074000c00741d4403000400c400d848918402e00309403280308010005100b400c5d00b680e2090600f11007014207010a0b08400e49600c2a96100219030040480c0f5991038148420303050001012820b40825442040c0b00d4000400c01741024a40146000e5440d0022842540140018010341845210000210350414003941260b02c032135011501800408500b04642e0342c0000802040c482100000360490b03201d40302c05085680d82c0e86400b0040c0000d4007070380c8025002408101c14540c82511040103400000050b1140302c0c100080103451035100a5150021903102050402d1340e02d41482001204500300078103009502002d0402090144000e2009001c8407840303000c644121f01c01c2058980d000c5810180c4d5030300c0f80c0108000342030803032440c100324803462414002250200e034078000a9006000380342820030092081d83c030740010b8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 446660233 1250 446658983 446659009
    0x307080f03031909080a020102071106040602121608070b01060e0103050f010909030207050303190914030a0803041401050a0f0e010626030715020714030313030c060f0e030c0c150306 80
    0x2a110b01d10714005ca0780d900c000745402c0880b0380006a54148078a030105040d407408180078400e0707809002c2040490303004542402d003045c511240b03a0b500d03094480a5820030f400302c1c03400780c00e041021450780b041100811803d03041c0c880c2d940310f0404668244004400340c610441b105400718aa8a0040280038540d402c81c030480c0c1d00ca401540c403805e8583c404a89103402c4421034602c0032402c1500d0f0410a0741011255001d40f05850314214914282e4003ca0f9036019256070040100b400040014188203184000c4852641110024004d07402d00c140250090500b4030000b028440c90144000c440300b805126040885468205820000031003a88440350100355140f10191030000708060300006174507161482042070724000068840200d4180300f00b80d110410103500389c541c41001845203000c0392001c58a00241e2515200c0e20081c22883c2c004040c02425060040c0c00e4181821624840c0e404009015032480c014101c0c1c03580016403041101001c00c0d444080e8030008100046001c0341488400b010380303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 446661483 1250 446660233 446660281
    0xc04030f0212030d0c02010209041503170a20030421050705090c09090f040507050d0503190c060507080601110a020a090914190b072f0c1e0307080f0303 67
    0x30400c90301e411030150350000105c940140d43c005016040b0b0b03d840d02c201004600c91000b051012801d607500c040951098103e4078200420100f0943d2589118404036100c08599004403840c40b2901c160482d940c0d0854050702c1481d054050000c5229106280d03951461900440244015807a0105206003040068200b942c041802c000300301850310388802c61130098803040c10f00f100340c0ca400d00780a070914000da00098440c500480900d00890360000c190303140110f500c105980e0822000c10251481700c03800d1002040e8904050070080d0b41c80d00300c0304041c805c0310280c849080c0d40d0b072502800c40d110500000c000350301c010114070030300011170320703601c403038056482040c41074a52912403034418507058618100000c1c44480380b901c002000800e60b8078a070868030a0402c2c08805520584850803190880d5020310b0301580c14850400a140c1001020740310300c000341114841344001511000d03107003001c4050340d0103446071940000b01030303d00080761b00742170002c88003a5045480e858040d4003074484002035444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 446662733 1250 446661483 446661487
    0x309110d11060f0706061a0d05070516060e0105070203160308060a05060403121d09010e190609061d0105061c02090301050a020304020907170601120e0703050c090c04030f021203 78
    0x50350780b10180108290086400b031280c4444c0c05150441c141e0303a85800800b070352920400903942d0b201d00601030714012541039001181c00d80c0e400c402290603000303103105100703a4a00e01d041170003800807640c0594407030041c90f8002d1000750b842c81c0040e81d9130305c5518200c260307105c0d010f031042d40030901c00d6622076080344000306140c40f86a95400043c02d03030307001030300269a85008114890a0660003006440150060106002e201e6440f80001804600d05200d040703c40c2420700e000915105000c2d4000400c800c4900041004c3d0b40c44101406c010700d402c3c05500818000a05070740e500ca5000402d1504884005241c00d1a01940e100038004400b150030b8040e14032902032107c0c1643e42d130280100d13813003800d03051001a22031800340100040f605000e042a01032207950340000c1481c2c41d21003a0316074004400e00300b240004c00c04031210300081600c04940c0009014041d004402c00c400465113141ea2102124114042d4030b6051849180e842280300c01004103d03c8142c90005082c1300601c001c0d0140d0311016a8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 446663983 1250 446662733 446662763
    0x5130221100606050c0706090305070506030603240613050118090213061811090108070f0e030613020909030a0e0d02130513060e010b01020a11040b1008010806070309110d 75
    0x419181990004004130320003158281942404008401c01002c107031610070350003842e40d104c00c1e4864125000b62805035400000080440e01c08000b83e140c42001c07988080c01c0680b9003034000742003c1e82920b0441c4517404000c0c44c41901842806501e05aa40044906450103000f080c800d00405446800326041707007809140c048407070300c40c0c82050001c0c11a8203003140c4040d0650f2400b0122000130141010050092081860a0b68400d8410740e001d905400d010340541040103080da60200407683c0e80368148509010001e413401e981c034400201c0ca00c2a15026040d4071091402c035264014a031014000919a9407034040ca4075110340e01170240c900281c00c020304180400042c001b5a5021079442c81c1212550501504101e0b0034850040c8103840030000b007240b8100800003d4a900f110000500701203400034100c1f406547d503500c0070440310002002c0c03086924007558041c003000001d128000042c0a8100042c01460207402001103456200090840c4c420034541080300c61141e00030700b41c580c100c011f030501d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 446665233 1250 446663983 446664013
    0xe250c05100e0a080a02011410031119080109030e150a020a080f04170d0e03070612050408131805070f050910090e13050708210a02010b060f0d05130221 67
    0x4011760f00c4c85038004210707440e804440200c02c4102514415a40d00110002c0022990300b102030908020221000303002d000600c0910020b080080c1c000c0c1185501c2d04810b44101900320318003040304e003801d413050743e40503400d0f0321090180c1c0211810b410150f0041c10000c1300103411380c4010440118041400c608090300d404602c084a44045800c008075848500e0320341541d508100c80c03056610080b80100416030070301d003004083c204c55800b004074158982c00418100a0110161740030740580030825640680c0e80d00b8041d07030310205810588a107602e0070010a03a810310807503c8481250107515201d240c591031000f80407445412600b10b008105c1628400f090303007920001c0060040e2101603005000b200c8904001d0b04040c143d03032140c8415400586c01c0d031211000e84519100764800e201304680c80c1d40c1038100070303070142012009940c2d00000006880c22880504000740243d051503c1e010001ca9441102c00c2c03042d803070380c0c500280d40421260b03484c5020740507030580c000e100040e20058403a510496001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 446666483 1250 446665233 446665237
    0x3181203080a06030c06140403050f01060f09051006110f0105070f020708070503061611030a180506030f0a0f06080307150e06012d0e250c05100e0a08 66
    0x1104224910411242091641c000107442e04491804001c102151a5076140d50110340d0911801d030601002c0c2c5c00b641440725a000565005603005410390b840b000745010b10328003d0049002e844150f0300307112004184000c0600c21035110b1818444a240340604104041c3c0e642100110310500a00c1202141d02d104031007070240c94002c3c1010380301e04001000c0300c02e0190405101c0e400030003031913012000811007642c002032501c0e080203105001c541124142e81c0102c400c2d501ca03608034521840000303200c2d0015039104480802d034800720703040b403962aa1a4410485a0311059030200001402d400215942c40065805099411801200040d0740340c2c0d00c041003411908000d00a030b803114203841400f491901d550242442421454014220642c10319025803035140c0f1100e0000100866032000312000c442c0c00034208090415081519040c0c9007101d98100c01419030b01180c0b0480d40c620346c129510500501d100520709501001421a5400f0b0014600080050030f8a100e628407401841d24085014400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 446667733 1250 446666483 446666489
    0x6090f0a06110423280b0f07080a080714160b06031606051201080f2104090e1c0203030705040902030a060b031617060904030518031b010311090307120318 68
    0x48070751304003d540e80400801240e03030320001c00801d1100d1200c0d44507102c1003460300c0c152044100c0c410f1b01e981009404401c2e600510b00c0080c15003030001814490103070820070041c46104559681000020011070490700741c0151800070452200e0401000c000640c00f0080079070006001e41269070301e9048583c1c001c2200b807294807900110344006805c1071060207504c2c1c807070f014001c580d00403c148041c248a01e035586c011092458410a43d480d40b103101e091441c02118000d00940c01e00340030546485984540307039132014014021048014000960884c0040180c0e44109400e4440c107051900e000d04502c069400108200e8140740d0750000400c00020600245004103c4411042c1c001c00781c00101411440c0040c0900c12407118000800c1034581e1924102075103d03625180203900c1d000a641c0c038a2040d100343c2c403069814002c141e501c031450758020680c840a44400da07020b001400c5541110b030050300c1071440450b010382014006001803800354200030300592107071800d51022040004030680201c0307550 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 446668983 1250 446667733 446667779
    0x1050a031410030c050a14120c190603150e1522150602030715020c0c12030a0210180209131a010e0601170a0b0105041707050306090f0a061104 63
    0x2c07010300030300900c020b03035101404055620390500382c207140b0f14903c144009020719208030110007001040361b40502451000035005048500091904500d0000490303190062000103858a00075142144482200c0001c07546648058001398454125002c10445007442c081c2d0407103890400001c50160000c10050020042e82c8005100c150700805801c02c2003199001d01d04642c014040200450407500344290107015040005070b90300103d880003410002046031440e03000c03001400b241c00040d0080000c11041455900341e4410503121740781d082c110f83c0c1c59030000f4a90384191005500500301800b050b900b18001100700c030b2103901c2c3d0350303941516941c17401102d003454550000100094100c1c51032581c0c00c4413003428111040d1044a400040b0148020710038000d027034a608004240340d0180702210050300c1d415404000e50008850229960302e12841824024403407080025890480855400c0c103202e0110040d04040740389485000c00340030409045100c2c44020880055100800a101c100600602d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 446670233 1250 446668983 446669011
    0x6030b0a05011403120d0f09080a020a060c030603210e030f0304030b0105151204171803070b1c020a02070b1204060f0e031b1507080f060103021801050a0314 69
    0x44540324241440240203004c0d40c89424411101003400007a00d0b840c0d03020503000240300b001d0002d1800070300403084000c2c0140000154410b12503502144010f4a82e02444040c42518a034080072007c959162202505800e811030404902c0e6014038591340402c0030a02d4000c00c010f0107000000d04024102d08800d92a0780300040400411841040e80740c0100030454007500000101c910a400620800603140504082c0d20700241c10000c0041c4d0a20540040031030081d00e0740d402030003a10420119002d928402c3c4070b1300c1000941c100c004400c54070509856810b00c441c01c0c501200c0d50f0302039080341d140c40b4194024010081895461000a48002c0911f0b0354054220304040c01d151040380c1010540840150505080c4804030a000088801d130981c0c0e0030112054044200005080009040750909440d03a10014021229404003805004041c14100b0b040643c44200040d0100e2080d2030911180005000031005250702034000341c44030020904000c1a02c0429440c00304584000b241e100c5591300d22 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 446671483 1250 446670233 446670239
    0xa15060e0f100e0c0f1e0a03020705121e0d11071520090607030309060204031b0b0c07090b12060a020408010e030708191206060806010305091b100306030b0a0501 71
    0x44103900b00101450600d6a2060501c24031880b424410024400c0805c03500142c3c11051000c0d0340e02c024044002c0615480e192140380d08010080d51080344241c845100320301d11121a40d4030031045600c0f070929440300304030030701c0803950f0803800741c0054080c0f0090940d142c0c1c03415240f805200c001e01c8614405d6008028850850285030111001c0c18902c04564a10001d4400700415010031184178200454441e5181c0d0450310302100642189080100528004140001000011003420010380c42c0440550580c640b9120f41c08442c0c081c105241c1c0d416480b035001003104110a50107903107007900140480880d055010360280c94800c06542c100d034141d500080400c042d80c002e00c1140c8800e5480c00c091442c0441c151a030550310300401240013050b52035800d10740c41c0d290188421094210210b00c013484003a6581708042c0500d54200e80e440c4c0404e0401d00000d0b00c0134000320303030844401103801602402011140600c00d0b00500c03c4485418140e44010100114140c1d0040d1841010800004529581 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 446672733 1250 446671483 446671501
    0xc130909060515010c020405100503010e0a0611180d060f05070206430207051203030703180f0b19090b16030203042019080d0806120a15060e0f 63
    0x80c000b010f00e001404100e180c05102c1c0c0e4010b01c1001ca030742e011900400d840c2c0340d02010f585000c44560000b0340c150302e0804083d01381180802c4482440f4010342e410007044501801d0200d192184007902103801c201c00d500d40c0070301c0c40c09200042100707010b503400103404d54840e040001110b0b02a544040964049010460b00c002100e19400000d8040c1c808440001241c0f20603000704550014064a0300d100d104505400ca4401c10604008003001800c0d111491003020b41d4640741d034001c0d80c0420003e41805904507044061081d0180645e81c001e12080041e4150340300c4403103661010304410b10040ca000315800984c0c2d01400b94100ca507005100c400c6a0782070460340340740700135400e40102050600600400000c1207404261500030004c0d207000007815907050000501034842e800d140f4981030202e49011940d80c00c00901641100c8060301c4206c1640c942d90100030040c1080681c04031244d121289260001d040a01814101000c640340841e6450315080940b000a40480e10b0105064015003000600c40c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 446673983 1250 446672733 446672741
    0x20c0309210d110d03050901181211030304032c0a0f2c0f04050703080a03050711070305030f09010909060603020c16060c0b04050f1006090f0b060904050c13090906 72
    0x3030003410507035124030b03002841d113460b111510300035018183c2e0381d800290000d41c290014010040e26007030a2030307078414030301c0c00b4101840d4203c80c0c5c0700000c1410600e100310700c07800001c480c003403a050b44401d05070314014032400b0712401c04420088070320b28a08012055a890301d0355014041d108034003000e42041e0511010141d0360a079450415000383c42c00c20ac001800e10882580d83c0c03c1040310102014558443c10301d1407170701c0000d510040101800003004560694142e1003030303018061a54860107018024520306a071a1414040648590010030212007611034400c010121610b044c100304541591321883c80d8102c41007175202d080440d800265450309484140500500b2809001d0116501c50404a00820142070058005c00c0280c2d100b0101d02480010400142d800000c1c1044030500488010a14060b048038401c2010403410401c0c3e600c1992024043c0d00410704014040908116401e010070010b04009400303207a444a0410100b07040480724010781c006084540d00210f1600c0036403030f00c80111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 446675233 1250 446673983 446674003
    0x3030209130b090105041d0a03050a17041205130803040306020301031a010b071502121501020d05180616020a03080304170405090f04080d0612020a0608010e010603020c030921 77
    0x2280361400c0c1e10125a9150f03d103905440c429100020302492140e00100b0b210040340059038079101c0d80382150308140e4802c0091001d15203642d41c1c0b03801c0f2030180c1007018850740180d5009051056441d42c012070f82e1f1140c40600303e0070b503820152241341c50740e9903c142d0441d4081e400c11795401da00000148184401405030704900000da4580c541c0d90340c50038094000741c2c062054010544036200d518081103041e40d4068030407105a1104529450a000300407420030716407520603e0160213900e21f500702c0c280c015010b50388101122440e100a6281100801ca020b51204c005694201c1c070780c59140002d0380305c0d4142e1401851140456a54a003403034140142900158524640b0b080c60401040c0000e803600b03501c141d004013030040320400036103451404180c01d009107039003030210610b020000540c040d092200204102d009580c0d40152944400048030718282c00d000c2c400701d0307400031001006094800c1c0e000f0110b13422a402030340e0600312400700043c0810160084081030160141109950040078000c501c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 446676483 1250 446675233 446675269
    0xc0b0a02150708070c0f06020913050402040c020123061c05060708010f0f0504020306150f07031403070903080c0a0501020d0c0f030e071a07060f050702060a1e0e160303030209 77
    0x40c51804c1d030801040240400e100030030100b50781340000104900740e01941d07810100180184c0142c4081c0310401c00426003210164803031400c09524280050061041700c01220600591644000c500d84061004c00400b038810341e00440502ca05e0300300030030080002c030a0284103801425250429002c0104542e5040c1c000c5030100e080c4400c1004208600300040080794402d071801358882d91072400041c40d10310045e2615003400400203d15000d94041002400541d00c0383e01d0f05024136202e204501200d000844240e804545204018004960f00801420005203404211900b03012030356912402ea0f0803039004025016203a1034080c0c02607401030075480a22140b8a8100104d220074802e03255540380a2250a0840c8116641800400645011500d081c0c3c0c02480134445040c107425004020107044a00a00601070600030407041007090003020081403801c003030540c4c80d01c5240803540050411062003200ca12805404a01c813440b014068001103001c1d03180180c4600e2490b0a000d00c484040300b2440b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 446677733 1250 446676483 446676497
    0x110a08030c0601170c0a240302120c0309120c07030308011502100f060e090d030e0a03020606010f09050d0506090615030703060b06040e0406061e05010512040c0b0a021507 75
    0x101c0288006001811941081e4142c00d009802600050914000450007608144000c0c0c012442150b1400c42d101c8001006081592078018480e0403000c0340148813103d03001e40d0b01240031400501429001c3c0d5040401c1b401960062252a03614080300d6000481000c5140c010701c0c010030505801840107030051a00c4444014401d000c008001d44426811440c2c10030349a80780d80548441e05107a2080014085040c3d00008078101807c20907581c00041c14043c0c000307030400718140c101d21004148201160380c150010541038a5807001503d1101e0000d030b410b0100000810006215659010304100c154040da01500c081d0400004280c1401e0000701016016044c0340003202098500142d11011207401c072a00103990068000058490b00c1907900c14400b022035401808107020181d0710103c110341042c40c148100840c142624a1100210700c40c80d80030460030711480400c00b241507500b607031085c4590b048180c0d0907100c202c41d8003650813440310301c0c0040c7e11103094114065007040e051500071029080c290 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 446678983 1250 446677733 446677747
    0x1914040f0e0c01031a0406090f0f0605010f21050a09050606040c0225030629040504030801060c02040617030918010b03040f0c0e13060f2f0d0504110a0803 68
    0x36a88525510b01e081c10503507902e81464020012041004443d4402002840025a500d2860b40680021017031114504c0c80c10074404001c85051040e20b08940381071f110900150303e07941c42500c3c4043c0215981066908804480740001d09502c5024030a030026800020700c600d15050040ca490402000140a285013803584141c0c2c94000401c01d403010800c0344030b402e802481c00d441400c001a1580014000f80c10b10103040840032185100460380d4411001c4800200394a00401090354420b40c0c021380420f0440c8010300c6450300ca00391103c2080e00107030010803007541d02c40140c41f50304c1140621060355080440d07843c0c0f00d4501018821881c86074501114450750400120051030300c4080c000400d0001410b0405003004000b114100c010856110986030616101c0d5081002405800044982515218460352004000d10812030090841e1102681300c110101c020158030a00030b000e0903081c01d0038407402005041c6405564403562091040340c0740c04540700c0a00020003056081001150010310140c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 446680233 1250 446678983 446679011
    0x40f062d031a2409040902030a0506040510050c04060e0418030503061206010b0f1308010e0c1807021c0309020402030a0603111807050310030219031407061407021914040f 75
    0x30a00e48820014404d540b03442d0707003001800408200c1c4009400d40070704503140090103004100f0520031405502601c5800b042200329130100c1d80f0442c0c0051a081b420300c03007440300601c200c48945d40380701c002d440040c401d400c0400400e030f0700300c2002045000a5000003007040c035003031280d007484164086000810780c9504100300940345000781004ac00a10f43d002c2041d0b954024200c90b1400141007140007040644001c00b8082d4a803040c541d0040d0041d6200070380f142000308449003d62007260350383e014050340c84040d007076240241021000c0401709519442e640000d66941c0c4021402100b840c034001030750f075186203041303c4005070048005124104c034964a0840d160442409a8805d2007441c11a40d071380e45207142585280b0442d0006074211401968503007440607800c10f4841903c0c01100b180750030070286400306a40d20201d000b070200045228000c52100a030201c042d228551008002c4c07a00301007882d6681644110039403220745d01c2c1c00c009001d1502401c1a20890720410808001400001d07080505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 446681483 1250 446680233 446680279
    0x3021305150103110d18020604080606101d090408040f0602030c011512080d0914010213091803030218060c070306050615031f080d090305060606040f062d031a 70
    0x494816038589003800c01b202054060030200541c010a050349440d1650401030386c41c40e040324035078012501c10f80d107444110b001e03041c0f00082824030303c0d441001506480920151450103481140d01c450281300100328000230144840140403180c2c010741d25005c03043d06071420340e83d100345602e10398100c0740d07400c3c000b5904c6e2245811810f0781168042c0c0e0784e40c9801c0c8017503008040880740517001a04c542c844640015041d001091500071090006003040d48078941e210448000e280c004461350b1081034402c0002ccc0c000d401a00d50009007111040b240300262010509680c809180302400e13801020301482007281c10310030036400c42801d689414100e40d03d03144414082c0300c041c0c2044000d022103c4c1e5409640f010205000c041d08c3c01000b07a0342c0803001c4400c090103c8075070f400211203d00a00c0001040340c1000e0042c1c82c225860042001140d500d4413206407010000191441602910b4101450141d07204400c5a001c044ca29500040e07100c4990780031301c80801c0c0c4084041d104200c440182100d9125080c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 446682733 1250 446681483 446681497
    0x1090c0e0a27020a052b050a0207140d090501110319020f0f0d0504050f0613060305180c130504020a080706090e01060509010903031427091608011203090302130515010311 75
    0x121b2201d041d201c6980708451200746004403540c101070030019041015009840703a0303441200c0d03154410940d0802c85803187c852603246000961114003c03c15903110790010b109d91066041500c0c60901a01c0c5018960f46a0249840160b41304210070031009500700314080314201203502800051480e0b401c02810362145100b41486940300c0321042000e0707501d40303080301e0b04901280030f014005a91410082c0103000b0441700700442000601d1200d00850300420382c1030707095070f000b400c4c803140d10840b41c0004c0c004c04000e04244e800180c4144042152003007005501c004c2d1541d5228000d101c0e1400d1441000c40105030450800c0082c1413187d602c1c940d070040308100541ea032500b41128012904450725145000d03c088400203070302ca403055444001c20050403103400a4082d0743d0721005656040d52006609601000d09000500841c01080a003071a40042c0701000e221b45080390440b60340340c00148405080c0d222080c50945d680040c0483d1425005111409510a00b0107002d00c07050a040c00e0414010305c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 446683983 1250 446682733 446682757
    0x6010302090709170c0a050105090a0314160305152202010f0203160804080c1c3201020903010516230d0908030a06090902060301090c0e0a27020a05 65
    0x4800b081c5440d00426488010740681010002c2248109526075503074098400719600030312aa1002103802c0d44944222030802c0406080c0c242a0746c40c540e180f2148244203010a42c65010300c19000b0712640050041c100110f006800901503044403c080c1900c60360302030644908000c80e1121071079007008049401c916a902400d00302103543c000501a41140f043c540150805044410000200325201001c0c00a589111007200c078003800c03803000c0c08502e10401a81d0114190040800c070001800f181c001072083d0b0741510910011903000440712141c001c8904118883e0750049643c0c80582800d100d80d907070010b40804104d012419014001e003400c007039a4101108008106103807404010004210383d0714946140e802c0002c00064106809150401d03541d84c030090b803c020001030801840d00401090640040102d072940e443d20358000d00903c05041c100e01481458031241e115651020500e80042084035180440f2400490042c4a5120281d00c041621403060000b01ca11507844420b440e1403044078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 446685233 1250 446683983 446683999
    0x6150c020f0a09060b0703110d020303060d0f060504030c1101020705010e01050a0c0c062c060906090d06050a33060e15130906150e010e150c01230906010302 69
    0x1c90100c0c0b001c1ca000d401405160781400000500c4818040050900c14003c2c1d64030061401318000039a212803055940000685c418400b0488520b0700c14941c401d29845484042e8440110355210030689604550a0380824040b03104076003480341c1d02a00481c03040091002e084080e04110028144140085920341003000c040b52a415030f9001d0710b64220125080300c07165400650702c1000034281c0e10350343c1d0340d01c503403001c041280240e01140c088140e0300f264000780014140343c80101400341ca604501642e96102070064103850210308640b00d1a40180360140c008107800080044e10a016000005084c03403005d40541408115501003c01e4400c4c0c0c0c10900c0c00740d00542c00c0d00002aa02c00b120048034a543c0e40000f0b1940a072010340711071170215108500305204890b5241c03481c1d94505944a1940d02040300c421503600291f10842c51482040030007403900441910001d0060700c0c07500000b1360000e5980d955004201c45050142281ca0901e115092045443c90004006515240180f200900803908 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 446686483 1250 446685233 446685259
    0xa090612150902070521090603070905040516020d090302090f060406051002010905070f030201050a11190b0f0609040f080a031103071806230702030a0515010906150c02 74
    0x1290304500c0c00940100d10152030642c840c4030200003948081c900b11814402d0748001400c5c45007a0803c04400345055101e241001510418003000b0342c4000c20a00420101c18000315241d60b4600c1990301407040ea260103241055072500c06494403010300500c8041c00492a000c2006a07904412250703c847c020741601e806444007408103019103100d402459104840358042c3d010780d6815031103002014014000c98004075950184c00c0c1c3c480b000e50201a000900c108032000301c46000d0000402d45114140499070581160082507243e0980d403441115406844010f1068034841d080c0302a0708007400300c1740c80d9810b042c203690b007106030002c141008041c6000804da146941380240d2040001c1441e600016030782340341000c0010305080c1c4441c8420208006000d02141c40c0c1d105101d0b1b50000a580d84400c0d9580c4120440318a0715000104120381c9032251950100c0000c806100d40c1c02107411030f00c180c61665060600080541c2c1c07a942084008c502800226416940d0002d00e030783c002e54060790b07c00c0d03070f03000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 446687733 1250 446686483 446686517
    0x2d030405060901290607050a080d14040b04060c180603020a081006020a0314040506041202010815060a1808150906011211040b310c0903171b0f1b0301020a0906 70
    0x178004c0047c195026294041d01401201c1c001880c035034105007001c000110200450030b20480060b6005450a88140005000240c1c954030254160760b00d03083c008101164004e02640b007d41507042070002a070041400280c80750021b0340c1503040240162010301240c01c02c0c00080d91b40d542e0b19030240400c54080f131483d00e01b0003000d040740c000d40800f4001070740d210380301d01440300515403c80d8200d00040d035040010701002c9060f00c200840500c0200b0342441c11340300ca10226400c90141000e0081b4141410b000990385c40200201c61484045494003c2c861501c08905801c2c090140c4c80420042c000100d81800a9400800c02502e100d04031000903000d020440440d2040645050407a20701c0140040d04036140c1030701c0c00d0f5040e500581d11051107005482241142c2e240700610000f44620b501600c0e00c6040c10260014100406403003c00c403100710f02a03440a46802440d507091a9950805580c010f040d142010042c440440d00b94000d510341003a465004182402902c20f145c1000b00d5402c01fa46608 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 446688983 1250 446687733 446687737
    0xa03030e0a0f0b0306240406051c090309030206031008061306050c040806010b0d0204080f0f1e15090a0f0b070e10020607030504050708030d050f01120312022d0304050609012906 78
    0xc1401b000c1035440c0e80d190840504140c0c041c520704108100c2c1400c505100350002e01603a58003581c1a507580345c1480c555030034442c0302c2c2c00141c000c16080360040e00201d0070031410800c0d0b522410800412105100c4141031501c101d0700f000c0d000544114013000140520380d00069040d0448898801484d074807844505071000a00640e08002c81901a42214540030000010081b0351482140309a840340320281108180d40d69a05810321140c1c1c0041c0c40300e903181d40418030a41c0e03015041c0c5056400007240c82d600e0144c42c0121150440d80c5005035802d010238940e0001c12100d000b0402e442c8056200080c1d10040c2d5501c100611420806855100150420a09010401c010314000e8100c030b0315030040d14401c00162904683c00341000c0c11590000640c8002e07a0400200e46405132505a0301000c044208406507114818070608003190324003100514010a0a01d40800d00d003105c050307100d041902e0303ca800c1440180046455070b0412510103080c0500da01c00010940454034069240c001078004241e1038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 446690233 1250 446688983 446689039
    0x120d141e030408070314030714030901022b0501050306040309120f0b07020106090e01061d0c0906120a0f0b221401120507170a080304050c0a03030e0a0f0b0306 70
    0x400300801440300700401840500100b030f200e9200d5040c0c0e2090380d0b00030003c5020446050001581c940e100807160100080150707048220000050320344407092a02e02c1c1c5118222101c00b4140f002601d01c00c0040f2640e1055501418085000d8612810242c40007810000c0078003590a0031500c0851400c02c02c5121a00c0d0b1a009600c102558803a20301060080c2c020011b80c444c1040305070800400004544040c440c242c103980031000e030001140b010b2005c082101c10020088007900ca01005a0015a50703128080c002ca421030844131149031a29602c14002d90703d104107008410390600a4890280d95160b09800c00210440c40d00ea21a1504c000700c1c0d0b0150401c00d11a0740078080b508000b1400f0320440400c001203e00810845000c25641c4000784242c012407440e80c601e58001035180000111500015038006006404890240154800140d15079403ea40201c011406020a009641c2007105d202e40091400c2d10494811178600114500a440001d0903503102d030700e450403600c0c28190000740d0070b1f800f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 446691483 1250 446690233 446690287
    0x60a0309150615080412110f0f0307020a050d120e010509060304060e06061207060c080c060f0103060f090c0b03060d2021190c1211120d14 61
    0x341c0d80700d8164540061801c0e008031641841c99021200b0018094403034a4000c2e640800c3d40b00e070300b25500d4803c60740040360030f010410b60b000d041d00c1560404001c1004049203802c84001c1c40d40d42e8500d10410181e80030ba41d03c642d000300074501404020401d520900d1280a40d10b003851001d00441000480305c0d03104000702da5500c40804005e0000740881940403660040e10f86003110965180c804c1080707540d180c4960030400d140c0c44604140003039403240d044050705e03520030030403071342414243d10110341440012500a1042c1382c16100400520002d405803c1139000c0e02201004072b004140c491f0303503440c80140146044c0840010202d503140d10340941ca00002500507206140181810040840004107446503502c51034090400c1c1c03103945540001c0039000001d020041944900b00d9030740c100340c00103888040d00d141e907581100255100d6035a201c40140e0b84541d0344801000150f80400ca120113583c1c3c4501c1140c0d1003401c001c00d03100c2d00010140d003401a003014268464115034030300d4414400403000d940c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 446692733 1250 446691483 446691503
    0x903020d1110060f05090a020c07060c080708040e090d090f0b0304020a080102040b0316020106050d1112010203070c0302070906030812040f051b040c0201050601140a020f0a0804060824060a0309 85
    0x10307481080d5013a01007a030301c04440b08456a141d40340c860f13050307000d280407002c1030750090001005054052202000300c1031040a41701d0616116072030b81e0003a6001684a402d070304404004210300700c071080c854940c000b60f0740d040c040440341c1003017072041d4164a02e00883d001e41d840000400c040d5174030080c0b004001c042901c000c1d9a100d4490382120015001950740c80c5c0303000300b0419645071460045c090041620000389c00c3c2c541100d05500c420a001d40d0604030705810803580100b0114418086c002540301d40c0483c1c80318140800c2a00d4001c0c41c00c01e00358011002c007890500709100007040341c400c48900300c0c1d2480405000b42c07200e0401c0c040d1424109802000c1d0300c42c00d048600c6482040303a10156000c01200c0812418104901c180c1c00d0300c030215041c50000f0300d94000314050f00580809041441c0f40d82c8119001c800c0804956460050914001d84041c40017007010000c803940540c20079482203960030003001c100310025039259a10030b90f00c2d050f84100310104250b002c051213540f00c048019000322100d6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 446693983 1250 446692733 446692739
    0x60308090108010b04052b050604110114070c060f140403031214090601030219030506010b07290604090602120403081009020c0a0803070c050d03021207030903020d111006 75
    0x182250340440e2509020407240d5000043c41400401654110b6074003800703d501e088104030603441090010340552025034072103000000841d0082015911a0317215281100640e44511f001525054040c00c452640d010704120000014051054010488655003418455614440000d84a0389035001c041d007503c00d40464008207059100000c40d451421035030301000749490054007480c3c02c0c041111542c4459001100403c01410176801e2040b80085119007400001d480c0d944483c02e140342a4010840c5603000303ea81001c1c00701a80740c0c0c00280c0640d41c0b20b0302c03844021080c500410480101121300c5150340d482c1b542c082c0001b40c1c0480e42e001d00d07642d410b40780c0c5150900e0b02400c4180d0a072030541809180ba040454214030900c01c490100d007a0350000c00700e850b004e40e1100c0e9150320040440040089100308400002c0040101e0000030049440158482031002d419580124004008104142c10b10020360b01281c1c01203003242a600861400c40b00964528050341c1c54680c61030044284c03149401400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 446695233 1250 446693983 446693993
    0xa0b15061c0609090b150f0627120619060306022805030606120a060b0c1506042304061413060b0301090b060904030903080a05070201170118110d0603 66
    0x10140d12560840200051a110450701d81140c110010041800c8017401c04504900c24080755180b184200402c0266800c0380c50001ca03910b50044110300c1480705a441e401120b980c244289942130400549044518900700310700d199a03894040c028240b48140c0d140020403a0b2199000300d8051500300400355980c03024001803078264041c2d001c010545a01080006402c5c900c200202c0703005400080c9000c0c00c07d640e032007190202a20150070400b40c00d64806000520b190388002074260605400b0240060b50240d004048404a00030143d5128600d0174003d402100303c0c1003680019008054400c1350300c0d46d15890030310300401942c10b1907044190694200009001c0b000300c1819114415802400311608a405241c262110140c1c02003411101400103003882c1040554561b000d4000c0c50b00000c1c855881d02c900b6400e61080d5202c40005038005200429560040f1700442108172411840e4010b614054250075500000e00c0a08881503c4000c80c02c85130140d03000b550382d454103c039810001c040e501c1c502 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 446696483 1250 446695233 446695267
    0x1b03010e0129030105011803050607020a2603070e012f01061a030610021612060c0206041722080714030601030c210b1302040f0e0a0b1506 61
    0x15a041c1c0b1503840300c074003403408480c4800b2249880e0803441a0542e402d160054400001001c90002030903002e0318000045601040034500889a0360064503120305036080c2a165903402d00340c02c0d00144c041c100c203c0c0d560a0134404407580000a864000981e0a003035004845140c0003c0d210700c0307a80854602c0754901c00140300d801140000d000020005556078003400c8498003642071010350306041c14800100a41022111440c0c1071001d48180c4040c8121528103168050260f00061600303c0c00b0f4201008000740b9120f880b0490400380001c1440340b50507502c006400204e0440c480c800038020940007001092540c6441c4a02140c0148031500e03520bc540d00c40c1d0300d02c414480e05182403851210b2042c1030801065a5060f0f03904201411642c2c0d0910480704030b608050108440ea00c00e22000302d2000c00c0707100c07040c1c1c3e000e4010100300003110300c3c1e98010002510302140d0140146841c001c0c40384a03500000031441180382d40310700c4150141d41c40d00074089000c0400c03440507810000000b00b00c40c9820a03811 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 446697733 1250 446696483 446696489
    0x915030a121821050304170307051207150f0b04020c06040c0509070c06020705030915211512070905090a060c020607171519061202090307030b1b03010e01 68
    0x52a0301c01062040718181c0a070455210316403001d03042d00e816541d00709040c00d4252009009a01712482d1564620070b0070303038110341400e081080d070308085614400c104080c010b103607140c0071101c001e42c20680252100112122882088454540d54044101540c011a0400c0341c1854006000715140c80000d19640d031030703074004c6504031182d44c8072203008031b03407031400894107070041c900380d0317074100c1300031165079900e00207521603031003070301c0500c001c0c0440e42c51542c1d00d05e104c0c4098600c5005250f21000b13141c240304000004002e004d141303200c00c00e04200d903802072880811103030f850484941c4103103100e0201e0035003007002c0340c0c20406000f03003000c7c200f00000c40300094110440d88201000c010034150a00c013240c440d0415200c0100041968131543e2006c10300404040e0441032021100c4403c14491001500301001140c0444005024641c00c2011642002d89050100034803101586000040d80000f61a0981703030000401100080b40414071408291510442c2c0412102d6100e070f903540c51b1040e4000c602c0b400d00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 446698983 1250 446697733 446697737
    0x11070303050603030a0f050a050d090804051807021903030221041e02060a0804060b030f0115060203180402070309091a090108010b0102060403110c0607060617030c0c0915030a12 78
    0x280104400c3d00780082204c0682e06a0780d035603e20f8280c400002c0f5003540c0100c0c80c41c1e0401c01c05000f911003003032841c460f02041c18401c40106584030f03d800c090000c04031b0b43c1a00c0030f1101304204104401d403a00403600d40011001080400304080007071038154020b020300200e4040c0d00050a150303651541d543c2e06020f000314090011540400070351034141400b107542410080d04503205000c190102405046070a0b08180b140002045a41e40000800c1c9880c242452000700b6079181c1310117062039001c8403c2d810241c0705901c0030350728105407490803140c0200301304e50040c001c0303a0003d13070300c0d09062203000c511000d040648405d0120034004602c00e407001178ac0903c50ba101c2d500718000003032031071014410744845d1001a0094125555075844c15200071600c00d1246013103002d030106140c1203070307074400c0103001c81e0740b003107030000b4580f82000d05140405049050744803c562080000c2d00b180440000e0f20343c4a101c0403107400d400e075a51000032549081d105038940380c01d07114036904030041009040601106103126 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 446700233 1250 446698983 446698991
    0xe0a0c03061514090a0902030403030c090f080606060705190c0503011b0804020d030905031e12070f12020709061418060a142719050c0f0a110111070303 67
    0x5211203081c1050840740700c50100342d4504000c46102040d0001d4004c5140040c0400440e6584002c1d9105aa00840303045001a0f9505084800f407a00500440c025000402e5000004c60520036640d95985001c0c0641f4461040800c80d881006010001185040030400c40c07280c03080c605141c40c4555000c45d024040c072030750034015601c8024100482e1444005110743e81c00465841e2a000d100220200550517420002810300c042440d880030040c0d0140004002c511080d800015105c0700d041141390007290341003150801004000c5030001c0d0700074110075008a03541c140200700303c10a07880c0050b01d038080d541117414603a0004110007088100481c0d420207940010346109851000c0c1c002d6441104c05641c032074204074082c00100c0e80b612801d150902c2c0580302c5001c6084044140b00c040744940b10480b00c89001d01c0070443c5042d44580c4103c2c48074002c1c0400d0010341484800d00d9410f01030074855680c180b101151440510380f0962000c090301c0142c5008005108200f01b10744201c1e800002c0c1503001c6418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 446701483 1250 446700233 446700239
    0x8040c080c06040b0706090503040b04140f011722121808191a010e04051005060a140303090d051b011107120c17010f1a1e030102040e0a0c0306 63
    0x21030305408038400201450f00e0181000c403402007a03009564150b42450303a0702c0408000403002c100070300c0988440d102940d20f1b6485c0000001d501442480781600680000c0c0d0003c8540e40c1150103c000e8900c1b40d4a0300301640d0383d15038051000034040c0c0507526803544148001c030070f108804040119044656880042281c0c0020310050b58800d240310b150a9607101c001d0700d5408170307902150108010300c1601c2003164104420210840f8800a81002a10203074100900c82005001c028000034810880410b010515101000445a103034038451140107038070001e4445405d5405200702c410210005114100c200d17001e00340f15070385440141c400c105984102009410f00d6000b9143c40c07000302409001003000600302200416015410f0100f29641040c8403404030701207039400c500c0300e00c0c8000d440001400b540810200e90a0310003205489240c10400c001100d000e8407403034500d0b45100d0300f503400f0840c01145a801700c0e00a101c1ea41c0701a802458800501c0103c0541c0e801454106d0020755042c014036071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 446702733 1250 446701483 446701499
    0x4080f0d022502180c04260610031a0612010f0c0f020304050a031104091401090c0501050c0c01080928140102042601091e030305090303070507060e07051008040c 71
    0x91038650103540200081c2090130b0303210000444c1a4407008010300241000e0340c07610320780c6d039174035542088004e620400d109aa201d000200042c5034002d01804501301401c4c80c5844410b5000110714010400441000006001c0e0312122601c5d0701c0d548210b4020003031008001034402c01001004503680c0051103000307120420713904c00070a540548600415090f0410720710360b25810003000c02c0c07030f000d90026219840031010501d0000c4a00030440301300004100c428031450f002c88070706040c0c1c01141c1403023010b020000703014400140080c006402804d000b81c3d15207514035a20310702202d00000c5440d15030201103404c40d01d0620040c2c01002e51140000c000b805035804d50031801e0740030b18002e0440c0400300301e00580004822600c3c001d040d00c408800003444010a17120180f00d9041c1c104958010b115103030584d030806d541442980e0340840710601640c158241448010140d10840c800030f408181c8230150b41a02d81c44c1400303807a000b00002025024004120701014107580d904541c1560311000070240050300b00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 446703983 1250 446702733 446702797
    0x1211011b0203120603070b040b19050a05040302041526190b040f1104060617130201020706030c0509042d091707210305061216030b04080f0d02 63
    0x8103264014506000c2c0c10010b50700121002041c42e54103102c2e9060001e502d40c0d182c8000c001a1050a0f000c903a078024403110122001c00c1c2501403420400c04000c4202c116501005032410303241e0444000c1000c0e5401d034800003003000c4580244248043c014205509800310070307043c20501020bc400c1d81e03140702d0036150702c01d04804080e001074002c1e40c4a40009001442459940245034424441d816190b5050380200e0f0031200c01d40c03c00c101090502c018640c580c3e00d51070b00c099020400030700c0038070b1070101039000079142c000910800b4141610785006604641c040c000f900c40301c182c050003c2041107c9400d408403002440c0c55505250707890b2a4012003105098000e8503c00303900300000c141a40101e0856103942c1c2d001c00c3c81030f10266400d040c030903100c540641d07030024018820f68000c2b815082003c108120f1b0580d000015506604c0311100c50400c001d101504c400f181e0b00102d240c0e096a4803800d1150303031131294400440b1400d1001400324040300b90382c1e0140141080d0103003659035590201031580002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 446705233 1250 446703983 446704031
    0x60f02210d050c0f0a09030204060b0c0a0803061c1a0124080601030b1801060e030307200f0604030c1e060c0209070201060f06050405030d020102030f0121121101 71
    0x5010050781d100350905822060308682981e00c0b00c2c0c0380055a289501c000c1e046016030600141c411141001076286c2406090301501140c0111480c1c5520714016070f81d50030f041c0b5030003042d41001000003411641c4216003601500f08045006000740500d240455280b446800d41c1800418a4400030030303001003c040e403661050480c01c441011303840182c01514883d90041410b41055120460f500046d110b003583c01000a2103000080309a5040a03005050020724901060007641b042c001040441c0504060905d1543c4698803c9450b100001c040b03003414640120541d00114009400400c0100b15440242140c0313451038091a031841c680c40d60308035403965200b1030000035403136043c010161074443c140e60b42204641c000018a41e0b90381d4024401811300d544404042030020a0400c51402e06005200d40c1c0c46c0c0751300c02145185010800f4418049060091060700082008002d008100c8c0070000d560090b00005000c00107090b0b8a8010003011001c1d140a000d0350800340d403040704101044d51a841 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 446706483 1250 446705233 446705293
    0x307060501120c09090816080a030b0915040e100606080f06030d14090a03052d010504020904170d0627050709060318080c061f0e01030602030718060f02 67
    0x46541351003400405882c0700305003514003007810013850b0702040c40b24059a00c4540701d116403649541038500080c00300c824101d00f860161300100304020707031b00649540c07490b82440100c03030000c0c2c42c030725031407845261291410740501c9440c64450003084a80c1c000081030303ca02d048140403145a035480051586582d0803c0101b030104613115180e810701d080345006841800070240580c7d4940307507240c84051605107004140c0b1460580300030400e41c0140c1e00f01310fa502a543c194002d00c40340c01c0590104102c40340081000e40780b103c20303c8402c10103400b190304441008080e0304050100c203880b00b81061b21800914440360800030b000c0d540003140c101a000b07207481b982058581c0301c01a468000c0503030213045000c0d45c00c04409003035082c00002130a6079000d407400c0d0901000408843c581100c40460070004c8445650a50452002c1049042d5038840c032507054a51000000d40c9075140e108082e05c9490620400d01c294401c9c01001113522039000f120743c0401040342d400c41e8070412403250500c0003512400b040c220 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 446707733 1250 446706483 446706503
    0xd0203040b1b010f0209032a010809120310050a090c0207171f0507090e0906061011060f06030120180a0815091006060e0f01140c030706050112 63
    0x32418040c2809440c40b0700d0a070003400150402a0500b5086542c00018580c449a021403840c3d29400c0030403801c50078051901841c0410407282d07d9603541d10711071400e21410040f810000a071a01e8040c02040c0251103580c084c0c13522402d00d0403d01d2422900b90264034098035011b03074002101000d500581c030f0942820303005460014141620700155090f10003101026104800b8071030801c0f004c881110f040d543c2a00310000b02810034403401090000198031030200d03806c0b0841071192080d0045010750700094110303820400d1403541d84082d1490010500e092403180112810050f283c40070f4a50240f0803902140200440030200c9441d2800c600c212711030694104040c800403110b000080188070440707500501e44a496039072110100d00e4046420b08411025440b03030240100c0340410040ca40007401da180043c03010b6030500000805424856183c07a00c55480300c901e03914183d006411600e003002404180a65a0b06100074481e40c0f0f034070034001281c1886c68071000250041d210200d0312046030740800606 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 446708983 1250 446707733 446707739
    0x2070809090705041e0503010b03070b04060f030b060a0818010e070612091209030615060e09040c0902030a0c1805030d0f030b0418030206102106240e090d020304 71
    0x4481005040d101030100c10000452005402045d43c0345010b0780c1340d640312101e4200784c149400e4440608516000368006401800030802c08010b9030181c1c3c059180050301b0380c0100d107080b4042d00b035401007540c01610004854a21560200710284071307801d8020304003010344d041049142258014980400d00c0e03001200c1c203002d41c511500f0820000411142c0c0415501103a481e40301508143e401803802043d40e402d820070030002107006040c0100c03507440c41807800702d02d1b00304040c0400c021602c10038428980400090200044003c052016019281c421510391a10303050740c1e80241840080f400200f080700032180702d039030101c5009009880001d401b038442c3c1c0203d0705042e0b4015003402d02603024507468500708246030700c40703104141c2d070b0f0760344040501068501030a0181c20000040c14110704c462000d4803c0c40000010f02144112100e441c1d000d03c6a07030000c0c00c00c4401411400b142009000c10740d058008240d4079064400b05480703032040c41000541700c58003540d5a580b0514851005a0004d002c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 446710233 1250 446708983 446708989
    0x607080c0a0c020f06220e0c0f031305060901021305060304080910050c1912110d12090203070e041b0e0a0b0117100f050d050307021504031a060306060402070809 71
    0x107416200e00c040c0c010b450b4a83c04d100040c8513504a110b000c0e810038800b89a0f1074100b602140060020800400c030210b96082102e102449441100305001030544c0c0040403410511000c00b8400c1c03150740040a45e2142d00303240380802d010b0350080984840080038400c008c1007a00e4401d0440740580e501c0082070745800b4601c0184012400b03003200c1242070000903c80d003660f8a2040c40f0079a180b1006d103100d8104100c0d1482d00300c2c3e0003807105080004000f41e00c0d02c4058284800246805070705c4440c01d00690604044910710054154104000d402d8011514005025010308003594066031184c0310500c508a1280584904e015030b6114050640f4680c5c00440c1c0b201d0110b91201081c0d01040c0740c900e15642e070b00780c2c00501c150360a035110a40e0003102c8008010f501d4134a105540580b504458612014000f602c0d004d549001c0d10802034803031466507000318490b14101d01101d0003194422004120a64070110846e01000e0494015000c0d000b08070002d040381c5003d10803503111a0b4442c1074113061160003800c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 446711483 1250 446710233 446710247
    0x1008060411090604060c0506250e130c08090f030702060a030b030c120d020c0102010c0c0b100906150206090105070c0f03020106030501020309030d1a03070e072d020607080c0a 77
    0x1070405038070070408026141c48001c0104094002c1b6201c214071225a440c100f45040001807440101c812500640c42061640c5a0b0b6114410034601d04074900c9004a40029121f141d070310540302c400c9141500720700405800015031445a0412400d680f2081010440c5035100e10038824021360100c4e00308031240540c0e00035802103070b00d120003400703e07484440c0303034004903d00c1c104031000400250310880300145016410805c1500b461020300c0240305600c210400503022000b0020001c01c403d0308000004d0801e14801c206000504080005104650b0340301d960b1203003a001116040c0040c02800300060364070b481401100e00481c03440d5101503003580c0070307154001d40c176880281c100d0865484000020100700c1c02d0001c1c6010f248000e01850b65a202c9020700da0440ea540002c840095101c281c01144070340d804144001194840c00320001590349a51080b01e02211015030010f004c04182420401700e55201d14124126416408132405c1d40c86540c0283c0d029001101c20394590402081100a0703544034501c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 446712733 1250 446711483 446711501
    0x2301120f1418032208010504111306030c090902010201090c0b19020d050a030e010207020a2301080606030a02031b0d0501030606121104021e070f0506060d05070e060d02060a1d10080604 81
    0x2003002c4c152036803440c03401c0d1202070b141950644ca9420890100340340050344003410f1002032000308007041c42c5548a1500d00101c2c459203680c00e54408805013507900039003050341800d03070010800d0ba095403611011240c0707030040c4400380544010320b0a00d0099500000f00c6500c400c007592680c5003820840b040440150201c1d00c0c100f071aa5400b8082072006890307580ca510007809000141031401d070f100c07008134003a6110800d01141000341c4d070000d0041e152201400c49410442d9214050fa80340e4906042d26140b40d150000100c204200148281c4818916445941a24410744041c0080d540c2c0b158816506440000c2c0030300a4911241c00160a143c181e00405030317401c40c0380c1298800c07005030480c4040d6810841c8203403240403101d5082004c0080034058594005c000300e608100c44400d503200c0c5075071203055001d8181d244001c1c0001c50140e0381c48214500c1d4060703008011b541e45130f20f001c500501b0005481c07032500a465420281502d145030822444824283d00d1361131240c0c40d6603440400018110b83c913 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 446713983 1250 446712733 446712787
    0x81e07050c06360312040b160203150c0901080a0902030606100e0a03060917071e050307060c1205010e0601021002090a09020403051b0105042301120f141803 69
    0x10f044084209030301030601030b01c1c0c0c080300c40c2c01c4501000c801d05017003511709003c8410800d4100710602c807d0750f2000958003040d10a04880f0504812803005c05d1a1502c1c011a6440c8000c12004002c100b50002e0000c00002e4006c0e610081581c403032401309000d032524400c6c0250f042c0c105c03100088050030082c02c08010032180b45002c04602e000e0001040e0b044405800507910181c444541a0038071005031701030280d0308400880103141c05181e40303680001b409002880315130401d0b007a1409003400410010381d00116040f039000c00c5094540c2e1406440010302d070409025140c10400000b468418000c5c0080c85034406030060700e010300001c0303d04002540411007043d40306541050200740000300d8405440994031410050001103a000c1441d10840341440308075041020800c010b10501c900c0015031032610040d50050500e6299401c0181c07404480b805c001c100a9180c0a441c1801c0c080d5600710486281c0e084d032204c041b81d1510604400506044641d000c0b040c0d000b08085a040700c079441c1030840c0c4c0c071109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 446715233 1250 446713983 446714017
    0xc03050c0a0b010f0e09030a0e130f0606050d0e0a0302120702180708180a0203030a050c0c1f14070c140102190b06010f0216030305210103081e07050c06 67
    0x140e42d01150080203030003201c03c080b1070034000c1c40203090944c2800e030007101c0349004500740741c149070004180a0250150303d000f2030304a8620345030441250018030041002c0101805260f859450040840d000741c9641e1007894180018052842e0b07010030b00100d51509507000e84009000c184038484207034440300089130401d00380d00e118062249214402ea0040904ac1c3c1c0d00c5031a42412540780100075003804075548582c0022007400010b0780c0c004212200d07240d027408c1032511b502e030400b0340c58144071600600c00e80088120740001480c0b1196082002001e2060b02c1d0034044140720740310300c103850107013040003001401490028071654102d0403224525a00502c1200c20650300390010341207204a0040441d075080088041c45059038005000d07460322503561000700480655000c40f1440b44035248005000d00800041550410803410207134260070300d10107c5030704196075a1600345001c2d03000b0303a0914112074202d0b4030748544ca43e4500440b49142d80190080072100044401c10a4641c00301001882c101c980f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 446716483 1250 446715233 446715253
    0xf0312030c0a020105010501080708130312020c010c030f02130e090a02150c0607050a0807080619170d081009020906093f1b040b190f05100c03050c 65
    0xa000440c401c140c41e06200e42c682030200c4020b82560784c1a005541400410401c2000c40307640112526880b0003450349803800c0390828201035800740c940140380c990309400012048480141500321480207041541d0401c0f9180e250306481d42240180c1c5040340701c414800c0020007000c1c0c1708100d110f0700b00c04070205690088006134009640d0f04494000c0c020407220108803ca1004402d0006036842101303410124a801043d540080007440010400802e002913880460b140751183d24800b9402201c00107028000e07502c0301285e0301c51588011901e1038500c110442d23140f80c0b03445000814000d0503c511c00c42c1600f810280c0d80310103508600c0e141500484281b10f5190f01e03985034501054050502008242c980d145034201001124040100e0704120030300d902001810311001401840e40b585230384031212500407010024003c0e00b0070300b40711a805500d44413480b1310b09520382002d4007201d10120b07001d00800e5030b510a0126035102c840720400030945012000c40441c1c05000101045403200c400d6500710a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 446717733 1250 446716483 446716513
    0xa0312020d230a0501030f020d030c08031f0b1e0a0c021302070b070e0303091c0b09060601020d02070b1215031203090f19030e0a0807091e0203150f03 66
    0xc080840c0907000d0710841c0d00b00c0782a11401249904920031010500056045442d0b05c10103c0070860028050040510f1380720038584107805a400c03040d84001500c0d03490500364504000909141d0011a5000c0c80360360024a0020310000c44071404c0c0b901200306d18858a1740a4000c0c2c1e0780041131450180054001e9400c01a50380446c0c034a01c405000d140140c071a6400e042500d109080107050200748080070741952a5940c0000a035041f44104503084041400c2c24803020f00c25003600a80102609a5541448501d24011580301e10030202030f0b00722907048240c128200d80d9290284101080340b00c081080c1c1041d0000707124040d41c80403a40b0900381445200c00040381c0b400c81800000018150302106200c50100d0034080c8244810046000b001548002c5c1c03502e40c12000940b40c000c3c188088180c1062190700c4803041400108400d2080e25070059441210380b0207024200001d0581100341c000b03203c3c0302c516510a5034011801c142040440e2002e000a00c004003100a50413940b51041c0e0581c110406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 446718983 1250 446717733 446717741
    0x1e03010603020a0e010c020a0b03060d060e010203010e10030b0c131706070801060311040e090a0507090b09070306060f0c0c090e0a150b03061504020d05090d0815030a0312020d 77
    0x1250790059035919485001440d000200c80101d040001d44040348016903107503081d020585030500165070340c07034546000058145042e008000c041d1400c11076814070580c410360256040340e000701100090b135601e811901c400041c00d0300008080f003802d440842c0c21002402e001d4040a01ea40c090154581c0d290410140c0d100201241041140e121508010600d584005400e0051407542414060b145021030007800070b0099000b07011020707207104005040320000b04816000c0325000000e4552040e2101d081c00e000e0150181060f000380d8900c2e0100c0c080610a00c107090844140340d4850102d0306404504035600d0b04644020740e02141050700200e8012154031954100241400040c0002551842e100c50158030034582d01004910348801207505881c00305000b0307030016104da850345560403014000f500a000781d40c100000c0a01d000c0030048c1000c1d000843c203d10b4501034881d9041c0360350f942c130b150504625100d00641c041e001520607100107030040c070b82c8141c03801800d00003505000c0c240800c40112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 446720233 1250 446718983 446718989
    0xf0705011805060403030c0305060f043303030219020f04050601141804050a15050904080403050d05040602100e072c2d061e060d050c0a0e0306060a05061e0301 70
    0x20f500110309100130190188502c20502c060b9007003c0c44640760240001da02e103040e805000d030149440f00c8041d228010071126100c40e641c0c2012006500d00313400e42440145110b02e0000b01d000d841503000000d0403001c2c000e0244840f690003015400320601c4241400058480642080d042c011200240f0303010300b840794050881a20280f12210b51004850100300940c0c40180c500c060341860841114652181820084107444058860b4041d035100c0740351205661043e41d00107001d0340074940741034a8456008000b002125a41e50842d506603401e54030f04412111061203210380c03035004500420a442d018407031002c5c1040c0030790b00840400000c1ca10b130344881e04111005401c0c0010004803210601e92800341e06070258079040400c00f60b02d015400701d11400702116401e007165007a03032201041540c481c002c5070790000d9010010b1107141429641520a80c02145401d80440d5560040301882d04000070020311940c001480d100c1c800f4900f4050100075484a1140c2d80c600f5601d04046046403013500045000f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 446721483 1250 446720233 446720243
    0x302040c050c0a2a03020a090e07090c08040614150f06070602040306060e09070b1c090203030c010f0b030a02060906181008070f03050712110c1e0606010809030f07050118 75
    0x2a100c2102030000c0e24080c4c00e502d100d40910a14010300250b1110488030b01910003894000401c0817071444111328085656012400e06410507045a80c503a600c002c00c10700891098405000550703d1a80b6805e000800702c41c00240701e05e40d584412914900303407048440d4110040d20032494031504e0b89600e401e90f0301c01e4200795603164550b601049090a02040640d1001d1060040c040c0d10341041d91040c0c2d41e2040c0c0412080009101c0c00000445125078007504031103a008040300e0360f641030042014081c040e98145040d01c2440c000100e880342c2008580420601e50043c5400d02e0704100c1800c0000ca60414040b080ba20800c2c1802038000b602c403802c0c481101e03541502da121360381c0380c87c010040c11124108008000c05050400b8080d144c4c0c0c001d41c040307544880210340464400f40110548100d401001c40b0002144110690036412001d181401c42400303105000381e502c84e5079010015181000161380d401400c1c0e00070009140c150040d103006d802114820750010801650000482c001d142e215039098807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 446722733 1250 446721483 446721503
    0x20403060204080f03070510151214060105032404080c0a1401050c07030e0607030c0c290406021e07050301060303050d0b0d0c180b1207051302070b010302040c050c0a 73
    0x3841204002c120403d10280d401145468500d1f82c4a9498012000401c40c0b429250411000b400503102581409010340c030403d440013007128140400f0b0b00c1540d200c0c1c229240502c900104860401056112481e038001c00c001000c004e02082c400e064800040040c0c411a0b400d000700003182401744800d45420303028825800b85001c03d05d00c0709085840180039464040f100b00f0101c03000030703009900a0721a5600b151980e0f140c03403150600f03407003204407514010708030380c15102c010401000d180c0381e2040e02500d019401c0c4000c100c1140685040c800c0d80203103405644000300c0d40840c1048001c00302118034140c02038851042c3e5400120b030945103030340c10403000304402081b507403041205071003650116442103a04840c890481d4403011172030030050080103aa02011a1084504200c1d44c108109152000d07002003503000b00f00042c0394480d080c9000d81c03881f903c251a01c0091510300c500a5582141d041000304900380d1860b420800104081c4154800744a028015030700128028003800b0303a450f000c3c0b42800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 446723983 1250 446722733 446722739
    0x19021e06011503061d07020f071e0b0301080735030a0e060a0801030308060105040e040c171f090f06020d061a04080a11010e030f0703030f0e1807030b04020403060204 73
    0x46004202c0e58a4401090b2a0010410003210703080700d10015010890324003821501c414104074240307844120489043c1c81b0f800720004183c0381a050340298011503107544020300f07440d000a040c00f0b01c420b103d001c0301c582c030003c000d00c1080c2010040d40e400103201a050b4441000e47d1001151002903180301d0021038101144c000e00d02900001d103401c1c1350408450b860301c0c01c82c10440242102c60103000240c02c0111050008401c0c2c3d00031000c9401810b948440b0003603902d010328010344507404031700600c403862408008421106400044c411415035000417542c1c0c1d080307862101d4100a1440c0d60007036030060000500b80010544a20007000079449004000c10700320305050344c441d024205008104012001003208000c00c1401040d40c0c21070321b03407194104504007a0707480100d605036000600b69034140141c080c480d1f030a900024810302101d00c41d4a44686120035040c0941d0003122105050380c0000b60b00b1107042d0320700c0000c0e95441d0b00016600300054aa80b0410200c0c00b242c0241d08105c840076030005041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 446725233 1250 446723983 446723999
    0x9030105010906080a0b0601050d09050604021318030c0813171c09060e0301090803160f08060130111201050f0f0607080f030c0304200619021e0601 65
    0x31901404099100f440481d2030480c030183d440c080d030080549205111000318809030321850480b002543d00c45020300007114142032050300c07a14150b804a208241d000f100b82003400e454003c60600c81041c00180b104084162003c0d9036160030007030101c5561104004521241e0410364130740c0043d2900500e00e03030140144140c21840c0104240c40c6181d5014582541810603902c8040c501c255100c40c40c1c00b118240313400d4041790140a0420000701403900c003200300183c4240e04001c5948010300366550b4800c0484014040da03407000160342c1103001a0b283d145001140c5c7e10b03110020407881904500c0c80d400d03140301e44041d080f29012446151440b4000510a0f00e803d1400c0c0a030703000d000e08840307280484c0381d00000236405c0100c18104501070b80000c907504041c40507860580c0d85800748405c0c800da43e071401407400c2d100d035032003103074125485600f181ca04140c0000507002d40542030009840385140c1411064004894180140d00d40c0451090940c00400041500ca2460515103941c008140c03650600d40c0f4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 446726483 1250 446725233 446725241
    0x5070303090b0a090201120e1207060b040507030b010909091a0c0c250816050f130c20150a05130f152702010f0504050d14010e03090d1b1a090301 64
    0x80d4a2440381450191010070202041c00c51035501025492603941d61142f402e48007a08000d048103078014038003070810043c150141c126200045003680c580041544a0009a0440700c1120300a4020100303081000d141c40c1501c040c82c0d410110350160b0600300152003180f103240003000b51134620100345a45981000d401620141c00c09001000c0141c00310300c40b100a900d036150001c1c41914411182d001000b492a1038803011941e5841d030218051002002c1c400025040002c04d100080242428550410030b0a001040469180b1031400e0032048a0b12509644d10240c040a8600300c449941a0000400164021080c0c101c4c070340b0450b42c12070740c03034604a10801200d81e0b80c1c484680f81e14410400c40c051480c407054062205509007072a01c0040102c440450390f0f0300864020903089905058120705000b264140c40d011a007130b56000f8000080c404402c280c8078020044c0c10b6030003501c65075100300040d41901c81c008010310000d0101841070f9550940e400c110070008105001c0040c0003030b1100762404c0030b000f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 446727733 1250 446726483 446726507
    0x10e03030c060c0a0c0c0f0f0f03021e0604081f0e010b030304032a08030d05060f0d0f15020f12070206040c2310030b012a0305070303090b0a090201 65
    0x40034508000d001c1126a8594400030000c00c04103030000341c0020034038003a0502581c5140c1100c05a18500d0f2100903c4403508828065100c0b500050b4400192100c1070140300020741c2d60242214a200c50000201e519015a42d5801644045c1c1844003080300c120800c01016480e400d1000c40c8920940c0d45041000c135043c3c510000c00f1a410b0005011142d14004201c40c2100c0d406010542d409607141d00f8240440d100c84020120081c43c0c80f80018052000405054a41c031020070400075500c5080410042070310007004681c002c4800300440010549081ca42c0641902420b143d001520760b17100854120b9020186500044d0310228111450004256405911009900080c0950300b0591640018100725205403452840310018401480587c10700c00480d03d1006440d10404003040c24011b03014140640c01070340041c0c02501d0007500c01e103000c490003602074240400d15029240d03a031400c8403164000102a01855260034941e000a2100040e0034803890b070340306002076038100d280f00041507044040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 446728983 1250 446727733 446727739
    0x9090c0f110a033006030b09010e0708070501050904021303210e1305070e120105090c0603060d020105071a01030507060f0807080106180e040b06190605070f02041b090302010e 77
    0x40c10b84800690050300d00e07068144150100c40148080c3c00c00ca601003030078a025007034090309105000041001141030903002e40b006400900400300b25042c01a036451080c4210b1500343d000c808100629405440140b00126002e000585411040c200b100900585a4822209001030700d44142185d1040200f240222105207080f00070719100c00b0000b076424907072070743d551a01036440001c6000075016500d41b50803030070080c149000130526140910b009040c111402400b03030049150710421840d26004681c460f801c010169440300b200ba400440300e54101801c2218405100542482d2000c14407006c58020f40c440d0300140800c40c1404801095510701020410500001707406101200d81c0044c0824103440251405914558840541c1b40140641e54090229044d191082c4000c2c420b08481c80b9107d1141980d5680603c1d170001d400c00301003002c80c030903000091810300543d40080c0d0058550385041c0c1c00100701084003107c0c032024800c00e0340e0f1401602e0204031800010001c65800c5503110408080c12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 446730233 1250 446728983 446728993
    0x601050906010c0b093304031419020d02061602061b040503190210050723011d0102031609030203061909080f0a0201051b0a03021605030c0703030809010504110d0309090c0f11 77
    0x403840501b2070b0101800c02010320285000100980d0b44030400d07a0102a500c55604103003a425074406511008640c504c90010f00a01000442007030304c140340c2c444000d94540c010819583c951581900000e8143c84a007103004007084001a42e0398108850811100d40010301c0380102e5041c1b04112400906500100030700c40d0601c149404240e08a1000880e51480a500304947da405448a401051942c20030700c81c2e207a2210240017456015409984a441550165060701c42020b1040d56140030911002350f140c1e1041c00040c4e4151745a0300d030010714400c2c40c400400c81d0081581c0780007076608086c0d000b0000c92408100b000f04103609010301500400c0408201c40d0708a25045451302038850391000d20141900012a26040d40309030300b84889203500041940c0d11100c05e229499264082844140e00145c08a80410451803044c4540d5000341d62201c0410100e46552081c04010103c2c0441901404801d800001d1516418041c600800640f552042007841c50700c8406841c0c01c100c2c030f41d044200d900c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 446731483 1250 446730233 446730313
    0xf051c021f0810090515100923040b0406050325080703030809190512130906030503032a03010911070b013002100c0222020a200601050906010c0b09 65
    0x514401c41040101c191141f0b502c51141d0390003910301c1503856010b60310304d20407070790100400c0104402d90281c05004a80500c100c49887e810031090381d030030307005e560707415004642d020300900180c0803406554140504800e103e82c7d500c1d580380341022040d51098000c80e118004001b03081c80c09101ca51384504c1e031550580007900c415110999120711003103600800d88800214036000041c00c5803104010101480140030080c2c0f01e18280742c40380c1058801c2021f00444500342400c1d44501c20030354900001c0c0003034050440e8038110526024200904403d520a04100a04008503121940180c00303020340b00e4115440d00500b20f90380d0669454808291220f100301418200169202000200d5400880c64010303014501400001c5190310140840d00c1a1000314050f0201c00d1210f801524003064561030b0327400c030a200089030107814190404010801d40006006008078a0b21102c1035400280614000c3c500444a41c0c0701c81d0801401d80d4412669806500f500209240504440518564100f0116800c2c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 446732733 1250 446731483 446731501
    0x1020d060611070e09030903010509010e010b0a030b0f0a060302060307030c08060f030703060c03020c1006050307061b030f2001140612030d0209040924060f051c021f08100905 77
    0x20070b03030140c0c0c0d014015000c00701e401005d042042d103d40c0305e030040c002c02c41801e0000640703008017150a0700030b64550922520702958a420f40000c0d080701e420000c03441c6140e942d00340d904519a401042e04c40300b25500c400110140c1c40700009103216038916100000c0c0c188240e4400b415041004040c0c500c00c01c0440361140da40d850215910007225401030001c51107008203c002c0e030103809800380044440c4225146c1e45400314051b08030348100ca0042d4151500d003501c404040b906004150411510502c40a4191000910400080354917420310729044003003541d121356401e03840001000c0500e040e0744a079581c02c400298081615007000084400c550f622094224194681c06501030703110415901284805068485402c00c00119521401a51821145621002480100b952102d4002c4d20700780b0045401c0e680d42d0050390030764500038511800882a940c41e40b4a424090b4030483c1c104110526203801d402012010300045041ca865604181c41e03c0a031508400e0055030000040608020a00854003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 446733983 1250 446732733 446732743
    0xa030f1109090f0307032016140603061e0d1b1403030a0207120c0e0c0d0f090507090207060b060301060302031f03020d080c150108060106110703080a0e031e01020d060611 75
    0x142d05007082c0c0002c0000d02001c403448010480301c50b421b80074140c0e2030b07100b61260141002c2512115842c151180307122740d0034803000d0301041703908030340105e6040340750000710340740e40604107240c0d00003814001c52101030380d9650301c074003034141c160107528180c800e091200b0146440c80c905040c1c0150025801c045410b000256900f019124001003a90300411490034425000c030980042c0541019100c0c4070b017410106108540e005070016900305140400c00002d02c101c0740540c1034074a410000620060703090243c07000080d80402c5040f44e009903039401000854803290003031340c000c111075280140c491034600c0418002645d0b02c0e001c5231214034003183c24001640c803182c0c1c540c02103400c46692a280c0703103030001c514a0708a41c920829580320001c000010004400200e40381a6981590b505114641414646a841030540401481450180004a40c1c0d522407011104560f00040850740070b0510f5800c003650311303840780c25200820394000400c0d0a804005000d42d00c0102054540848107826440c0015100c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 446735233 1250 446733983 446733997
    0x2030c040312110102070807030813021f0908120306280b0f0c0f07030c06020102120c090f0a0b041a0c100b03010609231f030f020a030f1109090f03 65
    0x40307200610b070541c1c4584512035109410010500031591209181020b048030b07009080304800151102c40028200c0c030211074178040d01640a0820b00199040c2200c01c40d40500e510f1300c000820001c0c41c80000c061004000103205804801100c03643c0781081d40c1030100c02c0c0f190003804800c9000e005000309908480c2c1d0710070002c4540d8188881d80703c45088200c0c0c0c1c031900c01e028584030188100500408100c17000300c0e4034400c50744582114440280d403410140e090b80034500310200c102c04450002000e03468a6002000c0310307400184021160303d032590004034241400d4100342261140814288601c0340d01e107114541d02040b02492600340102499076030740d03680721881c0440c1d0694565502d00442d45094200384050300c91a0418031450410780c0311760240c0b8500c4111450103a5440c8040780d00c40000504400d0b5400e1a810124805800c0d13440382c1b81c00b20040d6508a070408401c1c0f200001060a050b1040c0013603104180c207031454403100303003044444c00000c1e107102c140760031402c403400c0c01c1c503800400c903409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 446736483 1250 446735233 446735243
    0x70506040b09031207080c061b070f0c03020933100c020f061c05150108070503130507060c1208070e0f0307030606090b1003060303020604171e0d0e0102030c0403 71
    0x26448020b00400c0c10441c0440c0c14616a06001c1036100c1042100d502a00c03140341450221181036a54000503203201c0703103078080319402c044100700b001c001c130303006080900404e0b0080c04030200d07040c0d50703600cc54041038046403158000c0d030020803946500c1542c1001d003421007490000041d54100000005101444c40030204024040402c210100f1915407091074400e181d8010845d9444000c084902c1e00400e082110075141180b404001810f049c803214408801c001c1706960b10308940d91034400644140d44003400e6800b0413012000c0c600009a010440d100141410f0703600e20041c1907291078600100041c10862900780044a130070404d9066005c280c850081c4400c4441002c2e00b0303517034404682450900d42001d80094201440401c03d8a02c9070440c0c1d80c000010360350529004c907241070450440780207000050040c1c1100010402245ea002d03108250b0400c000041841c00480014085012015032031a0440900100c0c9903043c0f10341da407250b10002c08844000750710f5031800c2603074500700e0b00c528000182 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 446737733 1250 446736483 446736487
    0x309160e070906360609090e0c040509030c0703060903080a021e0d150e01061b03020312150405040311060a1a1003060f0909060506010c230f2409070506040b 69
    0x140e000000341c00c0c82002501096407480303a2000c050611076030410317801210081030301c1c100001444e825034030442d540b00c24208080d201c00d180143c20407001d064003038104010380c48244600c03480000300f400408000d500c150800a4500c0d09441c0240109000821561a481c0b0501807000080450101303020308003a044c503160b660b5050f4480c1da00003800aa5007100011040120105450b51641500e5059030950b03250080000e90400b01c42c002d101c1c4800300180140c2040c0100c16024404502c002d401003049003d040400b00380002190458808440907130005400054441c41440d0074070500343c001050718410b100d4002c42d0507882052004040b00c150140c400c0700107003c0054842d0307000e40050030060341c2050805a07900c0c3c0040113080c0c19681a00c81d1442c0001007100703036005031780021480703a110101001285500141c16529501c51000280c28001c1380600e0410030000e01c804070351340542001003611412a6110004e0b540b10090920b81c4543c00441d0a106c1c5a540d14242da013100c41a50354aa = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 446738983 1250 446737733 446737757
    0xc15030412020712060605040e16031e060c080438060a0314060a1514060310080d120b09040f080706060b211506220b0309160e070906 59
    0x203141520390344c000701071510309131001000c00400e90051012500100c0b010b000d030701010030110f03448000f80c40c00c00c0c501c0e4550580800000e61450400341e0b280c044044401c900700c1d402c0c2c4601b02038401c044419030008800c04101300c20451041080200d145901410840c0400050700f040940d244000640c001100c4120004030242d0701c401280c0301a584c4101e1043c28030b0761024046640300743c00d0720401600d82c02d10f841020030304100301030303901140c0d000c2c5500d040c0864081c0904c242d80c0d00c040d11078100943c8160303000c108500d00f001411030006c03055980c5a0070001d0016400c00300c80030985058400c211440500001c50040020340031440c0c1c0060841e0368801161074184014007076503003e407070420302c041040c040c83e140c80b4280061040c6a10030f8820141e5845800da0790b00c074903404070141d11110510041110706492050b01005208281440b51441d07110010003034980c0040322074202c20ba2003084a5004074242d02c45180003442c011041c02c030709080c5800013406030301c06409882d0402070b45100c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 446740233 1250 446738983 446738987
    0x70501020f040f0515031902030414010e0c0a0504020309030327160e15031b03101118010c11090a11030403170105100512040503041a03090c15030412 66
    0x45654407049980c055440382d440d1900414603242c1c0c800c19200340d04c00c00075020048462001c807446140e0740003100382c01c2c01619000c0002900003401c140c40c00a062404159582424400c0c0c210411124004016944a000c204100c5641070341001c0d0081c3e0040c81481001c02c4000300707480e000300c00710031524800c0e40c5d400181040440e00c140305101500c80c5510150995100c414240152450310300e00711880e94585d01140e901d01e80c0c055010345c02d588110020700000c090103109104c140002025a54034400c0803a1603001d54030300e514440c440c11000640080c25039002c4918910411003800c0400d4038400b46c0d19038070390301081c40a400d0300072160320000840c4000700c7da000800d43c0c02ca004240d070301c83c00c15040c02080c4900c40030844462001550001ca19443c240c1d002407101c0381d650341c40514004a2560101c02c8840182003203c40b44424000890704841900c01c1041c12003c489d8441e45901c0c24940c00c6161000c8400141c2c0225845040d20007213010290480398040d41003d01040c803c2060641 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 446741483 1250 446740233 446740237
    0x30712030209150a0305060d11090601140d0b0a0e0606030703110409060305010b100207080a0f0507080a0f1703070e090709150906030e0304151d0402040603060e0f0f070507050102 79
    0x90030f50f02c48080303402c0030303a003a0010010b41301500030ba07641008940e5899041c007500c003041040240c04400c4081c174075062131a100e003d0941c005410325006162a05409844c2501c6e00a10541c00000303480c1c0601107500d05103080340c01e0092080454400c03590600b0008070b00544405003002082645544880184156240441e401005440002c110381c2e030303407030134090300034034000012a109800c1080d81c82c035850f10000d2910107849044020f807d05019540d0762a070f60b400001b4040316a030090b42c40003d1310150034422090054012407090000906030324210410003004110542601c8080c4180195030341d014400b91459001071760030b0134941e101ca10041d80c104c80f0680c801c0036101b202c009890600e541c080c0c51041241c085407810700c2540c08558070551a801607020f02e6014000906180c1c0680b40b00d000300a6030490324001428401c651900401c003a41d200740c0000000c07036100c0f0410060441000d0040ea4002c40b0074000c2115402c094907158492140580b501040020201300401440020b40c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 446742733 1250 446741483 446741497
    0x2704110a1209080409050613060b0406180f0b0405090a020f0a0e010e0307090b03010b0409020d06020304020109080f060403090e161412040f060c0807230909091b030d020307120302 79
    0x8461344841c0c0e2001040c0241604030b60a03405840550a0300c10000d03518001d007815100f420f8806802d207400c00710300315a451000e094444901c90462800100b580c694a03d00c4040c0440104003070780c0d6810503080c0306298030007a0030300f500300d48100300e0440c00004280648501d005585400145411041b00407901c860310001000d6240c09103060000f08074502e68030000704c0b00750550003842a100c901d01004121111100060b40260011108000088855004641c800d2050510350700311510307003840510b800c0e944020b511260348000d0030701c0141608102d01800610051005146611f0020421100e4102c59a88602132200000101c2030230000340099652004840c0c00d4a010f038581f40c00e00c417500c4c9004010940e006480d0202185d0390720b219008542c8100d207982c50710103070004807642480d102036040f01010510309043c002c0e06e140350713200940980074118040041000a010f4444a01c1c0001200e480d98800c1e4000f62606080503000710940d032131603400c9070304411285500720058002c0d100d6030ba = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 446743983 1250 446742733 446742743
    0x90601110d08070e0612060d080c0a0b04051006180905070b0a17060103021e0304020d0b0c09030c01082a0912030d15030c09021e2704110a1209 63
    0x80a41d1544601024800d90395a03555803008098541809001e20520f00300f42c10300d000d4000082c50b0783c1880a401d882182c46011403a142a00811031181800b41058007200c190749000c040c401801403c1041c3c40c4070040c0140204051481d1004c1c0805108480300340071401c540343c80c0307542e05101c014060003004043c0c4034003a43d030b60000040014002c1e446c0140071100d5058040200b0b159500c03a00c255480560f0a00010440010400512200e5000148100c4c1e00c4103808145600261043c0f0305035005401660f80c85483e04402030406060088402c0708604200200381045860004140c0c000c120035642801c8003402099201d1004162140e070325011340220010700c494140d0000040240008082e810080003001545040d0f6058076078244005405155021824885c1903d0350b03000705040e003e02901000901c9134105149441c0e00030190740044003402000d02c91070005810b60b100c2007108211410460901314402c81c007050f016480700c0320200211a501d000c0c0f48442507200042e00747c2c00c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 446745233 1250 446743983 446743993
    0xf030603170409060f05030607050d06030215030a0b0103090b150d0b13050d0302070c140d060509010f0c03050609180f03120709120203060412050405041a010f021b09060111 76
    0x301c00460b4414440c000f102407070050001162807426001c1c0060f248001c010b40310f2a00c0b003401c103da960300300b9010712155569030304001005035a900381d843d03822030a80220035103d00d8540c003640103d0380e04206503414107052003004c500041c0c1181078164001000d09d5030504211082010940404007010024600030740034051054140d01e241040c90a503102e04100d80c1d4001540c1e07011002ea0089103001003485244600901a06515981000b00c4d21000b070080d8805000719100c00061310b1040d18881e40d42c6e513460f03506002205503170255000700312290038240f0803420558041441030740f00426020380a28118260030491009019901010b1044404c80351140000403902180c0344083e140c200c003180c0d0a14000941042c1e0700602c08506800801528460340c0343c0d192201c0050812040004001d8108400300b9036544e01d02c14050161100542820712011490014040c0e40c0c1c603204640541d4003000c559209941407115100c14520280d68444154541e0401640c00740341c0030861034058064 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 446746483 1250 446745233 446745263
    0x206040605130c0b0c2505041a0d0318050d0314030a02040e15010801060f0203030f060f12160b121302011b0605041209150c1a010e0a0e0c100f030603 66
    0x1180007511744140c1501c15207928400f050715450400809414172840c10000840821a500d015480f100c14042c1c600303c03492607121228001541d0030700031035046000c90200c3c40b09014051070040900c0140805070340d020005062910050a50303441800d00c210403440c0000015000c0505405440003003440401c03140e01030500700921100241c55007000c4c0c1c001110304000145a030700c684009084104035401540c036640700c0e14201d00110000604241c1c0000e51032000010688400015102e04e044903005024510f41107080360050002992141c1103000043c000880e80802915400e41c1001c1040300c01400c600c000d1005a03240baa8601705c0c4000300b444482ca0109002403504483e20583c4949059810710300c5880090b02c1e0051180102203000e51851001d0203042c0c000e0b035100703100c43e018220004103d41c0820140c4082a1300740c0000101081e540c0074003141900c10300a00310421800005400e403102010045007110848060000070844060080100d40d40654081c5002e1600400748454450b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 446747733 1250 446746483 446746499
    0x30e0c060d022511010305270f0d030c090b03010f0509092505130c0503070c140313061101020a0c121e03230906010e06150d0c1407030206040605130c 66
    0x603c820941d00044a500c10321010342c0300b4810188980c004c139005540713901400ca51540c21076400404847c80c0c1c46a83c45540e800407040080611031072941c0d40115940c0a01900203290b120b03141d10030b50b18060144010311201051801a10a945064a243c0b15a030f4406105500e000f0000100020440d1990700d454600903c400a0000f9200262440c00324003250181960031500f14002c0e0b03400084050002c82c0c001481180d5811540c1d0240900d181900e90060445003160701c008003a51035003e60110401c06d890b00b040c411254001654000c41c20002e4003078001c0c1840c0c061000c000c25100d5404d074154804c0340034200e2003000e00b0302a09511030703106003441e0140080c450f0200c4016001114641c0c00300020404034454850b940c50005030600b64a07000c02e0107441207000d002c41c2d6200c072001d02c054000301d94000261001c02417070328000c40c1c4240d1950019162030310481414502e0003040000c8000300380c0009409130415030150002a0742c0d43c4e402c141698003141500c0090400054801c00104c2c11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 446748983 1250 446747733 446747797
    0x402102712020f0102031602060903011d03040f05060a0210021605150106080a180f022b0c0501110d080406060801020403030507020f060301150f300c030e0c060d02 72
    0x52080d1545654003c10324016a90780c0203228540d8002c0107003460301001410600c018100480d006000460810000143c0300c4408011101c0ca11a590000c6002c101201a00e03440703070001d14050781c41c94a0300c040d00f07100039158a01c0d0712140308070740c0d0005a800405103401260f20500c64200b07058403651941c0324a0480c2c5624284110800210090089400d903020b5220b41840183c15401c030407801c000907503860102864050017a40e210701081c0c1c1012062921036051540c41e0290f0060300764041c41da10344440c050003e07400c140e0401001c030480c000321040c00144240e84400c0c60504c04055616403900b00040d142641082c942e43d40040740c0001003640001c09450346d03602c01c6404900c2c48221005010041c00244654030b0840741d811281c01030035010364103c20440c4558038000c2c002c2e4207038a244100001d582000101c2a00d041a90f2001c0901c1e0f0f4860003040508600c0c1c04c0c0001c8143c102d210f42d0701c3d9940c1c09418401c1d2400155804d14031130300c2d4115105400d00c4840d45111900e60310901d10781c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 446750233 1250 446748983 446749019
    0x10110106081b0112020d02040b0c07060e0d0b191d0c0d1e03030e0a030e19060905010f02070f080c12060405070e060429100804021027 59
    0xa60030610041054100401c82c42d19140c070701c904490788807201d90011500300001d0000d941c44141d0802607207120130701c10300040c009044c049489940e070760900c040e91803400d81158403036010420340c00c901440a07520740245104a0781c01c001d111085844801d52007411410303890307003501d00c06e103400e10f808810a071001c0d1001d1355500d00d60a03030b03100d540c2d12810f102c242c424044008003884242c088940383c0c424040ea02c628042d000e440d0014114560040051514a0402040d00454190541115645840a0289404180f01c1e440c0440e45281c150081c251002a016050601203070b4012a00103e00c20040f840c01440c600204281c02982c0301e100a40b80c109002109004401d07502c00d03010300010001e503013030180340d001004002961403d034065080d480041c0c60641e100391101941d0120012140d108803c180b510b800b0b101d8848802020407240d064841825403c1c0125501044096030324060201c402411504020381c440490310819401c020100900d8541929260408280901582a54001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 446751483 1250 446750233 446750267
    0x50a0b07081b010f240303140c01020a0305010509010b090d0809030309030a110109081f09080903010234020612041b080609070e0f061e030a06050901050a020415050304050c10 77
    0x40d00c00412840c0011003111111501e480d001d415080002903c00d40e2000c11301c40008040038109011861118266480850024004ed46460040c0300c14130b00308540c5801000714401207072400c03020308041154003901220142000f0b20104110300252000d00840301802402010f564240c20203280c60a4440700d4403001e18001644128003180703441340010700020180300b4411101c402e00d0814880c101501e40b50804407422042801580b40070b4070f00f4005414003c4507206164610b112041614134480512614050400205031080c03000d40c8400080b04e40001d045510030907513a42e582010428170b1204400c0e041c916020440000f81c4210104206006241e0b81054820781582c68046904c24101541d20742881e00415000c41c1c0c152401402c0341030049050244003011101500019040481c1c000741912002d80720001c000c0300740d000b881000da00405000d411420542040315240841d00c80c07003009024404c0001c081418413104100c81051220010b0240108113400207005044450f09804084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 446752733 1250 446751483 446751491
    0x20d060801050403090e07020a06020315010f050a0509060904060506040b031b03010e0c0a1107060309030201141005010804050c03120702011706030c01050a030f1802010906030501050a0b07081b010f 87
    0x10104410b002e41800f5540603605c1141541c103002241a4400b0003612a0080d4072a000080d40024542c1c0095031186001041e004590880080090a0201441300f0442003003410001c00391440e800009880b04a40159030311502c4020420108005120541003d42c0c01003020a0001d6213403a0345006500c100c40460075501d40b8030240e0400e0480740001c2c0140a10394030900e0004807011000400380203000380c1d1b440e081c529480b8038106d150418600740c200d0000607880710f411005040e0240143c40c021402582ea0509900d040c404460b1041f8141c010740e810003040c40b0100e414400100700308400340c60010283c4061600c2d96455110303540c4501070480c08103031307824006200100c03994080c0d840784602402410b80020460011140c50307000c90900418165180200b081e500007033322810b90304c0344003100307000740ca10030314000548080342e5940711034209400c0074014041905e84040160807900c030818030540b1071540e807426041c03500908444d16502200e0121080124205400201c1081081c0c14100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 446753983 1250 446752733 446752739
    0x501050103150e1b1305040c05010f090b0d0b150301060e0117040302070e09030c0a26031504020f0408101401060f0c1203150305030310051215100f09020d06 69
    0x160360840c0700d029400c0d0068104142d65104c0411010b1014000400350214100c00f0b00c081d00c1202e400b85c4041d511140880304c14009035800c80e152a5245065051145e0301c0c520b804001d1100b441414801502d0715100e1034240e00c1d0f07840d0080d160002079a281c8030b01c3e869607100c580c010071a01c2165032407070019a403010800003c20a0750800780c0100d4041d40a0a00700303080c078252a014200260a44c405417004001d03000d0740410038001400c0080c070032400c1c503039900d8110201c440070071040070444510507420030501a9540003d00c0035403010f4400d6601580b910058550288113001301e6015190300d026403181030000170700d5513000d2101c22400c804480d906989403001222a41c14104000010521319036140300803603540381ca00024552940b4000c00e200d485811a4454000d29900071511940044144003100140c041030102400003030350810000c2000440044d562403241d01e1a140e40c500200118450f02d01000d080005040101a90030b00c003596004403100944c0308104035031940345485008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 446755233 1250 446753983 446754023
    0x1103030117010c3e030703031406100f3203040c0e060a05010e0f0409050f070608070816020c0306091501120c051e030109030f031416050f070606030501050103 70
    0x80d084100745048100f0034080207140d5240754134403582180e401994101050310042c00e0400007440d0345c138401d55012075225070007444401082000b8003000d03c10440e0910b03a14501d1740c00403041803601d4003403820105403c0c1040b10780010392076080e55400302003206c0942c0c41a030a9413100940c0a144501500d0042607583c0d60110181c00302600d8560f80a030841c03404114940c46207210200040000344402a6054103000180c00c44041c002c003105d4170340028001100c540000d002e840c009000504165540c0d1829060041000200801100f03514040070903c100c070900c04c0140f8848480090304441850502201c5590745142402c1c00c1c10707000c61040d001044000100c010042c025501030302d100d000b241820100310300b140b1000e0300d80200d10b09104d5980c1481d0b40902600c22120701035102c80400707242c00103000f0261180d070301c5408c03528041c400c140031200c2c2c0b80356200d0740d112170545030064803410400140034081c40703a040082c0040d0b048c000c0220078030006620183c122441005039014190860200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 446756483 1250 446755233 446755247
    0x60601030c0522080d08180307151a032e0e0c0409050f01091a2a160c0e0a0b01080709150509060705010b040b0409211103030117010c 59
    0x4000022000d104225010f2401005000c0e5400740901618680d070321380c0384441c54902d180c500304002400000034001c0e40714103190341e08070780352120020318039044164880e62001200520a4580d099480c1c0040b0900f030080a0580b00400000702518400c40141810840d001803006a45240800d03490551807035411a2058034040034028014184113015041000004c3c180a036007642e00cbe000317000ba081c40d4002e0a2041c460300c076118242220304030210034820790803098000c0048080c080080d1140003040306115808044801d0307560040d80c0d900c07106140c0c03010581350745402400c0307051310100400d41d495402c040714400c8400c400c0c1000000d00c03a00c01124009400d5038084042080343d1300030b1249040c02803022006042c14204986040040c0d00841c603203078012002500d80b6551143c0619103480c1c5405562200745080383c00380300825880e26a0480700b02130510b0310120405091105401c070f406800340ba07110940e01c0c41643d45035a5900315000c01541000d02d00d248951a1030a006501760240316 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 446757733 1250 446756483 446756501
    0x2010e010201180f0320010501090b040207020105070605151e040b15030a0c0201290102070906140913020405070908060106080c07030503060d02040e1609020304240b040203010608040506060103 85
    0xc1c08a80301d904a0300c5000d1400785140342517007040b8a190034861800c04940e00030300b002c042d640c00024290b25101c030b4102100d2036003a40b544540d00401074100542c0e4410180e80301541c101100080a441e45011103444100305a412030304081200c01814200d111301b01541c80c03100b0250307001d01020381980200100e080403000c0f07050201c1d10030b00c0441c0c0c2e0007005a00c0038160520500000884e10b2242e111406240071507015101d02c518011180111541e05118800081c40b40358024040c40c0c1c142191511041c00c0015018041c1c1c61035000140ca840380301d0210301405801800401041c202114014541d44aa000d28201c80c4034100001450078031a00520384500c01e071490b046c0c00c02406650403551a800542031030390005081c858180943e80302c1c4141192010640000d008003100803030360304a049099400440310603c14030802000c5800ea46410200c0140741b0211044000c6289042c0000c2520b440b8464210340701100100b0280e4002140f02c0c0100c0c01401141c0c541e944803801181901c10401c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 446758983 1250 446757733 446757761
    0x10061403010902030a080c0f0a080702011707080a1a09130506070203071110020a0c23012f16080a0308160c0201030c0c0b1608160503060d150c0c02010e010201 70
    0x2c5d01c180040713843e40000d0304034440f001c000c0d100e4800d48034800e586003000032030044d0351106000034a1800c56811650710003450f4440b410207076440c58205406001580300910740185d858450004c3c42507500d06140d07c401403c401000c8440074103000340602000c24402500310307581d10480001c556068000010b607422a540301c451409c0b9a0680d5007800107000e8601c040b00198410345c1c1c1e0210004007070b13205940180010600315001141c803008071f0200c075907000c1100d0307040c480d0540e102406c00e003800ca500c01043d9020001824904011000f01d0300d018545100115045904040403030301000103c0c080c81481d00940c0c98030846d4030303900142500800b0300c0104030042250501c00c1ca0055000b0b42200000004604100d074485040e40c59440d90048122101b414100402d20007140003a0811905a0041e0000c09494036448069001502234032014084603c80c2c0c46003511002040510b0700325200e24544404184840c50000704040c014240098089010801c0c5101c0341040354814844d03249595411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 446760233 1250 446758983 446758993
    0x12405031519050d0506040516050a0915170106051302040b1606200c0f070303050d0e0703060608012322022803030f0503012d081006140301090203 65
    0xc8402c1054a20520318403006036003901500044030360b00c0e0800c44c140c090080c3c0c081d250b1843d2514040b030800e400138a4003d501e92045000340075503240e8a01301816076022400005140d81c01c044401e203c0041030340500c00882c22000c901031408010b420060450f00d0503550380f100420011303034102c280e0240d0300030b4001c42d1205108451200440001d1500b04900034000013824080c4210780102030100c032404440c2d0030100045c10054044208a80003210046c207000d09011350841e82e0042041c400e41e42c1242e5141e4a804445000c4001400035100459006a0030092203136190901070217083c600041c03036141e56010040e01c04641e03504143c0c1d4461082010401503007035030165101b440c1900d018041c4d8006a8a40040c2101052401c803004a500c52140f0410310600d1403500900307586442c08404100a000e00c01041500c25111501c111850b4450344042c5100306802000c1c802201e60740002d100d8030034a06100001216544817406441c104004049060805000e0500307031051100029059404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 446761483 1250 446760233 446760271
    0x30504060e0a24021e130b0a0c020a0807080d0804112e0305010312230f0705060a09080415050c0106030b10060201110406051303060212240d0209090a080301240503 72
    0x250001020100d075440c0f030340e031405601c9015014048c1c11000701040424a022011810340c6401015000207220701001040c910b070500fa4500e495071350000c403450034000c20a0100b01042403c0c6030a0509041c0988070380345c1c2448185e140003c0e8a542c464002c0701c1c0c11034179102508984a400ba541c1a00d03001346130381516010010040b980c0300c0020084101002c00f041d1884002c8211000400c203180c0c00c402a00e44550f941d0a1060a0050141c41d2100982c900540640000c4100d4241e4003200c0d420341541c081e001c071291040e54180b20742c1d000e140f0254038005000c010031056003c11401404650300d0104a079403126001c0e422141544013010071100180010000540b14000030002800d01e5120302e00f0440d9681e440e04166000400f2400c9076580d40b108001c080c1074102d1341c1510341004020101d11400c5510046403004076620700c042d006d80d04c0007000501600d000c1002c40e0310554022082030f0b17a90380d01d80e880d03440609440f69241816510b0450071440a22540989006600a00100b241100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 446762589 1106 446761483 446761537
    0x1202010e0601141905030109050f2509050a09120e01020d03020906070f02030309030d080105090606030106122307030207060501081b01030504060e0a2402 68
    0x101c1240104a161110b240d4800c0b000015610340001180f688242445520f19401564041d07003020812020800c0010f0020210b0410405855051454071141c4140c401c1911044980154480050103004001d03440160826404040021081c00c2555281d81c0003080c4195140410700d030035005c040558041c42418011005458118540b2180d040010b0035401146405000c210020746040d0464400304112009018020200c560341c0d600c421000303151f99400d0098a0248005d00b001c98143d081403010303241a959180c95010448204000740001007989010522005521040e00c10185010441c9039000e00c1ca50ba0300980c3c2d60740642440310980b00c041c1d00c580019840681c0040e00b140002d458245440424030340405d040e129400c0c0318010384040e841400c80c50194000d4402044140d003521074011401e80b549100d00c4412411640c100d000d00040243e01c024a90b10100c0740203 = true := by decide +kernel

theorem cover : BRFrame.Cov 446582733 446762589 := by
  have h0 := BRFrame.cov_init 446582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 446582733 ≤ n) (h2 : n < 446762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
