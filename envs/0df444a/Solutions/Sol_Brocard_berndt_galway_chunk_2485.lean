-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2485
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:51:26.846407+00:00
-- url     : https://prove2.me/submissions/9a3b9690-6409-43ae-980d-8ac8b31de8f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 446762589 ≤ n < 446942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 446763839 1250 446762589 446762593
    0x216170a0219020d0b06040609050112050c030309010203031b1306030204050423071d03160303020f0601120803040f0c08010507121109010e03120a0201050a0e06160f0311071202010e 80
    0x810607404240810000a805400b517034890300850000d03075440e04124000c1505520520031541c6842e04a10048a24601141c503841801e0440a4908010040e2541118140c0246066951702840c41040d03107104201d60341a00b6040261b41ca00e0b030340c81c0380001c014011a5070016100c900340001c1c80200d6083e2a688401411800801c03841412580441e59015140340b409104032040d9112403001c1b03030780e0401c1450389405501c40000002c9003280848080324040d508035138194001f040045d450780c00c280501500440e81400e0b90001c14a200005d5801c2485042c0402c10040c1c01c2d03c8182e4090f18641103003049075160030038003d400381d22850076402d090701d215042200d080c10208580f402e104017500710741801450300145035130342d50a2059040000655420726980c840710f1200900030803040720114039603032a00e01081c0c20002c00042141c419055903000c200c220100b21000c2d14405449501241055164501100e0041c0d02c0700250080c0c074401c43e44920714a00301d8002030709440844160396029 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 446765089 1250 446763839 446763883
    0x3060111100c080f13110d15050403081b270319050f1605090a090803010305010504021302070b18030408010e0304080d1103030103080f0d05010605130e16030216170a02 74
    0x11302003150318044080da000c6181881b880407100070070007106241c580a09600c01045442c2500c0030282c01c07041c8124400d90f9540c1c2c49655810480241c40a00c1900c0b02c524401400398140740300964040c8452241e51181da41458610300300000c1c9800c5100c0040d02c1c05600c03511000080081c20403004181900317003c05042205d0f965800d480b03c0710701d5446264031851461b400f00c0d8102c0815844204070300c1d00200c000d91399684a040481c0a0107065070124000c0d0024020981400128030a03100015401504022161507004001207505507101c3c100c4528042000000741015003417251002400c0303c04095500d65103022030745401c00000d20380280c140403c544040061401c04801c03681075030b600c1480184c450603150214401401040c890584aa1a160000c15201d030414040c019904100104110341d03900e410303074091411010b0360f14050b00644145c102010502a4001e00038152848003a4848928143c0300c1a038040d001241a04003a08009101c5265a0f8140820310281407144c0181c074203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 446766339 1250 446765089 446765101
    0x2101050703020a23040e041406070e0a150311030a230106080f092503050d0f08060f0301090b010b071209060507030c080909100801150f0b03060111100c080f 69
    0x2610001180b04005010755403601314405074400a903005446440140d90040c6054030309944428560032246641e0301c2110005008240b14002210000c2d102070542000c280c03400c81144d007a884003030a4582450340760040701040c91650009103119002c032080c049094104050b40e12050010905400340750028400184440c1d5000700b42550080c151710400d12180e13440e400784038100418a5000c15004091401c4606090001d1404800f560b005805441d000e50030170f6000c0d24004240c400704408554000e000800a240401b41a4600d850250003c551180d241c0d0390201c1403502600114129040400c80006008480e40c0000c0c1d00b03029810180c007601c3c1045006090b5000d006070042c2001404288035041100b15010740e040c0480141684c03480d401c0420921080c42c0a80c0502c0d00782e0b6181040144001038503000c171000f02d40005000710b1080341004c20152499000600703030783c144140c0b00e84240764074070b080040503030301c130b40341c640000e0a010a440018500c44001d8080980c100c004814000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 446767589 1250 446766339 446766347
    0x90b060309030405211506090703090302070e1b120f0105030f030403060510080f101a01050906071b120b010501080402130903030b0a090f060909030914030106052101050703020a 78
    0x2604e100f00c88011000e4080025900e00084c032030b402d14118010340e071940e0b51914130005010f010726070031629591181d480d80b100b02d0803178031807190240c01680040d01c100100c0620f801e809401c4226081d000c0003004c1d40d0010035159a00c920b04403070140c0c0500003081484141081e09502500c03044028100380075440c10025a02d01903400050202e070f6554005c62411b0400c081100010040c80d0141c0f196800c50b003070095100d484902d1381c0c1c0c86807810b240d403485004480d11401d2208500c140c59450502640c9020720800350841202240d00c0c0043d100030300ea80b507000081400003464042440000300c15a0b2500507250301041e401981482a06c8050100503601e041e5000c1e0b208107007080008040c5038904040300504170100d4402d030040c011301d00105481c00340e900070b03044d07660b00d034030051000e00c0d42d410310041150b42000300a0000703801540240b01000d008800810031383d10080012070443d8130b130380001c0c039a4403012910154542007100b852011600c2070181c95409600c5090850900c00d81ca070b0003170 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 446768839 1250 446767589 446767597
    0x5030405090601110619140c070515060d031803060e0f010f021e07050c100f020f0616080417030c04080c0102070b0306040c020703080708030f152416030801090b06030903 75
    0x1084117074486d00f044111816681c04040b41500441c0718070410f0804c0c5203804201c0e8040b06003a5054040ca5502600c3c0d1075a10461034003500d0003501341c0d18581c80c2510200c0d02c00144111300c030600b47c82c000700000850041e00441e08100c8035800178103c15000c900c801d070f08442005e4a000181c90062007294458400110040004c840d06030b491550b0b1700b030301d107404ea0420722060400c1c1e900940c2c0c2c80c000360340306a0107a254026445990226881c06020325030341661102d0490741040f150100325041010305204054080d0802e01c5240480c0c04e140300e1100315100b030b820840354210002c0f80801c00300300ca40710810407000c81d04004e00141403440e0502c2d0b0849100c2c4001050140210307140c036244a030f0103108008000c002c5800c07034896900da2815240488640d4030a58003034112200000c0030a10040755400c0c2e4605585009003082580c010500116035461030a0702c0c40c0150381402c1c03003120340760064111460221442565196200c0d07050085050480381c640d0640e9000b400c0a00030852810400422a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 446770089 1250 446768839 446768851
    0xe0c1305010b0904020d0f110307090902131208160f060501090e0a060c0203130306150803030118090606080d020a14012f0708180a061103160302030412050304050906011106 76
    0x5640d84071b0b186820405082840501d900e043e00d07000381080c1034030400d0003440c0079404564036035034210307691002c1c03101381d0280c0342500400001c3d100040100d919194410206d051042038000d04100c3c1d030008a00b1511882c0b001a1140c07580e507400700c0204201c501c280c6001d850170b180304105100c410491141d4440c05140c2c001d10059903410710002c0f0600030015148858035940401180c10b49034500000506488898411440c85030f035408240f40d0004015070341600c0506285a0140034500b01d80b03000350a4810050703e85650b00e80010641c40402c0c400b14039020803035002005001d8a81c40c0028034a5182d002e4042c16901d0610010038600c02502c640d001c0100c1c007090703205003030001c2440650300e00c29094010301b2420009124500d4a40341040c0e0399042e902218150550b40d0b95030010b5440c22841100c0d8109278004001a4099006001402d258140244100d0b0f043c2034403506040900243c070a0240e030b41c2d0b440810200f00a01d00410b440780d02c05402c0c60b0171001c4584602117103540b02c0014110f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 446771339 1250 446770089 446770091
    0x91d0603030408070b04150305061c0809040903030b12120906070c08070612050601020307020105070807030905031603020406080d0503010b0a111207050607090305030307210e0c1305010b0904 84
    0x8141103603410030946002c1c101260680e080541d55175a242401d5100344146400e801d0a5005101d102e8001e1003180c2c0f1829000d0008405241c800c201c0200350903c0d641e00703c403590341c244001d01c0261100c0c410304985074440d860000e00030384644100a134412811050781c909034044807940f190b07042c00c40161a0000070660b9020b40b500c01c0341c507240c030b00302080f0f27003140c201c1c1e200b444070005e4541d0744205d01500c10140719101f00070329202d0308012a281c0c03140f02c02c040c5c04900d00700454000940002c0c02405c41d54064504006120f0310380340024141045050000314040301e410091042d071602d8400c5800070b00c580b0006065825114002a2043c041441490b0002d000071072480c40c0d080c012088503030f10410741c0050f01c80001851007120f0880d00200e5040e103441c441c4000060f0320314000c5010106898201004504550321454201d852040c41440c59000004511660440c00164025a480c8007003400180150031220014441c2940b50000b0102d80c550070309004102c0c48800d0070403100c2210040d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 446772589 1250 446771339 446771341
    0x5010311041a040938060f040902030703140c03060103020906010e01110304081606020d1d130f020c01051308030604050606160302062a04050427060b10091d 69
    0x30354881002d02d49200c00e801504000d6808200300480880705808841d0f20a204248074511000d0700e0f482c2c404450480310090000c0109195180c138031b4240d0a149001440404d001e0402d030b020900f0400107600850b4008610812001810400d11911551070410340042c4540c7d89903070005580060080c1c13600381804841c2d2824000e0b03902c60805400b00b4211002140d9807a9510600e031991081c049000848a00e611100415070501c0410710036800740d817a6907045400558001505006ca0105008552040b81018003088040c02405403900414052200584601191100c1c034290307140201007940000c4480e203014001000034040d2078011506a600045a07a60f4601145451040c3c0300020740303401d401110042010760018600b17210300304810f1000010f00d4000c0c0040000c015a404404020100b4001400030b81000c0d84034501c001c01d514040d140480b601c064010a000c0300b450162541a01d034cc00361000d60415003c81c009007811440e000d00540d1409401c0b40e2000c616050000e28041e88034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 446773839 1250 446772589 446772611
    0x10302101b02091b075003090307120606080105010b04030b1e09030702011d06040603201935040201022805060f0405031e0c0d050414040501031104 65
    0x1010b01003089031220302072a40e980369800c210b8166a02044007051206152450740e08100c01c0c1186c60900418262941061000c0401419a400155014640076210a02001005030703001c10202c4000d0000b08480304244140b414180d003502d010740c02c140ca0982c1880f004003c03250900e0110741c101c0f40c0042100c074080c1c8a0103503000310320108004101d40c00e00080c00303000703610002000405400d8230036251a64184074040c41c40d441901c0c1202c0d6140d1100c414001006a14003d0700b0910100300349504040002d1082281841c158219241018a06480c0c0302a1500d072034002d03503d40da90b203800134128000f0101c096440b110024444682c1c200522040002c1401c590081003103008003161010446a07003000902e031119414601101621144581000b03d4540c2400303040032801550802c0286152040303c48141800d41d0500d0601c101100d010414001001d805202c90402d5015694545503a28a040c182010321030b44088014490b034904401040000c4a0070403103030b2101429030b0042034200b901 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 446775089 1250 446773839 446773861
    0x206010b191b0f230c22060506041d0a0504080f0d0b0d2607020906010f020a060e03031605091e010e0301090f02010f0906090e0406060b0a08010302101b0209 69
    0x881c400401d40d4028402e10810001c0380300364100318410fa20041120681c021444c9562007000b0500d103500300c110b100945038803181d4400b0120721025044400b04046aa03140412265401030b44024030395440380355048d0f040e64000d001c0c0c0740c100071100c1c42440141810740f40ca2280f4030600c083d50013041000203880d03030b1086258001e04e4092800074400707403044440703080800c3e40c8005001c40c01e01e5034000c001e5500200c6001c100351558180c01421340002559418015a40e80c09684034080a51066042400001d42c450164000501d40d0102854580c24920400c442b01d5440e44604000c1c80001e0103605442d40b24100200c0e40c0c4040868074660380c401c00c00c016500c08413000e441513015401c181d801000c3c020b1444848010a01c01c2c1d81d850203041182000310342010300350003002c001079281c071010040c01000d02041c58005008d588009a0036980c0d4540784070b290320080800d004284d45100400551500d01c14124620799141008400c000f1007048040101c1040b51000b889440420040b400754450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 446776339 1250 446775089 446775137
    0x12020703030b040c0903060e0d050706020306030c12071d090a150b042904060e07050a120207030815190e0408160c0915030308070309050a060612030206010b19 70
    0x6802044104c0700000003c00308406030005950b194140300058140701c00c0040c0381e000007040c40d0383d4103041c0007442d03480c0000781d800541034540c54415458000389a0303450031404031000110000515485180c1070f0468074445142c04000c5d800c42c600c0c420400c0540c008192003d0555200c00142c0c43c418881c003e01009080400c42590040d2410b2400408410000100d610f6075560701100d01114452804100590300d43e8000d0403442c10f07802c4e0100d000140100c0c040d01818040b824440c48903400505400102e82001c1c0055000807a0f86044c800d615203041d1140c1c407002401d40d00300d4144000c0d200415540e00040c458401403800d014001403c0c01107990580d15501c10340c82940504900f941001b055142d070380e00441921626108460182100c003005071f0007140ea050711000f07025030f29118150024500c0400a035403031300030320300210006020343c031580018200a1922403046c40103410000d1811005820002811504200200440d200762030115180d100c0c40c9440d20290b20001c50034200416 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 446777589 1250 446776339 446776361
    0xd05160815090703050a0209041a0a0507030f0b03060123030f03040806010f120605130b090106080c030f070302060a090803180f01081306021e030a0b030c010f1202070303 75
    0x9419040030406103000310350807003190711010003456a501c4516202c0c2c1c035265640320081403588241030540050030300294051744940105081c00d190841c2e01c80803181000c04407955030a2958450400000541502c200e280446814000304050381d40400465680c00060090250b01c203a01000c03549000d05000d11600d210b040541030740c00c0e0131014804641d0340d0b0810b001b40052400382c0c0c0c002003986030754400310008030f90701d038030012007210720b1900ca0074000c140150258401380460440d0802103980c10b8000350240c0c11170400008c0c0d2038a4001d80364108201c030060b05120707070010702c4020b170001c200144440c242d03a011a2803541c1d0305401b103c25513400440e40c0c0052000d001c003080301a107008501140d180310b44400c1e40c40e040e12015090044480050880300551880a03001046000c40d41d140e000d0900901d0103100c41144080320b041900711600200d5480542944880145060b81014452244044803e0801d0361010510740400303040c07061402420020746a01090715014184281c2103003020364 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 446778839 1250 446777589 446777623
    0x10b01120e01270c05011701060e01140703020d02060a06030221010b09012306040e16231b070b12060f0405040308071e020a20030106120c05010903110d05 68
    0x14484010b9149030307060408203540854000700c0001e21940201003800c1a1064582039580507800c208061b0f40140ac000a46410070040d50320b00086400f80c1001450303100d02070740050182c6522140b0092404900502c80075125052030300400050b100d802e0140c2e44640700004c244a2100002600b500506144d04c1d510ba200d000031000050301160700c070401200c003080c0c450003050406640b0500c1154459841144014030700c1c00001012800b95080004e104880c5103484600716408004891044083c40b2141c2e540d400001003e82e0604107a25071b6910a1b1052030260080c6403422154a4140c01a4041e41d0f01480301c810008010b03503220071007400c440a005100b00001c0c10b0034200286101d0085a00d180480e656403030500704003001d861084843e0301d0980c01001100615034a64a881c41d01c00b004040300c0c03c4004614082d0f40e003e0143c840030b026240c05e003428003c000d00700300c0c11100c060360000b410300000580503c04030f07440003030003a0186000e441c95440d0000c075160152a00c00c0325128001c4075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 446780089 1250 446778839 446778881
    0x803010323011a0405070c06020d02090f0d020d0210092303011406031f0213091e0213030206090303130e06011709030a0309080c060406060e09010b01120e01 69
    0x301c0030070381d00e04985118440c1e103680c10040c0c88a007400c031100480e40f4045140e0200401101c1c3c60aa001141c0c00301d10391070700c0e560642079070340d4500030380e0416250100980d4021903555407a0800d20040c2e00c2c2c0030390890710a00100010740115050444c50750010740501c2c40803404036200381c051320901008258104150030121450310b01d0490003184c81c0540382c0302c3d5013480d0095031804a42080507000783c400030060811070008200142c191003040c441c8520060f000d0081056040a00088500610310300c2e801150032107035200d00100c0c03440d0300c40307048851a106104408640050210444c05d407a81514030b40d640305201030010b0b2850140d210100e42013031800101142d4544441c1e501c500601c42038891300000c0050500c607118802048030301c6030300e5a10a010914400e48242c0200514502034900e492800200010217414040304440544146071681001c00c12003030000300c0c2c6a400f0341008000c00003100c499000a191141c040c3c61000c04540340d020040c20700c2029070000d500a03101c4440f81d150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 446781339 1250 446780089 446780093
    0xc03060605042901080702010f1410050d0822031509021306030302030f0d0b030d0c121e0315360605030a03110c0603011e0602240a020708030103 64
    0x80c00007405918091400d041407980d241d2400c1e041c0c0c0400c076201200c584200c42c840001107070366a400420140840d900c0303201108111314540b0071042c100b0a0000c00700e00384c1c0392200030000c0040c0720350320007406440101c0c640350220f401801501c0400282c860132843d00d0a00004c4039807689140c6d0800b0709074107405254030061700055070105c00d046200755800c0511079400050754046840611001d005600304000600715010520010296810791000000f40b0214840200e8604140c0c0808000820b40d0f50f400642440b50304a1000d210340c6240c985514001694815640081c0e200329a540074182c43d0001112054000300c601c102a1100c130782141c1c114102400c041e10411607109e4410781d061100b07000059005201c1c0030310802d0380c0c4081c009210030441a039088070144184400c1c1d551038002c0c61203d81141da510b00c0150700030b00001c01d440070b60f1b4909000740c0d8001c41583c0d10100075540034690105403182003400c81c1031301c40c0b030300c4407400440e030358102c907900c0030f07104110004103120000400481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 446782589 1250 446781339 446781341
    0x509030a02060702191e0c0b070b0c09011409010201091403071103010b060717090a1418010e070c05010e01020a09060f0315180e0d02062d0a0203070c0c0306 69
    0x40044a5800c81d1072948036a14140e85030312000c1840e040f0a101010740f0000714500300f01c0402a90908491624046200e41f1064064486500500c0e80003030001180b500717020310048034540140c40e040c0035038030b00640c42c0006030010115491840601c078003c955900c0c1c41e030003980a400b0749500060f105110b1740320754030700c0e039100c2c0c0c040c01080368440c840d800b010b50981414480d2640e4150094006850701ba407035222a24488204518000d403040100012402d50300c0b032000e210000d14200c0000d40700072512804203c06003c001020060070480c92004010b40d851a001c86d07034100d441070030266040285814014090140003580010b698000141421070030381c1310700d60004541c0d640c0e5401c083e40815400403800e1302c0b10107403112070a0f1150401403010345071800682000307010030310002600139140d004042c1842c00c16400c0d140503811990401000c03070341e0344107041c103071140e4030300c0e080f10345101c40b03030384011b81d50b4040d140c054069400300000d0415030065001c121026040055030024940d80c1c07038540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 446783839 1250 446782589 446782597
    0xb18090411281d0c030402030322030201121802040506062703010c0207060207141f09030212070501080411032514151602041508340608060a0306050903 67
    0x14080342c0b0030340007421500c2291080711100920900110985a00010941c0c607000a002079900d80020416442030100840d1000780d0300284402c4005218614000076201001d03405803900614101890503030400d8a0104c0c1c69952581198001100c0e02c410012801601400002085500c0481c1700341d06c9690440c0405054118114000c0c000444e401c141281c035110644a80c00c00340e804000c081c00b0466150f51001c0f070300b5001070004180c0d0300c080e4130701402240b03603000240c0c081a125601801542044050070710003500b484010541140340c2000208040d000402c0641800344019034a081c0ba41d042c81100794000510000c000e420002885110340e1209911846128100c0700c03608082a007046922480b402070304955445c20403041c615101d0070808000d0080741c0c0f1076074403039035014030381071030400305000d400000000e202c22682007609505010790180c40d1401491560000002c0d54018015041030328154034105043e600c603d00800c00383c58440c3c1004101a09150030003203440c10004c060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 446785089 1250 446783839 446783899
    0x20d050601030e0613081201090203060a0b031005120f070305030c010605040501150809010e19060e0a020d02100c06052508060328020d03050703090b18090411 70
    0x10019900c40e080150b0494031103071400c10b1140c010b200007900042043d40014400b6024111840c03401c00c2a0054254204098201014540d404400d0003664100008020041c201070042c3e5803850400040d82a4600c1031407180600c0303a0041a10b03002c2c011010f2180310001c0d500340342201d103c540c90740741164982d040800d5803407041d883e15200090510385401400e040391761440220000c1d0039000401c80c0c41103401040010a0b40d01c800e03034076125030000c1224200303035030100102036410443d0b450100140c6d0703070180c0c0f28481039200d200c100d005a035841c261801965811600c03440c0700c1e8400b400075104011005400340400b07142908118818806034030b0428001c02c0c00311030001d00c1c5080001a1624082031351002d03056132114555104e9684003900002041c3c48070500c1420303d01b1280d000900000c0c98001c103c00284000c90094200741d08403a4100251001c0340c40241409800c2c411500c051094940c1c1511940c10724001c6001e00101c0c40880821301d0000e0403c0342590342c03000c050b4581010340542 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 446786339 1250 446785089 446785091
    0x4030c061115060f0303070b07081b031006030b032404020f240d060314010e060601090311042d050123010219080408070f06020129010f0306090c0201020d 68
    0x81c01ca522800308403582c0351600c0c1e01d8082c003940c55900a00441c00c1d500c0d04d085803d4441000b5420104148002040c420300f03e980d15a020b9262441581186c0d0341c0401c02000b0b8900103106018214541030215015284640360015051079443d001a06c2c000e03008054100020000b42007a540444015440b84128002c0e2030b040b030800c50310b02c203119204140d00002d440815a00700c84d1850000418004c0142100c0c1800c00324400e900c030340300d46050310700b40307400206580e654003220103100c501480300f55401082420030074000e9145440d04003401e068910301c14440c540e0740c1401070410f0303010800c0710010302210300b09005040100b000440288820701417401d07110700750802006000c03c000d001c0d000707a52041c0c2c068046400382c0c00c0b01400402200b08100c1d480c1c507080c400070982c2c4d08100020320003030054011052840d1b2600001a0844004120115040b4100c18015010016130260820154400c0c80e1203071444520900450003010950409102941040d0800bd5010b6054000e40710f007410b0014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 446787589 1250 446786339 446786357
    0x306060e01050303030414010204080106080c190503060c0d1b1701050f0d1b090207030503040303060509010b1902010e070920091f0302160303090327050d0809040204030c06 76
    0x68581940e5800744030b0641d05030700800005d000140c060b4031241d03060420000141c2440d0301c414445082d141035030484080e5520a43e14070302e440c603019050420030000030301a582154100b80c00700e07854803401091140c244100080094080c0c3c0183e210881818400300c1c1d01c0c200003641c210003811500c5001c8911079202484002240924104244e5191400003c0c000342d54450650760710480c903800101c02500241008800240340b9445000411400d4030030350703a2640d00d250516006c0c04840f0b4903000240524560401401411101400c44441d010f525101303030156181c4050403400351150030040740031400f45400020307400301c4c1d030b40000a000f0440b035649010840060400c2205008801c07285130301c1a185203d5684006002c10007640b184054580580b411404014111818554940c11030002e035035401800c05140d13107c40d0283d007154100151402d8100791801c1022255083d00429100e10302e02c42a400403c00000b0071a0b890010280c025910b0329601d08050b88490903c2c4680008540040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 446788839 1250 446787589 446787599
    0x150d030c38010602030a0e0a03051506180402060d050a0b030d020f0c03120a080915010e0106090509071d011206030c060e060a050708180306091c0e010818210301030606 74
    0x81c20641640ca09600840c01d01c2003002d41190281002d440481d0003100741b0b00701102140043c84030900751031052400c0481400d21805200c410700c0c0c940d461482c00002c4806100060352103070119030481c81c0c201008617550312410300d03100c003c0003500d605903414860080c040f00300d5500814050034103400b85003030711400300480061540702c201071851240241010044058014000d0f42000d810100050840b07260403604510030082402c03c0e00890b8040c55940d00400c2110351151402c006440d082d100b800040c1030889001d400d5481e040c0220781d5031348404610f40503503481040e5601b000e6000000c117202031907a03810160b01c01c40a50040030b0000c2d84a00c02141d6a0030148101c940e2000d081e950a46820007584070a841600450001c1c010864100444280d03960100943d0b40500040f40140c440103101c51004000f10b00208040018410f0b080d03c0070500b030781c1100310a44d000400c030011407001d40041d0056414800303806074090b500e04a0f03a0b0f8421243d403036000a5816030348158420030120380c480c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 446790089 1250 446788839 446788943
    0x71a0411010801150e0904050c060a0903121b170c1624020a11040b060705030931050a0e030c0708100504080d09050c04020a021b09150d030c 62
    0x481121000f05e2800310a0070002d09000a00a03805070190050740c55140d042400206035500483e100000201c446100f441800400c0d0b41d0700606080c2410708170000000000c3d1a000c00d08546800fa15019003c25407030100204002200c40c0c000c0d0001c00c0d0b03110a00d600d02040c00d0312425000d1020000380ca20750881030040150045e0394400d02c2500106000c070ba5981d41c2114610803200e07000e0b0440d454100c18075081c0c1307a4a01401e00c044c030407000355486050030b6060003003846410015034902c20b02d44003280191814920f040c9840d1b1050140032034180e031214625400352410840710219032000158003080710341c0110300c40c41138550f00da090340d00201d465940c40082d0b0f0025a805032040c40c040040140881e82c69100d020305901c214141c44e18208510009030480c2c02c030007181009604113644426441a00c3c0988090500c0d044075840441c0c2000070081c00c4109101c02c503180241400f040c0803042c14058614061004e51140e034000b07041070704c07044031140030880d44410003110f400c901001c2c1802241d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 446791339 1250 446790089 446790119
    0x13140108012304050c1c060c0201091205310302120607020d0c03020f0a12020c0402070506070e0a0807090c0305070201021e0307030e03160201090803070b0c071a0411010801 76
    0x40c1c2e841c6000100b01030a1000141020708111071503c40e0a01400440d100c504180804d100c10940e803035428800c6040940070f441052078003078116498842401b0001d80d681c41340002c4040e051802c40d4440000c0e400104055040b203484464040d034090300c0c481003d20244018041c3c0e442520144070859200130181d564402c103541940150308030442c801e0b1002d200303d050300e015a000c0c5c8126803404010300f500c0360030904a01c0c0f003510315500c0b04520030304003901000502c0c500f02099808600e004100d480316501c500e800303042c0801700000c60f4406a601c4c0d41d4202d010b40581a01419180b419039903602c3c102c020000302c1c40b0900406e05103400104054010310070b0380d0390842d0340c0940038441032012040300c039207a100420070402c1c1a0b80b41c4940e00d80440810150030011200000b08446240500014150540c0e550042641d9801007000c2e80000350204038035508100d00d02c1c05192984c50616003010f10211030210600301019160800040c040205000c4010f50801e803501c50043c3d803140c061b0104400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 446792589 1250 446791339 446791361
    0x80c03070621021602180123031506032d070605040e04060f02160f02030f1204090515120d090e091e01230718120f111314010801 57
    0x44480c159075001801e4005113580b20482d0071407411a08680d0004184008400c007000c440130407240140401d5030750420901d16141200c115030900a004800680d9520318040848095103681d00850826282006084d03071118005001c0c03091388180540c000540440c0050029081c0306220000804500402c101d074261551201d0844103562103485030005081031404001915608003c0644240100100310003d1072050450340202441401014980f0125118041d03094010815181d0000c2075031040701c048074002100400d4139070b82c8440010000070403070011030704880140b4581c40070070400300d64201560f08540b5000f107d103845030b1015481c140d04030f5054400d40d014026209007498442d001c1c040400700c0d140041000c1c64040c1150760842c40c40d5513000710b0144070030107009040c2d800a130303994410008a81d196100328680b4500702d02162211350701501800369050401d082c1b2000c00007150285102034040e03928540400b1801d001403003250f16065100f1006400401c110300d06018101c4510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 446793839 1250 446792589 446792627
    0x705010507030f030915020f04030c05030613020d1704030b0703050a09030936020717090a18150807060f0201060b030a110403060501060309020907030905250b04080c030706 76
    0x203800c0f11001e5000740040c44081d0364042e0705802c0003165a00500040010340078143d41e40b5102d0b851480c00007082c003025003120f4481d400c02002c11104411030714648030001c0e0101ca070207039040c249040520f81c081503c9117500365080d0004010003407011100d00240038800d01d59040199036102c2c030801d000c5500b00200240000c0a8480030001100030f05040048850300d843e040325007508000e400312180021070750780102550085040c07000d0081c0c0c402608004100324001c1d51030440c4010000720654414001c2c0021001e80d4814031503204060b0b03110028690840c103032016510b48541300c02c4d43e503000a200d80c000080203a81000f12451060086000702c4100c20005d50454803501224009080041001d164480b402e01000000c220540200c500070801c0d5240050440010300602c69501801090075092500f400c0350580003c000240c5d0a0100782c90888401d00d4034091070005000c224242c2c03046070784840100300490250000300e8403086028040741191039495940006448001c0305001c80d410302 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 446795089 1250 446793839 446793857
    0x2030c18090f070f020304090608012705060402150c0f010b1c0c1a070506161706032116140609010b03071202060409050106051206060f0f07170403080c070501050703 73
    0x209019942d01d0040b813040340190b82c100b82d1510b100c0c0003150004d9102a5550b074440c00c28180303113071125982022403605000e45151844482d190b569132150007420080c0242d0000c1d81c140c130003148510a40d4110314803d404d44d00410140d04903d4003800700751008500c180c80c0104041441c14880c0e1090214550200901c4aa80c1c9030452000c4064081642c42a5004041103010001070b01408028850441d90901c0c0c0f0003940440c10007080114518214103000702104180a51541c00003a40d206200c0700204000746c2042c1081c811005000701042190500d016488850401522030207440d9000702e01c400f2101700e03030396001d0114240c80104084a4060b00b0900061006000d20843c42c0c0207640042e0046240603550030b01d810490300d00740e03c503000040c404100300100c104c4043c1c0c0f8580001c0211100390404150f00006000382c4070b0b004400c2c50b40440021507000304044000c1840c40551106911510b81d5504d0400000c1580040112a000e0181250200d01036005606480b8050b4041e9984021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 446796339 1250 446795089 446795101
    0x30605240d0323070302030c07150c0605180106151202131712031915050102070b07021309030e190b0d0e2a030c061606020703110102030c18090f 64
    0x30310800010551000c0000701600c00543c10400070b00382644264000d590f81c3ca2407040742420202690040d1900d101300c5107114000c2c99004030288141a01b0000002d0541c6405803840c400c242e8444140b0503e50030030100041c0b4040100440403404000d4450342c00c06c40510307400c08224030035105040c07084061094288100e0310420004412507840c8422610980200c0d0600045034104036540d0001c682c0510000100143d80d0140184802c05032200018050800c0d002035240c1c1441d020b400314003540802e110055668141c03c00c0e01e044a66601041005c40d030f400c0040032500811541409100215070b00c00c1c0070540d8001d1101190031842c034050070288175090f140040d100e907032180141c520403181d0004a0300300c000d099180104c080810b410031004031600381400d00001032807445c441e4009004d600c0ca10000600c0e0404299448400140d64034a07a140513603240000459a071015840401004469046a8010309000036041c00754003128040c40208903401c88101c804507100e0f40c00300e0100d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 446797589 1250 446796339 446796347
    0x606050f07060504080c030301030615060203210a02070b040606030303061a0307210e060423061f1e03020f0a121103210301090b030102040f0312120501030605240d03 73
    0x14000d1300c100c500c40d246ca48140c56803491500f00780c20546495503102d50031400c03541100c0f520310044c010743c00550b062041c006414500354500c0341c4801c034448561000140340400766411950030550281d1082e03800d00302400d00200401040c00100d01181c0b0304040407030b070347d845d48071b0758150850060384103481d541c0d0b14001151180d45040c1c00500903c0c5c8684131040300800b501680340e1607180030380100074903e03190600a0741e000800416131060248010880290301001c2095640082120022550030152481c484c0041c40580d01c1540003501002e18041642102210070040f40d00031a0f584800700590010860380d1070403403041303c0401103c0c420b45800110382a00c040c20001005041d074811680ca1030440c800f0311400d007030041820600100510644000d4410306444070001d030001c50805003000c0007807001c50790602000d040782d40424842036046101d1040006206100441440b165035039141400c007500060310003900c0c400c040c86041840001c0c0c0030b48689808801041c03040080001c1d00c06503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 446798839 1250 446797589 446797591
    0xd090201121406010305180d1808070b0301060914010507020909070e13150e0c13061a07060b10140d0209180402091803120a0213060306090606050f070605 68
    0xa05010340110000c58960003446840c0340c45001e00b5806400f45006000141150401090841d0080c503529034070101c22800102c04d15204039600740715080c0c0407016031142c0243d41590190405208855001c5401070700c9102450407100c07161107000d00c881d100c06a440f111140300c6940d0380010030a110290241c60501c0039150800c5992094a294a44880c4c012907c034000302d85811241d03000d0034100041100001c408200d00040c0d28003000002160f190b1951242d0103e071403240706070301d400040c40e5201900c1d4081002010020303c9100140062004400c5079041040e060701c0103850104801401e081482085500704895070300e040c00368460500f507820799003010320b0103103441e942030282c00815200c0ca070054100b23110540b41c544c0d29203058410001c0711003004207901c8181d019400b0003200d0410000940303269080305100707034180ba035503000400024022180009508101700b0000145a9010382c410803d5070188401032221070b480b00c80c15201e0744a600c2c0c452601110410480e0080340c06030b403200b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 446800089 1250 446798839 446798843
    0x8030f06060d0903021e0f0a1202100e0601030606090b010e060d020c03030f0108060c0403031e03091217010902040311150f0d06080c0405040302060a2007030203030a1805030d09 78
    0x10b0418103800070003401c444000c0b8085000da4060f204013a20140510080703002c4101d0040140540c1070342e61881e5032904181d0710010004542c00340c60401c098002c0c001d000321184101c0080000d4203400d80f10320b07913941003880195403040c80c00d074006c9605034690044005641c41a110400d0204140003803010581c007035034001200c90360901c26501241020b000540c00345510b1188a4160750514201c42c2c1010005011024201c40806c01080041c1d0007000e03d80445d003210b8414809603103654800d8000e00413103e801401941e0503140c0800c03a0360009203030301c0c0c24804072480e81400e81c0c945002c0c008a109074040940000d13120583d5441510f080f40d1010b940c2800301c0403090030689420004d50440c0c02c950381c01c00c1810f441d5101403003520403c0000b010b490008550603c42414940c40103510789401505103044d250b01c030031f55442002002008041c45200000813175944280900b40251a9003003500e4441105042400380f80300000265046030710290440003452500381d807480000f00070281c502003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 446801339 1250 446800089 446800099
    0x1080a060f0b030103050d08090d211805010b1c0b04060b150c010b030111040b07031119050c0d03201009030c050c1f1d060c0f061308030f06 62
    0x45028900118941d0081511001954882d4117518042c0d0a140c21101031b401001404810446490b40c0022000014110f40c04d142030041c007580b40350b407071001519400c01c860605007200e0a140d0b10300400c1c0c19803080d0146000f0803414407000100b2440705107a1601d0b002002c42c5941d01c80103d2402c25085400c00e10500001036010301d04408940c0010222141500d240c0c0c0100744d14610903001c0c0501c26040708110000c12110384290410300d52805907000b0180109070106d4401d0805000303401e6250760022280c00c0301c02003907103c2d0481c111001050012519401410840065811b0041c00c03014403a9054543c011000100700000000100362401e0302e81d18400c210381032441040c58420140c0c07403802581c545034181003038103200340f6029045000a0184101040412000c004802150a41a840e1502e07070041615900c0f8040305100650603241c1c0010300160742c404c0e40400040c801c4500080303c080c0d840654401000218060314580c0c00f03040000204001400d044220740c4c081d42c40640180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 446802589 1250 446801339 446801351
    0x1e010315030209010806090f06060d11011809050109060801090b2d0c12010b090f0906041103090102030106090b0304050c1512070e0f0604050307090f0209060c0a02040f051501080a 79
    0x8070207201c20784c1703c069250002028000005801d100d9544803980120040486042c1074001c14000b507440000649401944ca4103120350f607101d005a4100405009100c2030100e890f00c841900504087c8035000b105450b020000402c9081170043d21005900081d00407541d68a965402d078142401c15140000c821410100e50b81047c2c05840d440d00031a0b00d0040180c9802d0b500412800400d01030300310000700101800001566541c82000d820503000a0301c02060686460012130081c05101c281c21400b00404410800695030541c0a035040f41c825039941c4070110350b1187d403010310784030a58025005070400e0009800ba810800c0582c20300c01345044060f4078120020720784810034a021f403040c0c00029294ac1c030a0049280911404c194180c08607281c5281a203840c000a81d44e0260744200d02c016502d49030b04a001700115030545074031010150005903948080440700c1e0311602e5441040b40304520704481000b46041600c0381c50710804980d030800c1d030049900c0703005440485004205030641c9441d01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 446803839 1250 446802589 446802593
    0x90402040b090c09010e01030605031e19051f060303091202060702040e100c0509010f030b130c0519090f3302150609040503040b18030d0507111e01031503 68
    0x1810380d43c880d2030514002500c54082000042c0341000d4111354504040c2461301c140b0543c0d90118000460728500d911508a0407098813a0354180b1108074410032806501003581000e07c0703404210031030388176460008444100200c4541c03008865003401702400103860a6024000040c02d01c40d68180703540004d20190905140e90300044c1620304c031904c07051490b002050110040e800a010f0407440036000e0800508104a81e4002091004818030613000c05842d01011050b5071030b4030102c43c4a039030350036a040c02881c0f59084050704541c080c0c48861702c60342d801d00c1c0c0a01c2c000c0c410132041c0d094038140d811a0001c1d600e80901c012024903041200090405d0550310001c0c00d0407030a40d42110411541c0141110403104d0102c08044400180058000c2c4102410000090320110440e41540c59017245262100c00040780d520305107016014442c3c1520950b0192145e8039002070140040f90700c541c03004000841032805020210081540c8000c200165807400f109560080d001aa85080b030020b104000c16601e0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 446805089 1250 446803839 446803849
    0x703080f0903060114121c051303020a090c080a060602070614090918071e031403070804030317060303091518030106030b16050c12070309031a06030c011b02090402040b 74
    0x20380c4103170080340c0d01c1c3c145080e5504041c48010107036003041e0003501090345045050743c21442000356203010000b002132480c8240048001c6036003c0d54010300720b01c880c02c0c4c540328040f0041060180100201d032060300025151800e601030b03007040c0c0d05154043e1001c40d2914009860104441c14030320300c40c0206005054190b02c03106040f92003a01c000c100c3c4141701c481c0200d02800c1c018280c008e00c1c0745c0084c003144030181c2c5544120351402c807a030110f07000b80c80d0380710884914114013078020028251800000d00200380740e8000d0381401c00004a108071038240c2c480004059032403088203450350b04a41d51409041400003000c0c0600064103052140210201020002a0841c1c400390001c407404990071090200d4098030210800f80c03d0000c3c20000d26004401c0103456807481030280d404804a0002018401c261041c4d41081c005c640c0046440c01d00710703c0008490450a040710128064401c2c0440c41040d0f6218104464602510700d020200c0e82c407154083c00f80490b0000c00c203a800c0343e00c400d0640720710744803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 446806339 1250 446805089 446805091
    0x27023a060f0f060f0506040303050f030c1204030e030105010b0909150301020d021216080408030103060e0a061b1e0516050a21031a091f05030706090f0906080703080f090306 76
    0x4048000fa00c40d0a042078901075038459000b91340582001c0c0010300c0001e411100b01c90002041025840e00c952714850704219600c54060b032207075499900000e100c01c05800044808011801301d0090109a032541d1501c0180e02079100e08517801a03160012440241d2980102c01b80504060000b45c07038681c00c0d50541050f40c0c000da0507849000d105104025044100704418486006680760505880c1400c1e150381c2183c0c08103010207010031342d40e989002090a810001e454109501001c24003902201580007440c40b0140c000300c1c00851071580540e0300f880c01b0480c00500b00111922068204003448017007200841d8500d8040b1454804e10201c0c00c08501c0f150b58800e54032400a6102c5111608000f0080655100f0384d44001c4081804280d010f403617807441c4c100c1d58418000910024440a0480f484203600c00039840150140607988001c105550f00680309015142c8002c41041e0721030303450b18060100d0301240b280c0031254000c0b040030300000c1c07001c900038802c814801d101e840c10014060002410200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 446807589 1250 446806339 446806361
    0x30703170403030315062109061b0305070c1203180b04060b03070801110a08040201120509061b120601231306030c022e27023a060f 58
    0x3020030200201580750091084030fa01d8800d20f100164030341900a40100d444c0c1c01c0c00210100301e1100d0145040341e603400050003580000e01848514540820030040080172012400000d013400c0019020b50f000b041d4680032194081c000001c0c030a501c40e01103006001e0341c020100320780c800305050f03c042a01ea50210b0302072409242c0000d03030015890304052a0000c60342c07081816034109041c5e0b40b44420014141d41c01d04645080030a0540c3c0d50f480126011b01d2044814221145001c00788120030030001211803140c00ca000c6000915808107010748941d0190003800c0301c0c0342c04000c000611a502c20200d06589003017114000209000c22105c40105401685044ca8000c0307400310100421981806600285282c034006410358014540580c900071011030040c00030131499503500d079010710b0540d2001041a0301d120b45040200301040c544088030041d4501640b09101400014808100c200310400e02c80c00c1e5a03450604503d005101e21500440000080e510f0340d6407941d08810180e46030143d401114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 446808839 1250 446807589 446807633
    0x3030f0d0213050307080d050d0b0d0b06090703020c101805070e15120c1509060c030301030b0c0a1d010e09011203021213090b0307091503060c140304020f030703 71
    0x420082c0c00700c0303514440e50700030351203584152800c000c42c039070104040c18122010310f00541d86605c0d0403214800741c034442d1207103a0440e0018402100f032100740380c0c400c0d0003900125010145512800e030101c081e0302400001091541001c0c1c03266440506587c07012010280e1440924422022919400e0a0a40507888250542c0030082004030042490102d4000607508031207c0400082c290021503464000c0403440d802440700407404485210088151007542d03a0041c401075880a8801480781c4982081c84200c03221012000410700c083c028409070b6600e0007403991002ca0300c0c40314a80344036403602107081c0b05041c03008244082803e5202e08070790380e01900811004c420a018585402482c003801c4160315400c1070414031101006440600404003220010703840071031804d608400290500e0f225501041c0d1091608440400c502283c00b96581140d021300802c00035040d100c070090343c070081c25019040c0004800c10000e001443c080100c0726000c24042c0454035413540b65910603040491910a9141e81 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 446810089 1250 446808839 446808847
    0xc09011206050a0c1b030e0603010f060e030703050d080a0b03060c12090106050f010c170c0703120c0507050409050109050607031505011b030807050c060705040302041406090a020903030f0d02 84
    0x442402d000d4240c00c4040c1c0c0d0b030200032a81c0010390041200640c040901c101ea00b18041c49410315106280d00b03529880000c103940c1d03032940d48828845900c52607129074008038615100c1706401d07203404203442c0c0032207030060b015240b1401030031800c40ba8060010221b40040f40d0b03401501032962420000e02e481152101e103656610252880358031504280145a0300d0a40c0c1070540a20044c0c9500c5400c149090f003e0a020f44651150300e0070403101145070300b10060440011421500350303e00003c403075040368011465400070040005040f10f00880d00f0b1000743c41c59010b58020055400c0c1548010038650150000142491380e581c0d0b524100507055403100000394403071070026003e900040e0180020242424030480d030303101981e24a006481c41c4540a8244049030b00050f01e0107004204540d085995401035038503a152290028100742c005010990081d4a03040300f10071110142c03200035001d010000c003243c000341d80e03110750039020394000107032030743c040c0000d02c080c50b1001c445502078484401c40307100258403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 446811339 1250 446810089 446810093
    0x4260d020d080a09050709051330050c030a0516060f1e02090906060f040e010303050324030309151903060503011a0108070503040c1829010e0108090c090112 69
    0x40e04409407080001c0c80c0751114135400a5800103078113007201c80b5084046640d540e4541440e0003400040320141014802e9107298204011880c42849241c070320f144c80c0c0b18070031054141150b9038090610000c5040c1c0c01040030a0802e4040c1d000b620401d2000d84410407205c40c6035855509441182d0711031580151240d403098000d005101448241c419148070460901c100c000004080f808064266401094001b0358190080e0048040340e000d0825200503480c65692854000d21a52045480c0802c940d002c0c00c100907214842d001d80e254404000b0011400c0c1000281040513001070700b00360301c1001c0800c04c82960b0006003a8940700c10440544c0300007521514000500d03003507032803244c404400ca0102c080010100c0e038212545540118662429a8030307559140742c2a0020055a089000e208891814481c1160501d8004918032064403d900b4070318003800c01c60940360b801050049011424070701d0081807175442000e00b1640401000e0848112402c800003149240e0000e8100040c501b03902680901 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 446812589 1250 446811339 446811347
    0x40317031603020906070206031f03030c030305100501140a0c051f111e030a20070201030b040b012c100f17060d0f052a01140f04260d020d 61
    0x4080e041c2c00c043d480e003181d00001410b503119801000780b04210100104030341d40710690031001b21030315203481c1c68461510f0b401c0241c80c88d00051002c400107410311000426020030910458211641a15100e41a030341107003404580303811a40e070302303001c0040c06110003010840030051b00010300411001441d0206440302480183d4034405440300c080c150411400705500b643e0600002e20801c1d03801519225100c1c01030003409030405d40ca04100750310745009102140c60b044402049414400d880c2004cc0c0800300d0309000640f140087c215000c40c1d07070389020001c0c1328403804103440e8041c5d120400104180a940000d030300303c50070308111000100c81011800102d1741140b000d244070850799182c10b80c10301e4800d000894807205010010b041c0540d01c2e8070b00d020400c0030000105403101d10045003000000402c1d024814003888110240091400320003120409800001c40d0700e0021100c0003540740c1420600401c00c1c4110007000314010100141c0282030030b103414040c000408403541d0151500b840302c0d00c0010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 446813839 1250 446812589 446812621
    0x70311060a060513140105060c0a05030c0c010806030606130518060c0301030c0608011a0d0204050303070b041101030608100504030207030212061e0105030c0103090302210d180302061b04031703 85
    0x4c40d14501d030048215042100125135811a50100c0f407490b0f4940c801a90a4280080450010700c284030125802060000100d941d500d01d0400303a89000c160740c0c4000c10159601c0041d50807542140030044800c803003861603000f06a02040c00e040001c0150403a804103454841c0484024402c400080014003c00082d0100c15005002d00c0c500380c00d980d41064074181294990805c0206414030000c0d0110100392160190341c000c040c020182c9440d01540c0c201109502d004403000c540040112603540b0740d0758044d200b103109032101c0300001d01c5601081e0301158020040607109409521951b0300020050340c1d01070b08040e050280e2805401c203400c105211344010448010101d140703202200052019803000114450703600400d10300420004010705099041051088030303040001c540140d030b07801800800000784492058000304103d5403801d0311031001c2c4880710b036400a0050708048049a00d41d82070042080c0c075441c0380d0050070b207460341d01e07610003541d1008503818424031100801040b5401c0c000c52100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 446815089 1250 446813839 446813869
    0x30b06040f080c09100618030c15031119141605031c0513030804060f050c0912070605072303070c030b15011e0203070f1110091505070311060a0605 65
    0xa00714904005e807000c000340d003250040c03a04109012076061200f0564403002002940c0061034520350b9501d031080809110755442403880440e0404001415044089048620641080b400003c69001c0c0e5401103504403ca43c814054030307070f400e001540c040d803160500082503502c00c000a40e0740320007145c4804401503001c403117080440d14000c01c1000e08854000c28624055040c58500410f58942c03900d85d004011a10411040da80390400300401200d890009083e03010040321210300c504011200c16075078801c0c1c1d00980000820500034100000c20311440382102d40c40400c084207101c5000d130011851900000307010741c2d81403282c40040003440141800c694212030940580960440703070b113001a000849e200c090301c030f034070301c1c004d400701c41d070500c00d200b66079420b40e00201c4800d008800d401c282543c490b255a00d18440e022848001480c14080c4440d030f01251524000e0100038400702100b0b5850b130304002c3e0190140000c0722885001000300707201c0c5610a031040703140042c070b9a0805040c4104121032501d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 446816339 1250 446815089 446815099
    0xd020903190318030c030b07050d050405030406032a0309021507080702270f061203030a05070905120c060a03020d020715050903090a0510200312280c030b06040f080c 73
    0x44c00450045158a4140c0341c04c5040f100f240e84030210121014443e03107280b001d4851912080c0000c212000c030040080b1482c40d6024420615a4503240d240c8000250780b072011004a80602c4001c0c0703010f608910707203041c0024140b0b000000310000841481d440100219a51440080c0030320031443d2000445007648205074081407040380d14031000c0041603014040c821010450000139003140c1d0303081890310708864a4010340307031a41403451005000d0502615100042021100c0204040c00c0240b000203c0200745401000322440d804184038080c1e01c0008058201a000c004014240e03100380000d1110b00d1051402c181400001c3d07031400100d802c080d10712000e50304100310b40042079848806c1074060701d10882e651040b0081400702a1020f080c040190301040c4444154440c803441c0210140c025070b030b00c2d20886401552000c14510b0103840182807045003c203a0b40780b41c2410195503100d44107078440ca04002882110840025829800c654003200841740c6410060003889424440e82c1014901954 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 446817589 1250 446816339 446816387
    0x15012d0609050a06030b0904150b04060b120114090106050c19080a020c01030b0a270c0c060b0d030f05161e031407080702060f160605040221030406050d0209031903 72
    0x100247c800f0031f0280000c1c20b090320134500d480d054440355204142c00c50b402030042000035520304048000d03800c60703c1c0c1d078214140d0b05000003078080b10301d480c21140b0440c01060030103281c0c200503096170f072504540d009026910411000401000c00041000240360180b4115900c804039004000d10701200c1c900d00a04242c14664806001d84030300c104002994000c01e00b10b0120608924a8012607000c0c3e200514028100416401110341141c80c01d040580544414800c01d6088010312081d4099100c004001407266074488503d58800d0003d4001003038113640d030441041e080c4d124000c10f0039200e4080714038045500402030405801c102c11641d8000d41d040300354202103540d02d0b040d56074080c21501900075940018146051441001243d800c10045000740c2092074242c03c14800420301180e0803402009006651074020030780310720445034001002c00851925003407010440d1560021940802103980a0001100903641803040f9008250400002241f56040f07007802001030313082e40b10780650301c1e00c110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 446818839 1250 446817589 446817611
    0xe0f060601030207050309030109030305090f030703080601030f090c03030801060215090304061103130305010b011d03210d050a020c190c05040b1512071115012d0609050a0603 77
    0x2045840c0d101009080060f201c200606100c0e0541c410289202d40c9546002220000c240c0c25034056809899040102c0702040100001c0542d81d114451014000c101d0603400145903602c01c0e00801c0c0780140c1c0000101c0c00a150341c4e10b00003e8985c40e0800c80100300b614005001e00d0354100403012a41600d402a034143c1c2c1008116241c5910403402120200f01c00901d0076202014100100c611265009110004190ba01c5c245107000b070455981443c00610803410f80c194040b2000600e81c6004001005000c0d035680c0c4107001680c10300400c0130084a40010311030069451f00900c903003885041d40c1c640c0507a48010178601503060075001810614080c1c091105030010494800032641992002d9034001408440d000010f2036042c818001100452000030b0724500d042503005205004035010303141c41e00000d0042c500607446402d104900303400c1c155610f004200d5161a0078a0b109001840c01c0383c83da20a0310315150051100700743e00a180400c0ca0b014041200342092138003040141982e01d010400e21801c2c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 446820089 1250 446818839 446818843
    0x2041e05070e010507060c020f070801090501060b03060609130f110c06100806041e06020f0a0f1b06090f0c0608150612060105031e15040501140a0e070e0915040e0f 72
    0x1104000c0c241587d2078035552000e0f40200200b440e0302c0200801c071003900766250703400c50281a81c50000c80d825420024006002e944150540740078a0004042c07508141d0600c1c00c1c42110405c52450030001c2d03071030742a0480c480703400e8402d00740420b80414119503507581c0d0210380e41c41c0803800740c0468462007403007108010519000ca1b070342e42c1090344800e500d54544d0b4a00d100d10440c4c140381c2ca001d44468030004540d40d0100c401402454080da40792604800d40d2090041520510b11035524a2036805000b40782c140000c03603e03448010000d105d010502549009615444004034698022801164100040c06080d2104d88035070303e01064100d035242e1514014103042d0180078005041a4107101c1c02001091401605a1194150029090211250740780c4007080c00000303020f8642e164040c5180200104441c0502c41141424103400b824144409141040b00110080700401c1c02c03040100b0b01c0700140842c1e980040f403502840d400641440551040000c10017102c5040020325041c1d401590040c480d030b100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 446821339 1250 446820089 446820097
    0x9150e0103020916020703171801080402060906070206130801020318060423190506061908030702190b0c0303060f030a050c010f0338090c0d110702041e05070e0105 72
    0x1483d861401c084400d44140e02d85046c41e0402001e455030039940360000d04884000d003131552005208000316007581001544e00d8801a10b001c0d403c41c00c01c12400103141020310080000b6440581803500d00b004842d00000000c201d5000700d401c03179400200380a109144100c0d20000040e4071000f130403003030825a0300d04411142403a40101c04d291036910403000e140c1c4c1440071612104050f840f41b0481ca81d00c0c42d000381c4800d81110668400c042e010b100507584c4880e40703007810940301600019461301d035540d02001705603040c10200030700e103110080011a2500020010304841c941038001503460341410070410001003164102d40b8020350010070a036010400025500711040800c0c200b130300c0c05219602c001c80c09050101ca0074070b9000e5404941501515141c446004032840417061080344409210030444c0100095540c1807480c041803040d44042501036000c04003e08000d090ba41c81d0189503401301e815512540c04001c0140410b0840741029191130080c02c2d4404c91701d2a20121000d005000070b8100ccc00707 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 446822589 1250 446821339 446821351
    0x812070605060f100806030d0c0f060b03011805030d0b040b1008071b050610081515030a020d032705010f030e152503020a08040312090c09150e01030209 67
    0x34030398001c035142d5214440455600140900751080d465400c62016104201c1a41c00c0350007841521121000c40e40b080c119091a103600c80030005046155807125005044060400e5900d5541c801ca104510443c5080c645203483c072843c05075444607003803c00d80c821107584190840c0601d041440881c03655544640d101c4908510b03092180d090b4407006404c45513484042c1c4140c120304040343c45030f8184100066094811107101c07480c0303000b1030f40321fa000e03e0f140e0b04409406003c508a400c0440c0b01c4940ea414691035506001e0100d540d212940d4002400441421105602181c03140f810281c90449000d00200441000c19003070310712503d4035000901000303041043c8800c150359140203d0744402c00f0f0211146a4079810000000f40c10088405807080347c41441400c0d00041000b84851a0340c001d00903695041d80c5a1210034182e900c5440a0f0b941c0b0740500303400e80c0703403079130350501c40b00090658440d400107000c074180d000800b10300391001810321000b076401480c01503201c10300410050780d403514003561160f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 446823839 1250 446822589 446822591
    0x3070e01050705010b0415032f0d1a16080709061d0a150e090702010902090103030c0f0506191505060703112a0405060405090601090c021504060608010608120706 71
    0x4250030f209004000500400e68824104203c14905421000004090780d000340d4030340a4000d082e6603000301020707454000e100c50800c0c2000d110410310b000c0111a8001d030285065200c10084403001c140ca110044581d44411000364000c140315550003039045502104505024400c00d0130120043c006142008079180c0c0c011a02d115044c040e145c0201c60b40051001c41e5000d4407980d05120301038110300d10465560b00803004500042d0704c1a105010740c0e012603401a01d0501d01d0790070760724100c0302107d6208090b0381646000780b4041c000f0b2030411545224900f140c401d404011a02a506025204c003008140b59a00204c1030900c1a41e175101b0454070056031505100410740030784145542407428802c00c940031261002d88403400304860400000f0901030465003040141d81d142d04000458006560350382c40c81d406003005118080341507000c7c4042d01c400d80120303591103680e280d4906840e5000c49040720015240c08040101d52024000c2101410007103024000c0e11640a0421605010f28078001d0421 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 446825089 1250 446823839 446823847
    0x20a120c1a070c06020408030705060721090827090112031e0315080c2422050a2403020a0c060b040f050403030207050c100e0d0c08030406090303090b03070e0105 71
    0xb80c0280c088415140d8080001d6480b10742d02c03c50b1706d4407900280c8050b5002c1c00740c1000a01050f116543c000886044103010f40c0403601502851802048425011103005030b042111000e105e2008245100640b83d14155000101700c000c2400304041069210075116200d82c0359401c0001d8100109040c0c3c1c42c01c82194101072030300c3d50f81c120040d00d041805900c0803c282c00020500c860003062a40c2e14071415a080c8829864030441c0c042c4e00222048480c5401406001c2c807481c0004070800c80d400d48000c2000c10311060303120300002d82026403a81c04801c1307894014111500740140300031035440f42c6506007411402c0c045c0910000d000764401c444014105503807420002a41c3da5180e12041030b03528001010881850a4a4060000d6001c85010b58040c469440701d048030740f4014130f18030804121581e071444e9038401034080c8020104a5001100c0c803452194010980d08000c1000d0401410f081d03440002082c0395003800b170300304009a000094404030400401644036044220015003103000e181503599 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 446826339 1250 446825089 446825101
    0x15020906040501030519110d0e1605090402181608060a030f021002010e01020a030b03160302060d02090301060503010f15150e2209051b031f090f0b07020a120c1a 71
    0x121004100341ca46c089841c00010030001145800039090214500c0c00c10400340d450901e1903969a07201d08904003801c2001d003030034130040c144001e00030340041c03005e0b1100c1e10a0002c0ca0b0445540441107031050385031841c00e00d40c000e80701d80c0814000d4002d00140c3e80c0071681070440c1c86568042034100e0700640a00403615101442c18801d500480c400c04224000715155000361000078041d00c0d00d0001c4600c04e124144242c404060003900340743c02c0342d9000b4216450400c19504200180d000f007072225030b0556a0388000107154034203004034505002c0e00007000801c400d6070740498043c01d4440c1c01c8114200118007012200c1a00403062801c02325044904203200208500001c4003c2d10306400f514900381000c040c54100a070000b10141410030350091104c145002c1e00a06540c0c2d15004184010328000842c0389580150076030011341d00d40d0140503032010081c0e013500c9200301000c05581110043c0e0044900100780810b9603052800309030131780ba1281c456205520303103240c4101d102d030801740190040d03004116 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 446827589 1250 446826339 446826361
    0x18060509010c0c02150f0d0212042102100509010b180a050c07030f1805040c08011502032d041a040905060d02060a1d130905010f1b0305040309170a150209060405010305 74
    0xc2c1c1a1080c066540760740c01012784911b485c041e50101c440c1000070241140902000303001c42c92800c441c0e4000d109840901c40c2d5900508000342010303c9655951150400544a8902c040c0900c04054031044660501c0c001c60002c50b40000c2031074580c14024803083c00000e40c0206030001c150060701e4807011400c2000445a241d40d65988441c0d07005203840240044150411002030403610a25071345039842490180980c6c80f0300c41c07408158072100c2007079210307942c58500c01c41c3c0c41d90035010400f099080ca500e90320041040c2d110021490300e0b40d040803c003000003180e94000c2c2d0350b0080c001c0c0e580800c10109a80406d99038001c160003042801003038884034240350903101a2a4800400a040e680d08503002a2148020002040240c603594200115110415000e020f000b05003040300c0c00a54103000904c1044008040280c01141001140c0000141040200c1150010303140c210000d0a460000d502c0d1081d40f803000c0c1c0080465503030040c009503003240e448a00740c4080b68002e0070081420b5035010300421b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 446828839 1250 446827589 446827597
    0xf0103090812041a070815040e0c19030501050702073803060f061602091b0307080c0f04090c0807080c0f0c10091412040509010b0d18060509010c0c02150f 68
    0xb610b02007a000801011750341c003009042c000c01021440d484141c144c0c0080c442038440030901256240d004142c1e200541c00c04d00c21480340780c11050705003403980f0345a81c2c8075820344409441c10401680315440a01240b0094001c06411710b1000c024080c522016412595080e900d40003c0500e0510100000341c168541c0c4124480c0c40c100100740651354401400700e002200010a402c0c1c1c040d500f0f0340c001032229100a04070000104010715014110794904108440c42600100442c2c802c20090005013200c690b0f0f00068005000701e0b101c0400c19400c82000100740c000c0041800042100c070106103c05150fa1404a8007400da081c0500303555105c1e0203404074500b20600c8117502c000e519280065050148181e030414109000d402501c80001406071800514081c2c1c0c000e55a014105800401c80c0012020061081d490440d00c085030305d0b400b04554444a1050b064244e4002d903c840400400020a00c1200e0f0101010b0520400285180e0003042030804903a2118107038460000b4041c001807100000c4d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 446830089 1250 446828839 446828873
    0x609040219390f021f14120c0a18060906080a02130302130b030601030f0c0b07030e21030d09170412150603080d0906060b120403030c0521060f010309081204 69
    0x12404e107041d20410710b54082e521041c0d50000e0038000e820f0410705201004c0b20403142c1e2802c003a1070252105940456641c0c0b011240c6000d0050708840b101194a403901cac504000c00c816220f4a90103483d00300080d004038001450741451901c100030a0301c92012480020040e03a13010390b002d0750007602c1355035004001c04018184035031502c18100004204402c3c0c0700c4003118144140d0b00c41c65550b588010481d0035010f2001d0040119000e076a011840f03007025042500c0204020380007041104070380340d5003400c40e440500400ca580c6e80342c8040780b0074000d03c00021a0413004050300103181034038101800c9440440d801c8002d00d49000100c003414894803e4201001070764210142550342c54240c00150000e02c40008102d50b820b0510f90000b4170a58010203a40d01080e2410300c0e00c0f15513955035800c0b0010f001d80780c045818044140426282405070244a4014244046042c444d500b0200c08000c50340b190842050f0425050000c000e000944500076a22858200d44c0d00114940700c529200245403007400d80d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 446831339 1250 446830089 446830099
    0xc050115030b0f06010521010504060506130e0c090d110306010602300c16090f0c090909170a02030406090b07031e090302060a270b03070c020609040219390f02 70
    0x5580384c0301f4002520141201e20807107040000076903401c02c0c442140a04020340304045040d000c208030925141080c50f90203004150010300e4441984001040b01c441118256030446490b4050116404d0812016000d40464001400c3c010b030741613040b2100c1340600c3c40d585c0785003440822402c03014490005440c1010700d074406a940c04e11f1540380c3d01d0f07405051403050760601401c20448815030380b50b911030062040d0503980d908111031b0901c2d00311340c0134088102c011140c642c440789001a200007003d01500b419100c50f8003850b611703841d000b40281890803a8010740c0060740c0811640002a41183c1c0c000f00c0030802a000352204c8681a00c152082c500c550700c041e401000000d900340d600c17a48603821708104074800a0800c9095281d0781c0381010110140200c8410805c100003003803056010315001d01000c3d100a0109280c5140c080104041c0c0c1c02c030071140601c41800107690035180e608106101105124820740c0c030b682d222042044034481c1c1d80307410745102c0061040170100078858400903a074207042d0043c5c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 446832589 1250 446831339 446831377
    0xb180303012c07020604050d0503072025150905090403180b070303091e0c0b0904060b040b030a061a0711010c0812010e150901052803030c050115030b0f060105 70
    0xf0000e5258041183c04990b140960480380340341c54003401c15207018030816a100b01c88030070003900e101220707600340001011911403c103500040d1095008060442c1c084c3c0c030000d40d152845e10820620141c1204800c9060007403a03c0700348440d895080c8642c2c0d0044d09850900c00c1c0c02000c000d1400044042d03040703007110340400500c0000703154250f00500581c5104002081c001c02c40051102d140c00c1220900502040404408009600d0300d80c024040054004200140e000d030390304450440b0394081d500ca4142e1100210070091800e903944600300040c148100e0070b15814031403202c0c2415600c58410001c0000d06818041c01d440e902c1584010411944010180c2e900d0721485a2a1000c82003407091584203040b2a000a100442554041400a40240243c880c0f642040300300b00f42d00400c031028180c8441210080c00902c41a03e40c44002103000351a075004402c440c0c117006081d40d10345100c031108251001c0007000050388103410076034012140c00c0c0045030f680315000101e034540b1420b6a400d6404039450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 446833839 1250 446832589 446832601
    0x60e06090d0e090609041502040503070303030e060105010c0201080f09010f1107020f1005040b030c091009090606080f010302060903011b03150e04110108070e06070c030b180303012c 80
    0x74861050221502c800c0d040300100b41c2003000e80c1d041243e600f80c1114502002c50009020628041c035600b2000001600305a183d030b0102c1c2ca00000eaa005400090311805e80b04c4405c2001c0c00407501400c0c080c60544040d200a03000a0003007540a0241d4504001d40781c00036600c5c0e2001c0d8020200e0341e141190030b0240203810b624a0043d80c01c4503005900c02d101e40401c2c2050f51400d006200d2042e000364407140e04081c54005242401e4000401c000104842040421f486940c1d80071070302c5080c0b01e10785034441ca07241000c0c0c4403021035890f80c005000303012200052290705001d01c01280d04490f81244d07500c0d03482c91508046409058903010404000000047c4101243c0d0503030084007002003114032010710141d440040d09052001620003030420b00c04140722001d5540300f82a070542c4811743d401c04000240500010a889034403883c0700f0f540d200001c503814000c21128007003254001c407002001075620910043c00035241d01c0107100306004c500c8071082d410754010764000c451801c2c8030700e084904410314000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 446835089 1250 446833839 446833843
    0x10303030e0c0307061d0a08030a1110061404020a02190809130b060d0b0d051b0a08010902031c1103030903030f07050705070612060e1f120803060607060e0609 70
    0x6201520224001c2d10303100161030400160100071540c8540e200d520f084204c041c100541958040c0c420b400001581d4042402903081004040001e0242e881214034030301c80b003801d814095110b003290a4181050750410105280c24a54008941e003101e006030b40f9000d60380164038010700c0d6255400b61140e4a0400000e100a100103841ca09000b501c0101c00a04100d015404607098006115880102800f6600e51040203030300c00765845101902d0390800d2652078aa661805200c0281010a0540c0441c002410b0030402580380050410720000c0c403409070f80e13a00003034450541240c0c14000303000251780302032098072601d81200c1d4209641c082e41d54030b0030301110301600d036401203481200c01005040451401b1f0310440858420325001005444a1401c04c1e0301142c002c80c0303c107900c008050310350201007800b10010b840c550140d802c5a49800d0001170030a2040041c060540c003810448045c007116a0101e030282044075072048088840c2c5030798081510304200185021032040da42d07449032000704000c000340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 446836339 1250 446835089 446835101
    0x807060f0b131b020a080706020306030a0203150702010b0f0d1709040c1805270910021603080105150906030405030d061d060d03091e05150901140c191a01030303 71
    0x8880118650401a19401c0c2e03501c0f105204028080034081047e0710100740e0b103902468001c203008044d180f0148550300003030b107040c02d849441a07004800009001005409200b01c1da02c5060540d4004107903a41000045d11601020740c014121210305c604104080082e101103644a01005008100300c010805006018810500d81c111058030040404661f515206d419408581440001c5072400d410409a240e0341c3c40c4054200c0c202ca00c80c0e6022814010818006071031800c1940e1420704940001d07081c000c12540041c2c2c0003500411200000000340c010b00c4080300c4400d00c055501642e00d44681ca80f4926502c980c0c202000d405203010ba011500b80088288145186200046500b443d1900020417075507442000c401004109401c0080010055080545041300e225824014100780d8600218195144e5400013840403140021003403201c0da04a0100d5070f000703400c440c1080c1024100d9079404e60fa80703600d00d60350781081040956081000030000c0b21803180d410b003d1980c440355039640382c05805000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 446837589 1250 446836339 446836361
    0x8040b0a0605150403060b040522060b0901091a09101208090306070e130b090403030b1212040914150d0c0b0c01050106031103040b07051b06150f0901030807060f0b13 73
    0x807d00f003c6400a00c0c00d400f0740350164058480460300603080c010120030186289008840355034460039071610640e24041442d00030300600350013040b54a401900d00940c20402d10205100c0c105d000244041c0c02800304c981030644c0c80203204100100d41a041103c10ba024901d00b4035414032405003004403c540c4003001f60b101c11025114498003400f074150324020b68141181e4550003044040c002000f0078400e421aa003010700140c00e08581304441d184041c245103c203013540342044400201004103265601c50481c0408400d5035600711800c02e51441d841d0700d1380c80c0d20001d1056808828030800e008014804900505140ca100c56a5030702e0254010301070038003440b660010914001c000040e00c40b858003100c1c411980400c03c1815542c603c071094420ba08490343d1035a2424400d42c01e408000e008103e503602070400100b1800e4810f020204109921005000c01800780b80c21000400015280109544105a11800101b41c080c5c03080544d40040ca80e0301400c42d072003200003002913104030080d44042940b1b2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 446838839 1250 446837589 446837591
    0x1407060e070b072112020c06070206010b0702061c02130f050109090203090c0d031b050705040b0a05090c0306030123040b28090f0209010f140a0608040b0a060515040306 74
    0x5070307601c40a188501550b400640503212414000c48000b4030110b28299134291424100ca00b40301e51400b000480e0800c016820103503000505101c440c5804008250042c40031301003003890082d0941c0428607500451080161844060050034650ba0841c0c041d1081c01e0700c814551880c10350740b10003010010751144503440c0884d03072421021407018814022248a8529603008201d04003021061103000f04403c1403d07003c0000a041c08030038096801605060b40d801071000300b40c03007030811003084100c81e070f0701a9441c0f00d035400e07902c2007101d5203030741c0081a840f5503440c0f502622540c1e41d5000c2030241c0a04036003040c4540301030455400d803a10301c1d591180220701403500c600da41e640303801d25208803901d982d1310068140040d0044090b1105180c003c038503554424407000006000681c081140210300b80c100076003000120704248021101a417603040300407411104280844d00d4140040e0418001910282c428010040051a81c0401d604034800030300e0702030415150030101020909094105000482e501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 446840089 1250 446838839 446838853
    0x402030f070e270405120a050406030f021201050607140109030f0201140f1803130609081207021e120703030206070905040506130e120307231c020a1407060e 69
    0x10381030036501504641000c5201814010034007108040c840300043c400c0b1298801c40d0f06c5000c1d00758120010300401e945130303150940c90b00d0400d040601501e0280c1d4004e400340c3d10500c190002c800e02c2030300c00c1c0c3c1111000e492295540400d400c0c4107801c180000c0c1d02d40e00d1982007800003000c05a1003c076922070314140340e008004c121190400400901016a02c0f000032207001c80200300142e078100c0c4500c81600e01901228941001c40c80011540c410540c0544040b8030850303400c000044060283c2e5419940481d00d107442c1c04019400113240b1132920780401e00700c0c1101580d03030f412912414404500e82c5500c2c02203900403903491400959542c0d003160400b0015100110024840c01c1c68024180245401400c204004600c0c8015a000f000c81100942640c440c0706080b6003000f562800842c01100300d5900d0603010441c5d01058080c0290b241c10032002d0704410080c1040c1c42d84204ca12110b06050360038092380e1aa03000780c040314010a1100700c030005100008114040203070f50303030201901204200c05c0e03443c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 446841339 1250 446840089 446840117
    0x40f0f050f030c04330509092107030908031303020406080c03120d18030c031e0c140c03030406120507031b1107120609061103160e030109020402030f07 67
    0x3084600c104669019031010a240115181c10b4105d1602c11010329101601c5003c4808404200b500d10381c21603046544c00300c1c003840541041804694410070300401030102c1039824800300142d0111194000320442d000c02c80d5030425200c0c12070b01d4020b0442d00c048a494825041082d844004a848100d00c281e1510000141414000c19805010700700200903000001c00ca000340182a4014460314803c0303542e810000c042400250b10390b9000701c0c026070700c40e00b1420551030302620880b2180f00c4880b02c0840c0004000304030f80d1100c00100c00315400102d04c201c15884244803450b040d03500700341940c140808070f40412903d910644082410000c80800d00140c0c031403020075000c0312000e40803041450606402200c22900822180903c42c00c0c03801160038482c0d03601154540355080300c00c101c91440d1a01000e10500c44030b4080c46c0002d0184089017443c0d81001400c0b24100f400c030080000500c0390000f02821075550a6001603009a00900150b41c0d0b450107010205611008851034008250040d5081d11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 446842589 1250 446841339 446841349
    0x90105060f01030e0c06160605091e1603030f1815140a0e270c1902161205011103150102070902040e060f030c040f0f0c320d02040f0f05 60
    0x140c58100d02c4041c0a0700d485c0032080c405640d1214500d0012480340201100c0060740da4843c070352140d24a83d02402d58840c28451001740c0310702c0d4100c0e00303180740e120409580030b000302c014070b8508890781420800c08501501e8419101215031000d0500c0301019418001089011011094178607226556101107203012000342c004140260000c03040080d2500d01c0e181d2660501c101c170700c001c2c1900301c0149503500d40c3c00a20001c1401c0f0480c3d4a0303514a42c046030101c4c04501d860600c4d2000003850028052607071601c21003c5a00405122f42c01603100c65804440920401703501c50f40101103905101540c03071401d502403250700204241d0090040c400c200c0c4c00240072085200780d60036103105000d000c20030313110b0008100c800000e19581550501545203181d40607542d511481e05054550300e80421010241007440044603a0b056034907040c41070b04004030031440c007804900c0d250107610281008110f8481c0d43d5145950103254504d03002c0b04c0c800034020501400c40c2c607550049980852644a14a071618184a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 446843839 1250 446842589 446842601
    0x14010f081515040b1c0f061803080708070521330607141e0f010905190615030b040b070504030210030b01180e040c09110a2303090105060f0103 63
    0x14101c04a1400200e01d00d1400d508002e9100c0e00c0200840c0b000819018800311904044a01b00c800c460000d09070f10410800c0d000e403a0701e140401c03101e000c0b4800c0b2501c002d481d00100400c9101005006800a400a40901c06072102c1540b5541681510303550030403003000c0039070281c5020035020b442200720040180048941d00c10f0006010345902d603100349205000f00c0b50403200080b940c0109036064004100d07c10040700b0304000c44050749102c001c01142e4070505020410300000910b03410800c0c40c40100780c3c0054031100c0c01441091140071a20542801360040610603d8580d8103240d940c0000300340000f80b140140201d00134408011a5114502d0a032464880c6100087d009401e01a01c0162030380254810ba81034035060529900d00303132255507804680c01c11074004a2902e072129081c00184000d85024601a050786a4104801c0c0000a0a00c04501034000b400c410058004020b004800c60035013100820390a03124100d880e03040550520f8084c00040b1350050048100841002043d07200780104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 446845089 1250 446843839 446843851
    0x15030b0604053402010908030712060503010b030d080901140f040b0106170402060706060f080703060e0303060607080c03040b070b060102010b0306040201080a0c0201020f0d020406020d05040302030c0405060414010f0815 96
    0x4140142143d0384400800c2120042d100540d5038510203040402c149030300543c0310b021103035510300e4051411150b40003224065048035000360314000150455480c00248421a00c1e628200040141e50300c42c0c0060140801a807400051044841800701c140c0300001c0700340c02284140046d10242e030b2540c00c11680040c40075480c2d072800c107181c404a070242c00c5c0300b00108602401400081070b800e441c5c4e0f958143c511129400303285541e000c0b88042081c0446446065840815800510b1950500c000010315601642d400a4588480000c00e04800300302007033114001c2441c003105640710409800c0c090030000044071242d02650820510b25102d00c0d000c81c41c04d109981c140c4841440b501c1d0a401800102001180c2e10190b640c200103001d040112640a02800100c4503005a65a030a1a10007400c3c080e00607149410b001e0300344000c0c401640d02103a15441e0b410306841c0019907a54800c005000381c090500005500260007002280f4035000d03c0a00c030907155114129590710a103904032a40c10f501c100c900c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 446846339 1250 446845089 446845141
    0x3020109290d09240609060503060c09010c06140a060905070f05090109050a0308071713090f0609021b0d0518040504052b0306050402040b0d0f15030b060405 69
    0x400c0c19a48800007400b940141e0300c2c40001d0320360066035000350303440d0103101d00700030848034031314840c0380169a014650180c003019200740081031508010039035500000d0140155400702260040042e40b10380341c00e85a8076001802480145490903203030140c18400c3d00d035590b5080c2001804615410300740074290240500741d072491301803c200380701110303d6004402c0160403c104c413400080c166440d0200031018500481105a40d10440e1605245070026002d615a0082c805d202240c40d0700d00c900080740c1150034880001c80d403000c800b9079100042c400c0341c1002e1680c43c07000c03d040c0c400d407565980c0303481c1c00c1c991202101d442d4002c142c2e041e9660702800c10701c00c800841c0c21542c0c00203814250030035504203100e1002c41e411003d1044e40805807140fa00540500d0440c0700c25021f036065414007422004000c01c0d2070440c41d0908055211030240b1502c0c154800540c2c071a004004045250ba004c144138800314501e4030206901c0303203002c00004c00c0584031207204a041001298039401488a181000321207805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 446847589 1250 446846339 446846399
    0x605010203070f050f0a0503031006020604030804080c10240b04050d020f060f190305010b040e070315210317090304031410090b010e090a030e0105091207090603020109 74
    0x150301e43c1c074a580600129024003800e024010801400c01000c5c08407445800a035481e46020a95107000c582c16620000455020340180004a0341261003241c00c1a004a52291740f015254140e51400c83c254100c00e41291030201c501d030800420601e050065601401d545054640e10501e04445001c1d90080381c0e40a1030510400c00140f8011210684601d03000e404182060300365015207138950852540301000d98000704500c40c040c0d40c14032a07a0301401c500301b4414102410240c103070f9962500180000d0525542d48142003040c10041d54040082000b05c1036035030000c2c100b0895231007050448204a0105120503a20f1850302100150144194504002182031510b141c0317035410000a010350702c1685000e14110250b0102c0700d030040300038050080800403503e5240404500712100002c0405030a90800400c1c1d43c0002d80c4038107a2600400240f07016510b82e0321a50010340f9480320503644409078800c1c00c0000660780c44940100b405c490003601c905004c10342d01c604254100f200300d000d0a2640a00e03075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 446848839 1250 446847589 446847593
    0x2040f05070503160201140103062003010b03040f210914010801080a02010e011704050a12020102090306160509130c0809072103050909070903050c040b010903140a0b0c03061003060501020307 84
    0x205081c0003d0384c1d988004181081c0581d003c03144168280c006403442500c030364110305000d142e148000c4c4502008a0001d15543c5004440020f40c08003070002418032515030722540920041c070300403a0505490a800c1103401d0190791010f418203a9a208064010601c8a080d1140358000c4419504907945603001d0f001c03002503030340111100c1045a05007418071040010140c9548010400d940c4500d200344003c2901d01141e06041c50700100412012045a0040000343c0144e00c003c1a080d0b0440c1c43e182074240c4c030f00341c456001e42d01409203000c026002035040c04180c0c04400285c11188089040d9200c50500d0f8507104210364903001d5501401c55411040400304d40900b080e2041d070700b042402840d11500340140302d030003c0d4189005446d140b002070318409091051000604c010750101d0f0b011241007000400010010703021030702c180300103040880c408030700e0b2800140510800000aa102141440b181303480d00070103403d07410903607946003c3c03441c0c2d61140014601a200b10b80664005800442c1085015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 446850089 1250 446848839 446848861
    0x201050d150e09030a0206060904030e040f061a07170c03030f0a0f11090117090d0c0203150103051e010606080f0a06030210020d11030306090c07060207170702040f05070503 76
    0x5000844074544003060002001c0b038880d00040d001d89104806507a5814001070024503081020f42024822840345080c00002600040350000c0380030305440100e486c203003420901c4028641d0341d00c440505078481c00e062004001400050100d244a1250002413504443c0d8100c0c05020314045041c56500800c0480c0d0380c081d1403070000717034000c8801c1c8010400248440c0324800759000080004c00340c0310040b030413070710541e0090202441742d141259505000d140a0440301e945d20b0a240314501400078031090314040d52424070001c02c040c45409020210b40d6940e1802c0e69840003c1520320a04099041622181034018082d1004a901c2c80e9140d900c0313601d07010b110110034200500001202a40c1b01d000200580358110f501300c1203495500500b074003014681010b00341141c985402d5840e60810400c010f10b82d0b4450b01099002410b6071001030b01d400451510600030f0bc2110005040f850569a896180020000061600e188203550900c03501c181c01c0703840e0080c3c860584420f40170400500c0050192141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 446851339 1250 446850089 446850101
    0x60e0109030c1b1806090e0604020f060703030b041a011d0d0b060105090904030504140f100c080c0703151b08041217010b04060f0c0507140d1e12020a0201050d 70
    0x480d0310650340c80d5120004401c0c0580d030761351001a203442c0d45003000141414858805000502d0018182074941640010b0002e001040254442d44c0007007007040900d44294003944520300c1c003510400814202d62003640485602440190020344a82c0641e000c1f41000200c01c0c402a60181c02807041811a0740c614070784c9000240007504000c02070041104690f42e404180340194025180d42c1e5503941012104400780001503941c1d40103d503100c1c4010210303200c50981d22080041d61603d203806011030702d0119090321400030b48030520702c50007101200340252a140c1080c020820300d8200050a10368510400110600484001090003040003c0114403502c2c6a441c405042c0d107000644600906401925210283c00c40121244045024040181c05c03e40100340c0844a06014000a85581d00c0d1170f6152154051040749841102c003524083e01c81035041000590711450095410050341448505011032810681d15140c082046503e100c3c00404d8507442c468041c3e50311031401d02c08407174050107000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 446852589 1250 446851339 446851373
    0x603060c02210d091a0411010207050114030c07050703110906040504051c12060603091727030109080309030306041d07030222091b091103010312031116060e0109030c 73
    0x41c0711081381001605907015420740c0300018125111508140c200354010365180400c246c15540030840c00e1040344e801c00c02884640d42c0800d00150f59642c0e0310200181b0f80283e030340003446803081d410040100300c015510064010b5080d211640c00340e60b070804100c140d60b800e840181c090703081243c00040603010548030f00b80c901094200804101103c4050344102e40507944014001380d81c0c0c1d81d10a08004456042c840c0c68030008100c0350a0104d108204505680364000d148000d035074401c4500741702d44003908503802c1690070042e2107440e803070201c89c45912a030040320898803a600d000490307440411036258018003902d10344000e020751411603080c00490f10301015120b425920400f02000011032502852100340d20400c10340e141000540590070440e29907400c0088000c0c10007180407100240c4a00b0340c0e0450b84c100488a40c0484a0075060b0010103001c200e0703a1076424002030b0803440304000035040b008984120300405c4409156403001c1c1c220366450b28000d0000320300c24080300204103003000e8440b000c2e07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 446853839 1250 446852589 446852591
    0x12020d08012d0308031609050d02030304170f030a1706030a110f060702060424050a0c0b04030c0c06030204050312120f0402030f030325020c03150c04050904060603060c02210d 77
    0x160f2251140308103034000316940c0c40c4520111300c400300150b03803207014800101425a6100240511540043e4917409103001d940780d211411080308181a0040008803e1455142d0907640d5034840142c0c01444139070301e003000c40d400b4040361011500350305002492005054102040c01304540480f420030800d07a1503040c44a601c00010f02007803000d80c2d00c0c2002071008011900309509500184405407070a00715900c100303c18418180112402c0700e400854040c0c0c601e52041001c40c459403070b4503042d200c000e07180d180644a1000c403000860466010f44c018000d1380c0e0304408503990404441c40060981c4a82e01054810303001002c0421a003040e800074031500984020f0940d10003540060706c16145800c1190162941500e202d240c2c0352075004000c600d1401001407000c0c0440302c00e1400440d98941d1040740102e412203100340000c01e100d48480a8a020701002000380d803031801e243c200745008d00341d107002c10b851540c0340c090b88060843c00020042c40920746400004401c1585096001a0380c000c0c0041c0a103031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 446855089 1250 446853839 446853929
    0x3050f0712110f22170703060903120f051f0614070305040509090304050a050f0d020f1c140106090203160e010c0f0803040b010b040b12040f0c0312020d0801 69
    0x14810f4900640074160a9546044140340241d46144903d4a01e07031000e031744408885424054600003180790025250020000b042d11003039071404650181e15000f20a070820318082e201e5222a860390006809801c484596610b480300e044088110040d40307106e80004036a8400c0f408201c0340c20b081c040c00c1c445000e03040c200e00341543e8202040c403801c8121540000c940001a0070b018030f00d00110a407001e40405e690340806045400080703507021628042c064410b100386400b05180d6922480305040442c491f0000022481f41498511107044041102181c03550078100003203988001031080d0380c803401e041208900001c1c05110b050742d5103440a60001c0c1002406800700001c518840d00c503000817803103846ca460b6640390a0030204120001a007000c00c0b0040c00700002c0040310700300000d4480400104508440d00d44652a060742c10400c83c5000a00c02d4603100320010a0281260890b004049503409441d000310501c44100da5840c003d00405003401c40181030f850800116020881c16094040648054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 446856339 1250 446855089 446855107
    0x30c100b06042d0611010c03090b0a1a03010c1715030d11010204030c1413060e01140a0905070522030c17151812040b030c0325030c03050f071211 64
    0x300f08840d400000c0880c81c00d10300100304c10400d1080c074a0700c80c8245020020f140142c0d8a40080000140098680940700d0001c0c40c0500c5201c018001d02001c010001c01811040e62805000e11110409144a940d12800040c0600e1481c0700d580d0300382c0d0b400070b0142910300c00c0510169255520306411407155036092002000091030b00c034014020f0484c8410301415240c00e20f0402ca211410134143d96001800d001040121100c0c50340524152450000003620118140c0c02103800c242188e84022442400c000c1030114280d0484018034648100c06441030505034a658050701600b11071000408091950320104400c0244900b88244454684260b4004082a8102e191049002d49154002c000f21812001d0804000c0080b044001401c6c40c42078201072911034041006d0000900340020020700000082012020f548000e000d10300385410a015401c1c500c0005008082120300080400c0ca020081444844645d84a91151103103a541a451025000d600301c064011035007110110882400f205c12 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 446857589 1250 446856339 446856419
    0x2060304140d031b030207030e1212040f2c04060c0c051506011812020d050109020901090e0601060914040b01030b0604030b09060a020a02030f0a0207090509030c100b0604 75
    0x1000c502d665008510b040f40c1c5421200803503c4501110181407040000c0360010341c01446951824000b06c0b00618100040404541800040c0c0c2d45001c6a800c009004144d2035901c40c3c10b42c098510f5810000740e0440d2400c1081c1748001e0112040d031510299800003800100141c0084100e01150f1409414881640d0396a52030b01c1042c01081c10030f41c0740c2d0820000d40356481070701d400000009142580ea81440e2200c000d44d0304001100c0a8001d5003c00c2204082c45025008580541d80c0981151700b02d60b980c501c1e01004003488003006105000d00070001909034811200c1038140d440a5803c20040154502084000c141003031400f810705071120f00344400c035903d0f10040e01c002d502801c840d083c5841d10162113030500d00000c0a13494030321b00c144520f140c0305070f0001c00d4409105c0b01c4c16040381e031040140e4040e803a25090b0791100780500e041604006000c200440501040301e183e00c121602a0314000c0a0341c01da030250503c4980003503040c4820400010b40e1949010600c080c2d0000692040e9545c4000d8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 446858839 1250 446857589 446857603
    0x17030402060702100e040b0f21070806070c030e04020f0d0902151b010612052104080709060302041b080606090609090c0a110703021014090d0b06030706110a0206030414 74
    0xc00300d10504045d0714142440d000b0700048002c11103080d401c3c1c1290b28006418010513101e400342480455145980c100020030000c409800c8000440d0348503c2c08140c01001c0c1e81c80f2100440c000b9040c8440921182000d000307076450405d28003421418184240d10300070043c0340e41d11085c0c1e41b00042020f6800c810740300200900d070142d050782407040c1a0703d41001403425a1041e51003040224008280301d0b000c9800030a06000a004140d100f00384440c0302e04c5544c04a000d1908400a24001e1a10010b00d0b82000e40c0304004491017036600f8084410003c0300c4e8080521001d1201d030200b809400092014074080b8000c06103079100900da9400c1514190103d07000c0715045070f443c0c0103281c0001e03a080840d60070031081d40d6540c00b040020b00f40107080d42d02199000c10740007001014042d48103140701c10301001806864007190064151840040c1b02d00700a96030900946e20309000713020745800450480d2007008100c42c02c980c540c0041556410715424002d03913030710080c41594061040200d40d00c0605003807100c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 446860089 1250 446858839 446858869
    0x1306050c0c04141806090604081309060b070606090c0206160306091d1207080901030c090b03160305010909170a051b060106080a02030601020d0e0307081218010c17030402060702 78
    0x1071461404602030074502e9000000130705503511203030811a01c1d100024540d944182d01c40c3c000c5850f0b24a5500050000c000d540200b400d160501e640481c40c4881400941541d9005107400d1010694603540d05080f20041c000c5c41c00142c10072400607003180581c2a1051540c5482c3c5000124a035071150020101e40c80ca480c4030402c03c50720400441256406c0140c22250090740701054074018099862010f03034481d85c00700c1410b05807201c2c0944d20090041409a00a1541c440c903d5500c1c602140d03c01c00c40c104544c410800f107841d20001003809049440380590707035039000000360481c00031682d410035541c00481c000010013a00b00101200c507025100b8015036000c0340300007414654100f4001902030b031802801c00d000b40d4410b000f003205aa0b400101c034034030350096007080b618810341c0c9030100e420a030160300025040e10815001e200320007441d40061558513034400c281c0f042540d500c001101c400d40a00c1004d051030010340c05004c216100d602c000c0d070300144001d100c11b1800c003896020038002d41c0e205900d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 446861339 1250 446860089 446860121
    0xd2a08010b0f0604060c1704030c03230705030307080d06150906080105041103040b1e070c031b03020604030503220b04020301050612031e090607050601080f031306050c0c04 76
    0x201c04207401c2c05410740c0ca0080c000c0314072505081c03c015000b0300955001c00040c1c20254000901c06d80c03050800211005160031512041080c2d4031390401e002c002c0c401200c0d1850b5a00e5800100e00302e0000828100c0503075000901075440c3c1425600d6214507900080151500680e0310880040c00700160302400c11038902c19110085c2e4580b6000e001360000340164407150089040071000c2e03c002c8407103004c49038015880008981c01d6182c2071650300448104146084001c1c43c11400d21034001d401ca408047d03400c0c42035441d1880e17140002c40303068501c16031401c0100503910440105000030b00900c003566000a00201441042e0003d200c2407012025092055641d00541e0090106504080c05019032045043e200c0f003010030900c600740d50740ca100d41c405513080c000e0000045403c0b00c404004a07401564000c140d1900c0d22a603080003500c8103020f02c6121201d11920b2420010801d0100c160b9491080e80501507002070728003035041d640c80d8070028007110640500c030030143c0a030380e40c0d01c0350088104003000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 446862589 1250 446861339 446861351
    0xc0a0b040308090f070501030c230c072909010c0f0b04030305070c022407061d01061e030609080d0f0e0609031e25060e06150d2a0801 59
    0x10090080e5002615100b12074102d00c1c044c6000c1d110000d449011110300f0300c0e0018415290000403909046003085121140d04028110740300c841100010704a041c102c0410b07507101a0355410300f84085900d2485800d017126965081081c810407030005010081e03810704090781c182a1555405900803d04041156059040020301060552500c1100e601911504041c81e000314190009628046409660f00d583c2c0c02840892402030074103415908081da015001748022000314031414290b100c21040c1c00c6896103480000514000f8104c0c00003011a20711104450480c1941c42d128050001c545049c3c90300001080344d691032007030620074013000442050002400d03801050400d414160080c1c140b0301c143d841441481c1c8000000e043d004280018038808070b5450140050160000140307102c2030306560f8a100c5885c041c81203d0708001000000311041c3c0d031aa03a503038111a42d0a80119412540142110f20010000740d412682612582c40142480c04044648442601840a21b030000c10080c0d443d86 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 446863839 1250 446862589 446862593
    0x30604110309062418070932090c030f0709030b0702030c0c0108011a0309010e0a05060a05070c12030906090506130c0806010b030718030602120f1e15060c0a0b04 71
    0x502c02054001030403000d03804e403004100080e081e00007460744400e04c00450400b18880500513140700c0300400c04850200d4108410320a404240007100700c00c10f00c00301c0d0940b00c217441c0389004040c0a10402c01c00c206541152944540380080c060024509018032101840100225420a2030300c2e1203104264000c1d5660314458401900b03002d009400141400261001801032207455049060055542c01c203658499179021020380c09002d121041295502803448003106211010614621500240310203004035110f0140c100c1c1e4001d4040b502820359111041502401031081c0c0105914601900002c04d079900300d43c0711755007881d106950f00104440c81441d00350822000e980c2c40b6005140e00000390415600d00780992410780b100410700b100300202840964400080b602c44480915046401152180b040c032503108401030095805018203000b01c0c0c0052a001d64070003280d6142d45500141d0615511150120b413500c200410f0181e520440034002540021820807018491790f0090110402c10306040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 446865089 1250 446863839 446863861
    0xf080c040908090d0f020a0f240507020405091e0616110a11130504080310170c01210509070510080f0105010509040915061e030f0803060411030906 65
    0x1018000d0045040400c1040864000010750f20000c000341c45079a407401042c40c1c10519200b0103400254403003904500498484581041002614041c030150300304040f00c0d00d01c0001c2c1c014203007403403400140304000040c0141001e401c1903410415080840303074614040c10240342800c0d01400c90030a20340c04402000703003001d8184001c8120503002c0c2055014140d2542000e03403100784600010b4100e244046128a86454000400951040a01c0704001e070381018500041d0ba507005a0b04407680008041c00455110141c099132240175500c440203280e82000c0900651315403c8146400342e80c10389a440c00c1c06524103030b000700b9100380c0020019040160809040240c8131910614000801c0300e41010010280c0c5401da6075030644009090154039038070140001070182031103070801428800c4805003ca0406107903007006044c0c4000daa1100c115081900200c0c203011881c3c070020f000301e034207001c505011540d90070041d600803030041c10218851010f03010062140d4016a40d8100c1079100104004404040d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 446866339 1250 446865089 446865103
    0x302131b170a1401170f0f0a02010206060109230102030c2b031401030605040204110c0c03070b0307020c010c0f0602030123030601031a0711010e10051005010206011a0f040f08 77
    0x102c0400c0075040d40c4000780b00982c0d05000351845402c0d50b5075031034a000b404002d80590401c80100702d44200840312001911502c84038004ca0240c4038200c00f00d865917002d18900340680b03d0802c04a030410700c0c1101040342404a0303160080c10b600040081d01401d600c2808241d100024a0050981c03503022400001a01038040b40f000080601d4409100c240d9054410810f044035005880450702c2d0310fa0380001001000719404402c95400c000891890506020401c49115030f02101960581d554441d038400151000311411001a005035055005640c05081401d0940c3d0281d1803004008a041c2d490700201c2e4402e800001d044078002c6a41d01c0d031303d024000306030b00105040e405040d255140d9030b510704220520310140d46000d0260400680f0541c4180480e4104500200c020301181c506020b015032900102c8400141345811720000a6036030b100c141c141c034116841a401404103a2134480c078042c55000b81460495400c10400c002d40881003203401800c0600308400d201c40540d45011380852800316 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 446867589 1250 446866339 446866351
    0x120d051c050108031c0204120c090515030712230313080c01120506120703030509030d030203090601120507081b0f030a02090601210906050a0b03160302131b17 70
    0x41818018006030f0b1002c070950780103020024114140b80c5090074510080e0190707030416540d0702c440802070414041da801c0c002041b14041c400c100220b4560442c1c0c1050030035000d40454140d40081c2040054a40610440401c54050401100c6070b004003601503080b0141c541140d80c07958008280598411510f00d400e10050808000400001e0800300000e010100101d80400c0aa5078030000100c3e16125600d40503807a847d07140655840b41d4491401900d00e4100410190091140c0b00580791101d01901c201c034081e072544030040c035450380ba141e0740c000d00b40c40500e0100c40c180100e02d0001000b401c10804554000f0038084044090390340c074400c0c080690400000c0300e100740d11640034500541c99184415030020f401f840c008620440440d0221048080c16003924802c0c1d1401024106119650380314500500d142e030020b000440c0f1450402d07544907c3e44104101486814500300014a4584442404054151004142801c2d0085141c003c050303080000c002182e01311501c80601c100ca4904503a00c1a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 446868839 1250 446867589 446867591
    0x90102060f040f06270b100518060904110316080c01080705180a15020709050609010f0627260f1b040e0105100f060e0d0602030402120d051c 62
    0x218160300d0300d03800c54440b450041c1400e035403254200c1e018190742e44011821291546000d40d00b006501e011400d1000172100905601007520707000c212450709a000740d2707090b4034508420029480d00fa0402082080c06041122092005510020380c0e440510001e05030800c0440a0389600d8688401030f0300302031101d201c65040102c0322040000584d0405c0c180d400c0006607a41030b8524050210209842000a400c41c91403040c2160707441d0f00c4168001140000e40d41808014411503c4840510111000c00c2c060300a002d95141d1040c02000c3c8624400f0b02d04150040c468135010800c10b00080c509440c0f90888c1d01401076140020201c28402c0b940e050030120100003c09070444850041034480705811032101d101c0c20144803802c595902c50304140031203030890000304200d0808980211581c00d46124101000070280303400030720f445c0142c400b50240c2c00090150020303d41507503146c100a40c0000d000f00d134885805150040070000400c08140011041d407241e40e91100d40410303411b8107236110306980a1007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 446870089 1250 446868839 446868841
    0x905010506071e0f02031f060519060f090306020708071b030b010501050c01020f0d0e150702061503011b020607031808070212150c0a080106020303061e01120e03090102060f 76
    0x9102d50781e083c0e4070182c514050000310001d038502a044904070ba18081d600d0700c00d80c0d5400981000c1e410024041409002d07040109076500c0c024410701d480c40380100405c0d40d8200d4400c00c07665018059446000800d494042e140903226992501213820060058808610104840040002110701d08031170319174006a2400c00c2c1d00c1d42e82d40d0254844140505d9041040c04140c015003036500750151890034a10b8000780340c0f04d015007072541c00246141003840003644603040c103035410043c61903540342c000c4400364040c0405994084005681028035841380c0e42540d60b0b01d00400722005e4020300e1095180c0d0641c0600f080d42800f100080a54000d00d20160146119204e8503001441800443d2152541a01c88140d1201d104108030309000601d00e070100420165000c0090310030f5004028070881040c0e4031410074598076144220f03501d00003294511340155182c41805200325041c806c00042e2503051404040e800c00782070022042e501d0800441d001c0340d01c0403c6100e05582c0511940d80d0180f00c04c03844140c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 446871339 1250 446870089 446870093
    0x9010801051801051302070807050c03120310050f0a03060f0b01091403030301030f0f02030a121806121e020406080105030c031c030c090f0602031c05070507031d1801090501050607 79
    0x20b8002c042c800c00c0d00c120410b0f000c2091013400b54058440320354201c0000ca84404035824500e444d081c0e807401e2103110f03002d0a4800002d82030f44c80192401a5061861105182c3c1800f05002c0c455840c0b541d40781e84000c204100000185050081e4014190404400306031903214200142186060750040041c05000a0303d1405980340042540d045a030801c509605507081d9042444450080a4020f074040c0581d0b003040c01800341d149030310b0440b400d46030384507041181d4180350685041d9260145030009403110400c5002849650010824400180081d007081100d071210003040703a0103a0301c600c0214502c400104940d160500000078441d400750050130702c00d00302c50b40c41c01070b0780c81d8012518141a5075400711240c162182403000090900598810500c1b520b6000295998001c54a10300074a401e044884000c40d1032405001d02032903980d02c504d820b1450740d50741552001f214849601c545000a0f00b1400560384903058415084401c480f110300399410003c3c5842a035005030441c0380a88410824240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 446872589 1250 446871339 446871379
    0x331063602150d020c03120f040f02101119060b03030a090605070501060801020f07140a0b06150c0105010b04060f030c050d1e0911030c0a030507090e0a0503040b0901080105 76
    0x540c254101ca85803003280c88002402d405020f8002440e865610200303040001c41c0d8000024248803100c0040000550368002500c0340c03021041724000c0c0a80d60554082c40182440082203c580070039050942e00b0110035140c00e0f00d04400c600c4e20721056402e1030b6080091000d988a40c00003d10244c0103103141003c4040041d00c10403440c803900b810402c00042c0241442020360246001d00045002503603200c402c4443c20402ea0171150094032200640c0c41150700c1d101c070000d088080030f40e104001103482c1c2e440401304803006040c03a580c0306401a042002c00300c00e460a20490380a4103406101c1604e8900b003620003007040100c6255841854a400c1d0341d90700782c0381c229040e03d40040d0384202c0820380020005405c005c280c081c12070307a000e5a05000c9030404015554502001026003602150550807240c000c1120704403c80c4005420354002c88000d1200c0c02040d004048080c42c05001c94030701c9000c2d130ba201c0b0b1560707010364441e044a8001040014081da80050740c14014034080b034a2102d4500c0c0b050382c43c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 446873839 1250 446872589 446872691
    0xa12082a09091306111c09030c0201030e0f01061e0b0301080304030f06020c01020a080f060f0d1407080a030929182b060b010311033106 60
    0x342c070074420b150015424039001c0c0700308814243d0107070f400c0c400c6400602e000c1100c0e410590701c14220407000c0060340c5200220b44103140d5084e4166440c00442021034006600410100c510700c134160203554601164210240035003401088100080210354040c40308000008415403c40c180140c0100300402c1800000001d59080c1d94100100b0b04501130070f858a0030003846904000b0342c0f154004140860480c0d04103803400e101d11000e0001d0446680c4c1d440c03c200f42c0500c1c24940076449020400024041000045c25080c181040421200c00e130b48c0701c210842c03a10035900400c0b400501011800e01c4410710704081c80540011b0382d103131390070340307050304180c0449a0042c5100782c500ca2041610440e91030703031901d5940c01140500b1600b482d980340d95003405460480000e0059803d503040c4502d45040354464810a560790002000d014155180c9850713408000d0140700c0c403450342c00d54402040c1540d035400d810300700c42c0c00e2060000184c4030b03881c0110600480703141c54500c50a003050b5a403a4804120301c0e1820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 446875089 1250 446873839 446873857
    0xf03190509010c0b010e0402100f02070306051b031815070e0103090323040501033c0905010c030c17010b180409050102040f08071a0d0504050a12082a 66
    0x1141e15510500012940c0d0341c9100340c09841002514000620320f0b541307000d201d004074000c1d612621070103034900094644030704a80034200182d00c00503040000c80c4c6103602090300b00c04030043e0003840480b1030500510680099441000800d5034034000c960715201000982c807409000d07940c0703d01c035240c602009030001700340c440305605241e2035a0303414041520480002c03000395a0450100c2248030400017100701500a03005142c0468541100c41c0c030f1101e41802c035007400300c0d450300038070803598451004001f5454560b440c911300640c03243c03a2040003820a01504400c080da03a60009501ca0003110001d101c0c00c400a00d40310f0094a4500600501d0300c5e0108840800e92104001c0c010000760f500890000e0110360740260065202240100310150690b1490044480060031a00515229038119184203c0b1100d086401c0b0b030104422000c4c1000c0d0340049501038018000e550102d52143c84c1d45403090410320110b0b0016400400700900d040040740380889840303a03210750403102d03609000048282e1113400ba0fa = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 446876339 1250 446875089 446875097
    0xe01080115051203090d0c061404080706050703020f070330080604020315031f1410030b060a03020d0b0406180302102406050a0e040e0604060504151a030f0319 70
    0x3049150001c108111141c80718050500c10380d06403113041281d41c20b1f50b540103a0300002c441c0c94182c0c0e0800702c02015101560942c00203031240750310f0640c05547c1d03640309070310442c05e501440840f195071507030601000c401103000711410102503a06000f885405540240e0410510910f2207c098541d51310840081d80117505480c016034a446107480b00402c640440000765240c400c98041003001e2100c21480e0300c80740c6d6400800d100c000185802c000600c2801c48445484143d602c4040020072000c1851710f070811406005e24856944a802092904441041c1610000c50035014003003001803610868148001040407a4072111540d98006d441e50304510500c8401510f5881400c0d0040c82924a03501b0500c2c000310581c0c810b0fa075820064400e0300b2407206140414141c140b04001410300b4091322130065604400b4040e00d9440e56a142c1c0101800390082d02c280b252418800c0c2500a184210100440040740014940201000f014a05540c0d00e80d405007030b800038010446404501e1081400482075420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 446877589 1250 446876339 446876359
    0x117041e0501061703120702010506030d0311091e09070302134505060a18050702071a040f0909170d020702060409060501020f0f0d0f030b1003060e0108011505 70
    0x601c0c1d409000e841d081016407000c290100c4141c504000001c05151010003098101952613000680c00c0320411107006405400c900d075002c41452080e80142c150009414615042803a8400403900c0300340c200c03050303002c00008803001400d9881c20b162410351014592400b5860040c0000e9120b180850f80c0c4a210b011503000c0c16410351f950202076244040c1c44d039119900c9040d41810420b5450f1758054620f041c1e0451820021900c1c90405110001c15035606a201d152070301007107649400144002080704045001d45100416440855005010784200103200d00380c503681450b01100441c4210342c030411300e5515051100000a070f034419000c0c07d00110080c40d40e210145610802d01900c50607a0003036010a00107000300b0070401070b074411002e4600071f81c202e40400ca928104076a5503103a00307175030480c2a4041510405c00750700c00e500080046009140100f501d0b4a902c0c0801d85540f0442600000300b51035142c18400e48281107100c50043c40300e00020300c011300e01d01d03840081c0392006026150141506c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 446878839 1250 446877589 446877593
    0x1b180c050a0309111921050d050c011b021c1b0f0812010b0720090a0b060f0304060e0115060e060711090702011d07032a0e0f0103020117041e 62
    0x24001c01c3c4800741200342030045041e4000c03c2885c0c02d02602c20440750640300c48119204101e110160940d01500800f04c0044146e001d540c1c82c8c00030140d5171307915900d0792840030002c2400100c0061121040d00180581c01c4040203489004a000004004000e8001c0e07a100081203c1c101c5400426000054114500d9450410709102e100701c020112090301080c00015910741080c0c020508580183c89450203c20802c0c0d000840038009964244c0c005614404500d0400c8280d016081106005001d41e283c015140c203001c00c1900300700d03000d55105a03a03246d4100011030a01492040c0c1c0301d841390440c5c80c1d90802c0f4014007114210400c1900811006c116641000300d00034a410303408a005218519504e88a6002400390844500343c504810400304241c04003040011030400756030340110240d0022004403c2414607403421700001c1003080400310001003e03040d0300d0703c05e409022010b28405140d81140009000382409210303a80302501c0302c0080001262450707815903d0000e40b000305c010580d51078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 446880089 1250 446878839 446878853
    0x6140603210c0f061008070b07030e0f040e0a03050d0c0504080a1202190609030212030115050304060f090317010f06090b0702010e1513080304030323071b180c050a0309 74
    0x48603c0f015031040d40140449070024070380810403500340c0811102582d403185154101400b5010340100864020b4a13140c496151184030388100ca000500001104440e940906150424023101030b0041013000031300d4801501207000d402401075107070509610b4286070075400d566508072284098820001220320002442c828402c0040c42c1e165803d400d00e4a0b152401d0003c024200c0d03420840c00f40c42440803180288807280c0949040f10180030a0000300e0140e0030082d660741e0f100800849440da92580c20070601205440b46010481c040d59030080144100d88500b1144901030300b240c2c80d0f000c1004001c104059001007500c050724014101c1c5911413509100603140343c00c1c58016a42c0c40322107140c450001c803007680c0c05004400d00d003060101003a076650080340c1d00ca01c603500016002503103042240e0002207507200e1031103801d0f40d80c80f0b0340752601d00c04c1d403298194100c1405040d4100b03511450204071108810700e0300c00100090304401c00c400815a880900300d449074249850505440d44160b00c203200c20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 446881339 1250 446880089 446880103
    0x111030f04262706040b130e040503030709080c0306061e03010509030d0b0d080306010c030c080c01021803010507020a0b060a03140c030f03040b04050103050c1606140603210c 77
    0xd44019541001c0c1221002e000c0b50300700e0324190308410030b050010b06030f8080f030014491090b01c1c0580f000d03203440d0500d00c1082d040d41c40400300341043c005540c1c1c001044c40e10403011901c500c1c0181d0281d501e0b42003c2500070000f0300d0540c40044158010f88540d012983c011851681042c81107440310f400060f41c0e404518201c2403000d003d40c0c19441c04c8108600124040024261036814000030000790807800304204414000c02c1c0d02900785001400000d085501400176800c905000c2e0908040c10295070f030301d0a11603030100c075604101345d4002c1041d1144010005c641c000f050000c4000b4041f61511810081da00c000303040000e01841c002c0800305146071184881c98014541140107240c1b00d03e0b81213083d90392880c170101d11902a20400100850000d40031080c0e4041c0c400407030185203081c2c03801e4011406090007030164a003000301000010440c0072101c11400001e13100f48030101b800501001c0c0e048500c040140018086d81141d080c0d0310400d5400d4a8440c048907030071411684a0540e20001440c001d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 446882589 1250 446881339 446881373
    0x705120c030c0a0303053a060e09120d0b0604050a03030201090c06051602150c01240f08070902090105040e0103061505060310031b090908130906050616050f10090b090111030f04 78
    0x2035251f400d40d0003e19080b41007038070210851011107880d8104048c0d91444600e0a440450006204d901c485e2030302d03500b1a00c440000202040e0500b500d400c0040c503650f2465000b200540e5403805080c00304008172000740c000701032500b00301e810701d000400505075610981c08028420821580c4001c5180032400c143c0c0d08145503070008101400408019020b100c0c14120691040340c03032030700300244100b032184ca010300f0307528084060f10716a031819120f240a5080551128140601400301140343c401002c04240258003810001c0b903c0e080804541c0c070489002d801250107440100100141407031440c11081c12694425070b150341000f4581f200d018094040d4102404880c2005c0e0704905000098014203940f40340e10004640c95503a802801007100c140c1e03c10140c01c6007050003041c5803c6803450781c10040c00e0242d81914000026140400d01f840c14600342c054050340d46400f180280b0101d00d000715441b080c1c20008018030903805508440c40d010080046550b1210800003031304204c41802c01b400521 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 446883839 1250 446882589 446882677
    0x613020310050109090c0c0f05070b0d061530060b0a1707020303151011011401230901030212030f040e0a0509010b090106030e0705120c030c0a030305 66
    0x300700078161808040c100d1185030300180c055000032400a11038132640b800711407184c403440100f5540350384620071843c100c1000c0d6014029400000b03501c0f144080140071040060200260560401303009441c02d00c0044081c078208142c01c0c081071a08510030982c2d809460303c1d08400c0b501c490f811150007020f84880d0b00106403d41c00480c219001c1504041198200210041c0b9000d59503a9420100ea59000458044114800c02c0c402c04419050011413000304a9040c6002c0110305d0440c46240e082d01c129584003a10f90079404010440c456601e540c5120200b0780c40c0d02038101108202c0096614078044c00040e200d40d100703030000c1c1032088040044805d40c035100211151541c2d941c29032804803403002c8900172050341c03c02000801c0710b081803040e40e00c2400c001301728004903401c10701e00314000d000c41082c950244c45408030208459850303a42140c44801040000c201c40448c2e4400d160401c1007540d05a40541620441400041d4001082c1c0303928050301c160b07040f50100300e40324084451101c01003041480c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 446885089 1250 446883839 446883841
    0x5030a0e030c0c04061a030109090312020a09170703110927030405090105090c120a0b0406030f02040f050603100c02070302040c200705010527060c060103110f0f0906130203 76
    0x40402040003801c2d0b103c1200d0800c117040d960340448000c80c03000b50a104042008000510070800300340e120b41a841d0003483c0c04a40c4011a05040080784d2144084401144105070104240000c0b040c510350780d00e80c9103000d0b004a52441d0381d24020038482160b0103104818682c0012407042103200111561001c1d00145101a00e820701607649960113030040a000c0c3d50014004519030034041c0503180a2540c40098610303000c0398144084241c1000f410540480352a0a4010001c1d55103000f0b80020714001c0800e00f026a000344104002c64a0542da850200c40c1000200035030345e0340205120f80e1070300c2c00003008283c603005c806c0228200b40031904000e510070700d805416400203500061520000e558294112080e103021401d0035a9510380744509400a0400c11006e003e00888103950322040101d0f000c0990111700e1800001c055800150750081c165202c400100213000d107043c01052100c200380ea80003c0315072100c01095443e1240580580a0600000854100c3d2510f035403003441280c0c04403085441e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 446886339 1250 446885089 446885107
    0xd0c0f15022b02041203260a020a08090a05120d020d0f0c030c090f060513030b040b0610080105090402010503190504060b030705150d0b010c0b040c060813021005030a0e03 75
    0x1042c0900303161114405410507032a07501d55140c82100c1c2a5a5851081e050404190341c04035070704102c1100004901e25002c200d0050350301c2d101c1d412800341005010150302d070203118070001c0081c80014940e04003a0b11016990002c43d002041c058034488084101c141d03030b041300c1c180313041c082d100b201d58a8080500c1d100c0c1c1c0350200c8500d40d002d449445d80d295002e1100c159400012903500310b00740038a40700c0c3c22003800300700f102e540101d0051010390000540c91043c07990b82e40f01d0341080c10007140c0903a07010152004020b04e80c5820324840841d0a2030741007520565042c50040748030020004d10082c140f106c004082542d0550002006030340015981c028003071403a043c03170b004000c6c04054180d80c0c040d1056210100d080d10701090041c0c800c034007000d055400c00e4410b04010005d0909071440c18144042540000c0c04a503052940c0c42c070071809142500341c010b250500041040e4001020302c1e00100d0b41810420043c1e441019041e00c81e059483c280b500d9841d0394005000130020801032000e544000507140c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 446887589 1250 446886339 446886367
    0x30c0b07020c0f0d0b0109051e09070f0503060c0f0f160c09050702030a1d15030406020301030203060604050106052d0403062009030a060c0e06030103060e010e0d0c0f1502 75
    0xe050312090783c9200c0d681082c282440040481c00c03000524421a0350010701c4070f4151a0702203580042c803440d0310403031403000c00b01100c00e422054a0641c0160400b0300280300007401c000e16240100001e900078106450710442010590007403071198000c07901c1c000f401500086400085d103051100702100c0c2e00300000c040c40c180b0321201b120301c141c80030320342014006490940040141c4060200c0c0c5d4613a8400310070110240c02403844101d80440d4040700229850409011200141d4810b5100740001a03132541180101031801c000200590b100303508040041c8169580207040d1003124120410440b030300418094004144a000340624440510100700013050000720780144801c804000d00094004481c4421002c1c24810003004a803d58030003d401c0000402c01d6210b2232820702980f034141d4102c1240c2001901503130003a442512100e4880e10f060304240d00070310035202501e45810050600c04105180030b00011910403018092030745501880c1c0912024501c1050015401c8904550311404900400c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 446888839 1250 446887589 446887603
    0x40809060f030f09061501120f02220506071e02120d030209130501050a0e07090e0112050c0f01140a030209030102031003140c01081501030b1801060f0e06090d030c0b0702 75
    0x221000c0c55460204103150300210b0514020400f444501c00030486c031100554411a10070381c20100c2c26914403c940304034142c2d2016040e00042c8101000000b0604260424541000c0d0803080c070410040211a0000d40043c1504012505501100042d9581070000420692450303007480e2140c061716500d082c00e140e140c2d0040c0100c0d9800c640340340b441c0b101c1e251400c0c1200d600340900c0e030304001046000c1c0003074152158000d03401452403030300c0140fa81d215000c001c01181c007030780700004400d1030100140801000748049144448152400000c0b0381a030000240011307040390043e00c607070718000b4275a41014460f4040700da1026018000755a01c0c01c3c05510002d442c6401d1206540e9190004132400c01d0b0b10020130f80c1d03203152405a40c1c2e5003086d2200b04506000e003011000c5541810f6a9007985800d46d1283c070f28240c0c0040d4000070252042d8075045001d0400c1540340d8420003080444c4034551920740c1c80800340c07085680181c0d60940f031a4001d14007038500f1105000d000c0c041e098030701c04100c45558005002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 446890089 1250 446888839 446888851
    0x6030e1015061107140105090310230702010c0c080f0705070b0714030406020a06020310030b090a030305070c050a0618150507120c0e09040c0f1404060b0408070608040809060f03 78
    0x3c50319401e003003007189481e0403640c000e40ba000703451029082281c1d80310700041c00c00e03020f000301a9030740c2d1111000181c088542c000c3d0f0150020800e0424500c1d03421059601715400541800203014440000c00c004018210310351004080b030102195a14550034100c051f0341c1241d62100459200c82d840f41002582c640180c042101e804075096180c4200070008419941210426001001501d2050340c0d41e10103500002d000c45030002c056400000803e0300c030710a580c003900300320010f806060490300f002826250001d140e0b8080c0465a031070080080c000040008880b07801c03000004001c00b034bc2c041250422000e00d005800d0f0301c000c0c2c0b205c10155900d03510040c0259429181c0300082000d0310008002d49074041d040340d000c11010300c54400c150410010300e650040c8140081d000041d140c40d0030070300c0c040f015084102215443c2d0b01c041030f5814184610750140c00d1460b145810301d031a001c80d0b69500c40c0540203030020010103a000c81c041000e664196120041c0c014140d503264045072035904a6500b0031074071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 446891339 1250 446890089 446890097
    0x111031504020901080117010209060711040b030606030c0d0503090d12020c01170c0c0c06030a0b011403060d120306080102210601031b0e180f070906170106030e101506 74
    0x1080301039107001d108903000b500f81a15103101c6686450040d141c00703029080300700c28954081090140650390a0001d081d20391050348403104000c44e030010310084421074650070380030354810750a0010b20381c0e000170b00d651421001c582c00750600d0743d0b0740b9004e420b500034800b80c81e4000c0c134800514002c0041601d110000d4264079800c4403540c882c3c6400458254456005c00d60781405500d0115641403405d40041c41c0c9604074404698692206401248150b44225045440290342d410310b40c600351390140001000c440d000300c0745411401c2990008130030030401c040081c030440da81600c8600c094000d0b04040014643c03800215112075861206e042505895640041c00600101c0000ca0540c0648141c840c0140d000c00124001c11300c41a05482000e070b42c1036500c0c0e0000b2010481e503624040055410f1240c00407510f07020590a210170080c000c42500e030051004c0c0701c007625803992010b800701a86411a11a0701d004100c03a00c0d800007540c2048900e18545100504140c46410b11020300002c1500300ca0041d95 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 446892589 1250 446891339 446891371
    0x617030306090c0f04030215070b0a24030809010503102711210a090c09020c0f06071211190207080c0102010605010e0d140a050120090102060720011103 67
    0x3c40300d03414440c0000065043c0410301040c80035091a0000b04400b0350301080d103900d001100e031241c0d0000301302255a201602d403500200c5100404400081111103a410102d9560906540e10b40c04903000c0c5107000c0b81000000310014841800e00f910800c001c24400c41a100c45001d0042000d08503a2110b842c40e0b82182062515904400c0750b408894110200410071f240300200d42c004500800e6000c0c240d0700c3c2140e00d030151000890b586610f050000d00f01c2d6140140e643c8204d2210a08145c448003998020ba002681003080c2650054450030311003090400006100728203001c080c6090082d250585080c0700300b80d074108102900002d4a900741c9101c002160041404803004900380e40702c2d03005e4280007a010030f203c800d00e410950140c4104502c240800d0598071009030300d281c980040200180d420f0381d142d00082c840c403196050b55040d0001c3c080d8225190200d8580041c0d560034020303101404010341e0040e00f5003990b03c1d1041012400034400024803036404417148912040c0c00a070f6504101c0b40c0002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 446893839 1250 446892589 446892601
    0x911190f0305010e0c01210f150801020403020a050906010507060b0301091202030702010e03160311061b031c0b090711120c0f0f030c06010612060b120708090109080d09020103061703030609 83
    0x41080c1d1990b03012040c0000f145400e10307494406404034588d4103c8190302c032101c905074940b0041501010340842c00c001a1911b103035004010011089501c00340c019079841e000c3c1302059900800f01c0b55000e070040008500c00e204480401d00500d4441e802408040020040d032000a84c08001006424004d90707030350740811000030405131903500d207010f0320180c84441c00080000030b03014115041802c00041c125400c2c0406407036a9500340803840d81d504215000011840c050701212508243c540804a004101010408000c03820143c000742c400014003160300c0e82c080048208108101000140ca9207168561040c0d0b481c1c2d568520110881d6013503070090013503581d480744000050f501c4205510009001503403818505456034800d42c0d001c0c8140e1030312601c0102d0100340c03d1005256548440b41a02490f00d8100c0c03008250700300140019103240d040120a4010480304800e482d00b9082418002840525510042e0004c04a9500004c8425803482c000e1411140110281d807045c0c0381501d070080265108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 446895089 1250 446893839 446893847
    0x1e120a0b010e03100e15100303090807030827041a030f03030405030304030c0812090c0103111201060f09030b09060105030607051e090a030b1801060503010911190f0305010e0c01 78
    0x12030140e605544550500342d04c0281c1078002540400821095900138030201070380014a6004440d225000d9a0743d401c10001c1540c0034409000030407592024000d02801d40d543d07420180306d00c010400540b103404004d561004000365800d8520034005104012040703500e403003124007044c9008090b129000300c10007041da80c6804001c4901c0b60f03074018080c6145659544d02541e031020180380a8640c480148500c0d011407006a801c5d601484141c030040190741c50500004054030380340e83d4440391124017400b03081010924040e100e0b05448250030280400052141c00311512215a40040c1400d40440b013807006640303001c038109050342c0d000d500b500c0550752000c100751050310514100c0e10310398038001082841ca0036002c010f440c0d0098002c0010410135502c1e2128000284151141a90b901c15001030382c48031002440741500501c402ea00a000840b55174844004280a000d151800343c20392030391140c040c60554a05801414040485000aa0f10ba0030014002c003600080c91003540314184101c1007135070203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 446896339 1250 446895089 446895107
    0x30d030603240905100e0d110604140c13020c01051e040807030c080c0c0132030a11070f03170606040501030903090e07020a06060e09121e120a0b01 65
    0x10040b1035811030403400d500c0241006000015039001d9603038a4640c00a60b050140d926604415032000c22035850518540e810b203203001c40d040f000d128030010500030540b03020425542c461740010740300c0380341c0d18084501814445a07104071540030300c418114440840c00d42e4041d280d000c9d9844002c00440ea2107000010030b00c81110714141c0840003240c0050001044440100b40c202d2092502c40722403c603da46841c01c940004001c1c60840c0c01103840364085580c01480c240c043c020808504946012030718030101c1481f098082c4070380b40107001000514040d0942c10007156001094125662518641450035090208079811000507180413110381e40c1c06558001a40034850090106103040c1ca004010340c000c040d202e404034103200c4d020600082c1c601585900310303c1818507401600040005242c65011220030350420104010700c101408400c01000a020350a000511403955176094070210b0390034442003003014004000340014500044c000c1c44a15580a80c0800905000080c9030030015206080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 446897589 1250 446896339 446896343
    0x20301061704110a1403010e0606131109030607091e030b0109050a150833060906181312030504050a080d09061a0f0a060206270607020c030d030603 65
    0x15407101040072000e007101d24140c0051240c3c0c1e42c44403000740c00b004500002c03900d500c000703011441c0030003480441c102801801801c1d81502c01400003490b1520019078410340300019990001d03034500404880394803041c103d4000d910000e044403007034074207020010034902043c082d140c0d41684509003040d006407450b04032410f4a910150840003a0300f4449203800400009010260440d00c480e4104580c0b008191404c02070141140545504c2040c0f446222460044c501080d40354a10b4080d0300303440c030404402d42c1f90400300880314103038261180c078005400855203100d98441c500c0d15109000c003404a003030200b54042c0c0b140e03c05d8495200e180d0800e504590b011a005803150300300d200241c000a0f49280103000082180030002410506526400101d450300281c880e180d0b0009000c88220b8503180390b803100f90401c11a8441c59003818140025100d10004d0041616007119420303820707114070040000d0b01040980000c03100c2a1400100003507035045540e0078036001e406020a078242d0944240036442c1565 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 446898839 1250 446897589 446897597
    0x1b09141f1208030709061b030509011b0c0302012a02100e120f100203090d0e0a080d0503011701060803040b090d06050421090807060c1e0b0412020606010807120e060c1c02030106 78
    0x701f11074038290390b2a0f109003103560401c82d180443d80102640c0d40c400c101345d10700410703501c00c4260a620000d0f040407000b62003840600e0701660700041c103120041946030b600e0360542e0f034141901510201501e00c032824000042d0300100c82c03040171540c00800181c4000080ea45011250000b01800c100c404a02c02501c841c04c030b0f03810175000130383d00078050705800058002c06021000b00c1641e03121054103140051400d940042d0340000104214901c42045041d00f241c410000c0041a140c20b280a5480c803417807050402c0030101080f03181c0c0a650b4204011241034201c0ca06210600c0c180c030f40b044c500c3c5800c03003030f04407510090805600c0c00d9103d80400000e40b41184010f10065003050300035180c0108640003182e000780c4842410030701099154140c12290312401d20140b4a00385450030040441e44858500119401001000300d2aa40f1501c103540001c42c034202014601c03500a038010151076980860b039803912a260a100300800c103107004101c0380c01c01c4502d207004200203410901c2070703120a01c9544009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 446900089 1250 446898839 446898887
    0x204240e0d110d0b01080102040602060615120a0f090303020c10050108190c090c020313120c051201090605040b091b06071704080a1b09141f120803070906 68
    0x1480100e111485034002014183d146116543e520340d880f0b8241c00c4070b2220794000c60b04000440d010400260090f104503058804a028001104200e0241403002c03040c07080c40300b0100c0c0d0854004d130301078080c10041034000c0c45103000c02d04000d0041c0d402000720000c5441615890900d913042c42c419141a50341e050041c207040c0400b407400c15801e242c1010140c0d10071010420002d10320480d8892003d0f40d00d51034001c1c40c1c80d00c203020900803403061146e00541c41041900340310400107000341411415140c00310788041c1c0107852010030f1401044170140041030721f031412040c0320601134102042407081040308126921007451040d405206440c0803091600072300f050200c60002801d12001054082452401a06155403031008a01e000302c2100c1c240c07280d6200003c1c44143c402004440c6001d0640050244100c44e08180c00c49613500c4003c0c5a110100d805182d0b91715541c20311403140000b4070319508071140b10603040c01c02c01440c1d4415183c9030086280c0040c0000c549006590314459011a03240c0c0c8611 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 446901339 1250 446900089 446900093
    0x50d0506070806030c0604091506080106020c01140909090109110303120c070201020a170703120c0507060c120f06081c0c08031017030d0b0103290301020d0204240e0d 73
    0x601c410160603c3d92600a0f800c0f860031580728440644014145118086402800110301e43d802d1109504408100701100c001031148507000070307111706055400c0c0f07081d2191000e08002c0c030b083c501030700d01c050341d11160034000c3c40070030607054200c528100d00460380e0361206540001019564030402a220300c900d121400040c4002d0883c6015194160060040d0340c0754618a642c0c124407c0300c8460390f40714102021030480c081c90303807140d580041014100400c102c0221000d5001e045401040002442541c42e0700103c80c0d100d02c00c18000440700c1c1501c0c010b1000d071840301880405064940102e5070710b4420810008a411000c0303c084c0c4c0e89540d95240d01942c2020703500c811160b40e00040184401c29560000010079082105da80114291508013458460035100b80d010151901f86406070304040c108200500301c07a210100041080d00000143d800e06c2801c500824003a003d801501200d01e4404540090201907803c87ca8a440c01100c03900117050180070802d0b03401c8008041982e03088a80c41c086400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 446902589 1250 446901339 446901347
    0x12060a0f020c121305100c14010902010e09060a08060901021c060501050403020d1b15020c030a05100e19081c110702060901021005040c05030d054f0e01050d050607 72
    0x948980441d02480c019501c400c081500a501b0320a50000a1003208164040c4401c208418040f014010000c0c844040300760002001d22444114551083c080e41001c1000c0b640c0c1d01044000804200080e42d065150841d14a8001d42040c0003007544411511824052000c15200f800c0c00c0e214140c40312820b0038195024880c8103601040100c494071801400c00846d001c3c82211003000f003441034041060078008000080c104038085026a01030351104001c40d0008a0201d0b482c00050480107000962101078aa003a240100c0c1c205040ca001103103822040030300915000a1660b002c450f0030fa40c644000c4100388804a07081030400c0641e03548184800c400601d0906d00400000e401481115082c0003c0c9000d8001ca0341c0c02d980445074001040c070300308103030300381072145082c0c00e01d945c1042414410f2848000c80d45172810f40120910120516240005591800741d461004501c80c4c04400131000030701141140f104180229241140c10000000f100d02d855400c1080c1d4035400000340100ea11218410340b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 446903839 1250 446902589 446902597
    0x30c0a03050c1c053705070c1703011e150c031103030f010f14090c0c010e0d0f0810050d030804110423070e03060f1512060a0f020c12 59
    0x110b44104070b50800c000c6400c1c01d0300c64000841c4400511810418110701103107a00300c0740c0b44d035002030b580030415406407036803200d00c801a04010702080564a140080380c0ba0014014014100990500d07841610020000558140c80d10303002810158076503021045154084d40c40f5072001004400c1c6c059003d14401d800042110b803013400c00c503a0800a500e20141036030402c40f43d1400c8001804010001c42000f009280020501e0400d0703003030b5041410340440d0482d44014064184007200140560208009600646802b80c52000395044141007400007004580c5000f19980026005808201e50018440700324040319001081c2d40410314a655056a42280003041615004481580300540380c5440c0190740182d030000855105000f40717002c0b005101c0b14094890020003080030740e001001d450002d0f5250300405075030440105503440400710210340401c030401030340041c1c40e5903404013085000078425018488407001404a1103412000408a0040c214000c6c01540851503900070080c0e898014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 446905089 1250 446903839 446903851
    0x2010204180209030706230d0903020c06160201030b030708071e0509070e04090614010b070605092107140d0503040519020a210c17060a020c0c04110c0d0305011505030c0a0305 77
    0x28881f000011490804580003845440c06107078468200500305079041c000c12100c4842151321505151107110b1000f094290990001d05059075041c1244c05070740e0400c1500b004200c1c80045440c100e07200e04081e030981c40303102c80a1025011076580130070301f03261084006116000507075030219610f034081c0c100006449042401d55005684142d013030070040050809602034070f68003d4079603607599185440b40c02c80e00c0c010314602240e0007900000d10100005c50b0f5803034980000800c2c540e201c0000c1e003002000d40c12212200300300d40c0316115410a11036003007000f851150f03000d075040d01d030080d000303042d001c4900105000086d406000c5000c103100c2025840c000100c0c1282c14100500c10000555440c080d07040035404c00c0c41c010900c0340501c20900c10410140358004c2c40c0d03501c1541000c0b81e0704003c43e602d526001c00c5500c6030b901c500041b50850101d0f000e13120384000312011224503541c1c84602400420007070082052200c01034030b80f0031029024400b01c9002d040e06c1410546070510501049000744009001c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 446906339 1250 446905089 446905127
    0x10804020f0d02040e160605091003150e011806050f0f041a09090102071407030c030210261005061204020906030f100204060306090b0303160303020903070602010204180209030706 79
    0x4096159803142d002c045c01810003c043d0014001546c3c940b000c0c846d1311100c2004010403c4010b9a111451054510001400e003c00c40034250351005100d2851600b010802d441d076000002100c0c00035421070003030030100382010404140c545003403224074001540583c5d00109003120386551030501d81d00c200d111048040c1c40a40000700c1000003460881c0c01d41d1100c1d00790b900400c65400b400b00300e0a00c40301c400704a400802503903241da5252105010b0300e2001911840c4c1101c000803803180200c60300030301c154824106000b54841c01e1303040d003c0c450003502e9808084070020800300b0fa6040c2070302100c0314201c0c0402400342550341c6030f080044c400001008943c140c09488480e81c090b010420121003904900310002d6126824942c0060841e0300301c0d8456034203281008500c0034244c801108480352880d40130072881d008c0481e820154040d2003025a40354252140840000782c0c03030340c10f41c050000d4514507001400064455003021059000c0d040c085035042d001214104801070085c400e100c6030402c2011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 446907589 1250 446906339 446906359
    0xf0c021902130e03090906040903080a020d11030c0a0f0207050a0302060c07150801061805011e030905070f031502030412110a080d061d22021302070305070c1202010804020f 76
    0x802d10059070a10002010282e2002c03032004c0c01403a1140810790710100540b0100320313070034003510000c0c54400f024043c2102c1681c0050458118041038203c490740600f403a602503a02e0406a00ea02002d40c059503800d400901103021326403000c3d102144540841e1130040040d14014115001c0004940c4159501c0c495481000c2000542142c03c0502501100403138407130701d02641c98580040c0c81c010b9942081c0507100b226400c01e12603681c1045030b80010750801d5440a5410b23030700c03440540041808040c040e00c00e205481c0c00145030640d90101d881964803c11144015020100003681a4003042d03400801e1008002944895113209240302a04107500e50f0448080c000662180e01e195401141c2070802561580f8081c0040148210080c0e4510030007154120b8078034026400c80a4480c0025003c3d42c001c03c00001d03403040d90b8030080c00c0001c154800700304542c2e130a01440d02409542c00100d0803a0420300c02140040e0404800f6802d03600503070107860b560010395640c0d0030032220301d10004c000c40e030052106c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 446908839 1250 446907589 446907619
    0x30c02010615051218030a120b210c03010e070e07020304030b040b041208061f0905210c01170c0304030c06141b131503110d020a030f0c021902 63
    0x405101c81500d25143c50b550740562210619845100600745400301c5810900c070850b9110000490f034590705645040c280c4c01183c10751080c0a04048001540c0c40100c80d107442400d402d501079003480080c0c3d03a20403591070100301c40034182a2444502190b1103070308145010440da00100d000d055011300b0710320650b8642034503a5508110b00c2011b442c1a02c443e9280002c20042004c0d130000017599600f80e003041d4080e4980300e00010003001c0c0c0000807418006c26040c982d01e20358000d01c04100030384002000c1103403855004000c1340202c04044a042d102e481202c010b01034550103030b0001030022003031100351f520356a00c00301070307003402e0f0310161003141045203c600b624080342551180300b141074000c03002c0301b11604144041e00032030310b62070b81c07400c0b03c42078208a0240c60380b201000701b204461501032004d15018009205034000c0081a81c07804004000007920b0383c0b500c0495009184282c0a91420003d456102d0040d808555002588501690103648140c5100c01441018079034144001c2800c500c0401d01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 446910089 1250 446908839 446908859
    0x507080604080703120204051c080415020c04060b091318060e0606010f030203090a020108061206091c02030406080601110c040e1605030c0603070c1110050d050907050f01030c020106 80
    0x720340903200b908021601d8401c040d44511004c1c4141c54000e001e40c20241040c0000300304070101c400c007410741c1d281c03281000100903070081580c00501c042000090300301702c5424040d40301c8410580780c40c406c40c80e080010600c0b854200984541c0403004d0310080b8034103054054a130041c511801c100c1c24003401410000002090350082114003601c0001400c0c007820804009401621034481d01c030b080c140140100f00e03115000103481c1481c02d80903e41010103484003404220b9420740300c4503004090040c0400c101c80404009203880b4200202200210603440d1031008036100d0040b4000d100000d400003020130202d45c0b007924845400c805003400d40c1c0b86400c7ca0300004003110344052010b1030a40102c2ca00e0700c04801c0260603000200025805021580a403c0008442d844010710030000d10401003101c0d010f001c3c0300384080c00b0103e4007508840340e061140c2ea001d040b50f00920710500030107007400000307011307031700701007030b201c044031b01c081e100d0740c11805500015005000c0142d0745000b190741e81c5200003011204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 446911339 1250 446910089 446910091
    0x8040f031b03050705060601081b0a050d0f1b020303060334180608070f150c0f0b040b16022e0216050c12032b0e0c03061f1205070806 59
    0xb0070344800f42d480100f407400c907042803070007030096060004070020800c2c0c06852400c00c2400603840142e0f142d0f00c45c2c4007072095070b042c083c020085001038540180303032029039420340c0051a4082d044c1142c83c25411581000ca82d288000c86020350190400b41000301c254100c0450200e8001c3c00c2c1d24000c180d6810b4501c09041145a507014407000c0d005040462000300c40d51146001070070340d2401821003241800e007001a0a0005d02c42c90001000c54518550003921030b054611505901050890324080700381820940000d044c2c0d015581c00b41c100307008c2a0000c0342c420070703001000c7c200e4000c0d101408640e80d2403c000c0c500ca155010001e80740003000c070450308071403004114803c02080b42c00038511890a04034645a07500303180b00d01400310700c01d038103906080000c2542d110303c4004c0c2c02151a480011520301c0e001c00c481811030b014505143e89889495800701e00d1611620b4291b040360b40f150780310280d82c000c10603542140c0f8040240d001041c0000d40d03035400e82010341d6008808543c81c2030f139580350b500d19080e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 446912589 1250 446911339 446911343
    0x50702060709050d05060115020c0d031e0306122307031a06010203030f1807050d0305031e0106050711040204080a05070303140a0822061109040f02070308040f031b 72
    0x3204108560381c00191a50191405a403601540d12455a80c40e80d51103040c007414a8030b421045500c41103d01c00c100d420b0344410003070f1020304000f20710300d4048d1130031040d010386400b00e007140006681103d100344216000c0701c141c1241d0b40c624003807544072031204248018004803014004c06a0001d200010000c1d1401103200300e2110b44030082c0400c0e01d422041c005800c05045410400c180194401081d0150750400c0350817041c40a10085003410616188a40d03010540081101e0583c40c203168100016520541294603100000e80000c024101c180307909004d0000850014017204000c00c4040446040300000900700504e020b80b180705003480c02c00c0610003200d041e440392000703104040d8489001c61420048809240c00d0141d003800c0078003000e000800c0c0584140000500000b042007030320680038820703041002085905607030495080c55910401e802800782d4180540c0f84000f1400744212088241c05a544500c00d07140ca580c2c0b40201e0495407001d81c1080840300c81045080444500340c00014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 446913839 1250 446912589 446912593
    0xc070b0a1209030c0b0114011106130308090a0204063201091208070206041221361401110c15031f0905041e121101020d020417060907120609060906050702 68
    0x1087c0c800004064600403003000901d508a0028448034003451412440501c0d81810304480c0c941d81d0400d00780c0b806034180801b9600909100300025000d00300c117205914038906007001d07030350904000c00e00f03190a60213040140c00212044810032450241003450344603944200e00c80392600c0c14540001e509030704150030143e50003d13280b400404104070b0301d400858204650429500e0702d0078000d0058030305040c11004000b650105082604040c0c00100e01d400c400c0c031103400c03004040340c945031070b4407400908040613400b141d0092408890690700040f080d03541100203004e444140d00c1c016008155400140110203d00250304010b10b00554842e1a00054803440c000000c85161605100511054106c0608554020039681d180464400e00c000311900e0b085082011580f022031030b200c0d0091041c0c10310344400340c3c8003003000300e408135900b0b00250401d0316520880f107007900e070011b0132502c0389030510802c4143d00120000600180e02608105401c034018072000071602803644440341580e504441d51401a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 446915089 1250 446913839 446913869
    0x2070804050306061801050904080904021207021e1209010c0f030309110604150c0c0914040212030f0a030c0c0c0b03041412070b0615040b0c070b0a1209030c0b01 71
    0x90504100303c40d4044012a101c401350003403e145121440d906000e8280070700c3c1e00b0300004050101c1e490484101290240c4119511001082e045584403421744003000140a10410000c0401036038038080c90034110030000d40704036050f0454080b00e035400b0001e580d05000c00380744100c0c041001c40d88a11003035400b13610301286071411341c5010703503928000c0080701d40b141c2002e20050041040410104511408900303207510309400e14284403207503044c40d0340700d50501c6041000d8620700754949450b65000d64802d4440c64204500c0c5248030b920788c001d0715407151901a09001c001d1501d071198108003580c1080e800c0c03a443d18622911014810216600010003540000040c08100007404903082c541c1d0408001803c003407204a6400311103445401d00141c50890360101040d20741e5290314001c9114541e81e0601507550f5621205004250400028039025010307240300000d21a07801c034120780030b150f055651070b144c143c0c80707101e000010304c0d4032242030b4100a204040400000c003400346080c043d0981d40312140c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 446916339 1250 446915089 446915099
    0x302340605182e1a10030b010305130f0206130803030c1b0f03030109110c03071b08010c0903030804031718100204030c09020a050f070309030b0603030a02120a020102090402070804 79
    0x94003c440d40382034880d042c5150001100f01480b20101106400e02c180891400845004c650f002c50352154025446803000c50325102d419090380c0480103c10083e2010301155444168400381c0740081c00340640781d20b03a0062200300600d41000280030089048500a0754240c648200c10710b143c00480c0c50401941002070303400c190040669492041541d910004c002142d855451143c40e804103201e007403c20707600e4410b100c0c0c0c5180c10a00fa1444014010112030311003401d800c00c14042e0340c00001d2003c4400e98410040707030108060007038070001542619502c0d125403855030201c2e01020020402da080050522000070790511041d0344a00807070708900058549201c0008150800b0b20a1100310a40c5104220420016000300008001ca4090140041c2c468421450544151290001c135152051000810104040c0c1054640c1e0030ba90181c0c0c005e550b03070358900f404c0c11703541e104035000341d030140c0e01100c05c104441c40e003100240031600e0700b80f00244c12f050700c6401141c1039070003804003103400708000303c0c5c00d001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 446917589 1250 446916339 446916343
    0x50705030301091416020c01030f0209030a15141e041103010e0d0f090501020c0d1106070b01150c05100507090f06081e1e040201020a080c010c0f030234060518 70
    0x90071112016101c0803074182c6485c06540c03440b08248160505894540c14460000e80d6030565288843c05000d94030fa601c000d281c5054000251059820011f01d001c041d07006c45540b60381054450070307190340e4042450707007801e001640f1000000e0084809042907488583c1ca0788081c011030358001c0c102c0d40140520358023110041e10310140e1100e08420062a800100200da80c006081c02101c84242c070f84200c0d400690400e1090207110069807034011200261440030081e2681f646412508062003a20403e00008011030321100035050280150340145d031040c03841070303c960240d80c22032113604010b42d59698070441d1101056481e440403020441c09420460800c900240702c1032040b030010ba100d142860030301541140f075002c0c8031208103034205850000301164000c020f0f505095402140c45510b070709181035600d0190071840e45400001c0c0e0880401d4541c140a0f009954259007a104103d00440003020865101003401c8400050410790041c25000b1520074800c240c00361010340c075802c000010205800d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 446918839 1250 446917589 446917591
    0xd030b040204120f05060f0601091215060f030519080414040605040f0c170705030106140c0a080a1803080906090301021b0a020901060c03081501180e0702160311060a0507050303010914 81
    0x141010047c2402c00100781cac2d1100d1420143c401c0040407105105260400c1003004200400740d9180900d4401c0c0402e40c0e410441c2c24200306c9200c2c03411a2544080055405611101040010070501e000d010520012240030b4894108000c0900001140c42d40c1e5000501035510b00b010709219269191981601d09500c901c4000902100c0c94601c01c0c0f50a0070a8024034510052140508000303681138250380c405078072000c032485c03080044101c40f20f42240d402c24902c00c2d4020250000030800403004854011b840210541c1260b820440341e5003000c1c1c0020a0003011ba03c81250701d41e1556080080380503c602e00c1d4a120811280980180506256403050102c0302506070001414032608030402d03c0000c0c0e0003000035901c1b610000c0c500305100005001a01c5030f501c81420041c5890b00000041401440b0381e4035548150503640c21601840d13510a03100010a1403404040d0104800d04185110350800c1c0008240511207454041d24001c916103940f401c581007a04a440415151184d07040c4a00b69285e0301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 446920089 1250 446918839 446918851
    0xc01050411040f27031107150f110c1c0501090809240f0703031b02010f0f020913092a14060f030a09021309060213080a02030d030b040204120f0506 65
    0x304100d0031201400d8001d10003000c200300410681301003810401d8450a0310350032007140345080380d4220703440d640d9090702c600c0a00c60240004805003010780b0254170580c1181e50b040881d1016000b080e44010500c40001d800b45008500c00d5200c045040001d8401d00c200300f0301d1409200303c0e1382c6400340e840400540d00a0b004401d8220350300111a20748180f0000d0855040e01444102c0c2030741c6040310b00d000d070054940818020380d0184501010300b03905406412000100c00b030b1280401c01e40d0000e41c032070030403130040880c00c0340c000c8490716454100000d590b000c90201801a02d81101055407002602c0340c2c000c0580203a505085500010001e04035080b54139103050300102c49450910700842007260150000400c1c41e004691215a960f00707549440d40c078144194800401803000801c142000e8022754800440348804400c1208001036030b01d40480d0320310305564000e004c0c060b0a6040d6034200d01400e911903042d0313030255080100146c0c0c0b402e40500700c2986031107505503a643c80e40b40d08086081c920020700c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 446921339 1250 446920089 446920091
    0x10121d011512050d0c1a070804110118060507060e070303180e0103020d0b04030903050f0313050f180a0209060d05010303261b070c1e0b07080d020f0c01050411040f 72
    0xb0200004902140042c2c00909600e019100b559040c188a820b800400301ea00c0c40b01c1c16150300b84501c555000c001d02c1d1203140036003944000020390100445064020b000141c4042c5680b090600c4483c0c8101e0003003250a001c0c45000c55500f5400c0591800c12005a20840120f880d0781c03201c0c40e07000c030b003100b1000c01043c442072010825032440e00400c4405004a00003410820344000041c20907005030401000b071034114080f500c0d00b59180054554075800021144201e1040d0840012a860580041c5a50201c003910040316800d0f5610035000645028014000c140e4003131207010309507100e41010301034804408001248652440c24040c00760034100014080c04460034019510425154422603000719120010341512004048002c1c45802500001064203000c0500010111114081c0d4116621440000000f0b00d0381c0c2e500d414140d11601030014000c100074031201070010b800da4060281d540c041d00e04030b8940081c0180f01d44c00c5401c120b40803540d9180682d00703c3c2950510344a1040d020301d0604c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 446922589 1250 446921339 446921369
    0x1c0203100501050f010c02061c021305030c42030a1a0f01080a020912060a060b070c0e0403110d080f0c040b040506070c1205010e0c01030b10121d0115 66
    0x860300641380d8400160610001c001e01700115121401211841c40240c240e0720110500c8499881c081d40c0110969240154904404036552502250401c030f24040241030b010b0850030308540744503011610100ca00c00c0b85025417080003504115000109081030114800c0d620314040c14a942201e000010315012890070307240e080100d4940d03284c160b100c4036003401c0c07502c840d588091500c4040d109000159402c140d1146014031080750005541d170080b07440902c10b110b199224665545140a02c000150010403c08803c0201850002e031982d003180c001d1070004148000c202c481442d202c14900d80074002190642042014295030314140e8104106c41c5603189042e15000104e0020301076405211302c00e102c0000d1034010001c2c81c280000040101841010101249041a600800d01004814494000c94240a2156110344140c103440040100390303c15000c449401207424102040c001e056856441d00000c040a885c0d1890301500015800045044400700c100f0031100040d643c0489000c0321040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 446923839 1250 446922589 446922599
    0x71d071403181207060f0c2d020c180f0106090501210204120b0702060f040f0f050a02040213061e0215091507170f04150b010504051c0203100501 64
    0x803044a412401c0b0308100c92940300d030004618140080403c103c96124400100782c8108030090300041d1000210350003c010341c01601e4019604400301c8500c44003508415a14000c030500f921b4134644150040b881124410180c010103d0f50601210342d50750b1244070000b0030004c03240301a0b0b40369405030000d4079024040d640391000103480320782800361590080505c00800801b200c5268103880c003c10024142e00c01c0d00c80070381080c00017640d05488500041c003c2d000001c284240e00414980120f82c40b4508444000710794860b90120b0300110b8003191303140188400c100251b900c2e800540038410500414a828070710f0800040d010030034002205c96106102440b410f0754540114030410b1115101c03104010b1075071007144c102e041c006d00e040604044041c180901040d654000c02c951442002460101a1500e0b03103a10368410351800c40300203094400a038034032141d0030780c103801c0811504c1040c1030245c1403c1d140d0380000c080c1202d0088528541922031030a0065140401a5070705580040904001c2d0303504007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 446925089 1250 446923839 446923877
    0x20906100e01050c0a0503030106050a021006030c0e0712052508060d060903050412061b0c0f02060d0f0e0a0210080106020a110a090213030501110f040504150305071d07 74
    0x201d41924107100c000f082c0848004000d01141d842d0b0b0381c0c4a02a80c0c7d4075a101c860251498114240040c01441610300d06011141588a1076095070780091b143c500881c03504007918a210302c010010780402120048240f0940d6a83c01468007039110b440c081e800c130000f40c10b040d410005408844030100b00d014030034003040e0307101d6203149101181c1201002c10140b103541820349480c03186a0025151040305800b403003d00c0799541c0a4156203d205c0c5443d103100d589250129480341d052840903000440e000d00d40401031910740d0090201c000268408202400ba4a280c1e604950303c614010507141c01c0a1640800c40c80c0c144100c506014443c10f2003031041d410024002e40e40c1d264102c008056141400000076155510f0b09140c00508111809550701c501980805480030014841204e4960030099204100304043d416211102d200382d40c41400c0c585820100b101070010b032903079030480c0340c0f2040010000c55414000d007005860b42040740c464036103041c5094045104002c02035002c101005501c80010015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 446926339 1250 446925089 446925107
    0xe03010e1504061d0a0c0305060c0c1b0102101103040204050c0c12070f02131d0105220f0f0c030308010e01060c0818030f07030b1608190209061602090610 68
    0x3200000900b01004e240031280d140c030255074101c85200f0b40ba80c24040003600180003098a11030030942d08140c80390500701c440e50054841d4000325801c060511840449103600b01e0908120510441351855925200c0104494114031054002c0d54000100400e5040c60702615801040314140640f511416580351307030700c1d54440f009240100f03800150000c2400504141e1282080e0000d03c0e050790050203281c03040061040c48081f40e01c19040318525481d400c0103100b001e1003604004030111841801603201300c10506107a0080314012074804500c0040b9445e4080c20148600c0f8021100c0c20608608000c0c2a03070405a0003811004410001840625807042842c41d03440e50008550b5250213618000040c0340d40e407900f0041d0184540d00c404900d094001450314112400703054503100b144c40b4a00650b14284255613014003244800c008602e08000c5002c03004003e503401d100044c205941c2200260882d4031500d5400035a440840481042d40360410116402c500100c8007440c41c044001005040901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 446927589 1250 446926339 446926343
    0xa0203090d050106051801030204050703050903031305070e0405030307090f0315020a0509030d0503160c0b040f051507030506120c0904030302090307030203060a0c1e05040b070804150e03010e1504 86
    0x200c1c2030030040802009410404c00b034600208004450b11060a000c0c03081842440143e100c0c0c1d08140200726541e0282c1304607400768203d2030181d840c40c3c0c1d034410700704044c0980d91021a50b41c42030020014602c0003134000103008500c50307400b4540d0380c05c08800003080c0070b4203a0400c007035050282c401003001510707001c451410918006805610303920b4201c0305031005e00400081d0b1703426019038242440219404001507202e50061741e945445900192001c9800c00c8070740c04020040302c180008240416940354101c3e88040c8200201c42c06261404140b80725a40181d4030f010200f82c561052110624100c2507654121003920010586c01d8050030000f103c80002403c050145640010802401d85091158002454000e001c60b10507040000043c07000304041ea940f5400030b03132074a0b41203400c08115400701c1e43c501071668505080c141040b0070b214041e8040d0504a403d413400b000300042030400c580c1070804000654aa8503c8102c1510a03d0700b501c10311403003201e003a0460b40c104810744982c041d100360443c2d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 446928839 1250 446927589 446927599
    0x91e0714071a06030d0c020d020f03011d01060501120e0d0e0f152505032b0c11010e03040501050a1107080604080c24040f020103061505130b0a020309 66
    0x180420a00c403400307200d0180d000e420300240724055a046030381400154090700054080310071091500c036085030508045840250b21540480e4440c026103071146101a00d05030040c0006100a01c2a00000303071488842e1400700b142c0d469003010052581c001c00d54800c0000d071000c003401040d13084032100d600c4800260400040c8040415000d9103519920142c001450016041140c0e60121303801c003020340e410039441c15600c2e40c2a00c99500300a101c183e840c1c003103e94410011803d000c401c20450140c00c2000c40d501c4207500300320181a45148490140300a01d10711a203c0e103c001d9800d103c51030035a88007011000341c43e030003040100404e0741e00070f0403503079058164070340020701c0071010740f80b10b040a19590020381d261248100340400e200c54803006011040c1c00354100e40c1d81525450702e40d40c521160504c103c0d01150440c0c00280410030591280190300c0c03052400207812602e43e040708002c1d0003c8681030001890210f520820602140e2100020380f100740c040500301080c10400070341d00d100700e080c8035000f8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 446930089 1250 446928839 446928857
    0x209011b050c06030108070f0909033614031006050a050d03020f0609060115080f0609060f03010603051e15010501030c1103040326031312020c030a0b0105091e07 71
    0x100405000390100300300003c004580e6960740d0101180d848586004001885c006a640010242e44034842d45014a5054407040c2e900d00450b400c50307107509111905130f0b03940144c040812102005201e203450151600d640c4a241d54100001450b2170084180055000240b40040500043d590409040c04940c0d08490f0044e030340699217422400c040908103200201e22494050000000d40400c1c0b8506945840e0026103079414040c030b08542c00e400954030310040d4815070020910504242800543c800c0700a4020490300051360042421150b40e0340c410341c0d4503007000c40414100704a0758003000f100000301e0000c3c4100c1b004680c0c0000c22840601c00d180c1410703611030340301c148a801041f03c041e000e003030003007540d403900e070703070713080c9403814450444450a00307050315505e80b4120204401902d005400030115030b0038000c4640d840c654000c8800c0038510552154112041e220f980400075090418481c500d0a444c17035160009000c04600702038142c0741102a105002a0181400c0e04007591101081c58a8585 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 446931339 1250 446930089 446930093
    0x150605121504020f161205180607030c0f050c04050606090102060a0f09021e0a0b1611120d0c0b1b0706150506270618240412060c030209011b 62
    0x80c4540415440004c8020032165040944e0304100040f02c2d020303100341112030000d050200d6161042c82d800104149407e40340c2010307402e014001c0d0085602c40d04101c400507006440c0d0200234030340140d080300c1c2d560000550360030322300700741c004d458014005503a418100360b01d0000103034a4000c0242140031041c0d0340c5094404911503604040c035041e802404200d40d68171100034241021420303050050141c500140005070704407080e421164450313064541152100a9540e40002e410001d40c40540d100c000009030b58042c08080c46501110025511403200c0000c0030705d821281840003c10148024103031103180070342c8540320340491b041181d024a0000e90032400704070f0202d001c0078540107280c2149006c14a6400410a03203107403040051001040208190000e0411686104180c02c004c0c0e81d208545081215041c004040310036008503144090402c4641c0c0d071140100e4029034080b41c003d01107000c6500502c85036104d04004c0612900d0154a400788440020b0140c0030303074003803907034111000040c0f82003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 446932589 1250 446931339 446931341
    0x1050f04050a06050403110d0c0b210c04030510150623070b070e090106050d151e030b010e0105010512270303060a170a030509030703080a03150605121504 68
    0x60700000707210304429038489200070226045070004584c03100c005900309640345440f1100804581c2c0c03041a041c20340c0d00f03010443d80c880d00310181c5058094854030444c00841e1134042e00341d00c83e4201040c1c075600d603407840c1071091a2000400000c83d860f8078050b0300220f0302c5205403016007681d0303860800600000c0d80200c1441070101e8010881407003840031607207a040203002489c06005081c5551058860704110040000d090f00070322401011920403c85030140c41c0c3c00d41c1010840c152075503038012409584001c081c2d1002c40806511052514081050081099207405617000d4448400d60504640c1040c0c006882480380d03d404140960700e0100280c9482e01600c0451030100c0d00c14021b03845000c05201c610303034a030002e5800920403601082c000c02c1e840c0902c1d5107601c0c1100b1342402486e03d441d42d5142aa004c0d48500b08054142c01007100c00f00102e80d00600038840f003211650001201c2003c4d20b0b034003142c400950041005c200c0c6c10041800f40c1c2e1a0700248541120b54820000102451140010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 446933839 1250 446932589 446932597
    0x4030b0a0b0a080f01020702040b04150e070302070203150711150c130306090c0801050106050906092103030108060708060f0d03030f1e02030a0e032805040302040608010c02070503190201050f 84
    0x143d1511035011000f5403400c040d005010661f2003a41c052107a601d900082009540e1401d00a038119040510100b0000d1000c002c845d400c40c155040c01485c105854001c241002c01345000d4400c0c6800c800d00384140158041c510440003500800074181c102d45039007a041524102a16652101030080392080000e500030320b10310021a0303c070307208000d41d042c0d900e09510200ca8a125405c201d500e0840002802c03401101298261140140543d28000346141001001c1e1101108600c8140c41a001c600c10450104002c44c060110f590040c40c180c07a140c0030090a01c0303001403c5500820700000013801644030340d002900440da2600700031400490001d5088000e000851550140d1605e01c0428082103a055000318042e0106902c00c0c0184078074903640942e02d2140c000b04a40030040c42c0c008012920101440d0005525546002c80c58960380340c0015043d60790300d801011069541d4000984010340400c0000c008000a6000d885544181910002542031001d00a41800000540401a10140c800f11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 446935089 1250 446933839 446933849
    0x12030406060b1209010b10170a06030204050106120b0a0302062a0303010f0914060105091207050d150b0108040206030118020408030d09031b0816050a0203011b0207060504030b0a0b0a 80
    0x400c1d20361000341c6030b00f12070703602c1581d400200e5480c101c3c00c8401030074483e0007410b0079842d644030201c0c049802c141d41d43c0400c0703004100303c415139554400400103035900d000e072500034066650743c0881c04101c01140700c102d40d0b204c061580725508a190400050711442c065980300100b107600c10141d1413150714072130180f4000205d41c0c896800008000700795800483c40a405590300310030204407000034120b0383c0d001c0290603201c83d40070400c240a4076601c3d14105506080700b4042d102074448480d40c4401041d140401b884040360805281440e84075006510322a0402003442440c003000310303040c0390300880c03820311040c06480c0301c50624401e03858260450b070301158000d1a2501c02c0f80d65030141c0303120b020001d041d640f0341280091945503101e4200a454140d5058040d08506401e00c1c0030443d803017010050740242c004444c10700070403400c9809643d082c070401c0ea8600c0c250340c3c011400d05c05503200904103d00ca802034400d00a0500007032000c90700d48079085611048c0b6810015480c4090000201030144641c85 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 446936339 1250 446935089 446935109
    0x21090409020a0f17030301080a060b01050d1a12010c0806090604060b040f060f020a24110c0607020d0201110405041802032401050616031224080d0c03021203040606 72
    0x300043e40076141541d0000c48800f12208401d2041c4414280e480e4402807081d103403e540614151030201311180d20582c06500f050415500d40008905d0610940c0d0f81203a600380d00d4021400050550308060326001440074001c40200950043d080000c0c00910010302058014a001e00020b40c4c5511180d00460182489201c01600c9507a168040000d00c41c5900404c0002160300c01900c02d000d00000b42c01f82c810f0b03480006088150810f90300344280e400740442d030030006900c4c0c003e644081400540248001c0d55040042c001601c1e000001a00c1c00807040d9854046a141c040885038480031081582e050358400c90b00840d980146a880364003050107900701a607d0300440c100001c00841c030440103882e01c4ac0c0b003940041c00382e0fa00d8003000400c2c09821124041008034101400011744661030988008414550000f150b60482c890310100c0000340d0043c01d407500101c10b080c40428002c1000480228161509006610b415580203488404d50791106452803008030102c1d0070820141c026102420341510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 446937589 1250 446936339 446936359
    0x3030f0609021b0706110601090f0f020f0706110f0d0b031e0a11010e01090b13031209061b08040e070e18070e0d11060c0109080f0406112109040902 65
    0x3114400703001002d10f80c0c0420302c036410700026500d0040e540e850081340c501010b040160b20b4410107a01905184840a06041c2c0d00c455080701c69603540f014101c2158041542900c0d0112441c0003811108080b0f01d10408000034050040002402d1003124010a0541c2001c079680011a000c03c0c9080d52a081d20842c0003200400000c1c1d51100003100c100680c020000c841e600603c0d0300056031501c0000445900003034030301000b0301c070480c40310000305078a0b544151f02508495898450801c480a100a00e20020700b42d08003c2240d1603111040500c03d061012000e980e10b5040e5031406030522491103a105108400c500081d40c031402003101d05008000030306950b80c1c8000301428031b2111031085405002003101c00403051007030b00701007030aa811280d0010b40d000c20b51003110304010f01c580000c88580c0720341d920751a060001030a03d02c080c1100c4050460545c1e1a81d0401c2800b4050000401c51007005a00a9801c004c1601b4180304082d40400c801e90020b40d00c07540c842c0401d02800100c00082c1d04050556 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 446938839 1250 446937589 446937607
    0x40603030e19050108151f1809020315190b0c011b03053d0e0106200a030e210c100923061b0303040c050103051303030f060902 56
    0x35144260741256840e080309858030340011000b4040c0281800103240c00300141c58200c810305440d100420040103820102c0094410703116058492807848006900501d1441e41240341a20740e401504010f0b00540c110700c1d1081251704110542200a80f0070940404e1846c1600f0b4600d1038030000d40350000c0c216a07100803540305e0074040d24900440c840980f03004901240000e11a110b0940113001078540000f000c420b80e004a100904003280035104224803a00040480340c50722140401000c0c00c1030300194961401d038010b0124040d091045400d02d0184112582807840070900282d01a03041c20030503a840641e001041501c000704150f0080e4803064441c203071b454030002440e044454400c441500c0b00e84143c40c411103400915224070048801041c25220030410000c0031030681c1900a8403090501c914184c1c04001d86903501d0080c03425030000024070060001200c2114040c00003802c041c40a42040e44200b690348081590150405648000314040707000a900880c009046da058195100d40c1c10f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 446940089 1250 446938839 446938847
    0x30301080705011202030103150c030204090c08150d0c03060e0c0a0801090204150f2310090612091109090a0506071d040b06072d030509031e0d1101020904060303 71
    0x580100c2e8040349400000140a048500031281030300d90240310700b02c0401c07201d19483c01a050f8803240c40141502132001040c840c1403807240040c0314200c1d94502d10103081005401c0d204001c1c2504403030241d03c42c007403081e021880c0d95003104210b0745d2010000800068402d0340d1401c0030b04c0041c40b154462034000740081e901005411440100340212400c100401d1120300d014040c00c00ca01c602c0e050400420800c200281c000c0b42c0607541d280f0780c2e26184050002f10400580d060049820711008510042c0c424400c0c241e005504404004420004115130f1040d074076580348404031403200714070514003000000c1601c2010300ca60b10840b50300074210382031818115801341009000c140d00c6c8558110015100010b40b81c04d0062542c442d201400307540ca02865a00c409080c0d038a00385680d56680048001258074000d044042c0341d00c940681d4841e41c84442d104c0400d410010a1610703400300c0d00030740c5407100c800d071408158031082c00150305010646030441a9040d01a009440e01e085d88186088000404e242e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 446941339 1250 446940089 446940103
    0xa080310080f0d0e0f01050d050c03040b010b030c0930030414040b150708070507060e011704051506030a21031136120109050c030703030c081b03030108 67
    0x340d01e007500d8098281d2034400383d40d0040041004006050350f001200f035030908490f0070180140624000d4030b02202c1400b002c081e101c0a554803080d016002041000384000c41c500c580c09030180c10003241c514100140c10884038042c100c0380910802e000c0b145150641490640e54400d098032007420700d01101c50b03081c060b4880e04203104032a442800080da03081d0360314052240b0920b90800a221414040f801c180e143c40603001350400722a00710041001c5000710318100880c1d00181000d96a4401c80c01c11880014003d90610004816609007001071000003000440e001c0301d0780c442d00c40d0000c084e643d250002464070555120207041d00810404210b40e62024404441221610380c805000c0f00c03000b072805045a200d48230509000760340102c92402820b804d51900744003100301110290280c1d408400080401100c20700f00c00c0203039543d80e0f800c01000303000c2c0060007014104070041c10100e0325548000d800141d80100007001d42000081505030004c0d50440000da5400306c4007140d03103d40e11180060343e1511 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 446942446 1107 446941339 446941349
    0xf0901030e070807050307060509030606130b0a060e15032a120118110c031c021201030f03030f2912030f040e0a020403120507050a080310 61
    0xc1002802d000d0b0414002600e0614540070406280050580c8181e044c060180f18840c1f95680105840360b00c0701007540e40c080f418450500b944020411140c01c0c50b8421058107000c100769500403c150441c41c0155440c030012109000c5a01d102c0c041100d4507800b1aa0542990340d4400c2040340203406d4400307100304c0b2030070888400310300a0200c5098104901e80c03200342ca5494203980c2c0f2401401d00e43c000e10030a0b50f00d060001a01d00b80c4a21440284071a180d42c08102201001000e904840034100c2448051504d03503140d141c201100c003c002020b0b0b0020742004910955511540b040c140d10b642001d90b1542c519007a43c0c1001503000c0140106503000301840c04a06840c481480100151604c1c01e003155030b600d00b09400c02250380c8020740644400e91050000b4400514014114400302c285424019124140d0385000d41c030f0601f01420082045802001344809042c0100040058403 = true := by decide +kernel

theorem cover : BRFrame.Cov 446762589 446942446 := by
  have h0 := BRFrame.cov_init 446762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 446762589 ≤ n) (h2 : n < 446942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
